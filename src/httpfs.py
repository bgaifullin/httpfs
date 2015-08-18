#!/usr/bin/env python
from __future__ import with_statement
import os
import sys
import errno
import dateutil.parser
import time
import logging
import logging.handlers
import array
import resource
from fuse import FUSE, FuseOSError, Operations
from threading import Lock

try:
    import urllib2 as urllib
except ImportError:
    import urllib

try:
    import urlparse
except ImportError:
    from urllib import parse as urlparse

try:
    from html.parser import HTMLParser
except ImportError:
    from HTMLParser import HTMLParser


class HTTPRequest(urllib.Request):
    def __init__(self, *args, **kwargs):
        self.__method = kwargs.pop("method", None)
        urllib.Request.__init__(self, *args, **kwargs)

    def get_method(self):
        if self.__method is not None:
            return self.__method
        return urllib.Request.get_method(self)


class FilesParser(HTMLParser):
    def __init__(self, prefix, callback):
        HTMLParser.__init__(self)
        self._prefix = prefix
        self._callback = callback

    def handle_starttag(self, tag, attrs):
        if tag != 'a':
            return

        for name, value in attrs:
            if name == 'href':
                if value.startswith('/') and not value.startswith(self._prefix):
                    break
                if value.startswith(os.pardir):
                    break

                if value[-1] == '/':
                    value = value[:-1]

                value = os.path.basename(value)
                if value[0] == '!':  # workarround to fix issue with buildsystem
                    break

                self._callback(os.path.basename(value))
                break


class FDTable:
    bitmask = (0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80)
    max_fds = resource.getrlimit(resource.RLIMIT_NOFILE)[1] // 8

    def __init__(self, size=0):
        """
        Create a BitMap
        """
        self.bitmap = array.array('B', [0] * ((size + 7) // 8))
        self.next_fd = 3

    def test(self, fd):
        """
        Return bit value
        """
        return (self.bitmap[fd // 8] & self.bitmask[fd % 8]) != 0

    def try_to_alloc(self, fd):
        """
        Test and set
        """
        if not self.test(fd):
            self.bitmap[fd // 8] |= self.bitmask[fd % 8]
            return True
        return False

    def close_fd(self, fd):
        """
        free fd
        """
        self.bitmap[fd // 8] &= ~self.bitmask[fd % 8]
        if fd < self.next_fd:
            self.next_fd = fd

    def alloc_fd(self):
        """
        allocate fd
        """
        for i in xrange(self.next_fd, len(self)):
            if self.try_to_alloc(i):
                self.next_fd = i + 1
                return i

        if len(self.bitmap) == self.max_fds:
            return -1

        self.next_fd = len(self)
        n = min(len(self.bitmap) * 2, self.max_fds) - len(self.bitmap)

        self.bitmap.extend([0] * n)
        return self.alloc_fd()

    def __len__(self):
        return len(self.bitmap) * 8


class SequentialFile(object):
    def __init__(self, fobj):
        self.fobj = fobj
        self.offset = 0

    def read(self, offset, length):
        if self.offset != offset:
            raise FuseOSError(errno.EINVAL)
        b = self.fobj.read(length)
        self.offset += len(b)
        return b

    def close(self):
        self.fobj.close()


class HttpFS(Operations):

    def __init__(self, url):
        if url[-1] != '/':
            url += '/'
        self.base = url
        self.opener = urllib.build_opener()
        self.openfiles = dict()
        self.fd_table = FDTable(16)
        self.file_class = SequentialFile
        self.guard = Lock()

    # Helpers
    # =======

    def _url(self, partial):
        if partial[0] == '/':
            partial = partial[1:]

        return urlparse.urljoin(self.base, partial)

    @staticmethod
    def _error(http_error):
        assert isinstance(http_error, urllib.HTTPError)
        logging.error("%d %s %s", http_error.code, http_error.read(), http_error.url)

        if http_error.code == 400:
            return FuseOSError(errno.EINVAL)
        if http_error.code in [401, 403]:
            return FuseOSError(errno.EACCES)
        if http_error.code == 404:
            return FuseOSError(errno.ENOENT)
        if http_error.code == 409:
            return FuseOSError(errno.EEXIST)

    # Filesystem methods
    # ==================

    def access(self, path, mode):
        try:
            url = self._url(path)
            logging.debug("access %s (%s), %s", path, url, mode)
            self.opener.open(HTTPRequest(self._url(path), method='HEAD'))
        except Exception as e:
            logging.exception("access -> %r", e)
            raise FuseOSError(errno.EACCES)

    def chmod(self, path, mode):
        logging.debug("chmod %s %s", path, mode)
        raise FuseOSError(errno.EROFS)

    def chown(self, path, uid, gid):
        logging.debug("chown %s %s %s", path, uid, gid)
        raise FuseOSError(errno.EROFS)

    def getattr(self, path, fh=None):
        try:
            url = self._url(path)
            logging.debug("getattr %s (%s), %s", path, url, fh)
            response = self.opener.open(HTTPRequest(url, method='HEAD'))
            url = response.geturl()
            logging.debug("getattr %s", url)

            if url.endswith('/'):
                m_mode = 040444
                m_time = 0
                m_size = 0
            else:
                m_mode = 0100444
                m_size = int(response.headers.get('Content-Length', 0))
                try:
                    m_time = int(time.mktime(dateutil.parser.parse(response.headers['Last-Modified']).timetuple()))
                except KeyError:
                    m_time = 0

            result = dict(st_atime=m_time, st_ctime=m_time, st_mtime=m_time, st_gid=os.getgid(),
                          st_mode=m_mode, st_nlink=1, st_uid=os.getuid(), st_size=m_size)
            logging.debug("getattr -> %s", result)
            return result

        except urllib.HTTPError as e:
            logging.error("getattr -> %r", e)
            raise self._error(e)
        except Exception as e:
            logging.exception("getattr -> %r", e)
            raise FuseOSError(errno.EAGAIN)

    def readdir(self, path, fh):
        try:
            url = self._url(path)
            logging.debug("readdir %s (%s)", path, url)
            response = self.opener.open(url)
            yield '.'
            yield '..'

            content = list()
            parser = FilesParser(urlparse.urlsplit(url).path, content.append)
            while True:
                data = response.read(1024)
                if not data:
                    break
                parser.feed(data)

                for c in content:
                    yield c

                del content[:]

        except urllib.HTTPError as e:
            logging.error("readdir %r", e)
            raise self._error(e)
        except Exception as e:
            logging.exception("getattr %r", e)
            raise FuseOSError(errno.EAGAIN)

    def readlink(self, path):
        logging.debug("readlink %s", path)
        raise FuseOSError(errno.ENOSYS)

    def mknod(self, path, mode, dev):
        logging.debug("mknod %s %s %s", path, mode, dev)
        raise FuseOSError(errno.EROFS)

    def rmdir(self, path):
        logging.debug("rmdir %s", path)
        raise FuseOSError(errno.EROFS)

    def mkdir(self, path, mode):
        logging.debug("mkdir %s %s", path, mode)
        raise FuseOSError(errno.EROFS)

    def statfs(self, path):
        logging.debug("statfs %s", path)
        return dict(f_bavail=0, f_bfree=0, f_blocks=0, f_bsize=0, f_favail=0, f_ffree=0, f_files=0, f_flag=5,
                    f_frsize=0, f_namemax=0)

    def unlink(self, path):
        logging.debug("unlink %s", path)
        raise FuseOSError(errno.EROFS)

    def symlink(self, name, target):
        logging.debug("symlink %s %s", name, target)
        raise FuseOSError(errno.EROFS)

    def rename(self, old, new):
        logging.debug("rename %s %s", old, new)
        raise FuseOSError(errno.EROFS)

    def link(self, target, name):
        logging.debug("link %s %s", target, name)
        raise FuseOSError(errno.EROFS)

    def utimens(self, path, times=None):
        logging.debug("utimens %s %s", path, times)
        raise FuseOSError(errno.ENOSYS)

    # File methods
    # ============

    def open(self, path, flags):
        try:
            logging.debug("open %s %s", path, flags)
            response = self.opener.open(self._url(path))
            with self.guard:
                fd = self.fd_table.alloc_fd()
            logging.debug("open -> %d", fd)
            if fd == -1:
                raise FuseOSError(errno.EMFILE)
            self.openfiles[fd] = self.file_class(response)
            return fd
        except FuseOSError:
            raise
        except urllib.HTTPError as e:
            logging.error("open -> %r", e)
            raise self._error(e)
        except Exception as e:
            logging.exception("open -> %r", e)
            raise FuseOSError(errno.EAGAIN)

    def create(self, path, mode, fi=None):
        logging.debug("create %s %s %s", path, mode, fi)
        raise FuseOSError(errno.EROFS)

    def read(self, path, length, offset, fh):
        logging.debug("read %s %d %d %d", path, length, offset, fh)
        try:
            seq_file = self.openfiles[fh]
        except KeyError:
            raise FuseOSError(errno.EINVAL)
        return seq_file.read(offset, length)

    def write(self, path, buf, offset, fh):
        logging.debug("write %s %s %d %d", path, buf, offset, fh)
        raise FuseOSError(errno.EROFS)

    def truncate(self, path, length, fh=None):
        logging.debug("truncate %s %d %d", path, length, fh)
        raise FuseOSError(errno.EROFS)

    def flush(self, path, fh):
        logging.debug("truncate %s %d", path, fh)
        raise FuseOSError(errno.EROFS)

    def release(self, path, fh):
        logging.debug("release %s %d", path, fh)
        try:
            self.openfiles.pop(fh).close()
            self.fd_table.close_fd(fh)
        except KeyError:
            raise FuseOSError(errno.EINVAL)

    def fsync(self, path, fdatasync, fh):
        logging.debug("fsync %s %s %d", path, fdatasync, fh)
        raise FuseOSError(errno.EROFS)


def parse_options(args):
    from argparse import ArgumentParser
    parser = ArgumentParser()
    parser.add_argument('-v', '--version', action='version', version='httpfs 1.0')
    parser.add_argument('source', nargs=1, help='site resource url')
    parser.add_argument('mountpoint', nargs=1, help='mount point')
    parser.add_argument("--debug", action='store_true', help='enable debug mode', default=False)
    return parser.parse_args(args)


def main(args):
    options = parse_options(args)
    if options.debug:
        logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)
    else:
        logging.getLogger().setLevel(logging.INFO)
        logging.getLogger().addHandler(logging.handlers.SysLogHandler())

    logging.debug("%s - %s", options.source[0], options.mountpoint[0])
    FUSE(HttpFS(options.source[0]), options.mountpoint[0], foreground=options.debug)

if __name__ == '__main__':
    main(sys.argv[1:])
