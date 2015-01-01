# btrfsTest.py

#/***************************************************************************
# *   Copyright (C) 2014-2015 deso (deso@posteo.net)                        *
# *                                                                         *
# *   This program is free software: you can redistribute it and/or modify  *
# *   it under the terms of the GNU General Public License as published by  *
# *   the Free Software Foundation, either version 3 of the License, or     *
# *   (at your option) any later version.                                   *
# *                                                                         *
# *   This program is distributed in the hope that it will be useful,       *
# *   but WITHOUT ANY WARRANTY; without even the implied warranty of        *
# *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *
# *   GNU General Public License for more details.                          *
# *                                                                         *
# *   You should have received a copy of the GNU General Public License     *
# *   along with this program.  If not, see <http://www.gnu.org/licenses/>. *
# ***************************************************************************/

"""Utility functionality for testing btrfs related functionality.

  This module provides the basic scaffolding for testing btrfs related
  changes. It contains classes that aid in creating loop back devices,
  formatting them with btrfs along with mounting them in the file
  system, and more.
  It furthermore makes ready-to-use test case base classes available
  that contain well defined execution environments.
"""

from deso.execute import (
  execute,
  executeAndRead,
)
from os import (
  O_CREAT,
  O_EXCL,
  O_RDWR,
  close,
  mkdir,
  open as mkfile,
  remove,
  rmdir,
  write,
)
from os.path import (
  join,
)
from tempfile import (
  mkdtemp,
  mkstemp,
)
from unittest import (
  TestCase,
)


_LOSETUP = "/sbin/losetup"
_MKBTRFS = "/sbin/mkfs.btrfs"
_MOUNT = "/bin/mount"
_UMOUNT = "/bin/umount"


def createFile(path, content=None):
  """Create a file given an absolute path."""
  fd = mkfile(path, O_CREAT | O_EXCL | O_RDWR)
  try:
    if content:
      write(fd, content)
  finally:
    close(fd)


def createDir(path):
  """Create a directory given an absolute path."""
  mkdir(path)


def alias(variable):
  """Provide an additional name for a variable temporarily.

    The aliasing functionality is meant to be used in conjunction with
    'with' blocks, like so:
    self._incredibly_long_variable_name = Object(...)
    with alias(self._incredibly_long_variable_name) as var:
      var.doSth()
      var.doSthElse()
  """
  class _Alias:
    """A wrapper object used for providing a new name for a variable.

      Notes: We rely on Python's closures here to avoid creating a
             separate member variable.
    """
    def __enter__(self):
      """The block enter handler just returns the variable."""
      return variable

    def __exit__(self, type_, value, traceback):
      """The block exit handler does nothing."""
      pass

  return _Alias()


class LoopBackDevice:
  """A class representing a loop back device."""
  def __init__(self, size):
    """Create a new loop back device backed by a file of given size."""
    # We start with retrieving the path to a loop device.
    self._loop_dev = executeAndRead(_LOSETUP, "-f")
    # Now create a temporary file to use as loop device backing store.
    fd, path = mkstemp()
    try:
      write(fd, b"\0" * size)

      # Actually set up the loop device. Now we have an ordinary block
      # device with absolute path 'self._loop_dev'.
      execute(_LOSETUP, self._loop_dev, path)
    finally:
      close(fd)
      # Now that the loop device is bound to the file we can already
      # unlink the file so that we do not have to take care of it any
      # longer.
      remove(path)


  def __enter__(self):
    """The block enter handler returns the already set up device object."""
    return self


  def __exit__(self, type_, value, traceback):
    """The block exit handler to destroy the loop back device."""
    self.destroy()


  def destroy(self):
    """Destroy the loop back device."""
    # Free the loop back device. Note that the temporary file used as
    # backing store got unlinked before already.
    execute(_LOSETUP, "-d", self._loop_dev)


  def device(self):
    """Retrieve the path to the loop back device."""
    return self._loop_dev


class BtrfsDevice(LoopBackDevice):
  """A class representing a device with a btrfs file system."""
  def __init__(self, size=16*1024*1024):
    """Create a loop back device with btrfs.

      Notes:
        Something in the order of 16 MiB seems to be the minimum size of
        a volume in which it is possible to create a btrfs file system.
    """
    super().__init__(size)
    try:
      execute(_MKBTRFS, self.device())
    except:
      super().destroy()
      raise


class Mount:
  """A class used for mounting a device."""
  def __init__(self, dev):
    """The constructor mounts the device in a temporary location."""
    self._directory = mkdtemp()
    try:
      execute(_MOUNT, dev, self._directory)
    except:
      rmdir(self._directory)
      raise


  def __enter__(self):
    """The block enter handler returns the already mounted device object."""
    return self


  def __exit__(self, type_, value, traceback):
    """The block exit handler to destroy the object."""
    self.destroy()


  def destroy(self):
    """Unmount the mounted device and remove the mount directory."""
    execute(_UMOUNT, self._directory)
    rmdir(self._directory)


  def path(self, *components):
    """Form an absolute path by combining the given components."""
    return join(self._directory, *components)


class BtrfsTestCase(TestCase):
  """A test case subclass that provides a mounted btrfs device."""
  def setUp(self):
    """Create a btrfs device and mount it ready for use."""
    super().setUp()

    self._device = BtrfsDevice()
    try:
      self._mount = Mount(self._device.device())
    except:
      self._device.destroy()
      raise


  def tearDown(self):
    """Unmount the btrfs device and destroy it."""
    self._mount.destroy()
    self._device.destroy()

    super().tearDown()
