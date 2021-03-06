# btrfsTest.py

#/***************************************************************************
# *   Copyright (C) 2014-2016 Daniel Mueller (deso@posteo.net)              *
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

from deso.btrfs.alias import (
  alias,
)
from deso.btrfs.command import (
  create,
  snapshot,
)
from deso.btrfs.repository import (
  Repository,
)
from deso.btrfs.test.util import (
  mkdtemp,
  mkstemp,
)
from deso.execute import (
  execute,
  findCommand,
)
from os import (
  O_CREAT,
  O_EXCL,
  O_RDWR,
  close,
  makedirs,
  open as open_,
  remove,
  rmdir,
  symlink,
  write,
)
from os.path import (
  dirname,
  join,
)
from unittest import (
  TestCase,
)


_LOSETUP = findCommand("losetup")
_MKBTRFS = findCommand("mkfs.btrfs")
_MOUNT = findCommand("mount")
_UMOUNT = findCommand("umount")


def createFile(path, content=None):
  """Create a file given an absolute path."""
  fd = open_(path, O_CREAT | O_EXCL | O_RDWR)
  try:
    if content:
      write(fd, content)
  finally:
    close(fd)


def make(container, *components, data=None, link=None, subvol=False):
  """Create a file, symlink, directory, or subvolume relative to an object with a path() method."""
  def assertOneMax(x, y, z):
    """Assert that that at most one of the three value is true."""
    assert int(bool(x)) + int(bool(y)) + int(bool(z)) <= 1

  assertOneMax(subvol, link, data is not None)

  path = container.path(*components)
  makedirs(dirname(path), exist_ok=True)

  if subvol:
    execute(*create(path))
  elif link:
    symlink(path, container.path(link))
  # Explicitly compare against none here to allow for empty file
  # creation by passing in b''.
  elif data is not None:
    createFile(path, data)
  else:
    makedirs(path, exist_ok=True)

  return path


class LoopBackDevice:
  """A class representing a loop back device."""
  def __init__(self, size):
    """Create a new loop back device backed by a file of given size."""
    # We start with retrieving the path to a loop device.
    dev, _ = execute(_LOSETUP, "-f", stdout=b"")
    # Now create a temporary file to use as loop device backing store.
    fd, path = mkstemp()
    try:
      write(fd, b"\0" * size)

      # Convert the byte array into a proper string and remove trailing
      # newline.
      self._loop_dev = dev.decode("utf-8")[:-1]
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
    """The block exit handler destroys the loop back device."""
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
  def __init__(self, size=128*1024*1024):
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
  def __init__(self, dev, *options):
    """The constructor mounts the device in a temporary location."""
    self._directory = mkdtemp()
    try:
      args = ["-o", ",".join(options)] if options else []
      execute(_MOUNT, dev, self._directory, *args)
    except:
      rmdir(self._directory)
      raise


  def __enter__(self):
    """The block enter handler returns the already mounted device object."""
    return self


  def __exit__(self, type_, value, traceback):
    """The block exit handler destroys the object."""
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


  def assertContains(self, file_, content):
    """Verify that a file has the given content."""
    with open(file_, "r") as handle:
      self.assertEqual(handle.read(), content)


class BtrfsSnapshotTestCase(BtrfsTestCase):
  """A test case subclass that provides a btrfs snapshot.

    The file system looks like this:
      /root/file
      /root_snapshot/file
  """
  def setUp(self):
    """Create a btrfs device and with a snapshot present."""
    super().setUp()

    try:
      with alias(self._mount) as m:
        execute(*create(m.path("root")))
        createFile(m.path("root", "file"))

        execute(*snapshot(m.path("root"),
                          m.path("root_snapshot")))
    except:
      super().tearDown()
      raise


class BtrfsRepositoryTestCase(BtrfsSnapshotTestCase):
  """A test case subclass that provides a btrfs repository with a snapshot present."""
  def setUp(self):
    """Create a btrfs repository."""
    super().setUp()

    try:
      # Snapshots are directly created in the root of the btrfs file
      # system here, so this is also where our repository is located.
      self._repository = Repository(self._mount.path())
    except:
      super().tearDown()
      raise
