# testBtrfs.py

#/***************************************************************************
# *   Copyright (C) 2014 deso (deso@posteo.net)                             *
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

"""Test btrfs wrapping functionality."""

from deso.btrfs.test.btrfsTest import (
  BtrfsDevice,
  Mount,
)
from unittest import (
  TestCase,
  main,
)


class TestBtrfsDevice(TestCase):
  """A test case for btrfs loop device related functionality."""
  def testBtrfsDeviceCreation(self):
    """Verify that we can create a btrfs formatted loop back device."""
    def testReadWrite(name, string):
      """Open a file, write something into it and read it back."""
      with open(mount.path(name), "w+") as handle:
        handle.write(string)
        handle.seek(0)
        self.assertEqual(handle.read(), string)

    with BtrfsDevice() as btrfs:
      with Mount(btrfs.device()) as mount:
        # We got the btrfs loop back device created and mounted
        # somewhere. Try creating a file, writing something to it, and
        # reading the data back to verify that everything actually
        # works.
        testReadWrite(mount.path("test.txt"), "testString98765")


if __name__ == "__main__":
  main()
