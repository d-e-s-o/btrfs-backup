# testMain.py

#/***************************************************************************
# *   Copyright (C) 2015 deso (deso@posteo.net)                             *
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

"""Test the progam's main functionality."""

from deso.btrfs.alias import (
  alias,
)
from deso.btrfs.command import (
  delete,
)
from deso.btrfs.main import (
  main as btrfsMain,
)
from deso.btrfs.test.btrfsTest import (
  BtrfsDevice,
  BtrfsTestCase,
  make,
  Mount,
)
from deso.execute import (
  execute,
)
from os.path import (
  join,
)
from glob import (
  glob,
)
from sys import (
  argv,
)
from unittest import (
  main,
)


class TestMain(BtrfsTestCase):
  """A test case for testing of the progam's main functionality."""
  def testRun(self):
    """Test a simple run of the program with two subvolumes."""
    def wipeSubvolumes(path, pattern="*"):
      """Remove all subvolumes in a given path (non recursively)."""
      snapshots = glob(join(path, pattern))

      for snapshot in snapshots:
        execute(*delete(snapshot))

      self.assertEqual(glob(join(path, pattern)), [])

    def run(src, dst, *options):
      """Run the program to work on two subvolumes."""
      args = [
        "-s", m.path("home", "user"),
        "--subvolume=%s" % m.path("root"),
        src, dst
      ]
      result = btrfsMain([argv[0]] + args + list(options))
      self.assertEqual(result, 0)

    def backup():
      """Invoke the program to backup snapshots/subvolumes."""
      run(m.path("snapshots"), b.path("backup"))

    def restore(*options, reverse=False):
      """Invoke the program to restore snapshots/subvolumes."""
      if not reverse:
        src = b.path("backup")
        dst = m.path("snapshots")
      else:
        src = m.path("snapshots")
        dst = b.path("backup")

      run(src, dst, "--restore", *options)

    with alias(self._mount) as m:
      # We backup our data to a different btrfs volume.
      with BtrfsDevice() as btrfs:
        with Mount(btrfs.device()) as b:
          make(m, "home", "user", subvol=True)
          make(m, "home", "user", "data", "movie.mp4", data=b"abcdefgh")
          make(m, "root", subvol=True)
          make(m, "root", ".ssh", "key.pub", data=b"1234567890")
          make(m, "snapshots")
          make(b, "backup")

          # Case 1) Run in ordinary fashion to backup data into a
          #         separate btrfs backup volume.
          backup()

          user, root = glob(b.path("backup", "*"))

          self.assertContains(join(user, "data", "movie.mp4"), "abcdefgh")
          self.assertContains(join(root, ".ssh", "key.pub"), "1234567890")

          # Case 2) Delete all created snapshots (really only the
          #         snapshots for now) from our "source" and try
          #         restoring them from the backup.
          wipeSubvolumes(m.path("snapshots"))
          restore("--snapshots-only")

          user, root = glob(m.path("snapshots", "*"))

          self.assertContains(m.path(user, "data", "movie.mp4"), "abcdefgh")
          self.assertContains(m.path(root, ".ssh", "key.pub"), "1234567890")

          # Case 3) Once again delete all snapshots but this time
          #         restore them in conjunction with the --reverse
          #         option.
          wipeSubvolumes(m.path("snapshots"))

          # This time we use the '--reverse' option.
          restore("--reverse", "--snapshots-only", reverse=True)

          user, root = glob(m.path("snapshots", "*"))

          self.assertContains(m.path(user, "data", "movie.mp4"), "abcdefgh")
          self.assertContains(m.path(root, ".ssh", "key.pub"), "1234567890")

          # Case 4) Also delete the original subvolumes we snapshotted
          #         and verify that they can be restored as well.
          wipeSubvolumes(m.path("home"))
          wipeSubvolumes(m.path(), pattern="root")
          wipeSubvolumes(m.path("snapshots"))
          restore()

          user, = glob(m.path("home", "user"))
          root, = glob(m.path("root"))

          self.assertContains(m.path(user, "data", "movie.mp4"), "abcdefgh")
          self.assertContains(m.path(root, ".ssh", "key.pub"), "1234567890")


if __name__ == "__main__":
  main()
