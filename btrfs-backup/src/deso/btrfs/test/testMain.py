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

from argparse import (
  ArgumentTypeError,
)
from datetime import (
  datetime,
  timedelta,
)
from deso.btrfs.alias import (
  alias,
)
from deso.btrfs.command import (
  delete,
)
from deso.btrfs.main import (
  duration,
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
  executable,
)
from unittest import (
  main,
)
from unittest.mock import (
  patch,
)


class TestMain(BtrfsTestCase):
  """A test case for testing of the progam's main functionality."""
  def testDurationParsingSuccess(self):
    """Test duration parsing with some examples that must succeed."""
    self.assertEqual(duration("20S"), timedelta(seconds=20))
    self.assertEqual(duration("1M"), timedelta(minutes=1))
    self.assertEqual(duration("56H"), timedelta(hours=56))
    self.assertEqual(duration("1d"), timedelta(hours=24))
    self.assertEqual(duration("5w"), timedelta(days=35))
    self.assertEqual(duration("13m"), timedelta(weeks=13*4))
    self.assertEqual(duration("8y"), timedelta(weeks=8*52))


  def testDurationParsingFailure(self):
    """Test duration parsing with some examples that must fail."""
    fails = ["", "x", "10u", "S5", "abc", "1y1", "13m_"]

    for fail in fails:
      with self.assertRaises(ArgumentTypeError):
        duration(fail)


  def testUsage(self):
    """Verify that the help contains an uppercase 'Usage:' string."""
    def runMain(*args):
      """Run the program and read the output it produces."""
      stdout, _ = execute(executable, "-m", "deso.btrfs.main", *args, read_out=True)
      stdout = stdout.decode("utf-8")
      return stdout

    stdout = runMain("--help")
    self.assertRegex(stdout, "^Usage:")

    stdout = runMain("backup", "--help")
    self.assertRegex(stdout, "^Usage:")

    stdout = runMain("restore", "--help")
    self.assertRegex(stdout, "^Usage:")


  def testUsageError(self):
    """Verify that the help contains an uppercase 'Usage:' string in case of wrong usage."""
    def runMain(*args):
      """Run the program."""
      execute(executable, "-m", "deso.btrfs.main", *args)

    def runAndTest(*args):
      """Run the program with the given arguments and verify there is only one Usage: string."""
      try:
        runMain(*args)
        # The command should fail due to missing arguments.
        self.assertFalse(True)
      except ChildProcessError as e:
        string = str(e)

      self.assertRegex(string, "Usage:")
      self.assertNotRegex(string, "usage:")
      # Remove the usage string. There should not be a second one (we
      # had a couple of problems with two usage strings being prepended
      # to the actual line of text, hence this test).
      string = string.replace("Usage", "", 1)
      self.assertNotRegex(string, "Usage:")

    runAndTest()
    runAndTest("backup")
    runAndTest("restore")


  def testKeepFor(self):
    """Verify that using the --keep-for option old snapshots get deleted."""
    with patch("deso.btrfs.repository.datetime", wraps=datetime) as mock_now:
      with alias(self._mount) as m:
        make(m, "subvol", subvol=True)
        make(m, "snapshots")
        make(m, "backup")

        now = datetime.now()
        mock_now.now.return_value = now

        args = "backup --subvolume {subvol} {src} {dst}"
        args = args.format(subvol=m.path("subvol"),
                           src=m.path("snapshots"),
                           dst=m.path("backup"))
        result = btrfsMain([argv[0]] + args.split())
        self.assertEqual(result, 0)
        self.assertEqual(len(glob(m.path("snapshots", "*"))), 1)

        # We need a second snapshot, taken at a later time.
        mock_now.now.return_value = now + timedelta(minutes=1)
        make(m, "subvol", "file1", data=b"data")

        result = btrfsMain([argv[0]] + args.split())
        self.assertEqual(result, 0)
        self.assertEqual(len(glob(m.path("snapshots", "*"))), 2)

        # Now for the purging.
        mock_now.now.return_value = now + timedelta(hours=7, seconds=1)

        # With a keep duration of one day the snapshots must stay.
        args1 = args + " --keep-for=1d"
        result = btrfsMain([argv[0]] + args1.split())
        self.assertEqual(result, 0)
        self.assertEqual(len(glob(m.path("snapshots", "*"))), 2)

        # With a duration of 7 hours one must go.
        args1 = args + " --keep-for=7H"
        result = btrfsMain([argv[0]] + args1.split())
        self.assertEqual(result, 0)
        self.assertEqual(len(glob(m.path("snapshots", "*"))), 1)


  def testRun(self):
    """Test a simple run of the program with two subvolumes."""
    def wipeSubvolumes(path, pattern="*"):
      """Remove all subvolumes in a given path (non recursively)."""
      snapshots = glob(join(path, pattern))

      for snapshot in snapshots:
        execute(*delete(snapshot))

      self.assertEqual(glob(join(path, pattern)), [])

    def run(command, src, dst, *options):
      """Run the program to work on two subvolumes."""
      args = [
        command,
        "-s", m.path("home", "user"),
        "--subvolume=%s" % m.path("root"),
        src, dst
      ]
      result = btrfsMain([argv[0]] + args + list(options))
      self.assertEqual(result, 0)

    def backup():
      """Invoke the program to backup snapshots/subvolumes."""
      run("backup", m.path("snapshots"), b.path("backup"))

    def restore(*options, reverse=False):
      """Invoke the program to restore snapshots/subvolumes."""
      if not reverse:
        src = b.path("backup")
        dst = m.path("snapshots")
      else:
        src = m.path("snapshots")
        dst = b.path("backup")

      run("restore", src, dst, *options)

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
