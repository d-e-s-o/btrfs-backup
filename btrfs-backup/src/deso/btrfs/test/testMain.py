# testMain.py

#/***************************************************************************
# *   Copyright (C) 2015-2016 Daniel Mueller (deso@posteo.net)              *
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
from deso.btrfs.test.util import (
  mkdtemp,
  NamedTemporaryFile,
  TemporaryDirectory,
)
from deso.cleanup import (
  defer,
)
from deso.execute import (
  execute,
  findCommand,
  pipeline,
  ProcessError,
)
from os import (
  environ,
  rmdir,
)
from os.path import (
  extsep,
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
  SkipTest,
  TestCase,
)
from unittest.mock import (
  patch,
)


class TestMainOptions(TestCase):
  """Test case for option handling in the main program."""
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


  def testInvokeNoArguments(self):
    """Verify the intended output is printed when the program is run without arguments."""
    regex = "the following arguments are required"
    with self.assertRaisesRegex(ProcessError, regex):
      execute(executable, "-m", "deso.btrfs.main")


  def testUsage(self):
    """Verify that the help contains an uppercase 'Usage:' string."""
    def runMain(*args):
      """Run the program and read the output it produces."""
      stdout, _ = execute(executable, "-m", "deso.btrfs.main", *args, stdout=b"")
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
      except ProcessError as e:
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


  def testDebugOption(self):
    """Verify that using the --debug option an exception leaves the main function."""
    with TemporaryDirectory() as path:
      args_base = "backup --subvolume {e} {e} {e} {d}"
      args = args_base.format(e=join(path, "not-existant"), d="")
      result = btrfsMain([argv[0]] + args.split())
      self.assertNotEqual(result, 0)

      args = args_base.format(e=join(path, "not-existant"), d="--debug")
      with self.assertRaises(FileNotFoundError):
        btrfsMain([argv[0]] + args.split())


  def testSnapshotExtOption(self):
    """Verify that the --snapshot-ext option works as expected."""
    def runMain(*args):
      """Run the program."""
      execute(executable, "-m", "deso.btrfs.main", *args)

    regex = r"Extension must not start"
    with self.assertRaisesRegex(ProcessError, regex):
      runMain("backup", "--snapshot-ext=%senc" % extsep)

    regex = r"The last receive filter must contain"
    with self.assertRaisesRegex(ProcessError, regex):
      runMain("backup", "--snapshot-ext=gz", "--recv-filter", "/bin/gzip")

    regex = r"The first send filter must contain"
    with self.assertRaisesRegex(ProcessError, regex):
      runMain("restore", "--snapshot-ext=gz", "--send-filter", "/bin/gzip")

    # TODO: We should likely add a test to verify that the {file}
    #       detection works in conjunction with springs and the --join
    #       option.

    # This call succeeds from the point of view of supplying the
    # snapshot-ext option but other arguments are missing so we still
    # bail out.
    regex = r"arguments are required"
    with self.assertRaisesRegex(ProcessError, regex):
      runMain("backup", "--snapshot-ext=gz", "--recv-filter=/bin/gzip",
              "--recv-filter", "/bin/dd of={file}")

    regex = r"arguments are required"
    with self.assertRaisesRegex(ProcessError, regex):
      runMain("restore", "--snapshot-ext=gz",
              "--send-filter=/bin/dd if={file}",
              "--send-filter", "/bin/gzip")


class TestMainMisc(BtrfsTestCase):
  """A test case for testing of the progam's main functionality."""
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


  def testRemoteAndFilterCommands(self):
    """Verify that the remote and send/receive filter commands are used correctly."""
    remote_cmd = "/usr/bin/ssh server"
    send_filt1 = "/bin/gzip --stdout --fast"
    send_filt2 = "/bin/bzip2 --stdout --compress --small"
    recv_filt1 = "/bin/bzip2 --decompress --small"
    recv_filt2 = "/bin/gzip --decompress"

    def isCommand(command, cmd_string):
      """Check if a given command begins with the given string."""
      return " ".join(command).startswith(cmd_string)

    def removeRemoteCommand(command):
      """Filter all remote command parts from a command (if any)."""
      # Since we do not have an SSH server running (and do not want to),
      # filter out the remote command part before execution.
      if isCommand(command, remote_cmd):
        command = command[2:]

      return command

    def isNoFilterCommand(command):
      """Check if a command is a filter command."""
      return not (isCommand(command, send_filt1) or\
                  isCommand(command, send_filt2) or\
                  isCommand(command, recv_filt1) or\
                  isCommand(command, recv_filt2))

    def filterCommands(commands):
      """Filter all remote and filter command parts from a command list (if any)."""
      return list(map(removeRemoteCommand, filter(isNoFilterCommand, commands)))

    def executeWrapper(*args, **kwargs):
      """Wrapper around the execute function that stores the commands it executed."""
      command = list(args)
      all_commands.append(command)
      command = removeRemoteCommand(command)

      return execute(*command, **kwargs)

    def runCommandsWrapper(commands, *args, **kwargs):
      """Wrapper around the runCommands function that stores the commands it executed."""
      # Note that we do not need to handle springs here because with the
      # given options a spring will never be used.
      for command in commands:
        all_commands.append(command)

      commands = filterCommands(commands)
      return pipeline(commands, *args, **kwargs)

    all_commands = []
    with patch("deso.btrfs.repository.execute", wraps=executeWrapper),\
         patch("deso.btrfs.repository.runCommands", wraps=runCommandsWrapper):
      with alias(self._mount) as m:
        subvolume = make(m, "subvol", subvol=True)
        snapshots = make(m, "snapshots")
        backup = make(m, "backup")

        args = [
          "backup",
          "--subvolume=%s" % subvolume,
          snapshots,
          backup,
          "--remote-cmd=%s" % remote_cmd,
          "--send-filter=%s" % send_filt1,
          "--recv-filter=%s" % send_filt2,
          "--send-filter=%s" % recv_filt1,
          "--recv-filter=%s" % recv_filt2,
        ]
        result = btrfsMain([argv[0]] + args)
        self.assertEqual(result, 0)

    # We do not check all commands here. However, we know for sure that
    # btrfs receive should be run on the remote side. So check that it
    # is properly prefixed.
    receive, = list(filter(lambda x: "receive" in x, all_commands))
    self.assertTrue(isCommand(receive, remote_cmd), receive)

    # Similarly, each of the send and receive filters should appear
    # somewhere in the commands.
    send_filt, = list(filter(lambda x: isCommand(x, send_filt1), all_commands))
    self.assertNotEqual(send_filt, [])

    recv_filt, = list(filter(lambda x: isCommand(x, recv_filt2), all_commands))
    self.assertNotEqual(recv_filt, [])


  def testNoStderrRead(self):
    """Verify that we get not a full error message when --no-read-stderr is used."""
    # Note that strictly speaking we do not actually test that the
    # problem for which we introduced the --no-read-stderr option in the
    # first place is solved. We mainly verify that the option is passed
    # down and we assume the remaining infrastructure to work as
    # expected.
    with patch("deso.btrfs.repository.datetime", wraps=datetime) as mock_now:
      mock_now.now.return_value = datetime(2015, 1, 29, 20, 59)

      with alias(self._mount) as m:
        # Note that 'subvol' is actually no subvolume so the backup will
        # fail at some point.
        make(m, "subvol")
        make(m, "snapshots")
        make(m, "backup")

        args = "backup --debug --no-read-stderr --subvolume {subvol} {src} {dst}"
        args = args.format(subvol=m.path("subvol"),
                           src=m.path("snapshots"),
                           dst=m.path("backup"))

        # When not using --no-read-stderr the time stamp would be
        # followed by an error string containing the program's stderr
        # output.
        regex = r"subvol-2015-01-29_20:59:00$"
        with self.assertRaisesRegex(ProcessError, regex):
          btrfsMain([argv[0]] + args.split())


class TestMainRunBase(BtrfsTestCase):
  """Test case base class for btrfs-backup end-to-end tests."""
  def setUp(self):
    """Create the test harness with a single btrfs volume and some data."""
    with defer() as d:
      super().setUp()
      d.defer(super().tearDown)

      with alias(self._mount) as m:
        self._user = make(m, "home", "user", subvol=True)
        self._root = make(m, "root", subvol=True)
        self._snapshots = make(m, "snapshots")

      d.release()


  def wipeSubvolumes(self, path, pattern="*"):
    """Remove all subvolumes in a given path (non recursively)."""
    snapshots = glob(join(path, pattern))

    for snapshot in snapshots:
      execute(*delete(snapshot))

    self.assertEqual(glob(join(path, pattern)), [])


  def _run(self, command, src, dst, *options):
    """Run the program to work on two subvolumes."""
    args = [
      command,
      "-s", self._user,
      "--subvolume=%s" % self._root,
      src, dst
    ]
    result = btrfsMain([argv[0]] + args + list(options))
    self.assertEqual(result, 0)


  def backup(self, src, dst, *options):
    """Invoke the program to backup snapshots/subvolumes."""
    self._run("backup", src, dst, *options)


  def restore(self, src, dst, *options, **kwargs):
    """Invoke the program to restore snapshots/subvolumes."""
    self._run("restore", src, dst, *options)


  def performTest(self, backup, restore, src, dst):
    """Test a simple run of the program with two subvolumes."""
    with alias(self._mount) as m:
      make(m, "home", "user", "data", "movie.mp4", data=b"abcdefgh")
      make(m, "root", ".ssh", "key.pub", data=b"1234567890")

      # Case 1) Run in ordinary fashion to backup data into a
      #         separate btrfs backup volume. Result is verified
      #         by the restore operation later on.
      backup(src, dst)

      # Case 2) Delete all created snapshots (really only the
      #         snapshots for now) from our "source" and try
      #         restoring them from the backup.
      self.wipeSubvolumes(self._snapshots)

      restore(dst, src, "--snapshots-only")
      user, root = glob(m.path("snapshots", "*"))

      self.assertContains(m.path(user, "data", "movie.mp4"), "abcdefgh")
      self.assertContains(m.path(root, ".ssh", "key.pub"), "1234567890")

      # Case 3) Also delete the original subvolumes we snapshotted
      #         and verify that they can be restored as well.
      self.wipeSubvolumes(m.path("home"))
      self.wipeSubvolumes(m.path(), pattern="root")
      self.wipeSubvolumes(m.path("snapshots"))

      restore(dst, src)

      user, = glob(m.path("home", "user"))
      root, = glob(m.path("root"))

      self.assertContains(m.path(user, "data", "movie.mp4"), "abcdefgh")
      self.assertContains(m.path(root, ".ssh", "key.pub"), "1234567890")


class TestLocalMainRun(TestMainRunBase):
  """Test case invoking the btrfs-progam for end-to-end tests with a local backup repository."""
  def setUp(self):
    """Create a btrfs device for the backups."""
    with defer() as d:
      super().setUp()
      d.defer(super().tearDown)

      self._bdevice = BtrfsDevice()
      d.defer(self._bdevice.destroy)

      self._backup = Mount(self._bdevice.device())
      d.defer(self._backup.destroy)

      self._backups = make(self._backup, "backup")
      d.release()


  def tearDown(self):
    """Unmount the backup device and destroy it."""
    self._backup.destroy()
    self._bdevice.destroy()

    super().tearDown()


  def testNormalRun(self):
    """Test backup and restore."""
    self.performTest(self.backup, self.restore, self._snapshots, self._backups)


  def testGpgRun(self):
    """Test backup and restore with end-to-end encryption by GnuPG."""
    # TODO: It could make sense to have the destination volume being
    #       backed by a file system other than btrfs.
    def backup(src, dst, *options):
      """Invoke the program to backup snapshots/subvolumes in an encrypted way."""
      gpg_options = "--encrypt --no-default-keyring "\
                    "--keyring={pubkey} --trust-model=always "\
                    "--recipient=tester --batch --output={{file}}"
      gpg_options = gpg_options.format(pubkey=public_key.name)
      options = list(options)
      options += [
        "--snapshot-ext=gpg",
        "--recv-filter=%s %s" % (GPG, gpg_options),
      ]
      self.backup(src, dst, *options)

    def restore(src, dst, *options):
      """Invoke the program to restore snapshots/subvolumes from an encrypted source."""
      gpg_options = "--decrypt --no-default-keyring "\
                    "--keyring={pubkey} --secret-keyring={privkey} "\
                    "--trust-model=always --batch {{file}}"
      gpg_options = gpg_options.format(pubkey=public_key.name,
                                       privkey=private_key.name)
      options = list(options)
      options += [
        "--snapshot-ext=gpg",
        "--send-filter=%s %s" % (GPG, gpg_options),
        "--join",
      ]
      self.restore(src, dst, *options)
    try:
      GPG = findCommand("gpg")
    except FileNotFoundError:
      raise SkipTest("GnuPG not found")

    from deso.btrfs.test.gpg import PRIVATE_KEY, PUBLIC_KEY

    with NamedTemporaryFile() as public_key,\
         NamedTemporaryFile() as private_key:
      # First we need to convert our ASCII keys into binary ones (which
      # reside in a file) for later usage. GnuPG can do that for us.
      stdin = PUBLIC_KEY.encode("utf-8")
      execute(GPG, "--dearmor", stdin=stdin, stdout=public_key.fileno())

      stdin = PRIVATE_KEY.encode("utf-8")
      execute(GPG, "--dearmor", stdin=stdin, stdout=private_key.fileno())

      # Invoke the test but have it run with the functions using GPG.
      self.performTest(backup, restore, self._snapshots, self._backups)


class TestRemoteMainRun(TestMainRunBase):
  """Test case invoking the btrfs-progam for end-to-end tests with a remote backup repository."""
  def setUp(self):
    """Determine a directory to use on the remote host."""
    def tmpdirpath():
      """Get the path to a temporary directory that does not exist.

        Note: tempfile.mktemp provides a superset of the functionality
              this function provides but got deprecated.
      """
      d = mkdtemp()
      rmdir(d)
      return d

    with defer() as d:
      super().setUp()
      d.defer(super().tearDown)

      self._backups = join(tmpdirpath(), "backup")
      d.release()


  # TODO: We still require a test that backs up data to a native remote
  #       repository. However, that requires a btrfs file system to
  #       exist at a particular location on the remote host which is not
  #       so trivial to have.


  def testSshRun(self):
    """Test backup and restore over an SSH connection to a remote host."""
    def backup(*options):
      """Invoke the program to backup snapshots/subvolumes to a remote host."""
      options = list(options)
      options += [
        "--remote-cmd=/usr/bin/ssh %s" % host,
        "--snapshot-ext=bin",
        "--recv-filter=/bin/dd of={file}",
        "--no-read-stderr",
      ]
      self.backup(*options)

    def restore(src, dst, *options):
      """Invoke the program to restore snapshots/subvolumes from a remote host."""
      options = list(options)
      options += [
        "--remote-cmd=/usr/bin/ssh %s" % host,
        "--snapshot-ext=bin",
        "--send-filter=/bin/dd if={file}",
        "--no-read-stderr",
      ]
      self.restore(src, dst, *options)

    try:
      SSH = findCommand("ssh")
    except FileNotFoundError:
      raise SkipTest("SSH not found")

    try:
      host = environ["TEST_SSH_HOST"]
    except KeyError:
      raise SkipTest("TEST_SSH_HOST environment variable not set")

    with defer() as d:
      # This part is a bit tricky. We do not know the directory
      # structure on the remote host. We only have a path that is unique
      # on our local machine. We try to create it on the remote host to
      # work on it later on.
      execute(SSH, host, "mkdir -p %s" % self._backups, stderr=None)
      d.defer(lambda: execute(SSH, host, "rm -r %s" % self._backups, stderr=None))
      self.performTest(backup, restore, self._snapshots, self._backups)


if __name__ == "__main__":
  main()
