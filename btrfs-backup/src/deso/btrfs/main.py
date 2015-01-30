# main.py

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

"""The main module interfaces with the user input and sets up bits required for execution."""

from deso.btrfs.alias import (
  alias,
)
from sys import (
  argv as sysargv,
  stderr,
)
from re import (
  compile as regex,
)
from datetime import (
  timedelta,
)
from argparse import (
  ArgumentParser,
  ArgumentTypeError,
  HelpFormatter,
)


def name():
  """Retrieve the name of the program."""
  return "btrfs-backup"


def description():
  """Retrieve a description of the program."""
  return "A simple and fast btrfs-based backup tool."


def version():
  """Retrieve the program's current version."""
  return "0.1"


def run(method, subvolumes, src_repo, dst_repo,
        send_filters=None, recv_filters=None, read_err=True,
        remote_cmd=None, debug=False, **kwargs):
  """Start actual execution."""
  try:
    # This import pulls in all required modules and we check for
    # availability of all required commands. If one is not available, we
    # bail out here.
    from deso.btrfs.program import Program
  except FileNotFoundError as e:
    if debug:
      raise
    print("A command was not found:\n\"%s\"" % e, file=stderr)
    return 1

  if remote_cmd:
    # TODO: Right now we do not support remote commands that contain
    #       spaces in their path. E.g., "/bin/connect to server" would
    #       not be a valid command.
    remote_cmd = remote_cmd.split()
  if send_filters:
    send_filters = [filt.split() for filt in send_filters]
  if recv_filters:
    recv_filters = [filt.split() for filt in recv_filters]

  try:
    program = Program(subvolumes, src_repo, dst_repo, send_filters,
                      recv_filters, read_err, remote_cmd)
    method(program)(**kwargs)
    return 0
  except ChildProcessError as e:
    if debug:
      raise
    print("Execution failure:\n\"%s\"" % e, file=stderr)
    return 2
  except Exception as e:
    if debug:
      raise
    print("A problem occurred:\n\"%s\"" % e, file=stderr)
    return 3


def duration(string):
  """Create a timedelta object from a duration string."""
  suffixes = {
    "S": timedelta(seconds=1),
    "M": timedelta(minutes=1),
    "H": timedelta(hours=1),
    "d": timedelta(days=1),
    "w": timedelta(weeks=1),
    "m": timedelta(weeks=4),
    "y": timedelta(weeks=52),
  }

  for suffix, duration_ in suffixes.items():
    expression = regex(r"^([1-9][0-9]*){s}$".format(s=suffix))
    m = expression.match(string)
    if m:
      amount, = m.groups()
      return int(amount) * duration_

  raise ArgumentTypeError("Invalid duration string: \"%s\"." % string)


def addStandardArgs(parser):
  """Add the standard arguments --version and --help to an argument parser."""
  parser.add_argument(
    "-h", "--help", action="help",
    help="Show this help message and exit.",
  )
  parser.add_argument(
    "--version", action="version", version="%s %s" % (name(), version()),
    help="Show the program\'s version and exit.",
  )


def addOptionalArgs(parser):
  """Add the optional arguments to a parser."""
  parser.add_argument(
    "--no-read-stderr", action="store_false", dest="read_err", default=True,
    help="Turn off reading of data from stderr. No information about "
         "the reason for a command failure except for the return code "
         "will be available. This option is helpful in certain cases "
         "where a command (likely a remote command) forks a child which "
         "stays alive longer than the actually run command. In such a "
         "case if we read the data from stderr we will effectively wait "
         "for the forked off command to terminate before continuing "
         "execution.",
  )
  parser.add_argument(
    "--remote-cmd", action="store", dest="remote_cmd", metavar="command",
    help="The command to use for running btrfs on a remote site. Needs "
         "to include the full path to the binary or script, e.g., "
         "\"/usr/bin/ssh server\".",
  )
  parser.add_argument(
    "--reverse", action="store_true", dest="reverse", default=False,
    help="Reverse (i.e., swap) the source and destination repositories "
         "as well as the send and receive filters.",
  )
  parser.add_argument(
    "--send-filter", action="append", default=None, dest="send_filters",
    metavar="command", nargs=1,
    help="A filter command applied in the snapshot send process. "
         "Multiple send filters can be supplied.",
  )
  parser.add_argument(
    "--recv-filter", action="append", default=None, dest="recv_filters",
    metavar="command", nargs=1,
    help="A filter command applied in the snapshot receive process. "
         "Multiple receive filters can be supplied.",
  )
  parser.add_argument(
    "--debug", action="store_true", dest="debug", default=False,
    help="Allow for exceptions to escape the program thereby producing "
         "full backtraces.",
  )


def addRequiredArgs(parser):
  """Add the various required arguments to a parser."""
  parser.add_argument(
    "src", action="store", metavar="source-repo",
    help="The path to the source repository.",
  )
  parser.add_argument(
    "dst", action="store", metavar="destination-repo",
    help="The path to the destination repository.",
  )
  parser.add_argument(
    "-s", "--subvolume", action="append", metavar="subvolume", nargs=1,
    dest="subvolumes", required=True,
    help="Path to a subvolume to include in the backup. Can be supplied "
         "multiple times to include more than one subvolume.",
  )


def addBackupParser(parser):
  """Add a parser for the backup command to another parser."""
  backup = parser.add_parser(
    "backup", add_help=False, formatter_class=SubLevelHelpFormatter,
    help="Backup one or more subvolumes.",
  )

  required = backup.add_argument_group("Required arguments")
  addRequiredArgs(required)

  optional = backup.add_argument_group("Optional arguments")
  optional.add_argument(
    "--keep-for", action="store", type=duration, metavar="duration",
    dest="keep_for",
    help="Duration how long to keep snapshots. Snapshots that are older "
         "than \'duration\' will be deleted from the source repository "
         "when the next backup is performed. A duration is specified by "
         "an amount (i.e., a number) along with a suffix. Valid "
         "suffixes are: S (seconds), M (minutes), H (hours), d (days), "
         "w (weeks), m (months), and y (years).",
  )
  addOptionalArgs(optional)
  addStandardArgs(optional)


def addRestoreParser(parser):
  """Add a parser for the restore command to another parser."""
  restore = parser.add_parser(
    "restore", add_help=False, formatter_class=SubLevelHelpFormatter,
    help="Restore subvolumes or snapshots from a repository.",
  )

  required = restore.add_argument_group("Required arguments")
  addRequiredArgs(required)

  optional = restore.add_argument_group("Optional arguments")
  optional.add_argument(
    "--snapshots-only", action="store_true", dest="snapshots_only",
    default=False,
    help="Restore only snapshots, not the entire source subvolume."
  )
  addOptionalArgs(optional)
  addStandardArgs(optional)


class TopLevelHelpFormatter(HelpFormatter):
  """A help formatter class for a top level parser."""
  def add_usage(self, usage, actions, groups, prefix=None):
    """Add usage information, overwrite the default prefix."""
    # Control flow is tricky here. Our invocation *might* come from the
    # sub-level parser or we might have been invoked directly. In the
    # latter case use our own prefix, otherwise just pass through the
    # given one.
    if prefix is None:
      prefix = "Usage: "

    super().add_usage(usage, actions, groups, prefix)


class SubLevelHelpFormatter(HelpFormatter):
  """A help formatter class for a sub level parser."""
  def add_usage(self, usage, actions, groups, prefix=None):
    """Add usage information, overwrite the default prefix."""
    super().add_usage(usage, actions, groups, "Usage: ")


def main(argv):
  """The main function parses the program arguments and reacts on them."""
  parser = ArgumentParser(prog=name(), add_help=False,
                          description="%s -- %s" % (name(), description()),
                          formatter_class=TopLevelHelpFormatter)
  subparsers = parser.add_subparsers(
    title="Subcommands", metavar="command", dest="command",
    help="A command to perform.",
  )
  subparsers.required = True
  optional = parser.add_argument_group("Optional arguments")
  addStandardArgs(optional)

  addBackupParser(subparsers)
  addRestoreParser(subparsers)

  # Note that argv contains the path to the program as the first element
  # which we kindly ignore.
  namespace = parser.parse_args(argv[1:])

  with alias(namespace) as ns:
    # The namespace's appended list arguments are stored as a list of
    # list of strings. Convert each to a list of strings.
    subvolumes = [x for x, in ns.subvolumes]
    send_filters = [x for x, in ns.send_filters] if ns.send_filters else None
    recv_filters = [x for x, in ns.recv_filters] if ns.recv_filters else None

    if ns.reverse:
      src_repo, dst_repo = ns.dst, ns.src
      send_filters, recv_filters = recv_filters, send_filters
    else:
      src_repo, dst_repo = ns.src, ns.dst
      send_filters, recv_filters = send_filters, recv_filters

    if ns.command == "backup":
      return run(lambda x: x.backup, subvolumes, src_repo, dst_repo,
                 send_filters=send_filters,
                 recv_filters=recv_filters,
                 read_err=ns.read_err,
                 remote_cmd=ns.remote_cmd,
                 keep_for=ns.keep_for,
                 debug=ns.debug)
    elif ns.command == "restore":
      return run(lambda x: x.restore, subvolumes, src_repo, dst_repo,
                 send_filters=send_filters,
                 recv_filters=recv_filters,
                 read_err=ns.read_err,
                 remote_cmd=ns.remote_cmd,
                 snapshots_only=ns.snapshots_only,
                 debug=ns.debug)
    else:
      assert False


if __name__ == "__main__":
  exit(main(sysargv))
