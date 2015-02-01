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
from deso.btrfs.argv import (
  insert as insertArg,
  reorder as reorderArg,
)
from sys import (
  argv as sysargv,
  stderr,
)
from os import (
  extsep,
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
  Namespace,
  SUPPRESS,
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


def checkSnapshotExtension(string, namespace, backup=True):
  """Validate the given snapshot extension parameter."""
  if string.startswith(extsep):
    error = "Extension must not start with \"%s\"." % extsep
    raise ArgumentTypeError(error)

  # We require that the namespace is already fully set up with the
  # appropriate filter argument. This constraint is enforced by
  # reordering the arguments before parsing them such that the snapshot
  # extension argument appears (and is evaluated) last.
  if backup:
    if not namespace.recv_filters:
      error = "This option must be used in conjunction with --recv-filter."
      raise ArgumentTypeError(error)
  else:
    if not namespace.send_filters:
      error = "This option must be used in conjunction with --send-filter."
      raise ArgumentTypeError(error)

  # There are different ways the {file} string can be provided which
  # depend on the command used. It might be part of a short option, a
  # long option, or it can be a stand alone argument. We do not care as
  # long as it does exist and so just create a string out of the
  # respective filter command and scan it instead of inspecting every
  # single argument of the command.
  if backup:
    if not "{file}" in " ".join(namespace.recv_filters[-1]):
      error = "The last receive filter must contain the \"{file}\" string."
      raise ArgumentTypeError(error)
  else:
    if not "{file}" in " ".join(namespace.send_filters[0]):
      error = "The first send filter must contain the \"{file}\" string."
      raise ArgumentTypeError(error)

  # The extension we store always includes the separator.
  return "%s%s" % (extsep, string)


def reverse(_, namespace):
  """Helper function to reverse arguments during parsing."""
  # In case the reverse option was given we swap the repositories and
  # the filters.
  with alias(namespace) as ns:
    if ns.reverse:
      ns.src, ns.dst = ns.dst, ns.src
      ns.send_filters, ns.recv_filters = ns.recv_filters, ns.send_filters

  return None


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


def addOptionalArgs(parser, namespace, backup):
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
  # A helper option that is used to perform the argument reordering
  # during parsing.
  parser.add_argument(
    "--reverse-hidden-helper", action="store", default=None,
    dest="reverse_hidden_helper", help=SUPPRESS,
    type=lambda x: reverse(x, namespace),
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

  if backup:
    text = "Extension to use for storing a snapshot file. Only allowed "\
           "in conjunction with a custom receive filter that stores data "\
           "in a file (with the given extension) rather than to "\
           "deserialize the stream into a btrfs subvolume. In this case, "\
           "the very last receive filter must contain the string "\
           "\"{file}\" (without quotes) which will be replaced by the "\
           "file name of the snapshot to create. The filter must ensure "\
           "to save the data it received on stdin (and potentially "\
           "processed) into the given file."
  else:
    text = "Extension to use for identifying a snapshot file. Only "\
           "allowed in conjunction with a custom send filter that reads "\
           "data from multiple files (with the given extension) rather "\
           "than to serialize btrfs snapshots or subvolumes. In this "\
           "case, the first send filter must contain the string "\
           "\"{file}\" (without quotes). The argument containing this "\
           "string will be replicated for each file to send. The filter "\
           "must ensure to output the (potentially processed) data to "\
           "stdout."

  # Unfortunately, the only acceptable way to allow for proper checking
  # of all constraints which the filters have to satisfy in case
  # --snapshot-ext is provided, is to work on the ArgumentParser's
  # namespace object here. Since the ArgumentParser parses arguments in
  # the order they are supplied on the command line (as opposed to the
  # order they were added in), we rely on the fact that the
  # --snapshot-ext option is at the end of the argument vector here. The
  # reorderArg invocation used earlier enforces this property.
  parser.add_argument(
    "--snapshot-ext", action="store", dest="extension", metavar="extension",
    type=lambda x: checkSnapshotExtension(x, namespace, backup),
    help=text,
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


def addBackupParser(parser, namespace):
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
  addOptionalArgs(optional, namespace, backup=True)
  addStandardArgs(optional)


def addRestoreParser(parser, namespace):
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
  addOptionalArgs(optional, namespace, backup=False)
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
  # We need access to the namespace object that parse_args() works on.
  namespace = Namespace()
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

  addBackupParser(subparsers, namespace)
  addRestoreParser(subparsers, namespace)

  # Note that argv contains the path to the program as the first element
  # which we kindly ignore. Furthermore, we do some trickery to have
  # proper argument checking: For the --snapshot-ext option we perform
  # various checks (see checkSnapshotExtension). For this checking to
  # work the option has to be evaluated after all filter options. To
  # that end, we move it to the end of the options because the
  # ArgumentParser evaluates arguments in the order in which they are
  # provided in the argument vector. In order to have less branching in
  # various cases, we want to evaluate the --reverse option on the fly.
  # The problem there is that it does not accept an argument. So we
  # insert an artificial, undocumented option that performs the checking
  # (--reverse-hidden-helper). Because --snapshot-ext already requires
  # properly ordered arguments, the hidden reverse helper option has to
  # be evaluated before the former (it also has to be evaluated after
  # the actual --reverse option, but that is guaranteed since we insert
  # it at the end).
  args = argv[1:].copy()
  args = insertArg(args, ["--reverse-hidden-helper", "42"])
  args = reorderArg(args, "--snapshot-ext")
  parser.parse_args(args, namespace)

  with alias(namespace) as ns:
    # The namespace's appended list arguments are stored as a list of
    # list of strings. Convert each to a list of strings.
    subvolumes = [x for x, in ns.subvolumes]
    send_filters = [x for x, in ns.send_filters] if ns.send_filters else None
    recv_filters = [x for x, in ns.recv_filters] if ns.recv_filters else None

    if ns.command == "backup":
      return run(lambda x: x.backup, subvolumes, ns.src, ns.dst,
                 send_filters=send_filters,
                 recv_filters=recv_filters,
                 read_err=ns.read_err,
                 remote_cmd=ns.remote_cmd,
                 keep_for=ns.keep_for,
                 debug=ns.debug)
    elif ns.command == "restore":
      return run(lambda x: x.restore, subvolumes, ns.src, ns.dst,
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
