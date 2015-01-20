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
  stderr,
)
from argparse import (
  ArgumentParser,
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


def run(subvolumes, src_repo, dst_repo, **kwargs):
  """Start actual execution."""
  try:
    # This import pulls in all required modules and we check for
    # availability of all required commands. If one is not available, we
    # bail out here.
    from deso.btrfs.program import Program
  except FileNotFoundError as e:
    print("A command was not found:\n\"%s\"" % e, file=stderr)
    return 1

  try:
    program = Program(subvolumes, src_repo, dst_repo)
    program.run(**kwargs)
    return 0
  except ChildProcessError as e:
    print("Execution failure:\n\"%s\"" % e, file=stderr)
    return 2
  except Exception as e:
    print("A problem occurred:\n\"%s\"" % e, file=stderr)
    return 3


def main(argv):
  """The main function parses the program arguments and reacts on them."""
  parser = ArgumentParser(prog=name(), add_help=False,
                          description="%s -- %s" % (name(), description()))
  parser.add_argument(
    "src", action="store", metavar="source-repo",
    help="The path to the source repository.",
  )
  parser.add_argument(
    "dst", action="store", metavar="destination-repo",
    help="The path to the destination repository.",
  )
  parser.add_argument(
    "-h", "--help", action="help",
    help="Show this help message and exit.",
  )
  parser.add_argument(
    "-r", "--restore", action="store_true", dest="restore", default=False,
    help="Restore from a backup repository rather than saving to it. "
         "This option triggers the opposite behavior to what is done by "
         "default.",
  )
  parser.add_argument(
    "--reverse", action="store_true", dest="reverse", default=False,
    help="Reverse (i.e., swap) the source and destination repositories.",
  )
  parser.add_argument(
    "-s", "--subvolume", action="append", metavar="subvolume", nargs=1,
    dest="subvolumes", required=True,
    help="Path to a subvolume to include in the backup. Can be supplied "
         "multiple times to include more than one subvolume.",
  )
  parser.add_argument(
    "--snapshots-only", action="store_true", dest="snapshots_only",
    default=False,
    help="Restore only snapshots, not the entire source subvolume. "
         "Valid only in restoration mode, i.e., together with "
         "-r/--restore.",
  )
  parser.add_argument(
    "--version", action="version", version="%s %s" % (name(), version()),
    help="Show the program\'s version and exit.",
  )

  # Note that argv contains the path to the program as the first element
  # which we kindly ignore.
  namespace = parser.parse_args(argv[1:])

  with alias(namespace) as ns:
    # The namespace's subvolumes are stored as a list of list of
    # strings. Convert it to a list of strings.
    subvolumes = [x for x, in ns.subvolumes]

    if ns.reverse:
      src_repo, dst_repo = ns.dst, ns.src
    else:
      src_repo, dst_repo = ns.src, ns.dst

    return run(subvolumes, src_repo, dst_repo, restore=ns.restore,
               snapshots_only=ns.snapshots_only)
