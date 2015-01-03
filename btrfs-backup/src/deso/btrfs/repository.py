# repository.py

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

"""Repository related functionality.

  This program uses the abstraction of a repository to reason about
  which files to transfer in order to create a backup of a btrfs
  subvolume. A repository is a directory that contains or is supposed to
  contain snapshots.
"""

from datetime import (
  datetime,
)
from deso.btrfs.command import (
  snapshots as listSnapshots,
)
from deso.execute import (
  executeAndRead,
)
from os.path import (
  join,
)
from re import (
  compile as regex,
)


_TIME_FORMAT = "%Y-%m-%d_%H:%M:%S"
_ANY_STRING = r"."
_NUM_STRING = r"[0-9]"
_NUMS_STRING = r"{nr}+".format(nr=_NUM_STRING)
_DATE_STRING = r"{nr}{{4}}-{nr}{{2}}-{nr}{{2}}".format(nr=_NUM_STRING)
_TIME_STRING = r"{nr}{{2}}:{nr}{{2}}:{nr}{{2}}".format(nr=_NUM_STRING)
_PATH_STRING = r"{any}+".format(any=_ANY_STRING)
# The format of a line as retrieved by executing the command returned by
# the snapshots() function. Each line is expected to be following the
# pattern:
# ID A gen B cgen C top level D otime 2015-01-01 18:40:49 path PATH
_LIST_STRING = (r"^ID {nums} gen {nums} cgen {nums} top level {nums}"
                r" otime ({date}) ({time}) path ({path})$")
_LIST_REGEX = regex(_LIST_STRING.format(nums=_NUMS_STRING, date=_DATE_STRING,
                                        time=_TIME_STRING, path=_PATH_STRING))


def _parseListLine(line):
  """Parse a line of output for the command as returned by snapshots()."""
  m = _LIST_REGEX.match(line)
  if not m:
    raise ValueError("Invalid snapshot list: unable to match line \"%s\"" % line)

  date, time, path = m.groups()

  result = {}
  result["time"] = datetime.strptime("%s_%s" % (date, time), _TIME_FORMAT)
  result["path"] = path
  return result


def _snapshots(directory):
  """Retrieve a list of snapshots in a directory.

    Note:
      Because of a supposed bug in btrfs' handling of passed in
      directories, the output of this function is *not* necessarily
      limited to subvolumes *below* the given directory. See test case
      testRepositoryListNoSnapshotPresentInSubdir. For that matter,
      usage of this function is discouraged. Use the Repository's
      snapshots() method instead.
  """
  output = executeAndRead(*listSnapshots(directory))
  # We might retrieve an empty output if no snapshots were present. In
  # this case, just return early here.
  if not output:
    return []

  # Convert from byte array, remove the trailing new line, and split to
  # retrieve a list of lines.
  output = output.decode("utf-8")[:-1].split("\n")
  return [_parseListLine(line) for line in output]


class Repository:
  """This class represents a repository for snapshots."""
  def __init__(self, directory):
    """Initialize the object and bind it to the given directory."""
    self._directory = directory


  def snapshots(self):
    """Retrieve a list of snapshots in this repository."""
    return _snapshots(self._directory)


  def path(self, *components):
    """Form an absolute path by combining the given path components."""
    return join(self._directory, *components)
