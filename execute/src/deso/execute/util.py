# util.py

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

"""Utility functionality related to command execution."""

from os import (
  environ,
  pathsep,
)
from os.path import (
  isfile,
  join,
)


def findCommand(name):
  """Given a name, find the path to a command."""
  try:
    path = environ["PATH"]
  except KeyError:
    raise EnvironmentError("Unable to find PATH variable")

  dirs = path.split(pathsep)

  for d in dirs:
    f = join(d, name)
    if isfile(f):
      return f

  raise FileNotFoundError("No command named '%s' found in PATH (%s)" % (name, path))
