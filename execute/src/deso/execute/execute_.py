# execute_.py

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

"""Functions for command execution."""

from os import (
  devnull,
)
from subprocess import (
  PIPE,
  Popen,
  check_call,
)


def executeAndRead(*args):
  """Execute a command synchronously and retrieve its stdout output."""
  with open(devnull) as null:
    with Popen(args, stdin=null, stdout=PIPE, stderr=null, close_fds=True) as process:
      # Wait for process to finish and retrieve output.
      data, _ = process.communicate()
      # Remove null termination byte.
      return data[:-1]


def execute(*args):
  """Execute a program synchronously."""
  with open(devnull) as null:
    check_call(args, stdin=null, stdout=null, stderr=null, close_fds=True)
