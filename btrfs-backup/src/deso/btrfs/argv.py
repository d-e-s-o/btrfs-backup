# argv.py

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

"""Functionality for modifying an argv style argument vector."""


def insert(args, arg):
  """Insert an argument at the end of an argument vector."""
  # Depending on whether there exists a -- separator we have to insert
  # the argument just in front of it or truly at the end of the vector.
  try:
    l = len(args)
    i = l - list(reversed(args)).index("--") - 1
  except ValueError:
    i = l

  args[i:i] = arg
  return args
