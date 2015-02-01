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


def remove(args, option):
  """Remove an option along with an argument from an argument vector."""
  i = 0
  while i < len(args):
    # There are two forms in which an option can appear in conjunction
    # with an argument after parsing. The first one is as two separate
    # arguments if both were separated using whitespaces.
    if args[i] == option:
      result = [args[i], args[i+1]]
      del args[i+1]
      del args[i]
      return args, result

    # The second one is as a single argument in which case they must
    # have been separated by an equality sign ('=').
    if args[i].startswith(option):
      assert "=" in args[i]
      result = [args[i]]
      del args[i]
      return args, result

    i += 1
  return args, None


def reorder(args, option):
  """Move an option along with its argument to the end of the given argument vector."""
  args, arg = remove(args, option)
  if arg:
    insert(args, arg)
  return args
