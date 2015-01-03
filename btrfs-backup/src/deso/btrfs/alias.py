# alias.py

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

"""Module to contain the variable aliasing functionality."""


def alias(variable):
  """Provide an additional name for a variable temporarily.

    The aliasing functionality is meant to be used in conjunction with
    'with' blocks, like so:
    self._incredibly_long_variable_name = Object(...)
    with alias(self._incredibly_long_variable_name) as var:
      var.doSth()
      var.doSthElse()
  """
  class _Alias:
    """A wrapper object used for providing a new name for a variable.

      Notes: We rely on Python's closures here to avoid creating a
             separate member variable.
    """
    def __enter__(self):
      """The block enter handler just returns the variable."""
      return variable

    def __exit__(self, type_, value, traceback):
      """The block exit handler does nothing."""
      pass

  return _Alias()
