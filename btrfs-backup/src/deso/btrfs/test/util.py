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

"""Utility functions for the testing environment."""

from os import (
  environ,
)
from tempfile import (
  mkdtemp as mkdtemp_,
  mkstemp as mkstemp_,
  mktemp as mktemp_,
)


def _getTestDir():
  """Retrieve the directory where to run tests in."""
  if "TEST_TMP_DIR" in environ:
    return environ["TEST_TMP_DIR"]
  else:
    return None


def mkdtemp(*args, **kwargs):
  """Wrapper around mkdtemp that honors the TEST_TMP_DIR environment variable."""
  return mkdtemp_(*args, dir=_getTestDir(), **kwargs)


def mkstemp(*args, **kwargs):
  """Wrapper around mkstemp that honors the TEST_TMP_DIR environment variable."""
  return mkstemp_(*args, dir=_getTestDir(), **kwargs)
