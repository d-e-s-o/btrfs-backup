# testArgv.py

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

"""Test the argv module."""

from deso.btrfs.argv import (
  insert,
)
from unittest import (
  main,
  TestCase,
)


class TestArgv(TestCase):
  """Test case for the argv related functionality."""
  def testInsertArg(self):
    """Verify insertion of arguments works as expected."""
    arg = "--test"
    self.assertEqual(insert([], [arg]), [arg])
    self.assertEqual(insert(["--"], [arg]), [arg, "--"])
    self.assertEqual(insert(["--", "arg"], [arg]), [arg, "--", "arg"])

    args = ["--test2", "--", "arg"]
    expected = ["--test2", arg, "--", "arg"]
    self.assertEqual(insert(args, [arg]), expected)


if __name__ == "__main__":
  main()
