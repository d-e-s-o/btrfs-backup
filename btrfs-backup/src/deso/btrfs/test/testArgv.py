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
  reorder,
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


  def testReorderArgs(self):
    """Verify reordering of arguments works as expected."""
    arg = "--test-arg"

    # Case 1) Only a single argument that is the one to reorder. Nothing
    #         should happen.
    args = ["%s=test" % arg]
    self.assertEqual(reorder(args, arg), args)

    # Case 2) Again a single argument but this time not connected by '='
    #         but rather split as done by automated argument splitting.
    args = [arg, "test"]
    self.assertEqual(reorder(args, arg), args)

    # Case 3) The argument intermixed with other ones.
    args = ["--test1", "%s=test" % arg, "--test2"]
    expected = ["--test1", "--test2", "%s=test" % arg]
    self.assertEqual(reorder(args, arg), expected)

    # Case 4) The argument intermixed and also split in two again.
    args = ["--test1", arg, "test", "--test2"]
    expected = ["--test1", "--test2", arg, "test"]
    self.assertEqual(reorder(args, arg), expected)

    # Case 5) The argument intermixed with other ones. Also verify that
    #         the passed in argument vector is modified in place.
    args = ["--test1", arg, "test", "--test2", "--", "test3"]
    expected = ["--test1", "--test2", arg, "test", "--", "test3"]
    reordered = reorder(args, arg)

    self.assertEqual(args, reordered)
    self.assertEqual(reordered, expected)


if __name__ == "__main__":
  main()
