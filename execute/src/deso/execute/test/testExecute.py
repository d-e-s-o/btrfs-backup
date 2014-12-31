# testExecute.py

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

"""Test command execution wrappers."""

from deso.execute import (
  execute,
  executeAndRead,
)
from subprocess import (
  CalledProcessError,
)
from unittest import (
  TestCase,
  main,
)


class TestExecute(TestCase):
  """A test case for command execution functionality."""
  def testExecuteAndNoOutput(self):
    """Test command execution and output retrieval for empty output."""
    output = executeAndRead("/bin/true")
    self.assertEqual(output, b"")


  def testExecuteAndOutput(self):
    """Test command execution and output retrieval."""
    output = executeAndRead("/bin/echo", "success")
    self.assertEqual(output, b"success")


  def testExecuteAndOutputMultipleLines(self):
    """Test command execution with multiple lines of output."""
    string = "first-line\nsuccess"
    output = executeAndRead("/bin/echo", string)
    self.assertEqual(output, bytes(string, "utf-8"))


  def testExecuteThrowsOnCommandFailure(self):
    """Verify that a failing command causes an exception to be raised."""
    with self.assertRaises(CalledProcessError):
      execute("/bin/false")


if __name__ == "__main__":
  main()
