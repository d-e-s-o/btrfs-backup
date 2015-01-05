# testExecute.py

#/***************************************************************************
# *   Copyright (C) 2014-2015 deso (deso@posteo.net)                        *
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
  findCommand,
  formatPipeline,
  pipeline,
  pipelineAndRead,
)
from os import (
  remove,
)
from os.path import (
  isfile,
)
from tempfile import (
  mktemp,
)
from unittest import (
  TestCase,
  main,
)


_TRUE = findCommand("true")
_FALSE = findCommand("false")
_ECHO = findCommand("echo")
_TOUCH = findCommand("touch")
_TR = findCommand("tr")
_DD = findCommand("dd")
_URAND = "/dev/urandom"


class TestExecute(TestCase):
  """A test case for command execution functionality."""
  def testExecuteAndNoOutput(self):
    """Test command execution and output retrieval for empty output."""
    output = executeAndRead(_TRUE)
    self.assertEqual(output, b"")


  def testExecuteAndOutput(self):
    """Test command execution and output retrieval."""
    output = executeAndRead(_ECHO, "success")
    self.assertEqual(output, b"success\n")


  def testExecuteAndOutputMultipleLines(self):
    """Test command execution with multiple lines of output."""
    string = "first-line\nsuccess"
    output = executeAndRead(_ECHO, string)
    self.assertEqual(output, bytes(string + "\n", "utf-8"))


  def testExecuteThrowsOnCommandFailure(self):
    """Verify that a failing command causes an exception to be raised."""
    with self.assertRaises(ChildProcessError):
      execute(_FALSE)


  def testFormatPipeline(self):
    """Test conversion of a series of commands into a string."""
    commands = [
      [_ECHO, "test"],
      [_TR, "t", "z"],
      [_TR, "z", "t"],
    ]
    expected = "{echo} test | {tr} t z | {tr} z t".format(echo=_ECHO, tr=_TR)

    self.assertEqual(formatPipeline(commands), expected)


  def testPipelineSingleProgram(self):
    """Verify that a pipeline can run a single program."""
    path = mktemp()
    commands = [[_TOUCH, path]]

    self.assertFalse(isfile(path))
    pipeline(commands)
    self.assertTrue(isfile(path))

    remove(path)


  def testPipelineMultiplePrograms(self):
    """Verify that a pipeline can run two and more programs."""
    def doTest(intermediates):
      """Actually perform the test for a given pipeline depth."""
      tmp_file = mktemp()
      identity = [_TR, "a", "a"]
      commands = [
        [_ECHO, "test-abc-123"],
        [_DD, "of=%s" % tmp_file],
      ]

      commands[1:1] = [identity] * intermediates

      self.assertFalse(isfile(tmp_file))
      pipeline(commands)
      self.assertTrue(isfile(tmp_file))

      remove(tmp_file)

    for i in range(0, 4):
      doTest(i)


  def testPipelineWithRead(self):
    """Test execution of a pipeline and reading the output."""
    commands = [
      [_ECHO, "suaaerr"],
      [_TR, "a", "c"],
      [_TR, "r", "s"],
    ]
    output = pipelineAndRead(commands)

    self.assertEqual(output, b"success\n")


  def testPipelineWithExcessiveRead(self):
    """Verify that we do not deadlock when receiving large quantities of data."""
    megabytes = 32
    commands = [
      [_DD, "bs=%s" % (1024*1024), "count=%s" % megabytes, "if=%s" % _URAND],
    ]
    output = pipelineAndRead(commands)

    self.assertEqual(len(output), megabytes*1024*1024)


  def testPipelineWithFailingCommand(self):
    """Verify that a failing command in a pipeline fails the entire execution."""
    identity = [_TR, "a", "a"]
    commands = [
      [_ECHO, "test-abc-123"],
      identity,
      [_FALSE],
    ]

    # Run twice, once with failing command at the end and once somewhere
    # in the middle.
    for _ in range(2):
      with self.assertRaises(ChildProcessError):
        pipeline(commands)

      commands += [identity]


if __name__ == "__main__":
  main()
