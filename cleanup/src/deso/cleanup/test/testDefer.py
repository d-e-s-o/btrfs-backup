# testDefer.py

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

"""Test function defer functionality."""

from deso.cleanup import (
  defer,
)
from unittest import (
  TestCase,
  main,
)


class Counter:
  """A mutable counter object."""
  def __init__(self):
    """Initialize the counter with zero."""
    self._count = 0


  def increment(self):
    """Increment the counter's value."""
    self._count += 1


  def set(self, value):
    """Directly set the counter's value."""
    self._count = value


  def count(self):
    """Retrieve the counter's value."""
    return self._count


class TestExecute(TestCase):
  """A test case for testing of the defer functionality."""
  def setUp(self):
    """Create a new Counter object ready to use."""
    self._counter = Counter()


  def testDefer(self):
    """Verify that with non-exceptional control flow a deferred function is invoked."""
    self.assertEqual(self._counter.count(), 0)

    with defer() as d:
      d.defer(self._counter.increment)
      # Must not be incremented immediately, only after block exit.
      self.assertEqual(self._counter.count(), 0)

    self.assertEqual(self._counter.count(), 1)


  def testDeferWithException(self):
    """Verify that defer functionality behaves correctly in the face of exceptions."""
    with self.assertRaises(Exception):
      with defer() as d:
        d.defer(self._counter.increment)
        raise Exception()

    self.assertEqual(self._counter.count(), 1)


  def testDeferHasCorrectOrder(self):
    """Verify that deferred functions are invoked in the right order."""
    with defer() as d:
      d.defer(lambda: self._counter.set(2))
      d.defer(lambda: self._counter.set(1))

    # Functions should be invoked in reverse order to honor potential
    # dependencies between objects.
    self.assertEqual(self._counter.count(), 2)


  def testDeferNested(self):
    """Verify that defer blocks can be nested."""
    with self.assertRaises(Exception):
      with defer() as d1:
        # Note that when this expression gets evaluated the value of
        # self._counter.count() should be five.
        d1.defer(lambda: self._counter.set(self._counter.count() * 3))

        with defer() as d2:
          # Increment d1 once more but in different block.
          d1.defer(self._counter.increment)
          # And now also let d2 change the value.
          d2.defer(lambda: self._counter.set(4))

          raise Exception()

    self.assertEqual(self._counter.count(), 15)


  def testDeferRunEarlyRunOnce(self):
    """Verify that we can invoke a deferred function early using the returned object."""
    with defer() as d:
      deferer = d.defer(self._counter.increment)
      deferer()
      self.assertEqual(self._counter.count(), 1)

    # Should not be run a second time.
    self.assertEqual(self._counter.count(), 1)


if __name__ == "__main__":
  main()
