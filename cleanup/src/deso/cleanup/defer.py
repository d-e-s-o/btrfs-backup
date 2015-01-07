# defer.py

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

"""A module for deferred function invocation functionality."""


def defer():
  """Request a new defer context.

    The defer functionality is meant to be used in conjunction with
    'with' blocks, like so:
    with defer() as d:
      d.defer(doSth)
      d.defer(lambda: print("Executed"))
      raise Exception()

    The result is that even in the face of exceptions the doSth()
    function call and the print with the given arguments are executed on
    block exit (but not beforehand).
    This functionality allows to perform clean up in an exception-safe
    manner.
  """
  class _Function:
    """A function wrapper guarding against multiple executions."""
    def __init__(self, function):
      """Initialize a function wrapper."""
      self._function = function

    def __call__(self):
      """On a call of the object invoke the underlying function."""
      if self._function is not None:
        self._function()
        # Mark function as executed.
        self._function = None

  class _Defer:
    """Objects of this class act as a context with which to register deferred functions."""
    def __init__(self):
      """Initialize a defer object to make it ready for use."""
      self._functions = []

    def __enter__(self):
      """The block enter handler just returns a reference to this object."""
      return self

    def __exit__(self, type_, value, traceback):
      """The block exit handler destroys the object."""
      self.destroy()

    def defer(self, function):
      """Register a deferred function invocation."""
      result = _Function(function)
      self._functions += [result]
      return result

    def destroy(self):
      """Destroy the object, invoke all deferred functions."""
      # Always invoke in reverse order of registration.
      for function in reversed(self._functions):
        function()

  return _Defer()
