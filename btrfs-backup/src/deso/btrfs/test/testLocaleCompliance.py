# testLocaleCompliance.py

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

"""Test that the program works independently of the used locale."""

from deso.btrfs.repository import (
  _TIME_FORMAT,
)
from datetime import (
  datetime,
)
from functools import (
  cmp_to_key,
)
from locale import (
  Error,
  LC_COLLATE,
  getlocale,
  locale_alias,
  setlocale,
  strcoll,
)
from random import (
  shuffle,
)
from unittest import (
  TestCase,
  main,
)


class TestLocaleCompliance(TestCase):
  """Test compliance with various locales."""
  def testSortability(self):
    """Verify that sorting with our time stamp format works independently of the locale."""
    def testSort():
      """Perform the sort test with the current locale."""
      datetimes = [
        datetime(1970, 1,  1,  0,  0,  0),
        datetime(1970, 2,  1,  0,  0,  0),
        datetime(1988, 10, 13, 14, 33, 37),
        datetime(1995, 12, 31, 23, 59, 59),
        datetime(2000, 1,  1,  0,  0,  0),
        datetime(2014, 2,  28, 17, 1,  48),
        datetime(2015, 1,  4,  9,  34, 20),
      ]
      expected = [
        "1970-01-01_00:00:00",
        "1970-02-01_00:00:00",
        "1988-10-13_14:33:37",
        "1995-12-31_23:59:59",
        "2000-01-01_00:00:00",
        "2014-02-28_17:01:48",
        "2015-01-04_09:34:20",
      ]
      timestamps = [datetime.strftime(d, _TIME_FORMAT) for d in datetimes]
      shuffle(timestamps)
      timestamps.sort(key=cmp_to_key(strcoll))
      self.assertEqual(timestamps, expected)

    previous = getlocale(LC_COLLATE)
    locales = set(locale_alias.values())

    # We have a list of all (Python-) known locales, a lot of which will
    # not be supported by the underlying operating system. We can only
    # do a best effort approach here and try our sorting with locales
    # that actually are supported.
    for locale in locales:
      try:
        setlocale(LC_COLLATE, locale)
        testSort()
      except Error:
        # Ignore unsupported locales.
        pass

    setlocale(LC_COLLATE, previous)


if __name__ == "__main__":
  main()
