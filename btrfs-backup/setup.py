#!/usr/bin/env python

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

from os.path import (
  dirname,
  join,
  pardir,
)
from setuptools import (
  setup,
)
from sys import (
  path as syspath,
)


def _importAndRun(work):
  """Import the program's main module and pass it to a work function."""
  root = join(dirname(__file__), pardir)

  syspath.insert(1, join(root, "cleanup", "src"))
  syspath.insert(1, join(root, "execute", "src"))
  syspath.insert(1, join(root, "btrfs-backup", "src"))
  from deso.btrfs import main
  syspath.pop(1)
  syspath.pop(1)
  syspath.pop(1)
  return work(main)


def retrieveName():
  """Retrieve the program's name."""
  return _importAndRun(lambda x: x.name())


def retrieveVersion():
  """Retrieve the program's version."""
  return _importAndRun(lambda x: x.version())


def retrieveDescription():
  """Retrieve a description of the program."""
  return _importAndRun(lambda x: x.description())


setup(
  name = retrieveName(),
  author = "Daniel Mueller",
  author_email = "deso@posteo.net",
  maintainer = "Daniel Mueller",
  maintainer_email = "deso@posteo.net",
  version = retrieveVersion(),
  description = retrieveDescription(),
  url = "https://github.com/d-e-s-o/btrfs-backup",
  classifiers = [
    "Environment :: Console",
    "Operating System :: POSIX",
    "Programming Language :: Python",
    "Programming Language :: Python :: 3.3",
    "Programming Language :: Python :: 3.4",
    "Topic :: System :: Systems Administration",
    "Topic :: Utilities :: System",
  ],
  keywords = "btrfs backup",
  license = "GPLv3",
  packages = [
    "deso.btrfs",
    "deso.btrfs.test",
  ],
  package_dir = {
    "deso.btrfs": join("src", "deso", "btrfs"),
    "deso.btrfs.test": join("src", "deso", "btrfs", "test"),
  },
  scripts = [
    join("src", "deso", "btrfs", "btrfs-backup"),
  ],
  test_suite = "deso.btrfs.test.allTests",
  tests_require = [
    "mock>=1.0.1",
  ],
  install_requires = [
    "argparse>=1.1",
    "setuptools>=7.0",
  ],
  zip_safe=True,
)
