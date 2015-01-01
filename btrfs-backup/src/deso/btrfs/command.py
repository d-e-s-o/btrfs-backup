# command.py

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

"""Functions for creating btrfs commands ready for execution.

  In order to perform btrfs related actions we interface with the
  btrfs(8) command. This command provides the necessary functionality we
  require throughout the program.
"""

_BTRFS = "/sbin/btrfs"


def create(subvolume):
  """Retrieve the command to create a new btrfs subvolume."""
  return [_BTRFS, "subvolume", "create", subvolume]


def delete(subvolume):
  """Retrieve the command to delete a btrfs subvolume."""
  return [_BTRFS, "subvolume", "delete", subvolume]


def snapshot(source, destination):
  """Retrieve the command to create a read-only snapshot of a subvolume."""
  return [_BTRFS, "subvolume", "snapshot", "-r", source, destination]
