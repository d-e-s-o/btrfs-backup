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
  require throughout the program, e.g., for creating and deleting
  subvolumes (only used for testing), listing, creating and deleting
  snapshots, sending and receiving them, and more.
"""

_BTRFS = "/sbin/btrfs"


def create(subvolume):
  """Retrieve the command to create a new btrfs subvolume."""
  return [_BTRFS, "subvolume", "create", subvolume]


def delete(subvolume):
  """Retrieve the command to delete a btrfs subvolume."""
  return [_BTRFS, "subvolume", "delete", subvolume]


def show(subvolume):
  """Retrieve the command to show information about a btrfs subvolume."""
  return [_BTRFS, "subvolume", "show", subvolume]


def snapshot(source, destination):
  """Retrieve the command to create a read-only snapshot of a subvolume."""
  return [_BTRFS, "subvolume", "snapshot", "-r", source, destination]


def sync(filesystem):
  """Retrieve the command to sync the given btrfs file system to disk.

    Notes:
      A sync operation should be performed before attempting to send
      (i.e., serialize) a btrfs snapshot.
  """
  return [_BTRFS, "filesystem", "sync", filesystem]


def serialize(subvolume):
  """Retrieve the command to serialize a btrfs subvolume into a byte stream."""
  return [_BTRFS, "send", subvolume]


def deserialize(data):
  """Retrieve the command to deserialize a btrfs subvolume from a byte stream."""
  return [_BTRFS, "receive", data]


def snapshots(directory):
  """Retrieve a command to list all snapshots in a given directory.

    Notes:
      Please be aware of the wrong handling of the -o parameter in
      btrfs, leading to *not* necessarily only snapshots below the given
      directory being returned.
  """
  return [_BTRFS, "subvolume", "list", "-s", "-r", "-o", directory]


def diff(subvolume, generation):
  """Retrieve a command to query a list of changed files for the given subvolume.

    This function creates a command that, given a btrfs subvolume and a
    previous generation ID, determines the files that have been changed.
  """
  return [_BTRFS, "subvolume", "find-new", subvolume, generation]
