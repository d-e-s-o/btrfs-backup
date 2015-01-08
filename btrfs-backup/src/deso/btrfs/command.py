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

from deso.execute import (
  findCommand,
)


_BTRFS = findCommand("btrfs")


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


def serialize(subvolume, parent=None):
  """Retrieve the command to serialize a btrfs subvolume into a byte stream."""
  options = []
  if parent:
    # We use both the parent and clone-source options here. Clone-source
    # indicates that data from the given snapshot(s) is used to create
    # the new snapshot, i.e., better sharing can happen. The parent
    # option in general indicates that we are sending an incremental
    # snapshot only, that is, only the differences between 'snapshot'
    # and 'parent' are put into the byte stream.
    options += ["-p", parent, "-c", parent]

  return [_BTRFS, "send"] + options + [subvolume]


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
  # Note: We include a time stamp into a snapshot's name which is
  #       formatted in a way so as to ensure sorting a list of snapshots
  #       is in ascending order with respect to the time each was
  #       created at.
  # Note: We do not pass in the -s option here. The reason is that once
  #       we send and received a snapshot, the property of it being a
  #       snapshot is lost. The only property that is preserved is it
  #       being read-only.
  return [_BTRFS, "subvolume", "list", "--sort=path", "-r", "-o", directory]


def diff(subvolume, generation):
  """Retrieve a command to query a list of changed files for the given subvolume.

    This function creates a command that, given a btrfs subvolume and a
    previous generation ID, determines the files that have been changed.
  """
  return [_BTRFS, "subvolume", "find-new", subvolume, generation]
