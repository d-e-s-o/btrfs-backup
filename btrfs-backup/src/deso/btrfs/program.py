# program.py

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

"""The program module wraps Repository functionality for easy access from the main module."""

from deso.btrfs.repository import (
  Repository,
  restore as restore_,
  sync,
)


class Program:
  """A program object performs the actual work of synchronizing two repositories."""
  def __init__(self, subvolumes, src_repo, dst_repo):
    """Create a new Program object using the given subvolumes and repositories."""
    self._subvolumes = subvolumes
    self._src_repo = src_repo
    self._dst_repo = dst_repo


  def backup(self, send_filters=None, recv_filters=None, read_err=True,
             remote_cmd=None, extension=None, keep_for=None):
    """Backup subvolumes to a repository."""
    src = Repository(self._src_repo, send_filters, read_err)
    dst = Repository(self._dst_repo, recv_filters, read_err, remote_cmd)

    sync(self._subvolumes, src, dst)
    if keep_for:
      src.purge(self._subvolumes, keep_for)


  def restore(self, send_filters=None, recv_filters=None, read_err=True,
              remote_cmd=None, extension=None, snapshots_only=False):
    """Restore subvolumes or snapshots from a repository."""
    src = Repository(self._src_repo, send_filters, read_err, remote_cmd)
    dst = Repository(self._dst_repo, recv_filters, read_err)

    restore_(self._subvolumes, src, dst, snapshots_only)
