# testRepository.py

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

"""Test the repository functionality."""

from datetime import (
  datetime,
  timedelta,
)
from deso.btrfs.alias import (
  alias,
)
from deso.btrfs.command import (
  create,
  delete,
  deserialize,
  serialize,
  snapshot,
  sync,
)
from deso.btrfs.repository import (
  Repository,
  restore,
  _findCommonSnapshots,
  _snapshots,
  sync as syncRepos,
)
from deso.btrfs.test.btrfsTest import (
  BtrfsDevice,
  BtrfsRepositoryTestCase,
  BtrfsSnapshotTestCase,
  BtrfsTestCase,
  make,
  Mount,
)
from deso.execute import (
  execute,
)
from glob import (
  glob,
)
from os import (
  remove,
)
from os.path import (
  isfile,
  join,
  pardir,
)
from unittest import (
  main,
)
from unittest.mock import (
  patch,
)


class TestRepositoryBase(BtrfsTestCase):
  """Test basic repository functionality."""
  def testRepositoryInNonExistentDirectory(self):
    """Verify that creation of a repository in a non-existent directory fails."""
    directory = "a-non-existent-directory"
    regex = r"%s.*No such file or directory" % directory

    with self.assertRaisesRegex(ChildProcessError, regex):
      Repository(self._mount.path(directory))


  def testRepositoryListNoSnapshotPresent(self):
    """Verify that if no snapshot is present an empty list is returned."""
    repo = Repository(self._mount.path())
    self.assertEqual(repo.snapshots(), [])


  def testRepositorySubvolumeFindRootOnRoot(self):
    """Test retrieval of the absolute path of the btrfs root from the root."""
    with alias(self._mount) as m:
      repo = Repository(m.path())
      self.assertEqual(repo.root, m.path())


  def testRepositorySubvolumeFindRootFromBelowRoot(self):
    """Test retrieval of the absolute path of the btrfs root from a sub-directory."""
    with alias(self._mount) as m:
      repo = Repository(make(m, "dir"))
      self.assertEqual(repo.root, m.path())


  def testRepositorySubvolumeFindRootFromSubvolume(self):
    """Test retrieval of the absolute path of the btrfs root from a true subvolume."""
    with alias(self._mount) as m:
      repo = Repository(make(m, "root", subvol=True))
      self.assertEqual(repo.root, m.path())


  def testRepositoryFindCommonSnapshots(self):
    """Test the _findCommonSnapshots() function on various snapshot sets."""
    def makeTrueSnapshots(snaps):
      """Convert a list of snapshot paths into a list of snapshot dicts as used internally."""
      # Our internally used snapshots are made up not only of the path
      # but also the generation number. Assume it to be 0 here.
      return list(map(lambda x: {"path": x, "gen": 0}, snaps))

    def assertCommonality(snaps1, snaps2, expected):
      """Assert that two sets of snapshots have the expected common snapshots."""
      snaps1 = makeTrueSnapshots(snaps1)
      snaps2 = makeTrueSnapshots(snaps2)
      expected = makeTrueSnapshots(expected)

      self.assertEqual(list(_findCommonSnapshots(snaps1, snaps2)), expected)

    # Case 1) No commonality. One list empty.
    snaps1 = [
      "localhost-linux-x86_64-local-2015-01-09_15:39:47",
      "localhost-linux-x86_64-local-2015-01-09_16:57:16",
    ]
    assertCommonality(snaps1, [], [])

    # Case 2) Equal backed up subvolume. One common snapshot.
    snaps1 = [
      "localhost-linux-x86_64-local-2015-01-09_15:39:47",
      "localhost-linux-x86_64-local-2015-01-09_16:57:16",
    ]
    snaps2 = [
      "localhost-linux-x86_64-local-2015-01-09_14:57:12",
      "localhost-linux-x86_64-local-2015-01-09_15:39:47",
      "localhost-linux-x86_64-local-2015-01-09_17:50:32",
    ]
    expected = [
      "localhost-linux-x86_64-local-2015-01-09_15:39:47",
    ]
    assertCommonality(snaps1, snaps2, expected)

    # Case 3) Snapshots of different subvolumes with equal times. No
    #         commonality.
    snaps1 = [
      "localhost-linux-x86_64-local-2015-01-09_15:39:47",
      "localhost-linux-x86_64-local-2015-01-09_16:57:16",
    ]
    snaps2 = [
      "localhost-linux-x86_64-root-2015-01-09_15:39:47",
      "localhost-linux-x86_64-root-2015-01-09_16:57:16",
    ]
    assertCommonality(snaps1, snaps2, [])


  def testRepositorySerializeIncremental(self):
    """Test the incremental serialization functionality."""
    def snap(name):
      """Create a snapshot of the 'root' directory under the given name."""
      # Now we need a new snapshot.
      execute(*snapshot(m.path("root"),
                        m.path(name)))
      execute(*sync(m.path()))

    def transfer(snapshot, parent=None):
      """Transfer (serialize & deserialize) a snapshot into the 'sent' directory."""
      with alias(self._mount) as m:
        parent = m.path(parent) if parent else None
        snapshot = m.path(snapshot)

        # Serialize the given snapshot but read the data into a Python
        # object to determine the length of the byte stream.
        data, _ = execute(*serialize(snapshot, [parent] if parent else None),
                          read_out=True)
        size = len(data)
        # Now form back the snapshot out of the intermediate byte stream.
        execute(*deserialize(m.path("sent")), data_in=data)
        return size

    with alias(self._mount) as m:
      # Create a subvolume and file with some data so that the meta data
      # does not make up the majority of the byte stream once
      # serialized.
      make(m, "root", subvol=True)
      make(m, "root", "file2", data=b"data" * 1024)
      make(m, "sent", subvol=True)

      # Now we need an initial snapshot.
      snap("snap1")
      size1 = transfer("snap1")

      # Create a new file with some data.
      make(m, "root", "file3", data=b"data" * 512)
      # Create a second snapshot.
      snap("snap2")
      # Serialize only the differences to the first snapshot.
      size2 = transfer("snap2", parent="snap1")

      # We must have transferred less data for the incremental, second
      # snapshot than for the initial one which was a full transfer.
      self.assertGreater(size1, size2)
      self.assertTrue(isfile(m.path("sent", "snap1", "file2")))
      self.assertTrue(isfile(m.path("sent", "snap2", "file3")))


class TestRepositorySnapshots(BtrfsSnapshotTestCase):
  """Test snapshot related repository functionality."""
  def testRepositoryListNoSnapshotPresentInSubdir(self):
    """Verify that if no snapshot is present in a directory an empty list is returned."""
    with alias(self._mount) as m:
      # Create a new sub-directory where no snapshots are present.
      directory = make(m, "dir")
      repository = Repository(directory)
      # TODO: The assertion should really be assertEqual! I consider
      #       this behavior a bug because we pass in the -o option to
      #       the list command which is promoted as: "print only
      #       subvolumes below specified path".
      #       There is no subvolume below the given path, so reporting a
      #       snapshot here is wrong.
      self.assertNotEqual(_snapshots(repository), [])


  def testRepositoryListOnlySnapshotsInRepository(self):
    """Verify that listing snapshots in a repository not in the btrfs root works."""
    with alias(self._mount) as m:
      make(m, "repository")

      execute(*snapshot(m.path("root"),
                        m.path("root_snapshot2")))
      execute(*snapshot(m.path("root"),
                        m.path("repository", "root_snapshot3")))
      execute(*snapshot(m.path("root"),
                        m.path("repository", "root_snapshot4")))

      repo = Repository(m.path("repository"))
      # Only snapshots in the repository must occur in the list.
      snap1, snap2 = repo.snapshots()

      self.assertEqual(snap1["path"], "root_snapshot3")
      self.assertEqual(snap2["path"], "root_snapshot4")


class TestRepository(BtrfsRepositoryTestCase):
  """Test repository functionality."""
  def testRepositoryListSnapshots(self):
    """Verify that we can list a single snapshot and parse it correctly."""
    snap, = self._repository.snapshots()

    # We cannot tell the generation number with 100% certainty because
    # slight differences in the implementation could change it. So just
    # compare the reported path for now.
    self.assertEqual(snap["path"], "root_snapshot")
    self.assertTrue("gen" in snap)


  def testRepositoryListMultipleSnapshots(self):
    """Verify that we can list multiple snapshots and parse them correctly."""
    with alias(self._repository) as r:
      execute(*snapshot(r.path("root"),
                        r.path("root_snapshot2")))

      snap1, snap2 = r.snapshots()

    self.assertEqual(snap1["path"], "root_snapshot")
    self.assertEqual(snap2["path"], "root_snapshot2")


  def testRepositoryEmptyDiff(self):
    """Verify that an empty diff is reported on a fresh snapshot."""
    with alias(self._repository) as r:
      self.assertEqual(r.diff("root_snapshot", r.path("root")), [])


  def testRepositoryEmptyFileNotInDiff(self):
    """Check whether a newly created empty file is reported by diff().

      The find-new functionality provided by btrfs apparently does not
      catch cases where an empty file is created in a subvolume after a
      snapshot was taken. This test checks for this property. Note that
      this property is *not* favorable for the usage of find-new in this
      program. This test case is meant to raise awareness for this
      issue.
    """
    with alias(self._repository) as r:
      make(r, "root", "file2", data=b"")
      make(r, "root", "file3", data=b"")
      make(r, "root", "file4", data=b"")

      self.assertEqual(r.diff("root_snapshot", r.path("root")), [])
      self.assertTrue(isfile(r.path("root", "file2")))


  def testRepositoryDiff(self):
    """Verify that we can retrieve a list of changed files for a subvolume."""
    with alias(self._repository) as r:
      # Write something into the existing file to have it contain
      # changes over the snapshot.
      with open(r.path("root", "file"), "w") as f:
        f.write("\0")

      # Also create a new file with some content.
      make(r, "root", "dir", "file2", data=b"test-data")

      files = r.diff("root_snapshot", r.path("root"))
      # We cannot tell for sure the order in which the files appear so use
      # a set here.
      expected = {"file", join("dir", "file2")}

      self.assertEqual(set(files), expected)


  def testRepositoryDiffNoDiffAfterSnapshot(self):
    """Verify that after taking a snapshot the reported diff is empty."""
    with alias(self._repository) as r:
      # Create a file with actual content.
      make(r, "root", "dir", "file2", data=b"test-data")

      expected = [join("dir", "file2")]
      self.assertEqual(r.diff("root_snapshot", r.path("root")), expected)

      # After taking another snapshot the file must no longer be
      # reported as changed.
      execute(*snapshot(r.path("root"), r.path("root_snapshot2")))
      self.assertEqual(r.diff("root_snapshot2", r.path("root")), [])


  def testRepositoryDiffDeletion(self):
    """Check whether deleted files in a subvolume are reported by diff().

      This test case checks that files that are present in a snapshot
      but got deleted in the associated subvolume are not reported by
      diff(). This test's purpose is more to show case and create
      awareness of this behavior than to actually verify that this
      property is really enforced.
    """
    with alias(self._repository) as r:
      remove(r.path("root", "file"))

      self.assertEqual(r.diff("root_snapshot", r.path("root")), [])


class TestBtrfsSync(BtrfsTestCase):
  """Test repository synchronization functionality."""
  def testRepositorySyncFailsForNonExistentSubvolume(self):
    """Verify that synchronization fails if a subvolume does not exist."""
    with alias(self._mount) as m:
      snaps = make(m, "snapshots")
      backup = make(m, "backup")

      directory = "non-existent-directory"
      regex = r"error accessing.*%s" % directory
      src = Repository(snaps)
      dst = Repository(backup)

      with self.assertRaisesRegex(ChildProcessError, regex):
        syncRepos([m.path(directory)], src, dst)

      self.assertEqual(glob(join(snaps, "*")), [])
      self.assertEqual(glob(join(backup, "*")), [])


  def testRepositorySync(self):
    """Test that we can sync a single subvolume between two repositories."""
    with patch("deso.btrfs.repository.datetime", wraps=datetime) as mock_now:
      with alias(self._mount) as m:
        mock_now.now.return_value = datetime(2015, 1, 5, 22, 34)

        make(m, "root", subvol=True)
        make(m, "root", "dir", "file", data=b"")

        src = Repository(make(m, "repo1"))
        dst = Repository(make(m, "repo2"))

        # Case 1) Sync repositories initially. A snapshot should be taken
        #         in the source repository and transferred to the remote
        #         repository.
        syncRepos([m.path("root")], src, dst)

        # Verify that both repositories contain the proper snapshots.
        snap1, = src.snapshots()
        self.assertRegex(snap1["path"], "root-2015-01-05_22:34:00")

        snap2, = dst.snapshots()
        self.assertRegex(snap2["path"], "root-2015-01-05_22:34:00")

        # Case 2) Try to sync two repositories that are already in sync.
        #         The catch here is that the time did not advance
        #         neither did the snapshotted subvolume contain any new
        #         data. So no snapshot should be made.
        syncRepos([m.path("root")], src, dst)

        snap1, = src.snapshots()
        self.assertRegex(snap1["path"], "root-2015-01-05_22:34:00")

        snap2, = dst.snapshots()
        self.assertRegex(snap2["path"], "root-2015-01-05_22:34:00")

        # Case 3) Snapshot after new data is available in the subvolume.
        #         Once new data is available in the repository this fact
        #         should be detected and an additional sync operation
        #         must create a new snapshot and transfer it properly.
        mock_now.now.return_value = datetime(2015, 1, 5, 22, 35)

        # Create a new file with some data in it.
        make(m, "root", "dir", "file2", data=b"new-data")

        syncRepos([m.path("root")], src, dst)

        snap1_1, snap1_2 = src.snapshots()
        self.assertRegex(snap1_1["path"], "root-2015-01-05_22:34:00")
        self.assertRegex(snap1_2["path"], "root-2015-01-05_22:35:00")

        snap2_1, snap2_2 = dst.snapshots()
        self.assertRegex(snap2_1["path"], "root-2015-01-05_22:34:00")
        self.assertRegex(snap2_2["path"], "root-2015-01-05_22:35:00")

        # Case 4) Perform an additional sync (after new data was added)
        #         without time advancement. The result would normally be
        #         a name clash because a snapshot with the same name
        #         already exists (the time stamps are equal). The system
        #         needs to make sure to number snapshots appropriately
        #         if one with the same name already exists.
        make(m, "root", "dir", "file3", data=b"even-more-new-data")

        syncRepos([m.path("root")], src, dst)

        _, _, snap1_3 = src.snapshots()
        self.assertRegex(snap1_3["path"], "root-2015-01-05_22:35:00-1")

        # Case 5) Try once more to see that the appended number is
        #         properly incremented and not just appended to or so.
        make(m, "root", "dir", "file4", data=b"even-even-more-new-data")

        syncRepos([m.path("root")], src, dst)

        _, _, _, snap1_4 = src.snapshots()
        self.assertRegex(snap1_4["path"], "root-2015-01-05_22:35:00-2")


  def testRepositoryMultipleSubvolumeSync(self):
    """Verify that we can sync multiple subvolumes between two repositories."""
    with patch("deso.btrfs.repository.datetime", wraps=datetime) as mock_now:
      with BtrfsDevice() as btrfs:
        with Mount(btrfs.device()) as d:
          with alias(self._mount) as s:
            mock_now.now.return_value = datetime.now()
            make(s, "home")
            subvolumes = [
              s.path("home", "user"),
              s.path("home", "user", "local"),
              s.path("root"),
            ]
            for subvolume in subvolumes:
              execute(*create(subvolume))

            make(s, "home", "user", "data", "movie.mp4", data=b"abcdefgh")
            make(s, "home", "user", "local", "bin", "test.sh", data=b"#!/bin/sh")
            make(s, "root", ".ssh", "key.pub", data=b"1234567890")
            make(s, "snapshots")
            make(d, "backup")

            src = Repository(s.path("snapshots"))
            dst = Repository(d.path("backup"))

            syncRepos(subvolumes, src, dst)

            user, local, root = dst.snapshots()

            self.assertTrue(isfile(dst.path(user["path"], "data", "movie.mp4")))
            self.assertTrue(isfile(dst.path(local["path"], "bin", "test.sh")))
            self.assertTrue(isfile(dst.path(root["path"], ".ssh", "key.pub")))

            make(s, "home", "user", "local", "bin", "test.py", data=b"#!/usr/bin/python")
            make(s, "root", ".ssh", "authorized", data=b"localhost")

            # Advance time to avoid name clash.
            mock_now.now.return_value = mock_now.now.return_value + timedelta(seconds=1)

            syncRepos(subvolumes, src, dst)
            user, _, local, _, root = dst.snapshots()

            self.assertTrue(isfile(dst.path(user["path"], "data", "movie.mp4")))
            self.assertTrue(isfile(dst.path(local["path"], "bin", "test.py")))
            self.assertTrue(isfile(dst.path(local["path"], "bin", "test.sh")))
            self.assertTrue(isfile(dst.path(root["path"], ".ssh", "key.pub")))


  def testRepositoryUniqueSnapshotName(self):
    """Verify that subvolume paths are correctly canonicalized for snapshot names."""
    with alias(self._mount) as m:
      make(m, "home", "user", subvol=True)
      make(m, "home", "user", link="symlink")

      src = Repository(make(m, "snapshots"))
      dst = Repository(make(m, "backup"))

      # We have a real subvolume and a symbolic link to it. We try
      # synchronizing both. The end result should be a single a snapshot
      # because the canonical path to the "true" subvolume should be
      # used.
      syncRepos([m.path("symlink")], src, dst)
      self.assertEqual(len(src.snapshots()), 1)
      self.assertEqual(len(dst.snapshots()), 1)

      # Also try with a different non-canonical path.
      syncRepos([m.path("home", "user", pardir, "user")], src, dst)
      self.assertEqual(len(src.snapshots()), 1)
      self.assertEqual(len(dst.snapshots()), 1)

      syncRepos([m.path("home", "user")], src, dst)
      self.assertEqual(len(src.snapshots()), 1)
      self.assertEqual(len(dst.snapshots()), 1)


  def testRepositoryRestoreFailsIfNoSnapshotPresent(self):
    """Verify an error gets raised if no snapshot to restore is found."""
    with alias(self._mount) as m:
      user = make(m, "home", "user", subvol=True)
      snaps = make(m, "snapshots")
      backup = make(m, "backup")

      src = Repository(snaps)
      dst = Repository(backup)

      # Restoration must fail since we did not create a snapshot yet.
      regex = r"snapshot to restore found.*home.*user"
      with self.assertRaisesRegex(FileNotFoundError, regex):
        restore([user], dst, src)

      # Create a snapshot.
      syncRepos([user], src, dst)

      # Another attempt, this time we have a snapshot of /home/user but
      # none of /home/user1, so we should see a failure again.
      regex = r"snapshot to restore found.*home.*user1"
      with self.assertRaisesRegex(FileNotFoundError, regex):
        restore([m.path("home", "user1")], dst, src)


  def testRepositorySyncAndRestore(self):
    """Test restoring a snapshot after it was backed up."""
    with alias(self._mount) as m:
      make(m, "home", "user", subvol=True)
      make(m, "home", "user", "test-dir", "test", data=b"test-content")

      snaps = make(m, "snapshots")
      backup = make(m, "backup")

      src = Repository(snaps)
      dst = Repository(backup)

      syncRepos([m.path("home", "user")], src, dst)

      snap, = src.snapshots()
      # Delete the snapshot from the source directory.
      execute(*delete(src.path(snap["path"])))

      self.assertEqual(src.snapshots(), [])
      self.assertEqual(glob(join(snaps, "*")), [])

      restore([m.path("home", "user")], dst, src, snapshots_only=True)

      snap, = src.snapshots()
      file_ = src.path(snap["path"], "test-dir", "test")
      self.assertContains(file_, "test-content")


  def testRepositoryRestorePlain(self):
    """Test restoration of a snapshot if the destination btrfs volume got wiped."""
    with alias(self._mount) as b:
      # This time we create our test harness on the other btrfs device.
      with BtrfsDevice() as btrfs:
        with Mount(btrfs.device()) as s:
          make(s, "home", "user", subvol=True)
          make(s, "home", "user", "dir", "test1", data=b"content1")

          src = Repository(make(s, "snapshots"))
          bak = Repository(make(b, "backup"))

          # Remember absolute path of the subvolume to backup for later
          # use.
          subvolume = s.path("home", "user")
          syncRepos([subvolume], src, bak)

          # Create another snapshot with additional data.
          make(s, "home", "user", "dir2", "test2", data=b"content2")
          syncRepos([subvolume], src, bak)

      # Create a new (empty) btrfs file system.
      with BtrfsDevice() as btrfs:
        with Mount(btrfs.device()) as d:
          self.assertEqual(glob(d.path("*")), [])

          # Restore the snapshot from the backup. Note that we had to
          # remember the absolute path of the original directory of the
          # subvolume we backed up because that path likely changed when
          # we created a new btrfs device and mounted it (a new
          # temporary directory is used).
          dst = Repository(d.path())
          restore([subvolume], bak, dst, snapshots_only=True)
          snap, = dst.snapshots()

          file1 = dst.path(snap["path"], "dir", "test1")
          file2 = dst.path(snap["path"], "dir2", "test2")

          self.assertContains(file1, "content1")
          self.assertContains(file2, "content2")


  def testRepositoryRestoreFailExists(self):
    """Verify that restoration fails if the subvolume to restore exists."""
    with alias(self._mount) as m:
      make(m, "root", subvol=True)
      make(m, "root", "file", data=b"data")

      src = Repository(make(m, "snapshots"))
      bak = Repository(make(m, "backup"))

      syncRepos([m.path("root")], src, bak)

      snap, = src.snapshots()
      execute(*delete(src.path(snap["path"])))

      regex = r"root.*: a directory.*exists"
      with self.assertRaisesRegex(FileExistsError, regex):
        restore([m.path("root")], bak, src)

      # Also test that we fail if the previously existing root subvolume
      # got replaced by a file.
      execute(*delete(m.path("root")))
      make(m, "root", data=b"root")

      regex = r"%s.*exists and it is not a directory" % m.path("root")
      with self.assertRaisesRegex(ChildProcessError, regex):
        restore([m.path("root")], bak, src)


  def testRepositoryPurge(self):
    """Test auto deletion of old snapshots."""
    with patch("deso.btrfs.repository.datetime", wraps=datetime) as mock_now:
      with alias(self._mount) as m:
        subvolumes = [make(m, "subvol", subvol=True)]
        src = Repository(make(m, "snapshots"))
        dst = Repository(make(m, "backup"))
        now = datetime(2015, 1, 23, 21, 10, 17)

        # Create a lot of snapshots each with a different time stamp.
        for i in range(20):
          make(m, "subvol", "file%s" % i, data=b"test")
          mock_now.now.return_value = now - timedelta(minutes=i)
          syncRepos(subvolumes, src, dst)

        snapshots = src.snapshots()
        mock_now.now.return_value = now

        # Nothing should have been deleted for a duration of 1 hour of
        # keeping the snapshots.
        src.purge(subvolumes, timedelta(hours=1))
        self.assertEqual(src.snapshots(), snapshots)

        src.purge(subvolumes, timedelta(minutes=30))
        self.assertEqual(src.snapshots(), snapshots)

        src.purge(subvolumes, timedelta(minutes=19))
        self.assertEqual(src.snapshots(), snapshots)

        # Now with a keep duration of just less than 19 minutes we have
        # our first deletion (the first snapshot we created, to be
        # precise).
        src.purge(subvolumes, timedelta(minutes=18, seconds=59))
        self.assertEqual(src.snapshots(), snapshots[1:])

        src.purge(subvolumes, timedelta(minutes=10))
        self.assertEqual(src.snapshots(), snapshots[9:])

        src.purge(subvolumes, timedelta(seconds=59))
        self.assertEqual(src.snapshots(), snapshots[19:])

        # The most recent snapshots must never be purged.
        most_recent, = snapshots[19:]
        src.purge(subvolumes, timedelta(seconds=0))
        self.assertEqual(src.snapshots(), [most_recent])

        mock_now.now.return_value = now + timedelta(hours=12)
        src.purge(subvolumes, timedelta(minutes=1))
        self.assertEqual(src.snapshots(), [most_recent])


if __name__ == "__main__":
  main()
