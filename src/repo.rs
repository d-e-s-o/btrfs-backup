// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs::canonicalize;
use std::fs::create_dir_all;
use std::fs::metadata;
use std::io::ErrorKind;
use std::path::Path;
use std::path::PathBuf;

use anyhow::bail;
use anyhow::Context as _;
use anyhow::Result;

use crate::btrfs::Btrfs;
use crate::snapshot::Snapshot;
use crate::snapshot::SnapshotBase;
use crate::util::canonicalize_non_strict;


/// Check if a given directory represents the root of a btrfs file
/// system.
fn is_root(btrfs: &Btrfs, directory: &Path) -> Result<bool> {
  btrfs.is_btrfs(directory)
}

/// Find the root of a btrfs file system based on a path pointing
/// somewhere into it.
///
/// # Notes
/// This function may produce false positives, i.e., it may report a
/// btrfs root not actually for the file system that `directory` is on.
/// That is because we have no knowledge of mount points and so if
/// `directory` lies on a non-btrfs file system but it is mounted within
/// a btrfs file system, we actually end up detecting the btrfs file
/// system's root.
fn find_root(btrfs: &Btrfs, directory: &Path) -> Result<PathBuf> {
  let mut to_check = directory;
  loop {
    if is_root(btrfs, to_check)? {
      return Ok(to_check.to_path_buf())
    }

    if let Some(parent) = to_check.parent() {
      to_check = parent
    } else {
      break
    }
  }

  bail!(
    "failed to find btrfs file system containing {}",
    directory.display()
  )
}


/// Find the most recent snapshot of a subvolume.
fn find_most_recent_snapshot<'snaps>(
  snapshots: &'snaps [(Snapshot, usize)],
  subvol: &Path,
) -> Result<Option<&'snaps (Snapshot, usize)>> {
  let base_name = SnapshotBase::from_subvol_path(subvol)?;
  let snapshots = snapshots
    .iter()
    .filter(|(snapshot, _generation)| snapshot.as_base_name() == base_name)
    .collect::<Vec<_>>();

  // The most recent snapshot (i.e., the one with the largest time
  // stamp) will be the last one.
  Ok(snapshots.into_iter().last())
}


/// "Deploy" a snapshot in a source repository to a destination.
fn deploy(src: &Repo, dst: &Repo, src_snap: &Snapshot) -> Result<()> {
  let base_name = src_snap.as_base_name();
  let dst_snaps = dst
    .snapshots()?
    .into_iter()
    .map(|(snapshot, _generation)| snapshot)
    .filter(|snapshot| snapshot.as_base_name() == base_name)
    .collect::<BTreeSet<_>>();

  // Check whether the snapshot already exists at the destination. That
  // may be the case if the subvolume did not change and we did not
  // actually create a new snapshot to begin with.
  if dst_snaps.contains(src_snap) {
    return Ok(())
  }

  // TODO: The `src.snapshot` invocation above already retrieves the
  //       snapshot list internally. We should remove duplicate
  //       operations.
  let src_snaps = src
    .snapshots()?
    .into_iter()
    .map(|(snapshot, _generation)| snapshot)
    .filter(|snapshot| snapshot.as_base_name() == base_name)
    .collect::<BTreeSet<_>>();

  // Find all candidate parent snapshots, which is basically nothing
  // more than the set of snapshots of the provided subvolume available
  // in both repositories.
  let parents = src_snaps
    .intersection(&dst_snaps)
    .into_iter()
    .map(|snapshot| src.path().join(snapshot.to_string()))
    .collect::<Vec<_>>();
  let parents = parents.iter().map(OsStr::new);

  let () = src.btrfs.sync(&src.btrfs_root)?;
  let () = src
    .btrfs
    .send_recv(&src.path().join(src_snap.to_string()), parents, &dst.path())?;

  Ok(())
}


/// Backup a subvolume from a source repository to a destination.
pub fn backup(src: &Repo, dst: &Repo, subvol: &Path) -> Result<Snapshot> {
  let src_snap = src.snapshot(subvol)?;
  let () = deploy(src, dst, &src_snap)?;
  Ok(src_snap)
}


/// Check whether a `path` references a directory.
///
/// This function differs from [`std::path::Path::is_dir`] in that it
/// only maps file-not-found errors into the `Ok` portion of the result.
/// All other errors (such as permission denied) are reported verbatim.
fn is_dir(path: &Path) -> Result<bool> {
  match metadata(path) {
    Ok(info) => Ok(info.is_dir()),
    Err(err) if err.kind() == ErrorKind::NotFound => Ok(false),
    Err(err) => Err(err.into()),
  }
}


/// Restore a subvolume from a source repository.
pub fn restore(src: &Repo, dst: &Repo, subvol: &Path, snapshot_only: bool) -> Result<()> {
  let subvol = canonicalize_non_strict(subvol)?;
  if let Some(parent) = subvol.parent() {
    // The subvolume is unlikely to exist (after all, it's meant to be
    // restored). However, given that the user wants to restore it we
    // should make sure that the path to it exists.
    let () = create_dir_all(parent)?;
  }

  let snapshots = src.snapshots()?;
  let (snapshot, _generation) =
    find_most_recent_snapshot(&snapshots, &subvol)?.with_context(|| {
      // In case the given source repository does not contain any snapshots
      // for the given subvolume we cannot do anything but signal that to
      // the user.
      format!(
        "No snapshot to restore found for subvolume {} in {}",
        subvol.display(),
        src.path().display()
      )
    })?;

  // We want to signal an error to the user in case the subvolume
  // already exists but he/she has asked us to restore it. We cannot
  // solely rely on btrfs snapshot for this detection because in case
  // there is a directory where 'subvolume' points to, the command will
  // just manifest the new subvolume in this directory. So explicitly
  // guard against this case here.
  if !snapshot_only && is_dir(&subvol)? {
    bail!(
      "Cannot restore subvolume {}: a directory with this name exists",
      subvol.display()
    )
  }

  // Restoration of a subvolume involves a subset of the steps we do
  // when we pull a backup: the deployment.
  let () = deploy(src, dst, snapshot)?;

  if !snapshot_only {
    // Now that we got the snapshot back on the destination repository,
    // we can restore the actual subvolume from it.
    let readonly = true;
    let () = dst
      .btrfs
      .snapshot(&dst.path().join(snapshot.to_string()), &subvol, !readonly)?;
  }
  Ok(())
}


/// A repository used for managing btrfs snapshots.
#[derive(Clone, Debug)]
pub struct Repo {
  /// Our btrfs API.
  btrfs: Btrfs,
  /// The containing btrfs filesystem's root. This path has been
  /// canonicalized.
  btrfs_root: PathBuf,
  /// The repository's root directory, as a path relative to
  /// `btrfs_root`.
  repo_root: PathBuf,
}

impl Repo {
  /// Create a new `Repo` object, with `directory` as the root.
  pub fn new<P>(directory: P) -> Result<Self>
  where
    P: AsRef<Path>,
  {
    let directory = directory.as_ref();
    let () = create_dir_all(directory)
      .with_context(|| format!("could not ensure directory {} exists", directory.display()))?;

    let directory = canonicalize(directory)
      .with_context(|| format!("failed to canonicalize path {}", directory.display()))?;

    let btrfs = Btrfs::new();
    let root = find_root(&btrfs, &directory)?;

    let slf = Self {
      btrfs,
      // SANITY: Our detected btrfs root directory should always be a
      //         prefix of `directory`.
      repo_root: directory.strip_prefix(&root).unwrap().to_path_buf(),
      btrfs_root: root,
    };
    Ok(slf)
  }

  /// Create a snapshot of the given subvolume in this repository.
  ///
  /// If an up-to-date snapshot is present already, just return it
  /// directly.
  pub fn snapshot(&self, subvol: &Path) -> Result<Snapshot> {
    let subvol = canonicalize(subvol)?;
    let snapshots = self.snapshots()?;
    let most_recent = find_most_recent_snapshot(&snapshots, &subvol)?;

    let parent = if let Some((snapshot, generation)) = most_recent {
      let has_changes = self.btrfs.has_changes(&subvol, *generation)?;
      if !has_changes {
        return Ok(snapshot.clone())
      }
      Some(snapshot)
    } else {
      None
    };

    // At this point we know that we have to create a new snapshot for
    // the given subvolume, either because no snapshot was present or
    // because the subvolume has changed since it had been captured.
    let mut snapshot = Snapshot::from_subvol_path(&subvol)?;
    debug_assert_eq!(snapshot.number, None);

    // `parent` here is just referring to the most recent snapshot.
    if let Some(most_recent) = parent {
      // If the snapshot has the same base information as the most
      // recent one (including time stamp), disambiguate it by using the
      // most recent snapshot's number incremented by one. The snapshot
      // is then guaranteed to be unique.
      if snapshot == most_recent.strip_number() {
        snapshot = most_recent.bump_number();
      }
    }

    let readonly = true;
    let snapshot_path = self.path().join(snapshot.to_string());
    let () = self.btrfs.snapshot(&subvol, &snapshot_path, readonly)?;
    Ok(snapshot)
  }

  /// Delete the provided snapshot from the repository.
  pub fn delete(&self, snapshot: &Snapshot) -> Result<()> {
    let snapshot_path = self.path().join(snapshot.to_string());
    let () = self.btrfs.delete_subvol(&snapshot_path)?;
    Ok(())
  }

  /// Retrieve a list of snapshots in this repository.
  ///
  /// The list is sorted by a per-snapshot-base-name buckets, with the
  /// most recent snapshot being last in each such bucket.
  /// Each snapshot is accompanied by its current btrfs generation
  /// number. All subvolumes present in this repository that do not
  /// match the snapshot format are silently ignored, as they could not
  /// have been generated by the program.
  pub fn snapshots(&self) -> Result<Vec<(Snapshot, usize)>> {
    let readonly = true;
    let mut snapshots = self
      .btrfs
      .subvolumes(&self.btrfs_root, Some(&self.repo_root), readonly)?
      .into_iter()
      // We are only interested in snapshots *directly* inside of
      // `repo_root`.
      .filter_map(|(path, gen)| {
        // For relative paths, Path::parent returns Some("") if there is
        // no parent.
        if path.parent() == Some(Path::new("")) {
          path
            .file_name()
            .and_then(|snapshot| Snapshot::from_snapshot_name(snapshot).ok())
            .map(|snapshot| (snapshot, gen))
        } else {
          None
        }
      })
      .collect::<Vec<_>>();
    let () = snapshots.sort();

    Ok(snapshots)
  }

  /// Retrieve the path to the repository.
  #[inline]
  pub fn path(&self) -> PathBuf {
    self.btrfs_root.join(&self.repo_root)
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  use std::fs::read_to_string;
  use std::fs::write;
  use std::os::unix::fs::symlink;

  use serial_test::serial;

  use crate::snapshot::Subvol;
  use crate::test::with_btrfs;
  use crate::test::with_two_btrfs;
  use crate::test::BtrfsDev;
  use crate::test::Mount;


  /// Check that we can create a snapshot of a subvolume.
  #[test]
  #[serial]
  fn snapshot_creation() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let repo = Repo::new(root.join("repo")).unwrap();

      let snapshot = repo.snapshot(&subvol).unwrap();
      let content = read_to_string(repo.path().join(snapshot.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");
    })
  }

  /// Make sure that we do not create a new snapshot if a subvolume has
  /// not changed over its most recent snapshot.
  #[test]
  #[serial]
  fn snapshot_creation_up_to_date() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let repo = Repo::new(root).unwrap();

      let snapshot1 = repo.snapshot(&subvol).unwrap();
      let snapshot2 = repo.snapshot(&subvol).unwrap();
      assert_eq!(snapshot1, snapshot2);

      let snapshots = repo.snapshots().unwrap();
      assert_eq!(snapshots.len(), 1);
    })
  }

  /// Make sure that we create a new snapshot if a subvolume has changed
  /// over its most recent snapshot.
  #[test]
  #[serial]
  fn snapshot_creation_on_change() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let repo = Repo::new(root).unwrap();

      let snapshot1 = repo.snapshot(&subvol).unwrap();
      let () = write(subvol.join("file"), "test43").unwrap();
      let snapshot2 = repo.snapshot(&subvol).unwrap();
      assert_ne!(snapshot1, snapshot2);

      let snapshots = repo.snapshots().unwrap();
      assert_eq!(snapshots.len(), 2);

      let content = read_to_string(repo.path().join(snapshot1.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");
      let content = read_to_string(repo.path().join(snapshot2.to_string()).join("file")).unwrap();
      assert_eq!(content, "test43");
    })
  }

  /// Check that no snapshots are reported in an empty repository.
  #[test]
  #[serial]
  fn no_snapshots_in_empty_repo() {
    with_btrfs(|root| {
      let repo = Repo::new(root).unwrap();

      let snapshots = repo.snapshots().unwrap();
      assert!(snapshots.is_empty());
    })
  }

  /// Check that we can create a snapshot of a subvolume and that it is
  /// being returned as part of the snapshot listing.
  #[test]
  #[serial]
  fn snapshot_listing() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let repo = Repo::new(root.join("repo")).unwrap();

      let snapshot = repo.snapshot(&subvol).unwrap();
      let mut snapshots = repo.snapshots().unwrap().into_iter();
      assert_eq!(snapshots.len(), 1);

      let next = snapshots.next().unwrap();
      assert_eq!(next.0.subvol, Subvol::new(&subvol));
      assert_eq!(next.0.subvol, snapshot.subvol);
      assert_ne!(next.1, 0);
    })
  }

  /// Make sure that we ignore snapshots outside of a repository.
  #[test]
  #[serial]
  fn snapshot_outside_repo() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      // Our "business" repository.
      let repo = Repo::new(root.join("repo")).unwrap();

      // One repository in the root.
      let root_repo = Repo::new(root).unwrap();
      let _snapshot = root_repo.snapshot(&subvol).unwrap();

      // And another one below ours.
      let sub_repo = Repo::new(repo.path().join("foobar")).unwrap();
      let _snapshot = sub_repo.snapshot(&subvol).unwrap();

      // None of the other repositories' snapshots should appear in our
      // listing.
      let snapshots = repo.snapshots().unwrap();
      assert!(snapshots.is_empty());
    })
  }

  /// Make sure that only read-only subvolumes are considered as
  /// snapshots.
  #[test]
  #[serial]
  fn writable_snapshot_listing() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let snapshot = Snapshot::from_subvol_path(Path::new("/foobar")).unwrap();
      let subvol = root.join(snapshot.to_string());
      // Create a writable subvolume with a valid snapshot name.
      let () = btrfs.create_subvol(&subvol).unwrap();

      let repo = Repo::new(root).unwrap();
      // Because the subvolume is writable, it should not be produced in
      // the snapshot listing.
      let snapshots = repo.snapshots().unwrap();
      assert!(snapshots.is_empty());
    })
  }

  /// Check that we can backup a subvolume across file system
  /// boundaries.
  #[test]
  #[serial]
  fn backup_subvolume() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let snapshot = backup(&src, &dst, &subvol).unwrap();
      let content = read_to_string(dst.path().join(snapshot.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");
    })
  }

  /// Check that subvolume paths are canocicalized for backup.
  #[test]
  #[serial]
  fn backup_subvolume_canonicalized() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let snapshot = backup(&src, &dst, &subvol).unwrap();

      let link = src_root.join("symlink");
      let () = symlink(subvol, &link).unwrap();
      let new_snapshot = backup(&src, &dst, &link).unwrap();
      assert_eq!(new_snapshot, snapshot);

      let subvol = src_root.join("subvol").join("..").join("subvol");
      let new_snapshot = backup(&src, &dst, &subvol).unwrap();
      assert_eq!(new_snapshot, snapshot);
    })
  }

  /// Check that we can backup a subvolume mounted with the `subvol`
  /// option.
  #[test]
  #[serial]
  fn backup_subvolume_with_subvol_option() {
    let src_loopdev = BtrfsDev::with_default().unwrap();

    {
      let src_mount = Mount::new(src_loopdev.path()).unwrap();
      let btrfs = Btrfs::new();
      let subvol = src_mount.path().join("some-subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();
    }

    let src_mount = Mount::with_options(src_loopdev.path(), ["subvol=some-subvol"]).unwrap();
    let src_root = src_mount.path();
    assert!(src_root.join("file").exists());

    let dst_loopdev = BtrfsDev::with_default().unwrap();
    let dst_mount = Mount::new(dst_loopdev.path()).unwrap();
    let dst_root = dst_mount.path();

    let src = Repo::new(src_root).unwrap();
    let dst = Repo::new(dst_root).unwrap();

    let subvol = src_mount.path();
    let () = write(subvol.join("file"), "test42").unwrap();

    let snapshot = backup(&src, &dst, subvol).unwrap();
    let content = read_to_string(dst.path().join(snapshot.to_string()).join("file")).unwrap();
    assert_eq!(content, "test42");
  }

  /// Check that we error out as expected when attempting to backup a
  /// non-existent subvolume.
  #[test]
  #[serial]
  fn backup_non_existent_subvolume() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let subvol = src_root.join("subvol");
      let error = backup(&src, &dst, &subvol).unwrap_err();
      assert!(error.to_string().contains("No such file or directory"));
    })
  }

  /// Make sure that if the subvolume to backup is already up-to-date
  /// with respect to a snapshot, no additional work is done.
  #[test]
  #[serial]
  fn backup_subvolume_up_to_date() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let snapshot1 = backup(&src, &dst, &subvol).unwrap();
      let snapshot2 = backup(&src, &dst, &subvol).unwrap();
      assert_eq!(snapshot1, snapshot2);

      let snapshots = dst.snapshots().unwrap();
      assert_eq!(snapshots.len(), 1);
    })
  }

  // TODO: Ideally we'd have a test that checks that incremental backups
  //       cause less data to be transferred to make sure that we are
  //       doing everything right, but currently that's not easily
  //       possible to check for.

  /// Make sure that incremental backups can be pulled.
  #[test]
  #[serial]
  fn backup_subvolume_incremental() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let _snapshot = backup(&src, &dst, &subvol).unwrap();

      for i in 0..20 {
        let string = "test".to_string() + &i.to_string();
        let () = write(subvol.join("file"), &string).unwrap();

        let snapshot = backup(&src, &dst, &subvol).unwrap();
        let content = read_to_string(dst.path().join(snapshot.to_string()).join("file")).unwrap();
        assert_eq!(content, string);
      }
    })
  }

  /// Check that we can restore a subvolume from a snapshot.
  #[test]
  #[serial]
  fn restore_subvolume() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      // Backup the subvolume to the destination repository.
      let snapshot = backup(&src, &dst, &subvol).unwrap();
      // Then remove the source snapshot and the source subvolume.
      let () = src.delete(&snapshot).unwrap();
      assert!(!src.path().join(snapshot.to_string()).join("file").exists());

      let () = btrfs.delete_subvol(&subvol).unwrap();
      assert!(!subvol.join("file").exists());

      // And lastly, attempt restoration of both.
      let snapshot_only = false;
      let () = restore(&dst, &src, &subvol, snapshot_only).unwrap();

      // The snapshot should be back with the respective content.
      let content = read_to_string(src.path().join(snapshot.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");

      // And so should the subvolume.
      let content = read_to_string(subvol.join("file")).unwrap();
      assert_eq!(content, "test42");
    })
  }

  /// Check that we can restore only a snapshot.
  #[test]
  #[serial]
  fn restore_snapshot_only() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let snapshot = backup(&src, &dst, &subvol).unwrap();
      let () = src.delete(&snapshot).unwrap();

      let snapshot_only = true;
      let () = restore(&dst, &src, &subvol, snapshot_only).unwrap();

      // The snapshot should be back with the respective content.
      let content = read_to_string(src.path().join(snapshot.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");
    })
  }

  /// Check that subvolume paths are canocicalized for restoration.
  #[test]
  #[serial]
  fn restore_canonicalized() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let snapshot = backup(&src, &dst, &subvol).unwrap();
      let () = src.delete(&snapshot).unwrap();
      let () = btrfs.delete_subvol(&subvol).unwrap();

      let verbose_subvol = src_root.join("subvol").join("..").join("subvol");
      let snapshot_only = false;
      let () = restore(&dst, &src, &verbose_subvol, snapshot_only).unwrap();

      let content = read_to_string(src.path().join(snapshot.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");
      let content = read_to_string(subvol.join("file")).unwrap();
      assert_eq!(content, "test42");
    })
  }

  /// Check that we fail subvolume restoration if the subvolume already
  /// exists.
  #[test]
  #[serial]
  fn restore_subvolume_exists() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let snapshot = backup(&src, &dst, &subvol).unwrap();
      // Then remove the source snapshot and the source subvolume.
      let () = src.delete(&snapshot).unwrap();

      // And lastly, attempt restoration of both.
      let snapshot_only = false;
      let error = restore(&dst, &src, &subvol, snapshot_only).unwrap_err();
      assert!(error
        .to_string()
        .contains("a directory with this name exists"));
    })
  }

  /// Check that we fail subvolume restoration if no suitable snapshot
  /// is present to restore from.
  #[test]
  #[serial]
  fn restore_subvolume_missing_snapshot() {
    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let snapshot = backup(&src, &dst, &subvol).unwrap();
      // Then remove the just created snapshot.
      let () = dst.delete(&snapshot).unwrap();

      let snapshot_only = false;
      let error = restore(&dst, &src, &subvol, snapshot_only).unwrap_err();
      assert!(error.to_string().contains("No snapshot to restore found"));
    })
  }
}
