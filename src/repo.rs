// Copyright (C) 2022-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::ops::Deref as _;
use std::path::Path;
use std::path::PathBuf;
use std::rc::Rc;

use anyhow::bail;
use anyhow::Context as _;
use anyhow::Result;

use time::Duration;

use crate::btrfs::Btrfs;
use crate::ops::FileOps;
use crate::ops::LocalOps;
use crate::snapshot::current_time;
use crate::snapshot::Snapshot;
use crate::snapshot::SnapshotBase;
use crate::snapshot::Subvol;


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
///
/// If `tag` is `None` then the snapshot's tag is ignored.
///
/// Please note that in the presence of differing tags, it is possible
/// for this function to not actually return the absolutely most-recent
/// snapshot, if two (or more) snapshots were created at the exact same
/// time but with different tags, one with more up-to-date content than
/// the other, they are considered equally up-to-date but, crucially,
/// NOT distinguished by a number, and which one is reported depends on
/// the lexicographical ordering of the tag. In practice it should be
/// outstandingly rare to hit this case.
fn find_most_recent_snapshot<'snaps>(
  snapshots: &'snaps [(Snapshot, usize)],
  subvol: &Path,
  tag: Option<&str>,
) -> Result<Option<&'snaps (Snapshot, usize)>> {
  let base_name = SnapshotBase::from_subvol_path(subvol)?;
  let snapshots = snapshots
    .iter()
    .filter(|(snapshot, _generation)| {
      snapshot.as_base_name() == base_name && (tag.is_none() || Some(snapshot.tag.as_ref()) == tag)
    })
    .collect::<Vec<_>>();

  // The most recent snapshot (i.e., the one with the largest time
  // stamp) will be the last one.
  Ok(snapshots.into_iter().next_back())
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

  // Find all candidate source snapshots, which is basically nothing
  // more than the set of snapshots of the provided subvolume available
  // in both repositories.
  let sources = src_snaps
    .intersection(&dst_snaps)
    .map(|snapshot| src.path().join(snapshot.to_string()))
    .collect::<Vec<_>>();
  let sources = sources.iter().map(OsStr::new);

  let () = src.btrfs.sync(&src.btrfs_root)?;
  let () = src.btrfs.send_recv(
    &src.path().join(src_snap.to_string()),
    sources,
    &dst.btrfs,
    &dst.path(),
  )?;

  Ok(())
}


/// Backup a subvolume from a source repository to a destination.
pub fn backup(src: &Repo, dst: &Repo, subvol: &Path, tag: &str) -> Result<Snapshot> {
  let src_snap = src.snapshot(subvol, tag)?;
  let () = deploy(src, dst, &src_snap)?;
  Ok(src_snap)
}


/// Restore a subvolume from a source repository.
pub fn restore(src: &Repo, dst: &Repo, subvol: &Path, snapshot_only: bool) -> Result<()> {
  if let Some(parent) = subvol.parent() {
    // The subvolume is unlikely to exist (after all, it's meant to be
    // restored). However, given that the user wants to restore it we
    // should make sure that the path to it exists.
    let () = dst.file_ops.create_dir_all(parent)?;
  }

  let snapshots = src.snapshots()?;
  // Note that for restoration purposes we always ignore the tag: we
  // always restore from the most up-to-date snapshot.
  let (snapshot, _generation) =
    find_most_recent_snapshot(&snapshots, subvol, None)?.with_context(|| {
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
  if !snapshot_only && dst.file_ops.is_dir(subvol)? {
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
      .snapshot(&dst.path().join(snapshot.to_string()), subvol, !readonly)?;
  }
  Ok(())
}


/// Purge old snapshots of a subvolume from the provided repository.
pub fn purge(repo: &Repo, subvol: &Path, tag: &str, keep_for: Duration) -> Result<()> {
  let snapshots = repo
    .snapshots()
    .context("failed to list snapshots")?
    .into_iter()
    .map(|(snapshot, _generation)| snapshot)
    .filter(|snapshot| snapshot.subvol == Subvol::new(subvol) && snapshot.tag == tag);

  let current_time = current_time();
  let mut to_purge = snapshots
    .clone()
    .filter(|snapshot| current_time > snapshot.timestamp + keep_for);

  // If we are about to delete all snapshots for the provided
  // subvolume, make sure to keep the most recent one around.
  if to_purge.clone().count() == snapshots.count() {
    let _skipped = to_purge.next_back();
  }

  let () = to_purge.try_for_each(|snapshot| {
    repo.delete(&snapshot).with_context(|| {
      format!(
        "failed to delete snapshot {} in {}",
        snapshot,
        repo.path().display()
      )
    })
  })?;

  Ok(())
}


/// A builder for `Repo` objects.
#[derive(Clone, Debug, Default)]
pub struct RepoBuilder {
  /// The set of file operations to use.
  file_ops: Option<Rc<dyn FileOps>>,
  /// The `Btrfs` instance to use.
  btrfs: Option<Btrfs>,
}

impl RepoBuilder {
  /// Set the `FileOps` instance to use.
  pub fn set_file_ops<O>(&mut self, file_ops: O)
  where
    O: FileOps + 'static,
  {
    self.file_ops = Some(Rc::new(file_ops))
  }

  /// Set the `Btrfs` instance to use.
  pub fn set_btrfs_ops(&mut self, btrfs: Btrfs) {
    self.btrfs = Some(btrfs)
  }

  /// Build the `Repo` object.
  pub fn build<P>(self, directory: P) -> Result<Repo>
  where
    P: AsRef<Path>,
  {
    let file_ops = self.file_ops.unwrap_or_else(|| Rc::new(LocalOps));
    let directory = directory.as_ref();
    let () = file_ops
      .create_dir_all(directory)
      .with_context(|| format!("could not ensure directory {} exists", directory.display()))?;

    let directory = file_ops
      .canonicalize(directory)
      .with_context(|| format!("failed to canonicalize path {}", directory.display()))?;

    let btrfs = self.btrfs.unwrap_or_default();
    let root = find_root(&btrfs, &directory)?;

    let repo = Repo {
      file_ops,
      btrfs,
      // SANITY: Our detected btrfs root directory should always be a
      //         prefix of `directory`.
      repo_root: directory
        .strip_prefix(&root)
        .expect("btrfs root directory is not a prefix of the provided directory")
        .to_path_buf(),
      btrfs_root: root,
    };
    Ok(repo)
  }
}


/// A repository used for managing btrfs snapshots.
#[derive(Clone, Debug)]
pub struct Repo {
  /// The set of file operations to use.
  file_ops: Rc<dyn FileOps>,
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
  /// Create a `RepoBuilder` object.
  pub fn builder() -> RepoBuilder {
    RepoBuilder::default()
  }

  /// Create a new `Repo` object, with `directory` as the root.
  #[cfg(test)]
  pub fn new<P>(directory: P) -> Result<Self>
  where
    P: AsRef<Path>,
  {
    Self::builder().build(directory)
  }

  /// Create a snapshot of the given subvolume in this repository.
  ///
  /// If an up-to-date snapshot is present already, just return it
  /// directly.
  pub fn snapshot(&self, subvol: &Path, tag: &str) -> Result<Snapshot> {
    let snapshots = self.snapshots()?;
    // When searching for the most recent snapshot in this context we
    // are looking for one with not just any but this specific tag.
    let most_recent = find_most_recent_snapshot(&snapshots, subvol, Some(tag))?;

    let most_recent = if let Some((snapshot, generation)) = most_recent {
      let has_changes = self.btrfs.has_changes(subvol, *generation)?;
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
    let mut snapshot = Snapshot::builder().tag(tag).try_build(subvol)?;
    debug_assert_eq!(snapshot.number, None);

    if let Some(most_recent) = most_recent {
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
    let () = self.btrfs.snapshot(subvol, &snapshot_path, readonly)?;
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
      .subvolumes(
        self.file_ops.deref(),
        &self.btrfs_root,
        Some(&self.repo_root),
        readonly,
      )?
      .into_iter()
      // We are only interested in snapshots *directly* inside of
      // `repo_root`.
      .filter_map(|(path, gen_)| {
        // For relative paths, Path::parent returns Some("") if there is
        // no parent.
        if path.parent() == Some(Path::new("")) {
          path
            .file_name()
            .and_then(|snapshot| Snapshot::from_snapshot_name(snapshot).ok())
            .map(|snapshot| (snapshot, gen_))
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

  use serial_test::serial;

  use time_macros::datetime;

  use crate::snapshot::hostname;
  use crate::snapshot::utc_offset;
  use crate::snapshot::Subvol;
  use crate::test::with_btrfs;
  use crate::test::with_two_btrfs;
  use crate::test::BtrfsDev;
  use crate::test::Mount;


  /// Check that we can create a snapshot of a subvolume.
  #[test]
  #[serial]
  fn snapshot_creation() {
    let tag = "";

    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let repo = Repo::new(root.join("repo")).unwrap();

      let snapshot = repo.snapshot(&subvol, tag).unwrap();
      let content = read_to_string(repo.path().join(snapshot.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");
    })
  }

  /// Check that we can create a snapshot with a tag.
  #[test]
  #[serial]
  fn tagged_snapshot_creation() {
    let tag = "tagged";

    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let repo = Repo::new(root.join("repo")).unwrap();

      let snapshot = repo.snapshot(&subvol, tag).unwrap();
      assert_eq!(snapshot.tag, tag);

      let content = read_to_string(repo.path().join(snapshot.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");
    })
  }

  /// Make sure that we do not create a new snapshot if a subvolume has
  /// not changed over its most recent snapshot.
  #[test]
  #[serial]
  fn snapshot_creation_up_to_date() {
    let tag = "";

    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let repo = Repo::new(root).unwrap();

      let snapshot1 = repo.snapshot(&subvol, tag).unwrap();
      let snapshot2 = repo.snapshot(&subvol, tag).unwrap();
      assert_eq!(snapshot1, snapshot2);

      let snapshots = repo.snapshots().unwrap();
      assert_eq!(snapshots.len(), 1);
    })
  }

  /// Make sure that we do create a new snapshot if an untagged
  /// up-to-date snapshot exists, but not a tagged one.
  #[test]
  #[serial]
  fn snapshot_creation_up_to_date_tagged() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let repo = Repo::new(root).unwrap();

      let tag = "";
      let snapshot1 = repo.snapshot(&subvol, tag).unwrap();
      let tag = "different";
      let snapshot2 = repo.snapshot(&subvol, tag).unwrap();
      assert_ne!(snapshot1, snapshot2);

      let snapshots = repo.snapshots().unwrap();
      assert_eq!(snapshots.len(), 2);
    })
  }

  /// Make sure that we create a new snapshot if a subvolume has changed
  /// over its most recent snapshot.
  #[test]
  #[serial]
  fn snapshot_creation_on_change() {
    let tag = "";

    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let repo = Repo::new(root).unwrap();

      let snapshot1 = repo.snapshot(&subvol, tag).unwrap();
      let () = write(subvol.join("file"), "test43").unwrap();
      let snapshot2 = repo.snapshot(&subvol, tag).unwrap();
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
    let tag = "";

    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let repo = Repo::new(root.join("repo")).unwrap();

      let snapshot = repo.snapshot(&subvol, tag).unwrap();
      let mut snapshots = repo.snapshots().unwrap().into_iter();
      assert_eq!(snapshots.len(), 1);

      let next = snapshots.next().unwrap();
      assert_eq!(next.0.subvol, Subvol::new(&subvol));
      assert_eq!(next.0.subvol, snapshot.subvol);
      assert_ne!(next.1, 0);
    })
  }

  /// Check that our logic for finding the most recent snapshot works as
  /// expected.
  #[test]
  fn recent_snapshot_finding() {
    let subvols = [
      "host_documents_2023-03-21_22:20:23_",
      "host_documents_2023-03-21_23:00:51_tag2",
      "host_documents_2025-08-03_20:06:53_tag1",
      "host_documents_2025-08-07_18:24:40_tag1",
      "host_documents_2025-09-03_08:26:25_tag1",
      "host_local_2025-08-03_20:06:57_tag1",
      "host_local_2025-08-07_18:26:48_tag1",
      "host_local_2025-09-01_21:31:37_tag1",
      "host_local_2025-09-02_07:47:45_",
    ];

    let snapshots = subvols
      .iter()
      .enumerate()
      .map(|(gen_, subvol)| {
        let mut snapshot = Snapshot::from_snapshot_name(OsStr::new(subvol)).unwrap();
        snapshot.host = hostname().unwrap();
        (snapshot, gen_)
      })
      .collect::<Vec<_>>();
    assert!(snapshots.is_sorted());

    // /documents subvolume

    let subvol = Path::new("/documents");
    let tag = None;
    let (snapshot, _gen) = find_most_recent_snapshot(&snapshots, subvol, tag)
      .unwrap()
      .unwrap();
    assert_eq!(snapshot.subvol, Subvol::new(subvol));
    assert_eq!(
      snapshot.timestamp,
      datetime!(2025-09-03 08:26:25).assume_offset(utc_offset())
    );
    assert_eq!(snapshot.tag, "tag1");

    let tag = Some("");
    let (snapshot, _gen) = find_most_recent_snapshot(&snapshots, subvol, tag)
      .unwrap()
      .unwrap();
    assert_eq!(snapshot.subvol, Subvol::new(subvol));
    assert_eq!(
      snapshot.timestamp,
      datetime!(2023-03-21 22:20:23).assume_offset(utc_offset())
    );
    assert_eq!(snapshot.tag, tag.unwrap_or_default());

    let tag = Some("tag2");
    let (snapshot, _gen) = find_most_recent_snapshot(&snapshots, subvol, tag)
      .unwrap()
      .unwrap();
    assert_eq!(snapshot.subvol, Subvol::new(subvol));
    assert_eq!(
      snapshot.timestamp,
      datetime!(2023-03-21 23:00:51).assume_offset(utc_offset())
    );
    assert_eq!(snapshot.tag, tag.unwrap_or_default());

    // /local subvolume

    let subvol = Path::new("/local");
    let tag = None;
    let (snapshot, _gen) = find_most_recent_snapshot(&snapshots, subvol, tag)
      .unwrap()
      .unwrap();
    assert_eq!(snapshot.subvol, Subvol::new(subvol));
    assert_eq!(
      snapshot.timestamp,
      datetime!(2025-09-02 07:47:45).assume_offset(utc_offset())
    );
    assert_eq!(snapshot.tag, tag.unwrap_or_default());

    let tag = Some("tag2");
    let result = find_most_recent_snapshot(&snapshots, subvol, tag).unwrap();
    assert_eq!(result, None);

    let tag = Some("tag1");
    let (snapshot, _gen) = find_most_recent_snapshot(&snapshots, subvol, tag)
      .unwrap()
      .unwrap();
    assert_eq!(snapshot.subvol, Subvol::new(subvol));
    assert_eq!(
      snapshot.timestamp,
      datetime!(2025-09-01 21:31:37).assume_offset(utc_offset())
    );
    assert_eq!(snapshot.tag, tag.unwrap_or_default());
  }

  /// Make sure that we ignore snapshots outside of a repository.
  #[test]
  #[serial]
  fn snapshot_outside_repo() {
    let tag = "";

    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      // Our "business" repository.
      let repo = Repo::new(root.join("repo")).unwrap();

      // One repository in the root.
      let root_repo = Repo::new(root).unwrap();
      let _snapshot = root_repo.snapshot(&subvol, tag).unwrap();

      // And another one below ours.
      let sub_repo = Repo::new(repo.path().join("foobar")).unwrap();
      let _snapshot = sub_repo.snapshot(&subvol, tag).unwrap();

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
      let snapshot = Snapshot::builder().try_build(Path::new("/foobar")).unwrap();
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
    let tag = "";

    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let snapshot = backup(&src, &dst, &subvol, tag).unwrap();
      let content = read_to_string(dst.path().join(snapshot.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");
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

    let src_mount = Mount::builder()
      .options(["subvol=some-subvol"])
      .mount(src_loopdev.path())
      .unwrap();
    let src_root = src_mount.path();
    assert!(src_root.join("file").exists());

    let dst_loopdev = BtrfsDev::with_default().unwrap();
    let dst_mount = Mount::new(dst_loopdev.path()).unwrap();
    let dst_root = dst_mount.path();

    let src = Repo::new(src_root).unwrap();
    let dst = Repo::new(dst_root).unwrap();

    let subvol = src_mount.path();
    let () = write(subvol.join("file"), "test42").unwrap();

    let tag = "";
    let snapshot = backup(&src, &dst, subvol, tag).unwrap();
    let content = read_to_string(dst.path().join(snapshot.to_string()).join("file")).unwrap();
    assert_eq!(content, "test42");
  }

  /// Check that we error out as expected when attempting to backup a
  /// non-existent subvolume.
  #[test]
  #[serial]
  fn backup_non_existent_subvolume() {
    let tag = "";

    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let subvol = src_root.join("subvol");
      let error = backup(&src, &dst, &subvol, tag).unwrap_err();
      assert!(error.to_string().contains("No such file or directory"));
    })
  }

  /// Make sure that if the subvolume to backup is already up-to-date
  /// with respect to a snapshot, no additional work is done.
  #[test]
  #[serial]
  fn backup_subvolume_up_to_date() {
    let tag = "";

    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let snapshot1 = backup(&src, &dst, &subvol, tag).unwrap();
      let snapshot2 = backup(&src, &dst, &subvol, tag).unwrap();
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
    let tag = "";

    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let _snapshot = backup(&src, &dst, &subvol, tag).unwrap();

      for i in 0..20 {
        let string = "test".to_string() + &i.to_string();
        let () = write(subvol.join("file"), &string).unwrap();

        let snapshot = backup(&src, &dst, &subvol, tag).unwrap();
        let content = read_to_string(dst.path().join(snapshot.to_string()).join("file")).unwrap();
        assert_eq!(content, string);
      }
    })
  }

  /// Check that we can restore a subvolume from a snapshot.
  #[test]
  #[serial]
  fn restore_subvolume() {
    let tag = "";

    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      // Backup the subvolume to the destination repository.
      let snapshot = backup(&src, &dst, &subvol, tag).unwrap();
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
    let tag = "";

    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), "test42").unwrap();

      let snapshot = backup(&src, &dst, &subvol, tag).unwrap();
      let () = src.delete(&snapshot).unwrap();

      let snapshot_only = true;
      let () = restore(&dst, &src, &subvol, snapshot_only).unwrap();

      // The snapshot should be back with the respective content.
      let content = read_to_string(src.path().join(snapshot.to_string()).join("file")).unwrap();
      assert_eq!(content, "test42");
    })
  }

  /// Check that we fail subvolume restoration if the subvolume already
  /// exists.
  #[test]
  #[serial]
  fn restore_subvolume_exists() {
    let tag = "";

    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let snapshot = backup(&src, &dst, &subvol, tag).unwrap();
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
    let tag = "";

    with_two_btrfs(|src_root, dst_root| {
      let src = Repo::new(src_root).unwrap();
      let dst = Repo::new(dst_root).unwrap();

      let btrfs = Btrfs::new();
      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let snapshot = backup(&src, &dst, &subvol, tag).unwrap();
      // Then remove the just created snapshot.
      let () = dst.delete(&snapshot).unwrap();

      let snapshot_only = false;
      let error = restore(&dst, &src, &subvol, snapshot_only).unwrap_err();
      assert!(error.to_string().contains("No snapshot to restore found"));
    })
  }
}
