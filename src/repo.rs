// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::fs::canonicalize;
use std::fs::create_dir_all;
use std::path::Path;
use std::path::PathBuf;

use anyhow::bail;
use anyhow::Context as _;
use anyhow::Result;

use crate::btrfs::Btrfs;


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
}
