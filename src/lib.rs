// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::let_and_return, clippy::let_unit_value)]

#[macro_use]
mod redefine;

mod args;
#[doc(hidden)]
pub mod btrfs;
mod repo;
#[doc(hidden)]
pub mod snapshot;
#[cfg(any(test, feature = "test"))]
pub mod test;
#[doc(hidden)]
pub mod util;

use std::borrow::Cow;
use std::ffi::OsString;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;
use anyhow::Result;

use clap::Parser as _;

use time::Duration;

use crate::args::Args;
use crate::args::Backup;
use crate::args::Command;
use crate::args::Purge;
use crate::args::Restore;
use crate::args::Snapshot;
use crate::btrfs::trace_commands;
use crate::repo::backup as backup_subvol;
use crate::repo::restore as restore_subvol;
use crate::repo::Repo;
use crate::snapshot::current_time;
use crate::snapshot::Subvol;
use crate::util::canonicalize_non_strict;


/// A helper function for creating a btrfs repository in the provided
/// directory, taking care of all error annotations.
fn create_repo(directory: &Path) -> Result<Repo> {
  let repo = Repo::new(directory).with_context(|| {
    format!(
      "failed to create btrfs snapshot repository at {}",
      directory.display()
    )
  })?;

  Ok(repo)
}


/// Perform an operation on a bunch of subvolumes, providing either a
/// single repository at the provided path or create a new one
/// co-located to each subvolume.
fn with_repo_and_subvols<F>(repo_path: Option<&Path>, subvols: &[PathBuf], f: F) -> Result<()>
where
  F: FnMut(&Repo, &Path) -> Result<()>,
{
  let mut f = f;

  let repo = if let Some(repo_path) = repo_path {
    Some(create_repo(repo_path)?)
  } else {
    None
  };

  let () = subvols.iter().try_for_each::<_, Result<()>>(|subvol| {
    let repo = if let Some(repo) = &repo {
      Cow::Borrowed(repo)
    } else {
      let directory = subvol.parent().with_context(|| {
        format!(
          "subvolume {} does not have a parent; need repository path",
          subvol.display()
        )
      })?;
      Cow::Owned(create_repo(directory)?)
    };

    f(&repo, subvol)
  })?;

  Ok(())
}


/// Handler for the `backup` sub-command.
fn backup(backup: Backup) -> Result<()> {
  let Backup {
    subvolumes,
    destination,
    source,
  } = backup;

  let dst = create_repo(&destination)?;

  with_repo_and_subvols(source.as_deref(), subvolumes.as_slice(), |src, subvol| {
    let _snapshot = backup_subvol(src, &dst, subvol)
      .with_context(|| format!("failed to backup subvolume {}", subvol.display()))?;
    Ok(())
  })
}


/// Handler for the `restore` sub-command.
fn restore(restore: Restore) -> Result<()> {
  let Restore {
    subvolumes,
    destination,
    source,
    snapshots_only,
  } = restore;

  let src = create_repo(&source)?;

  with_repo_and_subvols(
    destination.as_deref(),
    subvolumes.as_slice(),
    |dst, subvol| {
      let _snapshot = restore_subvol(&src, dst, subvol, snapshots_only)
        .with_context(|| format!("failed to restore subvolume {}", subvol.display()))?;
      Ok(())
    },
  )
}


/// Handler for the `purge` sub-command.
fn purge(purge: Purge) -> Result<()> {
  fn purge_subvol(repo: &Repo, subvol: &Path, keep_for: Duration) -> Result<()> {
    let subvol = canonicalize_non_strict(subvol)?;
    let snapshots = repo
      .snapshots()
      .context("failed to list snapshots")?
      .into_iter()
      .map(|(snapshot, _generation)| snapshot)
      .filter(|snapshot| snapshot.subvol == Subvol::new(&subvol));

    let current_time = current_time();
    let mut to_purge = snapshots
      .clone()
      .filter(|snapshot| current_time > snapshot.timestamp + keep_for);

    // If we are about to delete all snapshots for the provided
    // subvolume, make sure to keep the most recent one around.
    if to_purge.clone().count() == snapshots.clone().count() {
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


  let Purge {
    subvolumes,
    source,
    destination,
    keep_for,
  } = purge;

  if let Some(destination) = destination {
    let repo = create_repo(&destination)?;

    let () = subvolumes
      .iter()
      .try_for_each(|subvol| purge_subvol(&repo, subvol, keep_for))?;
  }

  // TODO: This logic is arguably a bit sub-optimal for the single-repo
  //       case, because we list snapshots for each subvolume.
  with_repo_and_subvols(source.as_deref(), subvolumes.as_slice(), |repo, subvol| {
    purge_subvol(repo, subvol, keep_for)
  })
}


/// Handler for the `snapshot` sub-command.
fn snapshot(snapshot: Snapshot) -> Result<()> {
  let Snapshot {
    repository,
    subvolumes,
  } = snapshot;

  with_repo_and_subvols(
    repository.as_deref(),
    subvolumes.as_slice(),
    |repo, subvol| {
      let _snapshot = repo
        .snapshot(subvol)
        .with_context(|| format!("failed to snapshot subvolume {}", subvol.display()))?;
      Ok(())
    },
  )
}


/// Run the program and report errors, if any.
pub fn run<A, T>(args: A) -> Result<()>
where
  A: IntoIterator<Item = T>,
  T: Into<OsString> + Clone,
{
  let args = Args::try_parse_from(args).context("failed to parse program arguments")?;

  if args.trace {
    let () = trace_commands();
  }

  match args.command {
    Command::Backup(backup) => self::backup(backup),
    Command::Purge(purge) => self::purge(purge),
    Command::Restore(restore) => self::restore(restore),
    Command::Snapshot(snapshot) => self::snapshot(snapshot),
  }
}
