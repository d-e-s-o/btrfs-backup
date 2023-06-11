// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::let_and_return, clippy::let_unit_value)]

#[macro_use]
mod redefine;

mod args;
mod btrfs;
mod repo;
mod snapshot;
#[cfg(test)]
mod test;
mod util;

use std::borrow::Cow;
use std::path::Path;

use anyhow::Context as _;
use anyhow::Result;

use clap::Parser as _;

use crate::args::Args;
use crate::args::Backup;
use crate::args::Command;
use crate::args::Restore;
use crate::args::Snapshot;
use crate::btrfs::trace_commands;
use crate::repo::backup as backup_subvol;
use crate::repo::restore as restore_subvol;
use crate::repo::Repo;


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


/// Handler for the `backup` sub-command.
fn backup(backup: Backup) -> Result<()> {
  let Backup {
    subvolumes,
    destination,
    source,
  } = backup;

  let src = if let Some(source) = source {
    Some(create_repo(&source)?)
  } else {
    None
  };

  let dst = create_repo(&destination)?;

  let () = subvolumes.iter().try_for_each::<_, Result<()>>(|subvol| {
    let src = if let Some(src) = &src {
      Cow::Borrowed(src)
    } else {
      let directory = subvol.parent().with_context(|| {
        format!(
          "subvolume {} does not have a parent; unable to store snapshots",
          subvol.display()
        )
      })?;
      Cow::Owned(create_repo(directory)?)
    };

    let _snapshot = backup_subvol(&src, &dst, subvol)
      .with_context(|| format!("failed to backup subvolume {}", subvol.display()))?;
    Ok(())
  })?;

  Ok(())
}


/// Handler for the `restore` sub-command.
fn restore(restore: Restore) -> Result<()> {
  let Restore {
    subvolumes,
    destination,
    source,
    snapshots_only,
  } = restore;

  let dst = if let Some(destination) = destination {
    Some(create_repo(&destination)?)
  } else {
    None
  };

  let src = create_repo(&source)?;

  let () = subvolumes.iter().try_for_each::<_, Result<()>>(|subvol| {
    let dst = if let Some(dst) = &dst {
      Cow::Borrowed(dst)
    } else {
      let directory = subvol.parent().with_context(|| {
        format!(
          "subvolume {} does not have a parent; unable to store snapshots",
          subvol.display()
        )
      })?;
      Cow::Owned(create_repo(directory)?)
    };

    let _snapshot = restore_subvol(&src, &dst, subvol, snapshots_only)
      .with_context(|| format!("failed to restore subvolume {}", subvol.display()))?;
    Ok(())
  })?;

  Ok(())
}


/// Handler for the `snapshot` sub-command.
fn snapshot(snapshot: Snapshot) -> Result<()> {
  let Snapshot {
    repository,
    subvolumes,
  } = snapshot;

  let repo = if let Some(repository) = repository {
    Some(create_repo(&repository)?)
  } else {
    None
  };

  let () = subvolumes.iter().try_for_each::<_, Result<()>>(|subvol| {
    let repo = if let Some(repo) = &repo {
      Cow::Borrowed(repo)
    } else {
      let directory = subvol.parent().with_context(|| {
        format!(
          "subvolume {} does not have a parent; unable to store snapshots",
          subvol.display()
        )
      })?;
      Cow::Owned(create_repo(directory)?)
    };

    let _snapshot = repo
      .snapshot(subvol)
      .with_context(|| format!("failed to snapshot subvolume {}", subvol.display()))?;
    Ok(())
  })?;

  Ok(())
}


/// Run the program and report errors, if any.
pub fn run() -> Result<()> {
  let args = Args::parse();

  if args.trace {
    let () = trace_commands();
  }

  match args.command {
    Command::Backup(backup) => self::backup(backup),
    Command::Restore(restore) => self::restore(restore),
    Command::Snapshot(snapshot) => self::snapshot(snapshot),
  }
}
