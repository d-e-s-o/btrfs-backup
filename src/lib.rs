// Copyright (C) 2022-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A program for backup & restoration of btrfs subvolumes.

#[macro_use]
mod redefine;

mod args;
#[doc(hidden)]
pub mod btrfs;
mod ops;
mod repo;
#[doc(hidden)]
pub mod snapshot;
#[allow(missing_docs, clippy::unwrap_used)]
#[cfg(any(test, feature = "test"))]
pub mod test;
#[doc(hidden)]
pub mod util;

use std::borrow::Cow;
use std::ffi::OsString;
use std::fs::canonicalize;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;
use anyhow::Error;
use anyhow::Result;

use clap::error::ErrorKind;
use clap::Parser as _;

use crate::args::Args;
use crate::args::Backup;
use crate::args::Command;
use crate::args::Purge;
use crate::args::RemoteCommand;
use crate::args::Restore;
use crate::args::Snapshot;
use crate::args::Tag;
use crate::btrfs::trace_commands;
use crate::btrfs::Btrfs;
use crate::ops::RemoteOps;
use crate::repo::backup as backup_subvol;
use crate::repo::purge as purge_subvol;
use crate::repo::restore as restore_subvol;
use crate::repo::Repo;
use crate::util::canonicalize_non_strict;


/// A helper function for creating a btrfs repository in the provided
/// directory, taking care of all error annotations.
fn create_repo(directory: &Path, remote_command: Option<(String, Vec<String>)>) -> Result<Repo> {
  let mut builder = Repo::builder();

  if let Some((command, args)) = remote_command {
    let ops = RemoteOps::new(command.clone(), args.clone());
    let () = builder.set_file_ops(ops);

    let btrfs = Btrfs::with_command_prefix(command, args);
    let () = builder.set_btrfs_ops(btrfs);
  }

  let repo = builder.build(directory).with_context(|| {
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
    Some(create_repo(repo_path, None)?)
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
      Cow::Owned(create_repo(directory, None)?)
    };

    f(&repo, subvol)
  })?;

  Ok(())
}


/// Handler for the `backup` sub-command.
fn backup(backup: Backup) -> Result<()> {
  let Backup {
    mut subvolumes,
    destination,
    source,
    tag: Tag { tag },
    remote_command: RemoteCommand { remote_command },
  } = backup;

  let () = subvolumes.iter_mut().try_for_each(|subvol| {
    *subvol = canonicalize(&*subvol)?;
    Result::<(), Error>::Ok(())
  })?;

  let dst = create_repo(&destination, remote_command)?;

  with_repo_and_subvols(source.as_deref(), subvolumes.as_slice(), |src, subvol| {
    let _snapshot = backup_subvol(src, &dst, subvol, &tag)
      .with_context(|| format!("failed to backup subvolume {}", subvol.display()))?;
    Ok(())
  })
}


/// Handler for the `restore` sub-command.
fn restore(restore: Restore) -> Result<()> {
  let Restore {
    mut subvolumes,
    destination,
    source,
    remote_command: RemoteCommand { remote_command },
    snapshots_only,
  } = restore;

  let () = subvolumes.iter_mut().try_for_each(|subvol| {
    *subvol = canonicalize_non_strict(subvol)?;
    Result::<(), Error>::Ok(())
  })?;

  let src = create_repo(&source, remote_command)?;

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
  let Purge {
    mut subvolumes,
    source,
    destination,
    tag: Tag { tag },
    remote_command: RemoteCommand { remote_command },
    keep_for,
  } = purge;

  let () = subvolumes.iter_mut().try_for_each(|subvol| {
    *subvol = canonicalize_non_strict(subvol)?;
    Result::<(), Error>::Ok(())
  })?;

  if let Some(destination) = destination {
    let repo = create_repo(&destination, remote_command)?;

    let () = subvolumes
      .iter()
      .try_for_each(|subvol| purge_subvol(&repo, subvol, &tag, keep_for))?;
  }

  // TODO: This logic is arguably a bit sub-optimal for the single-repo
  //       case, because we list snapshots for each subvolume.
  with_repo_and_subvols(source.as_deref(), subvolumes.as_slice(), |repo, subvol| {
    purge_subvol(repo, subvol, &tag, keep_for)
  })
}


/// Handler for the `snapshot` sub-command.
fn snapshot(snapshot: Snapshot) -> Result<()> {
  let Snapshot {
    repository,
    mut subvolumes,
    tag: Tag { tag },
  } = snapshot;

  let () = subvolumes.iter_mut().try_for_each(|subvol| {
    *subvol = canonicalize(&*subvol)?;
    Result::<(), Error>::Ok(())
  })?;

  with_repo_and_subvols(
    repository.as_deref(),
    subvolumes.as_slice(),
    |repo, subvol| {
      let _snapshot = repo
        .snapshot(subvol, &tag)
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
  let args = match Args::try_parse_from(args) {
    Ok(args) => args,
    Err(err) => match err.kind() {
      ErrorKind::DisplayHelp | ErrorKind::DisplayVersion => {
        print!("{err}");
        return Ok(())
      },
      _ => return Err(err.into()),
    },
  };

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


#[cfg(test)]
mod tests {
  use super::*;

  use std::ffi::OsStr;


  /// Check that we do not error out on the --version option.
  #[test]
  fn version() {
    let args = [OsStr::new("btrfs-backup"), OsStr::new("--version")];
    let () = run(args).unwrap();
  }

  /// Check that we do not error out on the --help option.
  #[test]
  fn help() {
    let args = [OsStr::new("btrfs-backup"), OsStr::new("--help")];
    let () = run(args).unwrap();
  }
}
