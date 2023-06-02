// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::let_and_return, clippy::let_unit_value)]

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
use crate::args::Command;
use crate::args::Snapshot;
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
  match args.command {
    Command::Snapshot(snapshot) => self::snapshot(snapshot),
  }
}
