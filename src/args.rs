// Copyright (C) 2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::path::PathBuf;

use clap::Args as Arguments;
use clap::Parser;
use clap::Subcommand;


/// A program for backup & restoration of btrfs subvolumes.
#[derive(Debug, Parser)]
pub struct Args {
  #[command(subcommand)]
  pub command: Command,
}

#[derive(Debug, Subcommand)]
pub enum Command {
  /// Create a snapshot of one or more subvolumes.
  Snapshot(Snapshot),
}

/// An enumeration representing the `snapshot` command.
#[derive(Debug, Arguments)]
pub struct Snapshot {
  /// The subvolumes to snapshot.
  pub subvolumes: Vec<PathBuf>,
  /// The path to the "repository" to create the snapshots in.
  ///
  /// If not provided, snapshots will be co-located with the very
  /// subvolume being snapshot.
  #[clap(short, long)]
  pub repository: Option<PathBuf>,
}
