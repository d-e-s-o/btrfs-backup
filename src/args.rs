// Copyright (C) 2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::path::PathBuf;

use clap::Args as Arguments;
use clap::Parser;
use clap::Subcommand;


/// A program for backup & restoration of btrfs subvolumes.
#[derive(Debug, Parser)]
#[clap(version = env!("VERSION"))]
pub struct Args {
  #[command(subcommand)]
  pub command: Command,
  /// Print a trace of all commands executed.
  #[clap(long = "trace", global = true)]
  pub trace: bool,
}

#[derive(Debug, Subcommand)]
pub enum Command {
  /// Backup one or more subvolumes from one btrfs file system to
  /// another.
  Backup(Backup),
  /// Restore subvolumes from snapshots taken earlier.
  Restore(Restore),
  /// Create a snapshot of one or more subvolumes.
  Snapshot(Snapshot),
}

/// An enumeration representing the `backup` command.
#[derive(Debug, Arguments)]
pub struct Backup {
  /// The subvolumes to snapshot.
  pub subvolumes: Vec<PathBuf>,
  /// The path to the source "repository" to create the snapshots in.
  ///
  /// If not provided, snapshots will be co-located with the very
  /// subvolume being backed up.
  #[clap(short, long)]
  pub source: Option<PathBuf>,
  /// The path to the destination "repository" to back up the subvolumes
  /// to.
  #[clap(short, long)]
  pub destination: PathBuf,
}

/// An enumeration representing the `restore` command.
#[derive(Debug, Arguments)]
pub struct Restore {
  /// The subvolumes to restore.
  pub subvolumes: Vec<PathBuf>,
  /// The path to the source "repository" containing backup snapshots.
  #[clap(short, long)]
  pub source: PathBuf,
  /// The path to the destination "repository" to restore snapshots to.
  ///
  /// If not provided, snapshots will be co-located with the very
  /// subvolume being restored.
  #[clap(short, long)]
  pub destination: Option<PathBuf>,
  /// Whether or not to only restore snapshots, not actual subvolumes
  /// they represent.
  #[clap(long)]
  pub snapshots_only: bool,
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
