// Copyright (C) 2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::path::PathBuf;

use anyhow::anyhow;
use anyhow::Result;

use clap::Args as Arguments;
use clap::Parser;
use clap::Subcommand;

use time::Duration;


/// Parse a duration from a string.
fn parse_duration(s: &str) -> Result<Duration> {
  // Yes, months and years may not be day-accurate. But hopefully it
  // will be good enough. *duck*
  let durations = [("d", 1), ("w", 7), ("m", 30), ("y", 365)];

  for (suffix, multiplier) in &durations {
    if let Some(base) = s.strip_suffix(suffix) {
      if let Ok(count) = base.parse::<u64>() {
        return Ok(Duration::days(i64::try_from(count)? * multiplier))
      }
    }
  }

  Err(anyhow!("invalid duration provided: {}", s))
}


/// The `--tag` argument.
#[derive(Debug, Arguments)]
pub struct Tag {
  /// The tag to use. The tag is stored in a snapshot's name. Only
  /// snapshots with the same tag are considered during purge.
  #[clap(long = "tag", default_value_t)]
  pub tag: String,
}


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
  /// Purge old snapshots by deleting them.
  Purge(Purge),
  /// Restore subvolumes from snapshots taken earlier.
  Restore(Restore),
  /// Create a snapshot of one or more subvolumes.
  Snapshot(Snapshot),
}

/// An type representing the `backup` command.
#[derive(Debug, Arguments)]
pub struct Backup {
  /// The subvolumes to backup.
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
  #[command(flatten)]
  pub tag: Tag,
}

/// An type representing the `restore` command.
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

/// An type representing the `purge` command.
#[derive(Debug, Arguments)]
pub struct Purge {
  /// The subvolumes for which to purge snapshots.
  pub subvolumes: Vec<PathBuf>,
  /// The path to the source "repository" containing snapshots.
  ///
  /// If not provided snapshots are assumed to be co-located with the
  /// subvolumes provided.
  #[clap(short, long)]
  pub source: Option<PathBuf>,
  /// An optional path to the destination "repository" to which
  /// snapshots were backed up.
  ///
  /// If this option is provided, snapshots may get deleted from your
  /// backup!
  #[clap(short, long)]
  pub destination: Option<PathBuf>,
  #[command(flatten)]
  pub tag: Tag,
  /// The duration for which to keep snapshots. E.g., 3w (three weeks)
  /// or 1m (one month). Supported suffixes are 'd' (day), 'w' (week),
  /// 'm' (month), and 'y' (year). Snapshots older than that will get
  /// deleted.
  ///
  /// Please note that as a precaution, the most recent snapshot of a
  /// subvolume is never deleted.
  #[arg(value_parser = parse_duration)]
  #[clap(long)]
  pub keep_for: Duration,
}

/// An type representing the `snapshot` command.
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
  #[command(flatten)]
  pub tag: Tag,
}


#[cfg(test)]
mod tests {
  use super::*;


  /// Make sure that we can parse durations properly.
  #[test]
  fn duration_parsing() {
    assert_eq!(parse_duration("1d").unwrap(), Duration::days(1));
    assert_eq!(parse_duration("23w").unwrap(), Duration::weeks(23));
    assert_eq!(parse_duration("2m").unwrap(), Duration::days(60));
    assert_eq!(parse_duration("3y").unwrap(), Duration::days(3 * 365));
    assert!(parse_duration("xxx")
      .unwrap_err()
      .to_string()
      .contains("invalid duration provided"));
  }
}
