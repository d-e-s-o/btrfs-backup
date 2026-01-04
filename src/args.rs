// Copyright (C) 2023-2026 Daniel Mueller <deso@posteo.net>
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

  Err(anyhow!("invalid duration provided: {s}"))
}


/// Parse a command from a string.
fn parse_command(s: &str) -> Result<(String, Vec<String>)> {
  // TODO: We currently don't support escaped inputs here but we really
  //       should, because right now a command itself cannot contain
  //       a space in its name (it would be parsed as a command with
  //       arguments).
  let mut iter = s.split(' ');
  let command = iter
    .next()
    .ok_or_else(|| anyhow!("provided command is empty"))?
    .to_string();
  let args = iter.map(str::to_string).collect();
  Ok((command, args))
}


/// The `--tag` argument.
#[derive(Debug, Arguments)]
pub struct Tag {
  /// The tag to use. The tag is stored in a snapshot's name. Only
  /// snapshots with the same tag are considered during purge.
  #[clap(long = "tag", default_value_t)]
  pub tag: String,
}


/// The `--remote-command` argument.
#[derive(Debug, Arguments)]
pub struct RemoteCommand {
  /// The remote command to use (and its arguments). This command will
  /// be used as a prefix for btrfs (and other) commands to execute,
  /// enabling for example backup to a remote system over ssh. As such,
  /// this command needs to accept a list of arguments directly, similar
  /// to `ssh` (and as opposed to assuming a quoted & escaped
  /// concatenation of said arguments as `sh -c` does).
  /// Note that this command may contain arguments separated by spaces.
  /// It is not currently possible to reference an executable that
  /// contains a space in its name.
  #[clap(long, value_parser = parse_command)]
  pub remote_command: Option<(String, Vec<String>)>,
}


/// A program for backup & restoration of btrfs subvolumes.
#[derive(Debug, Parser)]
#[clap(version = env!("VERSION"))]
pub struct Args {
  #[command(subcommand)]
  pub command: Command,
  /// Print a trace of all btrfs commands executed.
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
  #[command(flatten)]
  pub remote_command: RemoteCommand,
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
  #[command(flatten)]
  pub remote_command: RemoteCommand,
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
  #[command(flatten)]
  pub remote_command: RemoteCommand,
  /// The duration for which to keep snapshots. E.g., 3w (three weeks)
  /// or 1m (one month). Supported suffixes are 'd' (day), 'w' (week),
  /// 'm' (month), and 'y' (year). Snapshots older than that will get
  /// deleted.
  ///
  /// Please note that as a precaution, the most recent snapshot of a
  /// subvolume is never deleted.
  #[clap(long, value_parser = parse_duration)]
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


  /// Make sure that we can parse durations properly.
  #[test]
  fn command_parsing() {
    assert_eq!(
      parse_command("ssh").unwrap(),
      ("ssh".to_string(), Vec::new())
    );
    assert_eq!(
      parse_command("ssh server").unwrap(),
      ("ssh".to_string(), vec!["server".to_string()])
    );
  }
}
