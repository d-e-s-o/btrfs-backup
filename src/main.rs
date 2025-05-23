// Copyright (C) 2022-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A program for backup & restoration of btrfs subvolumes.

use std::env::args_os;

use anyhow::Result;

use btrfs_backup::run;


fn main() -> Result<()> {
  let args = args_os();
  run(args)
}
