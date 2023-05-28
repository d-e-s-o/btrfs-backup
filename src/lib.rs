// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::let_and_return, clippy::let_unit_value)]

mod btrfs;
#[cfg(test)]
mod test;
mod util;

use anyhow::Result;


/// Run the program and report errors, if any.
pub fn run() -> Result<()> {
  Ok(())
}
