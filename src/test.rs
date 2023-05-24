// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::cmp::min;
use std::ffi::OsStr;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::str;

use anyhow::Context as _;
use anyhow::Result;

use tempfile::NamedTempFile;

use crate::util::output;
use crate::util::run;
use crate::util::vec_to_path_buf;


/// The name of the `losetup` binary.
const LOSETUP: &str = "losetup";


/// A type representing loop back devices.
struct LoopDev {
  /// The path to the loop back device.
  device: PathBuf,
}

impl LoopDev {
  pub fn empty() -> Result<Self> {
    let mut path = output(LOSETUP, ["--find", "--nooverlap"])?;
    // Make sure to exclude the trailing newline that is unconditionally
    // emitted.
    let _last = path.pop();
    let path = vec_to_path_buf(path)?;

    Ok(Self { device: path })
  }

  /// Create a new loop device with the provided size (in bytes).
  pub fn new(size: usize) -> Result<Self> {
    static EMPTY: [u8; 4096] = [0; 4096];

    let mut file = NamedTempFile::new().context("failed to create temporary file")?;

    let mut n = 0;
    while n < size {
      let length = min(size - n, EMPTY.len());
      let count = file
        .write(&EMPTY[..length])
        .context("failed to zero out temporary file")?;
      n += count;
    }

    let mut slf = Self::empty()?;
    let () = slf.attach(file.path())?;

    // `file` is free to go out of scope here because we have bound the
    // file object to the loop device already, which will keep it
    // around while needed.

    Ok(slf)
  }

  /// Attach the loop device at the provided path.
  fn attach(&mut self, path: &Path) -> Result<()> {
    let () = run(LOSETUP, [&self.device, path]).with_context(|| {
      format!(
        "failed to attach file {} to loop device {}",
        path.display(),
        self.device.display()
      )
    })?;
    Ok(())
  }

  /// Destroy the loop device.
  fn destroy(&mut self) -> Result<()> {
    let () = run(LOSETUP, [OsStr::new("--detach"), self.device.as_os_str()])?;
    Ok(())
  }

  /// Retrieve the loop device's path.
  #[inline]
  pub fn path(&self) -> &Path {
    &self.device
  }
}

impl Drop for LoopDev {
  fn drop(&mut self) {
    let _ = self.destroy().unwrap_or_else(|error| {
      panic!(
        "failed to detach loop device {}: {error}",
        self.device.display()
      )
    });
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  use serial_test::serial;


  /// Check that we can create and destroy a loop device.
  #[test]
  #[serial]
  fn create_destroy_loopdev() {
    let _loopdev = LoopDev::new(1024).unwrap();
  }
}
