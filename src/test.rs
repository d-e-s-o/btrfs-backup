// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::cmp::min;
use std::ffi::OsStr;
use std::fmt::Display;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::str;

use anyhow::Context as _;
use anyhow::Result;

use tempfile::NamedTempFile;
use tempfile::TempDir;

use crate::util::join;
use crate::util::output;
use crate::util::run;
use crate::util::vec_to_path_buf;


/// The name of the `losetup` binary.
const LOSETUP: &str = "losetup";
/// The name of the `mkfs.btrfs` binary.
const MKBTRFS: &str = "mkfs.btrfs";
/// The name of the `mount` binary.
const MOUNT: &str = "mount";
/// The name of the `umount` binary.
const UMOUNT: &str = "umount";


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


/// A loop back device containing a btrfs file system.
pub struct BtrfsDev {
  /// The used loop back device.
  device: LoopDev,
}

impl BtrfsDev {
  /// Create a new btrfs loop back device with the provided size (in
  /// bytes).
  pub fn new(size: usize) -> Result<Self> {
    let device = LoopDev::new(size)?;
    let () = run(MKBTRFS, [device.path()])?;

    Ok(Self { device })
  }

  /// Create a new btrfs loop back device with the default size (which
  /// is close to the supported minimum).
  pub fn with_default() -> Result<Self> {
    // 109 MiB seems to be the current lowest size of a btrfs volume.
    // Give it some more.
    Self::new(128 * 1024 * 1024)
  }

  /// Retrieve the btrfs file system's path.
  #[inline]
  pub fn path(&self) -> &Path {
    self.device.path()
  }
}


/// An object representing a mounted file system.
pub struct Mount {
  /// The directory in which the file system was mounted.
  directory: TempDir,
}

impl Mount {
  /// Mount the provided device in a temporary directory.
  pub fn new(device: &Path) -> Result<Self> {
    let no_options = [""; 0];
    Self::with_options(device, no_options)
  }

  /// Mount the provided device in a temporary directory, providing the
  /// given set of options to the `mount(8)` command.
  pub fn with_options<O, S>(device: &Path, options: O) -> Result<Self>
  where
    O: IntoIterator<Item = S>,
    S: AsRef<str> + Display,
  {
    let directory = TempDir::new()?;
    let options = join(',', options.into_iter());

    let () = if let Some(options) = options {
      run(
        MOUNT,
        [
          device.as_os_str(),
          directory.path().as_os_str(),
          OsStr::new("-o"),
          options.as_ref(),
        ],
      )
    } else {
      run(MOUNT, [device.as_os_str(), directory.path().as_os_str()])
    }?;

    Ok(Self { directory })
  }

  /// Retrieve the path of the mount.
  #[inline]
  pub fn path(&self) -> &Path {
    self.directory.path()
  }
}

impl Drop for Mount {
  fn drop(&mut self) {
    let () = run(UMOUNT, [self.directory.path()]).unwrap_or_else(|error| {
      panic!(
        "failed to unmount {}: {error}",
        self.directory.path().display()
      )
    });
  }
}


/// Create and mount a btrfs file system and invoke a function on it.
pub fn with_btrfs<F>(f: F)
where
  F: FnOnce(&Path),
{
  let loopdev = BtrfsDev::with_default().unwrap();
  let mount = Mount::new(loopdev.path()).unwrap();

  f(mount.path())
}


/// Create and mount two btrfs file systems and invoke a function on
/// them.
pub fn with_two_btrfs<F>(f: F)
where
  F: FnOnce(&Path, &Path),
{
  let loopdev1 = BtrfsDev::with_default().unwrap();
  let mount1 = Mount::new(loopdev1.path()).unwrap();

  let loopdev2 = BtrfsDev::with_default().unwrap();
  let mount2 = Mount::new(loopdev2.path()).unwrap();

  f(mount1.path(), mount2.path())
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

  /// Check that we can create and mount btrfs file system.
  #[test]
  #[serial]
  fn create_mount_btrfs() {
    let loopdev = BtrfsDev::with_default().unwrap();
    let _mount = Mount::new(loopdev.path()).unwrap();
  }
}
