// Copyright (C) 2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::fmt::Debug;
use std::fs::canonicalize;
use std::fs::create_dir_all;
use std::fs::metadata;
use std::io::ErrorKind;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Result;


/// A trait representing the ability to perform certain file/path
/// related operations.
pub trait FileOps
where
  Self: Debug,
{
  /// Returns `true` if the provided `path` represents a directory.
  fn is_dir(&self, path: &Path) -> Result<bool>;

  /// Recursively create a directory and all of its parent components if
  /// they are missing.
  fn create_dir_all(&self, path: &Path) -> Result<()>;

  /// Returns the canonical, absolute form of a path with all
  /// intermediate components normalized and symbolic links resolved.
  fn canonicalize(&self, path: &Path) -> Result<PathBuf>;
}


/// Operations working on the local system.
#[derive(Clone, Debug, Default)]
pub struct LocalOps;

impl FileOps for LocalOps {
  /// Check whether a `path` references a directory.
  ///
  /// This function differs from [`std::path::Path::is_dir`] in that it
  /// only maps file-not-found errors into the `Ok` portion of the result.
  /// All other errors (such as permission denied) are reported verbatim.
  fn is_dir(&self, path: &Path) -> Result<bool> {
    match metadata(path) {
      Ok(info) => Ok(info.is_dir()),
      Err(err) if err.kind() == ErrorKind::NotFound => Ok(false),
      Err(err) => Err(err.into()),
    }
  }

  fn create_dir_all(&self, path: &Path) -> Result<()> {
    let () = create_dir_all(path)?;
    Ok(())
  }

  fn canonicalize(&self, path: &Path) -> Result<PathBuf> {
    let path = canonicalize(path)?;
    Ok(path)
  }
}
