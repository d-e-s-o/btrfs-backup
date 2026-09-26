// Copyright (C) 2023-2026 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::ffi::OsStr;
use std::ffi::OsString;
use std::fmt::Debug;
use std::fs::canonicalize;
use std::fs::create_dir_all;
use std::fs::metadata;
use std::io::ErrorKind;
use std::iter;
use std::os::unix::ffi::OsStringExt as _;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Result;

use crate::util::check;
use crate::util::output;
use crate::util::run;
use crate::util::Either;


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


/// Operations working on a remote system.
#[derive(Debug)]
pub struct RemoteOps {
  /// The command to use for connecting to the remote.
  command: OsString,
  /// Arguments to provide to the command.
  args: Vec<OsString>,
}

impl RemoteOps {
  /// Create a new `RemoteOps` instance, using the provided command
  /// (along with the arguments) for prefixing any shell commands
  /// issued.
  pub fn new<C, A, S>(command: C, args: A) -> Self
  where
    C: AsRef<OsStr>,
    A: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
  {
    Self {
      command: command.as_ref().to_os_string(),
      args: args
        .into_iter()
        .map(|arg| arg.as_ref().to_os_string())
        .collect(),
    }
  }

  // TODO: Merge this function with `Btrfs::command`.
  fn command<'slf, C, A, S>(
    &'slf self,
    command: C,
    args: A,
  ) -> (
    impl AsRef<OsStr> + Clone + 'slf,
    impl IntoIterator<Item = impl AsRef<OsStr> + Clone + 'slf> + Clone + 'slf,
  )
  where
    C: AsRef<OsStr> + Clone + 'slf,
    A: IntoIterator<Item = S> + 'slf,
    A::IntoIter: Clone,
    S: AsRef<OsStr> + Clone + 'slf,
  {
    let mut iter = iter::once(AsRef::<OsStr>::as_ref(&self.command))
      .chain(self.args.iter().map(OsString::as_ref))
      .map(Either::Left)
      .chain(iter::once(Either::Right(Either::Left(command))))
      .chain(args.into_iter().map(Either::Right).map(Either::Right));

    // SANITY: There will always be at least `self.command` in `iter`.
    let command = iter.next().expect("constructed command is empty");
    (command, iter)
  }
}


fn trim_trailing_whitespace(bytes: &mut Vec<u8>) {
  let len = bytes
    .iter()
    .rposition(|b| !b.is_ascii_whitespace())
    .map_or(0, |i| i + 1);

  bytes.truncate(len);
}


// Note: we use short options here because there is a belief that they
//       are more widely supported. busybox or other providers of
//       similar functionality may not support `mkdir --parents`, for
//       example.
impl FileOps for RemoteOps {
  fn is_dir(&self, path: &Path) -> Result<bool> {
    let (command, args) = self.command("test", ["-d".as_ref(), path.as_os_str()]);
    check(command, args)
  }

  fn create_dir_all(&self, path: &Path) -> Result<()> {
    let (command, args) = self.command("mkdir", ["-p".as_ref(), path.as_os_str()]);
    run(command, args)
  }

  fn canonicalize(&self, path: &Path) -> Result<PathBuf> {
    let (command, args) = self.command("readlink", ["-e".as_ref(), path.as_os_str()]);
    let mut output = output(command, args)?;
    // Make sure to remove trailing newline.
    let () = trim_trailing_whitespace(&mut output);
    Ok(PathBuf::from(OsString::from_vec(output)))
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  use std::os::unix::fs::symlink;

  use tempfile::TempDir;


  /// Check that we can trim trailing whitespaces on a `Vec<u8>`.
  #[test]
  fn trailing_whitespace_trimming() {
    let cases = [
      (b"foo".as_slice(), b"foo".as_slice()),
      (b"foo ".as_slice(), b"foo".as_slice()),
      (b"foo\t".as_slice(), b"foo".as_slice()),
      (b"foo\n".as_slice(), b"foo".as_slice()),
      (b"foo\r\n\t ".as_slice(), b"foo".as_slice()),
      (b"\tfoo".as_slice(), b"\tfoo".as_slice()),
      (b" foo ".as_slice(), b" foo".as_slice()),
      (b"   ".as_slice(), b"".as_slice()),
      (b"".as_slice(), b"".as_slice()),
      // Non-whitespace bytes should be preserved.
      (b"foo\xff\t".as_slice(), b"foo\xff".as_slice()),
    ];

    for (input, expected) in cases {
      let mut bytes = input.to_vec();
      let () = trim_trailing_whitespace(&mut bytes);
      assert_eq!(bytes, expected, "input: {input:?}");
    }
  }


  fn sh() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("var")
      .join("sh-run")
  }


  fn for_each_file_op(test_fn: fn(&dyn FileOps)) {
    let local_ops = LocalOps;
    let remote_ops = RemoteOps::new(sh(), [""; 0]);

    [&local_ops as &dyn FileOps, &remote_ops as &dyn FileOps]
      .into_iter()
      .for_each(test_fn)
  }


  /// Test that we can correctly check whether a path represents a
  /// directory.
  #[test]
  fn directory_check() {
    fn test(ops: &dyn FileOps) {
      let path = {
        let directory = TempDir::new().unwrap();
        assert!(ops.is_dir(directory.path()).unwrap());
        directory.path().to_path_buf()
      };

      assert!(!ops.is_dir(&path).unwrap())
    }

    for_each_file_op(test)
  }


  /// Check that we can correctly create directories.
  #[test]
  fn directory_creation() {
    fn test(ops: &dyn FileOps) {
      let directory = TempDir::new().unwrap();
      let subdir = directory.path().join("foobar").join("baz");

      let () = ops.create_dir_all(&subdir).unwrap();
      assert!(ops.is_dir(directory.path()).unwrap());
    }

    for_each_file_op(test)
  }


  /// Check that we can canonicalize paths properly.
  #[test]
  fn path_canonicalization() {
    fn test(ops: &dyn FileOps) {
      let directory = TempDir::new().unwrap();
      let subdir = directory.path().join("sub-dir");
      let path = subdir.join(".").join("..").join("sub-dir");
      // Canonicalization should not succeed because the path does not
      // exist. We can't check for much more than *that* we encountered
      // an error here, unfortunately.
      let _err = ops.canonicalize(&path).unwrap_err();

      let () = ops.create_dir_all(&subdir).unwrap();
      let canonical = ops.canonicalize(&path).unwrap();
      let suffix = canonical.strip_prefix(directory.path()).unwrap();
      assert_eq!(suffix, Path::new("sub-dir"));

      let link = directory.path().join("symlink");
      let () = symlink(subdir, &link).unwrap();

      let canonical = ops.canonicalize(&link).unwrap();
      let suffix = canonical.strip_prefix(directory.path()).unwrap();
      assert_eq!(suffix, Path::new("sub-dir"));
    }

    for_each_file_op(test)
  }
}
