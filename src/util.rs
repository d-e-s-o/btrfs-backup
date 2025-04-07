// Copyright (C) 2022-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::borrow::Cow;
use std::env::current_dir;
use std::ffi::OsStr;
use std::ffi::OsString;
#[cfg(any(test, feature = "test"))]
use std::fmt::Display;
use std::fs::canonicalize;
use std::io;
use std::io::ErrorKind;
use std::os::unix::ffi::OsStrExt as _;
use std::path::Component;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;
use std::process::Stdio;

use anyhow::bail;
use anyhow::Context as _;
use anyhow::Result;


/// An enum used for wrapping two different iterator types.
#[derive(Clone, Debug)]
pub enum Either<L, R> {
  /// The first type.
  Left(L),
  /// The second type.
  Right(R),
}

impl<L, R, T> Iterator for Either<L, R>
where
  L: Iterator<Item = T>,
  R: Iterator<Item = T>,
{
  type Item = T;

  fn next(&mut self) -> Option<T> {
    match self {
      Self::Left(left) => left.next(),
      Self::Right(right) => right.next(),
    }
  }
}

impl<L, R, T> AsRef<T> for Either<L, R>
where
  L: AsRef<T>,
  R: AsRef<T>,
  T: ?Sized,
{
  fn as_ref(&self) -> &T {
    match self {
      Self::Left(left) => left.as_ref(),
      Self::Right(right) => right.as_ref(),
    }
  }
}


/// Join items with a character.
#[cfg(any(test, feature = "test"))]
pub fn join<I, T>(joiner: char, iter: I) -> Option<String>
where
  I: IntoIterator<Item = T>,
  T: Display,
{
  let mut iter = iter.into_iter();
  iter.next().map(|first| {
    iter.fold(first.to_string(), |list, item| {
      format!("{list}{joiner}{item}")
    })
  })
}


/// Concatenate a command and its arguments into a single string.
pub fn concat_command<C, A, S>(command: C, args: A) -> OsString
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S>,
  S: AsRef<OsStr>,
{
  args
    .into_iter()
    .fold(command.as_ref().to_os_string(), |mut cmd, arg| {
      cmd.push(OsStr::new(" "));
      cmd.push(arg.as_ref());
      cmd
    })
}


/// Format a command with the given list of arguments as a string.
pub fn format_command<C, A, S>(command: C, args: A) -> String
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S>,
  S: AsRef<OsStr>,
{
  concat_command(command, args).to_string_lossy().to_string()
}


/// Convert a byte slice into a [`Path`].
pub fn bytes_to_path(bytes: &[u8]) -> Cow<'_, Path> {
  AsRef::<Path>::as_ref(OsStr::from_bytes(bytes)).into()
}


/// Convert a byte vector into a [`PathBuf`].
#[cfg(any(test, feature = "test"))]
pub fn vec_to_path_buf(vec: Vec<u8>) -> Result<PathBuf> {
  use std::os::unix::ffi::OsStringExt as _;

  Ok(PathBuf::from(OsString::from_vec(vec)))
}


/// Normalize a path, removing current and parent directory components
/// (if possible).
// Compared to Cargo's "reference" implementation
// https://github.com/rust-lang/cargo/blob/fede83ccf973457de319ba6fa0e36ead454d2e20/src/cargo/util/paths.rs#L61
// we correctly handle something like '../x' (by leaving it alone). On
// the downside, we can end up with '..' components unresolved, if they
// are at the beginning of the path.
pub fn normalize(path: &Path) -> PathBuf {
  let components = path.components();
  let path = PathBuf::with_capacity(path.as_os_str().len());

  let mut path = components.fold(path, |mut path, component| {
    match component {
      Component::Prefix(..) | Component::RootDir => (),
      Component::CurDir => return path,
      Component::ParentDir => {
        if let Some(prev) = path.components().next_back() {
          match prev {
            Component::CurDir => {
              // SANITY: We can never have a current directory component
              //         inside `path` because we never added one to
              //         begin with.
              unreachable!()
            },
            Component::Prefix(..) | Component::RootDir | Component::ParentDir => (),
            Component::Normal(..) => {
              path.pop();
              return path
            },
          }
        }
      },
      Component::Normal(c) => {
        path.push(c);
        return path
      },
    }

    path.push(component.as_os_str());
    path
  });

  let () = path.shrink_to_fit();
  path
}


/// Perform best-effort canonicalization on the provided path.
///
/// Path components that do not exist do not cause the function to fail
/// and will be included in the result, with only normalization
/// performed on them.
pub fn canonicalize_non_strict(path: &Path) -> io::Result<PathBuf> {
  let mut path = path;
  let input = path;

  let resolved = loop {
    match canonicalize(path) {
      Ok(resolved) => break Cow::Owned(resolved),
      Err(err) if err.kind() == ErrorKind::NotFound => (),
      e => return e,
    }

    match path.parent() {
      None => {
        // We have reached the root. No point in attempting to
        // canonicalize further. We are done.
        path = Path::new("");
        break Cow::Borrowed(path)
      },
      Some(parent) if parent == Path::new("") => {
        // `path` is a relative path with a single component, so resolve
        // it to the current directory.
        path = parent;
        break Cow::Owned(current_dir()?)
      },
      Some(parent) => {
        // We need a bit of a dance here in order to get the parent path
        // but including the trailing path separator. That's necessary
        // for our path "subtraction" below to work correctly.
        let parent_len = parent.as_os_str().as_bytes().len();
        let path_bytes = path.as_os_str().as_bytes();
        // SANITY: We know that `path` has a parent (a true substring).
        //         Given that we are dealing with paths, we also know
        //         that a trailing path separator *must* exist, meaning
        //         we will always be in bounds.
        path = Path::new(OsStr::from_bytes(
          path_bytes
            .get(parent_len + 1..)
            .expect("constructed path has no trailing separator"),
        ));
      },
    }
  };

  let input_bytes = input.as_os_str().as_bytes();
  let path_len = path.as_os_str().as_bytes().len();
  // SANITY: We know that `path` is a substring of `input` and so we can
  //         never be out-of-bounds here.
  let unresolved = input_bytes
    .get(path_len..)
    .expect("failed to access input path sub-string");
  let complete = resolved.join(OsStr::from_bytes(unresolved));
  // We need to make sure to normalize the result here, because while
  // the unresolved part does not actually exist on the file system, it
  // could still contain symbolic references to the current or parent
  // directory that we do not want in the result.
  let normalized = normalize(&complete);
  Ok(normalized)
}


/// Run a command with the provided arguments, returning whether it
/// succeeded or not.
pub fn check<C, A, S>(command: C, args: A) -> Result<bool>
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S> + Clone,
  S: AsRef<OsStr>,
{
  let status = Command::new(command.as_ref())
    .stdin(Stdio::null())
    .stdout(Stdio::null())
    .stderr(Stdio::null())
    .args(args.clone())
    .status()
    .with_context(|| format!("failed to run `{}`", format_command(command.as_ref(), args)))?;

  Ok(status.success())
}

fn evaluate<C, A, S>(output: &Output, command: C, args: A) -> Result<()>
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S>,
  S: AsRef<OsStr>,
{
  if !output.status.success() {
    let code = if let Some(code) = output.status.code() {
      format!(" ({code})")
    } else {
      " (terminated by signal)".to_string()
    };

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stderr = stderr.trim_end();
    let stderr = if !stderr.is_empty() {
      format!(": {stderr}")
    } else {
      String::new()
    };

    bail!(
      "`{}` reported non-zero exit-status{code}{stderr}",
      format_command(command, args),
    );
  }
  Ok(())
}

/// Run a command with the provided arguments.
fn run_impl<C, A, S>(command: C, args: A, stdout: Stdio) -> Result<Output>
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S> + Clone,
  S: AsRef<OsStr>,
{
  let output = Command::new(command.as_ref())
    .stdin(Stdio::null())
    .stdout(stdout)
    .args(args.clone())
    .output()
    .with_context(|| {
      format!(
        "failed to run `{}`",
        format_command(command.as_ref(), args.clone())
      )
    })?;

  let () = evaluate(&output, command, args)?;
  Ok(output)
}

/// Run a command with the provided arguments.
pub fn run<C, A, S>(command: C, args: A) -> Result<()>
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S> + Clone,
  S: AsRef<OsStr>,
{
  let _output = run_impl(command, args, Stdio::null())?;
  Ok(())
}

/// Run a command and capture its output.
pub fn output<C, A, S>(command: C, args: A) -> Result<Vec<u8>>
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S> + Clone,
  S: AsRef<OsStr>,
{
  let output = run_impl(command, args, Stdio::piped())?;
  Ok(output.stdout)
}

pub fn pipeline<C1, A1, S1, C2, A2, S2>(
  command1: C1,
  args1: A1,
  command2: C2,
  args2: A2,
) -> Result<()>
where
  C1: AsRef<OsStr>,
  A1: IntoIterator<Item = S1> + Clone,
  S1: AsRef<OsStr>,
  C2: AsRef<OsStr>,
  A2: IntoIterator<Item = S2> + Clone,
  S2: AsRef<OsStr>,
{
  let mut child1 = Command::new(command1.as_ref())
    .stdin(Stdio::null())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .args(args1.clone())
    .spawn()
    .with_context(|| {
      format!(
        "failed to run `{}`",
        format_command(command1.as_ref(), args1.clone())
      )
    })?;

  // SANITY: We know that `child1` has a stdout pipe.
  let stdout = child1
    .stdout
    .take()
    .expect("created process does not have stdout set");

  let child2 = Command::new(command2.as_ref())
    .stdin(stdout)
    .stdout(Stdio::null())
    .stderr(Stdio::piped())
    .args(args2.clone())
    .spawn()
    .with_context(|| {
      format!(
        "failed to run `{}`",
        format_command(command2.as_ref(), args2.clone())
      )
    })?;

  let output1 = child1.wait_with_output().with_context(|| {
    format!(
      "failed to run `{}`",
      format_command(command1.as_ref(), args1.clone())
    )
  })?;
  let output2 = child2.wait_with_output().with_context(|| {
    format!(
      "failed to run `{}`",
      format_command(command2.as_ref(), args2.clone())
    )
  })?;

  let () = evaluate(&output1, command1, args1)?;
  let () = evaluate(&output2, command2, args2)?;
  Ok(())
}


/// Escape all occurrences of `character` in `string`.
///
/// # Panics
/// The function panics if `character` is anything but a single ASCII
/// character string.
pub fn escape(character: &str, string: &str) -> String {
  debug_assert_eq!(
    character.len(),
    1,
    "string to escape (`{character}`) is not a single ASCII character"
  );

  // We escape characters by duplicating them.
  string.replace(character, &(character.to_owned() + character))
}


/// Unescape all occurrences of `character` in `string`.
///
/// # Panics
/// The function panics if `character` is anything but a single ASCII
/// character string.
pub fn unescape(character: &str, string: &str) -> String {
  debug_assert_eq!(
    character.len(),
    1,
    "string to escape (`{character}`) is not a single ASCII character"
  );
  string.replace(&(character.to_owned() + character), character)
}


/// Split the provided `string` at the first occurrence of `character`
/// that has not been escaped. `character` is escaped if it is
/// immediately followed by another instance of `character`.
///
/// # Panics
/// The function panics if `character` is anything but a single ASCII
/// character string.
pub fn split_once_escaped<'str>(
  string: &'str str,
  character: &str,
) -> Option<(&'str str, &'str str)> {
  debug_assert_eq!(
    character.len(),
    1,
    "string to escape (`{character}`) is not a single ASCII character"
  );
  debug_assert!(string.is_ascii(), "{string}");

  let mut substr = string;
  let mut subidx = 0usize;

  while let Some(idx) = substr.find(character) {
    // Skip the character we just found.
    let mut next_idx = idx + 1;
    let next_str = substr.get(next_idx..)?;

    if !next_str.starts_with(character) {
      // If the character has not been escaped, we found our match.
      let first = string
        .get(..subidx + idx)
        .expect("calculated escape string sub-string out-of-bounds");
      return Some((first, next_str))
    } else {
      next_idx += 1;
    }

    substr = substr.get(next_idx..)?;
    subidx += next_idx;
  }
  None
}


#[cfg(test)]
mod tests {
  use super::*;

  use tempfile::TempDir;


  /// Verify that we can escape characters in strings and unescape them
  /// again.
  #[test]
  fn escape_unescape() {
    /// Check correctness of encoding and decoding functionality.
    fn test(string: &str, expected: &str) {
      let escaped = escape("_", string);
      assert_eq!(escaped, expected);

      let unescaped = unescape("_", &escaped);
      assert_eq!(unescaped, string);
    }

    test("", "");
    test("_", "__");
    test("a_", "a__");
    test("_a_", "__a__");
    test("a_b", "a__b");
    test("a__b", "a____b");
    test("a_b_c_d", "a__b__c__d");
    test("a_b_c_d__", "a__b__c__d____");
  }

  /// Check that we can split a string at certain separation characters,
  /// but handle escaped characters correctly.
  #[test]
  fn escaped_splitting() {
    assert_eq!(split_once_escaped("foo", "_"), None);
    assert_eq!(split_once_escaped("foo_", "_"), Some(("foo", "")));
    assert_eq!(split_once_escaped("foo_bar", "_"), Some(("foo", "bar")));
    assert_eq!(
      split_once_escaped("foo_bar_baz", "_"),
      Some(("foo", "bar_baz"))
    );
    assert_eq!(
      split_once_escaped("foo__bar_baz", "_"),
      Some(("foo__bar", "baz"))
    );
    assert_eq!(
      split_once_escaped("foo_bar__baz", "_"),
      Some(("foo", "bar__baz"))
    );
    assert_eq!(split_once_escaped("foo__bar", "_"), None);
    assert_eq!(split_once_escaped("foo__", "_"), None);
    assert_eq!(split_once_escaped("foo__bar__baz", "_"), None);
    assert_eq!(split_once_escaped("_bar_baz", "_"), Some(("", "bar_baz")));
    assert_eq!(split_once_escaped("__bar_baz", "_"), Some(("__bar", "baz")));
    assert_eq!(split_once_escaped("_", "_"), Some(("", "")));
    assert_eq!(split_once_escaped("__", "_"), None);
  }

  /// Check that we can normalize paths as expected.
  #[test]
  fn path_normalization() {
    assert_eq!(normalize(Path::new("tmp/foobar/..")), Path::new("tmp"));
    assert_eq!(normalize(Path::new("/tmp/foobar/..")), Path::new("/tmp"));
    assert_eq!(normalize(Path::new("/tmp/.")), Path::new("/tmp"));
    assert_eq!(normalize(Path::new("/tmp/./blah")), Path::new("/tmp/blah"));
    assert_eq!(normalize(Path::new("/tmp/../blah")), Path::new("/blah"));
    assert_eq!(normalize(Path::new("./foo")), Path::new("foo"));
    assert_eq!(
      normalize(Path::new("./foo/")).as_os_str(),
      Path::new("foo").as_os_str()
    );
    assert_eq!(normalize(Path::new("foo")), Path::new("foo"));
    assert_eq!(
      normalize(Path::new("foo/")).as_os_str(),
      Path::new("foo").as_os_str()
    );
    assert_eq!(normalize(Path::new("../foo")), Path::new("../foo"));
    assert_eq!(normalize(Path::new("../foo/")), Path::new("../foo"));
    assert_eq!(
      normalize(Path::new("./././relative-dir-that-does-not-exist/../file")),
      Path::new("file")
    );
  }

  /// Test that we can canonicalize paths on a best-effort basis.
  #[test]
  fn non_strict_canonicalization() {
    let dir = current_dir().unwrap();
    let path = Path::new("relative-path-that-does-not-exist");
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(real, dir.join(path));

    let dir = current_dir().unwrap();
    let path = Path::new("relative-path-that-does-not-exist/");
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(
      real.as_os_str(),
      dir
        .join(Path::new("relative-path-that-does-not-exist"))
        .as_os_str()
    );

    let path = Path::new("relative-dir-that-does-not-exist/file");
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(real, dir.join(path));

    let path = Path::new("./relative-dir-that-does-not-exist/file");
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(real, dir.join(normalize(path)));

    let path = Path::new("./././relative-dir-that-does-not-exist/../file");
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(real, dir.join("file"));

    let path = Path::new("../relative-path-that-does-not-exist");
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(
      real,
      dir
        .parent()
        .unwrap()
        .join("relative-path-that-does-not-exist")
    );

    let path = Path::new("../relative-dir-that-does-not-exist/file");
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(
      real,
      dir
        .parent()
        .unwrap()
        .join("relative-dir-that-does-not-exist/file")
    );

    let path = Path::new("/absolute-path-that-does-not-exist");
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(real, path);

    let path = Path::new("/absolute-dir-that-does-not-exist/file");
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(real, path);

    let dir = TempDir::new().unwrap();
    let dir = dir.path();

    let path = dir;
    let real = canonicalize_non_strict(path).unwrap();
    assert_eq!(real, path);

    let path = dir.join("foobar");
    let real = canonicalize_non_strict(&path).unwrap();
    assert_eq!(real, path);
  }
}
