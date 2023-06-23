// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::borrow::Cow;
use std::ffi::OsStr;
#[cfg(any(test, feature = "test"))]
use std::fmt::Display;
use std::ops::Deref as _;
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


/// Format a command with the given list of arguments as a string.
pub fn format_command<C, A, S>(command: C, args: A) -> String
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S>,
  S: AsRef<OsStr>,
{
  args.into_iter().fold(
    command.as_ref().to_string_lossy().into_owned(),
    |mut cmd, arg| {
      cmd += " ";
      cmd += arg.as_ref().to_string_lossy().deref();
      cmd
    },
  )
}


/// Convert a byte slice into a [`Path`].
pub fn bytes_to_path(bytes: &[u8]) -> Cow<'_, Path> {
  AsRef::<Path>::as_ref(OsStr::from_bytes(bytes)).into()
}


/// Convert a byte vector into a [`PathBuf`].
#[cfg(any(test, feature = "test"))]
pub fn vec_to_path_buf(vec: Vec<u8>) -> Result<PathBuf> {
  use std::ffi::OsString;
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
    .with_context(|| {
      format!(
        "failed to run `{}`",
        format_command(command.as_ref(), args.clone())
      )
    })?;

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
  let stdout = child1.stdout.take().unwrap();

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
      let first = string.get(..subidx + idx).unwrap();
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
    assert_eq!(normalize(Path::new("foo")), Path::new("foo"));
    assert_eq!(normalize(Path::new("../foo")), Path::new("../foo"));
  }
}
