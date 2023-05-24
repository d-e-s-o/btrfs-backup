// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::borrow::Cow;
use std::ffi::OsStr;
#[cfg(test)]
use std::fmt::Display;
use std::ops::Deref as _;
use std::os::unix::ffi::OsStrExt as _;
use std::path::Path;
#[cfg(test)]
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;
use std::process::Stdio;

use anyhow::bail;
use anyhow::Context as _;
use anyhow::Result;


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
#[cfg(test)]
pub fn vec_to_path_buf(vec: Vec<u8>) -> Result<PathBuf> {
  use std::ffi::OsString;
  use std::os::unix::ffi::OsStringExt as _;

  Ok(PathBuf::from(OsString::from_vec(vec)))
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
