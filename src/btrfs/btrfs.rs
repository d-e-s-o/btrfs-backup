// Copyright (C) 2023-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A module providing a fully-typed programmatic interface to
//! btrfs functionality by shelling out to btrfs-progs.

use std::borrow::Cow;
use std::ffi::OsStr;
use std::ffi::OsString;
use std::iter;
use std::path::Path;
use std::path::PathBuf;
use std::str::FromStr as _;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::LazyLock;

use anyhow::Context as _;
use anyhow::Result;

use regex::Regex;

use crate::ops::FileOps;
use crate::util::bytes_to_path;
use crate::util::check;
use crate::util::format_command;
use crate::util::output;
use crate::util::pipeline;
use crate::util::run;
use crate::util::Either;

use super::commands;

const BTRFS: &str = "btrfs";

const NUMS_STRING: &str = r"[0-9]+";
const PATH_STRING: &str = r".+";
/// The format of a line as retrieved by executing the command returned
/// by the `snapshots()` method. Each line is expected to be following
/// the pattern:
/// ID A gen B top level C path PATH
static SNAPSHOTS_LINE_REGEX: LazyLock<Regex> = LazyLock::new(|| {
  Regex::new(&format!(
      r"^ID {NUMS_STRING} gen (?P<gen>{NUMS_STRING}) top level {NUMS_STRING} path (?P<path>{PATH_STRING})$"
  )).expect("failed to create snapshot regular expression")
});
/// The marker ending the file list reported by the `subvolume find-new`
/// command. If this marker is the only thing reported then no files
/// have changed.
static DIFF_END_MARKER: &[u8] = b"transid marker";

/// A flag indicating whether to print traces of all commands executed.
static TRACE_COMMANDS: AtomicBool = AtomicBool::new(false);


/// Enable command tracing, i.e., printing of all executed commands to
/// stdout.
#[inline]
pub fn trace_commands() {
  TRACE_COMMANDS.store(true, Ordering::Relaxed)
}


/// A type for performing various btrfs related operations.
#[derive(Clone, Debug, Default)]
pub struct Btrfs {
  /// Command & arguments to prefix each btrfs command with.
  command: Option<(OsString, Vec<OsString>)>,
}

impl Btrfs {
  /// Create a new `Btrfs` instance.
  pub fn new() -> Self {
    Self { command: None }
  }

  /// Create a `Btrfs` instance that prefixes all `btrfs` commands with
  /// he given one (and its arguments).
  pub fn with_command_prefix<C, A, S>(command: C, args: A) -> Self
  where
    C: AsRef<OsStr>,
    A: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
  {
    let command = command.as_ref().to_os_string();
    let args = args
      .into_iter()
      .map(|arg| arg.as_ref().to_os_string())
      .collect();

    Self {
      command: Some((command, args)),
    }
  }

  fn command<'slf, A, S>(
    &'slf self,
    args: A,
  ) -> (
    impl AsRef<OsStr> + Clone + 'slf,
    impl IntoIterator<Item = impl AsRef<OsStr> + Clone + 'slf> + Clone + 'slf,
  )
  where
    A: IntoIterator<Item = S> + 'slf,
    A::IntoIter: Clone,
    S: AsRef<OsStr> + Clone + 'slf,
  {
    let prefix_command = self.command.as_ref().map(|(command, _args)| command);
    let prefix_args = self.command.as_ref().map(|(_command, args)| args);

    let mut iter = prefix_command
      .into_iter()
      .map(AsRef::<OsStr>::as_ref)
      .chain(prefix_args.into_iter().flatten().map(OsString::as_ref))
      .map(Either::Left)
      .chain(iter::once(Either::Right(Either::Left(BTRFS))))
      .chain(args.into_iter().map(Either::Right).map(Either::Right));

    // SANITY: There will always be at least `BTRFS` in `iter`.
    let command = iter.next().expect("constructed btrfs command is empty");
    (command, iter)
  }

  /// Print a btrfs command to stdout, if enabled.
  fn maybe_print<A, S>(&self, args: A)
  where
    A: IntoIterator<Item = S> + Clone,
    A::IntoIter: Clone,
    S: AsRef<OsStr> + Clone,
  {
    if TRACE_COMMANDS.load(Ordering::Relaxed) {
      let (command, args) = self.command(args);
      println!("{}", format_command(command, args))
    }
  }

  /// Check whether `filesystem` points to a valid btrfs filesystem.
  pub fn is_btrfs(&self, filesystem: &Path) -> Result<bool> {
    let args = commands::show_filesystem(filesystem);
    let () = self.maybe_print(args);
    let (command, args) = self.command(args);
    check(command, args)
  }

  /// Create a subvolume.
  pub fn create_subvol(&self, subvolume: &Path) -> Result<()> {
    let args = commands::create(subvolume);
    let () = self.maybe_print(args);
    let (command, args) = self.command(args);
    run(command, args)
  }

  /// Delete a subvolume.
  pub fn delete_subvol(&self, subvolume: &Path) -> Result<()> {
    let args = commands::delete(subvolume);
    let () = self.maybe_print(args);
    let (command, args) = self.command(args);
    run(command, args)
  }

  /// Snapshot a subvolume `source` to `destination`.
  pub fn snapshot(&self, source: &Path, destination: &Path, readonly: bool) -> Result<()> {
    let args = commands::snapshot(source, destination, readonly);
    let () = self.maybe_print(args.clone());
    let (command, args) = self.command(args);
    run(command, args)
  }

  /// Synchronize the provided btrfs file system to disk.
  pub fn sync(&self, filesystem: &Path) -> Result<()> {
    let args = commands::sync(filesystem);
    let () = self.maybe_print(args);
    let (command, args) = self.command(args);
    run(command, args)
  }

  /// List all subvolumes in `directory`.
  fn subvolumes_impl(&self, directory: &Path, readonly: bool) -> Result<Vec<(PathBuf, usize)>> {
    let args = commands::subvolumes(directory, readonly);
    let () = self.maybe_print(args.clone());
    let (command, args) = self.command(args);

    let output = output(command.clone(), args.clone())?;
    let output = String::from_utf8(output).with_context(|| {
      format!(
        "failed to read `{}` output as UTF-8 string",
        format_command(command, args.clone())
      )
    })?;

    let vec = output
      .lines()
      .map(|line| {
        let captures = SNAPSHOTS_LINE_REGEX
          .captures(line)
          .with_context(|| format!("failed to parse snapshot output line: `{line}`"))?;
        let gen_ = &captures["gen"];
        let gen_ = usize::from_str(gen_)
          .with_context(|| format!("failed to parse generation string `{gen_}` as integer"))?;
        let path = PathBuf::from(&captures["path"]);
        Ok((path, gen_))
      })
      .collect::<Result<_>>()?;

    Ok(vec)
  }

  /// Find the path of a subvolume containing the given directory relative
  /// to the btrfs root.
  fn find_subvol_path(&self, directory: &Path) -> Result<PathBuf> {
    // We start off by looking up the ID of the subvolume containing the
    // given directory.
    let id = self.subvol_id(directory)?;
    // Once we have that ID we can look up the subvolume's path relative
    // to the btrfs root.
    let path = self.resolve_id(id, directory)?;
    Ok(path)
  }

  /// List subvolumes in the given `directory`, which has to be relative
  /// to `root`, the actual btrfs file system mount point.
  ///
  /// # Panics
  /// This method will panic if `directory` is not relative to `root`.
  pub fn subvolumes(
    &self,
    ops: &dyn FileOps,
    root: &Path,
    directory: Option<&Path>,
    readonly: bool,
  ) -> Result<Vec<(PathBuf, usize)>> {
    // In order for our path substitution "magic" below to work we
    // should make sure to work with canonical paths only.
    let root = ops.canonicalize(root)?;
    let directory = if let Some(directory) = directory {
      assert!(
        directory.is_relative(),
        "directory path {} needs to be relative",
        directory.display()
      );

      Cow::Owned(ops.canonicalize(&root.join(directory))?)
    } else {
      Cow::Borrowed(&root)
    };

    // Convert a subvolume relative to the root directory to an absolute one.
    let make_absolute = |subvol: &Path| root.join(subvol);

    // The list of subvolumes we are going to retrieve can be "wrong" in
    // a variety of ways one would not expect given the intuitively
    // simple task of listing subvolumes. If, for example, a subvolume
    // of a btrfs file system was mounted in a directory that is named
    // differently than the subvolume being mounted (by means of the
    // 'subvol' option), the subvolume path will still contain the name
    // of the subvolume, not that of the directory. The work around is
    // rather adventurous: We find the subvolume containing "our"
    // directory and retrieve its name. We then replace the last part of
    // "our" directory with this name and use the result as the
    // "expected" directory.
    let subvol_path = self.find_subvol_path(&root)?;

    let subvols = self
      .subvolumes_impl(&directory, readonly)?
      .into_iter()
      .filter_map(|(subvol, gen_)| {
        subvol
          .strip_prefix(&subvol_path)
          .ok()
          .map(Path::to_path_buf)
          .map(|subvol| (subvol, gen_))
      })
      .map(|(subvol, gen_)| (make_absolute(&subvol), gen_))
      // We need to work around the btrfs problem that not necessarily
      // all subvolumes listed are located in our repository's
      // directory. This is done as one step along with converting the
      // absolute subvolume paths to relative ones where we just sort
      // out everything not below our directory.
      .filter_map(|(subvol, gen_)| {
        subvol
          .strip_prefix(directory.as_ref())
          .ok()
          .map(Path::to_path_buf)
          .map(|subvol| (subvol, gen_))
      })
      .collect();

    Ok(subvols)
  }

  /// Check whether `subvolume` has changed over the provided
  /// `generation`.
  pub fn has_changes(&self, subvolume: &Path, generation: usize) -> Result<bool> {
    // Because of an apparent bug in btrfs(8) (or a misunderstanding on
    // my side), we cannot use the generation reported for a snapshot to
    // create a diff of the files that changed *since* then. Rather, we
    // have to increment the generation by one, otherwise the files
    // changed *in* the snapshot are included in the diff as well.
    let args = commands::diff(subvolume, generation + 1);
    let () = self.maybe_print(args.clone());
    let (command, args) = self.command(args);

    let output = output(command, args)?;
    let result = !output.starts_with(DIFF_END_MARKER);
    Ok(result)
  }

  /// Query the ID of a subvolume at the provided `path`.
  pub fn subvol_id(&self, path: &Path) -> Result<usize> {
    let args = commands::root_id(path);
    let () = self.maybe_print(args);
    let (command, args) = self.command(args);

    let output = output(command.clone(), args.clone())?;
    let output = String::from_utf8(output).with_context(|| {
      format!(
        "failed to read `{}` output as UTF-8 string",
        format_command(command.clone(), args.clone())
      )
    })?;

    let id = usize::from_str(&output[..output.len().saturating_sub(1)]).with_context(|| {
      format!(
        "failed to convert `{}` output to ID",
        format_command(command, args)
      )
    })?;

    Ok(id)
  }

  /// Resolve a subvolume `id` to its path within `root`.
  ///
  /// `root` identifies the btrfs file system in which the subvol ID is
  /// valid. It can point anywhere inside the file system.
  ///
  /// The returned path will be relative to the file system's root.
  pub fn resolve_id(&self, id: usize, root: &Path) -> Result<PathBuf> {
    let args = commands::resolve_id(id, root);
    let () = self.maybe_print(args.clone());
    let (command, args) = self.command(args);

    let output = output(command, args)?;
    let path = bytes_to_path(&output[..output.len().saturating_sub(1)]);
    Ok(path.to_path_buf())
  }

  /// Make a subvolume read-only.
  pub fn make_subvol_readonly(&self, subvol: &Path) -> Result<()> {
    let args = commands::set_readonly(subvol);
    let () = self.maybe_print(args.clone());
    let (command, args) = self.command(args);
    run(command, args)
  }

  /// Send `send_subvolume` to `recv_destination`.
  pub fn send_recv<'input, I>(
    &self,
    send_subvolume: &'input Path,
    send_sources: I,
    recv: &Btrfs,
    recv_destination: &Path,
  ) -> Result<()>
  where
    // TODO: Ideally we'd accept any P: AsRef<OsStr> as item, but that
    //       fails with today's borrow checker.
    I: IntoIterator<Item = &'input OsStr>,
    I::IntoIter: Clone,
  {
    let src_args = commands::serialize(send_subvolume, send_sources);
    let (src_cmd, src_args) = self.command(src_args);
    let dst_args = commands::deserialize(recv_destination);
    let (dst_cmd, dst_args) = recv.command(dst_args);

    if TRACE_COMMANDS.load(Ordering::Relaxed) {
      println!(
        "{} | {}",
        format_command(src_cmd.clone(), src_args.clone()),
        format_command(dst_cmd.clone(), dst_args.clone())
      )
    }

    pipeline(src_cmd, src_args, dst_cmd, dst_args)
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  use std::collections::HashMap;
  use std::fs::create_dir_all as create_dirs;
  use std::fs::write;

  use serial_test::serial;

  use crate::ops::LocalOps;
  use crate::test::with_btrfs;
  use crate::test::BtrfsDev;
  use crate::test::Mount;


  /// Test that we can successfully detect whether a mounted file system
  /// is a btrfs one.
  #[test]
  #[serial]
  fn filesystem_check() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let result = btrfs.is_btrfs(root).unwrap();
      assert!(result);

      // Check that a file is not reported as btrfs file system.
      let file = root.join("file");
      let () = write(&file, b"content").unwrap();
      let result = btrfs.is_btrfs(&file).unwrap();
      assert!(!result);

      // Check that a subvolume is not reported as btrfs file system.
      let subvol = root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let result = btrfs.is_btrfs(&subvol).unwrap();
      assert!(!result);
    })
  }

  /// Check that we can sync a btrfs filesystem.
  #[test]
  #[serial]
  fn filesystem_sync() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let () = btrfs.sync(root).unwrap();
    })
  }

  /// Make sure that we can create and delete a btrfs subvolume.
  #[test]
  #[serial]
  fn subvol_creation_deletion() {
    with_btrfs(|root| {
      let subvol = root.join("subvol");
      let btrfs = Btrfs::new();
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = btrfs.delete_subvol(&subvol).unwrap();
    })
  }

  /// Check that we can query the ID of a btrfs subvolume and then
  /// resolve back its path.
  #[test]
  #[serial]
  fn subvol_id_resolution() {
    with_btrfs(|root| {
      let subvol_name = OsStr::new("subvol");
      let subvol_path = root.join(subvol_name);
      let btrfs = Btrfs::new();
      let () = btrfs.create_subvol(&subvol_path).unwrap();
      let id = btrfs.subvol_id(&subvol_path).unwrap();
      assert_ne!(id, 0);

      let subvol_path = btrfs.resolve_id(id, root).unwrap();
      assert_eq!(subvol_path, subvol_name);
    })
  }

  /// Check that we can list subvolumes in a btrfs volume.
  #[test]
  #[serial]
  fn subvolumes() {
    with_btrfs(|root| {
      let ops = LocalOps;
      let btrfs = Btrfs::new();

      let readonly = true;
      let subvolumes = btrfs.subvolumes(&ops, root, None, readonly).unwrap();
      assert!(subvolumes.is_empty());
      let subvolumes = btrfs.subvolumes(&ops, root, None, !readonly).unwrap();
      assert!(subvolumes.is_empty());

      let subvol_name = OsStr::new("subvol");
      let subvol_path = root.join(subvol_name);
      // Create a subvolume.
      let () = btrfs.create_subvol(&subvol_path).unwrap();

      // Then create a snapshot of this subvolume.
      let snapshot_name = OsStr::new("snapshot");
      let snapshot_path = root.join(snapshot_name);
      let () = btrfs
        .snapshot(&subvol_path, &snapshot_path, readonly)
        .unwrap();

      // List the readonly subvolumes. One should be reported.
      let mut subvolumes = btrfs
        .subvolumes(&ops, root, None, readonly)
        .unwrap()
        .into_iter();
      assert_eq!(subvolumes.len(), 1);

      let next = subvolumes.next().unwrap();
      assert_eq!(next.0, snapshot_name);
      assert_ne!(next.1, 0);

      let mut subvolumes = btrfs.subvolumes(&ops, root, None, !readonly).unwrap();
      let () = subvolumes.sort();

      let mut subvolumes = subvolumes.into_iter();
      assert_eq!(subvolumes.len(), 2);

      let next = subvolumes.next().unwrap();
      assert_eq!(next.0, snapshot_name);
      assert_ne!(next.1, 0);

      let next = subvolumes.next().unwrap();
      assert_eq!(next.0, subvol_name);
      assert_ne!(next.1, 0);
    })
  }

  /// Check that we can list subvolumes in a sub-directory of a btrfs
  /// volume.
  #[test]
  #[serial]
  fn subvolumes_in_subdir() {
    with_btrfs(|root| {
      let ops = LocalOps;
      let btrfs = Btrfs::new();

      let subvol_name = OsStr::new("subvol");
      let subvol_dir = root.join("test-dir");
      let subvol_path = subvol_dir.join(subvol_name);
      let () = create_dirs(&subvol_dir).unwrap();
      // Create a subvolume.
      let () = btrfs.create_subvol(&subvol_path).unwrap();

      // List the subvolumes in "test-dir".
      let readonly = true;
      let mut subvolumes = btrfs
        .subvolumes(&ops, root, Some(Path::new("test-dir")), !readonly)
        .unwrap()
        .into_iter();
      assert_eq!(subvolumes.len(), 1);

      let next = subvolumes.next().unwrap();
      // The reported path should be relative to "test-dir", i.e., only
      // the name.
      assert_eq!(next.0, subvol_name);
      assert_ne!(next.1, 0);
    })
  }

  /// Check that we can detect changes to a btrfs subvolume.
  #[test]
  #[serial]
  fn subvol_changes() {
    with_btrfs(|root| {
      let ops = LocalOps;
      let btrfs = Btrfs::new();

      let subvol = root.join("root");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), b"content").unwrap();

      let snapshot_name = OsStr::new("root-snapshot");
      let snapshot_path = root.join(snapshot_name);
      let readonly = true;
      let () = btrfs.snapshot(&subvol, &snapshot_path, !readonly).unwrap();

      let subvolumes = btrfs
        .subvolumes(&ops, root, None, !readonly)
        .unwrap()
        .into_iter()
        .collect::<HashMap<_, _>>();

      // The snapshot should have no changes.
      let root_snap_gen = *subvolumes
        .get(AsRef::<Path>::as_ref(snapshot_name))
        .unwrap();
      assert!(!btrfs.has_changes(&snapshot_path, root_snap_gen).unwrap());

      // Make a change; that should be reported accordingly.
      let () = write(snapshot_path.join("file2"), b"content2").unwrap();
      assert!(btrfs.has_changes(&snapshot_path, root_snap_gen).unwrap());
    })
  }

  /// Check that we can send and receive a snapshot between btrfs
  /// volumes.
  #[test]
  #[serial]
  fn snapshot_send_recv() {
    let loopdev1 = BtrfsDev::with_default().unwrap();
    let mount1 = Mount::new(loopdev1.path()).unwrap();

    let loopdev2 = BtrfsDev::with_default().unwrap();
    let mount2 = Mount::new(loopdev2.path()).unwrap();

    let btrfs = Btrfs::new();
    let subvol = mount1.path().join("subvol");
    let () = btrfs.create_subvol(&subvol).unwrap();

    let snapshot = mount1.path().join("snapshot");
    let readonly = true;
    let () = btrfs.snapshot(&subvol, &snapshot, readonly).unwrap();

    let () = btrfs
      .send_recv(&snapshot, [], &btrfs, mount2.path())
      .unwrap();
    assert!(mount2.path().join("snapshot").exists());
  }

  /// Make sure that we can make a subvolume read-only.
  #[test]
  #[serial]
  fn subvolume_readonly() {
    with_btrfs(|root| {
      let btrfs = Btrfs::new();
      let subvol = root.join("root");
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = write(subvol.join("file"), b"content").unwrap();

      let () = btrfs.make_subvol_readonly(&subvol).unwrap();
      let err = write(subvol.join("file"), b"changed-content").unwrap_err();
      assert!(
        err
          .to_string()
          .to_lowercase()
          .contains("read-only file system"),
        "{err}"
      );
    })
  }
}
