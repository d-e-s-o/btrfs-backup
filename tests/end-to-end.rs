// Copyright (C) 2023-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::unwrap_used)]

//! End-to-end tests for `btrfs_backup`, mostly focused on argument
//! handling.

use std::collections::HashMap;
use std::collections::HashSet;
use std::env::split_paths;
use std::env::var_os;
use std::ffi::OsStr;
use std::fs::copy as copy_file;
use std::fs::create_dir_all;
use std::fs::metadata;
use std::fs::read_to_string;
use std::fs::write;
use std::fs::File;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::ErrorKind;
use std::os::unix::fs::symlink;
use std::os::unix::fs::PermissionsExt as _;
use std::path::Path;
use std::path::PathBuf;

use anyhow::bail;
use anyhow::Context as _;
use anyhow::Error;
use anyhow::Result;

use glob::glob;
use goblin::elf;
use memmap::Mmap;
use serial_test::serial;
use time::Duration;

use btrfs_backup::btrfs::Btrfs;
use btrfs_backup::run;
use btrfs_backup::snapshot::Snapshot;
use btrfs_backup::test::with_btrfs;
use btrfs_backup::test::with_two_btrfs;
use btrfs_backup::test::Mount;
use btrfs_backup::util::normalize;


/// Collect all shared object search paths from an `ld.so.conf` style
/// configuration file.
fn collect_so_search_paths(ldso_conf: &Path, paths: &mut Vec<PathBuf>) -> Result<()> {
  let ldso = File::open(ldso_conf)
    .with_context(|| format!("failed to open {} for reading", ldso_conf.display()))?;
  let reader = BufReader::new(ldso);
  for line in reader.lines() {
    let line = line.context("failed to reader line from /etc/ld.so.conf")?;
    // Ignore comments.
    if line.starts_with('#') {
      continue
    }

    if let Some(include) = line.strip_prefix("include ") {
      let dir = ldso_conf.parent().with_context(|| {
        format!(
          "ld.so.conf path {} does not have a parent",
          ldso_conf.display()
        )
      })?;
      let include = dir.join(include);
      let include = include.to_str().with_context(|| {
        format!(
          "ld.so.conf configuration path {} is not a valid string",
          include.display()
        )
      })?;
      let () = glob(include)?.try_for_each(|result| {
        let ldso_conf = result?;
        let () = collect_so_search_paths(&ldso_conf, paths)?;
        Result::<(), Error>::Ok(())
      })?;
    } else {
      let () = paths.push(PathBuf::from(line));
    }
  }

  Ok(())
}


/// Check whether a `path` represents a file or symlink.
fn is_valid_file(path: &Path) -> Result<bool> {
  match metadata(path) {
    Ok(metadata) => Ok(metadata.is_file() || metadata.is_symlink()),
    Err(err) if err.kind() == ErrorKind::NotFound => Ok(false),
    Err(err) => Err(err.into()),
  }
}


/// Resolve the path to a shared object.
fn resolve_shared_object<S>(shared_object: S) -> Result<PathBuf>
where
  S: AsRef<OsStr>,
{
  let shared_object = shared_object.as_ref();

  // See ld.so(8) for the proper procedure to follow for path
  // resolution. We take tremendous short cuts here.
  let mut search_dirs = Vec::new();
  let ldso_conf = Path::new("/etc/ld.so.conf");
  let () = collect_so_search_paths(ldso_conf, &mut search_dirs)?;

  for search_dir in search_dirs {
    let candidate = search_dir.join(shared_object);

    if is_valid_file(&candidate)? {
      return Ok(candidate)
    }
  }

  bail!(
    "shared object {} not found",
    shared_object.to_string_lossy()
  )
}


/// Check whether a `path` represents an executable file.
fn is_executable_file(path: &Path) -> Result<bool> {
  // This constant would be defined by `libc`, but we currently don't
  // depend on that.
  const S_IXUSR: u32 = 64;

  match metadata(path) {
    Ok(metadata) => {
      if metadata.is_file() || metadata.is_symlink() {
        let permissions = metadata.permissions();
        Ok(permissions.mode() & S_IXUSR != 0)
      } else {
        Ok(false)
      }
    },
    Err(err) if err.kind() == ErrorKind::NotFound => Ok(false),
    Err(err) => Err(err.into()),
  }
}


/// Resolve the absolute path to a binary.
fn resolve_executable_path<E>(executable: E) -> Result<PathBuf>
where
  E: AsRef<OsStr>,
{
  let executable = executable.as_ref();

  // TODO: It's unclear whether no `PATH` should be treated as error or
  //       not.
  for dir in split_paths(&var_os("PATH").unwrap_or_default()) {
    let candidate = dir.join(executable);

    if is_executable_file(&candidate)? {
      return Ok(candidate)
    }
  }

  bail!("executable {} not found", executable.to_string_lossy())
}


/// Collect the dependencies of an ELF binary into the provided
/// `HashMap`.
fn collect_deps(bin: PathBuf, deps: &mut HashMap<PathBuf, Vec<PathBuf>>) -> Result<()> {
  if deps.contains_key(&bin) {
    // We already covered this binary. No point in redoing that step.
    return Ok(())
  }

  let file =
    File::open(&bin).with_context(|| format!("failed to open `{}` for reading", bin.display()))?;
  // SAFETY: The function is always safe to call.
  let mmap = unsafe { Mmap::map(&file) }
    .with_context(|| format!("failed to memory map `{}`", bin.display()))?;

  let elf = elf::Elf::parse(&mmap)
    .with_context(|| format!("failed to parse ELF file `{}`", bin.display()))?;
  let mut libs = elf
    .libraries
    .iter()
    .map(resolve_shared_object)
    .collect::<Result<Vec<_>, _>>()?;

  if let Some(interpreter) = elf.interpreter {
    let () = libs.push(PathBuf::from(interpreter));
  }

  let _previous = deps.insert(bin, libs.clone());

  let () = libs
    .into_iter()
    .try_for_each(|lib| collect_deps(lib, deps))?;

  Ok(())
}

/// Copy a list of files below a destination directory.
///
/// This function assumes paths to those files are absolute and will
/// establish the same directory hierarchy below `dest`.
fn copy_files<F, P, D>(files: F, dest: D) -> Result<()>
where
  F: IntoIterator<Item = P>,
  P: AsRef<Path>,
  D: AsRef<Path>,
{
  let dest = dest.as_ref();
  // Each file is expected to already be an absolute path.
  for file in files {
    let file = file.as_ref();
    debug_assert!(file.is_absolute(), "{}", file.display());

    // Create a relative path, so that we can join properly.
    let rel = file.strip_prefix("/")?;
    let dest_path = dest.join(rel);
    // SANITY: We should always have a parent in `dest_path` at this
    //         point.
    let () = create_dir_all(dest_path.parent().unwrap())?;

    let _count = copy_file(file, dest_path)?;
  }
  Ok(())
}

/// Copy a list of binary ELF files, including their ELF dependencies,
/// below a destination directory.
///
/// This function assumes paths to those files are absolute and will
/// establish the same directory hierarchy below `dest`.
fn copy_with_deps<B, P, D>(bins: B, dest: D) -> Result<()>
where
  B: IntoIterator<Item = P>,
  P: AsRef<Path>,
  D: AsRef<Path>,
{
  let deps = bins.into_iter().try_fold(HashMap::new(), |mut deps, bin| {
    let () = collect_deps(bin.as_ref().to_path_buf(), &mut deps)?;
    Result::<HashMap<PathBuf, Vec<PathBuf>>>::Ok(deps)
  })?;

  let deps = deps
    .into_iter()
    .flat_map(|(binary, deps)| Some(binary).into_iter().chain(deps))
    .collect::<HashSet<_>>();

  copy_files(deps, dest)
}


/// Create and mount a btrfs file system and then create a chroot'able
/// directory structure in there that includes all commands necessary
/// for being on the receiving end of a `btrfs-backup` invocation (e.g.,
/// the destination of a backup).
fn with_btrfs_chroot<F>(f: F)
where
  F: FnOnce(&Path),
{
  with_btrfs(|root| {
    // This is effectively a list of all command dependencies that
    // btrfs-backup requires. `sh` and `env` are only needed due to
    // test plumbing, though.
    // TODO: It would be better to consume this list from the actual
    //       program instead of maintaining it here.
    let sh = resolve_executable_path("sh").unwrap();
    let env = resolve_executable_path("env").unwrap();
    let btrfs = resolve_executable_path("btrfs").unwrap();
    let mkdir = resolve_executable_path("mkdir").unwrap();
    let readlink = resolve_executable_path("readlink").unwrap();

    let () = copy_with_deps([sh, env, btrfs, mkdir, readlink], root).unwrap();

    let sh_run = Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("var")
      .join("sh-run");

    let bin_dir = root.join("bin");
    let () = create_dir_all(&bin_dir).unwrap();
    let _count = copy_file(sh_run, bin_dir.join("sh-run")).unwrap();

    let proc_dir = root.join("proc");
    let () = create_dir_all(&proc_dir).unwrap();
    let _proc = Mount::builder()
      .directory(proc_dir)
      .arguments(["-t", "proc"])
      .mount("proc")
      .unwrap();

    f(root)
  })
}


/// Test that we can backup subvolumes with co-located snapshot
/// repositories.
#[test]
#[serial]
fn backup_with_colocated_repos() {
  with_two_btrfs(|src_root, dst_root| {
    let btrfs = Btrfs::new();

    let subdir = src_root.join("sub-dir");
    let subvol1 = src_root.join("subvol1");
    let subvol2 = subdir.join("subvol2");
    let () = create_dir_all(&subdir).unwrap();
    let () = btrfs.create_subvol(&subvol1).unwrap();
    let () = btrfs.create_subvol(&subvol2).unwrap();

    assert_eq!(src_root.read_dir().unwrap().count(), 2);
    assert_eq!(subdir.read_dir().unwrap().count(), 1);
    assert_eq!(dst_root.read_dir().unwrap().count(), 0);

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      subvol1.as_os_str(),
      subvol2.as_os_str(),
      OsStr::new("--destination"),
      dst_root.as_os_str(),
    ];
    let () = run(args).unwrap();

    assert_eq!(src_root.read_dir().unwrap().count(), 3);
    assert_eq!(subdir.read_dir().unwrap().count(), 2);
    assert_eq!(dst_root.read_dir().unwrap().count(), 2);
  })
}

/// Test that we can backup a subvolume using a separate snapshot
/// repository.
#[test]
#[serial]
fn backup_with_distinct_repo() {
  let tag = "tagged";

  with_two_btrfs(|src_root, dst_root| {
    let btrfs = Btrfs::new();

    let snapshots = src_root.join("snapshots");
    let subvol = src_root.join("subvol");
    let () = create_dir_all(&snapshots).unwrap();
    let () = btrfs.create_subvol(&subvol).unwrap();

    assert_eq!(src_root.read_dir().unwrap().count(), 2);
    assert_eq!(snapshots.read_dir().unwrap().count(), 0);
    assert_eq!(dst_root.read_dir().unwrap().count(), 0);

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      snapshots.as_os_str(),
      OsStr::new("--destination"),
      dst_root.as_os_str(),
      OsStr::new("--tag"),
      OsStr::new(tag),
    ];
    let () = run(args).unwrap();

    assert_eq!(src_root.read_dir().unwrap().count(), 2);
    assert_eq!(snapshots.read_dir().unwrap().count(), 1);
    assert_eq!(dst_root.read_dir().unwrap().count(), 1);
  })
}

/// Check that subvolume paths are canocicalized for backup.
#[test]
#[serial]
fn backup_subvolume_canonicalized() {
  with_two_btrfs(|src_root, dst_root| {
    let btrfs = Btrfs::new();
    let subvol = src_root.join("subvol");
    let () = btrfs.create_subvol(&subvol).unwrap();
    let () = write(subvol.join("file"), "test42").unwrap();

    let snapshots = dst_root.join("snapshots");
    let () = btrfs.create_subvol(&snapshots).unwrap();

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      src_root.as_os_str(),
      OsStr::new("--destination"),
      snapshots.as_os_str(),
    ];
    let () = run(args).unwrap();
    assert_eq!(snapshots.read_dir().unwrap().count(), 1);

    let link = src_root.join("symlink");
    let () = symlink(subvol, &link).unwrap();

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      link.as_os_str(),
      OsStr::new("--source"),
      src_root.as_os_str(),
      OsStr::new("--destination"),
      snapshots.as_os_str(),
    ];
    let () = run(args).unwrap();
    assert_eq!(snapshots.read_dir().unwrap().count(), 1);

    let subvol = src_root.join("subvol").join("..").join("subvol");
    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      src_root.as_os_str(),
      OsStr::new("--destination"),
      snapshots.as_os_str(),
    ];
    let () = run(args).unwrap();
    assert_eq!(snapshots.read_dir().unwrap().count(), 1);
  })
}

/// Check that we can backup a subvolume to a "remote" system.
#[test]
#[serial]
fn backup_remote() {
  with_btrfs(|src_root| {
    with_btrfs_chroot(|dst_root| {
      let btrfs = Btrfs::new();

      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let remote_cmd = format!("chroot {} /bin/sh-run", dst_root.display());
      let args = [
        OsStr::new("btrfs-backup"),
        OsStr::new("backup"),
        subvol.as_os_str(),
        OsStr::new("--destination"),
        OsStr::new("/backups"),
        OsStr::new("--remote-command"),
        OsStr::new(&remote_cmd),
      ];
      let () = run(args).unwrap();
    })
  })
}

/// Check that we can purge old snapshots as expected.
#[test]
#[serial]
fn purge_snapshots() {
  with_btrfs(|root| {
    let btrfs = Btrfs::new();
    let subvol1 = root.join("some-subvol").join("..").join("some-subvol");
    let subvol2 = root.join("some-other-subvol");

    let snapshot1 = Snapshot::builder().try_build(&normalize(&subvol1)).unwrap();
    let mut snapshot2 = snapshot1.clone();
    snapshot2.timestamp -= Duration::weeks(2);
    let mut snapshot3 = snapshot1.clone();
    snapshot3.timestamp -= Duration::weeks(4);
    let mut snapshot4 = snapshot1.clone();
    snapshot4.timestamp -= Duration::weeks(5);

    // Also create a snapshot for `subvol2`.
    let mut snapshot5 = Snapshot::builder().try_build(&subvol2).unwrap();
    snapshot5.timestamp -= Duration::weeks(5);

    let snapshots = [&snapshot1, &snapshot2, &snapshot3, &snapshot4, &snapshot5];

    let () = snapshots.iter().for_each(|snapshot| {
      let subvol = root.join(snapshot.to_string());
      let () = btrfs.create_subvol(&subvol).unwrap();
      // Make the subvolumes read-only to fake actual snapshots.
      let () = btrfs.make_subvol_readonly(&subvol).unwrap();
    });

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("purge"),
      subvol1.as_os_str(),
      OsStr::new("--source"),
      root.as_os_str(),
      OsStr::new("--keep-for=3w"),
    ];
    let () = run(args).unwrap();

    assert!(root.join(snapshot1.to_string()).exists());
    assert!(root.join(snapshot2.to_string()).exists());
    assert!(!root.join(snapshot3.to_string()).exists());
    assert!(!root.join(snapshot4.to_string()).exists());
    // We did not ask for purge of snapshots for `subvol2`, so its
    // snapshot should have survived.
    assert!(root.join(snapshot5.to_string()).exists());
  })
}

/// Check that we can purge old snapshots as expected.
#[test]
#[serial]
fn purge_leaves_differently_tagged() {
  with_btrfs(|root| {
    let btrfs = Btrfs::new();
    let subvol = root.join("some-subvol");

    let snapshot1 = Snapshot::builder().try_build(&subvol).unwrap();
    let mut snapshot2 = snapshot1.clone();
    snapshot2.timestamp -= Duration::weeks(2);
    let mut snapshot3 = snapshot1.clone();
    snapshot3.timestamp -= Duration::weeks(4);
    let mut snapshot4 = snapshot1.clone();
    snapshot4.timestamp -= Duration::weeks(5);

    // The last snapshot is outdated but differently tagged.
    let tag = "tagged";
    let mut snapshot5 = Snapshot::builder().tag(tag).try_build(&subvol).unwrap();
    snapshot5.timestamp -= Duration::weeks(6);

    let snapshots = [&snapshot1, &snapshot2, &snapshot3, &snapshot4, &snapshot5];

    let () = snapshots.iter().for_each(|snapshot| {
      let subvol = root.join(snapshot.to_string());
      let () = btrfs.create_subvol(&subvol).unwrap();
      // Make the subvolumes read-only to fake actual snapshots.
      let () = btrfs.make_subvol_readonly(&subvol).unwrap();
    });

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("purge"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      root.as_os_str(),
      OsStr::new("--keep-for=3w"),
    ];
    let () = run(args).unwrap();

    assert!(root.join(snapshot1.to_string()).exists());
    assert!(root.join(snapshot2.to_string()).exists());
    assert!(!root.join(snapshot3.to_string()).exists());
    assert!(!root.join(snapshot4.to_string()).exists());
    // The last snapshot is differently tagged and should have been
    // preserved.
    assert!(root.join(snapshot5.to_string()).exists());
  })
}

/// Make sure that the `purge` sub-command leaves the most recent
/// snapshot around, even if older than desired.
#[test]
#[serial]
fn purge_leaves_most_recent() {
  fn purge_leaves_most_recent_impl(src: &Path, dst: &Path, to_test: &Path) {
    let btrfs = Btrfs::new();
    let subvol = to_test.join("some-subvol");

    let snapshot = Snapshot::builder().try_build(&subvol).unwrap();
    let mut snapshot1 = snapshot.clone();
    snapshot1.timestamp -= Duration::weeks(3);
    let mut snapshot2 = snapshot.clone();
    snapshot2.timestamp -= Duration::weeks(4);
    let mut snapshot3 = snapshot;
    snapshot3.timestamp -= Duration::weeks(5);

    let snapshots = [&snapshot1, &snapshot2, &snapshot3];

    let () = snapshots.iter().for_each(|snapshot| {
      let subvol = to_test.join(snapshot.to_string());
      let () = btrfs.create_subvol(&subvol).unwrap();
      let () = btrfs.make_subvol_readonly(&subvol).unwrap();
    });

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("purge"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      src.as_os_str(),
      OsStr::new("--destination"),
      dst.as_os_str(),
      OsStr::new("--keep-for=1w"),
    ];
    let () = run(args).unwrap();

    // `snapshot1` is the most recent snapshot and should be kept
    // around, despite being old.
    assert!(to_test.join(snapshot1.to_string()).exists());
    assert!(!to_test.join(snapshot2.to_string()).exists());
    assert!(!to_test.join(snapshot3.to_string()).exists());
  }

  with_two_btrfs(|src, dst| {
    purge_leaves_most_recent_impl(src, dst, src);
    purge_leaves_most_recent_impl(src, dst, dst);
  })
}

/// Check that we can purge old snapshots on the destination repository.
#[test]
#[serial]
fn purge_destination_snapshots() {
  with_two_btrfs(|src, dst| {
    let btrfs = Btrfs::new();
    let subvol = dst.join("some-subvol").join("..").join("some-subvol");

    let snapshot1 = Snapshot::builder().try_build(&normalize(&subvol)).unwrap();
    let mut snapshot2 = snapshot1.clone();
    snapshot2.timestamp -= Duration::weeks(1);
    let mut snapshot3 = snapshot1.clone();
    snapshot3.timestamp -= Duration::weeks(20);

    let snapshots = [&snapshot1, &snapshot2, &snapshot3];

    let () = snapshots.iter().for_each(|snapshot| {
      let create = |root: &Path| {
        let subvol = root.join(snapshot.to_string());
        let () = btrfs.create_subvol(&subvol).unwrap();
        let () = btrfs.make_subvol_readonly(&subvol).unwrap();
      };

      create(src);
      create(dst);
    });

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("purge"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      src.as_os_str(),
      OsStr::new("--destination"),
      dst.as_os_str(),
      OsStr::new("--keep-for=2m"),
    ];
    let () = run(args).unwrap();

    assert!(src.join(snapshot1.to_string()).exists());
    assert!(src.join(snapshot2.to_string()).exists());
    assert!(!src.join(snapshot3.to_string()).exists());
    assert!(dst.join(snapshot1.to_string()).exists());
    assert!(dst.join(snapshot2.to_string()).exists());
    assert!(!dst.join(snapshot3.to_string()).exists());
  })
}

/// Check that we can purge old snapshots from a remote.
#[test]
#[serial]
fn purge_remote() {
  with_btrfs_chroot(|root| {
    let btrfs = Btrfs::new();
    let subvol = root.join("some-subvol");

    let snapshot1 = Snapshot::builder().try_build(&subvol).unwrap();
    let mut snapshot2 = snapshot1.clone();
    snapshot2.timestamp -= Duration::weeks(2);
    let mut snapshot3 = snapshot1.clone();
    snapshot3.timestamp -= Duration::weeks(4);
    let mut snapshot4 = snapshot1.clone();
    snapshot4.timestamp -= Duration::weeks(5);

    let snapshots = [&snapshot1, &snapshot2, &snapshot3, &snapshot4];

    let () = snapshots.iter().for_each(|snapshot| {
      let subvol = root.join(snapshot.to_string());
      let () = btrfs.create_subvol(&subvol).unwrap();
      // Make the subvolumes read-only to fake actual snapshots.
      let () = btrfs.make_subvol_readonly(&subvol).unwrap();
    });

    let non_existent = root.join("non-existent");

    let remote_cmd = format!("chroot {} /bin/sh-run", root.display());
    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("purge"),
      subvol.as_os_str(),
      // We set a non-existing source repository here, to actually test
      // that we purge from the destination and not the source
      // repository.
      OsStr::new("--source"),
      non_existent.as_os_str(),
      OsStr::new("--destination"),
      OsStr::new("/"),
      OsStr::new("--keep-for=3w"),
      OsStr::new("--remote-command"),
      OsStr::new(&remote_cmd),
    ];
    let () = run(args).unwrap();

    assert!(root.join(snapshot1.to_string()).exists());
    assert!(root.join(snapshot2.to_string()).exists());
    assert!(!root.join(snapshot3.to_string()).exists());
    assert!(!root.join(snapshot4.to_string()).exists());
  })
}

/// Test that we can restore a subvolume.
#[test]
#[serial]
fn restore_subvolume() {
  with_two_btrfs(|src_root, dst_root| {
    let btrfs = Btrfs::new();

    let subvol = src_root.join("subvol");
    let () = btrfs.create_subvol(&subvol).unwrap();

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      subvol.as_os_str(),
      OsStr::new("--destination"),
      dst_root.as_os_str(),
    ];
    let () = run(args).unwrap();

    let () = btrfs.delete_subvol(&subvol).unwrap();

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("restore"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      dst_root.as_os_str(),
    ];
    let () = run(args).unwrap();

    assert!(subvol.exists())
  })
}

/// Test that we can restore the snapshots for a subvolume.
#[test]
#[serial]
fn restore_subvolume_snapshots() {
  with_two_btrfs(|src_root, dst_root| {
    let btrfs = Btrfs::new();

    let snapshots = src_root.join("snapshots");
    let subvol = src_root.join("subvol");
    let () = create_dir_all(&snapshots).unwrap();
    let () = btrfs.create_subvol(&subvol).unwrap();

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      snapshots.as_os_str(),
      OsStr::new("--destination"),
      dst_root.as_os_str(),
    ];
    let () = run(args).unwrap();

    let snapshot = snapshots
      .read_dir()
      .unwrap()
      .next()
      .unwrap()
      .unwrap()
      .path();
    let () = btrfs.delete_subvol(&snapshot).unwrap();
    assert_eq!(snapshots.read_dir().unwrap().count(), 0);

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("restore"),
      subvol.as_os_str(),
      OsStr::new("--destination"),
      snapshots.as_os_str(),
      OsStr::new("--source"),
      dst_root.as_os_str(),
      OsStr::new("--snapshots-only"),
    ];
    let () = run(args).unwrap();

    assert_eq!(snapshots.read_dir().unwrap().count(), 1);
  })
}

/// Check that subvolume restoration ignores snapshot tags.
#[test]
#[serial]
fn restore_ignores_snapshot_tag() {
  with_two_btrfs(|src_root, dst_root| {
    let btrfs = Btrfs::new();

    let snapshots = src_root.join("snapshots");
    let subvol = src_root.join("subvol");
    let () = create_dir_all(&snapshots).unwrap();
    let () = btrfs.create_subvol(&subvol).unwrap();
    let () = write(subvol.join("file"), "test-old").unwrap();

    // Perform a backup without a tag.
    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      snapshots.as_os_str(),
      OsStr::new("--destination"),
      dst_root.as_os_str(),
    ];
    let () = run(args).unwrap();

    let () = write(subvol.join("file"), "test-new").unwrap();

    // Now, with the changed subvolume contents, create another backup,
    // this time with a tag.
    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      snapshots.as_os_str(),
      OsStr::new("--destination"),
      dst_root.as_os_str(),
      OsStr::new("--tag=foobar"),
    ];
    let () = run(args).unwrap();

    let () = btrfs.delete_subvol(&subvol).unwrap();

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("restore"),
      subvol.as_os_str(),
      OsStr::new("--destination"),
      snapshots.as_os_str(),
      OsStr::new("--source"),
      dst_root.as_os_str(),
    ];
    let () = run(args).unwrap();

    // We did not ask for restoration from a specific tag (which is not
    // possible), but expect the most recent snapshot to be restored.
    let content = read_to_string(subvol.join("file")).unwrap();
    assert_eq!(content, "test-new");
  })
}

/// Check that subvolume paths are canonicalized for restoration.
#[test]
#[serial]
fn restore_subvolume_canonicalized() {
  with_two_btrfs(|src_root, dst_root| {
    let btrfs = Btrfs::new();

    let snapshots = src_root.join("snapshots");
    let subvol = src_root.join("subvol");
    let () = btrfs.create_subvol(&subvol).unwrap();
    let () = write(subvol.join("file"), "test42").unwrap();

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("backup"),
      subvol.as_os_str(),
      OsStr::new("--source"),
      snapshots.as_os_str(),
      OsStr::new("--destination"),
      dst_root.as_os_str(),
    ];
    let () = run(args).unwrap();

    let snapshot = snapshots
      .read_dir()
      .unwrap()
      .next()
      .unwrap()
      .unwrap()
      .path();
    let () = btrfs.delete_subvol(&snapshot).unwrap();
    assert_eq!(snapshots.read_dir().unwrap().count(), 0);

    let () = btrfs.delete_subvol(&subvol).unwrap();

    let verbose_subvol = src_root.join("subvol").join("..").join("subvol");
    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("restore"),
      verbose_subvol.as_os_str(),
      OsStr::new("--destination"),
      snapshots.as_os_str(),
      OsStr::new("--source"),
      dst_root.as_os_str(),
    ];
    let () = run(args).unwrap();

    let content = read_to_string(subvol.join("file")).unwrap();
    assert_eq!(content, "test42");
  })
}

/// Test that we can restore a subvolume from a remote.
#[test]
#[serial]
fn restore_remote() {
  with_btrfs(|src_root| {
    with_btrfs_chroot(|dst_root| {
      let btrfs = Btrfs::new();

      let subvol = src_root.join("subvol");
      let () = btrfs.create_subvol(&subvol).unwrap();

      let remote_cmd = format!("chroot {} /bin/sh-run", dst_root.display());
      let args = [
        OsStr::new("btrfs-backup"),
        OsStr::new("backup"),
        subvol.as_os_str(),
        OsStr::new("--destination"),
        OsStr::new("/backups"),
        OsStr::new("--remote-command"),
        OsStr::new(&remote_cmd),
      ];
      let () = run(args).unwrap();

      let () = btrfs.delete_subvol(&subvol).unwrap();

      let args = [
        OsStr::new("btrfs-backup"),
        OsStr::new("restore"),
        subvol.as_os_str(),
        OsStr::new("--source"),
        OsStr::new("/backups"),
        OsStr::new("--remote-command"),
        OsStr::new(&remote_cmd),
      ];
      let () = run(args).unwrap();

      assert!(subvol.exists())
    })
  })
}

/// Test that we can snapshot subvolumes with co-located snapshot
/// repositories.
#[test]
#[serial]
fn snapshot_with_colocated_repos() {
  with_btrfs(|root| {
    let btrfs = Btrfs::new();

    let subdir = root.join("sub-dir");
    let subvol1 = root.join("subvol1");
    let subvol2 = subdir.join("subvol2");
    let () = create_dir_all(&subdir).unwrap();
    let () = btrfs.create_subvol(&subvol1).unwrap();
    let () = btrfs.create_subvol(&subvol2).unwrap();

    assert_eq!(root.read_dir().unwrap().count(), 2);
    assert_eq!(subdir.read_dir().unwrap().count(), 1);

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("snapshot"),
      subvol1.as_os_str(),
      subvol2.as_os_str(),
    ];
    let () = run(args).unwrap();

    assert_eq!(root.read_dir().unwrap().count(), 3);
    assert_eq!(subdir.read_dir().unwrap().count(), 2);
  })
}

/// Test that we can snapshot a subvolume using a separate snapshot
/// repository.
#[test]
#[serial]
fn snapshot_with_distinct_repo() {
  with_btrfs(|root| {
    let btrfs = Btrfs::new();

    let subvol = root.join("subvol");
    let () = btrfs.create_subvol(&subvol).unwrap();

    assert_eq!(root.read_dir().unwrap().count(), 1);

    let args = [
      OsStr::new("btrfs-backup"),
      OsStr::new("snapshot"),
      subvol.as_os_str(),
      OsStr::new("--repository"),
      root.as_os_str(),
    ];
    let () = run(args).unwrap();

    assert_eq!(root.read_dir().unwrap().count(), 2);
  })
}
