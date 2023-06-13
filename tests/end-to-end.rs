// Copyright (C) 2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::let_and_return, clippy::let_unit_value)]

//! End-to-end tests for `btrfs_backup`, mostly focused on argument
//! handling.

use std::ffi::OsStr;
use std::fs::create_dir_all;

use serial_test::serial;

use btrfs_backup::btrfs::Btrfs;
use btrfs_backup::run;
use btrfs_backup::test::with_btrfs;
use btrfs_backup::test::with_two_btrfs;


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
    ];
    let () = run(args).unwrap();

    assert_eq!(src_root.read_dir().unwrap().count(), 2);
    assert_eq!(snapshots.read_dir().unwrap().count(), 1);
    assert_eq!(dst_root.read_dir().unwrap().count(), 1);
  })
}

/// Test that we can restore a subvolume.
#[test]
#[serial]
fn restore_subvolumes() {
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
