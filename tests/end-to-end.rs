// Copyright (C) 2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::let_and_return, clippy::let_unit_value)]

//! End-to-end tests for `btrfs_backup`, mostly focused on argument
//! handling.

use std::ffi::OsStr;
use std::fs::create_dir_all;
use std::fs::read_to_string;
use std::fs::write;
use std::path::Path;

use time::Duration;

use serial_test::serial;

use btrfs_backup::btrfs::Btrfs;
use btrfs_backup::run;
use btrfs_backup::snapshot::Snapshot;
use btrfs_backup::test::with_btrfs;
use btrfs_backup::test::with_two_btrfs;
use btrfs_backup::util::normalize;


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

/// Check that we can purge old snapshots as expected.
#[test]
#[serial]
fn purge_snapshots() {
  let tag = "";

  with_btrfs(|root| {
    let btrfs = Btrfs::new();
    let subvol1 = root.join("some-subvol").join("..").join("some-subvol");
    let subvol2 = root.join("some-other-subvol");

    let snapshot1 = Snapshot::from_subvol_path(&normalize(&subvol1), tag).unwrap();
    let mut snapshot2 = snapshot1.clone();
    snapshot2.timestamp -= Duration::weeks(2);
    let mut snapshot3 = snapshot1.clone();
    snapshot3.timestamp -= Duration::weeks(4);
    let mut snapshot4 = snapshot1.clone();
    snapshot4.timestamp -= Duration::weeks(5);

    // Also create a snapshot for `subvol2`.
    let mut snapshot5 = Snapshot::from_subvol_path(&subvol2, tag).unwrap();
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

    let tag = "";
    let snapshot1 = Snapshot::from_subvol_path(&subvol, tag).unwrap();
    let mut snapshot2 = snapshot1.clone();
    snapshot2.timestamp -= Duration::weeks(2);
    let mut snapshot3 = snapshot1.clone();
    snapshot3.timestamp -= Duration::weeks(4);
    let mut snapshot4 = snapshot1.clone();
    snapshot4.timestamp -= Duration::weeks(5);

    // The last snapshot is outdated but differently tagged.
    let tag = "tagged";
    let mut snapshot5 = Snapshot::from_subvol_path(&subvol, tag).unwrap();
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
    let tag = "";
    let btrfs = Btrfs::new();
    let subvol = to_test.join("some-subvol");

    let snapshot = Snapshot::from_subvol_path(&subvol, tag).unwrap();
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
  let tag = "";

  with_two_btrfs(|src, dst| {
    let btrfs = Btrfs::new();
    let subvol = dst.join("some-subvol").join("..").join("some-subvol");

    let snapshot1 = Snapshot::from_subvol_path(&normalize(&subvol), tag).unwrap();
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
