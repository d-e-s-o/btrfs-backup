[![pipeline](https://github.com/d-e-s-o/btrfs-backup/actions/workflows/test.yml/badge.svg?branch=main)](https://github.com/d-e-s-o/btrfs-backup/actions/workflows/test.yml)
[![crates.io](https://img.shields.io/crates/v/btrfs-backup.svg)](https://crates.io/crates/btrfs-backup)
[![rustc](https://img.shields.io/badge/rustc-1.66+-blue.svg)](https://blog.rust-lang.org/2022/12/15/Rust-1.66.0.html)

btrfs-backup
============

- [Changelog](CHANGELOG.md)

**btrfs-backup** is a program for backing up `btrfs` subvolumes in an
incremental fashion.


Installation
------------

**btrfs-backup** is written in Rust and requires the Cargo package
manager to be built. It can be installed using `cargo install
btrfs-backup`. The program requires [`btrfs-progs`][btrfs-progs] to be
installed and its `btrfs` binary to be discoverable via the `PATH`
environment variable.


Usage
-----

Let's say you have two subvolumes that you would like to back up to
some external HDD mounted at `/mnt/backup`:
```sh
$ mount /mnt/backup/
$ mkdir /.tmpjWzWMn/
$ mkdir /.tmpjWzWMn/subdir
$ btrfs subvolume create /.tmpjWzWMn/subvol1
$ btrfs subvolume create /.tmpjWzWMn/subdir/subvol2
```

Then backup can be as simple as:
```sh
$ btrfs-backup backup /.tmpjWzWMn/subvol1 /.tmpjWzWMn/subdir/subvol2 --destination /mnt/backup/
```

This command results in the following backup snapshots:
```sh
$ ls -l /mnt/backup/
> drwxr-xr-x 1 root root 0 Feb 20 11:13 <hostname>_.tmpjWzWMn-subdir-subvol2_2023-02-20_11:14:35_
> drwxr-xr-x 1 root root 0 Feb 20 11:13 <hostname>_.tmpjWzWMn-subvol1_2023-02-20_11:14:35_
```

The way backups work on a `btrfs` file system, a read-only snapshot of
the subvolume to back up is created on the source file system and then
send over to the destination file system. Shown above are the snapshots
on the destination file system. Because we did not provide the
`--source` argument to the command, snapshots on the source file system
are co-located with the actual subvolume in question (that is, they
reside in the same parent directory):
```sh
$ ls -al /.tmpjWzWMn/
> drwxr-xr-x 1 root root   0 Feb 20 11:13 nuc_.tmpjWzWMn-subvol1_2023-02-20_11:14:35_
> drwxr-xr-x 1 root root 112 Feb 20 11:14 subdir
> drwxr-xr-x 1 root root   0 Feb 20 11:13 subvol1
```

If you want to have snapshots centrally managed, provide the `--source`
flag with a path to a directory on the `btrfs` file system on which the
subvolumes to back up are located.

Please refer to the help text (`--help`) for additional details.


Status
------

The program supports backup and restoration of subvolumes on a single
system as well as to/from a remote one (e.g., over an `ssh` connection).
It also can automatically clean stale snapshots. As such, it is fully
usable for backup needs.

Compared to the [original][btrfs-backup-py] Python version of the
program, the snapshot naming scheme has changed and a few bugs have been
fixed. Support for backups to files is not yet present (and may not ever
be added, as it was considered a fringe feature that was not used
regularly).

[btrfs-backup-py]: https://github.com/d-e-s-o/btrfs-backup-python/tree/main/btrfs-backup
[btrfs-progs]: https://github.com/kdave/btrfs-progs
