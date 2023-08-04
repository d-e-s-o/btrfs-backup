[![pipeline](https://github.com/d-e-s-o/btrfs-backup/actions/workflows/test.yml/badge.svg?branch=main)](https://github.com/d-e-s-o/btrfs-backup/actions/workflows/test.yml)
[![crates.io](https://img.shields.io/crates/v/btrfs-backup.svg)](https://crates.io/crates/btrfs-backup)
[![rustc](https://img.shields.io/badge/rustc-1.66+-blue.svg)](https://blog.rust-lang.org/2022/12/15/Rust-1.66.0.html)

btrfs-backup
============

- [Changelog](CHANGELOG.md)

**btrfs-backup** is a program that can be used to backup data from one
or multiple btrfs file systems. It relies on the btrfs(8) utility
program to perform its job and provides a very simple interface for
quick btrfs snapshot creation and transferal.

As for the btrfs file system itself, the unit of backup is a subvolume.
Creation of snapshots for subvolumes is performed on an on demand basis,
that is, only if new data is detected to be available on the respective
subvolume a new snapshot is taken. Transfer of data can happen
incrementally, i.e., only changes over the most recent snapshot state
will have to be sent.

The program reasons in terms of repositories. A repository is a
directory which is used to contain the newly created as well as already
available snapshots.

In terms of backup there are two repositories involved: a source
repository and a destination repository. These repositories are kept in
sync by performing an incremental transfer of the files of a snapshot
from the source to the destination. On the destination repository, the
snapshot will subsequently be remanifested or stored in a file.


Usage
-----

Let's say you have two subvolumes that you would like to back up to
some external HDD mounted at `/mnt/backup`:
```sh
# Mount some backup drive.
$ mount /mnt/backup/
# Create a fake hierarchy of btrfs subvolumes for illustration purposes.
$ mkdir /.btrfs-root/
$ mkdir /.btrfs-root/subdir
$ btrfs subvolume create /.btrfs-root/subvol1
$ btrfs subvolume create /.btrfs-root/subdir/subvol2
```

```
/.btrfs-root/
├── subdir
│   └── subvol2
└── subvol1
```


### Backup
In this setup, backup can be as simple as:
```sh
$ btrfs-backup backup \
    /.btrfs-root/subvol1 \
    /.btrfs-root/subdir/subvol2 \
    --destination /mnt/backup/
```

This command results in the following backup snapshots:
```
/mnt/backup/
├── <hostname>_.btrfs-root-subdir-subvol2_2023-02-20_11:14:35_
└── <hostname>_.btrfs-root-subvol1_2023-02-20:11:14:35_
```

The way backups work on a btrfs file system, a read-only snapshot of the
subvolume to back up is created on the source file system and then sent
over to the destination file system. Shown above are the snapshots on
the destination file system. Because we did not provide the `--source`
argument to the command, snapshots on the source file system are
co-located with the actual subvolume in question (that is, they reside
in the same parent directory):
```
/.btrfs-root/
├── <hostname>_.btrfs-root-subvol1_2023-02-20_11:14:35_
├── subdir
│   ├── <hostname>_.btrfs-root-subdir-subvol2_2023-02-20_11:14:35_
│   └── subvol2
└── subvol1
```

If you want to have snapshots centrally managed, provide the `--source`
flag with a path to a directory on the btrfs file system on which the
subvolumes to back up are located:

```sh
# Create central snapshot location.
$ mkdir /snapshots
$ btrfs-backup backup \
    /.btrfs-root/subvol1 \
    /.btrfs-root/subdir/subvol2 \
    --source /snapshots \
    --destination /mnt/backup/
```

Now instead of the snapshots residing next to the subvolumes:
```
/.btrfs-root/
├── subdir
│   └── subvol2
└── subvol1
```

They are located in a single directory:
```
/snapshots/
├── <hostname>_.btrfs-root-subdir-subvol2_2023-02-20_11:14:35_
└── <hostname>_.btrfs-root-subvol1_2023-02-20_11:14:35_
```


### Restore
Subvolumes can be restored in a similar fashion, using
**btrfs-backup**'s `restore` sub-command:
```sh
# Let's say all our source data is gone and only /mnt/backup still
# available.
$ rm -rf /.btrfs-root
$ btrfs-backup restore \
    /.btrfs-root/subvol1 \
    /.btrfs-root/subdir/subvol2 \
    --source /mnt/backup/
```

Essentially, we now use `/mnt/backup` as the source repository and get
back our original subvolume state along with co-located snapshots (it
works analogous with centrally managed snapshots if you provide the
`--destination` argument):
```
/.btrfs-root/
├── <hostname>_.btrfs-root-subvol1_2023-02-20_11:14:35_
├── subdir
│   ├── <hostname>_.btrfs-root-subdir-subvol2_2023-02-20_11:14:35_
│   └── subvol2
└── subvol1
```


### Purge
**btrfs-backup** is able to identify and delete no longer used snapshots
via the `purge` sub-command. This sub-command accepts the `--keep-for`
argument that understands a duration specification such as `2d` (two
days), `1w` (one week), `5m` (five months), `1y` (one year) and will
delete snapshots older than that.

For example given the following state:
```
/.btrfs-root/
├── <hostname>_.btrfs-root-subvol1_2023-01-31_19:56:07_
├── <hostname>_.btrfs-root-subvol1_2023-02-10_09:23:11_
├── <hostname>_.btrfs-root-subvol1_2023-02-20_11:14:35_
├── subdir
│   ├── <hostname>_.btrfs-root-subdir-subvol2_2023-01-31_19:56:07_
│   ├── <hostname>_.btrfs-root-subdir-subvol2_2023-02-10_09:23:11_
│   ├── <hostname>_.btrfs-root-subdir-subvol2_2023-02-20_11:14:35_
│   └── subvol2
└── subvol1
```

The following command:
```sh
$ date
> Mo 20. Feb 11:15:53 PST 2023
# Delete all snapshots older than two weeks.
$ btrfs-backup purge \
    /.btrfs-root/subvol1 \
    /.btrfs-root/subdir/subvol2 \
    --destination /mnt/backup/ \
    --keep-for 2w
```
will result in the snapshots from `2023-01-31` to be removed because
they are more than two weeks old:
```
/.btrfs-root/
├── <hostname>_.btrfs-root-subvol1_2023-02-10_09:23:11_
├── <hostname>_.btrfs-root-subvol1_2023-02-20_11:14:35_
├── subdir
│   ├── <hostname>_.btrfs-root-subdir-subvol2_2023-02-10_09:23:11_
│   ├── <hostname>_.btrfs-root-subdir-subvol2_2023-02-20_11:14:35_
│   └── subvol2
└── subvol1
```

Please note that the original backed up subvolume will never be deleted
-- only its snapshots will ever be "purged". On top of that, the most
recent snapshot is also always preserved to aid with *incremental*
backups in the future.


### Remote Execution
In many cases it is a requirement to backup a subvolume to a remote host
(or restore a subvolume from it). Mounting a remote btrfs file system
locally by means of, for instance, SSHFS will not provide the ability to
use btrfs specific tools on it.
To that end, commands can be run on the remote host directly (provided
it offers an interface for command execution from the outside and that
is has the required btrfs tool suite installed). A typical example for
remote command execution is SSH. Using **btrfs-backup** on a remote host
by means of an SSH connection can be achieved with the
`--remote-command` argument, which can be provided to the `backup`,
`restore`, as well as `purge` sub-commands. E.g.,

```
$ btrfs-backup backup --remote-command='ssh server'
$ btrfs-backup backup \
    /.btrfs-root/subvol1 \
    /.btrfs-root/subdir/subvol2 \
    --destination /mnt/backup/ \
    --remote-command='ssh server'
```

This command will transfer snapshots over an SSH connection to `server`.
They will be stored inside `/mnt/backup` on the remote system.


### Snapshot Tagging
Snapshots can be "tagged" with a more or less arbitrary string, which
will be contained in the snapshot name. Doing so is enabled by means of
the `--tag` argument to various sub-commands.

When a `purge` is performed, only snapshots of the provided tag will be
affected and all others will be left untouched. That can be useful when
subvolumes are backed up to multiple backups at different frequencies,
as it can help ensure that relevant snapshots are not removed
automatically to preserve the incremental nature of future backups.

On top of that, tags also serve an informational purpose: because the
tag is contained in the snapshot's name, it can be used to easily
identify when a subvolume has been backed up to a certain backup
location last, for example.

Please refer to the help text (`--help`) for additional details.


Installation
------------

**btrfs-backup** is written in Rust and requires the Cargo package
manager to be built. It can be installed using `cargo install
btrfs-backup`. The program requires [`btrfs-progs`][btrfs-progs] to be
installed and its `btrfs` binary to be discoverable via the `PATH`
environment variable.


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
