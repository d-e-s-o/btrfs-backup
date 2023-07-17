// Copyright (C) 2022-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A module providing the means to create btrfs-progs commands for a
//! chosen set of purposes as necessary by the program.

use std::borrow::Cow;
use std::ffi::OsStr;
use std::ffi::OsString;
use std::path::Path;

use crate::util::Either;


/// Retrieve the command to create a new btrfs subvolume.
pub fn create(subvol: &Path) -> impl IntoIterator<Item = &OsStr> + Clone {
  ["subvolume".as_ref(), "create".as_ref(), subvol.as_os_str()]
}

/// Retrieve the command to delete a btrfs subvolume.
pub fn delete(subvol: &Path) -> impl IntoIterator<Item = &OsStr> + Clone {
  ["subvolume".as_ref(), "delete".as_ref(), subvol.as_os_str()]
}

/// Retrieve the command to create a snapshot of a subvolume.
pub fn snapshot<'input>(
  source: &'input Path,
  destination: &'input Path,
  readonly: bool,
) -> impl IntoIterator<Item = &'input OsStr> + Clone {
  let command = [
    "subvolume".as_ref(),
    "snapshot".as_ref(),
    source.as_os_str(),
    destination.as_os_str(),
  ];

  if readonly {
    Either::Left(command.into_iter().chain(["-r".as_ref()]))
  } else {
    Either::Right(command.into_iter())
  }
}

/// Retrieve the command to sync the given btrfs file system to disk.
///
/// # Notes
/// A sync operation should be performed before attempting to send
/// (i.e., serialize) a btrfs snapshot.
pub fn sync(filesystem: &Path) -> impl IntoIterator<Item = &OsStr> + Clone {
  [
    "filesystem".as_ref(),
    "sync".as_ref(),
    filesystem.as_os_str(),
  ]
}

/// Retrieve the command to serialize a btrfs subvolume into a byte stream.
pub fn serialize<'input, I>(
  subvol: &'input Path,
  parents: I,
) -> impl IntoIterator<Item = &'input OsStr> + Clone
where
  // TODO: Ideally we'd accept any P: AsRef<OsStr> as item, but that
  //       fails with today's borrow checker.
  I: IntoIterator<Item = &'input OsStr>,
  I::IntoIter: Clone,
{
  // We only use the clone-source (-c) option here and not the
  // parent (-p) one because we can specify multiple clone sources
  // (the parameter is allowed multiple times) whereas we must only
  // specify one parent. In any case, if the -c option is given the
  // btrfs command will figure out the parent to use by itself.
  //
  // In general, the clone-source option specifies that data from a
  // given snapshot (that has to be available on both the source and
  // the destination) is used when constructing back the subvolume
  // from the byte stream. This additional information can be used
  // to achieve better sharing of internally used data in the
  // resulting subvolume. Since the clone-source option implies the
  // parent option, it also instructs the command to send only the
  // incremental data (to the latest snapshot).
  let options = parents
    .into_iter()
    .flat_map(|parent| ["-c".as_ref(), parent]);

  ["send".as_ref()]
    .into_iter()
    .chain(options)
    .chain([subvol.as_os_str()])
}

/// Retrieve the command to deserialize a btrfs subvolume from a byte
/// stream.
pub fn deserialize(destination: &Path) -> impl IntoIterator<Item = &OsStr> + Clone {
  ["receive".as_ref(), destination.as_os_str()]
}

/// Retrieve a command to list all subvolumes in a given directory.
///
/// The order of subvolumes is unspecified.
///
/// # Notes
/// Please be aware of the wrong handling of the `-o` parameter by
/// `btrfs`, leading to *not* necessarily only subvolumes below the
/// given directory being returned.
pub fn subvolumes(directory: &Path, readonly: bool) -> impl IntoIterator<Item = &OsStr> + Clone {
  // Note: We do not pass in the -s option here. The reason is that once
  //       we send and received a snapshot, the property of it being a
  //       snapshot is lost. The only property that is preserved is it
  //       being read-only.
  // Note: We could report subvolumes in a sorted manner via something
  //       like `--sort=path`, but we want to leave sorting up to higher
  //       levels.
  let command = [
    "subvolume".as_ref(),
    "list".as_ref(),
    "-o".as_ref(),
    directory.as_os_str(),
  ];

  if readonly {
    Either::Left(command.into_iter().chain(["-r".as_ref()]))
  } else {
    Either::Right(command.into_iter())
  }
}

/// Retrieve a command to query a list of changed files for the given
/// subvolume.
///
/// This function creates a command that, given a btrfs subvolume and
/// a previous generation ID, determines the files that have been
/// changed.
pub fn diff(subvol: &Path, generation: usize) -> impl IntoIterator<Item = Cow<'_, OsStr>> + Clone {
  let generation = generation.to_string();
  [
    "subvolume".as_ref(),
    "find-new".as_ref(),
    subvol.as_os_str(),
  ]
  .into_iter()
  .map(Cow::from)
  .chain([Cow::from(OsString::from(generation))])
}

/// Retrieve the command to show information about a btrfs file
/// system.
pub fn show_filesystem(filesystem: &Path) -> impl IntoIterator<Item = &OsStr> + Clone {
  [
    "filesystem".as_ref(),
    "show".as_ref(),
    filesystem.as_os_str(),
  ]
}

/// Retrieve the command to retrieve the subvolume ID of a given path.
pub fn root_id(path: &Path) -> impl IntoIterator<Item = &OsStr> + Clone {
  [
    "inspect-internal".as_ref(),
    "rootid".as_ref(),
    path.as_os_str(),
  ]
}

/// Retrieve the command to resolve the path for a subvolume ID.
pub fn resolve_id(id: usize, path: &Path) -> impl IntoIterator<Item = Cow<'_, OsStr>> + Clone {
  let id = id.to_string();

  ["inspect-internal".as_ref(), "subvolid-resolve".as_ref()]
    .into_iter()
    .map(Cow::Borrowed)
    .chain([Cow::from(OsString::from(id))])
    .chain([Cow::from(path.as_os_str())])
}


/// Retrieve the command to make a subvolume read-only.
pub fn set_readonly(path: &Path) -> impl IntoIterator<Item = Cow<'_, OsStr>> + Clone {
  ["property".as_ref(), "set".as_ref()]
    .into_iter()
    .map(Cow::Borrowed)
    .chain([
      Cow::from(path.as_os_str()),
      Cow::from(OsStr::new("ro")),
      Cow::from(OsStr::new("true")),
    ])
}


#[cfg(test)]
mod tests {
  use super::*;

  use crate::util::join;


  /// Make sure that we can construct the proper `btrfs` command
  /// arguments.
  #[test]
  fn command_construction() {
    /// Convert an iterator of `OsStr` into a string.
    fn stringify<'iter, I>(iter: I) -> String
    where
      I: IntoIterator<Item = &'iter OsStr>,
    {
      let iter = iter.into_iter().map(|part| part.to_str().unwrap());
      join(' ', iter).unwrap()
    }

    /// Convert an iterator of `Cow<OsStr>` into a string.
    fn stringify_cow<'iter, I>(iter: I) -> String
    where
      I: IntoIterator<Item = Cow<'iter, OsStr>>,
    {
      let iter = iter
        .into_iter()
        .map(|part| part.to_str().unwrap().to_string());
      join(' ', iter).unwrap()
    }


    let command = stringify(create(Path::new("/tmp/foobar")));
    assert_eq!(command, "subvolume create /tmp/foobar");

    let command = stringify(delete(Path::new("blahblubber")));
    assert_eq!(command, "subvolume delete blahblubber");

    let src = Path::new("source");
    let dst = Path::new("destination");
    let command = stringify(snapshot(src, dst, true));
    assert_eq!(command, "subvolume snapshot source destination -r");

    let command = stringify(snapshot(src, dst, false));
    assert_eq!(command, "subvolume snapshot source destination");

    let fs = Path::new("some-filesystem");
    let command = stringify(sync(fs));
    assert_eq!(command, "filesystem sync some-filesystem");

    let subvol = Path::new("a-sub-volume");
    let parents = [];
    let command = stringify(serialize(subvol, parents));
    assert_eq!(command, "send a-sub-volume");

    let dst = Path::new("destination-volume");
    let command = stringify(deserialize(dst));
    assert_eq!(command, "receive destination-volume");

    let dir = Path::new("/usr/bin/baz");
    let readonly = true;
    let command = stringify(subvolumes(dir, readonly));
    assert_eq!(command, "subvolume list -o /usr/bin/baz -r");

    let subvol = Path::new("/var/my-subvol");
    let gen = 1337;
    let command = stringify_cow(diff(subvol, gen));
    assert_eq!(command, "subvolume find-new /var/my-subvol 1337");

    let fs = Path::new("another-fs");
    let command = stringify(show_filesystem(fs));
    assert_eq!(command, "filesystem show another-fs");

    let path = Path::new("/var/some-path");
    let command = stringify(root_id(path));
    assert_eq!(command, "inspect-internal rootid /var/some-path");

    let id = 42;
    let path = Path::new("hihi-i-am-relative");
    let command = stringify_cow(resolve_id(id, path));
    assert_eq!(
      command,
      "inspect-internal subvolid-resolve 42 hihi-i-am-relative"
    );

    let path = Path::new("/var/some-subvol");
    let command = stringify_cow(set_readonly(path));
    assert_eq!(command, "property set /var/some-subvol ro true");
  }
}
