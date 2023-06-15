// Copyright (C) 2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::borrow::Cow;
use std::ffi::OsStr;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
use std::path::Path;
use std::path::PathBuf;
use std::path::MAIN_SEPARATOR;
use std::str::FromStr as _;

use anyhow::ensure;
use anyhow::Context as _;
use anyhow::Result;

use once_cell::sync::Lazy;

use time::macros::format_description;
use time::util::local_offset::set_soundness;
use time::util::local_offset::Soundness;
use time::Date;
use time::OffsetDateTime;
use time::PrimitiveDateTime;
use time::Time;
use time::UtcOffset;

use uname::uname;

/// The UTC time zone offset we use throughout the program.
static UTC_OFFSET: Lazy<UtcOffset> = Lazy::new(|| {
  if cfg!(test) || cfg!(feature = "test") {
    // SAFETY: Our tests do not mutate the environment.
    let () = unsafe { set_soundness(Soundness::Unsound) };
  }

  let offset = UtcOffset::current_local_offset().unwrap();

  if cfg!(test) || cfg!(feature = "test") {
    // SAFETY: The call is always safe for `Soundness::Sound`.
    let () = unsafe { set_soundness(Soundness::Sound) };
  }

  offset
});


/// A type representing the base name of a snapshot.
///
/// The base name is the part of the first part of a snapshot's name
/// that stays constant over time (but not system), i.e., that has no
/// time information encoded in it and does not depend on data variable
/// over time.
#[derive(Clone, Debug, Eq, Ord, PartialOrd, PartialEq)]
pub struct SnapshotBase<'snap> {
  /// See [`Snapshot::host`].
  pub host: Cow<'snap, str>,
  /// See [`Snapshot::os`].
  pub os: Cow<'snap, str>,
  /// See [`Snapshot::hw`].
  pub hw: Cow<'snap, str>,
  /// See [`Snapshot::subvol`].
  pub subvol: Cow<'snap, Path>,
}

impl SnapshotBase<'_> {
  /// Create a snapshot base name for the provided subvolume.
  pub fn from_subvol_path(subvol: &Path) -> Result<SnapshotBase<'static>> {
    ensure!(
      subvol.is_absolute(),
      "subvolume path {} is not absolute",
      subvol.display()
    );

    let info = uname().context("failed to retrieve uname system information")?;
    let base_name = SnapshotBase {
      host: Cow::Owned(info.nodename.to_lowercase()),
      os: Cow::Owned(info.sysname.to_lowercase()),
      hw: Cow::Owned(info.machine.to_lowercase()),
      subvol: Cow::Owned(subvol.to_path_buf()),
    };
    Ok(base_name)
  }
}


/// A snapshot name and its identifying components.
#[derive(Clone, Debug, Eq, Ord, PartialOrd, PartialEq)]
pub struct Snapshot {
  /// The name of the host to which this snapshot belongs.
  pub host: String,
  /// The operating system identifier of the above host.
  pub os: String,
  /// The above host's hardware type identifier.
  pub hw: String,
  /// The absolute path to the subvolume that was snapshot.
  pub subvol: PathBuf,
  /// The snapshot's time stamp.
  ///
  /// Time is treated as local time.
  pub timestamp: OffsetDateTime,
  /// An optional number making the snapshot unique, in case the time
  /// stamp is insufficient because of its second resolution.
  pub number: Option<usize>,
}

impl Snapshot {
  /// Generate a `Snapshot` object from a snapshot name, parsing the
  /// constituent parts.
  ///
  /// The subvolume name format of a snapshot is:
  /// <host>-<os>-<hw>-<path>-<date>_<time>
  ///
  /// It may also contain an additional <number> suffix, separated from
  /// the main name by another `-`.
  ///
  /// <path> itself has all path separators replaced with underscores.
  pub fn from_snapshot_name(subvol: &OsStr) -> Result<Self> {
    fn from_snapshot_name_impl(subvol: &OsStr) -> Result<Snapshot> {
      let string = subvol
        .to_str()
        .context("subvolume name is not a valid UTF-8 string")?;
      // TODO: We cannot handle '-' separators *within* the various
      //       components correctly. What we'd really need is proper
      //       infrastructure for escaping those characters.
      let (host, string) = string
        .split_once('-')
        .context("subvolume name does not contain host component")?;
      let (os, string) = string
        .split_once('-')
        .context("subvolume name does not contain operating system component")?;
      let (hw, string) = string
        .split_once('-')
        .context("subvolume name does not contain hardware type identifier")?;
      let (path, string) = string
        .split_once('-')
        .context("subvolume name does not contain a path")?;
      let (date, string) = string
        .split_once('_')
        .context("subvolume name does not contain snapshot date")?;

      let (time, number) = string.split_once('-').unzip();
      let time = time.unwrap_or(string);

      let format = format_description!("[hour]:[minute]:[second]");
      let time = Time::parse(time, &format)
        .with_context(|| format!("failed to parse snapshot time string: {time}"))?;

      let format = format_description!("[year]-[month]-[day]");
      let date = Date::parse(date, &format)
        .with_context(|| format!("failed to parse snapshot date string: {date}"))?;

      let number = number
        .map(|number| {
          usize::from_str(number)
            .with_context(|| format!("failed to parse snapshot number string: {number}"))
        })
        .transpose()?;

      let subvol = path.split('_').fold(
        PathBuf::from(MAIN_SEPARATOR.to_string()),
        |mut path, component| {
          path.push(component);
          path
        },
      );

      let slf = Snapshot {
        host: host.to_string(),
        os: os.to_string(),
        hw: hw.to_string(),
        subvol,
        timestamp: PrimitiveDateTime::new(date, time).assume_offset(*UTC_OFFSET),
        number,
      };
      Ok(slf)
    }

    from_snapshot_name_impl(subvol).with_context(|| {
      format!(
        "subvolume {} is not a valid snapshot identifier",
        subvol.to_string_lossy()
      )
    })
  }

  /// Create a new snapshot name using the provided subvolume path
  /// together with information gathered from the system (such as the
  /// current time and date).
  pub fn from_subvol_path(subvol: &Path) -> Result<Snapshot> {
    let SnapshotBase {
      host,
      os,
      hw,
      subvol,
    } = SnapshotBase::from_subvol_path(subvol)?;
    let datetime = OffsetDateTime::now_utc().to_offset(*UTC_OFFSET);

    let slf = Self {
      host: host.into_owned(),
      os: os.into_owned(),
      hw: hw.into_owned(),
      subvol: subvol.into_owned(),
      // Make sure to erase all sub-second information.
      // SANITY: 0 is always a valid millisecond.
      timestamp: datetime.replace_millisecond(0).unwrap(),
      number: None,
    };
    Ok(slf)
  }

  /// Create a new `Snapshot` object based on the current one but with
  /// with `number` cleared.
  pub fn strip_number(&self) -> Self {
    let mut new = self.clone();
    new.number = None;
    new
  }

  /// Create a new `Snapshot` object with its number incremented by one.
  #[inline]
  pub fn bump_number(&self) -> Self {
    let mut new = self.clone();
    new.number = Some(self.number.as_ref().map(|number| number + 1).unwrap_or(0));
    new
  }

  /// Retrieve the base name of the snapshot.
  #[inline]
  pub fn as_base_name(&self) -> SnapshotBase<'_> {
    SnapshotBase {
      host: Cow::Borrowed(&self.host),
      os: Cow::Borrowed(&self.os),
      hw: Cow::Borrowed(&self.hw),
      subvol: Cow::Borrowed(&self.subvol),
    }
  }
}

impl Display for Snapshot {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    // TODO: Need to properly escape separating characters in the
    //       various strings.
    let subvol = self
      .subvol
      .to_string_lossy()
      .trim_matches(MAIN_SEPARATOR)
      .replace(MAIN_SEPARATOR, "_");
    let year = self.timestamp.year();
    let month = self.timestamp.month() as u8;
    let day = self.timestamp.day();
    let hour = self.timestamp.hour();
    let minute = self.timestamp.minute();
    let second = self.timestamp.second();

    let () = write!(
      f,
      "{}-{}-{}-{subvol}-{year:04}-{month:02}-{day:02}_{hour:02}:{minute:02}:{second:02}",
      self.host, self.os, self.hw,
    )?;

    if let Some(number) = self.number {
      let () = write!(f, "-{number}")?;
    }
    Ok(())
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  use std::cmp::Ordering;

  use time::Month;


  /// Check that trailing path separators are handled properly.
  #[test]
  fn snapshot_trailing_path_separator_handling() {
    let path1 = Path::new("/tmp/foobar");
    let path2 = Path::new("/tmp/foobar/");
    let snapshot1 = Snapshot::from_subvol_path(path1).unwrap();
    let snapshot2 = Snapshot::from_subvol_path(path2).unwrap();

    dbg!(&snapshot1.subvol);
    dbg!(&snapshot2.subvol);
    assert_eq!(snapshot1.subvol, snapshot2.subvol);
  }

  /// Check that we can parse a snapshot name and emit it back.
  #[test]
  fn snapshot_name_parsing_and_emitting() {
    let name = OsStr::new("vaio-linux-x86_64-home_deso_media-2019-10-27_08:23:16");
    let snapshot = Snapshot::from_snapshot_name(name).unwrap();
    assert_eq!(snapshot.host, "vaio");
    assert_eq!(snapshot.os, "linux");
    assert_eq!(snapshot.hw, "x86_64");
    assert_eq!(snapshot.subvol, Path::new("/home/deso/media"));
    assert_eq!(
      snapshot.timestamp.date(),
      Date::from_calendar_date(2019, Month::October, 27).unwrap()
    );
    assert_eq!(
      snapshot.timestamp.time(),
      Time::from_hms(8, 23, 16).unwrap()
    );
    assert_eq!(snapshot.number, None);
    assert_eq!(OsStr::new(&snapshot.to_string()), name);

    let name = OsStr::new("vaio-linux-x86_64-home_deso_media-2019-10-27_08:23:16-1");
    let snapshot = Snapshot::from_snapshot_name(name).unwrap();
    assert_eq!(snapshot.number, Some(1));
    assert_eq!(OsStr::new(&snapshot.to_string()), name);
  }

  /// Check that snapshot names are ordered as expected.
  #[test]
  fn snapshot_name_ordering() {
    let name1 = OsStr::new("vaio-linux-x86_64-home_deso_media-2019-10-27_08:23:16");
    let snapshot1 = Snapshot::from_snapshot_name(name1).unwrap();
    let name2 = OsStr::new("vaio-linux-x86_64-home_deso_media-2019-10-27_08:23:16-1");
    let snapshot2 = Snapshot::from_snapshot_name(name2).unwrap();

    assert_eq!(snapshot1.cmp(&snapshot2), Ordering::Less);
    assert_eq!(snapshot1.cmp(&snapshot1), Ordering::Equal);
    assert_eq!(snapshot2.cmp(&snapshot1), Ordering::Greater);
    assert_eq!(
      snapshot1.as_base_name().cmp(&snapshot2.as_base_name()),
      Ordering::Equal
    );
    assert_eq!(
      snapshot1.as_base_name().cmp(&snapshot1.as_base_name()),
      Ordering::Equal
    );
    assert_eq!(
      snapshot2.as_base_name().cmp(&snapshot1.as_base_name()),
      Ordering::Equal
    );
  }
}
