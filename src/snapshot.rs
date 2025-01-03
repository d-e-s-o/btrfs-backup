// Copyright (C) 2023-2024 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::borrow::Cow;
use std::ffi::OsStr;
use std::fmt::Display;
use std::fmt::Error as FmtError;
use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
use std::path::Path;
use std::path::MAIN_SEPARATOR;
use std::str::FromStr as _;
use std::sync::LazyLock;

use anyhow::ensure;
use anyhow::Context as _;
use anyhow::Result;

use time::format_description::modifier::Day;
use time::format_description::modifier::Hour;
use time::format_description::modifier::Minute;
use time::format_description::modifier::Month;
use time::format_description::modifier::Second;
use time::format_description::modifier::Year;
use time::format_description::Component;
use time::format_description::FormatItem;
use time::Date;
use time::OffsetDateTime;
use time::PrimitiveDateTime;
use time::Time;
use time::UtcOffset;

use uname::uname;

use crate::util::escape;
use crate::util::split_once_escaped;
use crate::util::unescape;


/// The "character" we use for separating intra-component pieces.
///
/// This is a `&str` because while conceptually representable as `char`,
/// the latter is utterly hard to work with and the functions we use
/// this constant with all interoperate much more nicely with `&str`.
const ENCODED_INTRA_COMPONENT_SEPARATOR: &str = "-";
/// The "character" we use for separating the individual components
/// (such as host name and subvolume path) from each other in snapshot
/// names.
const ENCODED_COMPONENT_SEPARATOR: &str = "_";

/// The UTC time zone offset we use throughout the program.
static UTC_OFFSET: LazyLock<UtcOffset> = LazyLock::new(|| {
  UtcOffset::current_local_offset().expect("failed to inquire current local time offset")
});

/// The date format used in snapshot names.
const DATE_FORMAT: [FormatItem<'static>; 5] = [
  FormatItem::Component(Component::Year(Year::default())),
  FormatItem::Literal(ENCODED_INTRA_COMPONENT_SEPARATOR.as_bytes()),
  FormatItem::Component(Component::Month(Month::default())),
  FormatItem::Literal(ENCODED_INTRA_COMPONENT_SEPARATOR.as_bytes()),
  FormatItem::Component(Component::Day(Day::default())),
];

/// The time format used in snapshot names.
const TIME_FORMAT: [FormatItem<'static>; 5] = [
  FormatItem::Component(Component::Hour(Hour::default())),
  FormatItem::Literal(b":"),
  FormatItem::Component(Component::Minute(Minute::default())),
  FormatItem::Literal(b":"),
  FormatItem::Component(Component::Second(Second::default())),
];


/// Retrieve the current local time.
#[inline]
pub fn current_time() -> OffsetDateTime {
  OffsetDateTime::now_utc().to_offset(*UTC_OFFSET)
}


/// A type identifying a subvolume.
///
/// The subvolume is stored in encoded form. Encoding it is a lossy and
/// non-reversible transformation. As a result, we cannot actually
/// retrieve back the subvolume path, but we can tell when a provided
/// path is for this `Subvol` (however, there is the potential for
/// collisions, where two subvolume paths map to the same `Subvol`
/// object, but they are rare and we ignore them).
#[derive(Clone, Debug, Eq, Ord, PartialOrd, PartialEq)]
pub struct Subvol {
  /// The subvolume being referenced, in encoded form.
  encoded: String,
}

impl Subvol {
  /// Create a new `Subvol` object for a subvolume at the provided path.
  pub fn new(subvol: &Path) -> Self {
    Self {
      encoded: Self::to_encoded_string(subvol),
    }
  }

  /// Create a `Subvol` object from an already encoded string.
  fn from_encoded(subvol: String) -> Self {
    Self { encoded: subvol }
  }

  /// A helper method for encoding the provided path.
  fn to_encoded_string(path: &Path) -> String {
    if path == Path::new(&MAIN_SEPARATOR.to_string()) {
      ENCODED_INTRA_COMPONENT_SEPARATOR.to_string()
    } else {
      let string = path.to_string_lossy();
      let string = escape(ENCODED_COMPONENT_SEPARATOR, &string);
      let string = string
        .trim_matches(MAIN_SEPARATOR)
        .replace(MAIN_SEPARATOR, ENCODED_INTRA_COMPONENT_SEPARATOR);
      string
    }
  }

  /// Retrieve the encoded representation of the subvolume.
  fn as_encoded_str(&self) -> &str {
    &self.encoded
  }
}


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
  /// See [`Snapshot::subvol`].
  pub subvol: Cow<'snap, Subvol>,
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
      subvol: Cow::Owned(Subvol::new(subvol)),
    };
    Ok(base_name)
  }
}


/// A snapshot name and its identifying components.
#[derive(Clone, Debug, Eq, Ord, PartialOrd, PartialEq)]
pub struct Snapshot {
  /// The name of the host to which this snapshot belongs.
  pub host: String,
  /// The subvolume that was snapshot.
  pub subvol: Subvol,
  /// The snapshot's time stamp.
  ///
  /// Time is treated as local time.
  pub timestamp: OffsetDateTime,
  /// A tag provided by the user at some point.
  pub tag: String,
  /// An optional number making the snapshot unique, in case the time
  /// stamp is insufficient because of its second resolution.
  pub number: Option<usize>,
}

impl Snapshot {
  /// Generate a `Snapshot` object from a snapshot name, parsing the
  /// constituent parts.
  ///
  /// The subvolume name format of a snapshot is:
  /// <host>_<path>_<date>_<time>_<tag>
  ///
  /// It may also contain an additional <number> suffix, separated from
  /// the main name by another `_`.
  ///
  /// <path> itself has all path separators replaced with underscores.
  pub fn from_snapshot_name(subvol: &OsStr) -> Result<Self> {
    fn from_snapshot_name_impl(subvol: &OsStr) -> Result<Snapshot> {
      let string = subvol
        .to_str()
        .context("subvolume name is not a valid UTF-8 string")?;
      let (host, string) = split_once_escaped(string, ENCODED_COMPONENT_SEPARATOR)
        .context("subvolume name does not contain host component")?;
      let (path, string) = split_once_escaped(string, ENCODED_COMPONENT_SEPARATOR)
        .context("subvolume name does not contain a path")?;
      let (date, string) = string
        .split_once(ENCODED_COMPONENT_SEPARATOR)
        .context("subvolume name does not contain snapshot date")?;
      let (time, string) = string
        .split_once(ENCODED_COMPONENT_SEPARATOR)
        .context("subvolume name does not contain snapshot time")?;
      let (tag, number) = split_once_escaped(string, ENCODED_COMPONENT_SEPARATOR).unzip();
      let tag = tag.unwrap_or(string);

      let time = Time::parse(time, TIME_FORMAT.as_slice())
        .with_context(|| format!("failed to parse snapshot time string: {time}"))?;

      let date = Date::parse(date, DATE_FORMAT.as_slice())
        .with_context(|| format!("failed to parse snapshot date string: {date}"))?;

      let number = number
        .map(|number| {
          usize::from_str(number)
            .with_context(|| format!("failed to parse snapshot number string: {number}"))
        })
        .transpose()?;

      let slf = Snapshot {
        host: unescape(ENCODED_COMPONENT_SEPARATOR, host),
        subvol: Subvol::from_encoded(path.to_string()),
        timestamp: PrimitiveDateTime::new(date, time).assume_offset(*UTC_OFFSET),
        tag: unescape(ENCODED_COMPONENT_SEPARATOR, tag),
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
  pub fn from_subvol_path(subvol: &Path, tag: &str) -> Result<Snapshot> {
    let SnapshotBase { host, subvol } = SnapshotBase::from_subvol_path(subvol)?;

    let slf = Self {
      host: host.into_owned(),
      subvol: subvol.into_owned(),
      // Make sure to erase all sub-second information.
      // SANITY: 0 is always a valid millisecond.
      timestamp: current_time()
        .replace_millisecond(0)
        .expect("failed to replace milliseconds"),
      tag: tag.to_string(),
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
      subvol: Cow::Borrowed(&self.subvol),
    }
  }
}

impl Display for Snapshot {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    let Snapshot {
      host,
      subvol,
      timestamp,
      tag,
      number,
    } = &self;

    let sep = ENCODED_COMPONENT_SEPARATOR;
    let date = timestamp
      .date()
      .format(DATE_FORMAT.as_slice())
      .map_err(|_err| FmtError)?;
    let time = timestamp
      .time()
      .format(TIME_FORMAT.as_slice())
      .map_err(|_err| FmtError)?;

    debug_assert_eq!(escape(sep, &date), date);
    debug_assert_eq!(escape(sep, &time), time);

    let () = write!(
      f,
      "{host}{sep}{subvol}{sep}{date}{sep}{time}{sep}{tag}",
      host = escape(sep, host),
      subvol = subvol.as_encoded_str(),
      tag = escape(sep, tag),
    )?;

    if let Some(number) = number {
      let () = write!(f, "{sep}{number}")?;
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
    let tag = "";
    let path1 = Path::new("/tmp/foobar");
    let path2 = Path::new("/tmp/foobar/");
    let snapshot1 = Snapshot::from_subvol_path(path1, tag).unwrap();
    let snapshot2 = Snapshot::from_subvol_path(path2, tag).unwrap();

    assert_eq!(snapshot1.subvol, snapshot2.subvol);
  }

  /// Check that we can parse a snapshot name and emit it back.
  #[test]
  fn snapshot_name_parsing_and_emitting() {
    let name = OsStr::new("vaio_home-deso-media_2019-10-27_08:23:16_");
    let path = Path::new("/home/deso/media");
    let snapshot = Snapshot::from_snapshot_name(name).unwrap();
    assert_eq!(snapshot.host, "vaio");
    assert_eq!(snapshot.subvol, Subvol::new(path));
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

    let name = OsStr::new("vaio_home-deso-media_2019-10-27_08:23:16__1");
    let snapshot = Snapshot::from_snapshot_name(name).unwrap();
    assert_eq!(snapshot.number, Some(1));
    assert_eq!(OsStr::new(&snapshot.to_string()), name);

    let name = OsStr::new("nuc_-_2023-03-22_21:03:56_usb128gb-samsung");
    let snapshot = Snapshot::from_snapshot_name(name).unwrap();
    assert_eq!(snapshot.number, None);
    assert_eq!(snapshot.subvol, Subvol::new(Path::new("/")));
    assert_eq!(OsStr::new(&snapshot.to_string()), name);

    let tag = "foo-baz_baz";
    let snapshot = Snapshot::from_subvol_path(path, tag).unwrap();
    let snapshot_name = snapshot.to_string();
    let parsed = Snapshot::from_snapshot_name(snapshot_name.as_ref()).unwrap();
    assert_eq!(parsed, snapshot);
  }

  /// Check that snapshot names are ordered as expected.
  #[test]
  fn snapshot_name_ordering() {
    let name1 = OsStr::new("vaio_home-deso-media_2019-10-27_08:23:16_");
    let snapshot1 = Snapshot::from_snapshot_name(name1).unwrap();
    let name2 = OsStr::new("vaio_home-deso-media_2019-10-27_08:23:16__1");
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

  /// Make sure that subvolume path comparisons for `Snapshot` objects
  /// work as expected.
  #[test]
  fn snapshot_subvolume_comparison() {
    fn test(path: &Path) {
      let tag = "";
      let snapshot = Snapshot::from_subvol_path(path, tag).unwrap();
      let name = snapshot.to_string();
      let snapshot = Snapshot::from_snapshot_name(name.as_ref()).unwrap();
      assert_eq!(snapshot.subvol, Subvol::new(path));
    }

    test(Path::new("/snapshots/xxx_yyy"));
    test(Path::new("/snapshots/xxx/yyy"));
    test(Path::new("/snapshots/xxx-yyy"));
  }
}
