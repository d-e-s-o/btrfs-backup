// Copyright (C) 2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later


/// A replacement of the standard println!() macro that does not panic
/// when encountering an EPIPE.
macro_rules! println {
  ($($arg:tt)*) => {{
    use std::io::Write as _;

    match writeln!(::std::io::stdout(), $($arg)*) {
      Ok(..) => (),
      Err(err) if err.kind() == ::std::io::ErrorKind::BrokenPipe => (),
      Err(err) => panic!("failed printing to stdout: {}", err),
    }
  }};
}
