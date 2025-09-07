Unreleased
----------
- Fixed potential backup issues for subvolumes previously restored from
  a snapshot


0.2.3
-----
- Added statically linked builds for `arm-unknown-linux-musleabi` and
  `armv7-unknown-linux-musleabihf` targets


0.2.2
-----
- Removed `once_cell` dependency


0.2.1
-----
- Fixed wrong handling of root (`/`) subvolume in various sub-commands
- Adjusted publish workflow to also create GitHub release and Git tag


0.2.0
-----
- Introduced `--tag` option to various sub-commands to "tag" snapshots
  of the same subvolume for different backup destinations
- Added support for working with remote systems via `--remote-command`
  option
- Fixed `--help` & `--version` options to no longer report errors


0.1.0
-----
- Initial release
