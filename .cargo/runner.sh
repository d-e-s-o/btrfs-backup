#!/bin/sh

# We support `sudo` and attempt to use it, but fall back to `su`
# otherwise. God knows why we need $* for the `su` case instead of $@.
# ¯\_(°-°)_/¯
# Also, we always use a login shell. We have seen cases where, during
# package installation procedure, the temporary directory was redirected
# to a read-only file system and that caused tests to fail.
if command -v sudo; then
  exec sudo --login -- "$@"
else
  exec su --login root --command "$*"
fi
