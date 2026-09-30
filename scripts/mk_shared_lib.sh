#!/usr/bin/env bash
# Build a shared library that contains every object of a static archive.
# Usage: mk_shared_lib.sh OUT.so ARCHIVE.a [extra link args...]
set -euo pipefail
out=$1
archive=$2
shift 2
if [ "$(uname -s)" = Darwin ]; then
  # Apple's ld has no --whole-archive; -force_load is the equivalent.
  # Symbols from sibling libs / gmp are resolved at load time.
  exec c++ -shared -fPIC -o "$out" -Wl,-force_load,"$archive" \
    -undefined dynamic_lookup "$@"
else
  exec g++ -shared -fPIC -o "$out" \
    -Wl,--whole-archive "$archive" -Wl,--no-whole-archive "$@"
fi
