#!/usr/bin/env bash
# Check r1212_lower_bound and everything it uses with nanoda, an independent Lean 4 kernel.
#
# usage: LEAN4EXPORT=/path/to/lean4export NANODA=/path/to/nanoda_bin ./run_nanoda.sh
#
# Versions used for the logs in logs/: lean4export tag v4.32.2 (commit 86e4a33) built with
# its lean-toolchain set to v4.32.1; nanoda_lib commit d0a02cc (version 0.4.30), built with
# `cargo build --release --locked`. The full check needs about 11 GB of memory with 2 threads.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${LEAN4EXPORT:?set LEAN4EXPORT to the lean4export binary}"
: "${NANODA:?set NANODA to the nanoda_bin binary}"

mkdir -p "$HERE/export"
(cd "$HERE/../.." && lake env "$LEAN4EXPORT" RamseyIncrement.R1212.Main -- \
  RamseyIncrement.R1212.r1212_lower_bound) > "$HERE/export/r1212_lower_bound.ndjson"
cd "$HERE"
"$NANODA" configs/full.json
