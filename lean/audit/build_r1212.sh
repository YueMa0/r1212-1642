#!/usr/bin/env bash
# Build the Lean proof of R(12,12) >= 1642.
#
# The eight H01Branch modules each need 4-7 GB of memory in the Lean kernel.
# `lake build` compiles independent modules in parallel and has no option to limit
# this, so the branch modules are built one at a time first.
set -euo pipefail
cd "$(dirname "$0")/.."

lake exe cache get
for i in 0 1 2 3 4 5 6 7; do
  echo "== RamseyIncrement.R1212.H01Branch$i"
  lake build "RamseyIncrement.R1212.H01Branch$i"
done
lake build RamseyIncrement.R1212.Main
lake env lean audit/AxiomAuditR1212.lean
