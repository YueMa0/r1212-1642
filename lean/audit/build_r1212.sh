#!/usr/bin/env bash
# Build the Lean proof of R(12,12) >= 1642.
#
# usage: build_r1212.sh [-j JOBS]
#
# The eight H01Branch modules each need up to about 7 GB of memory in the Lean kernel.
# `lake build` compiles independent modules in parallel and has no option to limit
# this, so the branch modules are built first, JOBS per `lake build` call. JOBS comes
# from -j, else from R1212_JOBS, else from the memory size: (GB - 4) / 7, between 1
# and 8 (1 with 16 GB, 4 with 32 GB). See jobs.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
. audit/jobs.sh
njobs=$(r1212_jobs "$@")

lake exe cache get
i=0
while [ "$i" -lt 8 ]; do
  batch=()
  while [ "$i" -lt 8 ] && [ "${#batch[@]}" -lt "$njobs" ]; do
    batch+=("RamseyIncrement.R1212.H01Branch$i")
    i=$((i + 1))
  done
  echo "== ${batch[*]}"
  lake build "${batch[@]}"
done
# Exercise the default target too: it must include the final R1212 theorem.
lake build
lake env lean audit/AxiomAuditR1212.lean
