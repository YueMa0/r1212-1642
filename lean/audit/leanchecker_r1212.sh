#!/usr/bin/env bash
# Replay the new modules (ThirdConnector and R1212) through leanchecker.
#
# usage: leanchecker_r1212.sh [-j JOBS]
#
# leanchecker replays all modules it is given in parallel, and each H01Branch module
# needs up to about 7 GB. So the eight branch modules are replayed JOBS per run, with
# JOBS chosen as in build_r1212.sh, and the other modules one per run.
set -uo pipefail
cd "$(dirname "$0")/.."
. audit/jobs.sh
njobs=$(r1212_jobs "$@") || exit 2

status=0
replay() {
  if lake env leanchecker "$@"; then
    echo "ok    $*"
  else
    echo "FAIL  $*"
    status=1
  fi
}

for m in ThirdConnector.Construction ThirdConnector.ColourTable ThirdConnector.BlueEdges \
    ThirdConnector.RedEdges ThirdConnector.Projection ThirdConnector.BlueU ThirdConnector.RedU \
    ThirdConnector.Theorem R1212.Paley R1212.Search R1212.H01Data; do
  replay "RamseyIncrement.$m"
done
i=0
while [ "$i" -lt 8 ]; do
  batch=()
  while [ "$i" -lt 8 ] && [ "${#batch[@]}" -lt "$njobs" ]; do
    batch+=("RamseyIncrement.R1212.H01Branch$i")
    i=$((i + 1))
  done
  replay "${batch[@]}"
done
for m in R1212.H01NoK8 R1212.PaleyClique R1212.Mathon R1212.Main; do
  replay "RamseyIncrement.$m"
done
# Control: a module that does not exist must be rejected.
if lake env leanchecker RamseyIncrement.R1212.NoSuchModule > /dev/null 2>&1; then
  echo "FAIL  control: a missing module was accepted"
  status=1
else
  echo "ok    control: a missing module is rejected"
fi
exit $status
