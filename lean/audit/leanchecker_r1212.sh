#!/usr/bin/env bash
# Replay the new modules (ThirdConnector and R1212) through leanchecker, one module per run.
#
# leanchecker replays all modules it is given in parallel, and each H01Branch module
# needs 4-7 GB, so passing them together can exhaust memory.
set -uo pipefail
cd "$(dirname "$0")/.."

modules=(
  ThirdConnector.Construction ThirdConnector.ColourTable ThirdConnector.BlueEdges
  ThirdConnector.RedEdges ThirdConnector.Projection ThirdConnector.BlueU ThirdConnector.RedU
  ThirdConnector.Theorem
  R1212.Paley R1212.Search R1212.H01Data
  R1212.H01Branch0 R1212.H01Branch1 R1212.H01Branch2 R1212.H01Branch3
  R1212.H01Branch4 R1212.H01Branch5 R1212.H01Branch6 R1212.H01Branch7
  R1212.H01NoK8 R1212.PaleyClique R1212.Mathon R1212.Main
)
status=0
for m in "${modules[@]}"; do
  if lake env leanchecker "RamseyIncrement.$m"; then
    echo "ok    RamseyIncrement.$m"
  else
    echo "FAIL  RamseyIncrement.$m"
    status=1
  fi
done
# Control: a module that does not exist must be rejected.
if lake env leanchecker RamseyIncrement.R1212.NoSuchModule > /dev/null 2>&1; then
  echo "FAIL  control: a missing module was accepted"
  status=1
else
  echo "ok    control: a missing module is rejected"
fi
exit $status
