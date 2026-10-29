#!/usr/bin/env bash
# Replay the 43 modules of Tatarevic's library through leanchecker, one module per run.
set -uo pipefail
cd "$(dirname "$0")/.."

status=0
while IFS= read -r f; do
  m=$(echo "$f" | sed -e 's/\.lean$//' -e 's|/|.|g')
  if lake env leanchecker "$m"; then
    echo "ok    $m"
  else
    echo "FAIL  $m"
    status=1
  fi
done < <(find RamseyIncrement -name '*.lean' -not -path '*/R1212/*' -not -path '*/ThirdConnector/*' | sort)
exit $status
