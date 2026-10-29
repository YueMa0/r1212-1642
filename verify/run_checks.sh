#!/usr/bin/env bash
# Independent computer checks of graph/r1212_1641.graph; about a minute.
# Needs python3 with numpy and networkx (set PY=...) and a C compiler (set CC=...).
# The exhaustive search (about 15 CPU-hours) is not run here; see README.md.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
G="$HERE/../graph/r1212_1641.graph"
PY="${PY:-python3}"
CC="${CC:-cc}"
WORK="${WORK:-$(mktemp -d)}"

echo "### 1. M(797), neighbourhood lemma, certificates"
"$PY" -I "$HERE/check_mathon.py" "$G" "$WORK"
"$CC" -O3 -o "$WORK/maxclique" "$HERE/maxclique.c"
echo "### 2. clique search vs networkx"
"$PY" -I "$HERE/test_maxclique.py" "$WORK/maxclique" "$WORK/test_graph.txt"
echo "### 3. omega(P_797): maximum clique in the 198-vertex common neighbourhoods (must be 7)"
"$WORK/maxclique" "$WORK/p797_red_cn01.txt"
"$WORK/maxclique" "$WORK/p797_blue_cn02.txt"
echo "### 4. projection check on the 1641-vertex graph"
"$PY" -I "$HERE/check_projection.py" "$G"
for e in 1573:1616 1061:1626 1597:1627; do
  echo "### 5. negative control: undo flip $e (must FAIL)"
  "$PY" -I "$HERE/check_projection.py" "$G" "$e" | grep -E "PERTURBED|largest|unresolved \(|RESULT"
done
echo "### 6. projection vs brute force on the 126-vertex P101 instance"
"$PY" -I "$HERE/crosscheck_p101.py" "$HERE/data/P101_H+_4flips_plus1_126.json" "$WORK/maxclique" "$WORK/p101_full.txt"
echo "### 7. rebuild the colouring from the text of report/r1212_report.md and compare"
"$PY" -I "$HERE/rebuild_from_report.py" "$G" "$WORK/rebuilt.graph"
