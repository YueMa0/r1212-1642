"""Bounded tests for bruteforce_kclique; any mismatch or incomplete run fails.

usage: python3 -I test_bruteforce.py BINARY WORKDIR CANDIDATE_1641 P101_JSON
"""
import json
import math
from pathlib import Path
import random
import subprocess
import sys

import networkx as nx


def write_graph(rows, path):
    with open(path, "w", encoding="ascii", newline="\n") as fh:
        for r in rows:
            fh.write("".join("1" if x else "0" for x in r) + "\n")


def validate_records(rows, t, records, vlo=0, vhi=None):
    """Check coverage and witnesses independently of the solver's witness_ok flag."""
    n = len(rows)
    expected = {(v, c) for v in range(vlo, n if vhi is None else min(vhi, n)) for c in (0, 1)}
    seen = set()
    for r in records:
        v, c = r["v"], r["c"]
        if type(v) is not int or type(c) is not int or (v, c) not in expected or (v, c) in seen:
            raise ValueError("duplicate, invalid or unexpected task")
        seen.add((v, c))
        if type(r["m"]) is not int or r["m"] != sum(rows[v][w] == c for w in range(v + 1, n)):
            raise ValueError("incorrect candidate size")
        if (type(r["nodes"]) is not int or r["nodes"] < 0 or type(r["sec"]) not in (int, float)
                or not math.isfinite(r["sec"]) or r["sec"] < 0):
            raise ValueError("invalid task statistics")
        if r["result"] not in ("none", "found"):
            raise ValueError("unfinished task (timeout or invalid verdict)")
        if r["result"] == "found":
            w = r["witness"]
            if (r.get("witness_ok") is not True or not isinstance(w, list) or len(w) != t
                    or any(type(u) is not int or not 0 <= u < n for u in w)
                    or len(set(w)) != t or w[0] != v or any(u <= v for u in w[1:])
                    or any(rows[u][z] != c for i, u in enumerate(w) for z in w[i + 1:])):
                raise ValueError("invalid clique witness")
    if seen != expected:
        raise ValueError(f"incomplete task coverage: {len(seen)} of {len(expected)}")
    return records


def run(binary, path, rows, t, extra=()):
    outp = str(path) + f".t{t}.jsonl"
    Path(outp).write_text("", encoding="ascii")
    subprocess.run([binary, str(path), str(t), outp, "1", *map(str, extra)],
                   check=True, capture_output=True, timeout=60)
    raw = Path(outp).read_text(encoding="ascii")
    if raw and not raw.endswith("\n"):
        raise ValueError("truncated task record")
    res = [json.loads(line) for line in raw.splitlines()]
    vlo, vhi = (extra[1], extra[2]) if extra else (0, len(rows))
    return validate_records(rows, t, res, vlo, vhi)


def mono_omega(rows):
    best = 0
    for c in (0, 1):
        g = nx.Graph()
        g.add_nodes_from(range(len(rows)))
        g.add_edges_from((i, j) for i in range(len(rows)) for j in range(i + 1, len(rows)) if rows[i][j] == c)
        best = max(best, max(len(k) for k in nx.find_cliques(g)))
    return best


def main():
    binary, work, cand, p101 = sys.argv[1:5]
    rng = random.Random(7)
    bad = 0
    for trial in range(60):
        m = rng.randint(8, 40)
        p = rng.choice([0.3, 0.5, 0.7])
        rows = [[0] * m for _ in range(m)]
        for i in range(m):
            for j in range(i + 1, m):
                rows[i][j] = rows[j][i] = int(rng.random() < p)
        w = mono_omega(rows)
        path = f"{work}/rand{trial}.txt"
        write_graph(rows, path)
        above = run(binary, path, rows, w + 1)
        at = run(binary, path, rows, w)
        ok = all(r["result"] == "none" for r in above) and any(r["result"] == "found" for r in at)
        bad += not ok
        if not ok:
            print("MISMATCH", f"random trial {trial}")
    print("random 2-colourings: 60 tested, failures:", bad)

    m = json.loads(Path(p101).read_text(encoding="utf-8"))
    rows = [[(int(h, 16) >> j) & 1 for j in range(m["n"])] for h in m["adjacency_hex"]]
    path = f"{work}/p101_126.txt"
    write_graph(rows, path)
    r7, r6 = run(binary, path, rows, 7), run(binary, path, rows, 6)
    p101_ok = all(r["result"] == "none" for r in r7) and any(r["result"] == "found" for r in r6)
    print("P101 126-vertex instance: K7 tasks", len(r7), "results", sorted({r['result'] for r in r7}),
          "| K6 found:", any(r["result"] == "found" for r in r6))
    bad += not p101_ok

    # Undo c2x0: a red K12 with smallest vertex c1=926 must be found.
    lines = Path(cand).read_text(encoding="ascii").splitlines()
    rows = [list(map(int, line)) for line in lines]
    rows[1573][1616] = rows[1616][1573] = 1
    path = f"{work}/planted_1641.txt"
    write_graph(rows, path)
    rp = run(binary, path, rows, 12, (0, 926, 927))
    planted_ok = any(r["c"] == 1 and r["result"] == "found" for r in rp)
    print("planted K12 (undo c2x0), v=926:", [(r["c"], r["result"], r.get("witness_ok")) for r in rp])
    bad += not planted_ok
    print("RESULT:", "PASS" if bad == 0 else f"FAIL: {bad} mismatches")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
