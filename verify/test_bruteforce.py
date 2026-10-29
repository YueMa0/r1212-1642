"""Tests for bruteforce_kclique against networkx, a known (7,7)-graph, and a planted K12.

usage: python3 -I test_bruteforce.py BINARY WORKDIR CANDIDATE_1641 P101_JSON
"""
import json
import random
import subprocess
import sys

import networkx as nx

binary, work, cand, p101 = sys.argv[1:5]


def write_graph(rows, path):
    with open(path, "w") as fh:
        for r in rows:
            fh.write("".join("1" if x else "0" for x in r) + "\n")


def run(path, t, extra=()):
    outp = path + f".t{t}.jsonl"
    open(outp, "w").close()
    subprocess.run([binary, path, str(t), outp, "4", *map(str, extra)], check=True, capture_output=True)
    res = [json.loads(l) for l in open(outp)]
    return res


def mono_omega(rows):
    best = 0
    for c in (0, 1):
        g = nx.Graph()
        g.add_nodes_from(range(len(rows)))
        g.add_edges_from((i, j) for i in range(len(rows)) for j in range(i + 1, len(rows)) if rows[i][j] == c)
        best = max(best, max(len(k) for k in nx.find_cliques(g)))
    return best


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
    above = run(path, w + 1)
    at = run(path, w)
    ok = (all(r["result"] == "none" for r in above)
          and any(r["result"] == "found" and r["witness_ok"] for r in at)
          and len(above) == 2 * m)
    bad += not ok
print("random 2-colourings: 60 tested, failures:", bad)

m = json.load(open(p101))
rows = [[(int(h, 16) >> j) & 1 for j in range(m["n"])] for h in m["adjacency_hex"]]
path = f"{work}/p101_126.txt"
write_graph(rows, path)
r7, r6 = run(path, 7), run(path, 6)
print("P101 126-vertex instance: K7 tasks", len(r7), "results", sorted({r['result'] for r in r7}),
      "| K6 found:", any(r["result"] == "found" and r["witness_ok"] for r in r6))

# planted: undo the flip c2x0 (1573-1616) in the 1641 candidate; a red K12 with smallest vertex c1=926 exists
lines = open(cand).read().split("\n")[:-1]
rows = [list(map(int, l)) for l in lines]
rows[1573][1616] = rows[1616][1573] = 1
path = f"{work}/planted_1641.txt"
write_graph(rows, path)
rp = run(path, 12, (0, 926, 927))
print("planted K12 (undo c2x0), v=926:", [(r["c"], r["result"], r.get("witness_ok")) for r in rp])
