"""Test maxclique against networkx on random graphs and Paley graphs."""
import random
import subprocess
import sys

import networkx as nx

binary, tmp = sys.argv[1], sys.argv[2]


def run(adj, target=0):
    with open(tmp, "w") as fh:
        fh.write(f"{len(adj)}\n")
        for row in adj:
            fh.write("".join("1" if x else "0" for x in row) + "\n")
    out = subprocess.run([binary, tmp] + ([str(target)] if target else []),
                         capture_output=True, text=True, check=True).stdout
    for line in out.splitlines():
        if line.startswith("omega <="):
            return int(line.split()[-1]), False
        if line.startswith("omega"):
            return int(line.split()[1]), True
    raise RuntimeError(out)


def nx_omega(adj):
    g = nx.Graph()
    g.add_nodes_from(range(len(adj)))
    g.add_edges_from((i, j) for i in range(len(adj)) for j in range(i + 1, len(adj)) if adj[i][j])
    return max((len(c) for c in nx.find_cliques(g)), default=0)


rng = random.Random(1)
bad = 0
for trial in range(300):
    m = rng.randint(1, 70)
    p = rng.choice([0.1, 0.3, 0.5, 0.7, 0.9])
    adj = [[0] * m for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            if rng.random() < p:
                adj[i][j] = adj[j][i] = 1
    w = nx_omega(adj)
    got, _ = run(adj)
    t = rng.randint(1, w + 2)
    gt, found = run(adj, t)
    if got != w or found != (w >= t):
        bad += 1
        print("MISMATCH", m, p, w, got, t, found)
print("random graphs: 300 tested, mismatches:", bad)

for q in [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113]:
    sq = {x * x % q for x in range(1, q)}
    adj = [[1 if (i - j) % q in sq else 0 for j in range(q)] for i in range(q)]
    got, _ = run(adj)
    ref = nx_omega(adj) if q <= 61 else None
    print(f"P_{q}: omega {got}" + (f" (networkx {ref})" if ref is not None else ""))
