"""Cross-check the projection method against brute force on the project's 126-vertex instance
(P101 + Tatarevic, k=s=6, plus a third vertex with 4 flips; claimed to be a (7,7)-graph).

1. Load the bitrows JSON; V = first 101 vertices; check the V-block is P_101 (omega = alpha = 5).
2. Projection check (same logic as check_projection.py, parameterised by omega(G) = 5).
3. Brute force: exact maximum clique of the whole graph in both colours with the C program.
"""
import json
import subprocess
import sys

import networkx as nx
import numpy as np

path, binary, tmp = sys.argv[1], sys.argv[2], sys.argv[3]
m = json.load(open(path))
n, labels = m["n"], m["labels"]
rows = [int(h, 16) for h in m["adjacency_hex"]]
O = np.array([[(rows[i] >> j) & 1 for j in range(n)] for i in range(n)], dtype=np.uint8)
assert (O == O.T).all() and not np.diag(O).any(), "bit order / symmetry"
nV, wG = 101, 5
q = 101
sq = {x * x % q for x in range(1, q)}
P = np.array([[1 if (i - j) % q in sq else 0 for j in range(q)] for i in range(q)], dtype=np.uint8)
print("V-block equals P_101 (as labelled):", bool((O[:nV, :nV] == P).all()))
V, F = list(range(nV)), list(range(nV, n))
core = {i for i, l in enumerate(labels[:nV]) if l[0] in "ci" and l[1:].isdigit()}
print("core from labels:", sorted(labels[i] for i in core), "| new:", [labels[f] for f in F])


def omega_c(vs, c):
    vs = list(vs)
    g = nx.Graph()
    g.add_nodes_from(vs)
    g.add_edges_from((u, w) for i, u in enumerate(vs) for w in vs[i + 1:] if O[u, w] == c)
    return max((len(k) for k in nx.find_cliques(g)), default=0)


while True:
    V0 = np.array([v for v in V if v not in core])
    types, grow = {}, set()
    for f in F:
        row = O[f, V0]
        if row.all() or not row.any():
            types[f] = ("const", int(row.all()))
            continue
        hits = [g for g in sorted(core) if (O[g, V0] == row).all()]
        if len(hits) == 1:
            types[f] = ("copy", hits[0])
            continue
        mism = (O[np.ix_(V, V0)] != row).sum(axis=1)
        g = int(np.argmin(mism))
        grow |= {g, *[int(v) for v in V0 if O[g, v] != O[f, v] and v != g]}
    if not grow:
        break
    core |= grow
print("core size after growth:", len(core))
Sigma = sorted(core) + F
ok = True
for c, cname in [(1, "red"), (0, "blue")]:
    ws = omega_c(Sigma, c)
    no_c = {f for f in F if types[f] == ("const", 1 - c)}
    S2 = [v for v in Sigma if v not in no_c]
    g = nx.Graph()
    g.add_nodes_from(S2)
    g.add_edges_from((u, w) for i, u in enumerate(S2) for w in S2[i + 1:] if O[u, w] == c)
    bad = cnt = 0
    for K in nx.find_cliques(g):
        cnt += 1
        D = {v if v in core else types[v][1] for v in K if v in core or types[v][0] == "copy"}
        if omega_c(D, c) + 1 - len(K) < 0:
            bad += 1
    print(f"[{cname}] projection: omega inside Sigma {ws}, maximal cliques {cnt}, unresolved {bad}")
    ok &= ws <= wG + 1 and bad == 0
print("projection verdict:", "(7,7)-graph" if ok else "not proved")

for c, cname in [(1, "red"), (0, "blue")]:
    A = O if c else (1 - O) * (1 - np.eye(n, dtype=np.uint8))
    with open(tmp, "w") as fh:
        fh.write(f"{n}\n")
        for r in A:
            fh.write("".join(map(str, r)) + "\n")
    out = subprocess.run([binary, tmp], capture_output=True, text=True, check=True).stdout
    print(f"[{cname}] brute force on all {n} vertices:", out.split("\n")[0])
