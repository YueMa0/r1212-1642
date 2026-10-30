"""Test maxclique against networkx on random graphs and Paley graphs."""
from pathlib import Path
import random
import runpy
import sys

import networkx as nx

# -I omits the script directory from sys.path; load this local helper explicitly.
run_solver = runpy.run_path(str(Path(__file__).with_name("check_maxclique.py")))["run_solver"]


def run(binary, tmp, adj, target=None):
    with open(tmp, "w", encoding="ascii", newline="\n") as fh:
        fh.write(f"{len(adj)}\n")
        for row in adj:
            fh.write("".join("1" if x else "0" for x in row) + "\n")
    return run_solver(binary, tmp, adj, target)


def nx_omega(adj):
    g = nx.Graph()
    g.add_nodes_from(range(len(adj)))
    g.add_edges_from((i, j) for i in range(len(adj)) for j in range(i + 1, len(adj)) if adj[i][j])
    return max((len(c) for c in nx.find_cliques(g)), default=0)


def main():
    binary, tmp = sys.argv[1:]
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
        got, exact = run(binary, tmp, adj)
        t = rng.randint(1, w + 2)
        gt, found = run(binary, tmp, adj, t)
        if not exact or got != w or found != (w >= t) or gt != (w if found else t - 1):
            bad += 1
            print("MISMATCH", m, p, w, got, t, gt, found)
    print("random graphs: 300 tested, mismatches:", bad)

    for q in [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113]:
        sq = {x * x % q for x in range(1, q)}
        adj = [[1 if (i - j) % q in sq else 0 for j in range(q)] for i in range(q)]
        got, exact = run(binary, tmp, adj)
        ref = nx_omega(adj) if q <= 61 else None
        print(f"P_{q}: omega {got}" + (f" (networkx {ref})" if ref is not None else ""))
        if not exact or (ref is not None and got != ref):
            bad += 1
            print("MISMATCH", f"P_{q}", ref, got)
    print("RESULT:", "PASS" if bad == 0 else f"FAIL: {bad} mismatches")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
