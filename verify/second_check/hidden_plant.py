"""Hidden planted K12 in the largest tasks: a K10 of M(797) through v plus two random ordinary
vertices of M(797), flipping only the pairs that are not yet of the planted colour.  Unlike x0/x1 or
a0/a1, these vertices have ordinary degrees, so the search has to dig for the clique.

usage: python3.14 -I hidden_plant.py BF MAXCLIQUE GRAPH LOG WORKDIR
"""
import json
import random
import subprocess
import sys
import time

bf, mc, cand, log_path, work = sys.argv[1:6]
rows = [list(map(int, l)) for l in open(cand).read().split("\n")[:-1]]
n = len(rows)
logged = {(r["v"], r["c"]): r for r in map(json.loads, open(log_path))}
C = [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595]
I = [1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267]
sigma = set(C) | set(I) | set(range(1596, 1641))
core = [v for v in range(1596) if v not in sigma]
rng = random.Random(1642)


def is_clique(M, K, c):
    return len(set(K)) == len(K) and all(M[p][q] == c for i, p in enumerate(K) for q in K[i + 1:])


def mc_clique(M, verts, c, target):
    path = f"{work}/hmc_in.txt"
    with open(path, "w") as fh:
        fh.write(f"{len(verts)}\n")
        for p in verts:
            fh.write("".join("1" if (p != q and M[p][q] == c) else "0" for q in verts) + "\n")
    out = subprocess.run([mc, path, str(target)], capture_output=True, text=True, check=True).stdout
    for line in out.splitlines():
        if line.startswith("omega") and "witness" in line:
            return [verts[int(t)] for t in line.split("witness")[1].split()]
    return None


for v, colour in ((0, 1), (0, 0), (1, 1), (1, 0)):
    cname = "red" if colour else "blue"
    nb = [w for w in core if w > v and rows[v][w] == colour]
    k9 = mc_clique(rows, nb, colour, 9)
    rest = [w for w in nb if w not in k9]
    p, q = rng.sample(rest, 2)
    K12 = [v] + k9 + [p, q]
    M = [r[:] for r in rows]
    flips = []
    for i, s in enumerate(K12):
        for t in K12[i + 1:]:
            if M[s][t] != colour:
                M[s][t] = M[t][s] = colour
                flips.append((s, t))
    assert is_clique(M, K12, colour) and min(K12) == v
    path, out = f"{work}/hidden_{v}_{colour}.graph", f"{work}/hidden_{v}_{colour}.jsonl"
    with open(path, "w") as fh:
        fh.write("".join("".join(map(str, r)) + "\n" for r in M))
    open(out, "w").close()
    t0 = time.time()
    subprocess.run([bf, path, "12", out, "2", "0", str(v), str(v + 1)], check=True, capture_output=True)
    print(f"[hidden {cname} K12 at v={v}] {len(flips)} flips; planted extra vertices {p},{q}; wall {time.time() - t0:.0f}s", flush=True)
    for r in sorted((json.loads(l) for l in open(out)), key=lambda r: r["c"]):
        lg = logged[(v, r["c"])]
        if r["c"] == colour:
            K = r.get("witness") or []
            print(f"  task ({v},{r['c']}) |P|={r['m']}: {r['result']} after {r['nodes']} nodes, {r['sec']}s; "
                  f"witness_ok={r.get('witness_ok')}, re-checked here: {len(K) == 12 and min(K) == v and is_clique(M, K, colour)}, "
                  f"same as planted: {sorted(K) == sorted(K12)}", flush=True)
        else:
            print(f"  task ({v},{r['c']}) unchanged: {r['result']} nodes={r['nodes']} (log {lg['nodes']}, equal: {r['nodes'] == lg['nodes']})", flush=True)
