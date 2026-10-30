"""Exact check that the 1641-vertex file has no monochromatic K12, given that its first 1596
vertices form an (11,11)-graph G (checked separately: the block is M(797)).

Uses nothing from the R* proof or Tatarevic's theorem; only the file and the certificate
vertex list C u I (used as the starting core; the script verifies it suffices).

Method (clone projection):
- Sigma_V = core vertices of V, V0 = V minus Sigma_V, F = the 45 new vertices.
- Each f in F must be, on V0, constant (all red / all blue) or an exact copy of some g in Sigma_V.
- A colour-c clique Q of the whole graph splits as K = Q n (Sigma_V u F) and K0 = Q n V0.
  If K has a member that is constant not-c on V0, then K0 is empty.
  Otherwise K0 lies in V0 n N_c(g) for all g in D(K) = (K n Sigma_V) u {targets of copy-type f in K},
  so for any c-clique D' inside D(K), K0 u D' is a c-clique of G: |K0| <= 10 - omega_c(D(K)).
- slack(K) = omega_c(D(K)) + 1 - |K| never increases when K grows, so it suffices to check
  maximal cliques of (Sigma minus the constant-not-c vertices); plus omega_c(Sigma) <= 11.
"""
import hashlib
from pathlib import Path
import sys
from functools import lru_cache

import networkx as nx
import numpy as np

path = sys.argv[1]
raw = Path(path).read_bytes()
print("sha256", hashlib.sha256(raw).hexdigest())
lines = raw.split(b"\n")
if (len(lines) != 1642 or lines[-1] != b""
        or any(len(row) != 1641 or set(row) - {48, 49} for row in lines[:-1])):
    raise SystemExit("CHECK FAILED: expected 1641 binary LF-terminated rows of length 1641")
O = np.array([np.frombuffer(l, dtype=np.uint8) - 48 for l in lines[:-1]], dtype=np.uint8)
if not (O == O.T).all() or np.diag(O).any():
    raise SystemExit("CHECK FAILED: expected a symmetric graph with zero diagonal")
n, nV = O.shape[0], 1596
V, F = list(range(nV)), list(range(nV, n))
for spec in sys.argv[2:]:  # perturbations for negative controls: u:v flips the colour of edge uv
    u_, v_ = map(int, spec.split(":"))
    if not (0 <= u_ < n and 0 <= v_ < n and u_ != v_):
        raise SystemExit("CHECK FAILED: perturbation must name two distinct vertices in range")
    O[u_, v_] = O[v_, u_] = 1 - O[u_, v_]
    print(f"PERTURBED: flipped edge {u_}-{v_} to {'red' if O[u_, v_] else 'blue'}")

C = [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595]
I = [1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267]
role = {v: f"c{p}" for p, v in enumerate(C)} | {v: f"i{t}" for t, v in enumerate(I)}
names = ([f"a{p}" for p in range(10)] + [f"b{p}" for p in range(10)] + [f"x{r}" for r in range(10)]
         + ["x*"] + [f"y{r}" for r in range(10)] + ["y*", "z", "w", "u"])
role |= dict(zip(F, names))

# --- types of the new vertices on V0 (grow the core if some vertex is not of a clean type)
core = set(C) | set(I)
while True:
    V0 = np.array([v for v in V if v not in core])
    types, grow = {}, set()
    for f in F:
        row = O[f, V0]
        if row.all():
            types[f] = ("const", 1)
            continue
        if not row.any():
            types[f] = ("const", 0)
            continue
        hits = [g for g in sorted(core) if (O[g, V0] == row).all()]
        if len(hits) == 1:
            types[f] = ("copy", hits[0])
            continue
        # not clean: find nearest vertex of V and add it plus the exceptions to the core
        mism = (O[np.ix_(V, V0)] != row).sum(axis=1)
        g = int(np.argmin(mism))
        exc = [int(v) for v in V0 if O[g, v] != O[f, v] and v != g]
        print(f"  {role[f]}: not clean on V0; nearest g={g} with {len(exc)} exceptions")
        grow |= {g, *exc}
    if not grow:
        break
    core |= grow
print(f"core size {len(core)}; |V0| = {len(V0)}")
summary = {}
for f in F:
    t = types[f]
    key = ("const red" if t[1] else "const blue") if t[0] == "const" else f"copy {role.get(t[1], t[1])}"
    summary.setdefault(key, []).append(role[f])
for k, v in summary.items():
    print(f"  {k:12s}: {' '.join(v)}")

Sigma = sorted(core) + F
idx = {v: i for i, v in enumerate(Sigma)}


def omega_c(vs, c):
    """max colour-c clique among vertices vs (exact, via networkx maximal cliques)"""
    vs = list(vs)
    g = nx.Graph()
    g.add_nodes_from(vs)
    g.add_edges_from((u, w) for i, u in enumerate(vs) for w in vs[i + 1:] if O[u, w] == c)
    return max((len(k) for k in nx.find_cliques(g)), default=0)


@lru_cache(maxsize=None)
def omega_D(D, c):
    return omega_c(D, c)


total_bad = 0
for c, cname in [(1, "red"), (0, "blue")]:
    w_sigma = omega_c(Sigma, c)
    print(f"[{cname}] largest {cname} clique inside the {len(Sigma)} core+new vertices: {w_sigma}"
          f" ({'ok' if w_sigma <= 11 else 'FAIL'})")
    total_bad += w_sigma > 11
    no_c = {f for f in F if types[f] == ("const", 1 - c)}
    S2 = [v for v in Sigma if v not in no_c]
    g = nx.Graph()
    g.add_nodes_from(S2)
    g.add_edges_from((u, w) for i, u in enumerate(S2) for w in S2[i + 1:] if O[u, w] == c)
    count, worst, hist, bad = 0, None, {}, []
    for K in nx.find_cliques(g):
        count += 1
        D = set()
        for v in K:
            if v in core:
                D.add(v)
            elif types[v][0] == "copy":
                D.add(types[v][1])
            # const-c: no restriction
        d = omega_D(tuple(sorted(D)), c)
        slack = d + 1 - len(K)
        hist[slack] = hist.get(slack, 0) + 1
        if worst is None or slack < worst[0]:
            worst = (slack, K)
        if slack < 0:
            bad.append(K)
    print(f"[{cname}] maximal cliques checked: {count}; slack histogram {dict(sorted(hist.items()))}")
    print(f"[{cname}] tightest: slack {worst[0]} at {sorted(role.get(v, str(v)) for v in worst[1])}")
    print(f"[{cname}] unresolved (slack < 0): {len(bad)}")
    for K in bad[:10]:
        print("    ", sorted(role.get(v, str(v)) for v in K))
    total_bad += len(bad)
print("RESULT:", "no monochromatic K12 (given G is (11,11))" if total_bad == 0 else f"{total_bad} unresolved")
print("CHECK:", "PASS" if total_bad == 0 else "FAIL")
sys.exit(0 if total_bad == 0 else 1)
