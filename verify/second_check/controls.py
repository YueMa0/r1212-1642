"""Second check of bruteforce_kclique on the real 1641-vertex graph.

1. Planted K12 by one edge flip, inside the largest tasks (v = 0, |P| about 820), both colours.
   The planted clique is found independently with maxclique.c and re-checked here.
2. Undo each class of R* flips (c2x0, i0x*, a1y0); a true K12 must then be found.
3. Rerun tasks on the unmodified graph and compare result and node count with the log.

usage: python3.14 -I controls.py BF MAXCLIQUE GRAPH LOG WORKDIR
"""
import json
import subprocess
import sys
import time

bf, mc, cand, log_path, work = sys.argv[1:6]
rows = [list(map(int, l)) for l in open(cand).read().split("\n")[:-1]]
n = len(rows)
logged = {(r["v"], r["c"]): r for r in map(json.loads, open(log_path))}

C = [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595]
I = [1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267]
A_NEW = list(range(1596, 1606))          # a0..a9
X_NEW = list(range(1616, 1626))          # x0..x9
XSTAR, Y0 = 1626, 1627
sigma = set(C) | set(I) | set(range(1596, 1641))
core = [v for v in range(1596) if v not in sigma]


def say(*a):
    print(*a, flush=True)


def write(M, path):
    with open(path, "w") as fh:
        fh.write("".join("".join(map(str, r)) + "\n" for r in M))


def is_clique(M, K, c):
    return len(set(K)) == len(K) and all(M[p][q] == c for i, p in enumerate(K) for q in K[i + 1:])


def bf_run(M, name, vlo, vhi, threads):
    path, out = f"{work}/{name}.graph", f"{work}/{name}.jsonl"
    write(M, path)
    open(out, "w").close()
    t0 = time.time()
    subprocess.run([bf, path, "12", out, str(threads), "0", str(vlo), str(vhi)], check=True, capture_output=True)
    return [json.loads(l) for l in open(out)], time.time() - t0


def mc_clique(M, verts, c, target):
    path = f"{work}/mc_in.txt"
    with open(path, "w") as fh:
        fh.write(f"{len(verts)}\n")
        for p in verts:
            fh.write("".join("1" if (p != q and M[p][q] == c) else "0" for q in verts) + "\n")
    out = subprocess.run([mc, path, str(target)], capture_output=True, text=True, check=True).stdout
    for line in out.splitlines():
        if line.startswith("omega") and "witness" in line:
            return [verts[int(t)] for t in line.split("witness")[1].split()]
    return None


say("x0..x9, x* red to all", len(core), "core vertices:", all(rows[x][v] == 1 for x in X_NEW + [XSTAR] for v in core))
say("a0..a9 blue to all core vertices:", all(rows[a][v] == 0 for a in A_NEW for v in core))

# 1. planted K12 at v = 0
for colour, (p, q), name in ((1, (1616, 1617), "x0x1"), (0, (1596, 1597), "a0a1")):
    cname = "red" if colour else "blue"
    say(f"\n[plant {cname}] edge {name} has colour {rows[p][q]}; flip it to {colour}")
    assert rows[p][q] == 1 - colour
    nbrs = [v for v in core if v != 0 and rows[0][v] == colour]
    k9 = mc_clique(rows, nbrs, colour, 9)
    K12 = [0] + k9 + [p, q]
    M = [r[:] for r in rows]
    M[p][q] = M[q][p] = colour
    say(f"  {cname} K12 through v=0 after the flip (maxclique.c witness):", sorted(K12), "| is a clique:", is_clique(M, K12, colour))
    res, dt = bf_run(M, f"plant_{cname}", 0, 1, 2)
    for r in sorted(res, key=lambda r: r["c"]):
        same = logged[(0, r["c"])]
        extra = ""
        if r["result"] == "found":
            extra = f"witness_ok={r.get('witness_ok')} witness={r.get('witness')}"
            K = r.get("witness") or []
            extra += f" | re-checked here: {len(K) == 12 and min(K) == r['v'] and is_clique(M, K, r['c'])}"
        else:
            extra = f"nodes={r['nodes']} (log: {same['nodes']}, equal: {r['nodes'] == same['nodes']})"
        say(f"  task (0,{r['c']}) |P|={r['m']}: {r['result']} {extra} sec={r['sec']}")
    say(f"  wall {dt:.0f}s")

# 2. undo each class of flips
for (p, q, colour, name) in ((1573, 1616, 1, "c2x0"), (1061, XSTAR, 1, "i0x*"), (1597, Y0, 0, "a1y0")):
    assert rows[p][q] == 1 - colour, name
    M = [r[:] for r in rows]
    M[p][q] = M[q][p] = colour
    res, dt = bf_run(M, "undo_" + name.replace("*", "star"), 926, n, 6)
    found = [r for r in res if r["result"] == "found"]
    ok = all(r.get("witness_ok") for r in found)
    rech = all(len(r["witness"]) == 12 and min(r["witness"]) == r["v"] and is_clique(M, r["witness"], r["c"]) for r in found)
    say(f"\n[undo {name}] tasks {len(res)} (v=926..{n - 1}), found {len(found)}, witness_ok all: {ok}, re-checked here: {rech}, wall {dt:.0f}s")
    if found:
        r = found[0]
        say(f"  first: v={r['v']} c={r['c']} witness={r.get('witness')}")

# 3. reruns on the unmodified graph
total = same_nodes = 0
for vlo, vhi in ((1, 3), (400, 404), (1000, 1010), (1300, 1310), (1630, n)):
    res, dt = bf_run(rows, f"rerun_{vlo}", vlo, vhi, 6)
    for r in res:
        total += 1
        lg = logged[(r["v"], r["c"])]
        same_nodes += r["result"] == lg["result"] and r["nodes"] == lg["nodes"] and r["m"] == lg["m"]
    say(f"\n[rerun v={vlo}..{vhi - 1}] {len(res)} tasks, wall {dt:.0f}s")
say(f"reruns identical to the log (result, |P|, nodes): {same_nodes} of {total}")
