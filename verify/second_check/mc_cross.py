"""Cross-check a sample of brute-force tasks with the separate program maxclique.c.

For a task (v,c), P(v,c) = {w > v : colour(v,w) = c}; a monochromatic K12 with smallest vertex v
exists iff P(v,c) has a colour-c K11.  maxclique.c is asked for a K11 (target 11), and on smaller
tasks also for the exact clique number.

usage: python3.14 -I mc_cross.py MAXCLIQUE GRAPH LOG WORKDIR WORKERS
"""
import json
import random
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

mc, cand, log_path, work, workers = sys.argv[1:6]
rows = [l for l in open(cand).read().split("\n")[:-1]]
n = len(rows)
logged = {(r["v"], r["c"]): r for r in map(json.loads, open(log_path))}

rng = random.Random(20261029)
tasks = [(0, 0), (2, 1)]
for lo, hi in ((3, 300), (300, 600), (600, 900), (900, 1200), (1200, 1500), (1500, n)):
    for _ in range(2):
        tasks.append((rng.randrange(lo, hi), rng.randrange(2)))


def run(task, exact):
    v, c = task
    ch = "1" if c else "0"
    P = [w for w in range(v + 1, n) if rows[v][w] == ch]
    path = f"{work}/mc_{v}_{c}_{'x' if exact else 't'}.txt"
    with open(path, "w") as fh:
        fh.write(f"{len(P)}\n")
        for p in P:
            fh.write("".join("1" if (p != q and rows[p][q] == ch) else "0" for q in P) + "\n")
    t0 = time.time()
    out = subprocess.run([mc, path] + ([] if exact else ["11"]), capture_output=True, text=True, check=True).stdout
    return task, len(P), out.strip().replace("\n", " | "), time.time() - t0


with ThreadPoolExecutor(int(workers)) as ex:
    jobs = [ex.submit(run, t, False) for t in tasks]
    jobs += [ex.submit(run, t, True) for t in tasks if logged[t]["m"] <= 450]
    for j in jobs:
        (v, c), m, out, dt = j.result()
        lg = logged[(v, c)]
        print(f"task ({v},{c}) |P|={m} (log {lg['m']}, brute force {lg['result']}): maxclique -> {out} [{dt:.0f}s]", flush=True)
