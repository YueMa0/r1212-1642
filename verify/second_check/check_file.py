"""Second check of the 1641-vertex candidate file against the Lean Mathon graph and the brute-force log."""
import hashlib
import json
import sys

graph_path, lean_path, jsonl_path, cand_json, meta_path = sys.argv[1:6]
raw = open(graph_path, "rb").read()
sha = hashlib.sha256(raw).hexdigest()
meta = dict(l.split(" ", 1) for l in open(meta_path).read().splitlines() if " " in l)
cand = json.load(open(cand_json))
print("sha256", sha, "| = run_meta:", sha == meta["graph_sha256"].strip(), "| = candidate json:", sha == cand["sha256"])
print("bytes", len(raw), "| CR present:", b"\r" in raw, "| ends with newline:", raw.endswith(b"\n"))
lines = raw.decode("ascii").split("\n")
if lines[-1] == "":
    lines.pop()
n = len(lines)
print("rows", n, "| all rows length n and only 0/1:", all(len(l) == n and set(l) <= {"0", "1"} for l in lines))
M = [[ch == "1" for ch in l] for l in lines]
print("diagonal all 0:", all(not M[i][i] for i in range(n)))
print("asymmetric pairs:", sum(M[i][j] != M[j][i] for i in range(n) for j in range(i + 1, n)))
red = [sum(r) for r in M]
print("red degree min/max:", min(red), max(red), "| blue degree min/max:", n - 1 - max(red), n - 1 - min(red))

L = open(lean_path).read().split("\n")[:-1]
assert len(L) == 1596 and all(len(l) == 1596 for l in L)
print("core 1596x1596 cells differing from Lean mathon:",
      sum((L[i][j] == "1") != M[i][j] for i in range(1596) for j in range(1596)))

recs = [json.loads(l) for l in open(jsonl_path)]
keys = [(r["v"], r["c"]) for r in recs]
print("log records", len(recs), "| distinct (v,c)", len(set(keys)),
      "| covers every v in 0..n-1 and c in {0,1}:", set(keys) == {(v, c) for v in range(n) for c in (0, 1)})
print("results:", sorted({r["result"] for r in recs}), "| witness fields:", sum("witness" in r for r in recs))
size = {}
for v in range(n):
    later_red = sum(M[v][v + 1:])
    size[(v, 1)] = later_red
    size[(v, 0)] = (n - 1 - v) - later_red
print("logged |P| = recomputed |P(v,c)| (c=1 red) for", sum(r["m"] == size[(r["v"], r["c"])] for r in recs), "of", len(recs))
print("total nodes %.4e, total CPU seconds %.0f (%.2f h)" % (sum(r["nodes"] for r in recs), sum(r["sec"] for r in recs), sum(r["sec"] for r in recs) / 3600))
big = sorted(recs, key=lambda r: -r["sec"])[:3]
print("slowest tasks:", [(r["v"], r["c"], r["m"], r["nodes"], r["sec"]) for r in big])
