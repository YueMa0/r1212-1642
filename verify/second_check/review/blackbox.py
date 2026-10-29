"""Black-box per-task differential test of the compiled program against networkx.
For each random 2-colouring and each (v,c): program says found  <=>  omega_c(P(v,c)) >= t-1."""
import json, random, subprocess, sys, os
import networkx as nx
binary, work = sys.argv[1], sys.argv[2]
os.makedirs(work, exist_ok=True)
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)

def write(rows, path, eol="\n", final_eol=True, extra_blank=False):
    with open(path, "w", newline="") as fh:
        for i, r in enumerate(rows):
            fh.write("".join("1" if x else "0" for x in r))
            if i < len(rows) - 1 or final_eol: fh.write(eol)
        if extra_blank: fh.write(eol + eol)

def omega_P(rows, v, c):
    n = len(rows)
    P = [w for w in range(v + 1, n) if rows[v][w] == c]
    g = nx.Graph(); g.add_nodes_from(P)
    g.add_edges_from((a, b) for i, a in enumerate(P) for b in P[i + 1:] if rows[a][b] == c)
    return max((len(k) for k in nx.find_cliques(g)), default=0), len(P)

tot = bad = nf = nn_ = mwf = mwn = 0
for trial in range(int(sys.argv[4]) if len(sys.argv) > 4 else 12):
    n = rng.randint(70, 210)
    p = rng.uniform(0.4, 0.6)
    rows = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            rows[i][j] = rows[j][i] = int(rng.random() < p)
    om = {(v, c): omega_P(rows, v, c) for v in range(n) for c in (0, 1)}
    best = max(o for o, _ in om.values())
    t = rng.choice([best, best + 1, best - 1, best - 2]) + 1   # t-1 near omega of P sets -> mixed results
    variant = trial % 4
    path = f"{work}/g{trial}.txt"
    write(rows, path, eol="\r\n" if variant == 1 else "\n", final_eol=(variant != 2), extra_blank=(variant == 3))
    outp = f"{work}/g{trial}.jsonl"
    if os.path.exists(outp): os.remove(outp)
    pr = subprocess.run([binary, path, str(t), outp, "2"], capture_output=True, text=True)
    assert pr.returncode == 0, pr.stderr
    res = [json.loads(l) for l in open(outp)]
    got = {(r["v"], r["c"]): r for r in res}
    assert len(res) == 2 * n and len(got) == 2 * n, (len(res), n)
    for (v, c), (o, m) in om.items():
        r = got[(v, c)]
        truth = o >= t - 1
        ok = r["m"] == m and ((r["result"] == "found") == truth) and r["result"] != "timeout"
        if r["result"] == "found":
            wv = r["witness"]
            ok &= r["witness_ok"] and wv[0] == v and len(set(wv)) == t and all(w > v for w in wv[1:])
            ok &= all(rows[a][b] == c for i, a in enumerate(wv) for b in wv[i + 1:])
        tot += 1; bad += not ok; nf += truth; nn_ += not truth
        if m > 64: mwf += truth; mwn += not truth
        if not ok: print("MISMATCH", trial, v, c, m, o, t, r)
    print(f"trial {trial}: n={n} p={p:.2f} t={t} variant={variant} tasks={len(res)} found={sum(r['result']=='found' for r in res)}")
print(f"TOTAL tasks={tot} mismatches={bad} truth-found={nf} truth-none={nn_} multiword found={mwf} none={mwn}")
