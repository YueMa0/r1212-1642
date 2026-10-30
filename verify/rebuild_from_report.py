"""Task B1: rebuild the 1641-vertex colouring from the text of 02_expert_report.md only
(Sections 1.1, 1.2, 2 and Appendices A, B), then compare with the candidate file.

Every switch is applied only after asserting the source colour the report states.

usage: python3.14 -I rebuild_from_report.py CANDIDATE_GRAPH OUT_GRAPH
"""
import hashlib
from pathlib import Path
import sys

import numpy as np


def require(ok, message):
    if not ok:
        raise SystemExit(f"CHECK FAILED: {message}")


cand_path, out_path = sys.argv[1], sys.argv[2]
candidate, output = Path(cand_path), Path(out_path)
require(candidate.resolve(strict=True) != output.resolve()
        and not (output.exists() and candidate.samefile(output)),
        "candidate and output must be different files")
# Read the candidate before producing any output; never compare against our own write.
raw = candidate.read_bytes()
q, k, s = 797, 11, 11
R, Bl = 1, 0

# --- Section 1.2: M(q), labels A_x = x, B_x = q + x, a = 2q, b = 2q + 1
sq = np.zeros(q, dtype=bool)
sq[(np.arange(1, q) ** 2) % q] = True
X_ = np.arange(q)
Dm = (X_[:, None] - X_[None, :]) % q
nV = 2 * q + 2
G = np.zeros((nV, nV), dtype=np.uint8)
G[:q, :q] = sq[Dm]
G[q:2 * q, q:2 * q] = sq[Dm]
cross = (~sq[Dm]) & (Dm != 0)
G[:q, q:2 * q] = cross
G[q:2 * q, :q] = cross.T
G[2 * q, :q] = G[:q, 2 * q] = 1
G[2 * q + 1, q:2 * q] = G[q:2 * q, 2 * q + 1] = 1

# --- Appendix A certificates, Appendix B layout
C = [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595]
I = [1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267]
a = [1596 + p for p in range(k - 1)]
b = [1606 + p for p in range(k - 1)]
x = [1616 + r for r in range(s)]          # x[s-1] = x_*
y = [1627 + r for r in range(s)]          # y[s-1] = y_*
z, w, u = 1638, 1639, 1640
N = 1641
star = s - 1
O = np.full((N, N), 255, dtype=np.uint8)  # 255 = not yet coloured
O[:nV, :nV] = G
V = list(range(nV))
VC = set(C) | set(I)
V0 = [v for v in V if v not in VC]


def setc(p, t, c):
    O[p, t] = O[t, p] = c


def switch(p, t, src, dst):
    require(O[p, t] == src, f"switch {p}-{t}: expected source colour {src}, found {O[p, t]}")
    setc(p, t, dst)


beta = [{p for p in range(k - 1) if G[C[p], I[t]] == Bl} for t in range(s - 1)]
P = beta[0]
T = {t for t in range(s - 1) if G[C[0], I[t]] == R}
Q = set(range(2, k - 1)) - P
require(G[C[0], I[0]] == R and G[C[1], I[0]] == R and P and 2 in P and P <= set(range(2, k - 1)), "Type A")
require(all(bt != {1} for bt in beta), "Type A beta condition")
require(P == {2} and any(G[C[2], I[r]] == R for r in range(2, s - 1)), "(P1), (P2)")
require(0 in T, "0 not in T")

# --- Stage 1 (first lift)
for p in range(k - 1):
    for p2 in range(k - 1):
        if p != p2:
            setc(a[p], a[p2], R)
    for v in V:
        setc(a[p], v, R if v == C[p] else Bl)
blk = lambda p: 0 if p in (0, 1) else 1
for p in range(k - 1):
    for p2 in range(p + 1, k - 1):
        setc(b[p], b[p2], R if blk(p) == blk(p2) else Bl)
    for v in V:
        setc(b[p], v, Bl if v == C[p] else G[C[p], v])
    for p2 in range(k - 1):
        setc(a[p2], b[p], Bl if p2 == p else R)
L = V + a + b
J = I + [a[0]]
require(len(J) == s, "wrong certificate size")

# --- Stage 2 (complementary lift)
yblk = lambda r: 0 if r in (0, 1) else 1
for r in range(s):
    for r2 in range(s):
        if r != r2:
            setc(x[r], x[r2], Bl)
    for v in L:
        setc(x[r], v, Bl if v == J[r] else R)
for r in range(s):
    for r2 in range(r + 1, s):
        setc(y[r], y[r2], Bl if yblk(r) == yblk(r2) else R)
    for v in L:
        setc(y[r], v, R if v == J[r] else O[J[r], v])
    for r2 in range(s):
        setc(x[r2], y[r], R if r2 == r else Bl)

# --- Stage 3 (connector z): z copies b_0 on all vertices so far, z b_0 red; then switches
for v in L + x + y:
    if v != b[0]:
        setc(z, v, O[b[0], v])
setc(z, b[0], R)
for t in T:
    switch(a[0], y[t], Bl, R)
    switch(b[0], y[t], R, Bl)
switch(b[0], y[star], Bl, R)
switch(b[0], b[2], Bl, R)
switch(b[0], x[1], R, Bl)
switch(b[0], x[star], R, Bl)
for r in range(s):
    if r not in (1, star):
        switch(z, x[r], R, Bl)

# --- Stage 4 (connector w): switches, then w
for p in P:
    switch(C[p], x[star], R, Bl)
switch(I[0], a[2], Bl, R)
switch(y[0], y[star], R, Bl)
switch(y[0], y[2], R, Bl)
for v in V:
    setc(w, v, R if v in C else (Bl if v == I[0] else G[I[0], v]))
blue_w = {a[2], b[0], b[1], *[b[p] for p in P], *x[:s - 1],
          *[y[t] for t in range(s - 1) if t not in (0, 2)]}
red_w = {*[a[p] for p in range(k - 1) if p != 2], *[b[p] for p in Q], x[star], y[0], y[2], y[star], z}
require(not blue_w & red_w and len(blue_w | red_w) == 2 * (k - 1) + 2 * s + 1, "connector w colour table")
for v in blue_w:
    setc(w, v, Bl)
for v in red_w:
    setc(w, v, R)
require((O[:N - 1, :N - 1][~np.eye(N - 1, dtype=bool)] != 255).all(), "H+ is not fully coloured")

# --- Section 2: rule R*
switch(C[2], x[0], R, Bl)
switch(I[0], x[star], R, Bl)
for p in range(1, k - 1, 2):
    switch(a[p], y[0], Bl, R)
red_u = {*C, I[0], *[a[p] for p in range(0, k - 1, 2)], *[b[p] for p in range(k - 1) if p != 2],
         x[0], x[star], y[star]}
blue_u = {*I[1:], *[a[p] for p in range(1, k - 1, 2)], b[2], *x[1:s - 1], *y[:s - 1], z, w}
require(not red_u & blue_u and len(red_u | blue_u) == len(VC) + 2 * (k - 1) + 2 * s + 2, "connector u colour table")
for v in red_u:
    setc(u, v, R)
for v in blue_u:
    setc(u, v, Bl)
for v in V0:
    setc(u, v, G[I[0], v])
np.fill_diagonal(O, 0)
require((O != 255).all(), "uncoloured entries")

data = b"".join(bytes(row + 48) + b"\n" for row in O)
mine = hashlib.sha256(data).hexdigest()
lines = raw.split(b"\n")
if (len(lines) != N + 1 or lines[-1] != b""
        or any(len(row) != N or set(row) - {48, 49} for row in lines[:-1])):
    raise SystemExit("CHECK FAILED: candidate must contain 1641 binary LF-terminated rows")
F = np.array([np.frombuffer(l, dtype=np.uint8) - 48 for l in lines[:-1]], dtype=np.uint8)
output.write_bytes(data)
diff = np.argwhere(np.triu(F != O, 1))
print("rebuilt sha256  ", mine)
print("candidate sha256", hashlib.sha256(raw).hexdigest())
identical = data == raw
print("identical:", identical, "| differing pairs:", len(diff))
names = {**{v: f"c{p}" for p, v in enumerate(C)}, **{v: f"i{t}" for t, v in enumerate(I)},
         **{v: f"a{p}" for p, v in enumerate(a)}, **{v: f"b{p}" for p, v in enumerate(b)},
         **{v: (f"x{r}" if r < star else "x*") for r, v in enumerate(x)},
         **{v: (f"y{r}" if r < star else "y*") for r, v in enumerate(y)}, z: "z", w: "w", u: "u"}
for p_, t_ in diff[:20]:
    print("  differs:", names.get(int(p_), p_), names.get(int(t_), t_), "file", F[p_, t_], "rebuilt", O[p_, t_])
print("T =", sorted(T), "| P =", sorted(P), "| Q =", sorted(Q))
print("RESULT:", "PASS" if identical else "FAIL")
sys.exit(0 if identical else 1)
