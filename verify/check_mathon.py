"""Independent check, written from the report's definitions only (not the project's code).

1. Load the 1641-vertex candidate (0/1 text, char v of line u = 1 iff uv red).
2. Rebuild P_797 and M(797) with labels A_x=x, B_x=797+x, a=1594, b=1595 and compare
   with the file's first 1596 vertices.
3. Neighbourhood lemma for M(797), checked on the file's block:
   automorphisms x->alpha*x+beta (alpha square) on both copies, the swap A<->B, a<->b,
   and explicit isomorphisms of the red / blue neighbourhoods of A_0 and a with P_797.
4. Certificates C, I from the report: red K10, blue K10, disjoint, incidence matrix,
   Type A, (P1), (P2).
5. Write the two 198-vertex graphs whose clique numbers decide omega(P_797), alpha(P_797).
"""
import hashlib
import sys

import numpy as np

path, outdir = sys.argv[1], sys.argv[2]
q = 797
raw = open(path, "rb").read()
print("sha256", hashlib.sha256(raw).hexdigest())
lines = raw.split(b"\n")
assert lines[-1] == b"" and len(lines) == 1642
O = np.array([np.frombuffer(l, dtype=np.uint8) - 48 for l in lines[:-1]], dtype=np.uint8)
n = O.shape[0]
assert O.shape == (1641, 1641) and set(np.unique(O)) <= {0, 1}
assert (O == O.T).all(), "not symmetric"
assert (np.diag(O) == 0).all(), "diagonal not 0"
print("file: 1641x1641, symmetric, zero diagonal; red density", O.sum() / (n * (n - 1)))

# --- 2. P_q and M(q)
sq = np.zeros(q, dtype=bool)
sq[(np.arange(1, q) ** 2) % q] = True        # nonzero squares
QR = np.flatnonzero(sq)
NQR = np.array([x for x in range(1, q) if not sq[x]])
assert len(QR) == len(NQR) == (q - 1) // 2 and sq[q - 1]   # -1 is a square (q = 1 mod 4)
X = np.arange(q)
D = (X[:, None] - X[None, :]) % q
P = sq[D].astype(np.uint8)                   # red iff difference is a nonzero square
nonsq = (~sq[D]) & (D != 0)

N = 2 * q + 2
a, b = 2 * q, 2 * q + 1
M = np.zeros((N, N), dtype=np.uint8)
M[:q, :q] = P
M[q:2 * q, q:2 * q] = P
M[:q, q:2 * q] = nonsq                       # A_x B_y red iff x != y and x-y non-square
M[q:2 * q, :q] = nonsq.T
M[a, :q] = M[:q, a] = 1
M[b, q:2 * q] = M[q:2 * q, b] = 1
assert (M == M.T).all() and (np.diag(M) == 0).all()
G = O[:N, :N]
print("file block 0..1595 equals M(797):", bool((G == M).all()),
      "| differing pairs:", int((G != M).sum()) // 2)

# --- 3. neighbourhood lemma, checked on the file's block G
def is_aut(perm):
    perm = np.asarray(perm)
    return bool((G[np.ix_(perm, perm)] == G).all())

g = next(h for h in range(2, q) if all(pow(h, (q - 1) // p, q) != 1 for p in (2, 199)))  # primitive root
alpha = g * g % q                                       # generates the squares
for al, be in [(alpha, 0), (1, 1)]:
    img = (al * X + be) % q
    perm = np.concatenate([img, q + img, [a, b]])
    print(f"x -> {al}x+{be} on both copies is an automorphism:", is_aut(perm))
swap = np.concatenate([q + X, X, [b, a]])
print("swap A<->B, a<->b is an automorphism:", is_aut(swap))

inv = np.array([0] + [pow(int(x), q - 2, q) for x in range(1, q)])
nn = int(NQR[0])

def check_iso(verts, images, colour):
    verts, images = np.asarray(verts), np.asarray(images)
    assert len(set(images.tolist())) == q
    sub = G[np.ix_(verts, verts)] if colour == 1 else (1 - G[np.ix_(verts, verts)]) * (1 - np.eye(len(verts), dtype=np.uint8))
    return bool((sub == P[np.ix_(images, images)]).all())

A0 = 0
red_A0 = np.flatnonzero(G[A0] == 1)
exp_red = np.concatenate([[a], QR, q + NQR])
print("N_red(A_0) as expected:", set(red_A0.tolist()) == set(exp_red.tolist()),
      "| iso to P_797 via a->0, A_x->1/x, B_y->1/y:",
      check_iso(exp_red, np.concatenate([[0], inv[QR], inv[NQR]]), 1))
blue_A0 = np.array([v for v in range(N) if v != A0 and G[A0, v] == 0])
exp_blue = np.concatenate([[b], NQR, [q + 0], q + QR])
B0 = q
print("N_blue(A_0) as expected:", set(blue_A0.tolist()) == set(exp_blue.tolist()),
      "| B_0 red to rest of N_blue(A_0):", bool(G[B0, np.setdiff1d(exp_blue, [B0])].all()),
      "| blue graph on the rest iso to P_797 via b->0, A_x->n/x, B_y->n/y:",
      check_iso(np.concatenate([[b], NQR, q + QR]),
                np.concatenate([[0], nn * inv[NQR] % q, nn * inv[QR] % q]), 0))
print("N_red(a) = A:", set(np.flatnonzero(G[a]).tolist()) == set(range(q)),
      "| N_blue(a) = B+{b}:", set(v for v in range(N) if v != a and G[a, v] == 0) == set(range(q, 2 * q)) | {b},
      "| b red to all of B:", bool(G[b, q:2 * q].all()),
      "| blue graph on B iso to P_797 via B_x->n*x:", check_iso(q + X, nn * X % q, 0))

# --- 4. certificates (raw indices from the report, Appendix A)
C = [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595]
I = [1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267]
assert not set(C) & set(I)
redK = all(G[u, v] == 1 for i, u in enumerate(C) for v in C[i + 1:])
bluK = all(G[u, v] == 0 for i, u in enumerate(I) for v in I[i + 1:])
print("C red K10:", redK, "| I blue K10:", bluK)
mat = ["".join("R" if G[c, i] else "." for i in I) for c in C]
for p, row in enumerate(mat):
    print(f"  c{p} {row}")
beta = [{p for p in range(10) if G[C[p], I[t]] == 0} for t in range(10)]
typeA = (G[C[0], I[0]] == 1 and G[C[1], I[0]] == 1 and 2 in beta[0]
         and beta[0] <= set(range(2, 9)) and all(bt != {1} for bt in beta))
print("Type A:", typeA, "| P = beta(i0) =", sorted(beta[0]),
      "| (P1) P=={2}:", beta[0] == {2},
      "| (P2) c2 red to i_r, r>=2:", [r for r in range(2, 9) if G[C[2], I[r]] == 1])

# --- 5. graphs deciding omega/alpha of P_797 (arc-transitivity)
def dump(adj, fn):
    with open(fn, "w") as fh:
        fh.write(f"{adj.shape[0]}\n")
        for row in adj:
            fh.write("".join("1" if x else "0" for x in row) + "\n")

cn_red = [v for v in range(q) if P[0, v] and P[1, v]]
Pb = (1 - P) * (1 - np.eye(q, dtype=np.uint8))
assert not sq[2]
cn_blue = [v for v in range(q) if Pb[0, v] and Pb[2, v]]
print("common red nbhd of 0,1:", len(cn_red), "| common blue nbhd of 0,2:", len(cn_blue))
dump(P[np.ix_(cn_red, cn_red)], f"{outdir}/p797_red_cn01.txt")
dump(Pb[np.ix_(cn_blue, cn_blue)], f"{outdir}/p797_blue_cn02.txt")
np.save(f"{outdir}/O.npy", O)
for name, w, mat_ in [("red", [0, 1, 784, 788, 730, 773, 695, 643, 94], P),
                      ("blue", [0, 2, 768, 794, 760, 765, 626, 480, 478], Pb)]:
    ok = all(mat_[u, v] for i, u in enumerate(w) for v in w[i + 1:])
    print(f"report's {name} 9-clique witness in P_797 is valid:", ok)
