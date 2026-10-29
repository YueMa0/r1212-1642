"""Python mirror of RamseyIncrement.R1212.Search (same bit order and fuel), used to
count nodes and to list the top-level branch arguments."""
import sys

q = 797
sq = {x * x % q for x in range(1, q)}
adj = lambda u, v: (u - v) % q in sq


def h01(colour):
    """common red (colour=1) neighbourhood of 0,1 or common blue (colour=0) of 0,2"""
    if colour == 1:
        return [v for v in range(q) if adj(0, v) and adj(1, v)]
    return [v for v in range(q) if v not in (0, 2) and not adj(0, v) and not adj(2, v)]


def rows_for(vs, colour):
    rs = []
    for i, u in enumerate(vs):
        r = 0
        for j, w in enumerate(vs):
            if i != j and (adj(u, w) if colour == 1 else not adj(u, w)):
                r |= 1 << j
        rs.append(r)
    return rs


def make(rows):
    def log2(n): return n.bit_length() - 1

    def greedy(f, Q, S):
        while f > 0 and Q != 0:
            v = log2(Q)
            Q = Q ^ (Q & (rows[v] | (1 << v)))
            S = S | (1 << v)
            f -= 1
        return S

    def colour_union(c, U, L):
        for _ in range(c):
            S = greedy(256, U, 0)
            U, L = U ^ S, L | S
        return L

    stats = {"nodes": 0}

    def no_clique(t, P):
        stats["nodes"] += 1
        if t == 0:
            return False
        tt = t - 1
        if P == 0:
            return True
        L = colour_union(tt, P, 0)
        B = P ^ (P & L)
        if B == 0:
            return True
        R, f = P, 256
        while True:
            if f == 0:
                return False
            if B == 0:
                return True
            v = log2(B)
            if not no_clique(tt, R & rows[v]):
                return False
            R = R ^ (R & (1 << v))
            B = B ^ (1 << v)
            f -= 1

    def branches(t, P):
        tt = t - 1
        L = colour_union(tt, P, 0)
        B = P ^ (P & L)
        out, R = [], P
        while B:
            v = log2(B)
            out.append(R & rows[v])
            R = R ^ (R & (1 << v))
            B = B ^ (1 << v)
        return L, B, out

    return no_clique, branches, stats


if __name__ == "__main__":
    for colour in (1, 0):
        vs = h01(colour)
        rows = rows_for(vs, colour)
        no_clique, branches, stats = make(rows)
        full = (1 << len(vs)) - 1
        r8 = no_clique(8, full)
        n8 = stats["nodes"]
        stats["nodes"] = 0
        r7 = no_clique(7, full)
        L, B, br = branches(8, full)
        per = []
        for x in br:
            stats["nodes"] = 0
            assert no_clique(7, x)
            per.append(stats["nodes"])
        print(f"colour {colour}: |H|={len(vs)} noClique8={r8} (nodes {n8}) noClique7={r7}; "
              f"top branches {len(br)}; nodes per branch max {max(per)} sum {sum(per)}; "
              f"branch sizes max {max(bin(x).count('1') for x in br)}")
