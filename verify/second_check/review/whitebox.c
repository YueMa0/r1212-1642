/* White-box harness: includes the reviewed source unchanged (main renamed) and
 * (a) calls expand() directly on bitset graphs with planted cliques at chosen bit positions,
 * (b) calls run_task() on random 2-coloured matrices,
 * comparing found/none with an independent ordered clique search on a byte matrix. */
#define main orig_main
#include "../../bruteforce_kclique.c"
#undef main

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* independent: does graph (byte adjacency, mm vertices) contain a clique of size s? */
static long long ind_nodes;
static int ind_search(const unsigned char *adj, int mm, const int *cand, int nc, int size, int s, int *stack) {
    ind_nodes++;
    if (size == s) return 1;
    if (size + nc < s) return 0;
    int *nc2 = malloc(sizeof(int) * (nc + 1));
    for (int i = 0; i < nc; i++) {
        if (size + (nc - i) < s) break;
        int u = cand[i], k = 0;
        for (int j = i + 1; j < nc; j++) if (adj[(size_t)u * mm + cand[j]]) nc2[k++] = cand[j];
        stack[size] = u;
        if (ind_search(adj, mm, nc2, k, size + 1, s, stack)) { free(nc2); return 1; }
    }
    free(nc2);
    return 0;
}
static int ind_has(const unsigned char *adj, int mm, int s) {
    if (s <= 0) return 1;
    int *cand = malloc(sizeof(int) * (mm + 1)), stack[128];
    for (int i = 0; i < mm; i++) cand[i] = i;
    int r = ind_search(adj, mm, cand, mm, 0, s, stack);
    free(cand);
    return r;
}
static int ind_omega(const unsigned char *adj, int mm) {
    int w = 0;
    while (w < mm && ind_has(adj, mm, w + 1)) w++;
    return w;
}

static ctx_t X;
static int fails = 0, tests = 0, found_cases = 0, none_cases = 0, mw_found = 0, mw_none = 0, maxm_none = 0;

/* (a) direct expand test */
static void test_expand(int mm, double p, int s, const int *plant, int np) {
    unsigned char *adj = calloc((size_t)mm * mm, 1);
    for (int i = 0; i < mm; i++)
        for (int j = i + 1; j < mm; j++)
            if (urand() < p) adj[i * mm + j] = adj[j * mm + i] = 1;
    for (int a = 0; a < np; a++)
        for (int b = a + 1; b < np; b++) adj[plant[a] * mm + plant[b]] = adj[plant[b] * mm + plant[a]] = 1;
    X.m = mm; X.nw = (mm + 63) / 64; if (!X.nw) X.nw = 1;
    for (int i = 0; i < mm; i++) {
        memset(X.adj[i], 0, sizeof(uint64_t) * MW);
        for (int j = 0; j < mm; j++) if (adj[i * mm + j]) X.adj[i][j >> 6] |= 1ULL << (j & 63);
    }
    X.target = s; X.found = X.aborted = 0; X.nodes = 0;
    uint64_t P[MW] = {0};
    for (int i = 0; i < mm; i++) P[i >> 6] |= 1ULL << (i & 63);
    if (mm >= s) expand(&X, P, 0);
    int truth = ind_has(adj, mm, s);
    int ok = (X.found == truth) && !X.aborted;
    if (X.found) {   /* verify witness: distinct, pairwise adjacent */
        for (int a = 0; a < s; a++) for (int b = a + 1; b < s; b++)
            if (X.wit[a] == X.wit[b] || !adj[X.wit[a] * mm + X.wit[b]]) ok = 0;
    }
    tests++; found_cases += truth; none_cases += !truth;
    if (mm > 64) { mw_found += truth; mw_none += !truth; }
    if (!truth && mm > maxm_none) maxm_none = mm;
    if (!ok) { fails++; fprintf(stderr, "EXPAND FAIL m=%d p=%.2f s=%d prog=%d truth=%d\n", mm, p, s, X.found, truth); }
    free(adj);
}

/* (b) run_task on a random coloured matrix; checks every (v,c) of a random sample */
static void test_run_task(int nn, double pr, int t) {
    n = nn; T = t;
    A = calloc((size_t)nn * nn, 1);
    for (int i = 0; i < nn; i++) for (int j = i + 1; j < nn; j++) if (urand() < pr) A[i * nn + j] = A[j * nn + i] = 1;
    out = fopen("/dev/null", "w");
    for (int v = 0; v < nn; v++) for (int c = 0; c < 2; c++) {
        /* independent P(v,c) and its colour-c graph */
        int idx[MAXN], mm = 0;
        for (int w = 0; w < nn; w++) if (w > v && A[v * nn + w] == c) idx[mm++] = w;
        if (mm > MAXM) continue;
        unsigned char *adj = calloc((size_t)mm * mm + 1, 1);
        for (int i = 0; i < mm; i++) for (int j = 0; j < mm; j++) if (i != j && A[idx[i] * nn + idx[j]] == c) adj[i * mm + j] = 1;
        int truth = ind_has(adj, mm, t - 1);
        task_t tk = {v, c, mm};
        run_task(&X, &tk);
        int ok = (X.found == truth) && !X.aborted && X.m == mm;
        if (X.found) {
            int g[64]; g[0] = v;
            for (int i = 0; i < t - 1; i++) g[i + 1] = X.glob[X.wit[i]];
            for (int a = 0; a < t; a++) for (int b = a + 1; b < t; b++)
                if (g[a] == g[b] || A[g[a] * nn + g[b]] != c) ok = 0;
            for (int a = 1; a < t; a++) if (g[a] <= v) ok = 0;
        }
        tests++; found_cases += truth; none_cases += !truth;
        if (mm > 64) { mw_found += truth; mw_none += !truth; }
        if (!truth && mm > maxm_none) maxm_none = mm;
        if (!ok) { fails++; fprintf(stderr, "RUNTASK FAIL n=%d v=%d c=%d m=%d t=%d prog=%d truth=%d\n", nn, v, c, mm, t, X.found, truth); }
        free(adj);
    }
    fclose(out); free(A);
}

int main(int argc, char **argv) {
    node_cap = 0;
    if (argc > 1) rs = strtoull(argv[1], 0, 10) | 1;
    /* (a1) planted cliques straddling word boundaries, in random background graphs */
    int sizes[] = {63, 64, 65, 127, 128, 129, 191, 192, 193, 255, 256, 257, 511, 512, 513, 700, 822, 1000, 1023, 1024};
    for (unsigned si = 0; si < sizeof sizes / sizeof *sizes; si++) {
        int mm = sizes[si];
        for (int rep = 0; rep < 6; rep++) {
            double p = mm > 300 ? 0.08 + 0.04 * (rep % 3) : 0.2 + 0.1 * (rep % 3);
            int s = 5 + rep % 4;
            int plant[64], np = 0;
            /* clique on bits around each word boundary + the last bit */
            int cands[] = {0, 62, 63, 64, 65, 126, 127, 128, 129, 255, 256, 511, 512, mm - 2, mm - 1};
            for (unsigned q = 0; q < sizeof cands / sizeof *cands && np < s; q++) {
                int b = cands[(q * 7 + rep) % (sizeof cands / sizeof *cands)];
                if (b < 0 || b >= mm) continue;
                int dup = 0; for (int z = 0; z < np; z++) dup |= plant[z] == b;
                if (!dup) plant[np++] = b;
            }
            while (np < s) { int b = (int)(rnd() % mm), dup = 0; for (int z = 0; z < np; z++) dup |= plant[z] == b; if (!dup) plant[np++] = b; }
            test_expand(mm, p, s, plant, np);          /* planted K_s: must be found */
            test_expand(mm, p, s, plant, np - 1);      /* planted K_{s-1} only: found iff background has K_s */
        }
    }
    /* (a2) unplanted random graphs, s = omega and omega+1 (computed independently) */
    for (int rep = 0; rep < 120; rep++) {
        int mm = 20 + (int)(rnd() % 380);
        double p = 0.15 + 0.4 * urand();
        if (mm > 200) p *= 0.6;
        unsigned char *adj = calloc((size_t)mm * mm, 1);
        uint64_t save = rs;
        for (int i = 0; i < mm; i++) for (int j = i + 1; j < mm; j++) if (urand() < p) adj[i * mm + j] = adj[j * mm + i] = 1;
        int w = ind_omega(adj, mm);
        free(adj);
        rs = save; test_expand(mm, p, w, NULL, 0);       /* same graph regenerated: found */
        rs = save; test_expand(mm, p, w + 1, NULL, 0);   /* same graph: none */
    }
    fprintf(stderr, "expand tests: %d run, %d failures (found=%d none=%d; multi-word found=%d none=%d; largest m with none=%d)\n", tests, fails, found_cases, none_cases, mw_found, mw_none, maxm_none);
    mw_found = mw_none = maxm_none = 0;
    /* (b) run_task over all (v,c) of random coloured matrices, multi-word P */
    int t0 = tests, f0 = fails;
    found_cases = none_cases = 0;
    for (int rep = 0; rep < 8; rep++) {
        int nn = 130 + (int)(rnd() % 220);
        double pr = 0.45 + 0.1 * urand();
        int t = 9 + rep % 4;
        test_run_task(nn, pr, t);
    }
    fprintf(stderr, "run_task tests: %d run, %d failures (found=%d none=%d; multi-word found=%d none=%d; largest m with none=%d)\n", tests - t0, fails - f0, found_cases, none_cases, mw_found, mw_none, maxm_none);
    return fails != 0;
}
