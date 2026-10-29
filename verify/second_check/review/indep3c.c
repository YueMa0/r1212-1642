/* Second independent re-check, reviewer-written: colour-bound search written from scratch.
 * usage: indep2 GRAPH t v_lo v_hi
 * Differences from the reviewed program: 32-bit words, vertices in natural (index) order, candidate
 * colouring done by explicit class lists, branching loop over a materialised vertex list, and the
 * popcount bound in addition to the colour bound.  Prints: v c m result nodes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXW 64            /* up to 2048 vertices in P */
static int n, S, W;
static unsigned char *A;
static uint32_t *nb;
static long long nodes;
static int found_stack[64];

static int popc(const uint32_t *x) { int k = 0; for (int i = 0; i < W; i++) k += __builtin_popcount(x[i]); return k; }

/* returns 1 iff cand contains a clique of size S-size */
static int go(const uint32_t *cand0, int size) {
    nodes++;
    int need = S - size;
    if (need <= 0) return 1;
    uint32_t cand[MAXW], rest[MAXW], cls[MAXW], nc[MAXW];
    memcpy(cand, cand0, sizeof(uint32_t) * W);
    int k = popc(cand);
    if (k < need) return 0;
    /* greedy colouring: vert[] lists vertices class by class, colr[] their class number (1-based) */
    int vert[2048], colr[2048], cnt = 0, ncol = 0;
    memcpy(rest, cand, sizeof(uint32_t) * W);
    while (cnt < k) {
        ncol++;
        memcpy(cls, rest, sizeof(uint32_t) * W);       /* vertices still allowed in this class */
        for (int wi = 0; wi < W; wi++) {
            while (cls[wi]) {
                int b = __builtin_ctz(cls[wi]);
                int u = wi * 32 + b;
                cls[wi] &= ~(1u << b);
                rest[wi] &= ~(1u << b);
                for (int j = 0; j < W; j++) cls[j] &= ~nb[(size_t)u * W + j];   /* drop neighbours of u */
                vert[cnt] = u; colr[cnt] = ncol; cnt++;
            }
        }
    }
    if (ncol < need) return 0;
    /* branch from the highest class down; vertices already branched on are removed from cand */
    for (int i = cnt - 1; i >= 0; i--) {
        if (colr[i] < need) return 0;      /* cand now = vert[0..i], all of colour <= colr[i] */
        int u = vert[i];
        found_stack[size] = u;
        if (need == 1) return 1;
        int nonempty = 0;
        for (int j = 0; j < W; j++) { nc[j] = cand[j] & nb[(size_t)u * W + j]; nonempty |= nc[j] != 0; }
        if (nonempty && go(nc, size + 1)) return 1;
        cand[u / 32] &= ~(1u << (u % 32));
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    int t = atoi(argv[2]), vlo = atoi(argv[3]), vhi = atoi(argv[4]);
    FILE *f = fopen(argv[1], "rb");
    fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
    char *buf = malloc(sz + 1); if (fread(buf, 1, sz, f) != (size_t)sz) return 2; fclose(f);
    long nl = 0; for (long i = 0; i < sz; i++) nl += buf[i] == '\n';
    n = (int)nl;
    if ((long)n * (n + 1) != sz) { fprintf(stderr, "size mismatch\n"); return 2; }
    A = malloc((size_t)n * n);
    for (int i = 0; i < n; i++) {
        if (buf[(size_t)i * (n + 1) + n] != '\n') return 2;
        for (int j = 0; j < n; j++) {
            char ch = buf[(size_t)i * (n + 1) + j];
            if (ch != '0' && ch != '1') return 2;
            A[(size_t)i * n + j] = (unsigned char)(ch - '0');
        }
    }
    for (int i = 0; i < n; i++) { if (A[(size_t)i * n + i]) return 3; for (int j = 0; j < i; j++) if (A[(size_t)i * n + j] != A[(size_t)j * n + i]) return 4; }
    S = t - 1;
    if (vhi > n) vhi = n;
    int *P = malloc(sizeof(int) * n);
    for (int v = vlo; v < vhi; v++)
        for (int c = 0; c <= 1; c++) { if (argc > 5 && c != atoi(argv[5])) continue;
            int m = 0;
            for (int w = v + 1; w < n; w++) if (A[(size_t)v * n + w] == c) P[m++] = w;
            {   int *dg = malloc(sizeof(int) * (m + 1)), *tmp = malloc(sizeof(int) * (m + 1));
                for (int i = 0; i < m; i++) { dg[i] = 0; for (int j = 0; j < m; j++) if (j != i && A[(size_t)P[i] * n + P[j]] == c) dg[i]++; }
                /* stable merge-free selection: bucket by degree from high to low */
                int maxd = 0; for (int i = 0; i < m; i++) if (dg[i] > maxd) maxd = dg[i];
                int q = 0;
                for (int d = maxd; d >= 0; d--) for (int i = 0; i < m; i++) if (dg[i] == d) tmp[q++] = P[i];
                memcpy(P, tmp, sizeof(int) * m); free(dg); free(tmp);
            }
            W = (m + 31) / 32; if (!W) W = 1;
            if (W > MAXW) return 5;
            nb = calloc((size_t)(m + 1) * W, sizeof(uint32_t));
            for (int i = 0; i < m; i++)
                for (int j = 0; j < m; j++)
                    if (j != i && A[(size_t)P[i] * n + P[j]] == c) nb[(size_t)i * W + (j >> 5)] |= 1u << (j & 31);
            uint32_t all[MAXW] = {0};
            for (int i = 0; i < m; i++) all[i >> 5] |= 1u << (i & 31);
            nodes = 0;
            int r = (m >= S) ? go(all, 0) : 0;
            printf("%d %d %d %s %lld", v, c, m, r ? "found" : "none", nodes);
            if (r) {
                int ok = 1;
                for (int a = 0; a < S; a++) for (int b = a + 1; b < S; b++)
                    if (A[(size_t)P[found_stack[a]] * n + P[found_stack[b]]] != c || found_stack[a] == found_stack[b]) ok = 0;
                printf(" ok=%d", ok);
            }
            printf("\n");
            fflush(stdout);
            free(nb);
        }
    return 0;
}
