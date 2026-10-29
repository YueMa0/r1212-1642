/* Independent re-check (reviewer-written, shares no code with the reviewed program).
 * usage: indep_kclique GRAPH t v_lo v_hi [cmax]
 * For every v in [v_lo,v_hi) and c in {0,1}: does {w>v : col(v,w)=c} contain a colour-c clique of
 * size t-1?  Plain ordered enumeration (each clique visited in increasing vertex order) with only
 * the bound |clique| + |candidates| < t-1; 32-bit words; vertices kept in natural order.
 * Prints one line per task: v c m result nodes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n;
static unsigned char *A;
static int s_target, W;
static uint32_t *nb;     /* m rows x W words */
static long long nodes;
static int stack_[64];

static int pc(const uint32_t *x) { int k = 0; for (int i = 0; i < W; i++) k += __builtin_popcount(x[i]); return k; }

static int rec(uint32_t *cand, int size) {
    nodes++;
    if (size == s_target) return 1;
    uint32_t nc[64];
    for (;;) {
        int left = pc(cand);
        if (left == 0 || size + left < s_target) return 0;
        int u = -1;
        for (int i = 0; i < W; i++) if (cand[i]) { u = i * 32 + __builtin_ctz(cand[i]); break; }
        cand[u / 32] &= ~(1u << (u % 32));
        for (int i = 0; i < W; i++) nc[i] = cand[i] & nb[(size_t)u * W + i];
        stack_[size] = u;
        if (rec(nc, size + 1)) return 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage\n"); return 2; }
    int t = atoi(argv[2]), vlo = atoi(argv[3]), vhi = atoi(argv[4]);
    FILE *f = fopen(argv[1], "rb");
    fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
    char *buf = malloc(sz + 1); fread(buf, 1, sz, f); buf[sz] = 0; fclose(f);
    /* count lines, require all lines equal length n and n lines, chars only 0/1 */
    int lines = 0; long pos = 0; int len0 = -1;
    while (pos < sz) {
        long e = pos; while (e < sz && buf[e] != '\n') e++;
        int L = (int)(e - pos);
        if (len0 < 0) len0 = L;
        if (L != len0) { fprintf(stderr, "bad line length at %d\n", lines); return 2; }
        for (long k = pos; k < e; k++) if (buf[k] != '0' && buf[k] != '1') { fprintf(stderr, "bad char\n"); return 2; }
        lines++; pos = e + 1;
    }
    if (lines != len0) { fprintf(stderr, "not square %d x %d\n", lines, len0); return 2; }
    n = lines;
    A = malloc((size_t)n * n);
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) A[(size_t)i * n + j] = buf[(size_t)i * (n + 1) + j] - '0';
    for (int i = 0; i < n; i++) { if (A[(size_t)i * n + i]) return 3; for (int j = 0; j < n; j++) if (A[(size_t)i * n + j] != A[(size_t)j * n + i]) return 4; }
    s_target = t - 1;
    int *P = malloc(sizeof(int) * n);
    if (vhi > n) vhi = n;
    for (int v = vlo; v < vhi; v++)
        for (int c = 0; c < 2; c++) {
            int m = 0;
            for (int w = v + 1; w < n; w++) if (A[(size_t)v * n + w] == c) P[m++] = w;
            W = (m + 31) / 32; if (W == 0) W = 1;
            if (W > 64) return 5;
            nb = calloc((size_t)m * W + 1, sizeof(uint32_t));
            for (int i = 0; i < m; i++) for (int j = 0; j < m; j++)
                if (i != j && A[(size_t)P[i] * n + P[j]] == c) nb[(size_t)i * W + j / 32] |= 1u << (j % 32);
            uint32_t cand[64] = {0};
            for (int i = 0; i < m; i++) cand[i / 32] |= 1u << (i % 32);
            nodes = 0;
            int found = rec(cand, 0);
            printf("%d %d %d %s %lld", v, c, m, found ? "found" : "none", nodes);
            if (found) {   /* print and self-verify witness in original labels */
                int ok = 1;
                for (int a = 0; a < s_target; a++) for (int b = a + 1; b < s_target; b++)
                    if (A[(size_t)P[stack_[a]] * n + P[stack_[b]]] != c) ok = 0;
                printf(" ok=%d [%d", ok, v);
                for (int a = 0; a < s_target; a++) printf(",%d", P[stack_[a]]);
                printf("]");
            }
            printf("\n");
            free(nb);
        }
    return 0;
}
