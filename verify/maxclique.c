/* Exact maximum clique (bitset branch and bound, greedy colouring bound, MCQ style).
 * Input file: first line n (<= 1024), then n lines of '0'/'1'.  Output: omega, a witness
 * (original labels), node count.  Optional 2nd arg t: only decide "clique of size >= t?". */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 1024
#define MAXW (MAXN / 64)

static int n, nw;
static uint64_t adj[MAXN][MAXW];
static int best, bestset[MAXN], cur[MAXN], label[MAXN];
static long long nodes;

static int lowest(const uint64_t *s) {
    for (int i = 0; i < nw; i++)
        if (s[i]) return i * 64 + __builtin_ctzll(s[i]);
    return -1;
}

static void expand(uint64_t *P, int depth) {
    int order[MAXN], col[MAXN], cnt = 0, k = 0;
    uint64_t U[MAXW], Q[MAXW], NP[MAXW];
    nodes++;
    memcpy(U, P, sizeof(uint64_t) * nw);
    while (lowest(U) >= 0) {
        k++;
        memcpy(Q, U, sizeof(uint64_t) * nw);
        int v;
        while ((v = lowest(Q)) >= 0) {
            Q[v >> 6] &= ~(1ULL << (v & 63));
            U[v >> 6] &= ~(1ULL << (v & 63));
            for (int i = 0; i < nw; i++) Q[i] &= ~adj[v][i];
            order[cnt] = v;
            col[cnt++] = k;
        }
    }
    for (int i = cnt - 1; i >= 0; i--) {
        if (depth + col[i] <= best) return;
        int v = order[i];
        cur[depth] = v;
        int any = 0;
        for (int j = 0; j < nw; j++) any |= (NP[j] = P[j] & adj[v][j]) != 0;
        if (!any) {
            if (depth + 1 > best) {
                best = depth + 1;
                memcpy(bestset, cur, sizeof(int) * best);
            }
        } else {
            expand(NP, depth + 1);
        }
        P[v >> 6] &= ~(1ULL << (v & 63));
    }
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d", &n) != 1 || n > MAXN) { fprintf(stderr, "bad input\n"); return 2; }
    nw = (n + 63) / 64;
    static char row[MAXN + 2];
    static char a[MAXN][MAXN];
    for (int i = 0; i < n; i++) {
        if (fscanf(f, "%1025s", row) != 1 || (int)strlen(row) != n) { fprintf(stderr, "bad row\n"); return 2; }
        for (int j = 0; j < n; j++) a[i][j] = row[j] == '1';
    }
    fclose(f);
    for (int i = 0; i < n; i++) {
        if (a[i][i]) { fprintf(stderr, "loop\n"); return 2; }
        for (int j = 0; j < n; j++)
            if (a[i][j] != a[j][i]) { fprintf(stderr, "asym\n"); return 2; }
    }
    /* renumber by degree, descending (initial MCQ order; colouring takes lowest index first) */
    int deg[MAXN];
    for (int i = 0; i < n; i++) {
        deg[i] = 0;
        for (int j = 0; j < n; j++) deg[i] += a[i][j];
        label[i] = i;
    }
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (deg[label[j]] > deg[label[i]]) { int t = label[i]; label[i] = label[j]; label[j] = t; }
    memset(adj, 0, sizeof adj);
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            if (a[label[i]][label[j]]) adj[i][j >> 6] |= 1ULL << (j & 63);
    int target = argc > 2 ? atoi(argv[2]) : 0;
    best = target > 0 ? target - 1 : 0;
    uint64_t P[MAXW] = {0};
    for (int i = 0; i < n; i++) P[i >> 6] |= 1ULL << (i & 63);
    if (n > 0) expand(P, 0);
    int found = target > 0 ? best >= target : 1;
    if (target > 0) printf("target %d: %s\n", target, found ? "FOUND" : "none");
    if (found) {
        /* re-check witness against the input matrix */
        for (int i = 0; i < best; i++)
            for (int j = i + 1; j < best; j++)
                if (!a[label[bestset[i]]][label[bestset[j]]]) { printf("WITNESS INVALID\n"); return 3; }
        printf("omega %d witness", best);
        for (int i = 0; i < best; i++) printf(" %d", label[bestset[i]]);
        printf("\n");
    } else {
        printf("omega <= %d\n", target - 1);
    }
    printf("nodes %lld\n", nodes);
    return 0;
}
