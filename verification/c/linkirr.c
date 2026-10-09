/* linkirr.c -- checks for "Link-irregular tournaments exist for every order at least six".
 *
 *   linkirr count n    (2 <= n <= 7) every tournament on n vertices: how many are link-irregular
 *                      (labelled), how many up to isomorphism, and whether any has a source or a
 *                      sink.  Links are compared through a table of canonical codes of all
 *                      tournaments on n - 1 vertices (minimum code over all relabellings).
 *   linkirr build N    the tournaments T_6, T_7 of the paper and T_{n+2} = T_n^+ for n + 2 <= N:
 *                      checks that each is a tournament with neither a source nor a sink and that
 *                      its n links are pairwise non-isomorphic (backtracking with score refinement).
 *   linkirr table      the scores of T_6, T_7 and the score sequences of their links (Table 1).
 *
 * Exit status 0 means every claim checked here holds; the last line is "ALL OK".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int failed = 0;
#define CHECK(c, ...) do { if (c) printf("ok   "); else { printf("FAIL "); failed = 1; } \
                           printf(__VA_ARGS__); printf("\n"); } while (0)

#define MAXV 128
typedef struct { int n; unsigned char a[MAXV][MAXV]; } Tour;   /* a[i][j] = 1 iff i -> j */

static int score(const Tour *t, int v) { int s = 0; for (int w = 0; w < t->n; w++) s += t->a[v][w]; return s; }

static int is_tournament(const Tour *t) {
    for (int i = 0; i < t->n; i++) {
        if (t->a[i][i]) return 0;
        for (int j = i + 1; j < t->n; j++) if (t->a[i][j] + t->a[j][i] != 1) return 0;
    }
    return 1;
}

static void link_of(const Tour *t, int v, Tour *l) {
    int k = 0, idx[MAXV];
    for (int u = 0; u < t->n; u++) if (u != v) idx[k++] = u;
    l->n = k;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) l->a[i][j] = t->a[idx[i]][idx[j]];
}

/* ---------- isomorphism test: colour refinement and backtracking ---------- */
static int colA[MAXV], colB[MAXV], mapAB[MAXV], usedB[MAXV];

static void refine(const Tour *t, int *col) {
    /* start from scores; replace each colour by (colour, sorted out-neighbour colours), n rounds */
    int n = t->n;
    for (int v = 0; v < n; v++) col[v] = score(t, v);
    for (int round = 0; round < n; round++) {
        /* signature: colour, then counts of out-neighbours of each colour (colours < n) */
        static long sig[MAXV][MAXV + 1];
        for (int v = 0; v < n; v++) {
            for (int c = 0; c <= n; c++) sig[v][c] = 0;
            sig[v][0] = col[v];
            for (int w = 0; w < n; w++) if (t->a[v][w]) sig[v][1 + col[w]]++;
        }
        /* rank signatures; the rank is the new colour */
        int newc[MAXV];
        for (int v = 0; v < n; v++) {
            int r = 0;
            for (int w = 0; w < n; w++) if (memcmp(sig[w], sig[v], sizeof(long) * (n + 1)) < 0) r++;
            newc[v] = r;
        }
        int same = 1;
        for (int v = 0; v < n; v++) if (newc[v] != col[v]) same = 0;
        memcpy(col, newc, sizeof(int) * n);
        if (same) break;
    }
}

static int extend(const Tour *A, const Tour *B, int i) {
    int n = A->n;
    if (i == n) return 1;
    for (int b = 0; b < n; b++) {
        if (usedB[b] || colB[b] != colA[i]) continue;
        int ok = 1;
        for (int j = 0; j < i && ok; j++)
            if (A->a[i][j] != B->a[b][mapAB[j]] || A->a[j][i] != B->a[mapAB[j]][b]) ok = 0;
        if (!ok) continue;
        usedB[b] = 1; mapAB[i] = b;
        if (extend(A, B, i + 1)) { usedB[b] = 0; return 1; }
        usedB[b] = 0;
    }
    return 0;
}

/* the refinement is computed separately on A and B, so the colours must be compared as
   multisets of signatures; we refine the disjoint union instead, which gives comparable colours */
static int isomorphic(const Tour *A, const Tour *B) {
    if (A->n != B->n) return 0;
    int n = A->n;
    static Tour U;
    U.n = 2 * n;
    memset(U.a, 0, sizeof U.a);
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { U.a[i][j] = A->a[i][j]; U.a[n + i][n + j] = B->a[i][j]; }
    static int col[2 * MAXV];
    refine(&U, col);
    int cntA[2 * MAXV] = {0}, cntB[2 * MAXV] = {0};
    for (int i = 0; i < n; i++) { colA[i] = col[i]; colB[i] = col[n + i]; cntA[colA[i]]++; cntB[colB[i]]++; }
    for (int c = 0; c < 2 * n; c++) if (cntA[c] != cntB[c]) return 0;
    memset(usedB, 0, sizeof usedB);
    return extend(A, B, 0);
}

static int link_irregular(const Tour *t) {
    static Tour L[MAXV];
    for (int v = 0; v < t->n; v++) link_of(t, v, &L[v]);
    for (int v = 0; v < t->n; v++)
        for (int w = v + 1; w < t->n; w++)
            if (isomorphic(&L[v], &L[w])) return 0;
    return 1;
}

static int no_source_sink(const Tour *t) {
    for (int v = 0; v < t->n; v++) { int s = score(t, v); if (s == 0 || s == t->n - 1) return 0; }
    return 1;
}

static void from_arcs(Tour *t, int n, const int arcs[][2], int m) {
    t->n = n;
    memset(t->a, 0, sizeof t->a);
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i < j) t->a[j][i] = 1;  /* default: j -> i */
    for (int k = 0; k < m; k++) { int i = arcs[k][0], j = arcs[k][1]; t->a[i][j] = 1; t->a[j][i] = 0; }
}

static const int ARCS6[][2] = {{0,1},{0,2},{0,3},{0,4},{1,2},{1,3},{1,4},{1,5},{2,3},{2,5},{3,4},{3,5},{4,2},{5,0},{5,4}};
static const int ARCS7[][2] = {{0,1},{0,2},{0,3},{0,4},{0,5},{1,2},{1,3},{1,4},{1,5},{1,6},{2,3},{2,4},{2,6},
                               {3,4},{3,5},{3,6},{4,5},{5,2},{6,0},{6,4},{6,5}};

/* T^+: s = n beats all old vertices, all old vertices beat t = n + 1, t -> s */
static void plus(const Tour *t, Tour *p) {
    int n = t->n;
    p->n = n + 2;
    memset(p->a, 0, sizeof p->a);
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) p->a[i][j] = t->a[i][j];
    for (int v = 0; v < n; v++) { p->a[n][v] = 1; p->a[v][n + 1] = 1; }
    p->a[n + 1][n] = 1;
}

/* ---------- exhaustive counts through canonical codes ---------- */
static int npairs(int n) { return n * (n - 1) / 2; }

/* code of a tournament on m vertices: bit k of pair (i,j), i < j, lexicographic, set iff i -> j */
static uint32_t code_of(const Tour *t) {
    uint32_t c = 0; int k = 0;
    for (int i = 0; i < t->n; i++) for (int j = i + 1; j < t->n; j++, k++) if (t->a[i][j]) c |= 1u << k;
    return c;
}
static void decode(uint32_t c, int m, Tour *t) {
    t->n = m; int k = 0;
    for (int i = 0; i < m; i++) { t->a[i][i] = 0; for (int j = i + 1; j < m; j++, k++) { int b = (c >> k) & 1; t->a[i][j] = b; t->a[j][i] = !b; } }
}

static int perm[8], nperm;
static int allp[5040][8];
static void genperms(int m, int k, int *used) {
    if (k == m) { memcpy(allp[nperm++], perm, sizeof(int) * m); return; }
    for (int x = 0; x < m; x++) if (!used[x]) { used[x] = 1; perm[k] = x; genperms(m, k + 1, used); used[x] = 0; }
}

static uint32_t *canon;   /* canonical code of each tournament on m vertices */
static void build_canon(int m) {
    int used[8] = {0}; nperm = 0; genperms(m, 0, used);
    uint32_t N = 1u << npairs(m);
    canon = malloc(sizeof(uint32_t) * N);
    Tour t, u;
    for (uint32_t c = 0; c < N; c++) {
        decode(c, m, &t);
        uint32_t best = UINT32_MAX;
        for (int p = 0; p < nperm; p++) {
            u.n = m;
            for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) u.a[allp[p][i]][allp[p][j]] = t.a[i][j];
            uint32_t cc = code_of(&u);
            if (cc < best) best = cc;
        }
        canon[c] = best;
    }
}

static void count(int n) {
    long labelled = 0, withss = 0, plusok = 0;
    int m = n - 1;
    build_canon(m);
    uint32_t N = 1u << npairs(n);
    Tour t, l;
    long fact = 1; for (int i = 2; i <= n; i++) fact *= i;
    for (uint32_t c = 0; c < N; c++) {
        decode(c, n, &t);
        uint32_t cl[8];
        int ok = 1;
        for (int v = 0; v < n && ok; v++) {
            link_of(&t, v, &l);
            cl[v] = canon[code_of(&l)];
            for (int w = 0; w < v; w++) if (cl[w] == cl[v]) { ok = 0; break; }
        }
        if (ok) {
            labelled++;
            if (!no_source_sink(&t)) {
                withss++;
                Tour p; plus(&t, &p);
                if (link_irregular(&p)) plusok++;
            }
        }
    }
    free(canon);
    /* a link-irregular tournament has no nontrivial automorphism (an automorphism maps each link
       onto an isomorphic link), so each isomorphism class has exactly n! labellings */
    printf("n=%d: %ld labelled link-irregular tournaments, %ld up to isomorphism (labelled/n! = %ld/%ld), "
           "%ld with a source or a sink\n", n, labelled, labelled / fact, labelled, fact, withss);
    CHECK(labelled % fact == 0, "n=%d: the count is a multiple of n!", n);
    if (n <= 5) CHECK(labelled == 0, "n=%d: no link-irregular tournament", n);
    if (withss) printf("     of the %ld with a source or a sink, %ld give a link-irregular T^+\n", withss, plusok);
    if (n == 6) CHECK(labelled / fact == 4 && withss == 0,
                      "n=6: four link-irregular tournaments up to isomorphism, none with a source or a sink");
}

static void build(int N) {
    static Tour T[MAXV];
    from_arcs(&T[6], 6, ARCS6, 15);
    from_arcs(&T[7], 7, ARCS7, 21);
    for (int n = 8; n <= N; n++) plus(&T[n - 2], &T[n]);
    int all = 1;
    for (int n = 6; n <= N; n++) {
        int ok = is_tournament(&T[n]) && no_source_sink(&T[n]) && link_irregular(&T[n]);
        if (!ok) { all = 0; printf("FAIL T_%d\n", n); }
    }
    CHECK(all, "T_n is a link-irregular tournament with neither a source nor a sink for 6 <= n <= %d", N);
}

static void sorted_scores(const Tour *t, int *out) {
    for (int v = 0; v < t->n; v++) out[v] = score(t, v);
    for (int i = 1; i < t->n; i++) for (int j = i; j > 0 && out[j - 1] > out[j]; j--) { int x = out[j]; out[j] = out[j - 1]; out[j - 1] = x; }
}

static void table(void) {
    Tour T6, T7, l;
    from_arcs(&T6, 6, ARCS6, 15);
    from_arcs(&T7, 7, ARCS7, 21);
    CHECK(is_tournament(&T6) && is_tournament(&T7), "T_6 and T_7 are tournaments");
    int s6[] = {4, 4, 2, 2, 1, 2}, s7[] = {5, 5, 3, 3, 1, 1, 3}, ok = 1;
    for (int v = 0; v < 6; v++) ok &= score(&T6, v) == s6[v];
    for (int v = 0; v < 7; v++) ok &= score(&T7, v) == s7[v];
    CHECK(ok, "scores 4,4,2,2,1,2 and 5,5,3,3,1,1,3");
    static const int want6[6][5] = {{1,1,2,2,4},{1,2,2,2,3},{0,2,2,3,3},{1,1,2,3,3},{1,1,2,3,3},{1,1,1,3,4}};
    static const int want7[7][6] = {{1,1,2,3,3,5},{1,1,3,3,3,4},{0,1,3,3,4,4},{1,1,2,3,4,4},{1,2,2,2,4,4},
                                    {0,2,2,3,4,4},{1,1,2,2,4,5}};
    int seq[8]; ok = 1;
    for (int v = 0; v < 6; v++) { link_of(&T6, v, &l); sorted_scores(&l, seq); ok &= !memcmp(seq, want6[v], sizeof want6[v]); }
    for (int v = 0; v < 7; v++) { link_of(&T7, v, &l); sorted_scores(&l, seq); ok &= !memcmp(seq, want7[v], sizeof want7[v]); }
    CHECK(ok, "the score sequences of the links agree with Table 1");
    /* T_6 - 4 and T_6 - 5 (paper's labels): the vertex of score 2 and its out-neighbours */
    Tour a, b; link_of(&T6, 3, &a); link_of(&T6, 4, &b);
    CHECK(!isomorphic(&a, &b), "T_6 - 4 and T_6 - 5 are not isomorphic");
}

int main(int argc, char **argv) {
    if (argc >= 3 && !strcmp(argv[1], "count")) count(atoi(argv[2]));
    else if (argc >= 3 && !strcmp(argv[1], "build")) build(atoi(argv[2]));
    else if (argc >= 2 && !strcmp(argv[1], "table")) table();
    else { fprintf(stderr, "usage: linkirr count n | build N | table\n"); return 2; }
    printf(failed ? "SOME CHECKS FAILED\n" : "ALL OK\n");
    return failed;
}
