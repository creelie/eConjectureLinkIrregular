// linkirr.cpp -- an independent check of the computational facts in
// "Link-irregular tournaments exist for every order at least six".
//
// Isomorphism classes are told apart here by canonical forms: colour refinement (score, then
// the multiset of out-neighbour colours, repeated), then the lexicographically least adjacency
// string over all orderings that respect the colour classes.  This is a different algorithm from
// the pairwise backtracking and the code tables of the C program.
//
//   linkirr_cpp            1. for n = 2..6, every tournament on n vertices, links compared by
//                             trying all bijections (std::next_permutation);
//                          2. T_n for 6 <= n <= 36 (T_6, T_7 and T_{n+2} = T_n^+): tournament,
//                             no source, no sink, n pairwise different canonical link forms;
//                          3. in every link T_n - v (v old, n <= 36) the paper's marked vertex
//                             (score 1, out-neighbour of score n - 3) is unique and is t.
#include <algorithm>
#include <functional>
#include <cstdio>
#include <map>
#include <set>
#include <string>
#include <vector>

using Mat = std::vector<std::vector<int>>;
static bool failed = false;
static void check(bool c, const std::string &m) {
    std::printf("%s %s\n", c ? "ok  " : "FAIL", m.c_str());
    if (!c) failed = true;
}

static int score(const Mat &a, int v) { int s = 0; for (int x : a[v]) s += x; return s; }

static Mat linkOf(const Mat &a, int v) {
    std::vector<int> idx;
    for (int u = 0; u < (int)a.size(); u++) if (u != v) idx.push_back(u);
    Mat l(idx.size(), std::vector<int>(idx.size()));
    for (size_t i = 0; i < idx.size(); i++) for (size_t j = 0; j < idx.size(); j++) l[i][j] = a[idx[i]][idx[j]];
    return l;
}

static std::vector<int> refine(const Mat &a) {
    int n = a.size();
    std::vector<int> col(n);
    for (int v = 0; v < n; v++) col[v] = score(a, v);
    for (int round = 0; round <= n; round++) {
        std::map<std::vector<int>, int> ids;
        std::vector<std::vector<int>> sig(n);
        for (int v = 0; v < n; v++) {
            std::vector<int> out;
            for (int w = 0; w < n; w++) if (a[v][w]) out.push_back(col[w]);
            std::sort(out.begin(), out.end());
            sig[v] = {col[v]};
            sig[v].insert(sig[v].end(), out.begin(), out.end());
            ids[sig[v]] = 0;
        }
        int k = 0;
        for (auto &p : ids) p.second = k++;          // ordered by signature, so canonical
        std::vector<int> nc(n);
        for (int v = 0; v < n; v++) nc[v] = ids[sig[v]];
        bool same = true;                            // the partition is stable when the class count stops growing
        std::set<int> a1(col.begin(), col.end()), a2(nc.begin(), nc.end());
        if (a2.size() != a1.size()) same = false;
        col = nc;
        if (same && round > 0) break;
    }
    return col;
}

// least adjacency string over the orderings that list the colour classes in increasing order
static std::string canon(const Mat &a) {
    int n = a.size();
    std::vector<int> col = refine(a);
    std::vector<int> order(n);
    for (int i = 0; i < n; i++) order[i] = i;
    std::sort(order.begin(), order.end(), [&](int x, int y) { return col[x] < col[y] || (col[x] == col[y] && x < y); });
    // classes as consecutive blocks; permute within blocks
    std::vector<std::pair<int, int>> blocks;
    for (int i = 0; i < n;) { int j = i; while (j < n && col[order[j]] == col[order[i]]) j++; blocks.push_back({i, j}); i = j; }
    std::string best;
    std::vector<int> sortedCol = col;
    std::sort(sortedCol.begin(), sortedCol.end());
    std::string head;
    for (int c : sortedCol) head += std::to_string(c) + ",";
    std::function<void(size_t)> rec = [&](size_t b) {
        if (b == blocks.size()) {
            std::string s;
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) s += char('0' + a[order[i]][order[j]]);
            if (best.empty() || s < best) best = s;
            return;
        }
        auto [lo, hi] = blocks[b];
        std::sort(order.begin() + lo, order.begin() + hi);
        do rec(b + 1); while (std::next_permutation(order.begin() + lo, order.begin() + hi));
    };
    rec(0);
    return head + "|" + best;
}

static Mat fromArcs(int n, const std::vector<std::pair<int, int>> &arcs) {
    Mat a(n, std::vector<int>(n, 0));
    for (int i = 0; i < n; i++) for (int j = 0; j < i; j++) a[i][j] = 1;
    for (auto [i, j] : arcs) { a[i][j] = 1; a[j][i] = 0; }
    return a;
}

static Mat plusOf(const Mat &a) {
    int n = a.size();
    Mat p(n + 2, std::vector<int>(n + 2, 0));
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) p[i][j] = a[i][j];
    for (int v = 0; v < n; v++) { p[n][v] = 1; p[v][n + 1] = 1; }
    p[n + 1][n] = 1;
    return p;
}

static bool isTournament(const Mat &a) {
    int n = a.size();
    for (int i = 0; i < n; i++) { if (a[i][i]) return false; for (int j = i + 1; j < n; j++) if (a[i][j] + a[j][i] != 1) return false; }
    return true;
}

static bool isoBrute(const Mat &x, const Mat &y) {
    int m = x.size();
    std::vector<int> p(m);
    for (int i = 0; i < m; i++) p[i] = i;
    do {
        bool ok = true;
        for (int i = 0; i < m && ok; i++) for (int j = 0; j < m; j++) if (x[i][j] != y[p[i]][p[j]]) { ok = false; break; }
        if (ok) return true;
    } while (std::next_permutation(p.begin(), p.end()));
    return false;
}

int main() {
    // 1. exhaustive, n <= 6
    for (int n = 2; n <= 6; n++) {
        int pairs = n * (n - 1) / 2;
        long cnt = 0;
        for (long c = 0; c < (1L << pairs); c++) {
            Mat a(n, std::vector<int>(n, 0));
            int k = 0;
            for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++, k++) { if ((c >> k) & 1) a[i][j] = 1; else a[j][i] = 1; }
            std::vector<Mat> L;
            for (int v = 0; v < n; v++) L.push_back(linkOf(a, v));
            bool irr = true;
            for (int v = 0; v < n && irr; v++) for (int w = v + 1; w < n; w++) if (isoBrute(L[v], L[w])) { irr = false; break; }
            if (irr) cnt++;
        }
        long fact = 1; for (int i = 2; i <= n; i++) fact *= i;
        std::printf("     n=%d: %ld labelled link-irregular tournaments (%ld up to isomorphism)\n", n, cnt, cnt / fact);
        if (n <= 5) check(cnt == 0, "n=" + std::to_string(n) + ": none");
        else check(cnt == 2880, "n=6: 2880 labelled, 4 up to isomorphism");
    }
    // 2. T_n
    std::vector<Mat> T(37);
    T[6] = fromArcs(6, {{0,1},{0,2},{0,3},{0,4},{1,2},{1,3},{1,4},{1,5},{2,3},{2,5},{3,4},{3,5},{4,2},{5,0},{5,4}});
    T[7] = fromArcs(7, {{0,1},{0,2},{0,3},{0,4},{0,5},{1,2},{1,3},{1,4},{1,5},{1,6},{2,3},{2,4},{2,6},
                        {3,4},{3,5},{3,6},{4,5},{5,2},{6,0},{6,4},{6,5}});
    for (int n = 8; n <= 36; n++) T[n] = plusOf(T[n - 2]);
    bool all = true, marked = true;
    for (int n = 6; n <= 36; n++) {
        const Mat &a = T[n];
        bool ok = isTournament(a);
        for (int v = 0; v < n; v++) { int s = score(a, v); if (s == 0 || s == n - 1) ok = false; }
        std::set<std::string> forms;
        for (int v = 0; v < n; v++) forms.insert(canon(linkOf(a, v)));
        if ((int)forms.size() != n) ok = false;
        if (!ok) { all = false; std::printf("FAIL T_%d\n", n); }
        if (n >= 8) {  // old vertices are 0..n-3, s = n-2, t = n-1; in T_n - v, t has index n-2
            int m = n - 2;  // T_n = T_m^+
            for (int v = 0; v < m; v++) {
                Mat l = linkOf(a, v);
                int k = l.size();
                std::vector<int> mk;
                for (int y = 0; y < k; y++) {
                    if (score(l, y) != 1) continue;
                    bool good = true;
                    for (int z = 0; z < k; z++) if (l[y][z] && score(l, z) != m - 1) good = false;
                    if (good) mk.push_back(y);
                }
                if (!(mk.size() == 1 && mk[0] == k - 1)) marked = false;
            }
        }
    }
    check(all, "T_n: tournament, no source, no sink, n different canonical link forms, 6 <= n <= 36");
    check(marked, "in each link of an old vertex of T_n (8 <= n <= 36) the only marked vertex is t");
    std::printf(failed ? "SOME CHECKS FAILED\n" : "ALL OK\n");
    return failed ? 1 : 0;
}
