#!/usr/bin/env python3
"""verify_linkirr.py -- checks for "Link-irregular tournaments exist for every order at least six".

  * every tournament on n <= 6 vertices: links compared through canonical forms (least code over
    all relabellings); none is link-irregular for n <= 5, and for n = 6 there are 2880 labelled
    ones, i.e. 4 up to isomorphism, none with a source or a sink;
  * T_6, T_7: the arcs, the scores and Table 1;
  * the argument for T_6 - 4 and T_6 - 5 in the proof of Lemma 3.1;
  * T_n = T_{n-2}^+ for n <= 16: no source, no sink, links pairwise non-isomorphic (backtracking);
  * Lemma 2.1's scores: in T^+ - v the vertex s has score n - 1, t has score 1, and u gains one;
  * the remark: from T_7, the links of T_n for odd n <= 61 have pairwise different score sequences.

Prints "ALL OK" and exits 0 when every check passes.
"""
import itertools
import sys

failed = False


def check(cond, msg):
    global failed
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        failed = True


def from_arcs(n, arcs):
    a = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i):
            a[i][j] = 1
    for i, j in arcs:
        a[i][j], a[j][i] = 1, 0
    return a


ARCS6 = [(1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 6), (4, 5), (4, 6), (5, 3), (6, 1), (6, 5)]
ARCS7 = [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 7),
         (4, 5), (4, 6), (4, 7), (5, 6), (6, 3), (7, 1), (7, 5), (7, 6)]
T6 = from_arcs(6, [(i - 1, j - 1) for i, j in ARCS6])   # the paper's labels 1..6 become 0..5
T7 = from_arcs(7, [(i - 1, j - 1) for i, j in ARCS7])


def score(a, v):
    return sum(a[v])


def link(a, v):
    idx = [u for u in range(len(a)) if u != v]
    return [[a[i][j] for j in idx] for i in idx]


def is_tournament(a):
    n = len(a)
    return all(a[i][i] == 0 for i in range(n)) and all(a[i][j] + a[j][i] == 1 for i in range(n) for j in range(i + 1, n))


def no_source_sink(a):
    return all(0 < score(a, v) < len(a) - 1 for v in range(len(a)))


def plus(a):
    n = len(a)
    p = [row[:] + [0, 1] for row in a] + [[1] * n + [0, 0], [0] * n + [1, 0]]
    return p


def canon_small(a):
    n = len(a)
    best = None
    for p in itertools.permutations(range(n)):
        c = tuple(a[p[i]][p[j]] for i in range(n) for j in range(n))
        if best is None or c < best:
            best = c
    return best


def iso(x, y):
    """backtracking isomorphism test, candidates restricted by scores"""
    n = len(x)
    sx, sy = [score(x, v) for v in range(n)], [score(y, v) for v in range(n)]
    if sorted(sx) != sorted(sy):
        return False
    order = sorted(range(n), key=lambda v: sx.count(sx[v]))
    img, used = {}, [False] * n

    def ext(k):
        if k == n:
            return True
        i = order[k]
        for b in range(n):
            if used[b] or sy[b] != sx[i]:
                continue
            if all(x[i][j] == y[b][img[j]] for j in img):
                img[i], used[b] = b, True
                if ext(k + 1):
                    return True
                del img[i]
                used[b] = False
        return False

    return ext(0)


def main():
    # exhaustive, n <= 6
    tables = {}
    for m in range(1, 6):
        tab = {}
        for code in range(1 << (m * (m - 1) // 2)):
            a = [[0] * m for _ in range(m)]
            k = 0
            for i in range(m):
                for j in range(i + 1, m):
                    if (code >> k) & 1:
                        a[i][j] = 1
                    else:
                        a[j][i] = 1
                    k += 1
            tab[tuple(map(tuple, a))] = canon_small(a)
        tables[m] = tab
    for n in range(2, 7):
        cnt = withss = 0
        for code in range(1 << (n * (n - 1) // 2)):
            a = [[0] * n for _ in range(n)]
            k = 0
            for i in range(n):
                for j in range(i + 1, n):
                    if (code >> k) & 1:
                        a[i][j] = 1
                    else:
                        a[j][i] = 1
                    k += 1
            forms = {tables[n - 1][tuple(map(tuple, link(a, v)))] for v in range(n)}
            if len(forms) == n:
                cnt += 1
                if not no_source_sink(a):
                    withss += 1
        fact = 1
        for i in range(2, n + 1):
            fact *= i
        if n <= 5:
            check(cnt == 0, f"n={n}: no link-irregular tournament")
        else:
            check(cnt == 2880 and cnt // fact == 4 and withss == 0,
                  "n=6: 2880 labelled link-irregular tournaments, 4 up to isomorphism, none with a source or a sink")

    # T_6, T_7 and Table 1
    check(is_tournament(T6) and is_tournament(T7), "T_6 and T_7 are tournaments")
    check([score(T6, v) for v in range(6)] == [4, 4, 2, 2, 1, 2] and [score(T7, v) for v in range(7)] == [5, 5, 3, 3, 1, 1, 3],
          "scores 4,4,2,2,1,2 and 5,5,3,3,1,1,3")
    tab6 = [[1, 1, 2, 2, 4], [1, 2, 2, 2, 3], [0, 2, 2, 3, 3], [1, 1, 2, 3, 3], [1, 1, 2, 3, 3], [1, 1, 1, 3, 4]]
    tab7 = [[1, 1, 2, 3, 3, 5], [1, 1, 3, 3, 3, 4], [0, 1, 3, 3, 4, 4], [1, 1, 2, 3, 4, 4], [1, 2, 2, 2, 4, 4],
            [0, 2, 2, 3, 4, 4], [1, 1, 2, 2, 4, 5]]
    seq = lambda a: sorted(score(a, v) for v in range(len(a)))
    check([seq(link(T6, v)) for v in range(6)] == tab6 and [seq(link(T7, v)) for v in range(7)] == tab7, "Table 1")
    check(len({tuple(s) for s in tab7}) == 7, "the seven sequences of T_7 are distinct")

    # T_6 - 4 versus T_6 - 5, with the paper's labels
    def named_link(v):
        names = [u for u in range(1, 7) if u != v]
        L = link(T6, v - 1)
        sc = {names[i]: score(L, i) for i in range(5)}
        out = {names[i]: {names[j] for j in range(5) if L[i][j]} for i in range(5)}
        return sc, out
    sc4, out4 = named_link(4)
    sc5, out5 = named_link(5)
    check([u for u in sc4 if sc4[u] == 2] == [6] and 1 in out4[6] and sc4[1] == 3,
          "in T_6 - 4 the only vertex of score 2 is 6, and it beats 1, of score 3")
    check([u for u in sc5 if sc5[u] == 2] == [3] and out5[3] == {4, 6} and sc5[4] == sc5[6] == 1,
          "in T_6 - 5 the only vertex of score 2 is 3, and it beats only 4 and 6, of score 1")

    # T_n for n <= 16
    T = {6: T6, 7: T7}
    for n in range(8, 17):
        T[n] = plus(T[n - 2])
    ok = True
    for n in range(6, 17):
        a = T[n]
        L = [link(a, v) for v in range(n)]
        if not (is_tournament(a) and no_source_sink(a) and not any(iso(L[v], L[w]) for v in range(n) for w in range(v + 1, n))):
            ok = False
    check(ok, "T_n is a link-irregular tournament with neither a source nor a sink, 6 <= n <= 16")

    # scores in the links of T^+ (Lemma 2.1), for T = T_n, n <= 14
    ok = True
    for n in range(6, 15):
        a, p = T[n], plus(T[n])
        s, t = n, n + 1
        for v in range(n):
            l = link(p, v)          # vertices of p other than v, in order; s and t are the last two
            if score(l, n - 1) != n - 1 or score(l, n) != 1:
                ok = False
            lv = link(a, v)
            for i in range(n - 1):
                if score(l, i) != score(lv, i) + 1:
                    ok = False
        if score(link(p, s), n) != 0 or score(link(p, t), n) != n:
            ok = False
    check(ok, "in T^+ - v: s has score n - 1, t has score 1, old vertices gain one; t is a sink of T^+ - s, s a source of T^+ - t")

    # the remark on score sequences, odd n
    a, ok = T7, True
    for n in range(7, 62, 2):
        seqs = {tuple(seq(link(a, v))) for v in range(n)}
        if len(seqs) != n:
            ok = False
        a = plus(a)
    check(ok, "from T_7: the links of T_n have pairwise different score sequences for odd n <= 61")

    print("SOME CHECKS FAILED" if failed else "ALL OK")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
