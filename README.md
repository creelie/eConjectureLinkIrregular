# A short proof that link-irregular tournaments exist for every order at least six

Deep Bhattacharjee

A digraph is link-irregular if no two of its vertices have isomorphic links; in a tournament the
link of v is the subtournament T − v. Bastien and Khormali (*On link-irregular digraphs*, J. Combin.
Math. Combin. Comput. 130 (2026), Conjecture 3.7) conjectured that a link-irregular tournament on n
vertices exists if and only if n ≥ 6, and proved it for n ≤ 8.

Ching Ho Chau proved the conjecture in August 2026 (*A proof of the Bastien–Khormali conjecture on
link-irregular tournaments*, doi:10.5281/zenodo.22150037), by substituting link-irregular 2-strong
tournaments of orders 8 to 15 into a transitive tournament; Shane Harte formalised that proof in Lean
(doi:10.5281/zenodo.22232432). This repository gives a second, shorter proof whose only finite input is
two tournaments on six and seven vertices.

If T is link-irregular with neither a source nor a sink, add a vertex s
beating every vertex of T, a vertex t beaten by every vertex of T, and the arc t → s. The new
tournament T⁺ is again link-irregular with neither a source nor a sink: the links of s, t and the old
vertices are told apart by sources and sinks, and in each link T⁺ − v the vertex t is the only vertex
of score 1 whose out-neighbour has score n − 1, so an isomorphism T⁺ − v ≅ T⁺ − w fixes s and t and
restricts to T − v ≅ T − w. Starting from explicit tournaments T₆ and T₇ gives every n ≥ 6.

## Paper

`preprintLinkIrregular/` holds the paper (LaTeX source and the TikZ figure); `dist/` holds the PDF, a
source zip with the figure as PNG and an arXiv tarball, rebuilt by `scripts/build_paper.sh`.

## Checks

```
verification/c/linkirr.c               every tournament on 2..7 vertices (none link-irregular up to 5, 4 classes
                                       on 6, 139 on 7), T_n for 6 <= n <= 60, Table 1
verification/cpp/linkirr.cpp           every tournament on 2..6 vertices by trying all bijections; T_n for
                                       n <= 36 by canonical forms; the marked vertex of every link
verification/shell/check_linkirr.sh    bash integer arithmetic only: T_6, T_7, Table 1, the T_6 - 4 / T_6 - 5
                                       argument, the scores in T^+
verification/python/verify_linkirr.py  every tournament on n <= 6 vertices, Table 1, T_n for n <= 16, the scores
                                       of Lemma 2.1, the score-sequence remark for odd n <= 61
verification/julia/verify_linkirr.jl   T_n for n <= 22, the marked vertex, the score-sequence remark for odd n <= 101
verification/lean/LinkIrregular.lean   Lean 4 kernel check: no link-irregular tournament on 2..5 vertices,
                                       T_6 and T_7 link-irregular, Table 1
verification/lean/mathlib/             Lean 4 + Mathlib proof of Lemma 2.1 and of Theorem 1.1 for every n >= 6
                                       by this construction; standard axioms only
```

`scripts/run_all.sh` runs them all (`MATHLIB=1` also builds the Mathlib proof); the `verify` workflow
runs them on every pull request.

## Citation

See `CITATION.cff`. Please also cite Chau's earlier proof (doi:10.5281/zenodo.22150037).

## Licence

MIT, see `LICENSE`.
