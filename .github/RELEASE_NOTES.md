**Link-irregular tournaments exist for every order at least six**, by Deep Bhattacharjee.

Bastien and Khormali conjectured that a link-irregular tournament on n vertices (one whose vertex-deleted subtournaments are pairwise non-isomorphic) exists if and only if n ≥ 6, and proved it for n ≤ 8. The paper proves it for every n.

| Step | Content |
|---|---|
| Lemma 2.1 | If T is link-irregular with neither a source nor a sink, so is T⁺: add s beating all of T, t beaten by all of T, and t → s |
| Lemma 3.1 | Explicit link-irregular tournaments T₆ and T₇ without a source or a sink |
| Theorem 1.1 | T₆, T₇ and repeated T ↦ T⁺ give every n ≥ 6 |

The proofs are by hand. Every finite claim is re-checked in C, C++, Bash, Python, Julia and Lean 4: a Lean proof with Mathlib covers the theorem for every n ≥ 6 using only the standard axioms, and a kernel check shows that no tournament on 2 to 5 vertices is link-irregular. Exhaustive counts: 4 link-irregular tournaments on six vertices and 139 on seven, up to isomorphism.

Files:
- `link-irregular-tournaments.pdf`: the paper
- `link-irregular-tournaments-tex.zip`: LaTeX source with the figure as PNG (and its TikZ source)
- `link-irregular-tournaments-arxiv.tar.gz`: LaTeX source with the figure as PDF, ready for arXiv

Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.
