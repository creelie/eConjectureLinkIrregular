#!/usr/bin/env bash
# run_all.sh -- re-run every check of "Link-irregular tournaments exist for every order at least six".
#
#   C       verification/c/linkirr.c           every tournament on 2..7 vertices (code tables),
#                                              T_n for 6 <= n <= 60, Table 1
#   C++     verification/cpp/linkirr.cpp       every tournament on 2..6 vertices (all bijections),
#                                              T_n for n <= 36 by canonical forms, the marked vertex
#   Shell   verification/shell/check_linkirr.sh  bash integer arithmetic only
#   Python  verification/python/verify_linkirr.py
#   Julia   verification/julia/verify_linkirr.jl (if julia is on PATH or $JULIA is set)
#   Lean    verification/lean/LinkIrregular.lean (if lean is on PATH; the folder pins v4.34.1)
#           verification/lean/mathlib            (MATHLIB=1 only: lake fetches Mathlib's cache and
#                                                 builds the proof of the theorem for every n)
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
V="$ROOT/verification"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }

echo "== C and C++"
cc -O2 -Wall -o "$BUILD/linkirr" "$V/c/linkirr.c" || fail "compile linkirr.c"
c++ -O2 -Wall -std=c++17 -o "$BUILD/linkirr_cpp" "$V/cpp/linkirr.cpp" || fail "compile linkirr.cpp"
"$BUILD/linkirr" table > "$BUILD/c_table.txt" && ok "C: T_6, T_7 and Table 1" || fail "C: table (see build/c_table.txt)"
: > "$BUILD/c_count.txt"
for n in 2 3 4 5 6 7; do
  "$BUILD/linkirr" count $n >> "$BUILD/c_count.txt" || fail "C: count n=$n (see build/c_count.txt)"
done
grep -q "^n=7: 700560 labelled link-irregular tournaments, 139 up to isomorphism" "$BUILD/c_count.txt" \
  && ok "C: none on 2..5 vertices, 4 classes on 6, 139 on 7" || fail "C: counts (see build/c_count.txt)"
"$BUILD/linkirr" build 60 > "$BUILD/c_build.txt" && ok "C: T_n for 6 <= n <= 60" \
  || fail "C: T_n (see build/c_build.txt)"
"$BUILD/linkirr_cpp" > "$BUILD/cpp.txt" && grep -q '^ALL OK' "$BUILD/cpp.txt" \
  && ok "C++: counts, T_n by canonical forms, marked vertex" || fail "C++ (see build/cpp.txt)"

echo "== Shell"
bash "$V/shell/check_linkirr.sh" > "$BUILD/sh.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/sh.txt" \
  && ok "check_linkirr.sh" || fail "check_linkirr.sh (see build/sh.txt)"

echo "== Python"
python3 "$V/python/verify_linkirr.py" > "$BUILD/py.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/py.txt" \
  && ok "verify_linkirr.py" || fail "verify_linkirr.py (see build/py.txt)"

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  "$JULIA" "$V/julia/verify_linkirr.jl" > "$BUILD/jl.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/jl.txt" \
    && ok "verify_linkirr.jl" || fail "verify_linkirr.jl (see build/jl.txt)"
fi

echo "== Lean"
if ! command -v lean > /dev/null; then echo "lean not found: skipping (install elan)"; else
  out=$(cd "$V/lean" && lean LinkIrregular.lean 2>&1); st=$?
  echo "$out" > "$BUILD/lean.txt"
  if [ $st -eq 0 ] && ! grep -q "error\|sorryAx" <<< "$out" \
       && grep -q "'T7_irregular' depends on axioms: \[propext\]" <<< "$out" \
       && grep -q "'none_2_to_5' depends on axioms: \[propext\]" <<< "$out"; then
    ok "LinkIrregular.lean (kernel-checked)"
  else fail "LinkIrregular.lean (see build/lean.txt)"; fi
  if [ "${MATHLIB:-0}" = 1 ]; then
    out=$(cd "$V/lean/mathlib" && lake exe cache get > /dev/null && lake build 2>&1); st=$?
    echo "$out" > "$BUILD/lean_mathlib.txt"
    if [ $st -eq 0 ] && ! grep -q "sorryAx\|error" <<< "$out" \
         && grep -q "'Tournaments.exists_linkIrregular' depends on axioms: \[propext, Classical.choice, Quot.sound\]" <<< "$out"; then
      ok "mathlib/LinkIrregularMathlib.lean (Theorem 1.1 for every n; standard axioms only)"
    else fail "mathlib/LinkIrregularMathlib.lean (see build/lean_mathlib.txt)"; fi
  else echo "Mathlib proof skipped (set MATHLIB=1)"; fi
fi

if [ $FAILED -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAILED
