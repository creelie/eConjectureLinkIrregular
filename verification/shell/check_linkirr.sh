#!/usr/bin/env bash
# check_linkirr.sh -- bash integer arithmetic only.
#   1. T_6 and T_7 (the paper's arcs) are tournaments with the stated scores.
#   2. Table 1: the score sequence of every vertex-deleted subtournament of T_6 and T_7.
#   3. The argument for T_6 - 4 and T_6 - 5 in the proof of Lemma 3.1.
#   4. The scores of T^+ in Lemma 2.1, for T = T_6, T_7, ..., T_18: in T^+ every old score rises
#      by one, s has score n and t has score 1; in T^+ - v, s has n - 1 and t has 1.
# Prints "ALL OK" when everything passes.
set -u
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }

declare -A A   # A[i,j] = 1 iff i -> j
setup() {   # setup n "i>j,k;..." (the paper's notation, vertices 1..n)
  local n=$1 spec=$2 i j
  N=$n
  for ((i = 1; i <= n; i++)); do for ((j = 1; j <= n; j++)); do A[$i,$j]=0; done; done
  for ((i = 1; i <= n; i++)); do for ((j = 1; j < i; j++)); do A[$i,$j]=1; done; done
  IFS=';' read -ra parts <<< "$spec"
  for p in "${parts[@]}"; do
    i=${p%%>*}; IFS=',' read -ra outs <<< "${p#*>}"
    for j in "${outs[@]}"; do A[$i,$j]=1; A[$j,$i]=0; done
  done
}
istour() {
  local i j
  for ((i = 1; i <= N; i++)); do
    ((A[$i,$i] == 0)) || return 1
    for ((j = i + 1; j <= N; j++)); do ((A[$i,$j] + A[$j,$i] == 1)) || return 1; done
  done
}
score() { local s=0 w; for ((w = 1; w <= N; w++)); do ((s += A[$1,$w])); done; echo $s; }
linkseq() {   # sorted score sequence of T - v
  local v=$1 u w s out=()
  for ((u = 1; u <= N; u++)); do
    ((u == v)) && continue
    s=0; for ((w = 1; w <= N; w++)); do ((w != v)) && ((s += A[$u,$w])); done
    out+=("$s")
  done
  printf '%s\n' "${out[@]}" | sort -n | paste -sd, -
}

setup 6 "1>2,3,4,5;2>3,4,5,6;3>4,6;4>5,6;5>3;6>1,5"
istour && ok "T_6 is a tournament" || bad "T_6"
sc=""; for v in 1 2 3 4 5 6; do sc+="$(score $v) "; done
[[ "$sc" == "4 4 2 2 1 2 " ]] && ok "scores of T_6: $sc" || bad "scores of T_6: $sc"
want=("1,1,2,2,4" "1,2,2,2,3" "0,2,2,3,3" "1,1,2,3,3" "1,1,2,3,3" "1,1,1,3,4")
okt=1; for v in 1 2 3 4 5 6; do [[ "$(linkseq $v)" == "${want[$((v-1))]}" ]] || okt=0; done
((okt)) && ok "Table 1, T_6" || bad "Table 1, T_6"
# T_6 - 4: vertices of score 2 and their out-neighbours' scores (scores inside T_6 - 4)
lscore() { local v=$1 u=$2 s=0 w; for ((w = 1; w <= N; w++)); do ((w != v)) && ((s += A[$u,$w])); done; echo $s; }
two4=(); for u in 1 2 3 5 6; do (( $(lscore 4 $u) == 2 )) && two4+=($u); done
[[ "${two4[*]}" == "6" && ${A[6,1]} == 1 && $(lscore 4 1) == 3 ]] \
  && ok "T_6 - 4: the only vertex of score 2 is 6, and 6 -> 1 with 1 of score 3" || bad "T_6 - 4"
two5=(); for u in 1 2 3 4 6; do (( $(lscore 5 $u) == 2 )) && two5+=($u); done
outs=(); for u in 1 2 4 6; do ((A[3,$u])) && outs+=("$u:$(lscore 5 $u)"); done
[[ "${two5[*]}" == "3" && "${outs[*]}" == "4:1 6:1" ]] \
  && ok "T_6 - 5: the only vertex of score 2 is 3, and it beats only 4 and 6, both of score 1" || bad "T_6 - 5"

setup 7 "1>2,3,4,5,6;2>3,4,5,6,7;3>4,5,7;4>5,6,7;5>6;6>3;7>1,5,6"
istour && ok "T_7 is a tournament" || bad "T_7"
sc=""; for v in 1 2 3 4 5 6 7; do sc+="$(score $v) "; done
[[ "$sc" == "5 5 3 3 1 1 3 " ]] && ok "scores of T_7: $sc" || bad "scores of T_7: $sc"
want=("1,1,2,3,3,5" "1,1,3,3,3,4" "0,1,3,3,4,4" "1,1,2,3,4,4" "1,2,2,2,4,4" "0,2,2,3,4,4" "1,1,2,2,4,5")
okt=1; seen=""; for v in 1 2 3 4 5 6 7; do s=$(linkseq $v); [[ "$s" == "${want[$((v-1))]}" ]] || okt=0; seen+="$s"$'\n'; done
((okt)) && ok "Table 1, T_7" || bad "Table 1, T_7"
(( $(printf '%s' "$seen" | sort -u | wc -l) == 7 )) && ok "the seven score sequences of T_7 are distinct" || bad "T_7 sequences"

# 4. T^+ scores, starting from T_6 and T_7 and adding pairs
okp=1
for start in 6 7; do
  if ((start == 6)); then setup 6 "1>2,3,4,5;2>3,4,5,6;3>4,6;4>5,6;5>3;6>1,5"
  else setup 7 "1>2,3,4,5,6;2>3,4,5,6,7;3>4,5,7;4>5,6,7;5>6;6>3;7>1,5,6"; fi
  while ((N <= 16)); do
    n=$N; old=(); for ((v = 1; v <= n; v++)); do old+=("$(score $v)"); done
    s=$((n + 1)); t=$((n + 2))
    for ((v = 1; v <= n; v++)); do A[$s,$v]=1; A[$v,$s]=0; A[$v,$t]=1; A[$t,$v]=0; done
    A[$t,$s]=1; A[$s,$t]=0; A[$s,$s]=0; A[$t,$t]=0; N=$((n + 2))
    istour || okp=0
    for ((v = 1; v <= n; v++)); do (( $(score $v) == ${old[$((v-1))]} + 1 )) || okp=0; done
    (( $(score $s) == n && $(score $t) == 1 )) || okp=0
    for ((v = 1; v <= n; v++)); do (( $(lscore $v $s) == n - 1 && $(lscore $v $t) == 1 )) || okp=0; done
    for ((v = 1; v <= N; v++)); do sv=$(score $v); ((sv >= 1 && sv <= N - 2)) || okp=0; done
  done
done
((okp)) && ok "T^+ scores (old +1, s = n, t = 1; in T^+ - v: s = n - 1, t = 1), no source or sink, up to 18 vertices" \
       || bad "T^+ scores"

if ((fail == 0)); then echo "ALL OK"; else echo "SOME CHECKS FAILED"; fi
exit $fail
