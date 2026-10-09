/-
  Kernel-checked finite facts for "Link-irregular tournaments exist for every order at least six".

  A tournament on {0, ..., n-1} is coded by a number c < 2^(n(n-1)/2): the bit of the pair
  i < j (pairs in lexicographic order) is 1 when i → j.  Two links T - v and T - w are compared
  by trying every bijection between their vertex lists.

  * `none_2_to_5`: no tournament on 2, 3, 4 or 5 vertices is link-irregular (every one of the
    2^(n(n-1)/2) tournaments has two isomorphic links);
  * `T6_irregular`, `T7_irregular`: the tournaments T₆ and T₇ of the paper are link-irregular,
    have neither a source nor a sink, and have the scores and link score sequences of Table 1.

  The statement for every n ≥ 6 is proved with Mathlib in `mathlib/LinkIrregularMathlib.lean`.
  This file uses Lean 4 core only; every statement is checked by the kernel (`decide +kernel`).
-/

/-- all permutations of a list -/
def perms : List Nat → List (List Nat)
  | [] => [[]]
  | a :: l => (perms l).flatMap fun p =>
      (List.range (p.length + 1)).map fun i => p.take i ++ a :: p.drop i

/-- index of the pair i < j among the pairs of {0, ..., n-1} in lexicographic order -/
def pairIdx (n i j : Nat) : Nat := i * (2 * n - i - 1) / 2 + (j - i - 1)

/-- does i beat j in the tournament with code c on n vertices -/
def beats (n c i j : Nat) : Bool :=
  if i < j then c.testBit (pairIdx n i j) else if j < i then !c.testBit (pairIdx n j i) else false

def others (n v : Nat) : List Nat := (List.range n).filter (· != v)

/-- T - v ≅ T - w, by trying every bijection -/
def linkIso (n c v w : Nat) : Bool :=
  let a := others n v
  let b := others n w
  (perms (List.range (n - 1))).any fun p =>
    (List.range (n - 1)).all fun i => (List.range (n - 1)).all fun j =>
      beats n c (a.getD i 0) (a.getD j 0) == beats n c (b.getD (p.getD i 0) 0) (b.getD (p.getD j 0) 0)

def linkIrregular (n c : Nat) : Bool :=
  (List.range n).all fun v => (List.range n).all fun w => v < w → !linkIso n c v w

def score (n c v : Nat) : Nat := ((List.range n).filter fun w => beats n c v w).length

def noSourceSink (n c : Nat) : Bool := (List.range n).all fun v => 1 ≤ score n c v && score n c v + 2 ≤ n

/-- the code of the tournament with the given arcs -/
def code (n : Nat) (arcs : List (Nat × Nat)) : Nat :=
  arcs.foldl (fun c (i, j) => if i < j then c ||| (1 <<< pairIdx n i j) else c) 0

def arcs6 : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,4),(3,5),(4,2),(5,0),(5,4)]
def arcs7 : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,6),
   (3,4),(3,5),(3,6),(4,5),(5,2),(6,0),(6,4),(6,5)]

def c6 : Nat := code 6 arcs6
def c7 : Nat := code 7 arcs7

/-- the arc lists are consistent with the codes: every listed arc is an arc -/
theorem codes_ok : arcs6.all (fun (i, j) => beats 6 c6 i j) = true ∧
    arcs7.all (fun (i, j) => beats 7 c7 i j) = true := by decide +kernel

/-- sorted score sequence of T - v -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: l => if x ≤ y then x :: y :: l else y :: insertSorted x l
def linkScores (n c v : Nat) : List Nat :=
  ((others n v).map fun u => ((others n v).filter fun w => beats n c u w).length).foldr insertSorted []

theorem T6_irregular :
    linkIrregular 6 c6 = true ∧ noSourceSink 6 c6 = true ∧
    (List.range 6).map (score 6 c6) = [4, 4, 2, 2, 1, 2] ∧
    (List.range 6).map (linkScores 6 c6) =
      [[1,1,2,2,4], [1,2,2,2,3], [0,2,2,3,3], [1,1,2,3,3], [1,1,2,3,3], [1,1,1,3,4]] := by
  decide +kernel

theorem T7_irregular :
    linkIrregular 7 c7 = true ∧ noSourceSink 7 c7 = true ∧
    (List.range 7).map (score 7 c7) = [5, 5, 3, 3, 1, 1, 3] ∧
    (List.range 7).map (linkScores 7 c7) =
      [[1,1,2,3,3,5], [1,1,3,3,3,4], [0,1,3,3,4,4], [1,1,2,3,4,4], [1,2,2,2,4,4],
       [0,2,2,3,4,4], [1,1,2,2,4,5]] := by
  decide +kernel

/-- no tournament on n vertices is link-irregular, for n = 2, 3, 4, 5 -/
theorem none_2_to_5 :
    [2, 3, 4, 5].all (fun n => (List.range (2 ^ (n * (n - 1) / 2))).all fun c => !linkIrregular n c)
      = true := by
  decide +kernel

#print axioms T7_irregular
#print axioms none_2_to_5
