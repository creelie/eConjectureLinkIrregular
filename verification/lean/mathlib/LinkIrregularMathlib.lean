/-
  Link-irregular tournaments exist for every order at least six: the proof of
  D. Bhattacharjee, *A short proof that link-irregular tournaments exist for every order at least
  six*. The Bastien–Khormali conjecture was first proved by C. H. Chau (doi:10.5281/zenodo.22150037),
  by a different construction formalised by S. Harte (doi:10.5281/zenodo.22232432).

  A tournament is a Bool-valued relation r on a finite type V with r v v = false and, for u ≠ v,
  exactly one of r u v, r v u. The link of v is the subtournament on the other vertices, and r is
  link-irregular if no two links are isomorphic.

  Proved below with Mathlib, using only the standard axioms:
  * `plus_linkIrregular` (Lemma 2.1): if r is a link-irregular tournament on n ≥ 3 vertices with
    neither a source nor a sink, then so is r⁺ on n + 2 vertices, where r⁺ adds a vertex s beating
    every old vertex, a vertex t beaten by every old vertex, and the arc t → s;
  * `T6_linkIrregular`, `T7_linkIrregular` (Lemma 3.1): the tournaments T₆ and T₇ of the paper;
  * `exists_linkIrregular` (Theorem 1.1): for every n ≥ 6 there is a link-irregular tournament on
    n vertices with neither a source nor a sink.
  That no link-irregular tournament exists on 2 to 5 vertices is checked in the kernel in
  `../LinkIrregular.lean` and by the C, C++ and Python programs.
-/
import Mathlib

open Finset

namespace Tournaments

/-! ### Scores and isomorphisms of Bool-valued relations -/

section General

variable {W W' : Type*} [Fintype W] [Fintype W']

/-- the score (out-degree) of x -/
def score (R : W → W → Bool) (x : W) : ℕ := (univ.filter fun y => R x y = true).card

/-- isomorphisms of Bool-valued relations -/
abbrev Iso (R : W → W → Bool) (R' : W' → W' → Bool) :=
  (fun a b => R a b = true) ≃r (fun a b => R' a b = true)

lemma score_iso {R : W → W → Bool} {R' : W' → W' → Bool} (φ : Iso R R') (x : W) :
    score R' (φ x) = score R x := by
  unfold score
  symm
  refine Finset.card_equiv φ.toEquiv fun y => ?_
  simp only [mem_filter, mem_univ, true_and, RelIso.coe_fn_toEquiv]
  exact φ.map_rel_iff.symm

/-- the number of vertices of score k -/
def cnt (R : W → W → Bool) (k : ℕ) : ℕ := (univ.filter fun x => score R x = k).card

lemma cnt_iso {R : W → W → Bool} {R' : W' → W' → Bool} (φ : Iso R R') (k : ℕ) :
    cnt R' k = cnt R k := by
  unfold cnt
  symm
  refine Finset.card_equiv φ.toEquiv fun x => ?_
  simp only [mem_filter, mem_univ, true_and, RelIso.coe_fn_toEquiv, score_iso]

/-- the number of arcs from a vertex of score a to a vertex of score b -/
def arcCnt (R : W → W → Bool) (a b : ℕ) : ℕ :=
  (univ.filter fun p : W × W => R p.1 p.2 = true ∧ score R p.1 = a ∧ score R p.2 = b).card

lemma arcCnt_iso {R : W → W → Bool} {R' : W' → W' → Bool} (φ : Iso R R') (a b : ℕ) :
    arcCnt R' a b = arcCnt R a b := by
  unfold arcCnt
  symm
  refine Finset.card_equiv (Equiv.prodCongr φ.toEquiv φ.toEquiv) fun p => ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    RelIso.coe_fn_toEquiv, score_iso]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨φ.map_rel_iff.2 h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨φ.map_rel_iff.1 h1, h2, h3⟩

/-- an isomorphism carries a vertex of score k to a vertex of score k -/
lemma exists_score_iso {R : W → W → Bool} {R' : W' → W' → Bool} (φ : Iso R R') {k : ℕ}
    (h : ∃ y, score R y = k) : ∃ y, score R' y = k := by
  obtain ⟨y, hy⟩ := h
  exact ⟨φ y, by rw [score_iso, hy]⟩

/-- `x` has score 1 and its out-neighbours have score N - 1 -/
def Marked (R : W → W → Bool) (N : ℕ) (x : W) : Prop :=
  score R x = 1 ∧ ∀ y, R x y = true → score R y = N - 1

lemma marked_iso {R : W → W → Bool} {R' : W' → W' → Bool} (φ : Iso R R') {N : ℕ} {x : W}
    (h : Marked R N x) : Marked R' N (φ x) := by
  refine ⟨by rw [score_iso]; exact h.1, fun y hy => ?_⟩
  have hy' : R x (φ.symm y) = true := by
    have := φ.map_rel_iff (a := x) (b := φ.symm y)
    simp only [RelIso.apply_symm_apply] at this
    exact this.1 hy
  have := h.2 _ hy'
  rw [← this, ← score_iso φ (φ.symm y), RelIso.apply_symm_apply]

end General

/-! ### Tournaments and links -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- r is a tournament -/
structure IsTournament (r : V → V → Bool) : Prop where
  irrefl : ∀ v, r v v = false
  total : ∀ u v, u ≠ v → (r u v = true ↔ r v u = false)

/-- the link of v: the subtournament on the other vertices -/
def link (r : V → V → Bool) (v : V) : {u // u ≠ v} → {u // u ≠ v} → Bool :=
  fun a b => r a.1 b.1

/-- no two links are isomorphic -/
def LinkIrregular (r : V → V → Bool) : Prop :=
  ∀ v w, v ≠ w → IsEmpty (Iso (link r v) (link r w))

/-- every score lies between 1 and |V| - 2 -/
def NoSourceSink (r : V → V → Bool) : Prop :=
  ∀ v, 1 ≤ score r v ∧ score r v + 2 ≤ Fintype.card V

lemma score_link (r : V → V → Bool) (v : V) (x : {u // u ≠ v}) :
    score (link r v) x = (univ.filter fun y => y ≠ v ∧ r x.1 y = true).card := by
  unfold score link
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext y
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, h, rfl⟩

lemma score_link_le (r : V → V → Bool) (hT : IsTournament r) (v : V) (x : {u // u ≠ v}) :
    score (link r v) x + 2 ≤ Fintype.card V := by
  rw [score_link]
  have hsub : (univ.filter fun y => y ≠ v ∧ r x.1 y = true) ⊆ (univ.erase v).erase x.1 := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    simp only [mem_erase, mem_univ, and_true]
    refine ⟨?_, hy.1⟩
    rintro rfl
    rw [hT.irrefl] at hy
    exact absurd hy.2 (by simp)
  have h1 := card_le_card hsub
  rw [card_erase_of_mem (by simpa using x.2), card_erase_of_mem (mem_univ v), card_univ] at h1
  have : 2 ≤ Fintype.card V := by
    have h2 := card_le_univ ({v, x.1} : Finset V)
    rw [card_pair (fun e => x.2 e.symm)] at h2
    exact h2
  omega

/-! ### The step from n to n + 2 -/

/-- r⁺ on V ⊕ Bool: `inr true` is s, `inr false` is t -/
def plus (r : V → V → Bool) : V ⊕ Bool → V ⊕ Bool → Bool
  | .inl a, .inl b => r a b
  | .inr true, .inl _ => true
  | .inl _, .inr false => true
  | .inr false, .inr true => true
  | _, _ => false

lemma card_filter_sum (p : V ⊕ Bool → Prop) [DecidablePred p] :
    (univ.filter p).card = (univ.filter fun v => p (.inl v)).card +
      ((if p (.inr true) then 1 else 0) + (if p (.inr false) then 1 else 0)) := by
  rw [card_filter, card_filter, Fintype.sum_sum_type, Fintype.sum_bool]

section Scores

variable (r : V → V → Bool)

lemma score_plus_inl (u : V) : score (plus r) (.inl u) = score r u + 1 := by
  unfold score
  rw [card_filter_sum]
  simp [plus]
  rfl

lemma score_plus_s : score (plus r) (.inr true) = Fintype.card V := by
  unfold score
  rw [card_filter_sum]
  simp [plus]

lemma score_plus_t : score (plus r) (.inr false) = 1 := by
  unfold score
  rw [card_filter_sum]
  simp [plus]

/-- in the link of an old vertex v: t has score 1 -/
lemma sc_v_t (v : V) (h : (.inr false : V ⊕ Bool) ≠ .inl v) :
    score (link (plus r) (.inl v)) ⟨.inr false, h⟩ = 1 := by
  rw [score_link, card_filter_sum]
  simp [plus]

/-- in the link of an old vertex v: s has score n - 1 -/
lemma sc_v_s (v : V) (h : (.inr true : V ⊕ Bool) ≠ .inl v) :
    score (link (plus r) (.inl v)) ⟨.inr true, h⟩ = Fintype.card V - 1 := by
  rw [score_link, card_filter_sum]
  simp [plus, filter_ne', card_erase_of_mem]

/-- in the link of an old vertex v: an old vertex u gains one, from the arc u → t -/
lemma sc_v_u (v u : V) (h : (.inl u : V ⊕ Bool) ≠ .inl v) :
    score (link (plus r) (.inl v)) ⟨.inl u, h⟩ =
      score (link r v) ⟨u, fun e => h (by rw [e])⟩ + 1 := by
  rw [score_link, card_filter_sum, score_link]
  simp [plus]

/-- in the link of s: t has score 0 -/
lemma sc_s_t (h : (.inr false : V ⊕ Bool) ≠ .inr true) :
    score (link (plus r) (.inr true)) ⟨.inr false, h⟩ = 0 := by
  rw [score_link, card_filter_sum]
  simp [plus]

/-- in the link of s: an old vertex u has score sc(u) + 1 -/
lemma sc_s_u (u : V) (h : (.inl u : V ⊕ Bool) ≠ .inr true) :
    score (link (plus r) (.inr true)) ⟨.inl u, h⟩ = score r u + 1 := by
  rw [score_link, card_filter_sum]
  simp [plus, score]

/-- in the link of t: s has score n -/
lemma sc_t_s (h : (.inr true : V ⊕ Bool) ≠ .inr false) :
    score (link (plus r) (.inr false)) ⟨.inr true, h⟩ = Fintype.card V := by
  rw [score_link, card_filter_sum]
  simp [plus]

/-- in the link of t: an old vertex u has score sc(u) -/
lemma sc_t_u (u : V) (h : (.inl u : V ⊕ Bool) ≠ .inr false) :
    score (link (plus r) (.inr false)) ⟨.inl u, h⟩ = score r u := by
  rw [score_link, card_filter_sum]
  simp [plus, score]

end Scores

/-- the V-part of a vertex of V ⊕ Bool, with a default -/
def getL (d : V) : V ⊕ Bool → V
  | .inl u => u
  | .inr _ => d

/-- an isomorphism between links of r⁺ at old vertices that fixes s and t restricts to an
    isomorphism between the links of r -/
lemma restrict_iso {r : V → V → Bool} {v w : V}
    (φ : Iso (link (plus r) (.inl v)) (link (plus r) (.inl w)))
    (hs : ∀ x, (φ x).1 = .inr true ↔ x.1 = .inr true)
    (ht : ∀ x, (φ x).1 = .inr false ↔ x.1 = .inr false) :
    Nonempty (Iso (link r v) (link r w)) := by
  have hleft : ∀ x : {z // z ≠ (.inl v : V ⊕ Bool)}, (∃ a, x.1 = .inl a) →
      ∃ b, (φ x).1 = .inl b := by
    rintro x ⟨a, ha⟩
    rcases hφ : (φ x).1 with b | b
    · exact ⟨b, rfl⟩
    · cases b
      · have := (ht x).1 hφ
        rw [ha] at this
        exact absurd this (by simp)
      · have := (hs x).1 hφ
        rw [ha] at this
        exact absurd this (by simp)
  let A : {u // u ≠ v} → {z // z ≠ (.inl v : V ⊕ Bool)} :=
    fun a => ⟨.inl a.1, fun e => a.2 (Sum.inl_injective e)⟩
  have hne : ∀ a : {u // u ≠ v}, getL a.1 (φ (A a)).1 ≠ w := by
    intro a e
    obtain ⟨b, hb⟩ := hleft (A a) ⟨a.1, rfl⟩
    have h := (φ (A a)).2
    rw [hb] at e h
    exact h (by rw [← e]; rfl)
  let f : {u // u ≠ v} → {u // u ≠ w} := fun a => ⟨getL a.1 (φ (A a)).1, hne a⟩
  have hf : ∀ a, (.inl (f a).1 : V ⊕ Bool) = (φ (A a)).1 := by
    intro a
    obtain ⟨b, hb⟩ := hleft (A a) ⟨a.1, rfl⟩
    simp only [f, hb, getL]
  have hinj : Function.Injective f := by
    intro a a' h
    have h1 : (φ (A a)).1 = (φ (A a')).1 := by rw [← hf, ← hf, h]
    have h2 := φ.injective (Subtype.ext h1)
    exact Subtype.ext (Sum.inl_injective (congrArg Subtype.val h2))
  have hsurj : Function.Surjective f := by
    intro b
    let B : {z // z ≠ (.inl w : V ⊕ Bool)} := ⟨.inl b.1, fun e => b.2 (Sum.inl_injective e)⟩
    have hB : φ (φ.symm B) = B := φ.apply_symm_apply B
    obtain ⟨a, ha⟩ : ∃ a, (φ.symm B).1 = .inl a := by
      rcases hX : (φ.symm B).1 with a | c
      · exact ⟨a, rfl⟩
      · cases c
        · have := (ht (φ.symm B)).2 hX
          rw [hB] at this
          exact absurd this (by simp [B])
        · have := (hs (φ.symm B)).2 hX
          rw [hB] at this
          exact absurd this (by simp [B])
    have hav : a ≠ v := fun e => (φ.symm B).2 (by rw [ha, e])
    refine ⟨⟨a, hav⟩, Subtype.ext (Sum.inl_injective (β := Bool) ?_)⟩
    rw [hf]
    have hA : A ⟨a, hav⟩ = φ.symm B := Subtype.ext ha.symm
    rw [hA, hB]
  refine ⟨⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun {a b} => ?_⟩⟩
  show r (f a).1 (f b).1 = true ↔ r a.1 b.1 = true
  have e1 : r (f a).1 (f b).1 = plus r (.inl (f a).1) (.inl (f b).1) := rfl
  rw [e1, hf, hf]
  exact φ.map_rel_iff

/-- Lemma 2.1 -/
theorem plus_linkIrregular (r : V → V → Bool) (hT : IsTournament r) (hL : LinkIrregular r)
    (hN : NoSourceSink r) (h3 : 3 ≤ Fintype.card V) : LinkIrregular (plus r) := by
  set N := Fintype.card V with hNdef
  -- the three kinds of links, told apart by sources (score N) and sinks (score 0)
  have s_sink : ∃ y, score (link (plus r) (.inr true)) y = 0 :=
    ⟨⟨.inr false, by simp⟩, sc_s_t r _⟩
  have s_nosource : ¬ ∃ y, score (link (plus r) (.inr true)) y = N := by
    rintro ⟨⟨y, hy⟩, h⟩
    rcases y with u | b
    · rw [sc_s_u] at h
      have := (hN u).2
      omega
    · cases b
      · rw [sc_s_t] at h
        omega
      · exact hy rfl
  have t_source : ∃ y, score (link (plus r) (.inr false)) y = N :=
    ⟨⟨.inr true, by simp⟩, sc_t_s r _⟩
  have t_nosink : ¬ ∃ y, score (link (plus r) (.inr false)) y = 0 := by
    rintro ⟨⟨y, hy⟩, h⟩
    rcases y with u | b
    · rw [sc_t_u] at h
      have := (hN u).1
      omega
    · cases b
      · exact hy rfl
      · rw [sc_t_s] at h
        omega
  have v_nosource : ∀ v, ¬ ∃ y, score (link (plus r) (.inl v)) y = N := by
    rintro v ⟨⟨y, hy⟩, h⟩
    rcases y with u | b
    · rw [sc_v_u] at h
      have := score_link_le r hT v ⟨u, fun e => hy (by rw [e])⟩
      omega
    · cases b
      · rw [sc_v_t] at h
        omega
      · rw [sc_v_s] at h
        omega
  have v_nosink : ∀ v, ¬ ∃ y, score (link (plus r) (.inl v)) y = 0 := by
    rintro v ⟨⟨y, hy⟩, h⟩
    rcases y with u | b
    · rw [sc_v_u] at h
      omega
    · cases b
      · rw [sc_v_t] at h
        omega
      · rw [sc_v_s] at h
        omega
  -- the marked vertex of a link of an old vertex is t
  have marked_iff : ∀ v (x : {z // z ≠ (.inl v : V ⊕ Bool)}),
      Marked (link (plus r) (.inl v)) N x ↔ x.1 = .inr false := by
    intro v x
    obtain ⟨y, hy⟩ := x
    constructor
    · rintro ⟨h1, h2⟩
      rcases y with u | b
      · rw [sc_v_u] at h1
        have harc : link (plus r) (.inl v) ⟨.inl u, hy⟩ ⟨.inr false, by simp⟩ = true := rfl
        have := h2 _ harc
        rw [sc_v_t] at this
        omega
      · cases b
        · rfl
        · rw [sc_v_s] at h1
          omega
    · intro h
      simp only at h
      subst h
      refine ⟨sc_v_t r v hy, fun z hz => ?_⟩
      obtain ⟨z, hz'⟩ := z
      rcases z with u | b
      · exact absurd hz (by simp [link, plus])
      · cases b
        · exact absurd hz (by simp [link, plus])
        · exact sc_v_s r v hz'
  intro x y hxy
  constructor
  intro φ
  rcases x with v | b <;> rcases y with w | c
  · -- two old vertices
    have hvw : v ≠ w := fun e => hxy (by rw [e])
    have hv := hL v w hvw
    have ht : ∀ x, (φ x).1 = .inr false ↔ x.1 = .inr false := by
      have ht0 : (φ ⟨.inr false, by simp⟩).1 = .inr false :=
        (marked_iff w _).1 (marked_iso φ ((marked_iff v _).2 rfl))
      intro x
      constructor
      · intro h
        have : φ x = φ ⟨.inr false, by simp⟩ := Subtype.ext (by rw [h, ht0])
        rw [φ.injective this]
      · intro h
        have : x = ⟨.inr false, by simp⟩ := Subtype.ext h
        rw [this, ht0]
    have hs0 : (φ ⟨.inr true, by simp⟩).1 = .inr true := by
      have harc : link (plus r) (.inl v) ⟨.inr false, by simp⟩ ⟨.inr true, by simp⟩ = true := rfl
      have h : plus r (φ ⟨.inr false, by simp⟩).1 (φ ⟨.inr true, by simp⟩).1 = true :=
        φ.map_rel_iff.2 harc
      have ht0 := (ht ⟨.inr false, by simp⟩).2 rfl
      rw [ht0] at h
      rcases hz : (φ ⟨.inr true, by simp⟩).1 with u | d
      · rw [hz] at h
        exact absurd h (by simp [plus])
      · cases d
        · rw [hz] at h
          exact absurd h (by simp [plus])
        · rfl
    have hs : ∀ x, (φ x).1 = .inr true ↔ x.1 = .inr true := by
      intro x
      constructor
      · intro h
        have : φ x = φ ⟨.inr true, by simp⟩ := Subtype.ext (by rw [h, hs0])
        rw [φ.injective this]
      · intro h
        have : x = ⟨.inr true, by simp⟩ := Subtype.ext h
        rw [this, hs0]
    obtain ⟨ψ⟩ := restrict_iso φ hs ht
    exact hv.false ψ
  · cases c
    · exact v_nosource v (exists_score_iso φ.symm t_source)
    · exact v_nosink v (exists_score_iso φ.symm s_sink)
  · cases b
    · exact v_nosource w (exists_score_iso φ t_source)
    · exact v_nosink w (exists_score_iso φ s_sink)
  · cases b <;> cases c
    · exact hxy rfl
    · exact s_nosource (exists_score_iso φ t_source)
    · exact t_nosink (exists_score_iso φ s_sink)
    · exact hxy rfl


/-- r⁺ is a tournament -/
theorem plus_tournament (r : V → V → Bool) (hT : IsTournament r) : IsTournament (plus r) where
  irrefl x := by
    rcases x with u | b
    · exact hT.irrefl u
    · cases b <;> rfl
  total x y hxy := by
    rcases x with u | b <;> rcases y with w | c
    · exact hT.total u w (fun e => hxy (by rw [e]))
    · cases c <;> simp [plus]
    · cases b <;> simp [plus]
    · cases b <;> cases c <;> simp_all [plus]

/-- r⁺ has neither a source nor a sink -/
theorem plus_noSourceSink (r : V → V → Bool) (hN : NoSourceSink r) (h1 : 1 ≤ Fintype.card V) :
    NoSourceSink (plus r) := by
  intro x
  rw [Fintype.card_sum, Fintype.card_bool]
  rcases x with u | b
  · rw [score_plus_inl]
    have := hN u
    omega
  · cases b
    · rw [score_plus_t]
      omega
    · rw [score_plus_s]
      omega

/-! ### The two starting tournaments -/

/-- arcs of T₆, vertices 0..5 (the paper's 1..6) -/
def arcs6 : List (ℕ × ℕ) :=
  [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,4),(3,5),(4,2),(5,0),(5,4)]

/-- arcs of T₇, vertices 0..6 (the paper's 1..7) -/
def arcs7 : List (ℕ × ℕ) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,6),
   (3,4),(3,5),(3,6),(4,5),(5,2),(6,0),(6,4),(6,5)]

def T6 (i j : Fin 6) : Bool := arcs6.contains (i.val, j.val)
def T7 (i j : Fin 7) : Bool := arcs7.contains (i.val, j.val)

/-- links told apart by the number of vertices of some score, or by the number of arcs from a
    vertex of score 2 to a vertex of score 3, are not isomorphic -/
lemma linkIrregular_of_invariants {W : Type*} [Fintype W] [DecidableEq W] (r : W → W → Bool)
    (h : ∀ v w, v ≠ w → (∃ k : Fin 8, cnt (link r v) k ≠ cnt (link r w) k) ∨
      arcCnt (link r v) 2 3 ≠ arcCnt (link r w) 2 3) : LinkIrregular r := by
  intro v w hvw
  constructor
  intro φ
  rcases h v w hvw with ⟨k, hk⟩ | h23
  · exact hk (cnt_iso φ k).symm
  · exact h23 (arcCnt_iso φ 2 3).symm

theorem T6_tournament : IsTournament T6 := ⟨by decide +kernel, by decide +kernel⟩
theorem T7_tournament : IsTournament T7 := ⟨by decide +kernel, by decide +kernel⟩
theorem T6_noSourceSink : NoSourceSink T6 := by unfold NoSourceSink; decide +kernel
theorem T7_noSourceSink : NoSourceSink T7 := by unfold NoSourceSink; decide +kernel

/-- Lemma 3.1 for T₆: score sequences, and for T₆ - 4, T₆ - 5 (here 3 and 4) the arc from the
    vertex of score 2 to a vertex of score 3 -/
theorem T6_linkIrregular : LinkIrregular T6 :=
  linkIrregular_of_invariants T6 (by decide +kernel)

/-- Lemma 3.1 for T₇: the seven links have different score sequences -/
theorem T7_linkIrregular : LinkIrregular T7 :=
  linkIrregular_of_invariants T7 (by decide +kernel)

/-! ### Theorem 1.1 -/

/-- For every n ≥ 6 there is a link-irregular tournament on n vertices with neither a source nor
    a sink. -/
theorem exists_linkIrregular (n : ℕ) (hn : 6 ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (r : V → V → Bool),
      Fintype.card V = n ∧ IsTournament r ∧ LinkIrregular r ∧ NoSourceSink r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 6 ∨ n = 7 ∨ 8 ≤ n by omega) with rfl | rfl | h8
    · exact ⟨Fin 6, inferInstance, inferInstance, T6, by simp, T6_tournament, T6_linkIrregular,
        T6_noSourceSink⟩
    · exact ⟨Fin 7, inferInstance, inferInstance, T7, by simp, T7_tournament, T7_linkIrregular,
        T7_noSourceSink⟩
    · obtain ⟨V, _, _, r, hc, hT, hL, hN⟩ := ih (n - 2) (by omega) (by omega)
      refine ⟨V ⊕ Bool, inferInstance, inferInstance, plus r, ?_, plus_tournament r hT,
        plus_linkIrregular r hT hL hN (by omega), plus_noSourceSink r hN (by omega)⟩
      rw [Fintype.card_sum, Fintype.card_bool, hc]
      omega

#print axioms exists_linkIrregular

end Tournaments
