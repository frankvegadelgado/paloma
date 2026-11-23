module

public import Mathlib

@[expose] public section

/-!
# The formula `T_H` for a per-vertex degree function

For a finite simple graph `H` with degrees `d_v` and a port labelling, the formula `T_H` has
`d_v + 1` Boolean clones `(v, 0), …, (v, d_v)` per vertex `v`: the clone `(v, 0)` occurs in the
unit clause `(¬ (v,0))`, the clone `(v, p+1)` occurs in the edge clause of the edge at port `p`
of `v`, and the `d_v + 1` cyclic implications `(¬ (v,i) ∨ (v,i+1))` (indices modulo `d_v + 1`)
enforce consistency. This module proves, for every degree function:

* `Σ_v d_v = 2 m`, hence `Σ_v (d_v + 1) + m = n + 3 m`;
* the number of satisfied clauses equals `U(z) + (m - F(z)) + (Σ_v (d_v + 1) - T(z))`;
* the optimum equals `B + α` with `B = Σ_v (d_v + 1) + m` (`optimum_identity`);
* the lift of an independent set `I` has value `B + |I|` (`lift_satCount`).

The vertex `v` has the port set `Fin (d_v)`; the port structure is a bijection between the
`2 m` edge ends and the ports.
-/

namespace PalomaMax2SAT.GeneralDegreeFormula

/-- A graph on `n` vertices with `m` edges and a port labelling for the degree function `deg`:
the `2 m` edge ends are in bijection with the ports `Σ v, Fin (deg v)`. -/
structure GPortGraph (n m : ℕ) (deg : Fin n → ℕ) where
  leftPt : Fin m → Σ v : Fin n, Fin (deg v)
  rightPt : Fin m → Σ v : Fin n, Fin (deg v)
  left_ne_right : ∀ e, (leftPt e).1 ≠ (rightPt e).1
  ports_bijective : Function.Bijective (Sum.elim leftPt rightPt)

def GPortGraph.left {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg) (e : Fin m) :
    Fin n := (G.leftPt e).1

def GPortGraph.right {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg) (e : Fin m) :
    Fin n := (G.rightPt e).1

/-- The clone used by the left end of `e`: port `p` uses the clone `p + 1`. -/
def GPortGraph.leftClone {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg) (e : Fin m) :
    ℕ := ((G.leftPt e).2 : ℕ) + 1

def GPortGraph.rightClone {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg) (e : Fin m) :
    ℕ := ((G.rightPt e).2 : ℕ) + 1

theorem GPortGraph.leftClone_lt {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (e : Fin m) : G.leftClone e < deg (G.left e) + 1 := by
  unfold GPortGraph.leftClone GPortGraph.left
  have h := (G.leftPt e).2.isLt
  omega

theorem GPortGraph.rightClone_lt {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (e : Fin m) : G.rightClone e < deg (G.right e) + 1 := by
  unfold GPortGraph.rightClone GPortGraph.right
  have h := (G.rightPt e).2.isLt
  omega

def Independent {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (I : Finset (Fin n)) : Prop :=
  ∀ e, ¬ (G.left e ∈ I ∧ G.right e ∈ I)

def IsIndependenceNumber {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (alpha : ℕ) : Prop :=
  (∀ I, Independent G I → I.card ≤ alpha) ∧ ∃ I, Independent G I ∧ I.card = alpha

/-- Every edge has two ends and every vertex has `deg v` ports: `Σ_v d_v = 2 m`. -/
theorem sum_deg_eq {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg) :
    ∑ v, deg v = 2 * m := by
  have h := Fintype.card_of_bijective G.ports_bijective
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma] at h
  omega

/-- `Σ_v (d_v + 1) + m = n + 3 m`. -/
theorem constant_eq {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg) :
    ∑ v, (deg v + 1) + m = n + 3 * m := by
  have h1 : ∑ v : Fin n, (deg v + 1) = ∑ v, deg v + n := by
    rw [Finset.sum_add_distrib]
    simp
  have h2 := sum_deg_eq G
  omega

/-! ### Assignments and the score -/

/-- The successor of the clone `i` in the cycle of length `D + 1`. -/
def cyc (D i : ℕ) : ℕ := if i = D then 0 else i + 1

/-- A transition `1 → 0` of the cycle at `v` at the position `i`. -/
abbrev transAt {n : ℕ} (deg : Fin n → ℕ) (z : Fin n → ℕ → Bool) (v : Fin n) (i : ℕ) :
    Prop :=
  z v i = true ∧ z v (cyc (deg v) i) = false

/-- The number of transitions of the cycle at `v`. -/
def transCount {n : ℕ} (deg : Fin n → ℕ) (z : Fin n → ℕ → Bool) (v : Fin n) : ℕ :=
  ∑ i ∈ Finset.range (deg v + 1), if transAt deg z v i then 1 else 0

def selectedVertices {n : ℕ} (z : Fin n → ℕ → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => z v 0 = false

def transVertices {n : ℕ} (deg : Fin n → ℕ) (z : Fin n → ℕ → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => 0 < transCount deg z v

def cleanVertices {n : ℕ} (deg : Fin n → ℕ) (z : Fin n → ℕ → Bool) : Finset (Fin n) :=
  selectedVertices z \ transVertices deg z

def falseEdges {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (z : Fin n → ℕ → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun e =>
    z (G.left e) (G.leftClone e) = false ∧ z (G.right e) (G.rightClone e) = false

def deletionSet {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (z : Fin n → ℕ → Bool) : Finset (Fin n) :=
  (Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices deg z ∧ G.right e ∈ cleanVertices deg z).image G.left

def repairedSet {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (z : Fin n → ℕ → Bool) : Finset (Fin n) :=
  cleanVertices deg z \ deletionSet G z

/-- Satisfied unit, edge, and cyclic-consistency clauses. -/
def score {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (z : Fin n → ℕ → Bool) : ℕ :=
  (selectedVertices z).card + (m - (falseEdges G z).card) +
    (∑ v, (deg v + 1) - ∑ v, transCount deg z v)

theorem mem_selectedVertices {n : ℕ} (z : Fin n → ℕ → Bool) (v : Fin n) :
    v ∈ selectedVertices z ↔ z v 0 = false := by
  unfold selectedVertices
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_transVertices {n : ℕ} (deg : Fin n → ℕ) (z : Fin n → ℕ → Bool) (v : Fin n) :
    v ∈ transVertices deg z ↔ 0 < transCount deg z v := by
  unfold transVertices
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem transCount_pos {n : ℕ} (deg : Fin n → ℕ) (z : Fin n → ℕ → Bool) (v : Fin n) (i : ℕ)
    (hi : i ∈ Finset.range (deg v + 1)) (h : transAt deg z v i) : 0 < transCount deg z v := by
  unfold transCount
  calc 0 < (fun i => if transAt deg z v i then 1 else 0) i := by simp [h]
    _ ≤ ∑ i ∈ Finset.range (deg v + 1), if transAt deg z v i then 1 else 0 :=
      Finset.single_le_sum (f := fun i => if transAt deg z v i then 1 else 0)
        (fun _ _ => Nat.zero_le _) hi

theorem cons_split {n : ℕ} (deg : Fin n → ℕ) (z : Fin n → ℕ → Bool) (v : Fin n) :
    (∑ i ∈ Finset.range (deg v + 1), if ¬ transAt deg z v i then 1 else 0) +
      transCount deg z v = deg v + 1 := by
  unfold transCount
  rw [← Finset.sum_add_distrib]
  have h : ∀ i ∈ Finset.range (deg v + 1),
      ((if ¬ transAt deg z v i then 1 else 0) + (if transAt deg z v i then 1 else 0) : ℕ) =
        1 := by
    intro i _
    by_cases hi : transAt deg z v i <;> simp [hi]
  rw [Finset.sum_congr rfl h]
  simp

/-- With no transition at `v` and `z v 0 = false`, every clone of `v` is false: a true clone
would propagate around the cycle of implications to clone `0`. -/
theorem no_transition_all_false {n : ℕ} (deg : Fin n → ℕ) (z : Fin n → ℕ → Bool) (v : Fin n)
    (hzero : z v 0 = false) (hnone : ∀ i, i < deg v + 1 → ¬ transAt deg z v i) :
    ∀ i, i < deg v + 1 → z v i = false := by
  have fwd : ∀ k i, i + k = deg v → z v i = true → z v (deg v) = true := by
    intro k
    induction k with
    | zero =>
      intro i hi h
      have hv : i = deg v := by omega
      rw [← hv]
      exact h
    | succ k ih =>
      intro i hi h
      have hne : i ≠ deg v := by omega
      have hc : cyc (deg v) i = i + 1 := by
        unfold cyc
        exact if_neg hne
      have h1 : z v (i + 1) = true := by
        cases hz : z v (i + 1) with
        | true => rfl
        | false =>
          exact absurd (⟨h, by rw [hc]; exact hz⟩ : transAt deg z v i) (hnone i (by omega))
      exact ih (i + 1) (by omega) h1
  have hlast : z v (deg v) = false := by
    cases hz : z v (deg v) with
    | false => rfl
    | true =>
      have hc : cyc (deg v) (deg v) = 0 := by
        unfold cyc
        exact if_pos rfl
      exact absurd (⟨hz, by rw [hc]; exact hzero⟩ : transAt deg z v (deg v))
        (hnone (deg v) (by omega))
  intro i hi
  cases hz : z v i with
  | false => rfl
  | true =>
    have := fwd (deg v - i) i (by omega) hz
    rw [hlast] at this
    exact absurd this (by simp)

theorem repairedSet_independent {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (z : Fin n → ℕ → Bool) : Independent G (repairedSet G z) := by
  intro e he
  rcases he with ⟨hl, hr⟩
  have hlc : G.left e ∈ cleanVertices deg z := (Finset.mem_sdiff.mp hl).1
  have hrc : G.right e ∈ cleanVertices deg z := (Finset.mem_sdiff.mp hr).1
  have hdel : G.left e ∈ deletionSet G z := by
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlc, hrc⟩, rfl⟩
  exact (Finset.mem_sdiff.mp hl).2 hdel

theorem clean_all_false {n : ℕ} (deg : Fin n → ℕ) (z : Fin n → ℕ → Bool) (v : Fin n)
    (hv : v ∈ cleanVertices deg z) : ∀ i, i < deg v + 1 → z v i = false := by
  have h0 := (Finset.mem_sdiff.mp hv).1
  have hT := (Finset.mem_sdiff.mp hv).2
  exact no_transition_all_false deg z v ((mem_selectedVertices z v).mp h0)
    (fun i hi h => hT ((mem_transVertices deg z v).mpr
      (transCount_pos deg z v i (Finset.mem_range.mpr hi) h)))

theorem internalEdges_subset_falseEdges {n m : ℕ} {deg : Fin n → ℕ}
    (G : GPortGraph n m deg) (z : Fin n → ℕ → Bool) :
    (Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices deg z ∧ G.right e ∈ cleanVertices deg z) ⊆
        falseEdges G z := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨_, hl, hr⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    clean_all_false deg z (G.left e) hl _ (G.leftClone_lt e),
    clean_all_false deg z (G.right e) hr _ (G.rightClone_lt e)⟩

theorem score_le {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (z : Fin n → ℕ → Bool) :
    score G z ≤ ∑ v, (deg v + 1) + m + (repairedSet G z).card := by
  have htrans : (transVertices deg z).card ≤ ∑ v, transCount deg z v := by
    unfold transVertices
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro v _
    by_cases h : 0 < transCount deg z v
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      exact Nat.zero_le _
  have hTle : ∑ v, transCount deg z v ≤ ∑ v, (deg v + 1) := by
    apply Finset.sum_le_sum
    intro v _
    have := cons_split deg z v
    omega
  have hclean : (selectedVertices z).card ≤
      (cleanVertices deg z).card + (transVertices deg z).card := by
    unfold cleanVertices
    rw [← Finset.card_sdiff_add_card_inter (selectedVertices z) (transVertices deg z)]
    exact Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _
  have hdel : (deletionSet G z).card ≤ (falseEdges G z).card := by
    calc
      (deletionSet G z).card ≤
          (Finset.univ.filter fun e =>
            G.left e ∈ cleanVertices deg z ∧ G.right e ∈ cleanVertices deg z).card :=
        Finset.card_image_le
      _ ≤ (falseEdges G z).card :=
        Finset.card_le_card (internalEdges_subset_falseEdges G z)
  have hfalseBound : (falseEdges G z).card ≤ m := by
    simpa using Finset.card_le_univ (falseEdges G z)
  have hrepair : (cleanVertices deg z).card ≤
      (repairedSet G z).card + (deletionSet G z).card := by
    unfold repairedSet
    rw [← Finset.card_sdiff_add_card_inter (cleanVertices deg z) (deletionSet G z)]
    exact Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _
  unfold score
  omega

/-- The assignment of the independent set `I`: clones of `v ∈ I` false, all others true. -/
def assignmentOfIndependent {n : ℕ} (I : Finset (Fin n)) : Fin n → ℕ → Bool :=
  fun v _ => if v ∈ I then false else true

theorem score_assignmentOfIndependent {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (I : Finset (Fin n)) (hI : Independent G I) :
    score G (assignmentOfIndependent I) = ∑ v, (deg v + 1) + m + I.card := by
  have hselected : selectedVertices (assignmentOfIndependent I) = I := by
    ext v
    rw [mem_selectedVertices]
    simp [assignmentOfIndependent]
  have hT : ∑ v, transCount deg (assignmentOfIndependent I) v = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    unfold transCount
    apply Finset.sum_eq_zero
    intro i _
    by_cases hv : v ∈ I <;> simp [transAt, assignmentOfIndependent, hv]
  have hfalse : falseEdges G (assignmentOfIndependent I) = ∅ := by
    unfold falseEdges
    rw [Finset.filter_eq_empty_iff]
    intro e _ h
    apply hI e
    constructor
    · by_contra hl
      have h1 := h.1
      simp [assignmentOfIndependent, hl] at h1
    · by_contra hr
      have h2 := h.2
      simp [assignmentOfIndependent, hr] at h2
  unfold score
  rw [hselected, hT, hfalse]
  simp only [Finset.card_empty, Nat.sub_zero]
  omega

theorem optimum_bound {n m alpha : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (halpha : IsIndependenceNumber G alpha) :
    (∀ z : Fin n → ℕ → Bool, score G z ≤ ∑ v, (deg v + 1) + m + alpha) ∧
      ∃ z : Fin n → ℕ → Bool, score G z = ∑ v, (deg v + 1) + m + alpha := by
  constructor
  · intro z
    calc
      score G z ≤ ∑ v, (deg v + 1) + m + (repairedSet G z).card := score_le G z
      _ ≤ ∑ v, (deg v + 1) + m + alpha :=
        Nat.add_le_add_left (halpha.1 _ (repairedSet_independent G z)) _
  · obtain ⟨I, hI, hcard⟩ := halpha.2
    exact ⟨assignmentOfIndependent I, by
      rw [score_assignmentOfIndependent G I hI, hcard]⟩

/-! ### The formula as an explicit list of clauses -/

/-- A literal over the clone variables `(v, i)`; `positive = false` is a negated literal. -/
structure Lit (n : ℕ) where
  var : Fin n × ℕ
  positive : Bool

abbrev Clause (n : ℕ) := List (Lit n)

def Lit.eval {n : ℕ} (z : Fin n → ℕ → Bool) (l : Lit n) : Bool :=
  if l.positive then z l.var.1 l.var.2 else !z l.var.1 l.var.2

def Clause.satisfied {n : ℕ} (z : Fin n → ℕ → Bool) (c : Clause n) : Bool :=
  c.any (Lit.eval z)

/-- Indices of the clauses of `T_H`: one unit clause per vertex, one edge clause per edge,
and `deg v + 1` cyclic implications per vertex `v`. -/
abbrev ClauseIdx {n : ℕ} (m : ℕ) (deg : Fin n → ℕ) :=
  Fin n ⊕ Fin m ⊕ (Σ v : Fin n, Fin (deg v + 1))

def unitClause {n : ℕ} (v : Fin n) : Clause n :=
  [Lit.mk (v, 0) false]

def edgeClause {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg) (e : Fin m) :
    Clause n :=
  [Lit.mk (G.left e, G.leftClone e) true, Lit.mk (G.right e, G.rightClone e) true]

def consClause {n : ℕ} {deg : Fin n → ℕ} (p : Σ v : Fin n, Fin (deg v + 1)) : Clause n :=
  [Lit.mk (p.1, (p.2 : ℕ)) false, Lit.mk (p.1, cyc (deg p.1) (p.2 : ℕ)) true]

def clauseOf {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg) :
    ClauseIdx m deg → Clause n :=
  Sum.elim unitClause (Sum.elim (edgeClause G) consClause)

/-- The number of clauses of `T_H` satisfied by `z`. -/
noncomputable def satCount {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (z : Fin n → ℕ → Bool) : ℕ :=
  (Finset.univ.filter fun c : ClauseIdx m deg =>
    Clause.satisfied z (clauseOf G c) = true).card

theorem card_filter_sum_proof {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : α ⊕ β ⊕ γ → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter fun a => P (Sum.inl a)).card +
        (Finset.univ.filter fun b => P (Sum.inr (Sum.inl b))).card +
          (Finset.univ.filter fun c => P (Sum.inr (Sum.inr c))).card := by
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  ring

theorem consClause_satisfied {n : ℕ} {deg : Fin n → ℕ} (z : Fin n → ℕ → Bool)
    (p : Σ v : Fin n, Fin (deg v + 1)) :
    Clause.satisfied z (consClause p) = true ↔ ¬ transAt deg z p.1 (p.2 : ℕ) := by
  cases ha : z p.1 (p.2 : ℕ) <;> cases hb : z p.1 (cyc (deg p.1) (p.2 : ℕ)) <;>
    simp [transAt, consClause, Clause.satisfied, Lit.eval, ha, hb]

theorem satCount_eq_score {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (z : Fin n → ℕ → Bool) : satCount G z = score G z := by
  have h := card_filter_sum_proof
    (fun c : ClauseIdx m deg => Clause.satisfied z (clauseOf G c) = true)
  have hU : (Finset.univ.filter fun v : Fin n =>
      Clause.satisfied z (clauseOf G (Sum.inl v)) = true).card =
        (selectedVertices z).card := by
    apply congrArg Finset.card
    ext v
    cases ha : z v 0 <;> simp [selectedVertices, clauseOf, unitClause,
      Clause.satisfied, Lit.eval, ha]
  have hE : (Finset.univ.filter fun e : Fin m =>
      Clause.satisfied z (clauseOf G (Sum.inr (Sum.inl e))) = true).card =
        m - (falseEdges G z).card := by
    have hset : (Finset.univ.filter fun e : Fin m =>
        Clause.satisfied z (clauseOf G (Sum.inr (Sum.inl e))) = true) =
          (falseEdges G z)ᶜ := by
      ext e
      cases ha : z (G.left e) (G.leftClone e) <;>
        cases hb : z (G.right e) (G.rightClone e) <;>
          simp [falseEdges, clauseOf, edgeClause, Clause.satisfied, Lit.eval, ha, hb]
    rw [hset, Finset.card_compl]
    simp
  have hC : (Finset.univ.filter fun p : Σ v : Fin n, Fin (deg v + 1) =>
      Clause.satisfied z (clauseOf G (Sum.inr (Sum.inr p))) = true).card =
        ∑ v, ∑ i ∈ Finset.range (deg v + 1), if ¬ transAt deg z v i then 1 else 0 := by
    rw [Finset.card_filter, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact if_congr (consClause_satisfied (deg := deg) z ⟨v, i⟩) rfl rfl
  have hsplit : ∑ v, (∑ i ∈ Finset.range (deg v + 1), if ¬ transAt deg z v i then 1 else 0) +
      ∑ v, transCount deg z v = ∑ v, (deg v + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => cons_split deg z v
  unfold satCount score
  rw [h, hU, hE, hC]
  omega

theorem optimum_identity {n m alpha : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (halpha : IsIndependenceNumber G alpha) :
    IsGreatest (Set.range (satCount G)) (∑ v, (deg v + 1) + m + alpha) := by
  obtain ⟨hle, z, hz⟩ := optimum_bound G halpha
  refine ⟨⟨z, ?_⟩, ?_⟩
  · rw [satCount_eq_score]
    exact hz
  · rintro _ ⟨w, rfl⟩
    rw [satCount_eq_score]
    exact hle w

theorem lift_satCount {n m : ℕ} {deg : Fin n → ℕ} (G : GPortGraph n m deg)
    (I : Finset (Fin n)) (hI : Independent G I) :
    satCount G (assignmentOfIndependent I) = ∑ v, (deg v + 1) + m + I.card := by
  rw [satCount_eq_score]
  exact score_assignmentOfIndependent G I hI

end PalomaMax2SAT.GeneralDegreeFormula
