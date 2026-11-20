module

public import Mathlib

public section

/-!
# Canonical standalone challenge

This file intentionally imports only Mathlib so Palomar can compile it in an
isolated canonical environment. The implementation lives in the project
modules imported by `Solution.lean`.
-/

namespace PalomaMax2SAT.CubicThreeOccurrence

structure PortGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  left_ne_right : ∀ e, left e ≠ right e
  leftPort : Fin m → Fin 3
  rightPort : Fin m → Fin 3
  left_unique : ∀ e f, left e = left f → leftPort e = leftPort f → e = f
  right_unique : ∀ e f, right e = right f → rightPort e = rightPort f → e = f
  cross_unique : ∀ e f, left e = right f → leftPort e = rightPort f → False
  port_occupied : ∀ v : Fin n, ∀ p : Fin 3,
    (∃ e, left e = v ∧ leftPort e = p) ∨ (∃ e, right e = v ∧ rightPort e = p)

def Independent {n m : ℕ} (G : PortGraph n m) (I : Finset (Fin n)) : Prop :=
  ∀ e, ¬ (G.left e ∈ I ∧ G.right e ∈ I)

def IsIndependenceNumber {n m : ℕ} (G : PortGraph n m) (alpha : ℕ) : Prop :=
  (∀ I, Independent G I → I.card ≤ alpha) ∧
    ∃ I, Independent G I ∧ I.card = alpha

def edgeClone (p : Fin 3) : Fin 4 := p.succ

abbrev transition {n : ℕ} (z : Fin n → Fin 4 → Bool)
    (v : Fin n) (i : Fin 4) : Prop :=
  z v i = true ∧ z v (i + 1) = false

def selectedVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => z v 0 = false

noncomputable def transitionPairs {n : ℕ} (z : Fin n → Fin 4 → Bool) :
    Finset (Fin n × Fin 4) :=
  Finset.univ.filter fun pair => transition z pair.1 pair.2

noncomputable def transitionVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  (transitionPairs z).image Prod.fst

noncomputable def cleanVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  selectedVertices z \ transitionVertices z

def falseEdges {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun e =>
    z (G.left e) (edgeClone (G.leftPort e)) = false ∧
      z (G.right e) (edgeClone (G.rightPort e)) = false

noncomputable def deletionSet {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  ((Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z).image G.left)

noncomputable def repairedSet {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  cleanVertices z \ deletionSet G z

noncomputable def score {n m : ℕ} (G : PortGraph n m) (z : Fin n → Fin 4 → Bool) : ℕ :=
  (selectedVertices z).card + (m - (falseEdges G z).card) +
    (4 * n - (transitionPairs z).card)

private theorem no_transition_all_false {n : ℕ} (z : Fin n → Fin 4 → Bool)
    (v : Fin n) (hzero : z v 0 = false)
    (hnone : v ∉ transitionVertices z) : ∀ i, z v i = false := by
  have ht : ∀ i, ¬ transition z v i := by
    intro i hi
    apply hnone
    exact Finset.mem_image.mpr
      ⟨(v, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  have ht0 := ht 0
  have ht1 := ht 1
  have ht2 := ht 2
  have ht3 := ht 3
  generalize h0 : z v 0 = b0 at hzero ht0 ht1 ht2 ht3 ⊢
  generalize h1 : z v 1 = b1 at ht0 ht1 ht2 ht3 ⊢
  generalize h2 : z v 2 = b2 at ht0 ht1 ht2 ht3 ⊢
  generalize h3 : z v 3 = b3 at ht0 ht1 ht2 ht3 ⊢
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    intro i <;> fin_cases i <;> simp_all [transition]

private theorem internalEdges_subset_falseEdges {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) :
    (Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z) ⊆ falseEdges G z := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨_, hl, hr⟩
  have hleft0 := (Finset.mem_sdiff.mp hl).1
  have hleftT := (Finset.mem_sdiff.mp hl).2
  have hright0 := (Finset.mem_sdiff.mp hr).1
  have hrightT := (Finset.mem_sdiff.mp hr).2
  have al : ∀ i, z (G.left e) i = false :=
    no_transition_all_false z (G.left e) (Finset.mem_filter.mp hleft0).2 hleftT
  have ar : ∀ i, z (G.right e) i = false :=
    no_transition_all_false z (G.right e) (Finset.mem_filter.mp hright0).2 hrightT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, al _, ar _⟩

def assignmentOfIndependent {n : ℕ} (I : Finset (Fin n)) :
    Fin n → Fin 4 → Bool :=
  fun v _ => if v ∈ I then false else true

private theorem score_assignmentOfIndependent {n m : ℕ} (G : PortGraph n m)
    (I : Finset (Fin n)) (hI : Independent G I) :
    score G (assignmentOfIndependent I) = 4 * n + m + I.card := by
  have hselected : selectedVertices (assignmentOfIndependent I) = I := by
    ext v
    simp [selectedVertices, assignmentOfIndependent]
  have htransition : transitionPairs (assignmentOfIndependent I) = ∅ := by
    ext pair
    simp [transitionPairs, transition, assignmentOfIndependent]
  have hfalse : falseEdges G (assignmentOfIndependent I) = ∅ := by
    ext e
    simp [falseEdges, assignmentOfIndependent, hI e]
  simp only [score, hselected, htransition, hfalse, Finset.card_empty,
    Nat.sub_zero]
  omega

end PalomaMax2SAT.CubicThreeOccurrence

/-! Hard-implication cycle definitions used by the graph-transfer results. -/
namespace PalomaMax2SAT.HardOccurrenceSplit

abbrev advance {α : Type*} (next : α → α) (k : ℕ) (i : α) : α :=
  Nat.rec i (fun _ current => next current) k

abbrev OrbitConnected {α : Type*} (next : α → α) : Prop :=
  ∀ i j, ∃ k, advance next k i = j

abbrev HardImplicationsHold {α : Type*} (next : α → α) (z : α → Bool) : Prop :=
  ∀ i, z i = true → z (next i) = true

abbrev IsHardOptimum {Assignment : Type*} (feasible : Assignment → Prop)
    (score : Assignment → ℕ) (opt : ℕ) : Prop :=
  (∀ a, feasible a → score a ≤ opt) ∧ ∃ a, feasible a ∧ score a = opt

theorem propagate_hard_implications {α : Type*} (next : α → α)
    (z : α → Bool) (h : HardImplicationsHold next z) :
    ∀ k i, z i = true → z (advance next k i) = true := by
  intro k
  induction k with
  | zero =>
      intro i hi
      simpa using hi
  | succ k ih =>
      intro i hi
      change z (next (advance next k i)) = true
      exact h _ (ih i hi)

end PalomaMax2SAT.HardOccurrenceSplit

namespace PalomaMax2SAT.CubicPublic

open CubicThreeOccurrence

theorem repairedSet_independent {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Independent G (repairedSet G z) := by
  intro e he
  rcases he with ⟨hl, hr⟩
  have hlc : G.left e ∈ cleanVertices z := (Finset.mem_sdiff.mp hl).1
  have hrc : G.right e ∈ cleanVertices z := (Finset.mem_sdiff.mp hr).1
  have hdel : G.left e ∈ deletionSet G z := by
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlc, hrc⟩, rfl⟩
  exact (Finset.mem_sdiff.mp hl).2 hdel

theorem repairedSet_card_lower_bound {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) :
    score G z ≤ 4 * n + m + (repairedSet G z).card := by
  have htrans : (transitionVertices z).card ≤ (transitionPairs z).card :=
    Finset.card_image_le
  have hclean : (selectedVertices z).card ≤
      (cleanVertices z).card + (transitionVertices z).card := by
    rw [← Finset.card_sdiff_add_card_inter (selectedVertices z) (transitionVertices z)]
    exact Nat.add_le_add_left
      (Finset.card_le_card Finset.inter_subset_right) _
  have hdel : (deletionSet G z).card ≤ (falseEdges G z).card := by
    calc
      (deletionSet G z).card ≤
          (Finset.univ.filter fun e =>
            G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z).card :=
        Finset.card_image_le
      _ ≤ (falseEdges G z).card :=
        Finset.card_le_card (internalEdges_subset_falseEdges G z)
  have hfalseBound : (falseEdges G z).card ≤ m := by
    simpa using Finset.card_le_univ (falseEdges G z)
  have htransitionBound : (transitionPairs z).card ≤ 4 * n := by
    calc
      (transitionPairs z).card ≤
          (Finset.univ : Finset (Fin n × Fin 4)).card := Finset.card_le_univ _
      _ = 4 * n := by simp [Nat.mul_comm]
  have hrepair : (cleanVertices z).card ≤
      (repairedSet G z).card + (deletionSet G z).card := by
    rw [← Finset.card_sdiff_add_card_inter (cleanVertices z) (deletionSet G z)]
    exact Nat.add_le_add_left
      (Finset.card_le_card Finset.inter_subset_right) _
  unfold score
  omega

theorem exact_three_occurrence_identity {n m alpha : ℕ}
    (G : PortGraph n m) (halpha : IsIndependenceNumber G alpha) :
    (∀ z, score G z ≤ 4 * n + m + alpha) ∧
      ∃ z, score G z = 4 * n + m + alpha := by
  constructor
  · intro z
    calc
      score G z ≤ 4 * n + m + (repairedSet G z).card :=
        repairedSet_card_lower_bound G z
      _ ≤ 4 * n + m + alpha :=
        Nat.add_le_add_left (halpha.1 _ (repairedSet_independent G z)) _
  · obtain ⟨I, hI, hcard⟩ := halpha.2
    exact ⟨assignmentOfIndependent I, by
      rw [score_assignmentOfIndependent G I hI, hcard]⟩

theorem ratio_83_84_from_cubic_mis
    (n m alpha found : ℕ)
    (hcubic : 2 * m = 3 * n)
    (halpha : 2 * alpha ≤ n)
    (happrox : 7 * found ≥ 6 * alpha) :
    84 * (4 * n + m + found) ≥ 83 * (4 * n + m + alpha) := by
  omega

theorem ratio_83_84_arithmetic :
    (11 : ℚ) + 6 / 7 = (83 / 84) * 12 := by
  norm_num

end PalomaMax2SAT.CubicPublic

namespace PalomaMax2SAT.SemanticHorn

open PalomaMax2SAT.CubicThreeOccurrence

/-- A literal over the clone variables `(v, i)`; `positive = false` is a negated
literal. -/
structure Lit (n : ℕ) where
  var : Fin n × Fin 4
  positive : Bool

/-- A clause is a list of literals. -/
abbrev Clause (n : ℕ) := List (Lit n)

def Lit.eval {n : ℕ} (z : Fin n → Fin 4 → Bool) (l : Lit n) : Bool :=
  if l.positive then z l.var.1 l.var.2 else !z l.var.1 l.var.2

/-- A clause is satisfied when some literal evaluates to true. -/
def Clause.satisfied {n : ℕ} (z : Fin n → Fin 4 → Bool) (c : Clause n) : Bool :=
  c.any (Lit.eval z)

/-- Horn: at most one negative literal. -/
def IsHorn {n : ℕ} (c : Clause n) : Prop :=
  (c.filter fun l => !l.positive).length ≤ 1

/-- Indices of the clauses of `T_H`: one unit clause per vertex, one edge clause
per edge, and four cyclic implications per vertex. -/
abbrev ClauseIdx (n m : ℕ) := Fin n ⊕ Fin m ⊕ (Fin n × Fin 4)

/-- The clauses of `T_H`: `(¬ z v 0)`, `(z u p ∨ z w q)` for an edge `uw` with
endpoint ports `p`, `q`, and `(¬ z v i ∨ z v (i+1))`. -/
def clauseOf {n m : ℕ} (G : PortGraph n m) : ClauseIdx n m → Clause n :=
  Sum.elim (fun v => [Lit.mk (v, 0) false])
    (Sum.elim
      (fun e => [Lit.mk (G.left e, edgeClone (G.leftPort e)) true,
        Lit.mk (G.right e, edgeClone (G.rightPort e)) true])
      (fun p => [Lit.mk p false, Lit.mk (p.1, p.2 + 1) true]))

/-- The number of occurrences of the variable `x` in a clause. -/
def Clause.count {n : ℕ} (x : Fin n × Fin 4) (c : Clause n) : ℕ :=
  (c.map fun l => if l.var = x then 1 else 0).sum

/-- The number of occurrences of the variable `x` in the formula `T_H`. -/
noncomputable def occurrences {n m : ℕ} (G : PortGraph n m)
    (x : Fin n × Fin 4) : ℕ :=
  ∑ c : ClauseIdx n m, Clause.count x (clauseOf G c)

/-- The number of clauses of `T_H` satisfied by `z`. -/
noncomputable def satCount {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : ℕ :=
  (Finset.univ.filter fun c : ClauseIdx n m =>
    Clause.satisfied z (clauseOf G c) = true).card

theorem card_filter_sum_proof {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : α ⊕ β ⊕ γ → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter fun a => P (Sum.inl a)).card +
        (Finset.univ.filter fun b => P (Sum.inr (Sum.inl b))).card +
          (Finset.univ.filter fun c => P (Sum.inr (Sum.inr c))).card := by
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  ring

theorem satCount_eq_score_proof {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : satCount G z = score G z := by
  have h := card_filter_sum_proof
    (fun c : ClauseIdx n m => Clause.satisfied z (clauseOf G c) = true)
  have hU : (Finset.univ.filter fun v : Fin n =>
      Clause.satisfied z (clauseOf G (Sum.inl v)) = true).card =
        (selectedVertices z).card := by
    apply congrArg Finset.card
    ext v
    cases ha : z v 0 <;> simp [selectedVertices, clauseOf, Clause.satisfied, Lit.eval, ha]
  have hE : (Finset.univ.filter fun e : Fin m =>
      Clause.satisfied z (clauseOf G (Sum.inr (Sum.inl e))) = true).card =
        m - (falseEdges G z).card := by
    have hset : (Finset.univ.filter fun e : Fin m =>
        Clause.satisfied z (clauseOf G (Sum.inr (Sum.inl e))) = true) =
          (falseEdges G z)ᶜ := by
      ext e
      cases ha : z (G.left e) (edgeClone (G.leftPort e)) <;>
        cases hb : z (G.right e) (edgeClone (G.rightPort e)) <;>
          simp [falseEdges, clauseOf, Clause.satisfied, Lit.eval, ha, hb]
    rw [hset, Finset.card_compl]
    simp
  have hC : (Finset.univ.filter fun p : Fin n × Fin 4 =>
      Clause.satisfied z (clauseOf G (Sum.inr (Sum.inr p))) = true).card =
        4 * n - (transitionPairs z).card := by
    have hset : (Finset.univ.filter fun p : Fin n × Fin 4 =>
        Clause.satisfied z (clauseOf G (Sum.inr (Sum.inr p))) = true) =
          (transitionPairs z)ᶜ := by
      ext ⟨v, i⟩
      cases ha : z v i <;> cases hb : z v (i + 1) <;>
        simp [transitionPairs, transition, clauseOf, Clause.satisfied, Lit.eval, ha, hb]
    rw [hset, Finset.card_compl, Fintype.card_prod]
    simp [Nat.mul_comm]
  unfold satCount score
  omega

theorem optimum_identity_proof {n m alpha : ℕ} (G : PortGraph n m)
    (halpha : IsIndependenceNumber G alpha) :
    IsGreatest (Set.range (satCount G)) (4 * n + m + alpha) := by
  obtain ⟨hle, z, hz⟩ := PalomaMax2SAT.CubicPublic.exact_three_occurrence_identity G halpha
  refine ⟨⟨z, ?_⟩, ?_⟩
  · rw [satCount_eq_score_proof]
    exact hz
  · rintro _ ⟨w, rfl⟩
    rw [satCount_eq_score_proof]
    exact hle w

theorem formula_horn_proof {n m : ℕ} (G : PortGraph n m) (c : ClauseIdx n m) :
    IsHorn (clauseOf G c) := by
  rcases c with v | e | ⟨v, i⟩ <;> simp [IsHorn, clauseOf]

theorem formula_size_proof (n m : ℕ) :
    Fintype.card (ClauseIdx n m) = 5 * n + m := by
  show Fintype.card (Fin n ⊕ Fin m ⊕ (Fin n × Fin 4)) = 5 * n + m
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

private theorem ite_pair_zero {A B : Prop} [Decidable A] [Decidable B]
    (hA : ¬ A) (hB : ¬ B) :
    (if A then (1 : ℕ) else 0) + (if B then 1 else 0) = 0 := by
  simp [hA, hB]

private theorem ite_pair_left {A B : Prop} [Decidable A] [Decidable B]
    (hA : A) (hB : ¬ B) :
    (if A then (1 : ℕ) else 0) + (if B then 1 else 0) = 1 := by
  simp [hA, hB]

private theorem ite_pair_right {A B : Prop} [Decidable A] [Decidable B]
    (hA : ¬ A) (hB : B) :
    (if A then (1 : ℕ) else 0) + (if B then 1 else 0) = 1 := by
  simp [hA, hB]

theorem three_occurrences_proof {n m : ℕ} (G : PortGraph n m)
    (x : Fin n × Fin 4) : occurrences G x = 3 := by
  obtain ⟨w, j⟩ := x
  have hC : ∑ p : Fin n × Fin 4,
      Clause.count (w, j) (clauseOf G (Sum.inr (Sum.inr p))) = 2 := by
    have h1 : ∑ p : Fin n × Fin 4,
        Clause.count (w, j) (clauseOf G (Sum.inr (Sum.inr p))) =
          ∑ p : Fin n × Fin 4, ((if p = (w, j) then 1 else 0) +
            (if (p.1, p.2 + 1) = (w, j) then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      simp [clauseOf, Clause.count]
    rw [h1, Finset.sum_add_distrib]
    have h2 : ∑ p : Fin n × Fin 4, (if p = (w, j) then 1 else 0) = 1 := by
      simp
    have h3 : ∑ p : Fin n × Fin 4,
        (if (p.1, p.2 + 1) = (w, j) then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single (w, j - 1)]
      · simp
      · intro p _ hp
        have hne : ¬ ((p.1, p.2 + 1) = (w, j)) := by
          intro h
          apply hp
          have h1' : p.1 = w := congrArg Prod.fst h
          have h2' : p.2 + 1 = j := congrArg Prod.snd h
          exact Prod.ext h1' (eq_sub_of_add_eq h2')
        simp [hne]
      · intro h
        exact absurd (Finset.mem_univ _) h
    omega
  have hU : ∑ v : Fin n, Clause.count (w, j) (clauseOf G (Sum.inl v)) =
      if j = 0 then 1 else 0 := by
    have h1 : ∑ v : Fin n, Clause.count (w, j) (clauseOf G (Sum.inl v)) =
        ∑ v : Fin n, (if (v, (0 : Fin 4)) = (w, j) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      simp [clauseOf, Clause.count]
    rw [h1]
    by_cases hj : j = 0
    · subst hj
      simp
    · have hne : ∀ v : Fin n, ¬ ((v, (0 : Fin 4)) = (w, j)) := fun v h =>
        hj (congrArg Prod.snd h).symm
      simp [hne, hj]
  have hE : ∑ e : Fin m, Clause.count (w, j) (clauseOf G (Sum.inr (Sum.inl e))) =
      if j = 0 then 0 else 1 := by
    have hterm : ∀ e : Fin m,
        Clause.count (w, j) (clauseOf G (Sum.inr (Sum.inl e))) =
          (if (G.left e, edgeClone (G.leftPort e)) = (w, j) then 1 else 0) +
            (if (G.right e, edgeClone (G.rightPort e)) = (w, j) then 1 else 0) := by
      intro e
      simp [clauseOf, Clause.count]
    rw [Finset.sum_congr rfl (fun e _ => hterm e)]
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨p0, hj⟩
    · subst hj
      simp [edgeClone, Fin.succ_ne_zero]
    · subst hj
      have hcond : ∀ (a : Fin n) (q : Fin 3),
          ((a, edgeClone q) = (w, p0.succ)) ↔ (a = w ∧ q = p0) := by
        intro a q
        simp [edgeClone]
      simp only [hcond]
      rw [show ((if p0.succ = 0 then 0 else 1 : ℕ)) = 1 by
        simp [Fin.succ_ne_zero]]
      rcases G.port_occupied w p0 with ⟨e0, h0l, h0p⟩ | ⟨e0, h0r, h0p⟩
      · rw [Finset.sum_eq_single e0]
        · exact ite_pair_left ⟨h0l, h0p⟩ (fun ⟨hr, hrp⟩ =>
            G.cross_unique e0 e0 (h0l.trans hr.symm) (h0p.trans hrp.symm))
        · intro e _ hne
          exact ite_pair_zero
            (fun ⟨hl, hlp⟩ =>
              hne (G.left_unique e e0 (hl.trans h0l.symm) (hlp.trans h0p.symm)))
            (fun ⟨hr, hrp⟩ =>
              G.cross_unique e0 e (h0l.trans hr.symm) (h0p.trans hrp.symm))
        · intro h
          exact absurd (Finset.mem_univ e0) h
      · rw [Finset.sum_eq_single e0]
        · exact ite_pair_right
            (fun ⟨hl, hlp⟩ =>
              G.cross_unique e0 e0 (hl.trans h0r.symm) (hlp.trans h0p.symm))
            ⟨h0r, h0p⟩
        · intro e _ hne
          exact ite_pair_zero
            (fun ⟨hl, hlp⟩ =>
              G.cross_unique e e0 (hl.trans h0r.symm) (hlp.trans h0p.symm))
            (fun ⟨hr, hrp⟩ =>
              hne (G.right_unique e e0 (hr.trans h0r.symm) (hrp.trans h0p.symm)))
        · intro h
          exact absurd (Finset.mem_univ e0) h
  have h1 := Fintype.sum_sum_type
    (fun c : ClauseIdx n m => Clause.count (w, j) (clauseOf G c))
  have h2 := Fintype.sum_sum_type
    (fun s : Fin m ⊕ (Fin n × Fin 4) => Clause.count (w, j) (clauseOf G (Sum.inr s)))
  unfold occurrences
  rw [h1, h2, hU, hE, hC]
  by_cases hj : j = 0 <;> simp [hj]

end PalomaMax2SAT.SemanticHorn

namespace PalomaMax2SAT.SemanticPublic

open PalomaMax2SAT.CubicThreeOccurrence PalomaMax2SAT.SemanticHorn

/-- The number of satisfied clauses of the formula `T_H` equals the score. -/
theorem satCount_eq_score {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : satCount G z = score G z := by
  exact satCount_eq_score_proof G z

/-- `OPT(T_H) = 4n + m + alpha(H)`, stated for the clause semantics. -/
theorem optimum_identity {n m alpha : ℕ} (G : PortGraph n m)
    (halpha : IsIndependenceNumber G alpha) :
    IsGreatest (Set.range (satCount G)) (4 * n + m + alpha) := by
  exact optimum_identity_proof G halpha

/-- Every clause of `T_H` is Horn. -/
theorem formula_horn {n m : ℕ} (G : PortGraph n m) (c : ClauseIdx n m) :
    IsHorn (clauseOf G c) := by
  exact formula_horn_proof G c

/-- `T_H` has `5n + m` clauses. -/
theorem formula_size (n m : ℕ) :
    Fintype.card (ClauseIdx n m) = 5 * n + m := by
  exact formula_size_proof n m

/-- Every variable of `T_H` occurs exactly three times. -/
theorem three_occurrences {n m : ℕ} (G : PortGraph n m)
    (x : Fin n × Fin 4) : occurrences G x = 3 := by
  exact three_occurrences_proof G x

end PalomaMax2SAT.SemanticPublic

namespace PalomaMax2SAT.GraphTransfer
open PalomaMax2SAT.HardOccurrenceSplit

theorem hardImage_ratio (W a s : ℕ) (hw : 12*a ≤ W) (hs : 17*a ≤ 20*s) :
    260*(W+s) ≥ 257*(W+a) := by omega

open PalomaMax2SAT.CubicThreeOccurrence

/-- The hard cycle is a feasibility condition. Only units and edges earn weight. -/
noncomputable def fourScore {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : ℕ :=
  (selectedVertices z).card + 4 * (m - (falseEdges G z).card)

theorem fourScore_repair {n m : ℕ} (G : PortGraph n m) (z : Fin n → Fin 4 → Bool)
    (hz : transitionPairs z = ∅) :
    fourScore G z ≤ 4*m + (repairedSet G z).card := by
  have h := PalomaMax2SAT.CubicPublic.repairedSet_card_lower_bound G z
  simp only [score, hz, Finset.card_empty, Nat.sub_zero] at h
  unfold fourScore
  omega

theorem canonical_fourScore {n m : ℕ} (G : PortGraph n m)
    (I : Finset (Fin n)) (hI : Independent G I) :
    transitionPairs (assignmentOfIndependent I) = ∅ ∧
    fourScore G (assignmentOfIndependent I) = 4*m + I.card := by
  classical
  have hselected : selectedVertices (assignmentOfIndependent I) = I := by
    ext v
    simp [selectedVertices, assignmentOfIndependent]
  have hfalse : falseEdges G (assignmentOfIndependent I) = ∅ := by
    ext e
    simp [falseEdges, assignmentOfIndependent, hI e]
  constructor
  · ext pair
    simp [transitionPairs, transition, assignmentOfIndependent]
  · simp [fourScore, hselected, hfalse, Nat.add_comm]

theorem exact_fourScore {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (fourScore G) (4*m+a) := by
  constructor
  · intro z hz
    have hu := fourScore_repair G z hz
    have hi := ha.1 _ (PalomaMax2SAT.CubicPublic.repairedSet_independent G z)
    omega
  · obtain ⟨I, hi, hc⟩ := ha.2
    exact ⟨assignmentOfIndependent I, (canonical_fourScore G I hi).1,
      by rw [(canonical_fourScore G I hi).2, hc]⟩

theorem hardFour_transfer {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (I : Finset (Fin n)) (hi : Independent G I) (hs : 17*a ≤ 20*I.card) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (fourScore G) (4*m+a) ∧
    transitionPairs (assignmentOfIndependent I) = ∅ ∧
    260*fourScore G (assignmentOfIndependent I) ≥ 257*(4*m+a) := by
  obtain ⟨hz, hval⟩ := canonical_fourScore G I hi
  refine ⟨exact_fourScore G ha, hz, ?_⟩
  rw [hval]
  exact hardImage_ratio (4*m) a I.card (by omega) hs


private theorem unitCanonicalSoft {n m : ℕ} (G : PortGraph n m)
    (I : Finset (Fin n)) (hi : Independent G I) :
    score G (assignmentOfIndependent I) = 4*n+m+I.card := by
  have hz := (canonical_fourScore G I hi).1
  have hselected : selectedVertices (assignmentOfIndependent I) = I := by
    ext v
    simp [selectedVertices, assignmentOfIndependent]
  have hfalse : falseEdges G (assignmentOfIndependent I) = ∅ := by
    ext e
    simp [falseEdges, assignmentOfIndependent, hi e]
  simp only [score, hselected, hfalse, hz, Finset.card_empty, Nat.sub_zero]
  omega

/-- Original unit weights, with all implications mandatory and unscored. -/
noncomputable def unitScore {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : ℕ :=
  (selectedVertices z).card + (m - (falseEdges G z).card)

theorem exact_unitScore {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (unitScore G) (m+a) := by
  constructor
  · intro z hz
    have hu := PalomaMax2SAT.CubicPublic.repairedSet_card_lower_bound G z
    have hi := ha.1 _ (PalomaMax2SAT.CubicPublic.repairedSet_independent G z)
    simp only [score, hz, Finset.card_empty, Nat.sub_zero] at hu
    unfold unitScore
    omega
  · obtain ⟨I, hi, hc⟩ := ha.2
    have hz := (canonical_fourScore G I hi).1
    have hv := unitCanonicalSoft G I hi
    simp only [score, hz, Finset.card_empty, Nat.sub_zero] at hv
    exact ⟨assignmentOfIndependent I, hz, by unfold unitScore; omega⟩

theorem hardUnit_transfer {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (I : Finset (Fin n)) (hi : Independent G I) (hs : 17*a ≤ 20*I.card) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (unitScore G) (m+a) ∧
    transitionPairs (assignmentOfIndependent I) = ∅ ∧
    80*unitScore G (assignmentOfIndependent I) ≥ 77*(m+a) := by
  have hz := (canonical_fourScore G I hi).1
  have hv := unitCanonicalSoft G I hi
  simp only [score, hz, Finset.card_empty, Nat.sub_zero] at hv
  refine ⟨exact_unitScore G ha, hz, ?_⟩
  unfold unitScore
  omega

/-- Arithmetic only: assuming `s` meets one of the two stated numerical
guarantees (supplied by an external independent-set algorithm), the unit-weight
hard-split score satisfies `28*(m+s) ≥ 27*(m+a)`. Lean does not prove that an
algorithm attains either guarantee. -/
theorem unit_endpoint_arithmetic (n m a s : ℕ)
    (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (h : 6*a ≤ 7*s ∨ (20000*a ≤ 9999*n ∧ 5999993*a ≤ 7000000*s)) :
    28*(m+s) ≥ 27*(m+a) := by
  rcases h with h | ⟨h₁,h₂⟩ <;> omega

/-- Two-branch bridge for the conditional `27/28` bound. The hypotheses are
exactly the guarantees required from the external branches, with `n` the number
of vertices and `s` the size of the independent set returned: when
`2*a/n ≤ 9999/10000` the Berman--Fujito branch is assumed to return
`s ≥ (6/7 - 10^{-6}) * a`, and otherwise the near-bipartite cut branch is
assumed to return `s ≥ 37*n/80`. Lean proves only that these two guarantees
imply `28*(m+s) ≥ 27*(m+a)`; it does not prove that either algorithm attains
its guarantee. -/
theorem unit_endpoint_two_branch (n m a s : ℕ)
    (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (hBF : 20000*a ≤ 9999*n → 5999993*a ≤ 7000000*s)
    (hNB : 9999*n < 20000*a → 37*n ≤ 80*s) :
    28*(m+s) ≥ 27*(m+a) := by
  by_cases h : 20000*a ≤ 9999*n
  · have := hBF h
    omega
  · have := hNB (by omega)
    omega

end PalomaMax2SAT.GraphTransfer
