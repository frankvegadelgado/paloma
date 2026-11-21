module

public import Mathlib
public import PalomaMax2SAT.CubicThreeOccurrence

@[expose] public section

/-!
# The formula `T_H` as an explicit MAX-HORN-2SAT instance

Clauses are lists of literals over the clone variables; the number of satisfied
clauses is shown to equal the score used in `CubicThreeOccurrence`.
-/

namespace PalomaMax2SAT.SemanticHorn

open PalomaMax2SAT.CubicThreeOccurrence

/-- A named `NeZero 4` instance. Numerals of `Fin 4` in this namespace then carry this constant
instead of a nested proof term, whose auxiliary lemma name depends on the position in the file. -/
local instance (priority := high) neZeroFour : NeZero (4 : ℕ) := ⟨by decide⟩

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
def unitClause {n : ℕ} (v : Fin n) : Clause n :=
  [Lit.mk (v, 0) false]

/-- The edge clause `(z u p ∨ z w q)` of the edge `e`. -/
def edgeClause {n m : ℕ} (G : PortGraph n m) (e : Fin m) : Clause n :=
  [Lit.mk (G.left e, edgeClone (G.leftPort e)) true,
    Lit.mk (G.right e, edgeClone (G.rightPort e)) true]

/-- The consistency implication `(¬ z v i ∨ z v (i+1))`. -/
def consClause {n : ℕ} (p : Fin n × Fin 4) : Clause n :=
  [Lit.mk p false, Lit.mk (p.1, p.2 + 1) true]

def clauseOf {n m : ℕ} (G : PortGraph n m) : ClauseIdx n m → Clause n :=
  Sum.elim unitClause (Sum.elim (edgeClause G) consClause)

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
    cases ha : z v 0 <;> simp [selectedVertices, clauseOf, unitClause, Clause.satisfied, Lit.eval, ha]
  have hE : (Finset.univ.filter fun e : Fin m =>
      Clause.satisfied z (clauseOf G (Sum.inr (Sum.inl e))) = true).card =
        m - (falseEdges G z).card := by
    have hset : (Finset.univ.filter fun e : Fin m =>
        Clause.satisfied z (clauseOf G (Sum.inr (Sum.inl e))) = true) =
          (falseEdges G z)ᶜ := by
      ext e
      cases ha : z (G.left e) (edgeClone (G.leftPort e)) <;>
        cases hb : z (G.right e) (edgeClone (G.rightPort e)) <;>
          simp [falseEdges, clauseOf, edgeClause, Clause.satisfied, Lit.eval, ha, hb]
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
        simp [transitionPairs, transition, clauseOf, consClause, Clause.satisfied, Lit.eval, ha, hb]
    rw [hset, Finset.card_compl, Fintype.card_prod]
    simp [Nat.mul_comm]
  unfold satCount score
  omega

theorem optimum_identity_proof {n m alpha : ℕ} (G : PortGraph n m)
    (halpha : IsIndependenceNumber G alpha) :
    IsGreatest (Set.range (satCount G)) (4 * n + m + alpha) := by
  obtain ⟨hle, z, hz⟩ := exact_three_occurrence_identity_proof G halpha
  refine ⟨⟨z, ?_⟩, ?_⟩
  · rw [satCount_eq_score_proof]
    exact hz
  · rintro _ ⟨w, rfl⟩
    rw [satCount_eq_score_proof]
    exact hle w

theorem formula_horn_proof {n m : ℕ} (G : PortGraph n m) (c : ClauseIdx n m) :
    IsHorn (clauseOf G c) := by
  rcases c with v | e | ⟨v, i⟩ <;> simp [IsHorn, clauseOf, unitClause, edgeClause, consClause]

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
      simp [clauseOf, consClause, Clause.count]
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
      simp [clauseOf, unitClause, Clause.count]
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
      simp [clauseOf, edgeClause, Clause.count]
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
