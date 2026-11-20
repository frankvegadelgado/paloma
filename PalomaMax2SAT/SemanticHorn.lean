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
def clauseOf {n m : ℕ} (G : PortGraph n m) : ClauseIdx n m → Clause n
  | Sum.inl v => [Lit.mk (v, 0) false]
  | Sum.inr (Sum.inl e) =>
      [Lit.mk (G.left e, edgeClone (G.leftPort e)) true,
        Lit.mk (G.right e, edgeClone (G.rightPort e)) true]
  | Sum.inr (Sum.inr (v, i)) => [Lit.mk (v, i) false, Lit.mk (v, i + 1) true]

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
  obtain ⟨hle, z, hz⟩ := exact_three_occurrence_identity_proof G halpha
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

end PalomaMax2SAT.SemanticHorn
