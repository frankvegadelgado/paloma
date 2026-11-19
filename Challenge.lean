module

public import Mathlib

public section

/-!
# Exact MAX-2SAT conflict-graph challenge

For each variable the graph has two adjacent assignment vertices.  For each
literal occurrence in each clause-copy it has a witness vertex.  Witnesses in
one clause-copy form a clique, complementary witnesses are adjacent, and a
witness is adjacent to the assignment value that falsifies it.

`GraphIndependentSet` is an extensional encoding of an arbitrary independent
set in this graph: finite-set indexing enforces the two clique constraints,
and its last two fields state exactly the complementary-witness and
assignment--witness nonconflict conditions.  No decoded assignment or witness
validity is assumed; the Solution constructs and proves them.
-/

namespace PalomaMax2SAT

abbrev Literal (N : ℕ) := Fin N × Bool

structure Instance (N q : ℕ) where
  clause : Fin q → Finset (Literal N)
  width_two : ∀ j, (clause j).card ≤ 2

abbrev EvalLiteral (assignment : Fin N → Bool) (literal : Literal N) : Prop :=
  assignment literal.1 = literal.2

instance (assignment : Fin N → Bool) (literal : Literal N) :
    Decidable (EvalLiteral assignment literal) := inferInstance

abbrev SatisfiesClause {N q : ℕ} (φ : Instance N q)
    (assignment : Fin N → Bool) (j : Fin q) : Prop :=
  ∃ literal ∈ φ.clause j, EvalLiteral assignment literal

instance {N q : ℕ} (φ : Instance N q) (assignment : Fin N → Bool) (j : Fin q) :
    Decidable (SatisfiesClause φ assignment j) := inferInstance

def satisfiedClauses {N q : ℕ} (φ : Instance N q)
    (assignment : Fin N → Bool) : Finset (Fin q) :=
  Finset.univ.filter (SatisfiesClause φ assignment)

def satCount {N q : ℕ} (φ : Instance N q)
    (assignment : Fin N → Bool) : ℕ :=
  (satisfiedClauses φ assignment).card

def IsMAX2SATOptimum {N q : ℕ} (φ : Instance N q) (opt : ℕ) : Prop :=
  (∀ assignment, satCount φ assignment ≤ opt) ∧
    ∃ assignment, satCount φ assignment = opt

def Satisfiable {N q : ℕ} (φ : Instance N q) : Prop :=
  ∃ assignment, satCount φ assignment = q

/-- Extensional representation of an independent set in `G_{φ,K}`. -/
structure GraphIndependentSet {N q : ℕ} (φ : Instance N q) (K : ℕ) where
  /-- Variables whose assignment vertices are selected. -/
  selectedAssignments : Finset (Fin N)
  /-- Which of the two values is selected for each selected variable. -/
  assignmentValue : Fin N → Bool
  /-- Clause-copy pairs having a selected occurrence witness. -/
  chosen : Finset (Fin q × Fin K)
  /-- The selected literal occurrence in each chosen clause-copy. -/
  witnessLiteral : {pair // pair ∈ chosen} → Literal N
  /-- Every selected occurrence belongs to its source clause. -/
  witness_mem : ∀ pair, witnessLiteral pair ∈ φ.clause pair.1.1
  /-- Complementary occurrence witnesses cannot both be selected. -/
  witness_consistent : ∀ left right,
    (witnessLiteral left).1 = (witnessLiteral right).1 →
      (witnessLiteral left).2 = (witnessLiteral right).2
  /-- A selected witness excludes its falsifying assignment value. -/
  assignment_compatible : ∀ i, i ∈ selectedAssignments → ∀ pair,
    i = (witnessLiteral pair).1 →
      assignmentValue i = (witnessLiteral pair).2

def independentScore {N q K : ℕ} {φ : Instance N q}
    (independent : GraphIndependentSet φ K) : ℕ :=
  independent.selectedAssignments.card + independent.chosen.card

def IsMaximumScore {N q K : ℕ} (φ : Instance N q) (target : ℕ) : Prop :=
  (∃ independent : GraphIndependentSet φ K,
      independentScore independent = target) ∧
  ∀ independent : GraphIndependentSet φ K,
      independentScore independent ≤ target

/-- `α(G_{φ,K}) = N + K OPT_MAX2SAT(φ)`. -/
theorem exactMax2SATIdentity {N q K opt : ℕ} (φ : Instance N q)
    (hopt : IsMAX2SATOptimum φ opt) :
    IsMaximumScore (K := K) φ (N + K * opt) := by
  sorry

theorem satisfiable_iff_optimum_eq_clauseCount {N q opt : ℕ}
    (φ : Instance N q) (hopt : IsMAX2SATOptimum φ opt) :
    Satisfiable φ ↔ opt = q := by
  constructor
  · rintro ⟨assignment, hall⟩
    have hqopt : q ≤ opt := by simpa [hall] using hopt.1 assignment
    obtain ⟨best, hbest⟩ := hopt.2
    have hoptq : opt ≤ q := by
      rw [← hbest]
      simpa [satCount] using Finset.card_le_univ (satisfiedClauses φ best)
    omega
  · intro h
    obtain ⟨assignment, hassignment⟩ := hopt.2
    exact ⟨assignment, hassignment.trans h⟩

theorem satisfiable_iff_target {N q K opt : ℕ} (φ : Instance N q)
    (hopt : IsMAX2SATOptimum φ opt) (hK : 0 < K) :
    Satisfiable φ ↔ N + K * opt = N + K * q := by
  rw [satisfiable_iff_optimum_eq_clauseCount φ hopt]
  constructor
  · intro h
    simp [h]
  · intro h
    apply Nat.eq_of_mul_eq_mul_left hK
    exact Nat.add_left_cancel h

theorem conditionalUnsatOfRatioGap {N q K score graphOrder a b : ℕ}
    (φ : Instance N q)
    (hratio : Satisfiable φ →
      (N + K * q) ^ b ≤ score ^ b * graphOrder ^ (b - a))
    (hgap : score ^ b * graphOrder ^ (b - a) < (N + K * q) ^ b) :
    ¬ Satisfiable φ := by
  intro hsat
  exact (not_le_of_gt hgap) (hratio hsat)

def binaryClauseReward (left right : Bool) : ℕ :=
  if left || right then 1 else 0

theorem binaryClauseReward_truthTable (left right : Bool) :
    binaryClauseReward left right = 1 ↔ left = true ∨ right = true := by
  cases left <;> cases right <;> decide

/-- `2(10^0+10^1+10^2+10^3)=2222` tested formula/multiplicity pairs. -/
theorem exhaustiveAuditCount :
    2 * (∑ clauseCount ∈ Finset.range 4, 10 ^ clauseCount) = 2222 := by
  norm_num [Finset.sum_range_succ]

def internalBitCount (auxiliary : ℕ) : ℕ := auxiliary * (auxiliary - 1) / 2

def internalBitIndex (auxiliary left right : ℕ) : ℕ :=
  left * (2 * auxiliary - left - 1) / 2 + (right - left - 1)

def gadgetInternalEdge (auxiliary encoding left right : ℕ) : Bool :=
  if left = right then false
  else
    let lo := min left right
    let hi := max left right
    encoding.testBit (internalBitIndex auxiliary lo hi)

def gadgetAttached (arity auxiliary encoding vertex terminal : ℕ) : Bool :=
  encoding.testBit (internalBitCount auxiliary + vertex * arity + terminal)

def subsetCard (order subset : ℕ) : ℕ :=
  ((Finset.range order).filter fun vertex => subset.testBit vertex = true).card

abbrev gadgetSubsetFeasible (arity auxiliary encoding falseTerminals subset : ℕ) : Prop :=
  (∀ vertex ∈ Finset.range auxiliary,
      subset.testBit vertex = true →
      ∀ terminal ∈ Finset.range arity,
        falseTerminals.testBit terminal = true →
          gadgetAttached arity auxiliary encoding vertex terminal = false) ∧
  (∀ left ∈ Finset.range auxiliary,
      subset.testBit left = true →
      ∀ right ∈ Finset.range auxiliary,
        subset.testBit right = true → left < right →
          gadgetInternalEdge auxiliary encoding left right = false)

instance (arity auxiliary encoding falseTerminals subset : ℕ) :
    Decidable (gadgetSubsetFeasible arity auxiliary encoding falseTerminals subset) :=
  inferInstance

def gadgetReward (arity auxiliary encoding falseTerminals : ℕ) : ℕ :=
  (Finset.range (2 ^ auxiliary)).sup fun subset =>
    if gadgetSubsetFeasible arity auxiliary encoding falseTerminals subset
    then subsetCard auxiliary subset
    else 0

abbrev RealizesClauseOR (arity auxiliary encoding : ℕ) : Prop :=
  let allFalse := 2 ^ arity - 1
  let baseline := gadgetReward arity auxiliary encoding allFalse
  ∀ falseTerminals ∈ Finset.range (2 ^ arity),
    gadgetReward arity auxiliary encoding falseTerminals =
      baseline + if falseTerminals = allFalse then 0 else 1

instance (arity auxiliary encoding : ℕ) :
    Decidable (RealizesClauseOR arity auxiliary encoding) := inferInstance

def clauseORGadgetCount (arity auxiliary : ℕ) : ℕ :=
  let bits := internalBitCount auxiliary + auxiliary * arity
  ((Finset.range (2 ^ bits)).filter (RealizesClauseOR arity auxiliary)).card

/-- Exhaustive local search: minimum auxiliary orders are `1,2,3`. -/
theorem exhaustiveSmallGadgetSearch :
    clauseORGadgetCount 1 0 = 0 ∧ clauseORGadgetCount 1 1 = 1 ∧
    clauseORGadgetCount 2 0 = 0 ∧ clauseORGadgetCount 2 1 = 0 ∧
      clauseORGadgetCount 2 2 = 2 ∧
    clauseORGadgetCount 3 0 = 0 ∧ clauseORGadgetCount 3 1 = 0 ∧
      clauseORGadgetCount 3 2 = 0 ∧ clauseORGadgetCount 3 3 = 6 := by
  native_decide

end PalomaMax2SAT
