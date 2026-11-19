module

public import Mathlib

public section

/-!
# Exact MAX-2SAT assignment--witness identity

This module gives a finite, executable semantics for MAX-2SAT and formalizes
the normal form of an independent set in the assignment--witness
conflict graph.  The decoded assignment is constructed from witness
consistency and assignment--witness compatibility; witness validity is proved,
not stored as an assumption.

The main theorem proves the exact optimum

`N + K * OPT_MAX2SAT φ`.

The development also proves the satisfiability threshold, the sound
conditional ratio test, the binary-clause truth table, and the exact cardinality
of the exhaustive two-variable audit used by the companion Python experiment.
-/

namespace PalomaMax2SAT

/-- A literal is a variable together with the value that makes it true. -/
abbrev Literal (N : ℕ) := Fin N × Bool

/-- A MAX-2SAT instance with `N` variables and `q` clauses. -/
structure Instance (N q : ℕ) where
  clause : Fin q → Finset (Literal N)
  width_two : ∀ j, (clause j).card ≤ 2

/-- Evaluation of one signed literal. -/
abbrev EvalLiteral (assignment : Fin N → Bool) (literal : Literal N) : Prop :=
  assignment literal.1 = literal.2

instance (assignment : Fin N → Bool) (literal : Literal N) :
    Decidable (EvalLiteral assignment literal) := inferInstance

/-- A clause is satisfied when one of its literals evaluates to true. -/
abbrev SatisfiesClause {N q : ℕ} (φ : Instance N q)
    (assignment : Fin N → Bool) (j : Fin q) : Prop :=
  ∃ literal ∈ φ.clause j, EvalLiteral assignment literal

instance {N q : ℕ} (φ : Instance N q) (assignment : Fin N → Bool) (j : Fin q) :
    Decidable (SatisfiesClause φ assignment j) := inferInstance

/-- The finite set of clauses satisfied by an assignment. -/
def satisfiedClauses {N q : ℕ} (φ : Instance N q)
    (assignment : Fin N → Bool) : Finset (Fin q) :=
  Finset.univ.filter (SatisfiesClause φ assignment)

/-- Number of clauses satisfied by an assignment. -/
abbrev satCount {N q : ℕ} (φ : Instance N q)
    (assignment : Fin N → Bool) : ℕ :=
  (satisfiedClauses φ assignment).card

/-- `opt` is the exact MAX-2SAT optimum. -/
def IsMAX2SATOptimum {N q : ℕ} (φ : Instance N q) (opt : ℕ) : Prop :=
  (∀ assignment, satCount φ assignment ≤ opt) ∧
    ∃ assignment, satCount φ assignment = opt

/-- Satisfiability means that one assignment satisfies every clause. -/
def Satisfiable {N q : ℕ} (φ : Instance N q) : Prop :=
  ∃ assignment, satCount φ assignment = q

/--
Independent-set data for the assignment--witness conflict graph.

There is at most one selected assignment value per variable and at most one
selected literal per clause-copy because those selections are indexed by
finite sets. `witness_consistent` excludes complementary selected witnesses;
`assignment_compatible` excludes a witness together with the assignment value
that falsifies it. These are precisely the nontrivial conflict edges after
forgetting irrelevant occurrence labels.
-/
structure GraphIndependentSet {N q : ℕ} (φ : Instance N q) (K : ℕ) where
  selectedAssignments : Finset (Fin N)
  assignmentValue : Fin N → Bool
  chosen : Finset (Fin q × Fin K)
  witnessLiteral : {pair // pair ∈ chosen} → Literal N
  witness_mem : ∀ pair, witnessLiteral pair ∈ φ.clause pair.1.1
  witness_consistent : ∀ left right,
    (witnessLiteral left).1 = (witnessLiteral right).1 →
      (witnessLiteral left).2 = (witnessLiteral right).2
  assignment_compatible : ∀ i, i ∈ selectedAssignments → ∀ pair,
    i = (witnessLiteral pair).1 →
      assignmentValue i = (witnessLiteral pair).2

/-- Cardinality of the represented graph-independent set. -/
def independentScore {N q K : ℕ} {φ : Instance N q}
    (independent : GraphIndependentSet φ K) : ℕ :=
  independent.selectedAssignments.card + independent.chosen.card

/-- `target` is attained and bounds every graph-independent set. -/
def IsMaximumScore {N q K : ℕ} (φ : Instance N q) (target : ℕ) : Prop :=
  (∃ independent : GraphIndependentSet φ K,
      independentScore independent = target) ∧
  ∀ independent : GraphIndependentSet φ K,
      independentScore independent ≤ target

/-- Decode a total assignment, preferring the unique consistent witness sign. -/
noncomputable def decodedAssignment {N q K : ℕ} {φ : Instance N q}
    (independent : GraphIndependentSet φ K) (i : Fin N) : Bool :=
  if h : ∃ pair : {pair // pair ∈ independent.chosen},
      (independent.witnessLiteral pair).1 = i then
    (independent.witnessLiteral (Classical.choose h)).2
  else
    independent.assignmentValue i

/-- Every selected witness is true under the decoded assignment. -/
theorem decodedAssignment_satisfies_witness {N q K : ℕ} {φ : Instance N q}
    (independent : GraphIndependentSet φ K)
    (pair : {pair // pair ∈ independent.chosen}) :
    EvalLiteral (decodedAssignment independent) (independent.witnessLiteral pair) := by
  let h : ∃ other : {other // other ∈ independent.chosen},
      (independent.witnessLiteral other).1 =
        (independent.witnessLiteral pair).1 := ⟨pair, rfl⟩
  unfold EvalLiteral
  unfold decodedAssignment
  rw [dite_eq_left h]
  exact independent.witness_consistent (Classical.choose h) pair
    (Classical.choose_spec h)

/-- Completion preserves every assignment vertex already in the set. -/
theorem decodedAssignment_agrees_selected {N q K : ℕ} {φ : Instance N q}
    (independent : GraphIndependentSet φ K) (i : Fin N)
    (hi : i ∈ independent.selectedAssignments) :
    decodedAssignment independent i = independent.assignmentValue i := by
  unfold decodedAssignment
  split
  · rename_i h
    symm
    exact independent.assignment_compatible i hi (Classical.choose h)
      (Classical.choose_spec h).symm
  · rfl

private theorem chosen_subset_satisfied_product {N q K : ℕ}
    {φ : Instance N q} (independent : GraphIndependentSet φ K) :
    independent.chosen ⊆
      (satisfiedClauses φ (decodedAssignment independent)).product Finset.univ := by
  intro pair hpair
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    let selected : {pair // pair ∈ independent.chosen} := ⟨pair, hpair⟩
    exact ⟨independent.witnessLiteral selected,
      independent.witness_mem selected,
      decodedAssignment_satisfies_witness independent selected⟩
  · exact Finset.mem_univ _

/-- Every independent set is bounded by its formally decoded assignment. -/
theorem independentScore_le_decodedAssignment {N q K : ℕ} {φ : Instance N q}
    (independent : GraphIndependentSet φ K) :
    independentScore independent ≤
      N + K * satCount φ (decodedAssignment independent) := by
  have hassign : independent.selectedAssignments.card ≤ N := by
    simpa using Finset.card_le_univ independent.selectedAssignments
  have hwitness : independent.chosen.card ≤
      satCount φ (decodedAssignment independent) * K := by
    have hsubset := Finset.card_le_card (chosen_subset_satisfied_product independent)
    simpa using hsubset
  calc
    independentScore independent
        ≤ N + satCount φ (decodedAssignment independent) * K :=
          Nat.add_le_add hassign hwitness
    _ = N + K * satCount φ (decodedAssignment independent) := by
      rw [Nat.mul_comm]

/-- The exact assignment--witness optimum identity. -/
theorem exactMax2SATIdentity_proof {N q K opt : ℕ} (φ : Instance N q)
    (hopt : IsMAX2SATOptimum φ opt) :
    IsMaximumScore (K := K) φ (N + K * opt) := by
  constructor
  · obtain ⟨assignment, hassignment⟩ := hopt.2
    let independent : GraphIndependentSet φ K := {
      selectedAssignments := Finset.univ
      assignmentValue := assignment
      chosen := (satisfiedClauses φ assignment).product Finset.univ
      witnessLiteral := fun pair =>
        Classical.choose
          ((Finset.mem_filter.mp (Finset.mem_product.mp pair.property).1).2)
      witness_mem := by
        intro pair
        exact (Classical.choose_spec
          ((Finset.mem_filter.mp (Finset.mem_product.mp pair.property).1).2)).1
      witness_consistent := by
        intro left right hvariable
        have hleft := (Classical.choose_spec
          ((Finset.mem_filter.mp (Finset.mem_product.mp left.property).1).2)).2
        have hright := (Classical.choose_spec
          ((Finset.mem_filter.mp (Finset.mem_product.mp right.property).1).2)).2
        unfold EvalLiteral at hleft hright
        calc
          _ = assignment (Classical.choose
              ((Finset.mem_filter.mp (Finset.mem_product.mp left.property).1).2)).1 :=
                hleft.symm
          _ = assignment (Classical.choose
              ((Finset.mem_filter.mp (Finset.mem_product.mp right.property).1).2)).1 := by
                rw [hvariable]
          _ = _ := hright
      assignment_compatible := by
        intro i _ pair hi
        have htrue := (Classical.choose_spec
          ((Finset.mem_filter.mp (Finset.mem_product.mp pair.property).1).2)).2
        unfold EvalLiteral at htrue
        simpa [hi] using htrue
    }
    refine ⟨independent, ?_⟩
    simp [independentScore, independent, hassignment, Nat.mul_comm]
  · intro independent
    calc
      independentScore independent
          ≤ N + K * satCount φ (decodedAssignment independent) :=
            independentScore_le_decodedAssignment independent
      _ ≤ N + K * opt :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_left K (hopt.1 (decodedAssignment independent))) N

/-- No assignment can satisfy more than all `q` clauses. -/
theorem satCount_le_clauseCount {N q : ℕ} (φ : Instance N q)
    (assignment : Fin N → Bool) : satCount φ assignment ≤ q := by
  simpa using Finset.card_le_univ (satisfiedClauses φ assignment)

/-- An exact optimum equals `q` exactly when the MAX-2SAT instance is satisfiable. -/
theorem satisfiable_iff_optimum_eq_clauseCount_proof {N q opt : ℕ}
    (φ : Instance N q) (hopt : IsMAX2SATOptimum φ opt) :
    Satisfiable φ ↔ opt = q := by
  constructor
  · rintro ⟨assignment, hall⟩
    have hqopt : q ≤ opt := by simpa [hall] using hopt.1 assignment
    obtain ⟨best, hbest⟩ := hopt.2
    have hoptq : opt ≤ q := by simpa [hbest] using satCount_le_clauseCount φ best
    omega
  · intro h
    obtain ⟨assignment, hassignment⟩ := hopt.2
    exact ⟨assignment, hassignment.trans h⟩

/-- The exact graph target `N + Kq` characterizes satisfiability for `K > 0`. -/
theorem satisfiable_iff_target_proof {N q K opt : ℕ} (φ : Instance N q)
    (hopt : IsMAX2SATOptimum φ opt) (hK : 0 < K) :
    Satisfiable φ ↔ N + K * opt = N + K * q := by
  rw [satisfiable_iff_optimum_eq_clauseCount_proof φ hopt]
  constructor
  · intro h
    simp [h]
  · intro h
    apply Nat.eq_of_mul_eq_mul_left hK
    exact Nat.add_left_cancel h

/--
Exact integer form of the conditional approximation test.  If satisfiability
would force the ratio inequality but the observed score violates it, the
formula is unsatisfiable under that ratio hypothesis.
-/
theorem conditionalUnsatOfRatioGap_proof {N q K score graphOrder a b : ℕ}
    (φ : Instance N q)
    (hratio : Satisfiable φ →
      (N + K * q) ^ b ≤ score ^ b * graphOrder ^ (b - a))
    (hgap : score ^ b * graphOrder ^ (b - a) < (N + K * q) ^ b) :
    ¬ Satisfiable φ := by
  intro hsat
  exact (not_le_of_gt hgap) (hratio hsat)

/-- Reward of the canonical binary-clause witness edge. -/
def binaryClauseReward (left right : Bool) : ℕ :=
  if left || right then 1 else 0

/-- The canonical binary gadget contributes one witness iff the clause is true. -/
theorem binaryClauseReward_truthTable_proof (left right : Bool) :
    binaryClauseReward left right = 1 ↔ left = true ∨ right = true := by
  cases left <;> cases right <;> decide

/--
The independent audit uses ten nonempty width-one/two clauses over four signed
literals, ordered formula lengths zero through three, and two multiplicities.
-/
theorem exhaustiveAuditCount_proof :
    2 * (∑ clauseCount ∈ Finset.range 4, 10 ^ clauseCount) = 2222 := by
  norm_num [Finset.sum_range_succ]

/-! ## Executable exhaustive search for the local OR gadget -/

/-- Number of possible undirected internal edges on `auxiliary` labelled vertices. -/
def internalBitCount (auxiliary : ℕ) : ℕ := auxiliary * (auxiliary - 1) / 2

/-- Index of the unordered pair `left < right` in lexicographic upper-triangle order. -/
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

/-- Maximum available independent auxiliary reward for one false-terminal mask. -/
def gadgetReward (arity auxiliary encoding falseTerminals : ℕ) : ℕ :=
  (Finset.range (2 ^ auxiliary)).sup fun subset =>
    if gadgetSubsetFeasible arity auxiliary encoding falseTerminals subset
    then subsetCard auxiliary subset
    else 0

/-- Reward rises by one exactly when at least one clause literal is true. -/
abbrev RealizesClauseOR (arity auxiliary encoding : ℕ) : Prop :=
  let allFalse := 2 ^ arity - 1
  let baseline := gadgetReward arity auxiliary encoding allFalse
  ∀ falseTerminals ∈ Finset.range (2 ^ arity),
    gadgetReward arity auxiliary encoding falseTerminals =
      baseline + if falseTerminals = allFalse then 0 else 1

instance (arity auxiliary encoding : ℕ) :
    Decidable (RealizesClauseOR arity auxiliary encoding) := inferInstance

/-- Number of labelled internal-graph/attachment encodings realizing clause OR. -/
def clauseORGadgetCount (arity auxiliary : ℕ) : ℕ :=
  let bits := internalBitCount auxiliary + auxiliary * arity
  ((Finset.range (2 ^ bits)).filter (RealizesClauseOR arity auxiliary)).card

/--
Complete finite search through arity three: no smaller gadget exists, and the
minimum labelled counts are `1,2,6`, i.e. the occurrence clique with one-to-one
falsifying-terminal attachments up to auxiliary-vertex relabelling.
-/
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem exhaustiveSmallGadgetSearch_proof :
    clauseORGadgetCount 1 0 = 0 ∧ clauseORGadgetCount 1 1 = 1 ∧
    clauseORGadgetCount 2 0 = 0 ∧ clauseORGadgetCount 2 1 = 0 ∧
      clauseORGadgetCount 2 2 = 2 ∧
    clauseORGadgetCount 3 0 = 0 ∧ clauseORGadgetCount 3 1 = 0 ∧
      clauseORGadgetCount 3 2 = 0 ∧ clauseORGadgetCount 3 3 = 6 := by
  decide

end PalomaMax2SAT
