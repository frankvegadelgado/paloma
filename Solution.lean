module

public import PalomaMax2SAT

public section

namespace PalomaMax2SAT

theorem exactMax2SATIdentity {N q K opt : ℕ} (φ : Instance N q)
    (hopt : IsMAX2SATOptimum φ opt) :
    IsMaximumScore (K := K) φ (N + K * opt) := by
  exact exactMax2SATIdentity_proof φ hopt

theorem satisfiable_iff_optimum_eq_clauseCount {N q opt : ℕ}
    (φ : Instance N q) (hopt : IsMAX2SATOptimum φ opt) :
    Satisfiable φ ↔ opt = q := by
  exact satisfiable_iff_optimum_eq_clauseCount_proof φ hopt

theorem satisfiable_iff_target {N q K opt : ℕ} (φ : Instance N q)
    (hopt : IsMAX2SATOptimum φ opt) (hK : 0 < K) :
    Satisfiable φ ↔ N + K * opt = N + K * q := by
  exact satisfiable_iff_target_proof φ hopt hK

theorem conditionalUnsatOfRatioGap {N q K score graphOrder a b : ℕ}
    (φ : Instance N q)
    (hratio : Satisfiable φ →
      (N + K * q) ^ b ≤ score ^ b * graphOrder ^ (b - a))
    (hgap : score ^ b * graphOrder ^ (b - a) < (N + K * q) ^ b) :
    ¬ Satisfiable φ := by
  exact conditionalUnsatOfRatioGap_proof φ hratio hgap

theorem binaryClauseReward_truthTable (left right : Bool) :
    binaryClauseReward left right = 1 ↔ left = true ∨ right = true := by
  exact binaryClauseReward_truthTable_proof left right

theorem exhaustiveAuditCount :
    2 * (∑ clauseCount ∈ Finset.range 4, 10 ^ clauseCount) = 2222 := by
  exact exhaustiveAuditCount_proof

theorem exhaustiveSmallGadgetSearch :
    clauseORGadgetCount 1 0 = 0 ∧ clauseORGadgetCount 1 1 = 1 ∧
    clauseORGadgetCount 2 0 = 0 ∧ clauseORGadgetCount 2 1 = 0 ∧
      clauseORGadgetCount 2 2 = 2 ∧
    clauseORGadgetCount 3 0 = 0 ∧ clauseORGadgetCount 3 1 = 0 ∧
      clauseORGadgetCount 3 2 = 0 ∧ clauseORGadgetCount 3 3 = 6 := by
  exact exhaustiveSmallGadgetSearch_proof

end PalomaMax2SAT
