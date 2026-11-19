module

public import PalomaMax2SAT

public section

namespace PalomaMax2SAT.WeightedSplit

theorem dominant_consistency_weight_identity {Assignment : Type}
    (C M W opt : ℕ) (sourceScore consistencyFailures : Assignment → ℕ)
    (hfail : ∀ a, consistencyFailures a ≤ C)
    (hsource : ∀ a, sourceScore a ≤ W)
    (hconsistent : ∀ a, consistencyFailures a = 0 → sourceScore a ≤ opt)
    (hattain : ∃ a, consistencyFailures a = 0 ∧ sourceScore a = opt)
    (hdominates : W < M) :
    IsWeightedSplitOptimum C M sourceScore consistencyFailures (C * M + opt) := by
  exact dominant_consistency_weight_identity_proof C M W opt sourceScore
    consistencyFailures hfail hsource hconsistent hattain hdominates

theorem dominant_baseline_18_19 (C M opt : ℕ) (hC : 18 ≤ C)
    (hopt : opt < M) :
    18 * (C * M + opt) ≤ 19 * (C * M) := by
  exact dominant_baseline_18_19_proof C M opt hC hopt

theorem ratio_18_19_exceeds_general_weighted_horn :
    (18 : ℚ) / 19 > 94615981 / 100000000 := by
  exact ratio_18_19_exceeds_general_weighted_horn_proof

end PalomaMax2SAT.WeightedSplit
