module

public import Mathlib

public section

/-!
# Dominant weighted occurrence splitting

This module contains only the formal core of the weighted three-occurrence
MAX-HORN-2SAT image-class result. `C` is the number of clone variables and
cyclic consistency clauses, every consistency clause has weight `M`, and `W`
bounds the total source-clause weight.
-/

namespace PalomaMax2SAT.WeightedSplit

/-- Abstract objective of a split assignment. -/
def weightedSplitScore {Assignment : Type} (C M : ℕ)
    (sourceScore consistencyFailures : Assignment → ℕ) (a : Assignment) : ℕ :=
  (C - consistencyFailures a) * M + sourceScore a

/-- A number is the optimum when it is an upper bound attained by an assignment. -/
def IsWeightedSplitOptimum {Assignment : Type} (C M : ℕ)
    (sourceScore consistencyFailures : Assignment → ℕ) (target : ℕ) : Prop :=
  (∀ a, weightedSplitScore C M sourceScore consistencyFailures a ≤ target) ∧
    ∃ a, weightedSplitScore C M sourceScore consistencyFailures a = target

/-- One lost consistency clause outweighs all source clauses. -/
theorem dominant_consistency_weight_identity_proof {Assignment : Type}
    (C M W opt : ℕ) (sourceScore consistencyFailures : Assignment → ℕ)
    (hfail : ∀ a, consistencyFailures a ≤ C)
    (hsource : ∀ a, sourceScore a ≤ W)
    (hconsistent : ∀ a, consistencyFailures a = 0 → sourceScore a ≤ opt)
    (hattain : ∃ a, consistencyFailures a = 0 ∧ sourceScore a = opt)
    (hdominates : W < M) :
    IsWeightedSplitOptimum C M sourceScore consistencyFailures (C * M + opt) := by
  constructor
  · intro a
    by_cases hz : consistencyFailures a = 0
    · simp [weightedSplitScore, hz, hconsistent a hz]
    · have hpos : 0 < consistencyFailures a := Nat.pos_of_ne_zero hz
      have hCpos : 0 < C := lt_of_lt_of_le hpos (hfail a)
      have hremaining : C - consistencyFailures a ≤ C - 1 := by omega
      have hupper : weightedSplitScore C M sourceScore consistencyFailures a ≤
          (C - 1) * M + W := by
        unfold weightedSplitScore
        exact Nat.add_le_add (Nat.mul_le_mul_right M hremaining) (hsource a)
      have hstrict : (C - 1) * M + W < C * M := by
        calc
          (C - 1) * M + W < (C - 1) * M + M :=
            Nat.add_lt_add_left hdominates _
          _ = ((C - 1) + 1) * M := by ring
          _ = C * M := by congr 1 <;> omega
      exact le_trans hupper
        (Nat.le_of_lt (lt_of_lt_of_le hstrict (Nat.le_add_right _ _)))
  · obtain ⟨a, hzero, hopt⟩ := hattain
    exact ⟨a, by simp [weightedSplitScore, hzero, hopt]⟩

/-- Division-free form of the `18/19` baseline guarantee. -/
theorem dominant_baseline_18_19_proof (C M opt : ℕ) (hC : 18 ≤ C)
    (hopt : opt < M) :
    18 * (C * M + opt) ≤ 19 * (C * M) := by
  have hoptM : 18 * opt ≤ 18 * M :=
    Nat.mul_le_mul_left 18 (Nat.le_of_lt hopt)
  have hMC : 18 * M ≤ C * M := Nat.mul_le_mul_right M hC
  calc
    18 * (C * M + opt) = 18 * (C * M) + 18 * opt := by ring
    _ ≤ 18 * (C * M) + C * M := Nat.add_le_add_left (hoptM.trans hMC) _
    _ = 19 * (C * M) := by ring

/-- Exact rational comparison with the general weighted Horn threshold. -/
theorem ratio_18_19_exceeds_general_weighted_horn_proof :
    (18 : ℚ) / 19 > 94615981 / 100000000 := by
  norm_num

end PalomaMax2SAT.WeightedSplit
