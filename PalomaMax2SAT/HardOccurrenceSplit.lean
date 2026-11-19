module

public import Mathlib

public section

namespace PalomaMax2SAT.HardOccurrenceSplit

abbrev advance {α : Type*} (next : α → α) (k : ℕ) (i : α) : α :=
  Nat.rec i (fun _ current => next current) k

abbrev OrbitConnected {α : Type*} (next : α → α) : Prop :=
  ∀ i j, ∃ k, advance next k i = j

abbrev HardImplicationsHold {α : Type*} (next : α → α) (z : α → Bool) : Prop :=
  ∀ i, z i = true → z (next i) = true

abbrev IsOptimum {Assignment : Type*} (score : Assignment → ℕ) (opt : ℕ) : Prop :=
  (∀ a, score a ≤ opt) ∧ ∃ a, score a = opt

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

/-- Restored: the proof used by `Solution.lean` for
`HardSplitPublic.hard_implication_cycle_consistent`. -/
theorem hard_implication_cycle_consistent_proof {α : Type*} (next : α → α)
    (z : α → Bool) (horbit : OrbitConnected next)
    (hhard : HardImplicationsHold next z) :
    ∀ i j, z i = z j := by
  intro i j
  cases hi : z i <;> cases hj : z j
  · rfl
  · obtain ⟨k, hk⟩ := horbit j i
    have htrue := propagate_hard_implications next z hhard k j hj
    rw [hk, hi] at htrue
    simp at htrue
  · obtain ⟨k, hk⟩ := horbit i j
    have htrue := propagate_hard_implications next z hhard k i hi
    rw [hk, hj] at htrue
    simp at htrue
  · rfl

/-- Restored: the proof used by `Solution.lean` for
`HardSplitPublic.exact_hard_occurrence_split`. -/
theorem exact_hard_occurrence_split_proof
    {Source Split : Type}
    (sourceScore : Source → ℕ) (splitScore : Split → ℕ)
    (feasible : Split → Prop) (encode : Source → Split) (decode : Split → Source)
    (opt : ℕ)
    (hsource : IsOptimum sourceScore opt)
    (hencodeFeasible : ∀ a, feasible (encode a))
    (hencodeScore : ∀ a, splitScore (encode a) = sourceScore a)
    (hdecodeScore : ∀ z, feasible z → sourceScore (decode z) = splitScore z) :
    IsHardOptimum feasible splitScore opt := by
  constructor
  · intro z hz
    rw [← hdecodeScore z hz]
    exact hsource.1 (decode z)
  · obtain ⟨a, ha⟩ := hsource.2
    exact ⟨encode a, hencodeFeasible a, (hencodeScore a).trans ha⟩

/-- Restored: the proof used by `Solution.lean` for
`HardSplitPublic.feasible_solution_ratio_preserved`. -/
theorem feasible_solution_ratio_preserved_proof
    {Source Split : Type}
    (sourceScore : Source → ℕ) (splitScore : Split → ℕ)
    (feasible : Split → Prop) (decode : Split → Source)
    (hdecodeScore : ∀ z, feasible z → sourceScore (decode z) = splitScore z)
    (z : Split) (hz : feasible z) :
    splitScore z = sourceScore (decode z) := by
  exact (hdecodeScore z hz).symm

/-- Restored: the proof used by `Solution.lean` for
`HardSplitPublic.ratio_83_84_exceeds_general_horn_threshold`. -/
theorem ratio_83_84_exceeds_general_horn_threshold_proof :
    (83 : ℚ) / 84 > 94615981 / 100000000 := by
  norm_num

end PalomaMax2SAT.HardOccurrenceSplit
