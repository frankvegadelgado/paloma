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

/-- A directed hard-implication cycle forces all occurrence clones to agree. -/
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

end PalomaMax2SAT.HardOccurrenceSplit
