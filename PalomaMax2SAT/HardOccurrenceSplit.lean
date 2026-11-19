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

end PalomaMax2SAT.HardOccurrenceSplit
