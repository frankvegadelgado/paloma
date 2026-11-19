module

public import Mathlib

public section

/-!
# Canonical standalone challenge

This file intentionally imports only Mathlib so Palomar can compile it in an
isolated canonical environment. The implementation lives in the project
modules imported by `Solution.lean`.
-/

namespace PalomaMax2SAT.CubicThreeOccurrence

structure PortGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  left_ne_right : ∀ e, left e ≠ right e
  leftPort : Fin m → Fin 3
  rightPort : Fin m → Fin 3
  left_unique : ∀ e f, left e = left f → leftPort e = leftPort f → e = f
  right_unique : ∀ e f, right e = right f → rightPort e = rightPort f → e = f
  cross_unique : ∀ e f, left e = right f → leftPort e = rightPort f → False

def Independent {n m : ℕ} (G : PortGraph n m) (I : Finset (Fin n)) : Prop :=
  ∀ e, ¬ (G.left e ∈ I ∧ G.right e ∈ I)

def IsIndependenceNumber {n m : ℕ} (G : PortGraph n m) (alpha : ℕ) : Prop :=
  (∀ I, Independent G I → I.card ≤ alpha) ∧
    ∃ I, Independent G I ∧ I.card = alpha

def edgeClone (p : Fin 3) : Fin 4 := ⟨p.val + 1, by omega⟩

abbrev transition {n : ℕ} (z : Fin n → Fin 4 → Bool)
    (v : Fin n) (i : Fin 4) : Prop :=
  z v i = true ∧ z v ⟨(i.val + 1) % 4, Nat.mod_lt _ (by omega)⟩ = false

def selectedVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => z v 0 = false

def transitionPairs {n : ℕ} (z : Fin n → Fin 4 → Bool) :
    Finset (Fin n × Fin 4) :=
  Finset.univ.filter fun pair => transition z pair.1 pair.2

def transitionVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  (transitionPairs z).image Prod.fst

def cleanVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  selectedVertices z \ transitionVertices z

def falseEdges {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun e =>
    z (G.left e) (edgeClone (G.leftPort e)) = false ∧
      z (G.right e) (edgeClone (G.rightPort e)) = false

def deletionSet {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  ((Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z).image G.left)

def repairedSet {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  cleanVertices z \ deletionSet G z

def score {n m : ℕ} (G : PortGraph n m) (z : Fin n → Fin 4 → Bool) : ℕ :=
  (selectedVertices z).card + (m - (falseEdges G z).card) +
    (4 * n - (transitionPairs z).card)

end PalomaMax2SAT.CubicThreeOccurrence

namespace PalomaMax2SAT.HardOccurrenceSplit

def advance {α : Type} (next : α → α) : ℕ → α → α
  | 0, i => i
  | k + 1, i => advance next k (next i)

def OrbitConnected {α : Type} (next : α → α) : Prop :=
  ∀ i j, ∃ k, advance next k i = j

def HardImplicationsHold {α : Type} (next : α → α) (z : α → Bool) : Prop :=
  ∀ i, z i = true → z (next i) = true

def IsOptimum {Assignment : Type} (score : Assignment → ℕ) (opt : ℕ) : Prop :=
  (∀ a, score a ≤ opt) ∧ ∃ a, score a = opt

def IsHardOptimum {Assignment : Type} (feasible : Assignment → Prop)
    (score : Assignment → ℕ) (opt : ℕ) : Prop :=
  (∀ a, feasible a → score a ≤ opt) ∧ ∃ a, feasible a ∧ score a = opt

theorem propagate_hard_implications {α : Type} (next : α → α)
    (z : α → Bool) (h : HardImplicationsHold next z) :
    ∀ k i, z i = true → z (advance next k i) = true := by
  intro k
  induction k with
  | zero =>
      intro i hi
      simpa [advance] using hi
  | succ k ih =>
      intro i hi
      simp only [advance]
      exact ih (next i) (h i hi)

end PalomaMax2SAT.HardOccurrenceSplit

namespace PalomaMax2SAT.CubicPublic

open CubicThreeOccurrence

theorem repairedSet_independent {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Independent G (repairedSet G z) := by
  sorry

theorem repairedSet_card_lower_bound {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) :
    score G z ≤ 4 * n + m + (repairedSet G z).card := by
  sorry

theorem exact_three_occurrence_identity {n m alpha : ℕ}
    (G : PortGraph n m) (halpha : IsIndependenceNumber G alpha) :
    (∀ z, score G z ≤ 4 * n + m + alpha) ∧
      ∃ z, score G z = 4 * n + m + alpha := by
  sorry

theorem ratio_83_84_from_cubic_mis
    (n m alpha found : ℕ)
    (hcubic : 2 * m = 3 * n)
    (halpha : 2 * alpha ≤ n)
    (happrox : 7 * found ≥ 6 * alpha) :
    84 * (4 * n + m + found) ≥ 83 * (4 * n + m + alpha) := by
  omega

theorem ratio_83_84_arithmetic :
    (11 : ℚ) + 6 / 7 = (83 / 84) * 12 := by
  norm_num

end PalomaMax2SAT.CubicPublic

namespace PalomaMax2SAT.HardSplitPublic

open HardOccurrenceSplit

theorem hard_implication_cycle_consistent {α : Type} (next : α → α)
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

theorem exact_hard_occurrence_split
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

theorem feasible_solution_ratio_preserved
    {Source Split : Type}
    (sourceScore : Source → ℕ) (splitScore : Split → ℕ)
    (feasible : Split → Prop) (decode : Split → Source)
    (hdecodeScore : ∀ z, feasible z → sourceScore (decode z) = splitScore z)
    (z : Split) (hz : feasible z) :
    splitScore z = sourceScore (decode z) := by
  exact (hdecodeScore z hz).symm

theorem ratio_83_84_exceeds_general_horn_threshold :
    (83 : ℚ) / 84 > 94615981 / 100000000 := by
  norm_num

end PalomaMax2SAT.HardSplitPublic
