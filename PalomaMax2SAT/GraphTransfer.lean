module

public import PalomaMax2SAT.HardOccurrenceSplit

public import PalomaMax2SAT.CubicThreeOccurrence

public section

namespace PalomaMax2SAT.GraphTransfer

open PalomaMax2SAT.HardOccurrenceSplit

/-- In a fully occupied ring, let z i record selection of the true port.
The cross edge forbids selecting the true port and the next false port. -/
theorem fullRing_constant {ι : Type*} (next : ι → ι) (z : ι → Bool)
    (orbit : OrbitConnected next)
    (cross : ∀ i, ¬ (z i = true ∧ z (next i) = false)) :
    ∀ i j, z i = z j := by
  apply hard_implication_cycle_consistent_proof next z orbit
  intro i hi
  cases h : z (next i) with
  | false => exact False.elim (cross i ⟨hi, h⟩)
  | true => rfl

/-- K4 as a simple graph: every two distinct vertices conflict. -/
theorem singleton_maximum_K4 (s : Finset (Fin 4))
    (indep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → False) : s.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact Classical.byContradiction (indep i hi j hj)

theorem singleton_breaks_cycle :
    ¬ HardImplicationsHold (fun i : Fin 4 => i + 1) (fun i => decide (i = 0)) := by
  intro h
  have bad := h 0 (by decide)
  revert bad
  decide

/-- Counts of four cube components, one using an antipodal pair. -/
theorem hardening_loses_ratio :
    7 * 14 ≥ 6 * 16 ∧ 84 * 190 ≥ 83 * 192 ∧ 84 * 62 < 83 * 64 := by decide

/-- If edge clauses weigh four, the cubic edge total is at least 12 alpha. -/
theorem hardImage_ratio (W a s : ℕ) (hw : 12*a ≤ W) (hs : 17*a ≤ 20*s) :
    260*(W+s) ≥ 257*(W+a) := by omega

open PalomaMax2SAT.CubicThreeOccurrence

/-- The hard cycle is a feasibility condition. Only units and edges earn weight. -/
noncomputable def fourScore {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : ℕ :=
  (selectedVertices z).card + 4 * (m - (falseEdges G z).card)

theorem fourScore_repair {n m : ℕ} (G : PortGraph n m) (z : Fin n → Fin 4 → Bool)
    (hz : transitionPairs z = ∅) :
    fourScore G z ≤ 4*m + (repairedSet G z).card := by
  have h := repairedSet_card_lower_bound_proof G z
  simp only [score, hz, Finset.card_empty, Nat.sub_zero] at h
  unfold fourScore
  omega

theorem canonical_fourScore {n m : ℕ} (G : PortGraph n m)
    (I : Finset (Fin n)) (hI : Independent G I) :
    transitionPairs (assignmentOfIndependent I) = ∅ ∧
    fourScore G (assignmentOfIndependent I) = 4*m + I.card := by
  classical
  have hselected : selectedVertices (assignmentOfIndependent I) = I := by
    ext v
    simp [selectedVertices, assignmentOfIndependent]
  have hfalse : falseEdges G (assignmentOfIndependent I) = ∅ := by
    ext e
    simp [falseEdges, assignmentOfIndependent, hI e]
  constructor
  · ext pair
    simp [transitionPairs, transition, assignmentOfIndependent]
  · simp [fourScore, hselected, hfalse, Nat.add_comm]

theorem exact_fourScore {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (fourScore G) (4*m+a) := by
  constructor
  · intro z hz
    have hu := fourScore_repair G z hz
    have hi := ha.1 _ (repairedSet_independent_proof G z)
    omega
  · obtain ⟨I, hi, hc⟩ := ha.2
    exact ⟨assignmentOfIndependent I, (canonical_fourScore G I hi).1,
      by rw [(canonical_fourScore G I hi).2, hc]⟩

theorem hardFour_transfer {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (I : Finset (Fin n)) (hi : Independent G I) (hs : 17*a ≤ 20*I.card) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (fourScore G) (4*m+a) ∧
    transitionPairs (assignmentOfIndependent I) = ∅ ∧
    260*fourScore G (assignmentOfIndependent I) ≥ 257*(4*m+a) := by
  obtain ⟨hz, hval⟩ := canonical_fourScore G I hi
  refine ⟨exact_fourScore G ha, hz, ?_⟩
  rw [hval]
  exact hardImage_ratio (4*m) a I.card (by omega) hs

/-- Away from the bipartite limit a fixed slack in the MIS ratio suffices. -/
theorem far_ratio (n a s B : ℕ) (hb : 11*n ≤ 2*B)
    (ha : 20000*a ≤ 9999*n) (hs : 5999993*a ≤ 7000000*s) :
    84*(B+s) ≥ 83*(B+a) := by omega

/-- Original unit weights, with all implications mandatory and unscored. -/
noncomputable def unitScore {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : ℕ :=
  (selectedVertices z).card + (m - (falseEdges G z).card)

theorem exact_unitScore {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (unitScore G) (m+a) := by
  constructor
  · intro z hz
    have hu := repairedSet_card_lower_bound_proof G z
    have hi := ha.1 _ (repairedSet_independent_proof G z)
    simp only [score, hz, Finset.card_empty, Nat.sub_zero] at hu
    unfold unitScore
    omega
  · obtain ⟨I, hi, hc⟩ := ha.2
    have hz := (canonical_fourScore G I hi).1
    have hv := score_assignmentOfIndependent_proof G I hi
    simp only [score, hz, Finset.card_empty, Nat.sub_zero] at hv
    exact ⟨assignmentOfIndependent I, hz, by unfold unitScore; omega⟩

theorem hardUnit_transfer {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (I : Finset (Fin n)) (hi : Independent G I) (hs : 17*a ≤ 20*I.card) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (unitScore G) (m+a) ∧
    transitionPairs (assignmentOfIndependent I) = ∅ ∧
    80*unitScore G (assignmentOfIndependent I) ≥ 77*(m+a) := by
  have hz := (canonical_fourScore G I hi).1
  have hv := score_assignmentOfIndependent_proof G I hi
  simp only [score, hz, Finset.card_empty, Nat.sub_zero] at hv
  refine ⟨exact_unitScore G ha, hz, ?_⟩
  unfold unitScore
  omega

theorem unit_endpoint_arithmetic (n m a s : ℕ)
    (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (h : 6*a ≤ 7*s ∨ (20000*a ≤ 9999*n ∧ 5999993*a ≤ 7000000*s)) :
    28*(m+s) ≥ 27*(m+a) := by
  rcases h with h | ⟨h₁,h₂⟩ <;> omega

end PalomaMax2SAT.GraphTransfer
