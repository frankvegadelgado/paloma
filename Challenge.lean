module

public import PalomaMax2SAT

public section

namespace PalomaMax2SAT.CubicPublic

open CubicThreeOccurrence

theorem repairedSet_independent {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Independent G (repairedSet G z) := by
  exact repairedSet_independent_proof G z

theorem repairedSet_card_lower_bound {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) :
    score G z ≤ 4 * n + m + (repairedSet G z).card := by
  exact repairedSet_card_lower_bound_proof G z

theorem exact_three_occurrence_identity {n m alpha : ℕ}
    (G : PortGraph n m) (halpha : IsIndependenceNumber G alpha) :
    (∀ z, score G z ≤ 4 * n + m + alpha) ∧
      ∃ z, score G z = 4 * n + m + alpha := by
  exact exact_three_occurrence_identity_proof G halpha

theorem ratio_83_84_from_cubic_mis
    (n m alpha found : ℕ)
    (hcubic : 2 * m = 3 * n)
    (halpha : 2 * alpha ≤ n)
    (happrox : 7 * found ≥ 6 * alpha) :
    84 * (4 * n + m + found) ≥ 83 * (4 * n + m + alpha) := by
  exact ratio_83_84_from_cubic_mis_proof n m alpha found hcubic halpha happrox

theorem ratio_83_84_arithmetic :
    (11 : ℚ) + 6 / 7 = (83 / 84) * 12 := by
  exact ratio_83_84_arithmetic_proof

end PalomaMax2SAT.CubicPublic

namespace PalomaMax2SAT.HardSplitPublic

open HardOccurrenceSplit

theorem hard_implication_cycle_consistent {α : Type} (next : α → α)
    (z : α → Bool) (horbit : OrbitConnected next)
    (hhard : HardImplicationsHold next z) :
    ∀ i j, z i = z j := by
  exact hard_implication_cycle_consistent_proof next z horbit hhard

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
  exact exact_hard_occurrence_split_proof sourceScore splitScore feasible
    encode decode opt hsource hencodeFeasible hencodeScore hdecodeScore

theorem feasible_solution_ratio_preserved
    {Source Split : Type}
    (sourceScore : Source → ℕ) (splitScore : Split → ℕ)
    (feasible : Split → Prop) (decode : Split → Source)
    (hdecodeScore : ∀ z, feasible z → sourceScore (decode z) = splitScore z)
    (z : Split) (hz : feasible z) :
    splitScore z = sourceScore (decode z) := by
  exact feasible_solution_ratio_preserved_proof sourceScore splitScore feasible
    decode hdecodeScore z hz

theorem ratio_83_84_exceeds_general_horn_threshold :
    (83 : ℚ) / 84 > 94615981 / 100000000 := by
  exact ratio_83_84_exceeds_general_horn_threshold_proof

end PalomaMax2SAT.HardSplitPublic
