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

namespace PalomaMax2SAT.SemanticPublic

open PalomaMax2SAT.CubicThreeOccurrence PalomaMax2SAT.SemanticHorn

/-- The number of satisfied clauses of the formula `T_H` equals the score. -/
theorem satCount_eq_score {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : satCount G z = score G z := by
  exact satCount_eq_score_proof G z

/-- `OPT(T_H) = 4n + m + alpha(H)`, stated for the clause semantics. -/
theorem optimum_identity {n m alpha : ℕ} (G : PortGraph n m)
    (halpha : IsIndependenceNumber G alpha) :
    IsGreatest (Set.range (satCount G)) (4 * n + m + alpha) := by
  exact optimum_identity_proof G halpha

/-- Every clause of `T_H` is Horn. -/
theorem formula_horn {n m : ℕ} (G : PortGraph n m) (c : ClauseIdx n m) :
    IsHorn (clauseOf G c) := by
  exact formula_horn_proof G c

/-- `T_H` has `5n + m` clauses. -/
theorem formula_size (n m : ℕ) :
    Fintype.card (ClauseIdx n m) = 5 * n + m := by
  exact formula_size_proof n m

end PalomaMax2SAT.SemanticPublic
