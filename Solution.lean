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

theorem ratio_at_least_83_84_general
    (d n m alpha found : ℕ)
    (hd : 3 ≤ d)
    (hreg : 2 * m = d * n)
    (halpha : 2 * alpha ≤ n)
    (happrox : 7 * found ≥ 6 * alpha) :
    84 * ((d + 1) * n + m + found) ≥ 83 * ((d + 1) * n + m + alpha) := by
  have h1 : 3 * n ≤ d * n := Nat.mul_le_mul_right n hd
  have h2 : (d + 1) * n = d * n + n := by ring
  omega

theorem general_endpoint_ratio (d : ℕ) (hd : 3 ≤ d) :
    let β : ℚ := (3 * d + 2) / 2
    (β + 3 / 7) / (β + 1 / 2) ≥ (83 : ℚ) / 84 := by
  intro β
  have hd' : (3 : ℚ) ≤ d := by exact_mod_cast hd
  have hβ : β = (3 * (d : ℚ) + 2) / 2 := rfl
  have hpos : (0 : ℚ) < β + 1 / 2 := by rw [hβ]; linarith
  rw [ge_iff_le, le_div_iff₀ hpos, hβ]
  linarith

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

/-- Every variable of `T_H` occurs exactly three times. -/
theorem three_occurrences {n m : ℕ} (G : PortGraph n m)
    (x : Fin n × Fin 4) : occurrences G x = 3 := by
  exact three_occurrences_proof G x

end PalomaMax2SAT.SemanticPublic

namespace PalomaMax2SAT.DegreePublic

theorem baseline_degree_d (d n m a : ℕ) (hm : 2 * m = d * n) (hn : 2 * a ≤ n) :
    (3 * d + 2) * ((d + 1) * n + m + a) ≤ (3 * d + 3) * ((d + 1) * n + m) := by
  exact DegreeTransfer.baseline_degree_d_proof d n m a hm hn

theorem baseline_exceeds_83_84 (d n m a : ℕ) (hd : 27 ≤ d)
    (hm : 2 * m = d * n) (hn : 2 * a ≤ n) :
    83 * ((d + 1) * n + m + a) ≤ 84 * ((d + 1) * n + m) := by
  exact DegreeTransfer.baseline_exceeds_83_84_proof d n m a hd hm hn

theorem ratio_degree_d_from_mis (d n m a s : ℕ) (hm : 2 * m = d * n)
    (hn : 2 * a ≤ n) (hs : 6 * a ≤ 7 * s) :
    (21 * d + 20) * ((d + 1) * n + m + a) ≤
      (21 * d + 21) * ((d + 1) * n + m + s) := by
  exact DegreeTransfer.ratio_degree_d_from_mis_proof d n m a s hm hn hs

theorem bf_degree_d (d n m a s : ℕ) (hd : 22 ≤ d) (hm : 2 * m = d * n)
    (hn : 2 * a ≤ n) (hs : 5 * a ≤ (d + 3) * s) :
    83 * ((d + 1) * n + m + a) ≤ 84 * ((d + 1) * n + m + s) := by
  exact DegreeTransfer.bf_degree_d_proof d n m a s hd hm hn hs

theorem two_branch_degree_21 (n m a s : ℕ) (hm : 2 * m = 21 * n) (hn : 2 * a ≤ n)
    (hbf : 200 * a ≤ 99 * n → 50 * a ≤ 241 * s)
    (hcut : 99 * n < 200 * a → 3 * n ≤ 25 * s) :
    83 * (22 * n + m + a) ≤ 84 * (22 * n + m + s) := by
  exact DegreeTransfer.two_branch_degree_21_proof n m a s hm hn hbf hcut

theorem threshold_degree_d (d n m a s : ℕ) (hm : 2 * m = d * n) (hn : 2 * a ≤ n)
    (hs : 27 * a ≤ 28 * s + d * a) :
    83 * ((d + 1) * n + m + a) ≤ 84 * ((d + 1) * n + m + s) := by
  exact DegreeTransfer.threshold_degree_d_proof d n m a s hm hn hs

end PalomaMax2SAT.DegreePublic
