module

public import Mathlib
public import PalomaMax2SAT.DegreeFormula
public import PalomaMax2SAT.PaperArithmetic

@[expose] public section

/-!
# Theorem `thm:ugc-broken`: the Unique Games barrier is exceeded on bounded-occurrence classes

The formalized part of Theorem `thm:ugc-broken` is its item (3) together with the threshold
comparison that frames it:

* `β* = 0.94016567 < α* = 0.94615981 < 19/20 < 83/84`;
* `(3d+2)/(3d+3) > 19/20 > α*` for every `d ≥ 6` (division-free);
* for every degree `D ≥ 3`, an independent set `I` with `6 α ≤ 7 |I|` (a `6/7`-approximate
  independent set, which for `D = 3` is the endpoint of the Berman--Fujito guarantee) lifts to an
  assignment of `T_G` satisfying at least `83/84` of the optimum `(D+1) n + m + α`.

The bounded-occurrence guarantee of Ghoshal--Huang--Lee--Makarychev--Makarychev (items (1) and (2))
and the Unique Games hardness thresholds are cited results and are not formalized.
-/

namespace PalomaMax2SAT.UgcBroken

open PalomaMax2SAT.DegreeFormula

theorem ugc_broken :
    (((94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
        (94615981 : ℚ) / 100000000 < 83 / 84) ∧
      (94615981 : ℚ) / 100000000 < 19 / 20) ∧
    (∀ d : ℕ, 6 ≤ d → 19 * (3 * d + 3) < 20 * (3 * d + 2)) ∧
    ∀ {D n m alpha : ℕ} (G : PortGraph D n m) (_ : 3 ≤ D)
      (_ : IsIndependenceNumber G alpha) (I : Finset (Fin n)) (_ : Independent G I)
      (_ : 6 * alpha ≤ 7 * I.card),
      83 * ((D + 1) * n + m + alpha) ≤
        84 * satCount G (assignmentOfIndependent I : Fin n → Fin (D + 1) → Bool) := by
  refine ⟨⟨PalomaMax2SAT.PaperArithmetic.ugc_thresholds, by norm_num⟩,
    fun d hd => PalomaMax2SAT.PaperArithmetic.baseline_above_095 d hd, ?_⟩
  intro D n m alpha G hD halpha I hI hs
  have h := lift_ratio_from_mis G (by omega) halpha I hI hs
  have key : ∀ X S : ℕ, (21 * D + 20) * X ≤ (21 * D + 21) * S → 83 * X ≤ 84 * S := by
    intro X S hXS
    have hc : 83 * (21 * D + 21) ≤ 84 * (21 * D + 20) := by omega
    have h1 : 83 * (21 * D + 21) * X ≤ 84 * (21 * D + 20) * X := Nat.mul_le_mul_right X hc
    have h3 : 84 * ((21 * D + 20) * X) ≤ 84 * ((21 * D + 21) * S) := Nat.mul_le_mul_left 84 hXS
    have h4 : (21 * D + 21) * (83 * X) ≤ (21 * D + 21) * (84 * S) :=
      calc (21 * D + 21) * (83 * X) = 83 * (21 * D + 21) * X := by ring
        _ ≤ 84 * (21 * D + 20) * X := h1
        _ = 84 * ((21 * D + 20) * X) := by ring
        _ ≤ 84 * ((21 * D + 21) * S) := h3
        _ = (21 * D + 21) * (84 * S) := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by omega)
  exact key _ _ h

end PalomaMax2SAT.UgcBroken
