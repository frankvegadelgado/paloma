module

public import Mathlib
public import PalomaMax2SAT.DegreeFormula
public import PalomaMax2SAT.CutLift
public import PalomaMax2SAT.PaperArithmetic

@[expose] public section

/-!
# Theorem `thm:ugc-class`: the ratio `83/84` above the Unique Games thresholds

`83/84` exceeds the Unique Games thresholds `0.94615981` and `0.94016567`, and the lift of an
independent set `I` with `18785 α ≤ 20000 |I|` (the set obtained from a Goemans--Williamson cut)
satisfies at least `83/84` of the optimum of `T_H`. The cut guarantee is a hypothesis.
-/

namespace PalomaMax2SAT.UgcBarrier

open PalomaMax2SAT.DegreeFormula

theorem ugc_barrier :
    ((94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
      (94615981 : ℚ) / 100000000 < 83 / 84) ∧
    ∀ {D n m alpha : ℕ} (G : PortGraph D n m) (_ : 0 < D)
      (_ : IsIndependenceNumber G alpha) (I : Finset (Fin n)) (_ : Independent G I)
      (_ : 18785 * alpha ≤ 20000 * I.card),
      83 * ((D + 1) * n + m + alpha) ≤
        84 * satCount G (assignmentOfIndependent I : Fin n → Fin (D + 1) → Bool) :=
  ⟨PalomaMax2SAT.PaperArithmetic.ugc_thresholds,
    fun G hD halpha I hI hs =>
      PalomaMax2SAT.CutLift.lift_ratio_from_cut G hD halpha I hI hs⟩

end PalomaMax2SAT.UgcBarrier
