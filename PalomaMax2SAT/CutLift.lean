module

public import Mathlib
public import PalomaMax2SAT.DegreeFormula
public import PalomaMax2SAT.CutTransfer

@[expose] public section

/-!
# From a Goemans--Williamson cut to the ratio `83/84` on `T_H`

For a graph `G` the conflict graph `H(G)` has an independent set of size `m + cut(S)`
for every vertex set `S` (Theorem `thm:cutclass` of the paper, proved in the text), and
`α(H(G)) = m + maxcut(G)`. This module proves the part that follows once an independent
set `I` of `H` with `18785 α ≤ 20000 |I|` is available: its lift has ratio `83/84` on
`T_H`, for every degree `D ≥ 1`. The cut guarantee itself is cited
(Goemans--Williamson; Mahajan--Ramesh) and is a hypothesis.
-/

namespace PalomaMax2SAT.CutLift

open PalomaMax2SAT.DegreeFormula

theorem lift_ratio_from_cut {D n m alpha : ℕ} (G : PortGraph D n m) (hD : 0 < D)
    (halpha : IsIndependenceNumber G alpha) (I : Finset (Fin n))
    (hI : Independent G I) (hs : 18785 * alpha ≤ 20000 * I.card) :
    83 * ((D + 1) * n + m + alpha) ≤
      84 * satCount G (assignmentOfIndependent I : Fin n → Fin (D + 1) → Bool) :=
  lift_ratio_threshold G hD halpha I hI
    (PalomaMax2SAT.CutTransfer.threshold_from_cut D alpha I.card hD hs)

end PalomaMax2SAT.CutLift
