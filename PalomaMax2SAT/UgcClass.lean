module

public import Mathlib
public import PalomaMax2SAT.DegreeFormula
public import PalomaMax2SAT.CutTransfer
public import PalomaMax2SAT.CutLift
public import PalomaMax2SAT.ConflictGraph
public import PalomaMax2SAT.ConflictDegree
public import PalomaMax2SAT.PaperArithmetic

@[expose] public section

/-!
# Theorem `thm:ugc-class`: the cut-to-formula pipeline above the Unique Games thresholds

The formalized parts of Theorem `thm:ugc-class` and of the chain behind it
(Proposition `prop:cut2sat`, Proposition `prop:cutconflict`, Theorem `thm:cutclass`):

1. `83/84 > 0.94615981 > 0.94016567` (the Unique Games thresholds);
2. for every graph `G` given by an edge list and every vertex set `S`, the selected occurrences
   of the conflict graph form an independent set of size `m + cut(S)`;
3. `α(H(G)) = m + maxcut(G)`;
4. if `G` is `d`-regular, the conflict graph is `(d + 1)`-regular, and it has `4 m` vertices;
5. the arithmetic `8785 c ≤ 10000 cut → 18785 (m + c) ≤ 20000 (m + cut)`;
6. for every degree `D > 0`, an independent set `I` with `18785 α ≤ 20000 |I|` lifts to at least
   `83/84` of the optimum `(D + 1) n + m + α` of `T_G`.

The Goemans--Williamson guarantee, the polynomial running time and the Unique Games hardness
statements are not formalized.
-/

namespace PalomaMax2SAT.UgcClass

theorem ugc_class :
    ((94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
      (94615981 : ℚ) / 100000000 < 83 / 84) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (S : Finset (Fin n)),
      PalomaMax2SAT.ConflictGraph.Ind G (PalomaMax2SAT.ConflictGraph.selSet G S) ∧
        (PalomaMax2SAT.ConflictGraph.selSet G S).card =
          m + PalomaMax2SAT.CutTransfer.cutCount G S) ∧
    (∀ {n m mc : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m),
      PalomaMax2SAT.ConflictGraph.IsMaxCut G mc →
        PalomaMax2SAT.ConflictGraph.IsIndNumber G (m + mc)) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (d : ℕ),
      (∀ v, PalomaMax2SAT.ConflictDegree.occ G v = d) →
        ∀ p : PalomaMax2SAT.ConflictGraph.Occ m,
          (PalomaMax2SAT.ConflictDegree.nbrs G p).card = d + 1) ∧
    (∀ m : ℕ, Fintype.card (PalomaMax2SAT.ConflictGraph.Occ m) = 4 * m) ∧
    (∀ m c cut : ℕ, c ≤ m → 8785 * c ≤ 10000 * cut →
      18785 * (m + c) ≤ 20000 * (m + cut)) ∧
    ∀ {D n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph D n m) (_ : 0 < D)
      (_ : PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha)
      (I : Finset (Fin n)) (_ : PalomaMax2SAT.DegreeFormula.Independent G I)
      (_ : 18785 * alpha ≤ 20000 * I.card),
      83 * ((D + 1) * n + m + alpha) ≤
        84 * PalomaMax2SAT.DegreeFormula.satCount G
          (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
            Fin n → Fin (D + 1) → Bool) :=
  ⟨PalomaMax2SAT.PaperArithmetic.ugc_thresholds,
    fun G S =>
      ⟨PalomaMax2SAT.ConflictGraph.selSet_independent G S, by
        rw [PalomaMax2SAT.ConflictGraph.card_selSet,
          PalomaMax2SAT.CutTransfer.value_eq_edges_add_cut]⟩,
    fun G h => PalomaMax2SAT.ConflictGraph.alpha_eq G h,
    fun G d hd p => PalomaMax2SAT.ConflictDegree.card_nbrs_regular G d hd p,
    fun m => PalomaMax2SAT.ConflictDegree.card_occ m,
    fun m c cut hc hcut => PalomaMax2SAT.CutTransfer.independent_ratio_from_cut m c cut hc hcut,
    fun G hD halpha I hI hs =>
      PalomaMax2SAT.CutLift.lift_ratio_from_cut G hD halpha I hI hs⟩

end PalomaMax2SAT.UgcClass
