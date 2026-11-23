module

public import Mathlib
public import PalomaMax2SAT.GeneralDegreeFormula
public import PalomaMax2SAT.CutTransfer
public import PalomaMax2SAT.ConflictGraph
public import PalomaMax2SAT.ConflictDegree
public import PalomaMax2SAT.PaperArithmetic
public import PalomaMax2SAT.BoundedLemmas

@[expose] public section

/-!
# Theorem `thm:ugc-class` for bounded degree: the ratio above the Unique Games thresholds

The formalized parts of Theorem `thm:ugc-class` and of the non-regular family behind it
(Theorem `thm:nonreg-cutclass`, Lemma `lem:general-identity`):

1. `83/84 < 0.9932` and `83/84 > 0.94615981 > 0.94016567`;
2. the occurrences selected by a vertex set `S` of `G` form an independent set of the conflict
   graph `H(G)` of size `m + cut(S)`, and `α(H(G)) = m + maxcut(G)`;
3. if `G` has maximum degree at most `Dmax`, every vertex of `H(G)` has degree at most `Dmax + 1`;
4. for every graph `G`, the degree sum of `H(G)` is `4 m + 2 Σ_v deg(v)²`, so `H(G)` has at
   least `4 m` edges;
5. the division-free arithmetic `B ≥ 8 α`, `18785 α ≤ 20000 |I|` implies
   `9932 (B + α) ≤ 10000 (B + |I|)`, hence `83 (B + α) ≤ 84 (B + |I|)`;
6. for `T_H` of any graph with port labelling and degrees `d_v`: `Σ d_v = 2 m`,
   `Σ (d_v + 1) + m = n + 3 m`, the optimum is `Σ (d_v + 1) + m + α`, and the lift of an
   independent set `I` has value `Σ (d_v + 1) + m + |I|`.

The Goemans--Williamson guarantee, the polynomial running time and the Unique Games hardness
statements are not formalized. The identification of `H(G)` with a port-labelled graph, and so
of `T_{H(G)}` with an instance of item 6, is not formalized.
-/

namespace PalomaMax2SAT.UgcBounded

theorem ugc_bounded :
    (((94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
        (94615981 : ℚ) / 100000000 < 83 / 84) ∧
      (83 : ℚ) / 84 < 9932 / 10000) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (S : Finset (Fin n)),
      PalomaMax2SAT.ConflictGraph.Ind G (PalomaMax2SAT.ConflictGraph.selSet G S) ∧
        (PalomaMax2SAT.ConflictGraph.selSet G S).card =
          m + PalomaMax2SAT.CutTransfer.cutCount G S) ∧
    (∀ {n m mc : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m),
      PalomaMax2SAT.ConflictGraph.IsMaxCut G mc →
        PalomaMax2SAT.ConflictGraph.IsIndNumber G (m + mc)) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (Dmax : ℕ),
      (∀ v, PalomaMax2SAT.ConflictDegree.occ G v ≤ Dmax) →
        ∀ p : PalomaMax2SAT.ConflictGraph.Occ m,
          (PalomaMax2SAT.ConflictDegree.nbrs G p).card ≤ Dmax + 1) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (M : ℕ),
      2 * M = ∑ p : PalomaMax2SAT.ConflictGraph.Occ m,
          (PalomaMax2SAT.ConflictDegree.nbrs G p).card →
        2 * M = 4 * m + 2 * ∑ v, PalomaMax2SAT.ConflictDegree.occ G v ^ 2 ∧ 4 * m ≤ M) ∧
    (∀ m M alpha s : ℕ, 4 * m ≤ M → alpha ≤ 2 * m → 18785 * alpha ≤ 20000 * s →
      9932 * ((4 * m + 3 * M) + alpha) ≤ 10000 * ((4 * m + 3 * M) + s) ∧
        83 * ((4 * m + 3 * M) + alpha) ≤ 84 * ((4 * m + 3 * M) + s)) ∧
    (∀ {n m : ℕ} {deg : Fin n → ℕ}
      (G : PalomaMax2SAT.GeneralDegreeFormula.GPortGraph n m deg),
      ∑ v, deg v = 2 * m ∧ ∑ v, (deg v + 1) + m = n + 3 * m) ∧
    (∀ {n m alpha : ℕ} {deg : Fin n → ℕ}
      (G : PalomaMax2SAT.GeneralDegreeFormula.GPortGraph n m deg),
      PalomaMax2SAT.GeneralDegreeFormula.IsIndependenceNumber G alpha →
        IsGreatest (Set.range (PalomaMax2SAT.GeneralDegreeFormula.satCount G))
          (∑ v, (deg v + 1) + m + alpha)) ∧
    ∀ {n m alpha : ℕ} {deg : Fin n → ℕ}
      (G : PalomaMax2SAT.GeneralDegreeFormula.GPortGraph n m deg)
      (_ : PalomaMax2SAT.GeneralDegreeFormula.IsIndependenceNumber G alpha)
      (I : Finset (Fin n)) (_ : PalomaMax2SAT.GeneralDegreeFormula.Independent G I)
      (_ : 8 * alpha ≤ ∑ v, (deg v + 1) + m) (_ : 18785 * alpha ≤ 20000 * I.card),
      PalomaMax2SAT.GeneralDegreeFormula.satCount G
          (PalomaMax2SAT.GeneralDegreeFormula.assignmentOfIndependent I) =
        ∑ v, (deg v + 1) + m + I.card ∧
      9932 * (∑ v, (deg v + 1) + m + alpha) ≤
        10000 * PalomaMax2SAT.GeneralDegreeFormula.satCount G
          (PalomaMax2SAT.GeneralDegreeFormula.assignmentOfIndependent I) ∧
      83 * (∑ v, (deg v + 1) + m + alpha) ≤
        84 * PalomaMax2SAT.GeneralDegreeFormula.satCount G
          (PalomaMax2SAT.GeneralDegreeFormula.assignmentOfIndependent I) :=
  ⟨⟨PalomaMax2SAT.PaperArithmetic.ugc_thresholds, by norm_num⟩,
    fun G S =>
      ⟨PalomaMax2SAT.ConflictGraph.selSet_independent G S, by
        rw [PalomaMax2SAT.ConflictGraph.card_selSet,
          PalomaMax2SAT.CutTransfer.value_eq_edges_add_cut]⟩,
    fun G h => PalomaMax2SAT.ConflictGraph.alpha_eq G h,
    fun G Dmax hD p => PalomaMax2SAT.BoundedLemmas.nbrs_le G Dmax hD p,
    fun G M hM => PalomaMax2SAT.BoundedLemmas.edges_ge G M hM,
    fun m M alpha s hM ha hs => PalomaMax2SAT.BoundedLemmas.ratio_nonregular m M alpha s hM ha hs,
    fun G => ⟨PalomaMax2SAT.GeneralDegreeFormula.sum_deg_eq G,
      PalomaMax2SAT.GeneralDegreeFormula.constant_eq G⟩,
    fun G halpha => PalomaMax2SAT.GeneralDegreeFormula.optimum_identity G halpha,
    fun G halpha I hI hB hs => by
      have hlift := PalomaMax2SAT.GeneralDegreeFormula.lift_satCount G I hI
      refine ⟨hlift, ?_, ?_⟩ <;> rw [hlift] <;> omega⟩

end PalomaMax2SAT.UgcBounded
