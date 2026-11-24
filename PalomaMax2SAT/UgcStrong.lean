module

public import Mathlib
public import PalomaMax2SAT.StrongLemmas
public import PalomaMax2SAT.BoundedLemmas
public import PalomaMax2SAT.RegularLemmas
public import PalomaMax2SAT.DegreeFormula
public import PalomaMax2SAT.ConflictGraph
public import PalomaMax2SAT.ConflictDegree
public import PalomaMax2SAT.CutTransfer
public import PalomaMax2SAT.PaperArithmetic

@[expose] public section

/-!
# Theorem `thm:strong-ugc-broken`, item (2): the strong `α_GW + Õ(1/d)` barrier

The formalized parts of item (2) of Theorem `thm:strong-ugc-broken`:

1. `α_GW < β* < α* < 83/84 < 0.9932`;
2. for `α_ε ≥ 0.8785`, `1 - (1 - α_ε)/18 > 0.9932` and `1 - (1 - α_ε)/(6d + 12) > 0.9932` for
   every `d ≥ 1`; every threshold `τ ≤ 0.9932` is strictly below these ratios;
3. `1 - (1 - α_ε)/(6d + 12)` is eventually above `1 - ε` for every `ε > 0`;
4. `0.9326 - 0.87856 = 0.05404 > 0`;
5. a cut guarantee `p/q` gives the lifted ratio `1 - (1 - p/q)/(6d + 12)` on a `d`-regular graph;
6. `α(H(G)) = m + maxcut(G)`, maximum degree at most `d + 1` of `H(G)` for `G` of maximum
   degree at most `d`, `4 m ≤ M`, and the arithmetic `9932 (B + α) ≤ 10000 (B + s)`;
7. exact optima `3 n` (`d = 1`) and `4 n + α` (`d = 2`) of `T_H`.

The value of `τ_strong(d) = α_GW + Õ(1/d)`, the Goemans--Williamson and
Halperin--Livnat--Zwick guarantees, the polynomial running times, the exact algorithm on paths
and cycles, and the Unique Games statements are not formalized.
-/

namespace PalomaMax2SAT.UgcStrong

theorem strong_ugc_broken :
    ((((87856 : ℚ) / 100000 < 94016567 / 100000000 ∧
          (94016567 : ℚ) / 100000000 < 94615981 / 100000000) ∧
        (94615981 : ℚ) / 100000000 < 83 / 84) ∧
      (83 : ℚ) / 84 < 9932 / 10000) ∧
    (∀ a : ℚ, (8785 : ℚ) / 10000 ≤ a →
      (9932 : ℚ) / 10000 < 1 - (1 - a) / 18 ∧
        ∀ τ : ℚ, τ ≤ 9932 / 10000 → τ < 1 - (1 - a) / 18) ∧
    (∀ a : ℚ, (8785 : ℚ) / 10000 ≤ a → ∀ d : ℕ, 1 ≤ d →
      (9932 : ℚ) / 10000 < 1 - (1 - a) / (6 * d + 12) ∧
        ∀ τ : ℚ, τ ≤ 9932 / 10000 → τ < 1 - (1 - a) / (6 * d + 12)) ∧
    (∀ a : ℚ, (8785 : ℚ) / 10000 ≤ a → ∀ ε : ℚ, 0 < ε →
      ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 1 - ε < 1 - (1 - a) / (6 * d + 12)) ∧
    ((87856 : ℚ) / 100000 < 9326 / 10000 ∧
      (9326 : ℚ) / 10000 - 87856 / 100000 = 5404 / 100000) ∧
    (∀ d m mc cut p q : ℕ, mc ≤ m → p ≤ q → p * mc ≤ q * cut →
      (6 * d + 12) * q * (m * (6 * d + 10) + (m + mc)) ≤
        (6 * d + 12) * q * (m * (6 * d + 10) + (m + cut)) +
          (q - p) * (m * (6 * d + 10) + (m + mc))) ∧
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
    (∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 1 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        alpha = m ∧
          IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G)) (3 * n)) ∧
    ∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 2 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        m = n ∧
          IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G)) (4 * n + alpha) :=
  ⟨⟨⟨⟨by norm_num, PalomaMax2SAT.PaperArithmetic.ugc_thresholds.1⟩,
      PalomaMax2SAT.PaperArithmetic.ugc_thresholds.2⟩, by norm_num⟩,
    fun a ha => ⟨PalomaMax2SAT.StrongLemmas.lift_gt a ha, fun τ hτ =>
      lt_of_le_of_lt hτ (PalomaMax2SAT.StrongLemmas.lift_gt a ha)⟩,
    fun a ha d hd => ⟨PalomaMax2SAT.StrongLemmas.regular_gt a ha d hd, fun τ hτ =>
      lt_of_le_of_lt hτ (PalomaMax2SAT.StrongLemmas.regular_gt a ha d hd)⟩,
    fun a ha ε hε => PalomaMax2SAT.StrongLemmas.tends_one a ha ε hε,
    ⟨by norm_num, by norm_num⟩,
    fun d m mc cut p q hmc hpq hcut =>
      PalomaMax2SAT.StrongLemmas.cut_lift_ratio d m mc cut p q hmc hpq hcut,
    fun G h => PalomaMax2SAT.ConflictGraph.alpha_eq G h,
    fun G Dmax hD p => PalomaMax2SAT.BoundedLemmas.nbrs_le G Dmax hD p,
    fun G M hM => PalomaMax2SAT.BoundedLemmas.edges_ge G M hM,
    fun m M alpha s hM ha hs => PalomaMax2SAT.BoundedLemmas.ratio_nonregular m M alpha s hM ha hs,
    fun G ha => PalomaMax2SAT.RegularLemmas.opt_deg_one G ha,
    fun G ha => PalomaMax2SAT.RegularLemmas.opt_deg_two G ha⟩

end PalomaMax2SAT.UgcStrong
