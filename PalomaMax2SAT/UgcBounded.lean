module

public import Mathlib
public import PalomaMax2SAT.GeneralDegreeFormula
public import PalomaMax2SAT.CutTransfer
public import PalomaMax2SAT.ConflictGraph
public import PalomaMax2SAT.ConflictDegree
public import PalomaMax2SAT.PaperArithmetic

@[expose] public section

/-!
# Theorem `thm:ugc-class` for bounded degree: the ratio above the Unique Games thresholds

The formalized parts of Theorem `thm:ugc-class` and of the non-regular family behind it
(Theorem `thm:nonreg-cutclass`, Lemma `lem:general-identity`):

1. `83/84 < 0.9932` and `83/84 > 0.94615981 > 0.94016567`;
2. the occurrences selected by a vertex set `S` of `G` form an independent set of the conflict
   graph `H(G)` of size `m + cut(S)`, and `α(H(G)) = m + maxcut(G)`;
3. if `G` has maximum degree at most `Δ`, every vertex of `H(G)` has degree at most `Δ + 1`;
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

/-- The degrees of the vertices of `G` add up to `2 m`. -/
theorem sum_occ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) :
    ∑ v, PalomaMax2SAT.ConflictDegree.occ G v = 2 * m := by
  unfold PalomaMax2SAT.ConflictDegree.occ
  rw [Finset.sum_comm]
  have h : ∀ e : Fin m, ∑ v : Fin n,
      ((if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0)) = 2 := by
    intro e
    rw [Finset.sum_add_distrib]
    simp
  rw [Finset.sum_congr rfl (fun e _ => h e), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

/-- The degree sum of the conflict graph: `Σ_p deg(p) = 4 m + 2 Σ_v deg(v)²`. -/
theorem sum_nbrs {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) :
    ∑ p : PalomaMax2SAT.ConflictGraph.Occ m, (PalomaMax2SAT.ConflictDegree.nbrs G p).card =
      4 * m + 2 * ∑ v, PalomaMax2SAT.ConflictDegree.occ G v ^ 2 := by
  have h1 : ∀ p : PalomaMax2SAT.ConflictGraph.Occ m,
      (PalomaMax2SAT.ConflictDegree.nbrs G p).card =
        1 + PalomaMax2SAT.ConflictDegree.occ G (PalomaMax2SAT.ConflictGraph.var G p) := by
    rintro ⟨e, s, b⟩
    exact PalomaMax2SAT.ConflictDegree.card_nbrs G e s b
  rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, PalomaMax2SAT.ConflictDegree.card_occ, smul_eq_mul, mul_one]
  have h2 : ∑ p : PalomaMax2SAT.ConflictGraph.Occ m,
      PalomaMax2SAT.ConflictDegree.occ G (PalomaMax2SAT.ConflictGraph.var G p) =
        ∑ v, 2 * PalomaMax2SAT.ConflictDegree.occ G v *
          PalomaMax2SAT.ConflictDegree.occ G v := by
    have hf := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (PalomaMax2SAT.ConflictGraph.Occ m)))
      (t := (Finset.univ : Finset (Fin n))) (g := PalomaMax2SAT.ConflictGraph.var G)
      (fun p _ => Finset.mem_univ _)
      (fun p => PalomaMax2SAT.ConflictDegree.occ G (PalomaMax2SAT.ConflictGraph.var G p))
    rw [← hf]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hv : ∀ p ∈ Finset.univ.filter
        (fun p : PalomaMax2SAT.ConflictGraph.Occ m =>
          PalomaMax2SAT.ConflictGraph.var G p = v),
        PalomaMax2SAT.ConflictDegree.occ G (PalomaMax2SAT.ConflictGraph.var G p) =
          PalomaMax2SAT.ConflictDegree.occ G v := by
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    rw [Finset.sum_congr rfl hv, Finset.sum_const, smul_eq_mul,
      PalomaMax2SAT.ConflictDegree.occurrences_eq]
  have h3 : ∑ v, 2 * PalomaMax2SAT.ConflictDegree.occ G v *
      PalomaMax2SAT.ConflictDegree.occ G v =
        2 * ∑ v, PalomaMax2SAT.ConflictDegree.occ G v ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [h2, h3]

/-- The conflict graph has at least `4 m` edges: if `2 M = Σ_p deg(p)` then `4 m ≤ M`. -/
theorem edges_ge {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (M : ℕ)
    (hM : 2 * M = ∑ p : PalomaMax2SAT.ConflictGraph.Occ m,
      (PalomaMax2SAT.ConflictDegree.nbrs G p).card) :
    2 * M = 4 * m + 2 * ∑ v, PalomaMax2SAT.ConflictDegree.occ G v ^ 2 ∧ 4 * m ≤ M := by
  have h1 := sum_nbrs G
  have h2 := sum_occ G
  have h3 : ∑ v, PalomaMax2SAT.ConflictDegree.occ G v ≤
      ∑ v, PalomaMax2SAT.ConflictDegree.occ G v ^ 2 := by
    apply Finset.sum_le_sum
    intro v _
    calc PalomaMax2SAT.ConflictDegree.occ G v
        ≤ PalomaMax2SAT.ConflictDegree.occ G v * PalomaMax2SAT.ConflictDegree.occ G v :=
          Nat.le_mul_self _
      _ = PalomaMax2SAT.ConflictDegree.occ G v ^ 2 := (sq _).symm
  constructor
  · omega
  · omega

/-- With `N = 4 m`, `4 m ≤ M`, `α ≤ 2 m` and `18785 α ≤ 20000 s`, the value `B + s` with
`B = N + 3 M` satisfies `9932 (B + α) ≤ 10000 (B + s)` and `83 (B + α) ≤ 84 (B + s)`. -/
theorem ratio_nonregular (m M alpha s : ℕ) (hM : 4 * m ≤ M) (ha : alpha ≤ 2 * m)
    (hs : 18785 * alpha ≤ 20000 * s) :
    9932 * ((4 * m + 3 * M) + alpha) ≤ 10000 * ((4 * m + 3 * M) + s) ∧
      83 * ((4 * m + 3 * M) + alpha) ≤ 84 * ((4 * m + 3 * M) + s) := by
  constructor <;> omega

/-- A graph of maximum degree at most `Δ` has a conflict graph of maximum degree at most
`Δ + 1`. -/
theorem nbrs_le {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (Δ : ℕ)
    (hΔ : ∀ v, PalomaMax2SAT.ConflictDegree.occ G v ≤ Δ)
    (p : PalomaMax2SAT.ConflictGraph.Occ m) :
    (PalomaMax2SAT.ConflictDegree.nbrs G p).card ≤ Δ + 1 := by
  obtain ⟨e, s, b⟩ := p
  rw [PalomaMax2SAT.ConflictDegree.card_nbrs]
  have := hΔ (PalomaMax2SAT.ConflictGraph.ov G e b)
  omega

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
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (Δ : ℕ),
      (∀ v, PalomaMax2SAT.ConflictDegree.occ G v ≤ Δ) →
        ∀ p : PalomaMax2SAT.ConflictGraph.Occ m,
          (PalomaMax2SAT.ConflictDegree.nbrs G p).card ≤ Δ + 1) ∧
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
    fun G Δ hΔ p => nbrs_le G Δ hΔ p,
    fun G M hM => edges_ge G M hM,
    fun m M alpha s hM ha hs => ratio_nonregular m M alpha s hM ha hs,
    fun G => ⟨PalomaMax2SAT.GeneralDegreeFormula.sum_deg_eq G,
      PalomaMax2SAT.GeneralDegreeFormula.constant_eq G⟩,
    fun G halpha => PalomaMax2SAT.GeneralDegreeFormula.optimum_identity G halpha,
    fun G halpha I hI hB hs => by
      have hlift := PalomaMax2SAT.GeneralDegreeFormula.lift_satCount G I hI
      refine ⟨hlift, ?_, ?_⟩ <;> rw [hlift] <;> omega⟩

end PalomaMax2SAT.UgcBounded
