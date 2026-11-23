module

public import Mathlib
public import PalomaMax2SAT.CutTransfer
public import PalomaMax2SAT.ConflictGraph
public import PalomaMax2SAT.ConflictDegree

@[expose] public section

/-!
# Counting lemmas for the conflict graph of a bounded-degree graph

Degree sums, the edge-count lower bound `|E(H(G))| ≥ 4 m`, the maximum-degree bound
`Dmax + 1`, and the division-free ratio arithmetic used by `PalomaMax2SAT.UgcBounded.ugc_bounded`.
-/

namespace PalomaMax2SAT.BoundedLemmas


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

/-- A graph of maximum degree at most `Dmax` has a conflict graph of maximum degree at most
`Dmax + 1`. -/
theorem nbrs_le {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (Dmax : ℕ)
    (hD : ∀ v, PalomaMax2SAT.ConflictDegree.occ G v ≤ Dmax)
    (p : PalomaMax2SAT.ConflictGraph.Occ m) :
    (PalomaMax2SAT.ConflictDegree.nbrs G p).card ≤ Dmax + 1 := by
  obtain ⟨e, s, b⟩ := p
  rw [PalomaMax2SAT.ConflictDegree.card_nbrs]
  have := hD (PalomaMax2SAT.ConflictGraph.ov G e b)
  omega

end PalomaMax2SAT.BoundedLemmas
