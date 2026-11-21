module

public import Mathlib

@[expose] public section

/-!
# The `L`-reduction constants of Theorem `thm:apx`

For a graph of maximum degree `Δ` a greedy maximal independent set has at least `n / (Δ + 1)`
vertices. This gives the first `L`-reduction constant of the map `H ↦ T_H`. The second constant
is `1` by the quantitative repair.

* `exists_large_independent`: every graph on `n` vertices in which each vertex has at most `Δ`
  neighbours has an independent set `I` with `n ≤ (Δ + 1) |I|`;
* `opt_le_const`: with `OPT = (d + 1) n + m + α`, `2 m = d n` and `n ≤ (d + 1) α`, one has
  `2 OPT ≤ ((3 d + 2)(d + 1) + 2) α`;
* `cubic_opt_le`: the case `d = 3`, `OPT ≤ 23 α`;
* `repair_le`, `repair_abs_le`: `α - |R| ≤ OPT - A`.

That cubic MIS is APX-complete is a cited result and is not formalized.
-/

namespace PalomaMax2SAT.LReduction

variable {n : ℕ}

/-- A greedy (maximum-cardinality) independent set in a graph with all degrees at most `Δ`
has at least `n / (Δ + 1)` vertices. -/
theorem exists_large_independent (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (Δ : ℕ)
    (hdeg : ∀ v, (Finset.univ.filter fun u => G.Adj v u).card ≤ Δ) :
    ∃ I : Finset (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ n ≤ (Δ + 1) * I.card := by
  classical
  let S : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun I => ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v
  have hS : S.Nonempty := ⟨∅, by simp [S]⟩
  obtain ⟨I, hIS, hmax⟩ := Finset.exists_max_image S Finset.card hS
  have hI : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    simpa [S] using hIS
  refine ⟨I, hI, ?_⟩
  have hcover : ∀ v, v ∈ I ∨ ∃ u ∈ I, G.Adj u v := by
    intro v
    by_contra hcon
    push_neg at hcon
    obtain ⟨hvI, hnadj⟩ := hcon
    have hins : insert v I ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with ha' | ha' <;>
        rcases Finset.mem_insert.mp hb with hb' | hb'
      · rw [ha', hb'] at hab
        exact G.irrefl hab
      · rw [ha'] at hab
        exact hnadj b hb' hab.symm
      · rw [hb'] at hab
        exact hnadj a ha' hab
      · exact hI a ha' b hb' hab
    have h1 := hmax _ hins
    have h2 := Finset.card_lt_card (Finset.ssubset_insert hvI)
    omega
  have hsub : (Finset.univ : Finset (Fin n)) ⊆
      I.biUnion fun u => insert u (Finset.univ.filter fun w => G.Adj u w) := by
    intro v _
    rcases hcover v with hv | ⟨u, hu, huv⟩
    · exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_insert_self _ _⟩
    · refine Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_insert_of_mem ?_⟩
      simpa using huv
  have hb : ∀ u ∈ I, (insert u (Finset.univ.filter fun w => G.Adj u w)).card ≤ Δ + 1 :=
    fun u _ => le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (hdeg u))
  have h3 : (Finset.univ : Finset (Fin n)).card ≤
      (I.biUnion fun u => insert u (Finset.univ.filter fun w => G.Adj u w)).card :=
    Finset.card_le_card hsub
  have h4 := Finset.card_biUnion_le (s := I)
    (t := fun u => insert u (Finset.univ.filter fun w => G.Adj u w))
  have h5 : ∑ u ∈ I, (insert u (Finset.univ.filter fun w => G.Adj u w)).card ≤
      ∑ u ∈ I, (Δ + 1) := Finset.sum_le_sum hb
  rw [Finset.sum_const, smul_eq_mul] at h5
  have h6 : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [h6] at h3
  calc n ≤ I.card * (Δ + 1) := le_trans h3 (le_trans h4 h5)
    _ = (Δ + 1) * I.card := Nat.mul_comm _ _

/-- First `L`-reduction inequality for a `d`-regular graph with `2 m = d n` and
`n ≤ (d + 1) α`: `2 OPT ≤ ((3 d + 2)(d + 1) + 2) α`. -/
theorem opt_le_const (d n m α : ℕ) (hm : 2 * m = d * n) (hn : n ≤ (d + 1) * α) :
    2 * ((d + 1) * n + m + α) ≤ ((3 * d + 2) * (d + 1) + 2) * α := by
  have h := Nat.mul_le_mul_left (3 * d + 2) hn
  nlinarith [hm, h]

/-- The first `L`-reduction constant of Theorem `thm:apx`: for a cubic graph,
`OPT(T_H) = 4 n + m + α ≤ 23 α`. -/
theorem cubic_opt_le (n m α : ℕ) (hm : 2 * m = 3 * n) (hn : n ≤ 4 * α) :
    4 * n + m + α ≤ 23 * α := by
  omega

/-- Second `L`-reduction inequality, with constant `1`: an assignment of value `A` repairs to an
independent set of size `r ≥ A - B`, and `OPT = B + α`. -/
theorem repair_le (B α A r : ℕ) (hA : A ≤ B + r) (hAopt : A ≤ B + α) :
    α ≤ r + (B + α - A) := by
  omega

theorem repair_abs_le (B α A r : ℕ) (hA : A ≤ B + r) (hr : r ≤ α) :
    α - r ≤ B + α - A := by
  omega

end PalomaMax2SAT.LReduction
