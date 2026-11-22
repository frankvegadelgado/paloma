module

public import Mathlib

@[expose] public section

/-!
# MAX-CUT as MAX 2-SAT

For a graph with edge list `left, right : Fin m → Fin n`, the formula `F_G` has, for every
edge `e`, the clauses `(x_l ∨ x_r)` and `(¬x_l ∨ ¬x_r)`. An assignment is a set `S` of
true variables. This module proves that the number of satisfied clauses is
`m + cut(S)` (Proposition `prop:cut2sat` of the paper) and the arithmetic of the ratio
transfer from `F_G` and from `T_H` to the cut.

The conflict-graph identity `α(H) = m + maxcut(G)` (Proposition `prop:cutconflict`) is
proved in `ConflictGraph`.
-/

namespace PalomaMax2SAT.CutTransfer

/-- A graph given by the endpoints of its `m` edges. -/
structure EdgeGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  left_ne_right : ∀ e, left e ≠ right e

/-- The number of edges with exactly one endpoint in `S`. -/
def cutCount {n m : ℕ} (G : EdgeGraph n m) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun e : Fin m =>
    (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)).card

/-- The number of satisfied clauses among the two clauses of the edge `e`. -/
def edgeValue {n m : ℕ} (G : EdgeGraph n m) (S : Finset (Fin n)) (e : Fin m) : ℕ :=
  (if G.left e ∈ S ∨ G.right e ∈ S then 1 else 0) +
    (if G.left e ∉ S ∨ G.right e ∉ S then 1 else 0)

theorem edgeValue_eq {n m : ℕ} (G : EdgeGraph n m) (S : Finset (Fin n)) (e : Fin m) :
    edgeValue G S e = 1 +
      (if (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)
        then 1 else 0) := by
  unfold edgeValue
  by_cases ha : G.left e ∈ S <;> by_cases hb : G.right e ∈ S <;> simp [ha, hb]

/-- Proposition `prop:cut2sat`: the assignment `S` satisfies exactly `m + cut(S)`
clauses of `F_G`. -/
theorem value_eq_edges_add_cut {n m : ℕ} (G : EdgeGraph n m) (S : Finset (Fin n)) :
    ∑ e : Fin m, edgeValue G S e = m + cutCount G S := by
  unfold cutCount
  rw [Finset.card_filter, Finset.sum_congr rfl (fun e _ => edgeValue_eq G S e),
    Finset.sum_add_distrib]
  simp

/-- Ratio transfer from `F_G`: `p (m + c) ≤ q A` and `A ≤ m + cut` give
`p (m + c) ≤ q (m + cut)`; that is, `cut ≥ ρ (m + c) - m` for `ρ = p / q`. -/
theorem cut_from_2sat_value (p q m c A cut : ℕ) (hA : p * (m + c) ≤ q * A)
    (hcut : A ≤ m + cut) : p * (m + c) ≤ q * (m + cut) :=
  le_trans hA (Nat.mul_le_mul_left q hcut)

/-- Ratio transfer from `T_H`: with `A ≤ B + m + cut` (repair of an assignment of value
`A` followed by Proposition `prop:cut2sat`), `p (B + m + c) ≤ q A` gives
`p (B + m + c) ≤ q (B + m + cut)`. -/
theorem cut_from_TH_value (p q B m c A cut : ℕ) (hA : p * (B + m + c) ≤ q * A)
    (hcut : A ≤ B + m + cut) : p * (B + m + c) ≤ q * (B + m + cut) :=
  le_trans hA (Nat.mul_le_mul_left q hcut)

/-- For a `d`-regular graph with `2 m = d n`, the constant of `T_H` is
`B = (D+1) N + M = 2 m (3 d + 5)` with `D = d + 1`, `N = 4 m`, `2 M = D N`. -/
theorem constant_B (d m N M : ℕ) (hN : N = 4 * m) (hM : 2 * M = (d + 1) * N) :
    (d + 1 + 1) * N + M = 2 * m * (3 * d + 5) := by
  subst hN
  nlinarith [hM]

/-- From a cut with `8785 · maxcut ≤ 10000 · cut` (a Goemans--Williamson cut, whose constant
exceeds `0.8785`) and `maxcut ≤ m`, the independent set of size `m + cut` of the conflict
graph satisfies `18785 α ≤ 20000 |I|` with `α = m + maxcut`. -/
theorem independent_ratio_from_cut (m c cut : ℕ) (hc : c ≤ m)
    (hcut : 8785 * c ≤ 10000 * cut) : 18785 * (m + c) ≤ 20000 * (m + cut) := by
  omega

/-- `18785 α ≤ 20000 |I|` implies the threshold hypothesis `27 α ≤ 28 |I| + D α` of the
degree-`D` transfer for every `D ≥ 1`. -/
theorem threshold_from_cut (D a s : ℕ) (hD : 1 ≤ D) (hs : 18785 * a ≤ 20000 * s) :
    27 * a ≤ 28 * s + D * a := by
  have h : 1 * a ≤ D * a := Nat.mul_le_mul_right a hD
  omega

end PalomaMax2SAT.CutTransfer
