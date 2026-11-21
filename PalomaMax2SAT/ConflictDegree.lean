module

public import Mathlib
public import PalomaMax2SAT.ConflictGraph

@[expose] public section

/-!
# Degrees of the conflict graph of `F_G`

For the conflict graph `H(G)` on the literal occurrences `Occ m` of `F_G` this module proves:

* `occurrences_eq`: the variable `x_v` occurs in exactly `2 deg(v)` clauses (Proposition
  `prop:cut2sat`, item 2);
* `card_nbrs`: the occurrence `(e, s, b)` has `1 + deg(var)` neighbours, so `H(G)` is
  `(d + 1)`-regular when `G` is `d`-regular (Proposition `prop:cutconflict`);
* `ordered_edges_ge`: twice the number of edges of `H(G)` is at least `8 m`, that is,
  `M ≥ 4 m` (proof of Theorem `thm:nonreg-cutclass`).

Here `deg(v) = occ G v` is the number of edge endpoints equal to `v`.
-/

namespace PalomaMax2SAT.ConflictDegree

open PalomaMax2SAT.CutTransfer PalomaMax2SAT.ConflictGraph

variable {n m : ℕ}

/-- The degree of `v`: the number of edge endpoints equal to `v`. -/
def occ (G : EdgeGraph n m) (v : Fin n) : ℕ :=
  ∑ e : Fin m, ((if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0))

/-- The edge-endpoint slots at `v`. -/
def slots (G : EdgeGraph n m) (v : Fin n) : Finset (Fin m × Bool) :=
  Finset.univ.filter fun x => ov G x.1 x.2 = v

theorem card_slots (G : EdgeGraph n m) (v : Fin n) : (slots G v).card = occ G v := by
  unfold slots occ
  rw [Finset.card_filter]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, ov]

/-- The neighbours of an occurrence in the conflict graph. -/
def nbrs (G : EdgeGraph n m) (p : Occ m) : Finset (Occ m) :=
  Finset.univ.filter fun q => Adj G p q

theorem mem_adj_iff (G : EdgeGraph n m) (e e' : Fin m) (s s' b b' : Bool) :
    Adj G (e, s, b) (e', s', b') ↔
      (e', s', b') = (e, s, !b) ∨ (ov G e' b' = ov G e b ∧ s' = !s) := by
  unfold Adj
  cases s <;> cases s' <;> cases b <;> cases b' <;> simp [var, ov, eq_comm]

theorem nbrs_eq (G : EdgeGraph n m) (e : Fin m) (s b : Bool) :
    nbrs G (e, s, b) =
      {(e, s, !b)} ∪ ((slots G (ov G e b)).image fun x => (x.1, !s, x.2)) := by
  ext ⟨e', s', b'⟩
  simp only [nbrs, Finset.mem_filter, Finset.mem_univ, true_and, mem_adj_iff,
    Finset.mem_union, Finset.mem_singleton, Finset.mem_image, slots, Prod.exists]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e', b', h1, by rw [h2]⟩
  · rintro (h | ⟨a, c, h1, h2⟩)
    · exact Or.inl h
    · simp only [Prod.mk.injEq] at h2
      obtain ⟨h3, h4, h5⟩ := h2
      subst h3
      subst h5
      exact Or.inr ⟨h1, h4.symm⟩

theorem card_nbrs (G : EdgeGraph n m) (e : Fin m) (s b : Bool) :
    (nbrs G (e, s, b)).card = 1 + occ G (ov G e b) := by
  have hd : Disjoint ({(e, s, !b)} : Finset (Occ m))
      ((slots G (ov G e b)).image fun x => (x.1, !s, x.2)) := by
    rw [Finset.disjoint_singleton_left]
    intro hmem
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmem
    have h3 := congrArg (fun q : Occ m => q.2.1) hx
    cases s <;> simp at h3
  have hinj : Function.Injective fun x : Fin m × Bool => ((x.1, !s, x.2) : Occ m) := by
    intro x y h
    exact Prod.ext (congrArg (fun q : Occ m => q.1) h) (congrArg (fun q : Occ m => q.2.2) h)
  have h := Finset.card_union_add_card_inter ({(e, s, !b)} : Finset (Occ m))
    ((slots G (ov G e b)).image fun x => (x.1, !s, x.2))
  rw [Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.card_empty, Finset.card_singleton,
    Finset.card_image_of_injective _ hinj, card_slots] at h
  rw [nbrs_eq]
  omega

theorem one_le_occ (G : EdgeGraph n m) (e : Fin m) (b : Bool) : 1 ≤ occ G (ov G e b) := by
  rw [← card_slots]
  have h : 0 < (slots G (ov G e b)).card :=
    Finset.card_pos.mpr ⟨(e, b), by simp [slots]⟩
  omega

/-- Every occurrence has at least two neighbours. -/
theorem two_le_card_nbrs (G : EdgeGraph n m) (p : Occ m) : 2 ≤ (nbrs G p).card := by
  obtain ⟨e, s, b⟩ := p
  rw [card_nbrs]
  have := one_le_occ G e b
  omega

/-- Regularity: if every vertex of `G` has degree `d`, the conflict graph is `(d + 1)`-regular. -/
theorem card_nbrs_regular (G : EdgeGraph n m) (d : ℕ) (hd : ∀ v, occ G v = d) (p : Occ m) :
    (nbrs G p).card = d + 1 := by
  obtain ⟨e, s, b⟩ := p
  rw [card_nbrs, hd]
  omega

/-- Twice the number of edges of the conflict graph. -/
theorem ordered_edges_eq (G : EdgeGraph n m) :
    (Finset.univ.filter fun pq : Occ m × Occ m => Adj G pq.1 pq.2).card =
      ∑ p : Occ m, (nbrs G p).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [nbrs, Finset.card_filter]

/-- The conflict graph has `4 m` vertices. -/
theorem card_occ (m : ℕ) : Fintype.card (Occ m) = 4 * m := by
  simp [Occ, Fintype.card_prod] <;> ring

/-- `2 M ≥ 8 m`, that is `M ≥ 4 m`. -/
theorem ordered_edges_ge (G : EdgeGraph n m) :
    8 * m ≤ (Finset.univ.filter fun pq : Occ m × Occ m => Adj G pq.1 pq.2).card := by
  rw [ordered_edges_eq]
  have h1 : ∑ p : Occ m, (2 : ℕ) ≤ ∑ p : Occ m, (nbrs G p).card :=
    Finset.sum_le_sum fun p _ => two_le_card_nbrs G p
  rw [Finset.sum_const, Finset.card_univ, card_occ, smul_eq_mul] at h1
  omega

/-- With `M` edges in the conflict graph (`2 M` ordered pairs), `M ≥ 4 m`. -/
theorem edges_ge (G : EdgeGraph n m) (M : ℕ)
    (hM : 2 * M = (Finset.univ.filter fun pq : Occ m × Occ m => Adj G pq.1 pq.2).card) :
    4 * m ≤ M := by
  have := ordered_edges_ge G
  omega

/-- The variable `x_v` occurs in exactly `2 deg(v)` clauses. -/
theorem occurrences_eq (G : EdgeGraph n m) (v : Fin n) :
    (Finset.univ.filter fun p : Occ m => var G p = v).card = 2 * occ G v := by
  rw [Finset.card_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, var, ov]
  unfold occ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> omega

end PalomaMax2SAT.ConflictDegree
