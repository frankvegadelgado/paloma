module

public import Mathlib
public import PalomaMax2SAT.CutTransfer

@[expose] public section

/-!
# The conflict graph of `F_G` (Proposition `prop:cutconflict`)

The formula `F_G` has, for every edge `e` with endpoints `left e`, `right e`, the clauses
`(x_{left e} ∨ x_{right e})` and `(¬x_{left e} ∨ ¬x_{right e})`. Its literal occurrences are the
triples `(e, s, b)` of `Occ m`: the edge `e`, the sign `s` of the clause (`true` for the positive
clause) and the endpoint `b` (`true` for `left`). Two occurrences are adjacent in the conflict
graph when they are distinct and either lie in the same clause or belong to the same variable
with opposite signs.

This module proves `α(H) = m + maxcut(G)` for every graph `G`: independent sets of the conflict
graph have at most `m + cut(S)` elements for a suitable `S`, and every `S` yields an independent
set with exactly `m + cut(S)` elements. Regularity and the degree count are in
`PalomaMax2SAT.ConflictDegree`.
-/

namespace PalomaMax2SAT.ConflictGraph

open PalomaMax2SAT.CutTransfer

variable {n m : ℕ}

/-- Literal occurrences of `F_G`: edge, sign of the clause, endpoint. -/
abbrev Occ (m : ℕ) := Fin m × Bool × Bool

/-- The variable of the endpoint `b` of the edge `e`. -/
def ov (G : EdgeGraph n m) (e : Fin m) : Bool → Fin n
  | true => G.left e
  | false => G.right e

/-- The variable of a literal occurrence. -/
def var (G : EdgeGraph n m) (p : Occ m) : Fin n := ov G p.1 p.2.2

/-- Adjacency in the conflict graph. -/
def Adj (G : EdgeGraph n m) (p q : Occ m) : Prop :=
  p ≠ q ∧ ((p.1 = q.1 ∧ p.2.1 = q.2.1) ∨ (var G p = var G q ∧ p.2.1 ≠ q.2.1))

instance (G : EdgeGraph n m) : DecidableRel (Adj G) := fun p q => by
  unfold Adj
  infer_instance

/-- Independent sets of the conflict graph. -/
def Ind (G : EdgeGraph n m) (I : Finset (Occ m)) : Prop :=
  ∀ p ∈ I, ∀ q ∈ I, ¬ Adj G p q

def IsMaxCut (G : EdgeGraph n m) (mc : ℕ) : Prop :=
  (∀ S, cutCount G S ≤ mc) ∧ ∃ S, cutCount G S = mc

def IsIndNumber (G : EdgeGraph n m) (a : ℕ) : Prop :=
  (∀ I, Ind G I → I.card ≤ a) ∧ ∃ I, Ind G I ∧ I.card = a

/-! ### From a cut to an independent set -/

/-- Whether the occurrence `(e, s, b)` is the chosen witness of its clause under `S`. -/
def selB (G : EdgeGraph n m) (S : Finset (Fin n)) (e : Fin m) : Bool → Bool → Bool
  | true, true => decide (G.left e ∈ S)
  | true, false => decide (G.right e ∈ S) && decide (G.left e ∉ S)
  | false, true => decide (G.left e ∉ S)
  | false, false => decide (G.right e ∉ S) && decide (G.left e ∈ S)

/-- The independent set of size `m + cut(S)`. -/
def selSet (G : EdgeGraph n m) (S : Finset (Fin n)) : Finset (Occ m) :=
  Finset.univ.filter fun p => selB G S p.1 p.2.1 p.2.2 = true

theorem card_selSet (G : EdgeGraph n m) (S : Finset (Fin n)) :
    (selSet G S).card = ∑ e : Fin m, edgeValue G S e := by
  unfold selSet
  rw [Finset.card_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold edgeValue
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> simp [selB, hl, hr]

theorem var_mem_of_selB_pos (G : EdgeGraph n m) (S : Finset (Fin n)) (e : Fin m) (b : Bool)
    (h : selB G S e true b = true) : var G (e, true, b) ∈ S := by
  cases b <;> simp [selB, var, ov] at h ⊢ <;> tauto

theorem var_notMem_of_selB_neg (G : EdgeGraph n m) (S : Finset (Fin n)) (e : Fin m) (b : Bool)
    (h : selB G S e false b = true) : var G (e, false, b) ∉ S := by
  cases b <;> simp [selB, var, ov] at h ⊢ <;> tauto

theorem selSet_independent (G : EdgeGraph n m) (S : Finset (Fin n)) : Ind G (selSet G S) := by
  intro p hp q hq hadj
  obtain ⟨e, s, b⟩ := p
  obtain ⟨e', s', b'⟩ := q
  simp only [selSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  unfold Adj at hadj
  rcases hadj with ⟨hne, h | h⟩
  · obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1
    subst h2
    cases s <;> cases b <;> cases b' <;> simp_all [selB]
  · obtain ⟨h1, h2⟩ := h
    simp only at h2
    cases s <;> cases s'
    · exact h2 rfl
    · have hp' := var_notMem_of_selB_neg G S e b hp
      have hq' := var_mem_of_selB_pos G S e' b' hq
      exact hp' (by rw [h1]; exact hq')
    · have hp' := var_mem_of_selB_pos G S e b hp
      have hq' := var_notMem_of_selB_neg G S e' b' hq
      exact hq' (by rw [← h1]; exact hp')
    · exact h2 rfl

/-! ### From an independent set to a cut -/

/-- The variables that have a chosen positive literal. -/
def cutOf (G : EdgeGraph n m) (I : Finset (Occ m)) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ p ∈ I, var G p = v ∧ p.2.1 = true

theorem mem_cutOf_of_pos (G : EdgeGraph n m) (I : Finset (Occ m)) (e : Fin m) (b : Bool)
    (h : (e, true, b) ∈ I) : var G (e, true, b) ∈ cutOf G I := by
  simp only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(e, true, b), h, rfl, rfl⟩

theorem notMem_cutOf_of_neg (G : EdgeGraph n m) (I : Finset (Occ m)) (hI : Ind G I)
    (e : Fin m) (b : Bool) (h : (e, false, b) ∈ I) : var G (e, false, b) ∉ cutOf G I := by
  intro hv
  simp only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨⟨e', s', b'⟩, hp, hvar, hs⟩ := hv
  simp only at hs
  subst hs
  apply hI (e', true, b') hp (e, false, b) h
  unfold Adj
  refine ⟨?_, Or.inr ⟨hvar, ?_⟩⟩
  · intro hEq
    have h3 := congrArg (fun x : Occ m => x.2.1) hEq
    simp at h3
  · simp

/-- Per-edge bound: the number of chosen occurrences of an edge is at most the number of clauses
of that edge satisfied by `cutOf G I`. -/
theorem edge_bound (G : EdgeGraph n m) (I : Finset (Occ m)) (hI : Ind G I) (e : Fin m) :
    ((if (e, true, true) ∈ I then 1 else 0) + (if (e, true, false) ∈ I then 1 else 0)) +
      ((if (e, false, true) ∈ I then 1 else 0) + (if (e, false, false) ∈ I then 1 else 0))
      ≤ edgeValue G (cutOf G I) e := by
  have hpp : (e, true, true) ∈ I → (e, true, false) ∈ I → False := by
    intro h1 h2
    apply hI _ h1 _ h2
    unfold Adj
    refine ⟨?_, Or.inl ⟨rfl, rfl⟩⟩
    intro hEq
    have h3 := congrArg (fun x : Occ m => x.2.2) hEq
    simp at h3
  have hnn : (e, false, true) ∈ I → (e, false, false) ∈ I → False := by
    intro h1 h2
    apply hI _ h1 _ h2
    unfold Adj
    refine ⟨?_, Or.inl ⟨rfl, rfl⟩⟩
    intro hEq
    have h3 := congrArg (fun x : Occ m => x.2.2) hEq
    simp at h3
  have hl1 : (e, true, true) ∈ I → G.left e ∈ cutOf G I := fun h => mem_cutOf_of_pos G I e true h
  have hr1 : (e, true, false) ∈ I → G.right e ∈ cutOf G I :=
    fun h => mem_cutOf_of_pos G I e false h
  have hl0 : (e, false, true) ∈ I → G.left e ∉ cutOf G I :=
    fun h => notMem_cutOf_of_neg G I hI e true h
  have hr0 : (e, false, false) ∈ I → G.right e ∉ cutOf G I :=
    fun h => notMem_cutOf_of_neg G I hI e false h
  unfold edgeValue
  by_cases a1 : (e, true, true) ∈ I <;> by_cases a2 : (e, true, false) ∈ I <;>
    by_cases a3 : (e, false, true) ∈ I <;> by_cases a4 : (e, false, false) ∈ I <;>
    simp_all

theorem card_le_edgeValues (G : EdgeGraph n m) (I : Finset (Occ m)) (hI : Ind G I) :
    I.card ≤ ∑ e : Fin m, edgeValue G (cutOf G I) e := by
  have hc : I.card = ∑ p : Occ m, if p ∈ I then 1 else 0 := by
    rw [← Finset.card_filter]; congr 1; ext p; simp
  rw [hc]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  exact Finset.sum_le_sum fun e _ => edge_bound G I hI e

/-! ### The identity `α(H) = m + maxcut(G)` -/

/-- Proposition `prop:cutconflict`: the independence number of the conflict graph of `F_G` is
`m + maxcut(G)`. -/
theorem alpha_eq (G : EdgeGraph n m) {mc : ℕ} (h : IsMaxCut G mc) : IsIndNumber G (m + mc) := by
  constructor
  · intro I hI
    have h1 := card_le_edgeValues G I hI
    rw [value_eq_edges_add_cut] at h1
    have h2 := h.1 (cutOf G I)
    omega
  · obtain ⟨S, hS⟩ := h.2
    refine ⟨selSet G S, selSet_independent G S, ?_⟩
    rw [card_selSet, value_eq_edges_add_cut, hS]

end PalomaMax2SAT.ConflictGraph
