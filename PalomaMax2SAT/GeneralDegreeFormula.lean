module

public import Mathlib

@[expose] public section

/-!
# The formula `T_H` for arbitrary simple graphs: score, repair and exact optimum

For a graph `H` whose vertex `v` has degree `deg v` (not necessarily regular), the formula
`T_H` has `deg v + 1` clones of `v`: clone `0` occurs in the unit clause `(¬ z_{v,0})`,
the other clones occur in the edge clauses, and the cyclic implications
`(¬ z_{v,i} ∨ z_{v,i+1})` (indices modulo `deg v + 1`) link them.  The optimum is
`B + α(H)` with `B = Σ_v (deg v + 1) + m`, which equals `n + 3m` because `Σ_v deg v = 2m`
(Lemma `lem:general-identity` of the paper).

This module proves, at the level of the number of satisfied clauses
(unit + edge + cyclic clauses, as in `DegreeFormula.score`):

* the repair inequality `score z ≤ B + |R(z)|` with `R(z)` independent;
* the lift of an independent set `I` scores `B + |I|`;
* hence the exact identity `max score = B + α`;
* the division-free ratio step used for Theorem `thm:nonreg-cutclass`.

The explicit Horn clause list and the three-occurrence count are proved for the regular
case in `DegreeFormula`; they are not re-proved here.  The sum `Σ deg v = 2m` is not
needed by the proofs below, so `B` is stated as `Σ (deg v + 1) + m`; under that sum
identity it equals `n + 3m`.
-/

namespace PalomaMax2SAT.GeneralDegreeFormula

/-- A graph with `n` vertices, `m` edges, vertex degrees `deg`, and for every edge the clone
of each endpoint that carries the edge clause. -/
structure Graph (n m : ℕ) (deg : Fin n → ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  left_ne_right : ∀ e, left e ≠ right e
  leftClone : ∀ e, Fin (deg (left e) + 1)
  rightClone : ∀ e, Fin (deg (right e) + 1)

variable {n m : ℕ} {deg : Fin n → ℕ}

/-- The constant `B = Σ_v (deg v + 1) + m`. -/
def base (deg : Fin n → ℕ) (m : ℕ) : ℕ := (∑ v, (deg v + 1)) + m

/-- Under `Σ deg v = 2 m`, `B = n + 3 m`. -/
theorem base_eq_of_degree_sum (hdeg : ∑ v, deg v = 2 * m) :
    base deg m = n + 3 * m := by
  unfold base
  rw [Finset.sum_add_distrib]
  simp
  omega

def Independent (G : Graph n m deg) (I : Finset (Fin n)) : Prop :=
  ∀ e, ¬ (G.left e ∈ I ∧ G.right e ∈ I)

def IsIndependenceNumber (G : Graph n m deg) (alpha : ℕ) : Prop :=
  (∀ I, Independent G I → I.card ≤ alpha) ∧ ∃ I, Independent G I ∧ I.card = alpha

abbrev transition (z : (v : Fin n) → Fin (deg v + 1) → Bool)
    (v : Fin n) (i : Fin (deg v + 1)) : Prop :=
  z v i = true ∧ z v (i + 1) = false

def selectedVertices (z : (v : Fin n) → Fin (deg v + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => z v 0 = false

noncomputable def transitionPairs (z : (v : Fin n) → Fin (deg v + 1) → Bool) :
    Finset (Σ v : Fin n, Fin (deg v + 1)) :=
  Finset.univ.filter fun pair => transition z pair.1 pair.2

noncomputable def transitionVertices (z : (v : Fin n) → Fin (deg v + 1) → Bool) :
    Finset (Fin n) :=
  (transitionPairs z).image Sigma.fst

noncomputable def cleanVertices (z : (v : Fin n) → Fin (deg v + 1) → Bool) :
    Finset (Fin n) :=
  selectedVertices z \ transitionVertices z

def falseEdges (G : Graph n m deg) (z : (v : Fin n) → Fin (deg v + 1) → Bool) :
    Finset (Fin m) :=
  Finset.univ.filter fun e =>
    z (G.left e) (G.leftClone e) = false ∧ z (G.right e) (G.rightClone e) = false

noncomputable def deletionSet (G : Graph n m deg)
    (z : (v : Fin n) → Fin (deg v + 1) → Bool) : Finset (Fin n) :=
  (Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z).image G.left

noncomputable def repairedSet (G : Graph n m deg)
    (z : (v : Fin n) → Fin (deg v + 1) → Bool) : Finset (Fin n) :=
  cleanVertices z \ deletionSet G z

/-- Satisfied unit, edge and cyclic clauses. -/
noncomputable def score (G : Graph n m deg)
    (z : (v : Fin n) → Fin (deg v + 1) → Bool) : ℕ :=
  (selectedVertices z).card + (m - (falseEdges G z).card) +
    ((∑ v, (deg v + 1)) - (transitionPairs z).card)

/-- Cycle lemma (`lem:cycle`) for a cycle of any length `k + 1 ≥ 1`: a word starting with
`false` and having no `true`-to-`false` transition is constantly `false`. -/
theorem cycle_all_false {k : ℕ} (w : Fin (k + 1) → Bool) (h0 : w 0 = false)
    (hnone : ∀ i, ¬ (w i = true ∧ w (i + 1) = false)) : ∀ i, w i = false := by
  have back : ∀ i, w (i + 1) = false → w i = false := by
    intro i hi
    cases h : w i with
    | false => rfl
    | true => exact absurd ⟨h, hi⟩ (hnone i)
  have hlast : w (Fin.last k) = false := by
    apply back
    rw [Fin.last_add_one]
    exact h0
  intro i
  refine Fin.reverseInduction (motive := fun i => w i = false) hlast ?_ i
  intro j hj
  apply back
  rw [Fin.coeSucc_eq_succ]
  exact hj

private theorem no_transition_all_false (z : (v : Fin n) → Fin (deg v + 1) → Bool)
    (v : Fin n) (hzero : z v 0 = false)
    (hnone : v ∉ transitionVertices z) : ∀ i, z v i = false := by
  apply cycle_all_false (z v) hzero
  intro i hi
  apply hnone
  exact Finset.mem_image.mpr
    ⟨⟨v, i⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

theorem repairedSet_independent (G : Graph n m deg)
    (z : (v : Fin n) → Fin (deg v + 1) → Bool) : Independent G (repairedSet G z) := by
  intro e he
  rcases he with ⟨hl, hr⟩
  have hlc : G.left e ∈ cleanVertices z := (Finset.mem_sdiff.mp hl).1
  have hrc : G.right e ∈ cleanVertices z := (Finset.mem_sdiff.mp hr).1
  have hdel : G.left e ∈ deletionSet G z := by
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlc, hrc⟩, rfl⟩
  exact (Finset.mem_sdiff.mp hl).2 hdel

private theorem internalEdges_subset_falseEdges (G : Graph n m deg)
    (z : (v : Fin n) → Fin (deg v + 1) → Bool) :
    (Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z) ⊆ falseEdges G z := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨_, hl, hr⟩
  have hleft0 := (Finset.mem_sdiff.mp hl).1
  have hleftT := (Finset.mem_sdiff.mp hl).2
  have hright0 := (Finset.mem_sdiff.mp hr).1
  have hrightT := (Finset.mem_sdiff.mp hr).2
  have al : ∀ i, z (G.left e) i = false :=
    no_transition_all_false z (G.left e) (Finset.mem_filter.mp hleft0).2 hleftT
  have ar : ∀ i, z (G.right e) i = false :=
    no_transition_all_false z (G.right e) (Finset.mem_filter.mp hright0).2 hrightT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, al _, ar _⟩

/-- Repair inequality: `score z ≤ B + |R(z)|` with `B = Σ (deg v + 1) + m`. -/
theorem score_le_base_add_repaired (G : Graph n m deg)
    (z : (v : Fin n) → Fin (deg v + 1) → Bool) :
    score G z ≤ base deg m + (repairedSet G z).card := by
  have htrans : (transitionVertices z).card ≤ (transitionPairs z).card :=
    Finset.card_image_le
  have hclean : (selectedVertices z).card ≤
      (cleanVertices z).card + (transitionVertices z).card := by
    rw [← Finset.card_sdiff_add_card_inter (selectedVertices z) (transitionVertices z)]
    exact Nat.add_le_add_left
      (Finset.card_le_card Finset.inter_subset_right) _
  have hdel : (deletionSet G z).card ≤ (falseEdges G z).card := by
    calc
      (deletionSet G z).card ≤
          (Finset.univ.filter fun e =>
            G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z).card :=
        Finset.card_image_le
      _ ≤ (falseEdges G z).card :=
        Finset.card_le_card (internalEdges_subset_falseEdges G z)
  have hfalseBound : (falseEdges G z).card ≤ m := by
    simpa using Finset.card_le_univ (falseEdges G z)
  have htransitionBound : (transitionPairs z).card ≤ ∑ v, (deg v + 1) := by
    have h := Finset.card_le_univ (transitionPairs z)
    simpa [Fintype.card_sigma] using h
  have hrepair : (cleanVertices z).card ≤
      (repairedSet G z).card + (deletionSet G z).card := by
    rw [← Finset.card_sdiff_add_card_inter (cleanVertices z) (deletionSet G z)]
    exact Nat.add_le_add_left
      (Finset.card_le_card Finset.inter_subset_right) _
  unfold score base
  omega

/-- The assignment that sets all clones of `v` to `false` exactly when `v ∈ I`. -/
def assignmentOfIndependent (I : Finset (Fin n)) :
    (v : Fin n) → Fin (deg v + 1) → Bool :=
  fun v _ => if v ∈ I then false else true

theorem score_assignmentOfIndependent (G : Graph n m deg)
    (I : Finset (Fin n)) (hI : Independent G I) :
    score G (assignmentOfIndependent I) = base deg m + I.card := by
  have hselected : selectedVertices (assignmentOfIndependent (deg := deg) I) = I := by
    ext v
    simp [selectedVertices, assignmentOfIndependent]
  have htransition : transitionPairs (assignmentOfIndependent (deg := deg) I) = ∅ := by
    ext pair
    simp [transitionPairs, transition, assignmentOfIndependent]
  have hfalse : falseEdges G (assignmentOfIndependent I) = ∅ := by
    ext e
    simp [falseEdges, assignmentOfIndependent, hI e]
  simp only [score, base, hselected, htransition, hfalse, Finset.card_empty, Nat.sub_zero]
  omega

/-- Lemma `lem:general-identity`: the optimum is `B + α` for arbitrary degrees. -/
theorem exact_general_identity {alpha : ℕ} (G : Graph n m deg)
    (halpha : IsIndependenceNumber G alpha) :
    (∀ z : (v : Fin n) → Fin (deg v + 1) → Bool, score G z ≤ base deg m + alpha) ∧
      ∃ z : (v : Fin n) → Fin (deg v + 1) → Bool, score G z = base deg m + alpha := by
  constructor
  · intro z
    calc
      score G z ≤ base deg m + (repairedSet G z).card := score_le_base_add_repaired G z
      _ ≤ base deg m + alpha :=
        Nat.add_le_add_left (halpha.1 _ (repairedSet_independent G z)) _
  · obtain ⟨I, hI, hcard⟩ := halpha.2
    exact ⟨assignmentOfIndependent I, by
      rw [score_assignmentOfIndependent G I hI, hcard]⟩

/-- The same identity with `B = n + 3 m` when `Σ deg v = 2 m`. -/
theorem exact_general_identity_n3m {alpha : ℕ} (G : Graph n m deg)
    (hdeg : ∑ v, deg v = 2 * m) (halpha : IsIndependenceNumber G alpha) :
    (∀ z : (v : Fin n) → Fin (deg v + 1) → Bool, score G z ≤ n + 3 * m + alpha) ∧
      ∃ z : (v : Fin n) → Fin (deg v + 1) → Bool, score G z = n + 3 * m + alpha := by
  rw [← base_eq_of_degree_sum hdeg]
  exact exact_general_identity G halpha

/-- Division-free ratio step of Theorem `thm:nonreg-cutclass`: if `8 α ≤ B` and the
independent set has `18785 α ≤ 20000 s`, then `0.9932 (B + α) ≤ B + s`. -/
theorem ratio_step {B alpha s : ℕ} (hB : 8 * alpha ≤ B)
    (hs : 18785 * alpha ≤ 20000 * s) : 9932 * (B + alpha) ≤ 10000 * (B + s) := by
  omega

/-- A lifted independent set of size `s` attains ratio `0.9932` against the optimum. -/
theorem lift_ratio_general {alpha : ℕ} (G : Graph n m deg)
    (halpha : IsIndependenceNumber G alpha) (I : Finset (Fin n)) (hI : Independent G I)
    (hB : 8 * alpha ≤ base deg m) (hs : 18785 * alpha ≤ 20000 * I.card) :
    9932 * (base deg m + alpha) ≤ 10000 * score G (assignmentOfIndependent I) := by
  have := ratio_step hB hs
  rw [score_assignmentOfIndependent G I hI]
  exact this

/-- Conflict-graph arithmetic of Theorem `thm:nonreg-cutclass`: `Σ d_v ≤ Σ d_v²`. -/
theorem sum_le_sum_mul_self {ι : Type*} [Fintype ι] (deg : ι → ℕ) :
    ∑ v, deg v ≤ ∑ v, deg v * deg v :=
  Finset.sum_le_sum fun v _ => Nat.le_mul_self _

/-- `M = 2m + Σ d_v²` and `Σ d_v = 2m` give `4m ≤ M`. -/
theorem conflict_edges_ge {ι : Type*} [Fintype ι] (deg : ι → ℕ) (m M : ℕ)
    (hsum : ∑ v, deg v = 2 * m) (hM : M = 2 * m + ∑ v, deg v * deg v) : 4 * m ≤ M := by
  have := sum_le_sum_mul_self deg
  omega

/-- `N = 4m`, `4m ≤ M` and `α ≤ 2m` give `8 α ≤ B = N + 3M`. -/
theorem conflict_base_ge {m N M alpha : ℕ} (hN : N = 4 * m) (hM : 4 * m ≤ M)
    (halpha : alpha ≤ 2 * m) : 8 * alpha ≤ N + 3 * M := by
  omega

end PalomaMax2SAT.GeneralDegreeFormula
