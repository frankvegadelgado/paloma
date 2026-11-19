module

public import Mathlib

public section

/-!
# A cubic three-occurrence MAX-HORN-2SAT class

The four clones at each vertex consist of one unit-clause clone and three
edge-clause clones. Four cyclic implications enforce consistency. Every clone
therefore has one source occurrence and two consistency occurrences.
-/

namespace PalomaMax2SAT.CubicThreeOccurrence

structure PortGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  left_ne_right : ∀ e, left e ≠ right e
  leftPort : Fin m → Fin 3
  rightPort : Fin m → Fin 3
  left_unique : ∀ e f, left e = left f → leftPort e = leftPort f → e = f
  right_unique : ∀ e f, right e = right f → rightPort e = rightPort f → e = f
  cross_unique : ∀ e f, left e = right f → leftPort e = rightPort f → False

def Independent {n m : ℕ} (G : PortGraph n m) (I : Finset (Fin n)) : Prop :=
  ∀ e, ¬ (G.left e ∈ I ∧ G.right e ∈ I)

def IsIndependenceNumber {n m : ℕ} (G : PortGraph n m) (alpha : ℕ) : Prop :=
  (∀ I, Independent G I → I.card ≤ alpha) ∧
    ∃ I, Independent G I ∧ I.card = alpha

def edgeClone (p : Fin 3) : Fin 4 := ⟨p.val + 1, by omega⟩

abbrev transition {n : ℕ} (z : Fin n → Fin 4 → Bool)
    (v : Fin n) (i : Fin 4) : Prop :=
  z v i = true ∧ z v ⟨(i.val + 1) % 4, Nat.mod_lt _ (by omega)⟩ = false

def selectedVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => z v 0 = false

def transitionPairs {n : ℕ} (z : Fin n → Fin 4 → Bool) :
    Finset (Fin n × Fin 4) :=
  Finset.univ.filter fun pair => transition z pair.1 pair.2

def transitionVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  (transitionPairs z).image Prod.fst

def cleanVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  selectedVertices z \ transitionVertices z

def falseEdges {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun e =>
    z (G.left e) (edgeClone (G.leftPort e)) = false ∧
      z (G.right e) (edgeClone (G.rightPort e)) = false

def deletionSet {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  ((Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z).image G.left)

def repairedSet {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  cleanVertices z \ deletionSet G z

/-- Satisfied unit, edge, and cyclic-consistency clauses. -/
def score {n m : ℕ} (G : PortGraph n m) (z : Fin n → Fin 4 → Bool) : ℕ :=
  (selectedVertices z).card + (m - (falseEdges G z).card) +
    (4 * n - (transitionPairs z).card)

private theorem no_transition_all_false {n : ℕ} (z : Fin n → Fin 4 → Bool)
    (v : Fin n) (hzero : z v 0 = false)
    (hnone : v ∉ transitionVertices z) : ∀ i, z v i = false := by
  have ht : ∀ i, ¬ transition z v i := by
    intro i hi
    apply hnone
    exact Finset.mem_image.mpr
      ⟨(v, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  have ht0 := ht 0
  have ht1 := ht 1
  have ht2 := ht 2
  have ht3 := ht 3
  generalize h0 : z v 0 = b0 at hzero ht0 ht1 ht2 ht3 ⊢
  generalize h1 : z v 1 = b1 at ht0 ht1 ht2 ht3 ⊢
  generalize h2 : z v 2 = b2 at ht0 ht1 ht2 ht3 ⊢
  generalize h3 : z v 3 = b3 at ht0 ht1 ht2 ht3 ⊢
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    intro i <;> fin_cases i <;> simp_all [transition]

theorem repairedSet_independent_proof {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Independent G (repairedSet G z) := by
  intro e he
  rcases he with ⟨hl, hr⟩
  have hlc : G.left e ∈ cleanVertices z := (Finset.mem_sdiff.mp hl).1
  have hrc : G.right e ∈ cleanVertices z := (Finset.mem_sdiff.mp hr).1
  have hdel : G.left e ∈ deletionSet G z := by
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlc, hrc⟩, rfl⟩
  exact (Finset.mem_sdiff.mp hl).2 hdel

private theorem internalEdges_subset_falseEdges {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) :
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

theorem repairedSet_card_lower_bound_proof {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) :
    score G z ≤ 4 * n + m + (repairedSet G z).card := by
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
  have htransitionBound : (transitionPairs z).card ≤ 4 * n := by
    calc
      (transitionPairs z).card ≤
          (Finset.univ : Finset (Fin n × Fin 4)).card := Finset.card_le_univ _
      _ = 4 * n := by simp [Nat.mul_comm]
  have hrepair : (cleanVertices z).card ≤
      (repairedSet G z).card + (deletionSet G z).card := by
    rw [← Finset.card_sdiff_add_card_inter (cleanVertices z) (deletionSet G z)]
    exact Nat.add_le_add_left
      (Finset.card_le_card Finset.inter_subset_right) _
  unfold score
  omega

def assignmentOfIndependent {n : ℕ} (I : Finset (Fin n)) :
    Fin n → Fin 4 → Bool :=
  fun v _ => if v ∈ I then false else true

theorem score_assignmentOfIndependent_proof {n m : ℕ} (G : PortGraph n m)
    (I : Finset (Fin n)) (hI : Independent G I) :
    score G (assignmentOfIndependent I) = 4 * n + m + I.card := by
  have hselected : selectedVertices (assignmentOfIndependent I) = I := by
    ext v
    simp [selectedVertices, assignmentOfIndependent]
  have htransition : transitionPairs (assignmentOfIndependent I) = ∅ := by
    ext pair
    simp [transitionPairs, transition, assignmentOfIndependent]
  have hfalse : falseEdges G (assignmentOfIndependent I) = ∅ := by
    ext e
    simp [falseEdges, assignmentOfIndependent, hI e]
  simp only [score, hselected, htransition, hfalse, Finset.card_empty,
    Nat.sub_zero]
  omega

theorem exact_three_occurrence_identity_proof {n m alpha : ℕ}
    (G : PortGraph n m) (halpha : IsIndependenceNumber G alpha) :
    (∀ z, score G z ≤ 4 * n + m + alpha) ∧
      ∃ z, score G z = 4 * n + m + alpha := by
  constructor
  · intro z
    calc
      score G z ≤ 4 * n + m + (repairedSet G z).card :=
        repairedSet_card_lower_bound_proof G z
      _ ≤ 4 * n + m + alpha :=
        Nat.add_le_add_left (halpha.1 _ (repairedSet_independent_proof G z)) _
  · obtain ⟨I, hI, hcard⟩ := halpha.2
    exact ⟨assignmentOfIndependent I, by
      rw [score_assignmentOfIndependent_proof G I hI, hcard]⟩

/-- Arithmetic transfer of the Berman--Fujito `7/6` cubic-MIS guarantee. -/
theorem ratio_83_84_from_cubic_mis_proof
    (n m alpha found : ℕ)
    (hcubic : 2 * m = 3 * n)
    (halpha : 2 * alpha ≤ n)
    (happrox : 7 * found ≥ 6 * alpha) :
    84 * (4 * n + m + found) ≥ 83 * (4 * n + m + alpha) := by
  omega

theorem ratio_83_84_arithmetic_proof :
    (11 : ℚ) + 6 / 7 = (83 / 84) * 12 := by
  norm_num

end PalomaMax2SAT.CubicThreeOccurrence
