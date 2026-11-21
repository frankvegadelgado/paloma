module

public import Mathlib

@[expose] public section

/-!
# The signed graph for weighted inputs of width two (Theorem `thm:signed`)

A weighted source `F` of width at most two is given by its set `ι` of literal occurrences
(`D = |ι|`), the variable `var i`, the sign `pos i` (`true` for a positive literal), the clause
`cl i` and a nonnegative weight `w c` of every clause. The occurrences of one variable are
arranged in a cycle by `nxt`. With `M = W + 1` and `W = Σ_c w c`, the graph `J` has the following
vertices and edges:

* two ports `(i, true)` and `(i, false)` of weight `M` for every occurrence `i`, joined to each
  other, and `(i, true)` is joined to `(nxt i, false)`;
* a reward vertex `i` of weight `w (cl i)` for every occurrence, joined to the port
  `(i, !pos i)` that falsifies the literal, and to the reward vertices of the other occurrences
  of its clause.

An independent set of `J` is a pair `(P, R)` of a set `P` of ports and a set `R` of reward
vertices subject to the four conditions of `Indep`. This module proves that the maximum weight
of an independent set is `D * M + OPT(F)` and that every independent set of weight `A` decodes
to an assignment of score at least `A - D * M`.

The bounds on the number of vertices and on the maximum degree of `J` are counting statements
about the construction and are not formalized.
-/

namespace PalomaMax2SAT.SignedGraph

/-- A weighted source with a cyclic order on the occurrences of every variable. -/
structure Source (ι V C : Type) where
  var : ι → V
  pos : ι → Bool
  cl : ι → C
  w : C → ℕ
  nxt : ι → ι
  var_nxt : ∀ i, var (nxt i) = var i
  orbit : ∀ i j, var i = var j → ∃ k, nxt^[k] i = j

variable {ι V C : Type} [Fintype ι] [LinearOrder ι] [Fintype C] [DecidableEq C]

/-- The total clause weight plus one. -/
def M (S : Source ι V C) : ℕ := ∑ c, S.w c + 1

/-- The weight of the clauses satisfied by `x`; the literal of occurrence `i` is true when
`x (var i) = pos i`. -/
def score (S : Source ι V C) (x : V → Bool) : ℕ :=
  ∑ c ∈ Finset.univ.filter (fun c => ∃ i, S.cl i = c ∧ x (S.var i) = S.pos i), S.w c

/-- Independent sets of `J`, as a set `P` of ports and a set `R` of reward vertices. -/
structure Indep (S : Source ι V C) (P : Finset (ι × Bool)) (R : Finset ι) : Prop where
  pair : ∀ i, ¬ ((i, true) ∈ P ∧ (i, false) ∈ P)
  cyc : ∀ i, ¬ ((i, true) ∈ P ∧ (S.nxt i, false) ∈ P)
  rport : ∀ j ∈ R, (j, !S.pos j) ∉ P
  rr : ∀ i ∈ R, ∀ j ∈ R, S.cl i = S.cl j → i = j

/-- The weight of `(P, R)`. -/
def weight (S : Source ι V C) (P : Finset (ι × Bool)) (R : Finset ι) : ℕ :=
  M S * P.card + ∑ j ∈ R, S.w (S.cl j)

omit [Fintype ι] [LinearOrder ι] [Fintype C] [DecidableEq C] in
theorem fst_injOn {S : Source ι V C} {P : Finset (ι × Bool)} {R : Finset ι}
    (hI : Indep S P R) : Set.InjOn Prod.fst (P : Set (ι × Bool)) := by
  intro p hp q hq h
  obtain ⟨i, b⟩ := p
  obtain ⟨j, c⟩ := q
  simp only at h
  subst h
  cases b <;> cases c
  · rfl
  · exact absurd ⟨hq, hp⟩ (hI.pair i)
  · exact absurd ⟨hp, hq⟩ (hI.pair i)
  · rfl

omit [Fintype C] [DecidableEq C] in
theorem ports_le {S : Source ι V C} {P : Finset (ι × Bool)} {R : Finset ι}
    (hI : Indep S P R) : P.card ≤ Fintype.card ι := by
  calc P.card = (P.image Prod.fst).card := (Finset.card_image_of_injOn (fst_injOn hI)).symm
    _ ≤ Fintype.card ι := Finset.card_le_univ _

omit [Fintype ι] [LinearOrder ι] [Fintype C] in
theorem reward_sum_le (S : Source ι V C) (R : Finset ι)
    (hrr : ∀ i ∈ R, ∀ j ∈ R, S.cl i = S.cl j → i = j) (T : Finset C)
    (hT : ∀ j ∈ R, S.cl j ∈ T) : ∑ j ∈ R, S.w (S.cl j) ≤ ∑ c ∈ T, S.w c := by
  have hinj : Set.InjOn S.cl (R : Set ι) := fun i hi j hj h => hrr i hi j hj h
  calc ∑ j ∈ R, S.w (S.cl j) = ∑ c ∈ R.image S.cl, S.w c :=
        (Finset.sum_image (f := S.w) hinj).symm
    _ ≤ ∑ c ∈ T, S.w c := by
      apply Finset.sum_le_sum_of_subset
      intro c hc
      obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
      rw [← hjc]
      exact hT j hj

/-- Upper bound and decoding: every independent set of `J` has weight at most `D * M` plus the
score of an assignment read from its ports. -/
theorem upper (S : Source ι V C) {P : Finset (ι × Bool)} {R : Finset ι} (hI : Indep S P R) :
    ∃ x : V → Bool, weight S P R ≤ Fintype.card ι * M S + score S x := by
  classical
  have hP := ports_le hI
  have hR : ∑ j ∈ R, S.w (S.cl j) ≤ ∑ c, S.w c :=
    reward_sum_le S R hI.rr Finset.univ (fun _ _ => Finset.mem_univ _)
  by_cases hlt : P.card < Fintype.card ι
  · refine ⟨fun _ => true, ?_⟩
    unfold weight M
    have h1 : (∑ c, S.w c + 1) * (P.card + 1) ≤ (∑ c, S.w c + 1) * Fintype.card ι :=
      Nat.mul_le_mul_left _ hlt
    nlinarith [h1, hR]
  · have hPeq : P.card = Fintype.card ι := le_antisymm hP (not_lt.mp hlt)
    have hall : ∀ i, (i, true) ∈ P ∨ (i, false) ∈ P := by
      intro i
      have himg : P.image Prod.fst = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Finset.card_image_of_injOn (fst_injOn hI)]
        exact hPeq
      have hi : i ∈ P.image Prod.fst := by
        rw [himg]
        exact Finset.mem_univ i
      obtain ⟨⟨j, b⟩, hjb, hj⟩ := Finset.mem_image.mp hi
      simp only at hj
      subst hj
      cases b
      · exact Or.inr hjb
      · exact Or.inl hjb
    have hnext : ∀ i, (i, true) ∈ P → (S.nxt i, true) ∈ P := by
      intro i hi
      rcases hall (S.nxt i) with h | h
      · exact h
      · exact absurd ⟨hi, h⟩ (hI.cyc i)
    have hiter : ∀ k i, (i, true) ∈ P → (S.nxt^[k] i, true) ∈ P := by
      intro k
      induction k with
      | zero =>
        intro i hi
        simpa using hi
      | succ k ih =>
        intro i hi
        rw [Function.iterate_succ_apply]
        exact ih _ (hnext i hi)
    obtain ⟨x, hx⟩ : ∃ x : V → Bool, ∀ i, x (S.var i) = true ↔ (i, true) ∈ P := by
      refine ⟨fun u => decide (∃ i, S.var i = u ∧ (i, true) ∈ P), ?_⟩
      intro i
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, hjP⟩
        obtain ⟨k, hk⟩ := S.orbit j i hj
        rw [← hk]
        exact hiter k j hjP
      · intro h
        exact ⟨i, rfl, h⟩
    have hrew : ∀ j ∈ R, x (S.var j) = S.pos j := by
      intro j hj
      have h1 := hI.rport j hj
      cases hpos : S.pos j
      · rw [hpos] at h1
        simp only [Bool.not_false] at h1
        cases hxv : x (S.var j)
        · rfl
        · exact absurd ((hx j).mp hxv) h1
      · rw [hpos] at h1
        simp only [Bool.not_true] at h1
        rcases hall j with h | h
        · exact (hx j).mpr h
        · exact absurd h h1
    have hscore : ∑ j ∈ R, S.w (S.cl j) ≤ score S x := by
      unfold score
      apply reward_sum_le S R hI.rr
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨j, rfl, hrew j hj⟩
    refine ⟨x, ?_⟩
    unfold weight
    rw [hPeq, Nat.mul_comm (M S)]
    omega

/-- Lower bound: every assignment `x` yields an independent set of weight `D * M + score x`. -/
theorem lower (S : Source ι V C) (x : V → Bool) :
    ∃ (P : Finset (ι × Bool)) (R : Finset ι), Indep S P R ∧
      weight S P R = Fintype.card ι * M S + score S x := by
  classical
  let P : Finset (ι × Bool) := Finset.univ.image fun i => (i, x (S.var i))
  let R : Finset ι := Finset.univ.filter fun j =>
    x (S.var j) = S.pos j ∧ ∀ i, x (S.var i) = S.pos i → S.cl i = S.cl j → j ≤ i
  have hPmem : ∀ i b, (i, b) ∈ P ↔ b = x (S.var i) := by
    intro i b
    simp only [P, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨j, hj, h⟩
      subst hj
      exact h.symm
    · intro h
      exact ⟨i, rfl, h.symm⟩
  have hRmem : ∀ j, j ∈ R ↔
      (x (S.var j) = S.pos j ∧ ∀ i, x (S.var i) = S.pos i → S.cl i = S.cl j → j ≤ i) := by
    intro j
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
  have hrr : ∀ i ∈ R, ∀ j ∈ R, S.cl i = S.cl j → i = j := by
    intro i hi j hj hcl
    have hi' := (hRmem i).mp hi
    have hj' := (hRmem j).mp hj
    exact le_antisymm (hi'.2 j hj'.1 hcl.symm) (hj'.2 i hi'.1 hcl)
  have hinj : Function.Injective fun i : ι => ((i, x (S.var i)) : ι × Bool) :=
    fun i j h => (Prod.mk.inj h).1
  have hPcard : P.card = Fintype.card ι := by
    simp only [P]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hRimg : R.image S.cl =
      Finset.univ.filter (fun c => ∃ i, S.cl i = c ∧ x (S.var i) = S.pos i) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, hjc⟩
      exact ⟨j, hjc, ((hRmem j).mp hj).1⟩
    · rintro ⟨i, hi, hxi⟩
      let A : Finset ι := Finset.univ.filter fun i' => S.cl i' = c ∧ x (S.var i') = S.pos i'
      have hA : A.Nonempty := ⟨i, by simp [A, hi, hxi]⟩
      have hm := Finset.min'_mem A hA
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      refine ⟨A.min' hA, ?_, hm.1⟩
      rw [hRmem]
      refine ⟨hm.2, fun i' hi' hcl => ?_⟩
      apply Finset.min'_le
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hcl.trans hm.1, hi'⟩
  have hRsum : ∑ j ∈ R, S.w (S.cl j) = score S x := by
    have hinjOn : Set.InjOn S.cl (R : Set ι) := fun i hi j hj h => hrr i hi j hj h
    have h := Finset.sum_image (f := S.w) hinjOn
    rw [hRimg] at h
    exact h.symm
  refine ⟨P, R, ⟨?_, ?_, ?_, hrr⟩, ?_⟩
  · intro i hi
    have h1 := (hPmem i true).mp hi.1
    have h2 := (hPmem i false).mp hi.2
    rw [← h1] at h2
    exact absurd h2 (by decide)
  · intro i hi
    have h1 := (hPmem i true).mp hi.1
    have h2 := (hPmem (S.nxt i) false).mp hi.2
    rw [S.var_nxt, ← h1] at h2
    exact absurd h2 (by decide)
  · intro j hj hmem
    have hj' := ((hRmem j).mp hj).1
    have h3 := (hPmem j (!S.pos j)).mp hmem
    rw [hj'] at h3
    generalize S.pos j = b at h3
    cases b <;> simp at h3
  · unfold weight
    rw [hPcard, hRsum, Nat.mul_comm]

/-- Theorem `thm:signed`: the maximum weight of an independent set of `J` is `D * M + OPT`,
and every independent set of weight `A` decodes to an assignment of score at least `A - D * M`. -/
theorem signed_theorem (S : Source ι V C) {opt : ℕ}
    (hopt : (∀ x, score S x ≤ opt) ∧ ∃ x, score S x = opt) :
    (∀ P R, Indep S P R → ∃ x, weight S P R ≤ Fintype.card ι * M S + score S x) ∧
      (∀ P R, Indep S P R → weight S P R ≤ Fintype.card ι * M S + opt) ∧
      ∃ P R, Indep S P R ∧ weight S P R = Fintype.card ι * M S + opt := by
  refine ⟨fun P R hI => upper S hI, ?_, ?_⟩
  · intro P R hI
    obtain ⟨x, hx⟩ := upper S hI
    have := hopt.1 x
    omega
  · obtain ⟨x, hx⟩ := hopt.2
    obtain ⟨P, R, hI, hw⟩ := lower S x
    exact ⟨P, R, hI, by rw [hw, hx]⟩

end PalomaMax2SAT.SignedGraph
