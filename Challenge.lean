module

public import Mathlib

public section

/-!
# Canonical standalone challenge

This file intentionally imports only Mathlib so Palomar can compile it in an
isolated canonical environment. The implementation lives in the project
modules imported by `Solution.lean`.
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
  port_occupied : ∀ v : Fin n, ∀ p : Fin 3,
    (∃ e, left e = v ∧ leftPort e = p) ∨ (∃ e, right e = v ∧ rightPort e = p)

def Independent {n m : ℕ} (G : PortGraph n m) (I : Finset (Fin n)) : Prop :=
  ∀ e, ¬ (G.left e ∈ I ∧ G.right e ∈ I)

def IsIndependenceNumber {n m : ℕ} (G : PortGraph n m) (alpha : ℕ) : Prop :=
  (∀ I, Independent G I → I.card ≤ alpha) ∧
    ∃ I, Independent G I ∧ I.card = alpha

def edgeClone (p : Fin 3) : Fin 4 := p.succ

abbrev transition {n : ℕ} (z : Fin n → Fin 4 → Bool)
    (v : Fin n) (i : Fin 4) : Prop :=
  z v i = true ∧ z v (i + 1) = false

def selectedVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => z v 0 = false

noncomputable def transitionPairs {n : ℕ} (z : Fin n → Fin 4 → Bool) :
    Finset (Fin n × Fin 4) :=
  Finset.univ.filter fun pair => transition z pair.1 pair.2

noncomputable def transitionVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  (transitionPairs z).image Prod.fst

noncomputable def cleanVertices {n : ℕ} (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  selectedVertices z \ transitionVertices z

def falseEdges {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun e =>
    z (G.left e) (edgeClone (G.leftPort e)) = false ∧
      z (G.right e) (edgeClone (G.rightPort e)) = false

noncomputable def deletionSet {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  ((Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z).image G.left)

noncomputable def repairedSet {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Finset (Fin n) :=
  cleanVertices z \ deletionSet G z

noncomputable def score {n m : ℕ} (G : PortGraph n m) (z : Fin n → Fin 4 → Bool) : ℕ :=
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

def assignmentOfIndependent {n : ℕ} (I : Finset (Fin n)) :
    Fin n → Fin 4 → Bool :=
  fun v _ => if v ∈ I then false else true

private theorem score_assignmentOfIndependent {n m : ℕ} (G : PortGraph n m)
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

end PalomaMax2SAT.CubicThreeOccurrence

/-!
# Supporting formalization: standard forced-equality occurrence split

The results below formalize a routine consistency construction: a connected
cycle of hard implications forces all occurrence clones of a variable to
agree, and encoding/decoding then preserve weighted objective values pointwise.
They are included for verification and reuse; they are **not** claimed as a
standalone research contribution.
-/
namespace PalomaMax2SAT.HardOccurrenceSplit

abbrev advance {α : Type*} (next : α → α) (k : ℕ) (i : α) : α :=
  Nat.rec i (fun _ current => next current) k

abbrev OrbitConnected {α : Type*} (next : α → α) : Prop :=
  ∀ i j, ∃ k, advance next k i = j

abbrev HardImplicationsHold {α : Type*} (next : α → α) (z : α → Bool) : Prop :=
  ∀ i, z i = true → z (next i) = true

abbrev IsOptimum {Assignment : Type*} (score : Assignment → ℕ) (opt : ℕ) : Prop :=
  (∀ a, score a ≤ opt) ∧ ∃ a, score a = opt

abbrev IsHardOptimum {Assignment : Type*} (feasible : Assignment → Prop)
    (score : Assignment → ℕ) (opt : ℕ) : Prop :=
  (∀ a, feasible a → score a ≤ opt) ∧ ∃ a, feasible a ∧ score a = opt

theorem propagate_hard_implications {α : Type*} (next : α → α)
    (z : α → Bool) (h : HardImplicationsHold next z) :
    ∀ k i, z i = true → z (advance next k i) = true := by
  intro k
  induction k with
  | zero =>
      intro i hi
      simpa using hi
  | succ k ih =>
      intro i hi
      change z (next (advance next k i)) = true
      exact h _ (ih i hi)

end PalomaMax2SAT.HardOccurrenceSplit

namespace PalomaMax2SAT.CubicPublic

open CubicThreeOccurrence

theorem repairedSet_independent {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : Independent G (repairedSet G z) := by
  intro e he
  rcases he with ⟨hl, hr⟩
  have hlc : G.left e ∈ cleanVertices z := (Finset.mem_sdiff.mp hl).1
  have hrc : G.right e ∈ cleanVertices z := (Finset.mem_sdiff.mp hr).1
  have hdel : G.left e ∈ deletionSet G z := by
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlc, hrc⟩, rfl⟩
  exact (Finset.mem_sdiff.mp hl).2 hdel

theorem repairedSet_card_lower_bound {n m : ℕ} (G : PortGraph n m)
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

theorem exact_three_occurrence_identity {n m alpha : ℕ}
    (G : PortGraph n m) (halpha : IsIndependenceNumber G alpha) :
    (∀ z, score G z ≤ 4 * n + m + alpha) ∧
      ∃ z, score G z = 4 * n + m + alpha := by
  constructor
  · intro z
    calc
      score G z ≤ 4 * n + m + (repairedSet G z).card :=
        repairedSet_card_lower_bound G z
      _ ≤ 4 * n + m + alpha :=
        Nat.add_le_add_left (halpha.1 _ (repairedSet_independent G z)) _
  · obtain ⟨I, hI, hcard⟩ := halpha.2
    exact ⟨assignmentOfIndependent I, by
      rw [score_assignmentOfIndependent G I hI, hcard]⟩

theorem ratio_83_84_from_cubic_mis
    (n m alpha found : ℕ)
    (hcubic : 2 * m = 3 * n)
    (halpha : 2 * alpha ≤ n)
    (happrox : 7 * found ≥ 6 * alpha) :
    84 * (4 * n + m + found) ≥ 83 * (4 * n + m + alpha) := by
  omega

theorem ratio_83_84_arithmetic :
    (11 : ℚ) + 6 / 7 = (83 / 84) * 12 := by
  norm_num

end PalomaMax2SAT.CubicPublic

/-!
# Supporting formalization: abstract transfer lemmas

The lemmas below wrap the standard forced-equality occurrence split into
optimum- and feasible-solution value-preservation interfaces. They take the
encode/decode score equalities as hypotheses; they are reusable supporting
lemmas, not an independent research contribution.
-/
namespace PalomaMax2SAT.HardSplitPublic

open HardOccurrenceSplit

theorem hard_implication_cycle_consistent {α : Type*} (next : α → α)
    (z : α → Bool) (horbit : OrbitConnected next)
    (hhard : HardImplicationsHold next z) :
    ∀ i j, z i = z j := by
  intro i j
  cases hi : z i <;> cases hj : z j
  · rfl
  · obtain ⟨k, hk⟩ := horbit j i
    have htrue := propagate_hard_implications next z hhard k j hj
    rw [hk, hi] at htrue
    simp at htrue
  · obtain ⟨k, hk⟩ := horbit i j
    have htrue := propagate_hard_implications next z hhard k i hi
    rw [hk, hj] at htrue
    simp at htrue
  · rfl

theorem exact_hard_occurrence_split
    {Source Split : Type*}
    (sourceScore : Source → ℕ) (splitScore : Split → ℕ)
    (feasible : Split → Prop) (encode : Source → Split) (decode : Split → Source)
    (opt : ℕ)
    (hsource : IsOptimum sourceScore opt)
    (hencodeFeasible : ∀ a, feasible (encode a))
    (hencodeScore : ∀ a, splitScore (encode a) = sourceScore a)
    (hdecodeScore : ∀ z, feasible z → sourceScore (decode z) = splitScore z) :
    IsHardOptimum feasible splitScore opt := by
  constructor
  · intro z hz
    rw [← hdecodeScore z hz]
    exact hsource.1 (decode z)
  · obtain ⟨a, ha⟩ := hsource.2
    exact ⟨encode a, hencodeFeasible a, (hencodeScore a).trans ha⟩

theorem feasible_solution_ratio_preserved
    {Source Split : Type*}
    (sourceScore : Source → ℕ) (splitScore : Split → ℕ)
    (feasible : Split → Prop) (decode : Split → Source)
    (hdecodeScore : ∀ z, feasible z → sourceScore (decode z) = splitScore z)
    (z : Split) (hz : feasible z) :
    splitScore z = sourceScore (decode z) := by
  exact (hdecodeScore z hz).symm

theorem ratio_83_84_exceeds_general_horn_threshold :
    (83 : ℚ) / 84 > 94615981 / 100000000 := by
  norm_num

end PalomaMax2SAT.HardSplitPublic

/-!
# Supporting formalization: concrete weighted Horn occurrence split

A concrete weighted Horn occurrence-split model is formalized to instantiate
the abstract transfer lemmas. Feasible split assignments are exactly the
consistent lifts of source assignments, and encoding/decoding preserve the
weighted objective pointwise. This is a routine forced-equality gadget
formalized for verification and reuse; it is **not** claimed as an independent
research contribution.
-/
namespace PalomaMax2SAT.ConcreteHardSplit

open PalomaMax2SAT.HardOccurrenceSplit

structure Literal (Var : Type*) (Occ : Var → Type*) where
  var : Var
  occ : Occ var
  pos : Bool

abbrev HornClause {Var : Type*} {Occ : Var → Type*}
    (c : Finset (Literal Var Occ)) : Prop :=
  ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.pos = true → l₂.pos = true → l₁ = l₂

structure WeightedHornSplit (Var : Type*) (Occ : Var → Type*) (Clause : Type*) where
  weight : Clause → ℕ
  lits : Clause → Finset (Literal Var Occ)
  horn : ∀ c, HornClause (lits c)

noncomputable abbrev sourceScore {Var : Type*} {Occ : Var → Type*} {Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause) (x : Var → Bool) : ℕ := by
  classical
  exact ∑ c : Clause,
    if ∃ l ∈ F.lits c, x l.var = l.pos then F.weight c else 0

noncomputable abbrev splitScore {Var : Type*} {Occ : Var → Type*} {Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (z : (v : Var) → Occ v → Bool) : ℕ := by
  classical
  exact ∑ c : Clause,
    if ∃ l ∈ F.lits c, z l.var l.occ = l.pos then F.weight c else 0

abbrev Feasible {Var : Type*} {Occ : Var → Type*}
    (next : ∀ v, Occ v → Occ v)
    (z : (v : Var) → Occ v → Bool) : Prop :=
  ∀ v, HardImplicationsHold (next v) (z v)

abbrev encode {Var : Type*} {Occ : Var → Type*} (x : Var → Bool) :
    (v : Var) → Occ v → Bool :=
  fun v _ => x v

abbrev decode {Var : Type*} {Occ : Var → Type*} (base : ∀ v, Occ v)
    (z : (v : Var) → Occ v → Bool) : Var → Bool :=
  fun v => z v (base v)

theorem encode_feasible {Var : Type*} {Occ : Var → Type*}
    (next : ∀ v, Occ v → Occ v) (x : Var → Bool) :
    Feasible next (encode (Occ := Occ) x) := by
  intro v o ho
  simpa [encode] using ho

theorem encodeScore {Var : Type*} {Occ : Var → Type*} {Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ∀ v, Occ v → Occ v) (x : Var → Bool) :
    splitScore F (encode (Occ := Occ) x) = sourceScore F x := by
  classical
  unfold splitScore sourceScore
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : ∃ l ∈ F.lits c, x l.var = l.pos <;> simp [encode, h]

theorem feasible_constant {Var : Type*} {Occ : Var → Type*}
    (next : ∀ v, Occ v → Occ v) (base : ∀ v, Occ v)
    (horb : ∀ v, OrbitConnected (next v))
    {z : (v : Var) → Occ v → Bool} (hz : Feasible next z) :
    ∀ v o, z v (base v) = z v o := by
  intro v o
  cases hb : z v (base v) <;> cases ho : z v o
  · rfl
  · obtain ⟨k, hk⟩ := horb v o (base v)
    have htrue :=
      propagate_hard_implications (next v) (z v) (hz v) k o ho
    rw [hk, hb] at htrue
    simp at htrue
  · obtain ⟨k, hk⟩ := horb v (base v) o
    have htrue :=
      propagate_hard_implications (next v) (z v) (hz v) k (base v) hb
    rw [hk, ho] at htrue
    simp at htrue
  · rfl

theorem decodeScore {Var : Type*} {Occ : Var → Type*} {Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ∀ v, Occ v → Occ v) (base : ∀ v, Occ v)
    (horb : ∀ v, OrbitConnected (next v))
    {z : (v : Var) → Occ v → Bool} (hz : Feasible next z) :
    sourceScore F (decode base z) = splitScore F z := by
  classical
  have hconst : ∀ v o, z v (base v) = z v o :=
    feasible_constant next base horb hz
  unfold sourceScore splitScore decode
  apply Finset.sum_congr rfl
  intro c _
  have hsat : (∃ l ∈ F.lits c, z l.var (base l.var) = l.pos) ↔
      (∃ l ∈ F.lits c, z l.var l.occ = l.pos) := by
    constructor
    · rintro ⟨l, hl, h⟩
      exact ⟨l, hl, by rw [← hconst l.var l.occ]; exact h⟩
    · rintro ⟨l, hl, h⟩
      exact ⟨l, hl, by rw [hconst l.var l.occ]; exact h⟩
  by_cases h : ∃ l ∈ F.lits c, z l.var l.occ = l.pos
  · have h' : ∃ l ∈ F.lits c, z l.var (base l.var) = l.pos := hsat.mpr h
    simp [h, h']
  · have h' : ¬ ∃ l ∈ F.lits c, z l.var (base l.var) = l.pos :=
      fun hp => h (hsat.mp hp)
    simp [h, h']

theorem concrete_exact_hard_occurrence_split
    {Var : Type*} {Occ : Var → Type*} {Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ∀ v, Occ v → Occ v) (base : ∀ v, Occ v)
    (horb : ∀ v, OrbitConnected (next v))
    (opt : ℕ) (hsource : IsOptimum (sourceScore F) opt) :
    IsHardOptimum (Feasible next) (splitScore F) opt := by
  constructor
  · intro z hz
    rw [← decodeScore F next base horb hz]
    exact hsource.1 (decode base z)
  · obtain ⟨x, hx⟩ := hsource.2
    refine ⟨encode (Occ := Occ) x, encode_feasible next x, ?_⟩
    rw [encodeScore F next x, hx]

theorem concrete_feasible_solution_ratio_preserved
    {Var : Type*} {Occ : Var → Type*} {Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ∀ v, Occ v → Occ v) (base : ∀ v, Occ v)
    (horb : ∀ v, OrbitConnected (next v))
    (z : (v : Var) → Occ v → Bool) (hz : Feasible next z) :
    splitScore F z = sourceScore F (decode base z) := by
  exact (decodeScore F next base horb hz).symm

end PalomaMax2SAT.ConcreteHardSplit

namespace PalomaMax2SAT.GraphTransfer
open PalomaMax2SAT.HardOccurrenceSplit

theorem hardImage_ratio (W a s : ℕ) (hw : 12*a ≤ W) (hs : 17*a ≤ 20*s) :
    260*(W+s) ≥ 257*(W+a) := by omega

open PalomaMax2SAT.CubicThreeOccurrence

/-- The hard cycle is a feasibility condition. Only units and edges earn weight. -/
noncomputable def fourScore {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : ℕ :=
  (selectedVertices z).card + 4 * (m - (falseEdges G z).card)

theorem fourScore_repair {n m : ℕ} (G : PortGraph n m) (z : Fin n → Fin 4 → Bool)
    (hz : transitionPairs z = ∅) :
    fourScore G z ≤ 4*m + (repairedSet G z).card := by
  have h := PalomaMax2SAT.CubicPublic.repairedSet_card_lower_bound G z
  simp only [score, hz, Finset.card_empty, Nat.sub_zero] at h
  unfold fourScore
  omega

theorem canonical_fourScore {n m : ℕ} (G : PortGraph n m)
    (I : Finset (Fin n)) (hI : Independent G I) :
    transitionPairs (assignmentOfIndependent I) = ∅ ∧
    fourScore G (assignmentOfIndependent I) = 4*m + I.card := by
  classical
  have hselected : selectedVertices (assignmentOfIndependent I) = I := by
    ext v
    simp [selectedVertices, assignmentOfIndependent]
  have hfalse : falseEdges G (assignmentOfIndependent I) = ∅ := by
    ext e
    simp [falseEdges, assignmentOfIndependent, hI e]
  constructor
  · ext pair
    simp [transitionPairs, transition, assignmentOfIndependent]
  · simp [fourScore, hselected, hfalse, Nat.add_comm]

theorem exact_fourScore {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (fourScore G) (4*m+a) := by
  constructor
  · intro z hz
    have hu := fourScore_repair G z hz
    have hi := ha.1 _ (PalomaMax2SAT.CubicPublic.repairedSet_independent G z)
    omega
  · obtain ⟨I, hi, hc⟩ := ha.2
    exact ⟨assignmentOfIndependent I, (canonical_fourScore G I hi).1,
      by rw [(canonical_fourScore G I hi).2, hc]⟩

theorem hardFour_transfer {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (I : Finset (Fin n)) (hi : Independent G I) (hs : 17*a ≤ 20*I.card) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (fourScore G) (4*m+a) ∧
    transitionPairs (assignmentOfIndependent I) = ∅ ∧
    260*fourScore G (assignmentOfIndependent I) ≥ 257*(4*m+a) := by
  obtain ⟨hz, hval⟩ := canonical_fourScore G I hi
  refine ⟨exact_fourScore G ha, hz, ?_⟩
  rw [hval]
  exact hardImage_ratio (4*m) a I.card (by omega) hs


private theorem unitCanonicalSoft {n m : ℕ} (G : PortGraph n m)
    (I : Finset (Fin n)) (hi : Independent G I) :
    score G (assignmentOfIndependent I) = 4*n+m+I.card := by
  have hz := (canonical_fourScore G I hi).1
  have hselected : selectedVertices (assignmentOfIndependent I) = I := by
    ext v
    simp [selectedVertices, assignmentOfIndependent]
  have hfalse : falseEdges G (assignmentOfIndependent I) = ∅ := by
    ext e
    simp [falseEdges, assignmentOfIndependent, hi e]
  simp only [score, hselected, hfalse, hz, Finset.card_empty, Nat.sub_zero]
  omega

/-- Original unit weights, with all implications mandatory and unscored. -/
noncomputable def unitScore {n m : ℕ} (G : PortGraph n m)
    (z : Fin n → Fin 4 → Bool) : ℕ :=
  (selectedVertices z).card + (m - (falseEdges G z).card)

theorem exact_unitScore {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (unitScore G) (m+a) := by
  constructor
  · intro z hz
    have hu := PalomaMax2SAT.CubicPublic.repairedSet_card_lower_bound G z
    have hi := ha.1 _ (PalomaMax2SAT.CubicPublic.repairedSet_independent G z)
    simp only [score, hz, Finset.card_empty, Nat.sub_zero] at hu
    unfold unitScore
    omega
  · obtain ⟨I, hi, hc⟩ := ha.2
    have hz := (canonical_fourScore G I hi).1
    have hv := unitCanonicalSoft G I hi
    simp only [score, hz, Finset.card_empty, Nat.sub_zero] at hv
    exact ⟨assignmentOfIndependent I, hz, by unfold unitScore; omega⟩

theorem hardUnit_transfer {n m a : ℕ} (G : PortGraph n m)
    (ha : IsIndependenceNumber G a) (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (I : Finset (Fin n)) (hi : Independent G I) (hs : 17*a ≤ 20*I.card) :
    IsHardOptimum (fun z => transitionPairs z = ∅) (unitScore G) (m+a) ∧
    transitionPairs (assignmentOfIndependent I) = ∅ ∧
    80*unitScore G (assignmentOfIndependent I) ≥ 77*(m+a) := by
  have hz := (canonical_fourScore G I hi).1
  have hv := unitCanonicalSoft G I hi
  simp only [score, hz, Finset.card_empty, Nat.sub_zero] at hv
  refine ⟨exact_unitScore G ha, hz, ?_⟩
  unfold unitScore
  omega

theorem unit_endpoint_arithmetic (n m a s : ℕ)
    (hm : 2*m = 3*n) (hn : 2*a ≤ n)
    (h : 6*a ≤ 7*s ∨ (20000*a ≤ 9999*n ∧ 5999993*a ≤ 7000000*s)) :
    28*(m+s) ≥ 27*(m+a) := by
  rcases h with h | ⟨h₁,h₂⟩ <;> omega

end PalomaMax2SAT.GraphTransfer
