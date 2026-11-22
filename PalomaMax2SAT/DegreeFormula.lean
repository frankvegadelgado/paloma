module

public import Mathlib
public import PalomaMax2SAT.DegreeTransfer

@[expose] public section

/-!
# The degree-`d` formula `T_H` as an explicit MAX-HORN-2SAT instance

For a simple `d`-regular graph `H` with a port labelling, the formula `T_H` has
`d + 1` Boolean clones `(v, 0), …, (v, d)` per vertex `v`: the clone `(v, 0)` occurs in
the unit clause `(¬ (v,0))`, the clones `(v, p+1)` occur in the edge clauses of the
`d` edges at `v`, and the `d + 1` cyclic implications `(¬ (v,i) ∨ (v,i+1))` enforce
consistency. Every clone occurs exactly three times.

This module proves, for every `d`:

* the number of satisfied clauses equals `U(z) + (m - F(z)) + ((d+1) n - T(z))`;
* the optimum equals `(d+1) n + m + α`;
* every clause is Horn, the formula has `(d+2) n + m` clauses, and every variable
  occurs exactly three times;
* `2 m = d n` and `2 α ≤ n` follow from the port structure (for `d > 0`);
* the lift of an independent set has value `(d+1) n + m + |I|`, and the arithmetic of
  `DegreeTransfer` applies to it.

Lean does not prove that an algorithm attains any independent-set guarantee; those
guarantees are hypotheses of the transfer statements.
-/

namespace PalomaMax2SAT.DegreeFormula

/-- A `d`-regular graph on `n` vertices with `m` edges and a port labelling: every
vertex has exactly one incident edge at each of its `d` ports. -/
structure PortGraph (d n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  left_ne_right : ∀ e, left e ≠ right e
  leftPort : Fin m → Fin d
  rightPort : Fin m → Fin d
  left_unique : ∀ e f, left e = left f → leftPort e = leftPort f → e = f
  right_unique : ∀ e f, right e = right f → rightPort e = rightPort f → e = f
  cross_unique : ∀ e f, left e = right f → leftPort e = rightPort f → False
  port_occupied : ∀ v : Fin n, ∀ p : Fin d,
    (∃ e, left e = v ∧ leftPort e = p) ∨ (∃ e, right e = v ∧ rightPort e = p)

def Independent {d n m : ℕ} (G : PortGraph d n m) (I : Finset (Fin n)) : Prop :=
  ∀ e, ¬ (G.left e ∈ I ∧ G.right e ∈ I)

def IsIndependenceNumber {d n m : ℕ} (G : PortGraph d n m) (alpha : ℕ) : Prop :=
  (∀ I, Independent G I → I.card ≤ alpha) ∧
    ∃ I, Independent G I ∧ I.card = alpha

/-- The clone of a port: ports `0, …, d-1` use the clones `1, …, d`. -/
def edgeClone {d : ℕ} (p : Fin d) : Fin (d + 1) := p.succ

abbrev transition {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool)
    (v : Fin n) (i : Fin (d + 1)) : Prop :=
  z v i = true ∧ z v (i + 1) = false

def selectedVertices {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => z v 0 = false

noncomputable def transitionPairs {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool) :
    Finset (Fin n × Fin (d + 1)) :=
  Finset.univ.filter fun pair => transition z pair.1 pair.2

noncomputable def transitionVertices {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool) :
    Finset (Fin n) :=
  (transitionPairs z).image Prod.fst

noncomputable def cleanVertices {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool) :
    Finset (Fin n) :=
  selectedVertices z \ transitionVertices z

def falseEdges {d n m : ℕ} (G : PortGraph d n m)
    (z : Fin n → Fin (d + 1) → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun e =>
    z (G.left e) (edgeClone (G.leftPort e)) = false ∧
      z (G.right e) (edgeClone (G.rightPort e)) = false

noncomputable def deletionSet {d n m : ℕ} (G : PortGraph d n m)
    (z : Fin n → Fin (d + 1) → Bool) : Finset (Fin n) :=
  ((Finset.univ.filter fun e =>
      G.left e ∈ cleanVertices z ∧ G.right e ∈ cleanVertices z).image G.left)

noncomputable def repairedSet {d n m : ℕ} (G : PortGraph d n m)
    (z : Fin n → Fin (d + 1) → Bool) : Finset (Fin n) :=
  cleanVertices z \ deletionSet G z

/-- Satisfied unit, edge, and cyclic-consistency clauses. -/
noncomputable def score {d n m : ℕ} (G : PortGraph d n m)
    (z : Fin n → Fin (d + 1) → Bool) : ℕ :=
  (selectedVertices z).card + (m - (falseEdges G z).card) +
    ((d + 1) * n - (transitionPairs z).card)

/-- With no transition at `v` and `z v 0 = false`, every clone of `v` is false: a true
clone would propagate around the cycle of implications to clone `0`. -/
private theorem no_transition_all_false {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool)
    (v : Fin n) (hzero : z v 0 = false)
    (hnone : v ∉ transitionVertices z) : ∀ i, z v i = false := by
  have ht : ∀ i, ¬ transition z v i := by
    intro i hi
    apply hnone
    exact Finset.mem_image.mpr
      ⟨(v, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  have step : ∀ i, z v i = true → z v (i + 1) = true := by
    intro i hi
    cases h : z v (i + 1) with
    | true => rfl
    | false => exact absurd (⟨hi, h⟩ : transition z v i) (ht i)
  have back : ∀ i, z v (i + 1) = false → z v i = false := by
    intro i hi
    cases h : z v i with
    | false => rfl
    | true =>
      have h' := step i h
      rw [hi] at h'
      simp at h'
  have hlast : z v (Fin.last d) = false := by
    apply back
    rw [Fin.last_add_one]
    exact hzero
  intro i
  refine Fin.reverseInduction (motive := fun i => z v i = false) hlast ?_ i
  intro j hj
  apply back
  rw [Fin.coeSucc_eq_succ]
  exact hj

theorem repairedSet_independent_proof {d n m : ℕ} (G : PortGraph d n m)
    (z : Fin n → Fin (d + 1) → Bool) : Independent G (repairedSet G z) := by
  intro e he
  rcases he with ⟨hl, hr⟩
  have hlc : G.left e ∈ cleanVertices z := (Finset.mem_sdiff.mp hl).1
  have hrc : G.right e ∈ cleanVertices z := (Finset.mem_sdiff.mp hr).1
  have hdel : G.left e ∈ deletionSet G z := by
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlc, hrc⟩, rfl⟩
  exact (Finset.mem_sdiff.mp hl).2 hdel

private theorem internalEdges_subset_falseEdges {d n m : ℕ} (G : PortGraph d n m)
    (z : Fin n → Fin (d + 1) → Bool) :
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

theorem repairedSet_card_lower_bound_proof {d n m : ℕ} (G : PortGraph d n m)
    (z : Fin n → Fin (d + 1) → Bool) :
    score G z ≤ (d + 1) * n + m + (repairedSet G z).card := by
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
  have htransitionBound : (transitionPairs z).card ≤ (d + 1) * n := by
    have h := Finset.card_le_univ (transitionPairs z)
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact h.trans (Nat.mul_comm _ _).le
  have hrepair : (cleanVertices z).card ≤
      (repairedSet G z).card + (deletionSet G z).card := by
    rw [← Finset.card_sdiff_add_card_inter (cleanVertices z) (deletionSet G z)]
    exact Nat.add_le_add_left
      (Finset.card_le_card Finset.inter_subset_right) _
  unfold score
  omega

def assignmentOfIndependent {n d : ℕ} (I : Finset (Fin n)) :
    Fin n → Fin (d + 1) → Bool :=
  fun v _ => if v ∈ I then false else true

theorem score_assignmentOfIndependent_proof {d n m : ℕ} (G : PortGraph d n m)
    (I : Finset (Fin n)) (hI : Independent G I) :
    score G (assignmentOfIndependent I : Fin n → Fin (d + 1) → Bool) =
      (d + 1) * n + m + I.card := by
  have hselected : selectedVertices
      (assignmentOfIndependent I : Fin n → Fin (d + 1) → Bool) = I := by
    ext v
    simp [selectedVertices, assignmentOfIndependent]
  have htransition : transitionPairs
      (assignmentOfIndependent I : Fin n → Fin (d + 1) → Bool) = ∅ := by
    ext pair
    simp [transitionPairs, transition, assignmentOfIndependent]
  have hfalse : falseEdges G
      (assignmentOfIndependent I : Fin n → Fin (d + 1) → Bool) = ∅ := by
    ext e
    simp [falseEdges, assignmentOfIndependent, hI e]
  simp only [score, hselected, htransition, hfalse, Finset.card_empty,
    Nat.sub_zero]
  omega

theorem exact_degree_identity_proof {d n m alpha : ℕ}
    (G : PortGraph d n m) (halpha : IsIndependenceNumber G alpha) :
    (∀ z : Fin n → Fin (d + 1) → Bool, score G z ≤ (d + 1) * n + m + alpha) ∧
      ∃ z : Fin n → Fin (d + 1) → Bool, score G z = (d + 1) * n + m + alpha := by
  constructor
  · intro z
    calc
      score G z ≤ (d + 1) * n + m + (repairedSet G z).card :=
        repairedSet_card_lower_bound_proof G z
      _ ≤ (d + 1) * n + m + alpha :=
        Nat.add_le_add_left (halpha.1 _ (repairedSet_independent_proof G z)) _
  · obtain ⟨I, hI, hcard⟩ := halpha.2
    exact ⟨assignmentOfIndependent I, by
      rw [score_assignmentOfIndependent_proof G I hI, hcard]⟩

/-! ### Port structure: `2 m = d n` and `2 α ≤ n` -/

/-- The port at the given side of an edge. -/
def portOf {d n m : ℕ} (G : PortGraph d n m) : Fin m ⊕ Fin m → Fin n × Fin d
  | Sum.inl e => (G.left e, G.leftPort e)
  | Sum.inr e => (G.right e, G.rightPort e)

theorem portOf_bijective {d n m : ℕ} (G : PortGraph d n m) :
    Function.Bijective (portOf G) := by
  constructor
  · intro a b hab
    rcases a with e | e <;> rcases b with f | f <;>
      simp only [portOf, Prod.mk.injEq] at hab
    · exact congrArg Sum.inl (G.left_unique e f hab.1 hab.2)
    · exact (G.cross_unique e f hab.1 hab.2).elim
    · exact (G.cross_unique f e hab.1.symm hab.2.symm).elim
    · exact congrArg Sum.inr (G.right_unique e f hab.1 hab.2)
  · rintro ⟨v, p⟩
    rcases G.port_occupied v p with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩
    · exact ⟨Sum.inl e, by simp [portOf, h1, h2]⟩
    · exact ⟨Sum.inr e, by simp [portOf, h1, h2]⟩

/-- Every edge has two ports and every vertex has `d` ports: `2 m = d n`. -/
theorem two_mul_edges_eq {d n m : ℕ} (G : PortGraph d n m) : 2 * m = d * n := by
  have h := Fintype.card_of_bijective (portOf_bijective G)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h
  have hc : d * n = n * d := Nat.mul_comm d n
  omega

noncomputable def portEquiv {d n m : ℕ} (G : PortGraph d n m) :
    Fin m ⊕ Fin m ≃ Fin n × Fin d :=
  Equiv.ofBijective (portOf G) (portOf_bijective G)

noncomputable def edgeOfPort {d n m : ℕ} (G : PortGraph d n m) (q : Fin n × Fin d) : Fin m :=
  Sum.elim id id ((portEquiv G).symm q)

theorem portOf_symm {d n m : ℕ} (G : PortGraph d n m) (q : Fin n × Fin d) :
    portOf G ((portEquiv G).symm q) = q :=
  (portEquiv G).apply_symm_apply q

/-- Distinct ports at vertices of an independent set lie on distinct edges. -/
theorem edgeOfPort_injOn {d n m : ℕ} (G : PortGraph d n m) (I : Finset (Fin n))
    (hI : Independent G I) (q q' : Fin n × Fin d) (hq : q.1 ∈ I) (hq' : q'.1 ∈ I)
    (h : edgeOfPort G q = edgeOfPort G q') : q = q' := by
  have e1 := portOf_symm G q
  have e2 := portOf_symm G q'
  unfold edgeOfPort at h
  generalize (portEquiv G).symm q = s at e1 h
  generalize (portEquiv G).symm q' = s' at e2 h
  rcases s with e | e <;> rcases s' with f | f <;>
    simp only [Sum.elim_inl, Sum.elim_inr, id_eq] at h
  · rw [← h] at e2
    rw [← e1, ← e2]
  · rw [← h] at e2
    have a : G.left e ∈ I := by
      rw [← e1] at hq
      exact hq
    have b : G.right e ∈ I := by
      rw [← e2] at hq'
      exact hq'
    exact absurd ⟨a, b⟩ (hI e)
  · rw [← h] at e2
    have a : G.right e ∈ I := by
      rw [← e1] at hq
      exact hq
    have b : G.left e ∈ I := by
      rw [← e2] at hq'
      exact hq'
    exact absurd ⟨b, a⟩ (hI e)
  · rw [← h] at e2
    rw [← e1, ← e2]

/-- An independent set has at most `n / 2` vertices (for `d > 0`). -/
theorem independent_card_bound {d n m : ℕ} (G : PortGraph d n m) (hd : 0 < d)
    (I : Finset (Fin n)) (hI : Independent G I) : 2 * I.card ≤ n := by
  have hcard : (I ×ˢ (Finset.univ : Finset (Fin d))).card ≤
      (Finset.univ : Finset (Fin m)).card :=
    Finset.card_le_card_of_injOn (edgeOfPort G) (fun _ _ => Finset.mem_univ _)
      (fun q hq q' hq' h =>
        edgeOfPort_injOn G I hI q q'
          (Finset.mem_product.mp (Finset.mem_coe.mp hq)).1
          (Finset.mem_product.mp (Finset.mem_coe.mp hq')).1 h)
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hcard
  have h2m := two_mul_edges_eq G
  have h3 : d * (2 * I.card) ≤ d * n := by nlinarith [hcard, h2m]
  exact Nat.le_of_mul_le_mul_left h3 hd

theorem independence_number_le_half {d n m alpha : ℕ} (G : PortGraph d n m)
    (hd : 0 < d) (halpha : IsIndependenceNumber G alpha) : 2 * alpha ≤ n := by
  obtain ⟨I, hI, hc⟩ := halpha.2
  rw [← hc]
  exact independent_card_bound G hd I hI

/-! ### The formula as an explicit list of Horn clauses -/

/-- A literal over the clone variables `(v, i)`; `positive = false` is a negated
literal. -/
structure Lit (n d : ℕ) where
  var : Fin n × Fin (d + 1)
  positive : Bool

/-- A clause is a list of literals. -/
abbrev Clause (n d : ℕ) := List (Lit n d)

def Lit.eval {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool) (l : Lit n d) : Bool :=
  if l.positive then z l.var.1 l.var.2 else !z l.var.1 l.var.2

/-- A clause is satisfied when some literal evaluates to true. -/
def Clause.satisfied {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool) (c : Clause n d) : Bool :=
  c.any (Lit.eval z)

/-- Dual-Horn: at most one negative literal. This is the polarity in which `T_H` is written. -/
def IsDualHorn {n d : ℕ} (c : Clause n d) : Prop :=
  (c.filter fun l => !l.positive).length ≤ 1

/-- Horn: at most one positive literal. -/
def IsHorn {n d : ℕ} (c : Clause n d) : Prop :=
  (c.filter fun l => l.positive).length ≤ 1

/-- The complement of a literal: the variable is renamed to its negation. -/
def Lit.compl {n d : ℕ} (l : Lit n d) : Lit n d :=
  ⟨l.var, !l.positive⟩

/-- The complement of a clause: every literal is complemented. -/
def Clause.compl {n d : ℕ} (c : Clause n d) : Clause n d :=
  c.map Lit.compl

/-- Indices of the clauses of `T_H`: one unit clause per vertex, one edge clause per
edge, and `d + 1` cyclic implications per vertex. -/
abbrev ClauseIdx (d n m : ℕ) := Fin n ⊕ Fin m ⊕ (Fin n × Fin (d + 1))

/-- The unit clause `(¬ z v 0)`. -/
def unitClause {n d : ℕ} (v : Fin n) : Clause n d :=
  [Lit.mk (v, 0) false]

/-- The edge clause `(z u p ∨ z w q)` of the edge `e`. -/
def edgeClause {d n m : ℕ} (G : PortGraph d n m) (e : Fin m) : Clause n d :=
  [Lit.mk (G.left e, edgeClone (G.leftPort e)) true,
    Lit.mk (G.right e, edgeClone (G.rightPort e)) true]

/-- The consistency implication `(¬ z v i ∨ z v (i+1))`. -/
def consClause {n d : ℕ} (p : Fin n × Fin (d + 1)) : Clause n d :=
  [Lit.mk p false, Lit.mk (p.1, p.2 + 1) true]

def clauseOf {d n m : ℕ} (G : PortGraph d n m) : ClauseIdx d n m → Clause n d :=
  Sum.elim unitClause (Sum.elim (edgeClause G) consClause)

/-- The number of occurrences of the variable `x` in a clause. -/
def Clause.count {n d : ℕ} (x : Fin n × Fin (d + 1)) (c : Clause n d) : ℕ :=
  (c.map fun l => if l.var = x then 1 else 0).sum

/-- The number of occurrences of the variable `x` in the formula `T_H`. -/
noncomputable def occurrences {d n m : ℕ} (G : PortGraph d n m)
    (x : Fin n × Fin (d + 1)) : ℕ :=
  ∑ c : ClauseIdx d n m, Clause.count x (clauseOf G c)

/-- The number of clauses of `T_H` satisfied by `z`. -/
noncomputable def satCount {d n m : ℕ} (G : PortGraph d n m)
    (z : Fin n → Fin (d + 1) → Bool) : ℕ :=
  (Finset.univ.filter fun c : ClauseIdx d n m =>
    Clause.satisfied z (clauseOf G c) = true).card

theorem card_filter_sum_proof {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : α ⊕ β ⊕ γ → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter fun a => P (Sum.inl a)).card +
        (Finset.univ.filter fun b => P (Sum.inr (Sum.inl b))).card +
          (Finset.univ.filter fun c => P (Sum.inr (Sum.inr c))).card := by
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  ring

theorem satCount_eq_score_proof {d n m : ℕ} (G : PortGraph d n m)
    (z : Fin n → Fin (d + 1) → Bool) : satCount G z = score G z := by
  have h := card_filter_sum_proof
    (fun c : ClauseIdx d n m => Clause.satisfied z (clauseOf G c) = true)
  have hU : (Finset.univ.filter fun v : Fin n =>
      Clause.satisfied z (clauseOf G (Sum.inl v)) = true).card =
        (selectedVertices z).card := by
    apply congrArg Finset.card
    ext v
    cases ha : z v 0 <;> simp [selectedVertices, clauseOf, unitClause,
      Clause.satisfied, Lit.eval, ha]
  have hE : (Finset.univ.filter fun e : Fin m =>
      Clause.satisfied z (clauseOf G (Sum.inr (Sum.inl e))) = true).card =
        m - (falseEdges G z).card := by
    have hset : (Finset.univ.filter fun e : Fin m =>
        Clause.satisfied z (clauseOf G (Sum.inr (Sum.inl e))) = true) =
          (falseEdges G z)ᶜ := by
      ext e
      cases ha : z (G.left e) (edgeClone (G.leftPort e)) <;>
        cases hb : z (G.right e) (edgeClone (G.rightPort e)) <;>
          simp [falseEdges, clauseOf, edgeClause,
            Clause.satisfied, Lit.eval, ha, hb]
    rw [hset, Finset.card_compl]
    simp
  have hC : (Finset.univ.filter fun p : Fin n × Fin (d + 1) =>
      Clause.satisfied z (clauseOf G (Sum.inr (Sum.inr p))) = true).card =
        (d + 1) * n - (transitionPairs z).card := by
    have hset : (Finset.univ.filter fun p : Fin n × Fin (d + 1) =>
        Clause.satisfied z (clauseOf G (Sum.inr (Sum.inr p))) = true) =
          (transitionPairs z)ᶜ := by
      ext ⟨v, i⟩
      cases ha : z v i <;> cases hb : z v (i + 1) <;>
        simp [transitionPairs, transition, clauseOf,
          consClause, Clause.satisfied, Lit.eval, ha, hb]
    rw [hset, Finset.card_compl]
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [Nat.mul_comm]
  unfold satCount score
  omega

theorem optimum_identity_proof {d n m alpha : ℕ} (G : PortGraph d n m)
    (halpha : IsIndependenceNumber G alpha) :
    IsGreatest (Set.range (satCount G)) ((d + 1) * n + m + alpha) := by
  obtain ⟨hle, z, hz⟩ := exact_degree_identity_proof G halpha
  refine ⟨⟨z, ?_⟩, ?_⟩
  · rw [satCount_eq_score_proof]
    exact hz
  · rintro _ ⟨w, rfl⟩
    rw [satCount_eq_score_proof]
    exact hle w

theorem formula_dual_horn_proof {d n m : ℕ} (G : PortGraph d n m) (c : ClauseIdx d n m) :
    IsDualHorn (clauseOf G c) := by
  rcases c with v | e | ⟨v, i⟩ <;>
    simp [IsDualHorn, clauseOf, unitClause, edgeClause, consClause]

theorem formula_horn_proof {d n m : ℕ} (G : PortGraph d n m) (c : ClauseIdx d n m) :
    IsHorn (Clause.compl (clauseOf G c)) := by
  rcases c with v | e | ⟨v, i⟩ <;>
    simp [IsHorn, Clause.compl, Lit.compl, clauseOf, unitClause, edgeClause, consClause]

theorem eval_compl_proof {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool) (l : Lit n d) :
    Lit.eval (fun v i => !z v i) (Lit.compl l) = Lit.eval z l := by
  rcases l with ⟨⟨v, i⟩, b⟩
  cases b <;> simp [Lit.eval, Lit.compl]

theorem satisfied_compl_proof {n d : ℕ} (z : Fin n → Fin (d + 1) → Bool) (c : Clause n d) :
    Clause.satisfied (fun v i => !z v i) (Clause.compl c) = Clause.satisfied z c := by
  induction c with
  | nil => simp [Clause.satisfied, Clause.compl]
  | cons l t ih =>
    simp only [Clause.satisfied, Clause.compl, List.map_cons, List.any_cons,
      eval_compl_proof] at ih ⊢
    rw [ih]

theorem formula_size_proof (d n m : ℕ) :
    Fintype.card (ClauseIdx d n m) = (d + 2) * n + m := by
  show Fintype.card (Fin n ⊕ Fin m ⊕ (Fin n × Fin (d + 1))) = (d + 2) * n + m
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

private theorem ite_pair_zero {A B : Prop} [Decidable A] [Decidable B]
    (hA : ¬ A) (hB : ¬ B) :
    (if A then (1 : ℕ) else 0) + (if B then 1 else 0) = 0 := by
  simp [hA, hB]

private theorem ite_pair_left {A B : Prop} [Decidable A] [Decidable B]
    (hA : A) (hB : ¬ B) :
    (if A then (1 : ℕ) else 0) + (if B then 1 else 0) = 1 := by
  simp [hA, hB]

private theorem ite_pair_right {A B : Prop} [Decidable A] [Decidable B]
    (hA : ¬ A) (hB : B) :
    (if A then (1 : ℕ) else 0) + (if B then 1 else 0) = 1 := by
  simp [hA, hB]

theorem three_occurrences_proof {d n m : ℕ} (G : PortGraph d n m)
    (x : Fin n × Fin (d + 1)) : occurrences G x = 3 := by
  obtain ⟨w, j⟩ := x
  have hC : ∑ p : Fin n × Fin (d + 1),
      Clause.count (w, j) (clauseOf G (Sum.inr (Sum.inr p))) = 2 := by
    have h1 : ∑ p : Fin n × Fin (d + 1),
        Clause.count (w, j) (clauseOf G (Sum.inr (Sum.inr p))) =
          ∑ p : Fin n × Fin (d + 1), ((if p = (w, j) then 1 else 0) +
            (if (p.1, p.2 + 1) = (w, j) then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      simp [clauseOf, consClause, Clause.count]
    rw [h1, Finset.sum_add_distrib]
    have h2 : ∑ p : Fin n × Fin (d + 1), (if p = (w, j) then 1 else 0) = 1 := by
      simp
    have h3 : ∑ p : Fin n × Fin (d + 1),
        (if (p.1, p.2 + 1) = (w, j) then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single (w, j - 1)]
      · simp
      · intro p _ hp
        have hne : ¬ ((p.1, p.2 + 1) = (w, j)) := by
          intro h
          apply hp
          have h1' : p.1 = w := congrArg Prod.fst h
          have h2' : p.2 + 1 = j := congrArg Prod.snd h
          exact Prod.ext h1' (eq_sub_of_add_eq h2')
        simp [hne]
      · intro h
        exact absurd (Finset.mem_univ _) h
    omega
  have hU : ∑ v : Fin n, Clause.count (w, j) (clauseOf G (Sum.inl v)) =
      if j = 0 then 1 else 0 := by
    have h1 : ∑ v : Fin n, Clause.count (w, j) (clauseOf G (Sum.inl v)) =
        ∑ v : Fin n, (if (v, (0 : Fin (d + 1))) = (w, j) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      simp [clauseOf, unitClause, Clause.count]
    rw [h1]
    by_cases hj : j = 0
    · subst hj
      simp
    · have hne : ∀ v : Fin n, ¬ ((v, (0 : Fin (d + 1))) = (w, j)) := fun v h =>
        hj (congrArg Prod.snd h).symm
      simp [hne, hj]
  have hE : ∑ e : Fin m, Clause.count (w, j) (clauseOf G (Sum.inr (Sum.inl e))) =
      if j = 0 then 0 else 1 := by
    have hterm : ∀ e : Fin m,
        Clause.count (w, j) (clauseOf G (Sum.inr (Sum.inl e))) =
          (if (G.left e, edgeClone (G.leftPort e)) = (w, j) then 1 else 0) +
            (if (G.right e, edgeClone (G.rightPort e)) = (w, j) then 1 else 0) := by
      intro e
      simp [clauseOf, edgeClause, Clause.count]
    rw [Finset.sum_congr rfl (fun e _ => hterm e)]
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨p0, hj⟩
    · subst hj
      simp [edgeClone, Fin.succ_ne_zero]
    · subst hj
      have hcond : ∀ (a : Fin n) (q : Fin d),
          ((a, edgeClone q) = (w, p0.succ)) ↔ (a = w ∧ q = p0) := by
        intro a q
        simp [edgeClone]
      simp only [hcond]
      rw [show ((if p0.succ = 0 then 0 else 1 : ℕ)) = 1 by
        simp [Fin.succ_ne_zero]]
      rcases G.port_occupied w p0 with ⟨e0, h0l, h0p⟩ | ⟨e0, h0r, h0p⟩
      · rw [Finset.sum_eq_single e0]
        · exact ite_pair_left ⟨h0l, h0p⟩ (fun ⟨hr, hrp⟩ =>
            G.cross_unique e0 e0 (h0l.trans hr.symm) (h0p.trans hrp.symm))
        · intro e _ hne
          exact ite_pair_zero
            (fun ⟨hl, hlp⟩ =>
              hne (G.left_unique e e0 (hl.trans h0l.symm) (hlp.trans h0p.symm)))
            (fun ⟨hr, hrp⟩ =>
              G.cross_unique e0 e (h0l.trans hr.symm) (h0p.trans hrp.symm))
        · intro h
          exact absurd (Finset.mem_univ e0) h
      · rw [Finset.sum_eq_single e0]
        · exact ite_pair_right
            (fun ⟨hl, hlp⟩ =>
              G.cross_unique e0 e0 (hl.trans h0r.symm) (hlp.trans h0p.symm))
            ⟨h0r, h0p⟩
        · intro e _ hne
          exact ite_pair_zero
            (fun ⟨hl, hlp⟩ =>
              G.cross_unique e e0 (hl.trans h0r.symm) (hlp.trans h0p.symm))
            (fun ⟨hr, hrp⟩ =>
              hne (G.right_unique e e0 (hr.trans h0r.symm) (hrp.trans h0p.symm)))
        · intro h
          exact absurd (Finset.mem_univ e0) h
  have h1 := Fintype.sum_sum_type
    (fun c : ClauseIdx d n m => Clause.count (w, j) (clauseOf G c))
  have h2 := Fintype.sum_sum_type
    (fun s : Fin m ⊕ (Fin n × Fin (d + 1)) =>
      Clause.count (w, j) (clauseOf G (Sum.inr s)))
  unfold occurrences
  rw [h1, h2, hU, hE, hC]
  by_cases hj : j = 0 <;> simp [hj]

/-! ### Values of lifted assignments and the transfer to `T_H` -/

/-- The assignment of the independent set `I`: clones of `v ∈ I` false, all others true. -/
theorem lift_satCount {d n m : ℕ} (G : PortGraph d n m) (I : Finset (Fin n))
    (hI : Independent G I) :
    satCount G (assignmentOfIndependent I : Fin n → Fin (d + 1) → Bool) =
      (d + 1) * n + m + I.card := by
  rw [satCount_eq_score_proof]
  exact score_assignmentOfIndependent_proof G I hI

theorem empty_independent {d n m : ℕ} (G : PortGraph d n m) :
    Independent G (∅ : Finset (Fin n)) := by
  intro e h
  simp at h

/-- The assignment with every clone true satisfies exactly the `(d+1) n` consistency
implications and the `m` edge clauses. -/
theorem allTrue_satCount {d n m : ℕ} (G : PortGraph d n m) :
    satCount G (assignmentOfIndependent (∅ : Finset (Fin n)) :
        Fin n → Fin (d + 1) → Bool) = (d + 1) * n + m := by
  rw [lift_satCount G ∅ (empty_independent G)]
  simp

theorem assignmentOfIndependent_empty {n d : ℕ} :
    (assignmentOfIndependent (∅ : Finset (Fin n)) : Fin n → Fin (d + 1) → Bool) =
      fun _ _ => true := by
  funext v i
  simp [assignmentOfIndependent]

/-- Baseline: the all-true assignment is a `(3d+2)/(3d+3)` approximation. -/
theorem baseline_ratio {d n m alpha : ℕ} (G : PortGraph d n m) (hd : 0 < d)
    (halpha : IsIndependenceNumber G alpha) :
    (3 * d + 2) * ((d + 1) * n + m + alpha) ≤
      (3 * d + 3) * satCount G
        (assignmentOfIndependent (∅ : Finset (Fin n)) : Fin n → Fin (d + 1) → Bool) := by
  rw [allTrue_satCount G]
  exact PalomaMax2SAT.DegreeTransfer.baseline_degree_d_proof d n m alpha
    (two_mul_edges_eq G) (independence_number_le_half G hd halpha)

/-- For `d ≥ 27` the all-true assignment already has ratio `83/84`. -/
theorem baseline_ratio_83_84 {d n m alpha : ℕ} (G : PortGraph d n m) (hd : 27 ≤ d)
    (halpha : IsIndependenceNumber G alpha) :
    83 * ((d + 1) * n + m + alpha) ≤
      84 * satCount G
        (assignmentOfIndependent (∅ : Finset (Fin n)) : Fin n → Fin (d + 1) → Bool) := by
  rw [allTrue_satCount G]
  exact PalomaMax2SAT.DegreeTransfer.baseline_exceeds_83_84_proof d n m alpha hd
    (two_mul_edges_eq G) (independence_number_le_half G (by omega) halpha)

/-- A `6/7`-approximate independent set lifts to the ratio `(21d+20)/(21d+21)`. -/
theorem lift_ratio_from_mis {d n m alpha : ℕ} (G : PortGraph d n m) (hd : 0 < d)
    (halpha : IsIndependenceNumber G alpha) (I : Finset (Fin n))
    (hI : Independent G I) (hs : 6 * alpha ≤ 7 * I.card) :
    (21 * d + 20) * ((d + 1) * n + m + alpha) ≤
      (21 * d + 21) * satCount G
        (assignmentOfIndependent I : Fin n → Fin (d + 1) → Bool) := by
  rw [lift_satCount G I hI]
  exact PalomaMax2SAT.DegreeTransfer.ratio_degree_d_from_mis_proof d n m alpha I.card
    (two_mul_edges_eq G) (independence_number_le_half G hd halpha) hs

/-- Berman--Fujito transfer for `d ≥ 22`. -/
theorem lift_ratio_bf {d n m alpha : ℕ} (G : PortGraph d n m) (hd : 22 ≤ d)
    (halpha : IsIndependenceNumber G alpha) (I : Finset (Fin n))
    (hI : Independent G I) (hs : 5 * alpha ≤ (d + 3) * I.card) :
    83 * ((d + 1) * n + m + alpha) ≤
      84 * satCount G (assignmentOfIndependent I : Fin n → Fin (d + 1) → Bool) := by
  rw [lift_satCount G I hI]
  exact PalomaMax2SAT.DegreeTransfer.bf_degree_d_proof d n m alpha I.card hd
    (two_mul_edges_eq G) (independence_number_le_half G (by omega) halpha) hs

/-- Threshold transfer: `|I| ≥ ((27-d)/28) α` lifts to the ratio `83/84`. -/
theorem lift_ratio_threshold {d n m alpha : ℕ} (G : PortGraph d n m) (hd : 0 < d)
    (halpha : IsIndependenceNumber G alpha) (I : Finset (Fin n))
    (hI : Independent G I) (hs : 27 * alpha ≤ 28 * I.card + d * alpha) :
    83 * ((d + 1) * n + m + alpha) ≤
      84 * satCount G (assignmentOfIndependent I : Fin n → Fin (d + 1) → Bool) := by
  rw [lift_satCount G I hI]
  exact PalomaMax2SAT.DegreeTransfer.threshold_degree_d_proof d n m alpha I.card
    (two_mul_edges_eq G) (independence_number_le_half G hd halpha) hs

/-- Degree `21`: the two-branch transfer. -/
theorem lift_ratio_degree_21 {n m alpha : ℕ} (G : PortGraph 21 n m)
    (halpha : IsIndependenceNumber G alpha) (I : Finset (Fin n))
    (hI : Independent G I)
    (hbf : 200 * alpha ≤ 99 * n → 50 * alpha ≤ 241 * I.card)
    (hcut : 99 * n < 200 * alpha → 3 * n ≤ 25 * I.card) :
    83 * ((21 + 1) * n + m + alpha) ≤
      84 * satCount G (assignmentOfIndependent I : Fin n → Fin (21 + 1) → Bool) := by
  rw [lift_satCount G I hI]
  have h := PalomaMax2SAT.DegreeTransfer.two_branch_degree_21_proof n m alpha I.card
    (two_mul_edges_eq G) (independence_number_le_half G (by omega) halpha) hbf hcut
  omega

/-- Berman--Fujito transfer for every degree `e + 2` with `ε = 1/c`. -/
theorem lift_ratio_bf_general {e n m alpha c : ℕ} (G : PortGraph (e + 2) n m)
    (halpha : IsIndependenceNumber G alpha) (I : Finset (Fin n))
    (hI : Independent G I) (hs : 5 * c * alpha ≤ (((e + 2) + 3) * c + 1) * I.card) :
    (3 * (e + 2) + 3) * (((e + 2) + 3) * c + 1) * ((e + 2 + 1) * n + m + alpha) ≤
      (3 * (e + 2) + 3) * (((e + 2) + 3) * c + 1) *
          satCount G (assignmentOfIndependent I : Fin n → Fin (e + 2 + 1) → Bool) +
        (e * c + 1) * ((e + 2 + 1) * n + m + alpha) := by
  rw [lift_satCount G I hI]
  exact PalomaMax2SAT.DegreeTransfer.bf_general_degree_d_proof e n m alpha I.card c
    (two_mul_edges_eq G) (independence_number_le_half G (by omega) halpha) hs

end PalomaMax2SAT.DegreeFormula
