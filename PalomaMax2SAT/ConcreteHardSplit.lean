module

public import PalomaMax2SAT.HardOccurrenceSplit

public section

namespace PalomaMax2SAT.ConcreteHardSplit

open PalomaMax2SAT.HardOccurrenceSplit

/-- A literal occurrence: a variable, one of its occurrences, and a polarity. -/
structure Literal (Var : Type*) (Occ : Var ? Type*) where
  var : Var
  occ : Occ var
  pos : Bool

/-- At most one positive literal, i.e. a Horn clause. -/
def HornClause {Var : Type*} {Occ : Var ? Type*}
    (c : Finset (Literal Var Occ)) : Prop :=
  ? l1 ? c, ? l2 ? c, l1.pos = true ? l2.pos = true ? l1 = l2

/--
A weighted Horn formula in occurrence-split form.  Each clause already carries
literal occurrences.  The hard cycle implications are not part of the objective;
they are represented by `Feasible` below.
-/
structure WeightedHornSplit (Var : Type*) (Occ : Var ? Type*) (Clause : Type*) where
  weight : Clause ? N
  lits : Clause ? Finset (Literal Var Occ)
  horn : ? c, HornClause (lits c)

/-- Objective value of the source assignment, read through the occurrence literals. -/
noncomputable def sourceScore {Var Occ Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause) (x : Var ? Bool) : N := by
  classical
  exact ? c : Clause,
    if ? l ? F.lits c, x l.var = l.pos then F.weight c else 0

/-- Objective value of a split assignment. -/
noncomputable def splitScore {Var Occ Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (z : (v : Var) ? Occ v ? Bool) : N := by
  classical
  exact ? c : Clause,
    if ? l ? F.lits c, z l.var l.occ = l.pos then F.weight c else 0

/-- Feasible split assignments satisfy all hard cyclic implications. -/
def Feasible {Var : Type*} {Occ : Var ? Type*}
    (next : ? v, Occ v ? Occ v)
    (z : (v : Var) ? Occ v ? Bool) : Prop :=
  ? v, HardImplicationsHold (next v) (z v)

/-- Encode a source assignment by making all occurrences of a variable equal. -/
def encode {Var : Type*} {Occ : Var ? Type*} (x : Var ? Bool) :
    (v : Var) ? Occ v ? Bool :=
  fun v _ => x v

/-- Decode a split assignment by reading one chosen occurrence per variable. -/
def decode {Var : Type*} {Occ : Var ? Type*} (base : ? v, Occ v)
    (z : (v : Var) ? Occ v ? Bool) : Var ? Bool :=
  fun v => z v (base v)

theorem encode_feasible {Var : Type*} {Occ : Var ? Type*}
    (next : ? v, Occ v ? Occ v) (x : Var ? Bool) :
    Feasible next (encode (Occ := Occ) x) := by
  intro v o ho
  simpa [encode] using ho

theorem encodeScore {Var Occ Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ? v, Occ v ? Occ v) (x : Var ? Bool) :
    splitScore F (encode (Occ := Occ) x) = sourceScore F x := by
  classical
  unfold splitScore sourceScore
  apply Finset.sum_congr rfl
  intro c _
  simp [encode]

theorem feasible_constant {Var : Type*} {Occ : Var ? Type*}
    (next : ? v, Occ v ? Occ v) (base : ? v, Occ v)
    (horb : ? v, OrbitConnected (next v))
    {z : (v : Var) ? Occ v ? Bool} (hz : Feasible next z) :
    ? v o, z v (base v) = z v o := by
  intro v o
  cases hb : z v (base v) <;> cases ho : z v o
  · rfl
  · obtain ?k, hk? := horb v (base v) o
    have htrue :=
      propagate_hard_implications (next v) (z v) (hz v) k (base v) hb
    rw [hk, ho] at htrue
    simp at htrue
  · obtain ?k, hk? := horb v o (base v)
    have htrue :=
      propagate_hard_implications (next v) (z v) (hz v) k o ho
    rw [hk, hb] at htrue
    simp at htrue
  · rfl

theorem decodeScore {Var Occ Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ? v, Occ v ? Occ v) (base : ? v, Occ v)
    (horb : ? v, OrbitConnected (next v))
    {z : (v : Var) ? Occ v ? Bool} (hz : Feasible next z) :
    sourceScore F (decode base z) = splitScore F z := by
  classical
  have hconst : ? v o, z v (base v) = z v o :=
    feasible_constant next base horb hz
  unfold sourceScore splitScore decode
  apply Finset.sum_congr rfl
  intro c _
  have hsat : (? l ? F.lits c, z l.var (base l.var) = l.pos) ?
      (? l ? F.lits c, z l.var l.occ = l.pos) := by
    constructor
    · rintro ?l, hl, h?
      exact ?l, hl, by rw [? hconst l.var l.occ]; exact h?
    · rintro ?l, hl, h?
      exact ?l, hl, by rw [hconst l.var l.occ]; exact h?
  by_cases h : ? l ? F.lits c, z l.var l.occ = l.pos
  · have h' : ? l ? F.lits c, z l.var (base l.var) = l.pos := hsat.mpr h
    simp [h, h']
  · have h' : ¬ ? l ? F.lits c, z l.var (base l.var) = l.pos :=
      fun hp => h (hsat.mp hp)
    simp [h, h']

/-- Concrete optimum preservation for the weighted Horn occurrence split. -/
theorem concrete_exact_hard_occurrence_split
    {Var Occ Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ? v, Occ v ? Occ v) (base : ? v, Occ v)
    (horb : ? v, OrbitConnected (next v))
    (opt : N) (hsource : IsOptimum (sourceScore F) opt) :
    IsHardOptimum (Feasible next) (splitScore F) opt := by
  constructor
  · intro z hz
    rw [? decodeScore F next base horb hz]
    exact hsource.1 (decode base z)
  · obtain ?x, hx? := hsource.2
    refine ?encode (Occ := Occ) x, encode_feasible next x, ?_?
    rw [encodeScore F next x, hx]

/-- Concrete feasible-solution value preservation for the occurrence split. -/
theorem concrete_feasible_solution_ratio_preserved
    {Var Occ Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ? v, Occ v ? Occ v) (base : ? v, Occ v)
    (horb : ? v, OrbitConnected (next v))
    (z : (v : Var) ? Occ v ? Bool) (hz : Feasible next z) :
    splitScore F z = sourceScore F (decode base z) := by
  exact (decodeScore F next base horb hz).symm

end PalomaMax2SAT.ConcreteHardSplit