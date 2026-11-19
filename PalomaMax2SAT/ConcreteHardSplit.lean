module

public import PalomaMax2SAT.HardOccurrenceSplit

public section

namespace PalomaMax2SAT.ConcreteHardSplit

open PalomaMax2SAT.HardOccurrenceSplit

structure Literal (Var : Type*) (Occ : Var → Type*) where
  var : Var
  occ : Occ var
  pos : Bool

def HornClause {Var : Type*} {Occ : Var → Type*}
    (c : Finset (Literal Var Occ)) : Prop :=
  ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.pos = true → l₂.pos = true → l₁ = l₂

structure WeightedHornSplit (Var : Type*) (Occ : Var → Type*) (Clause : Type*) where
  weight : Clause → ℕ
  lits : Clause → Finset (Literal Var Occ)
  horn : ∀ c, HornClause (lits c)

noncomputable def sourceScore {Var : Type*} {Occ : Var → Type*} {Clause : Type*}
    [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause) (x : Var → Bool) : ℕ := by
  classical
  exact ∑ c : Clause,
    if ∃ l ∈ F.lits c, x l.var = l.pos then F.weight c else 0

noncomputable def splitScore {Var : Type*} {Occ : Var → Type*} {Clause : Type*}
    [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (z : (v : Var) → Occ v → Bool) : ℕ := by
  classical
  exact ∑ c : Clause,
    if ∃ l ∈ F.lits c, z l.var l.occ = l.pos then F.weight c else 0

def Feasible {Var : Type*} {Occ : Var → Type*}
    (next : ∀ v, Occ v → Occ v)
    (z : (v : Var) → Occ v → Bool) : Prop :=
  ∀ v, HardImplicationsHold (next v) (z v)

def encode {Var : Type*} {Occ : Var → Type*} (x : Var → Bool) :
    (v : Var) → Occ v → Bool :=
  fun v _ => x v

def decode {Var : Type*} {Occ : Var → Type*} (base : ∀ v, Occ v)
    (z : (v : Var) → Occ v → Bool) : Var → Bool :=
  fun v => z v (base v)

theorem encode_feasible {Var : Type*} {Occ : Var → Type*}
    (next : ∀ v, Occ v → Occ v) (x : Var → Bool) :
    Feasible next (encode (Occ := Occ) x) := by
  simp only [Feasible, HardImplicationsHold]
  intro v i hi
  simpa [encode] using hi

theorem encodeScore {Var : Type*} {Occ : Var → Type*} {Clause : Type*}
    [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ∀ v, Occ v → Occ v) (x : Var → Bool) :
    splitScore F (encode (Occ := Occ) x) = sourceScore F x := by
  classical
  unfold splitScore sourceScore
  apply Finset.sum_congr rfl
  intro c _
  simp [encode]

theorem feasible_constant {Var : Type*} {Occ : Var → Type*}
    (next : ∀ v, Occ v → Occ v) (base : ∀ v, Occ v)
    (horb : ∀ v, OrbitConnected (next v))
    {z : (v : Var) → Occ v → Bool} (hz : Feasible next z) :
    ∀ v o, z v (base v) = z v o := by
  have hz' : ∀ v i, z v i = true → z v (next v i) = true := by
    intro v
    simpa only [Feasible, HardImplicationsHold] using hz v
  have horb' : ∀ v i j, ∃ k, advance (next v) k i = j := by
    intro v
    simpa only [OrbitConnected] using horb v
  intro v o
  cases hb : z v (base v) <;> cases ho : z v o
  · rfl
  · obtain ⟨k, hk⟩ := horb' v (base v) o
    have htrue : z v (advance (next v) k (base v)) = true := by
      have hprop : ∀ k i, z v i = true → z v (advance (next v) k i) = true := by
        intro k
        induction k with
        | zero => intro i hi; simpa [advance] using hi
        | succ k ih =>
            intro i hi
            change z v (next v (advance (next v) k i)) = true
            exact hz' v _ (ih i hi)
      exact hprop k (base v) hb
    rw [hk, ho] at htrue
    simp at htrue
  · obtain ⟨k, hk⟩ := horb' v o (base v)
    have htrue : z v (advance (next v) k o) = true := by
      have hprop : ∀ k i, z v i = true → z v (advance (next v) k i) = true := by
        intro k
        induction k with
        | zero => intro i hi; simpa [advance] using hi
        | succ k ih =>
            intro i hi
            change z v (next v (advance (next v) k i)) = true
            exact hz' v _ (ih i hi)
      exact hprop k o ho
    rw [hk, hb] at htrue
    simp at htrue
  · rfl

theorem decodeScore {Var : Type*} {Occ : Var → Type*} {Clause : Type*}
    [Fintype Clause]
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

theorem concrete_exact_hard_occurrence_split_proof
    {Var : Type*} {Occ : Var → Type*} {Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ∀ v, Occ v → Occ v) (base : ∀ v, Occ v)
    (horb : ∀ v, OrbitConnected (next v))
    (opt : ℕ) (hsource : IsOptimum (sourceScore F) opt) :
    IsHardOptimum (Feasible next) (splitScore F) opt := by
  have hsource' :
      (∀ a, sourceScore F a ≤ opt) ∧ ∃ a, sourceScore F a = opt := by
    simpa only [IsOptimum] using hsource
  simp only [IsHardOptimum]
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [← decodeScore F next base horb hz]
    exact hsource'.1 (decode base z)
  · obtain ⟨x, hx⟩ := hsource'.2
    refine ⟨encode (Occ := Occ) x, encode_feasible next x, ?_⟩
    rw [encodeScore F next x, hx]

theorem concrete_feasible_solution_ratio_preserved_proof
    {Var : Type*} {Occ : Var → Type*} {Clause : Type*} [Fintype Clause]
    (F : WeightedHornSplit Var Occ Clause)
    (next : ∀ v, Occ v → Occ v) (base : ∀ v, Occ v)
    (horb : ∀ v, OrbitConnected (next v))
    (z : (v : Var) → Occ v → Bool) (hz : Feasible next z) :
    splitScore F z = sourceScore F (decode base z) := by
  exact (decodeScore F next base horb hz).symm

end PalomaMax2SAT.ConcreteHardSplit
