module

public import Mathlib

@[expose] public section

/-!
# Max-Ones for negative 2-CNF formulas and Min-Ones for positive 2-CNF formulas

Let `G` be a graph on the variables `x_0, …, x_{n-1}`.

* The *negative* formula of `(G, Z)` has the clause `(¬ x_u ∨ ¬ x_v)` for every edge `uv`
  and the unit clause `(¬ x_u)` for every `u ∈ Z`. It is a Horn formula.
* The *positive* formula of `(G, F)` has the clause `(x_u ∨ x_v)` for every edge `uv` and
  the unit clause `(x_u)` for every `u ∈ F`. It is not a Horn formula.

For an assignment `a`, `ones a` is the number of true variables. This module proves:

* `negSat_iff`: `a` satisfies the negative formula iff its set of true variables is an
  independent set of `G` that avoids `Z`;
* `maxOnes_negative`: the maximum number of true variables of a satisfying assignment of the
  negative formula is the independence number of `G` outside `Z`;
* `posSat_iff`: `a` satisfies the positive formula iff `F` is true and the set of true
  variables outside `F` is a vertex cover of the edges not touching `F`;
* `minOnes_positive`: the minimum number of true variables of a satisfying assignment of the
  positive formula is `|F|` plus the minimum size of such a cover.

The hardness statements about Maximum Independent Set and Minimum Vertex Cover that the
paper combines with these identities (Håstad; Zuckerman; Khot--Regev; Austrin--Khot--Safra;
Chan; Halperin; Alimonti--Kann) are cited in the paper and are not formalized.
-/

namespace PalomaMax2SAT.OnesOptimal

variable {n : ℕ}

/-- The set of true variables of an assignment. -/
def trueSet (a : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => a u = true

/-- The number of true variables. -/
def ones (a : Fin n → Bool) : ℕ := (trueSet a).card

/-- The assignment that is true exactly on `T`. -/
def ofSet (T : Finset (Fin n)) : Fin n → Bool := fun u => decide (u ∈ T)

theorem trueSet_ofSet (T : Finset (Fin n)) : trueSet (ofSet T) = T := by
  ext u
  simp [trueSet, ofSet]

theorem ones_ofSet (T : Finset (Fin n)) : ones (ofSet T) = T.card := by
  unfold ones
  rw [trueSet_ofSet]

theorem mem_trueSet {a : Fin n → Bool} {u : Fin n} : u ∈ trueSet a ↔ a u = true := by
  simp [trueSet]

/-! ### Negative formulas: Max-Ones is Maximum Independent Set -/

section Negative

variable (G : SimpleGraph (Fin n))

/-- `a` satisfies `(¬x_u ∨ ¬x_v)` for every edge and `(¬x_u)` for every `u ∈ Z`. -/
def NegSat (Z : Finset (Fin n)) (a : Fin n → Bool) : Prop :=
  (∀ u ∈ Z, a u = false) ∧ ∀ u v, G.Adj u v → ¬ (a u = true ∧ a v = true)

/-- An independent set of `G` avoiding `Z`. -/
def IndepOutside (Z T : Finset (Fin n)) : Prop :=
  (∀ u ∈ T, u ∉ Z) ∧ ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v

theorem negSat_iff (Z : Finset (Fin n)) (a : Fin n → Bool) :
    NegSat G Z a ↔ IndepOutside G Z (trueSet a) := by
  constructor
  · rintro ⟨hZ, hE⟩
    refine ⟨fun u hu hZu => ?_, fun u hu v hv hadj => ?_⟩
    · have h1 := hZ u hZu
      have h2 : a u = true := mem_trueSet.mp hu
      rw [h1] at h2
      exact Bool.false_ne_true h2
    · exact hE u v hadj ⟨mem_trueSet.mp hu, mem_trueSet.mp hv⟩
  · rintro ⟨hZ, hE⟩
    refine ⟨fun u hu => ?_, fun u v hadj hab => ?_⟩
    · by_contra h
      have h2 : a u = true := by simpa using h
      exact hZ u (mem_trueSet.mpr h2) hu
    · exact hE u (mem_trueSet.mpr hab.1) v (mem_trueSet.mpr hab.2) hadj

/-- Max-Ones of the negative formula is the independence number of `G` outside `Z`:
if `alpha` is that number, no satisfying assignment has more than `alpha` true variables and
some satisfying assignment has exactly `alpha`. -/
theorem maxOnes_negative (Z : Finset (Fin n)) {alpha : ℕ}
    (halpha : (∀ T, IndepOutside G Z T → T.card ≤ alpha) ∧
      ∃ T, IndepOutside G Z T ∧ T.card = alpha) :
    (∀ a, NegSat G Z a → ones a ≤ alpha) ∧ ∃ a, NegSat G Z a ∧ ones a = alpha := by
  constructor
  · intro a ha
    exact halpha.1 _ ((negSat_iff G Z a).mp ha)
  · obtain ⟨T, hT, hcard⟩ := halpha.2
    refine ⟨ofSet T, (negSat_iff G Z _).mpr ?_, by rw [ones_ofSet, hcard]⟩
    rw [trueSet_ofSet]
    exact hT

/-- The all-false assignment satisfies every negative formula. -/
theorem negSat_allFalse (Z : Finset (Fin n)) : NegSat G Z (fun _ => false) := by
  refine ⟨fun _ _ => rfl, fun u v _ h => ?_⟩
  exact Bool.false_ne_true h.1

end Negative

/-! ### Positive formulas: Min-Ones is Minimum Vertex Cover -/

section Positive

variable (G : SimpleGraph (Fin n))

/-- `a` satisfies `(x_u ∨ x_v)` for every edge and `(x_u)` for every `u ∈ F`. -/
def PosSat (F : Finset (Fin n)) (a : Fin n → Bool) : Prop :=
  (∀ u ∈ F, a u = true) ∧ ∀ u v, G.Adj u v → a u = true ∨ a v = true

/-- A set `C` outside `F` covering every edge that does not touch `F`. -/
def CoverOutside (F C : Finset (Fin n)) : Prop :=
  (∀ u ∈ C, u ∉ F) ∧ ∀ u v, G.Adj u v → u ∈ F ∨ v ∈ F ∨ u ∈ C ∨ v ∈ C

theorem posSat_iff_cover (F : Finset (Fin n)) (a : Fin n → Bool) :
    PosSat G F a ↔ F ⊆ trueSet a ∧ CoverOutside G F (trueSet a \ F) := by
  constructor
  · rintro ⟨hF, hE⟩
    refine ⟨fun u hu => mem_trueSet.mpr (hF u hu), fun u hu => ?_, fun u v hadj => ?_⟩
    · exact (Finset.mem_sdiff.mp hu).2
    · by_cases hu : u ∈ F
      · exact Or.inl hu
      · by_cases hv : v ∈ F
        · exact Or.inr (Or.inl hv)
        · rcases hE u v hadj with h | h
          · exact Or.inr (Or.inr (Or.inl
              (Finset.mem_sdiff.mpr ⟨mem_trueSet.mpr h, hu⟩)))
          · exact Or.inr (Or.inr (Or.inr
              (Finset.mem_sdiff.mpr ⟨mem_trueSet.mpr h, hv⟩)))
  · rintro ⟨hF, _, hE⟩
    refine ⟨fun u hu => mem_trueSet.mp (hF hu), fun u v hadj => ?_⟩
    rcases hE u v hadj with h | h | h | h
    · exact Or.inl (mem_trueSet.mp (hF h))
    · exact Or.inr (mem_trueSet.mp (hF h))
    · exact Or.inl (mem_trueSet.mp (Finset.mem_sdiff.mp h).1)
    · exact Or.inr (mem_trueSet.mp (Finset.mem_sdiff.mp h).1)

/-- Min-Ones of the positive formula is `|F|` plus the minimum size `tau` of a cover outside
`F`: every satisfying assignment has at least `|F| + tau` true variables and some satisfying
assignment has exactly `|F| + tau`. -/
theorem minOnes_positive (F : Finset (Fin n)) {tau : ℕ}
    (htau : (∀ C, CoverOutside G F C → tau ≤ C.card) ∧
      ∃ C, CoverOutside G F C ∧ C.card = tau) :
    (∀ a, PosSat G F a → F.card + tau ≤ ones a) ∧
      ∃ a, PosSat G F a ∧ ones a = F.card + tau := by
  constructor
  · intro a ha
    obtain ⟨hF, hC⟩ := (posSat_iff_cover G F a).mp ha
    have h1 := htau.1 _ hC
    have h2 := Finset.card_sdiff_add_card_eq_card hF
    unfold ones
    omega
  · obtain ⟨C, ⟨hCF, hE⟩, hcard⟩ := htau.2
    have hinter : F ∩ C = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
      intro u hu hC
      exact hCF u hC hu
    have hunion := Finset.card_union_add_card_inter F C
    rw [hinter, Finset.card_empty] at hunion
    refine ⟨ofSet (F ∪ C), ⟨fun u hu => ?_, fun u v hadj => ?_⟩, ?_⟩
    · simp [ofSet, hu]
    · rcases hE u v hadj with h | h | h | h <;> simp [ofSet, h]
    · rw [ones_ofSet]
      omega

/-- The all-true assignment satisfies every positive formula. -/
theorem posSat_allTrue (F : Finset (Fin n)) : PosSat G F (fun _ => true) :=
  ⟨fun _ _ => rfl, fun _ _ _ => Or.inl rfl⟩

/-! ### Gallai's identity -/

/-- `C` covers every edge of `G`. -/
def IsCover (C : Finset (Fin n)) : Prop := ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C

theorem coverOutside_empty_iff (C : Finset (Fin n)) :
    CoverOutside G ∅ C ↔ IsCover G C := by
  constructor
  · rintro ⟨_, hE⟩ u v hadj
    rcases hE u v hadj with h | h | h | h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    refine ⟨fun u _ => by simp, fun u v hadj => ?_⟩
    rcases h u v hadj with h1 | h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))

theorem independent_iff_compl_cover (T : Finset (Fin n)) :
    (∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) ↔ IsCover G Tᶜ := by
  constructor
  · intro h u v hadj
    by_contra hc
    have hu : u ∈ T := by
      by_contra hu
      exact hc (Or.inl (Finset.mem_compl.mpr hu))
    have hv : v ∈ T := by
      by_contra hv
      exact hc (Or.inr (Finset.mem_compl.mpr hv))
    exact h u hu v hv hadj
  · intro h u hu v hv hadj
    rcases h u v hadj with h1 | h1
    · exact (Finset.mem_compl.mp h1) hu
    · exact (Finset.mem_compl.mp h1) hv

/-- Gallai's identity: the minimum vertex cover size is `n - α`. -/
theorem gallai {alpha : ℕ}
    (halpha : (∀ T : Finset (Fin n), (∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) → T.card ≤ alpha) ∧
      ∃ T : Finset (Fin n), (∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) ∧ T.card = alpha) :
    (∀ C : Finset (Fin n), IsCover G C → n - alpha ≤ C.card) ∧
      ∃ C : Finset (Fin n), IsCover G C ∧ C.card = n - alpha := by
  constructor
  · intro C hC
    have hind : ∀ u ∈ Cᶜ, ∀ v ∈ Cᶜ, ¬ G.Adj u v := by
      rw [independent_iff_compl_cover]
      simpa using hC
    have h1 := halpha.1 Cᶜ hind
    have h2 : Cᶜ.card = n - C.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have h3 : C.card ≤ n := by
      have := Finset.card_le_univ C
      simpa using this
    omega
  · obtain ⟨T, hT, hcard⟩ := halpha.2
    refine ⟨Tᶜ, (independent_iff_compl_cover G T).mp hT, ?_⟩
    rw [Finset.card_compl, Fintype.card_fin, hcard]

end Positive

end PalomaMax2SAT.OnesOptimal
