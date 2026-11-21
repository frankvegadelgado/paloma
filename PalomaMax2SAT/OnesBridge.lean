module

public import Mathlib
public import PalomaMax2SAT.CubicThreeOccurrence
public import PalomaMax2SAT.OnesOptimal

@[expose] public section

/-!
# The cubic formula `T_H` and the Max-Ones / Min-Ones formulas of its graph

For a port graph `G` (the cubic class of `CubicThreeOccurrence`) let `negGraph G` be its simple
graph on the vertex set `Fin n`. The negative formula `N_H` (one clause `(¬x_u ∨ ¬x_v)` per edge)
and the positive formula `P_H` (one clause `(x_u ∨ x_v)` per edge) have the graph `negGraph G`.
This module proves, for `α = α(H)`:

* the optimum of `T_H` is `4 n + m + α` and the maximum number of true variables of a satisfying
  assignment of `N_H` is `α` (`opt_and_maxOnes`);
* the minimum number of true variables of a satisfying assignment of `P_H` is `n - α`
  (`minOnes_positive_graph`).
-/

namespace PalomaMax2SAT.OnesBridge

open PalomaMax2SAT.CubicThreeOccurrence
open PalomaMax2SAT.OnesOptimal

variable {n m : ℕ}

/-- The simple graph of a port graph. -/
def negGraph (G : PortGraph n m) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ e, G.left e = u ∧ G.right e = v

theorem independent_iff (G : PortGraph n m) (I : Finset (Fin n)) :
    Independent G I ↔ ∀ u ∈ I, ∀ v ∈ I, ¬ (negGraph G).Adj u v := by
  constructor
  · intro h u hu v hv hadj
    obtain ⟨_, ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hadj
    · exact h e ⟨by rw [h1]; exact hu, by rw [h2]; exact hv⟩
    · exact h e ⟨by rw [h2]; exact hv, by rw [h1]; exact hu⟩
  · intro h e he
    exact h _ he.1 _ he.2
      ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨G.left_ne_right e, Or.inl ⟨e, rfl, rfl⟩⟩)

theorem indepOutside_empty_iff (G : PortGraph n m) (T : Finset (Fin n)) :
    IndepOutside (negGraph G) ∅ T ↔ Independent G T := by
  rw [independent_iff]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨fun u _ => by simp, h⟩

/-- The optimum of `T_H` and the maximum number of true variables of `N_H` are
`4 n + m + α` and `α`. -/
theorem opt_and_maxOnes (G : PortGraph n m) {alpha : ℕ} (halpha : IsIndependenceNumber G alpha) :
    ((∀ z, score G z ≤ 4 * n + m + alpha) ∧ ∃ z, score G z = 4 * n + m + alpha) ∧
      ((∀ a, NegSat (negGraph G) ∅ a → ones a ≤ alpha) ∧
        ∃ a, NegSat (negGraph G) ∅ a ∧ ones a = alpha) := by
  refine ⟨exact_three_occurrence_identity_proof G halpha, ?_⟩
  apply maxOnes_negative
  constructor
  · intro T hT
    exact halpha.1 T ((indepOutside_empty_iff G T).mp hT)
  · obtain ⟨I, hI, hcard⟩ := halpha.2
    exact ⟨I, (indepOutside_empty_iff G I).mpr hI, hcard⟩

/-- The minimum number of true variables of a satisfying assignment of the positive formula
of `H` is `n - α`. -/
theorem minOnes_positive_graph (G : PortGraph n m) {alpha : ℕ}
    (halpha : IsIndependenceNumber G alpha) :
    (∀ a, PosSat (negGraph G) ∅ a → n - alpha ≤ ones a) ∧
      ∃ a, PosSat (negGraph G) ∅ a ∧ ones a = n - alpha := by
  have h1 : ∀ T : Finset (Fin n), (∀ u ∈ T, ∀ v ∈ T, ¬ (negGraph G).Adj u v) → T.card ≤ alpha :=
    fun T hT => halpha.1 T ((independent_iff G T).mpr hT)
  have h2 : ∃ T : Finset (Fin n), (∀ u ∈ T, ∀ v ∈ T, ¬ (negGraph G).Adj u v) ∧
      T.card = alpha := by
    obtain ⟨I, hI, hc⟩ := halpha.2
    exact ⟨I, (independent_iff G I).mp hI, hc⟩
  obtain ⟨hg1, C, hC, hcard⟩ := gallai (negGraph G) ⟨h1, h2⟩
  have hmin := minOnes_positive (negGraph G) ∅ (tau := n - alpha)
    ⟨fun C' hC' => hg1 C' ((coverOutside_empty_iff _ C').mp hC'),
      ⟨C, (coverOutside_empty_iff _ C).mpr hC, hcard⟩⟩
  constructor
  · intro a ha
    simpa using hmin.1 a ha
  · obtain ⟨a, ha, hones⟩ := hmin.2
    exact ⟨a, ha, by simpa using hones⟩

end PalomaMax2SAT.OnesBridge
