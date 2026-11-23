module

public import Mathlib
public import PalomaMax2SAT.DegreeFormula

@[expose] public section

/-!
# Exact optima of `T_H` in degrees `1` and `2`

Helper lemmas for `PalomaMax2SAT.UgcRegular.all_degd`.

* For a `1`-regular port graph the independence number is `m = n / 2` (one endpoint of every
  edge), so the optimum of `T_H` is `3 n`.
* For a `2`-regular port graph `m = n`, so the optimum of `T_H` is `4 n + α`.

That a maximum independent set of a graph of maximum degree `2` is computed in linear time is
not formalized.
-/

namespace PalomaMax2SAT.RegularLemmas

open PalomaMax2SAT.DegreeFormula

/-- In a `1`-regular port graph the independence number is `m`. -/
theorem alpha_deg_one {n m alpha : ℕ} (G : PortGraph 1 n m)
    (halpha : IsIndependenceNumber G alpha) : alpha = m := by
  have hle : 2 * alpha ≤ n := independence_number_le_half G (by norm_num) halpha
  have h2 : 2 * m = 1 * n := two_mul_edges_eq G
  have hinj : Function.Injective G.left := by
    intro e f h
    exact G.left_unique e f h (Subsingleton.elim _ _)
  have hind : Independent G (Finset.univ.image G.left) := by
    intro e h
    obtain ⟨_, hr⟩ := h
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hr
    exact G.cross_unique f e hf (Subsingleton.elim _ _)
  have hcard : (Finset.univ.image G.left).card = m := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have h1 := halpha.1 _ hind
  omega

/-- Degree `1`: the optimum of `T_H` is `3 n`. -/
theorem opt_deg_one {n m alpha : ℕ} (G : PortGraph 1 n m)
    (halpha : IsIndependenceNumber G alpha) :
    alpha = m ∧ IsGreatest (Set.range (satCount G)) (3 * n) := by
  have ha := alpha_deg_one G halpha
  have h2 : 2 * m = 1 * n := two_mul_edges_eq G
  refine ⟨ha, ?_⟩
  have h := optimum_identity_proof G halpha
  have e : (1 + 1) * n + m + alpha = 3 * n := by omega
  rw [e] at h
  exact h

/-- Degree `2`: `m = n` and the optimum of `T_H` is `4 n + α`. -/
theorem opt_deg_two {n m alpha : ℕ} (G : PortGraph 2 n m)
    (halpha : IsIndependenceNumber G alpha) :
    m = n ∧ IsGreatest (Set.range (satCount G)) (4 * n + alpha) := by
  have h2 : 2 * m = 2 * n := two_mul_edges_eq G
  refine ⟨by omega, ?_⟩
  have h := optimum_identity_proof G halpha
  have e : (2 + 1) * n + m + alpha = 4 * n + alpha := by omega
  rw [e] at h
  exact h

end PalomaMax2SAT.RegularLemmas
