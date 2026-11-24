module

public import Mathlib

@[expose] public section

/-!
# Arithmetic lemmas for the strong bounded-degree barrier

Rational and division-free arithmetic behind item (2) of Theorem `thm:strong-ugc-broken`:
the lifted ratio `1 - (1 - α_ε)/18` and `1 - (1 - α_ε)/(6d + 12)` with `α_ε ≥ 0.8785`
exceed `0.9932`, the ratio `1 - (1 - α_ε)/(6d + 12)` tends to `1`, and a cut guarantee `p/q` on
a graph with `m` edges and maximum cut `mc` gives the lifted ratio
`1 - (1 - p/q)/(6d + 12)` on `T_{H(G)}` for a `d`-regular graph `G`.
-/

namespace PalomaMax2SAT.StrongLemmas

/-- `1 - (1 - a)/18 > 0.9932` for `a ≥ 0.8785`. -/
theorem lift_gt (a : ℚ) (ha : (8785 : ℚ) / 10000 ≤ a) :
    (9932 : ℚ) / 10000 < 1 - (1 - a) / 18 := by
  linarith

/-- `1 - (1 - a)/(6d + 12) > 0.9932` for `a ≥ 0.8785` and every `d ≥ 1`. -/
theorem regular_gt (a : ℚ) (ha : (8785 : ℚ) / 10000 ≤ a) (d : ℕ) (hd : 1 ≤ d) :
    (9932 : ℚ) / 10000 < 1 - (1 - a) / (6 * d + 12) := by
  have hd' : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℚ) < 6 * d + 12 := by positivity
  have h : (1 - a) / (6 * d + 12) < 68 / 10000 := by
    rw [div_lt_iff₀ hpos]
    linarith
  linarith

/-- `1 - (1 - a)/(6d + 12)` tends to `1`. -/
theorem tends_one (a : ℚ) (ha : (8785 : ℚ) / 10000 ≤ a) (ε : ℚ) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 1 - ε < 1 - (1 - a) / (6 * d + 12) := by
  obtain ⟨D, hD⟩ := exists_nat_gt (1 / ε)
  refine ⟨D, fun d hd => ?_⟩
  have hdq : (D : ℚ) ≤ d := by exact_mod_cast hd
  have h1 : 1 < ε * d := by
    have := mul_lt_mul_of_pos_left (lt_of_lt_of_le hD hdq) hε
    rwa [mul_one_div_cancel hε.ne'] at this
  have hpos : (0 : ℚ) < 6 * d + 12 := by positivity
  have h2 : (1 - a) / (6 * d + 12) < ε := by
    rw [div_lt_iff₀ hpos]
    nlinarith
  linarith

/-- A cut guarantee `p/q` (`p * mc ≤ q * cut`, `p ≤ q`) on a `d`-regular graph with `m` edges and
maximum cut `mc ≤ m` gives, for `B = m (6d + 10)`, `α = m + mc`, `s = m + cut`, the ratio
`(B + s)/(B + α) ≥ 1 - (1 - p/q)/(6d + 12)`, division-free. -/
theorem cut_lift_ratio (d m mc cut p q : ℕ) (hmc : mc ≤ m) (hpq : p ≤ q)
    (hcut : p * mc ≤ q * cut) :
    (6 * d + 12) * q * (m * (6 * d + 10) + (m + mc)) ≤
      (6 * d + 12) * q * (m * (6 * d + 10) + (m + cut)) +
        (q - p) * (m * (6 * d + 10) + (m + mc)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hpq
  rw [Nat.add_sub_cancel_left]
  have h1 : (6 * d + 12) * (p * mc) ≤ (6 * d + 12) * ((p + r) * cut) :=
    Nat.mul_le_mul_left _ hcut
  have h2 : r * (6 * d + 11) * mc ≤ r * (6 * d + 11) * m := Nat.mul_le_mul_left _ hmc
  nlinarith [h1, h2]

end PalomaMax2SAT.StrongLemmas
