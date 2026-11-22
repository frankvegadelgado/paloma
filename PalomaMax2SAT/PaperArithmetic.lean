module

public import Mathlib

@[expose] public section

/-!
# Numerical statements of the paper

Division-free or rational arithmetic behind the statements of `paper.tex` that are not part of
another module: the comparison of `83/84` with the Unique Games thresholds (Theorem
`thm:ugc-class`), the two-branch arithmetic of Theorem `thm:ratio`, the numerical constants of
Theorem `thm:cutclass`, Theorem `thm:nonreg-cutclass` and Proposition `prop:bounded-cut`, the
supremum in Remark `rem:gamma-linear`, and the tables.
The Goemans--Williamson, Berman--Fujito and Trevisan guarantees enter only as hypotheses.
-/

namespace PalomaMax2SAT.PaperArithmetic

/-- Theorem `thm:ugc-class`: `83/84 > 0.94615981 > 0.94016567`. -/
theorem ugc_thresholds :
    (94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
      (94615981 : ℚ) / 100000000 < 83 / 84 := by
  constructor <;> norm_num

/-- `(3d+2)/(3d+3) > 0.95` for `d ≥ 6` (Section on larger degree). -/
theorem baseline_above_095 (d : ℕ) (hd : 6 ≤ d) : 19 * (3 * d + 3) < 20 * (3 * d + 2) := by
  omega

/-- `r(d) = (21d+20)/(21d+21)` is strictly increasing: `r(d) < r(d+1)`, division-free. -/
theorem endpoint_increasing (d : ℕ) :
    (21 * d + 20) * (21 * d + 42) < (21 * d + 41) * (21 * d + 21) := by
  have h : (21 * d + 41) * (21 * d + 21) = (21 * d + 20) * (21 * d + 42) + 21 := by ring
  omega

/-- `r(3) = 83/84`. -/
theorem endpoint_at_three : (21 * 3 + 20) * 84 = 83 * (21 * 3 + 21) := by norm_num

/-- Theorem `thm:cutclass`: `1 - α_ε ≤ 0.1215` gives a loss `(1 - α_ε)/(6d+12) < 1/84`. -/
theorem cutclass_loss_lt (d : ℕ) : 1215 * 84 < 10000 * (6 * d + 12) := by omega

/-- Theorem `thm:nonreg-cutclass`: `(1 - α_ε)/18 < 0.0068`, so the ratio exceeds `0.9932`. -/
theorem nonreg_constant : 1215 * 10000 < 68 * 180000 := by norm_num

/-- Proposition `prop:bounded-cut` with `c_3 = 0.9326`: the ratio exceeds `0.9977`. -/
theorem bounded_cut_cubic :
    (9977 : ℚ) / 10000 < 1 - (1 - 9326 / 10000) / (6 * 3 + 12) := by norm_num

/-- Remark `rem:gamma-linear`: `γ/(K+γ) ≤ 1/(K+1)` for `0 ≤ γ ≤ 1`, so the supremum of
`(1-α_ε)γ/(6d+11+γ)` over `γ ≤ 1` is `(1-α_ε)/(6d+12)` (take `K = 6d+11`). -/
theorem gamma_over_sum_le (K γ : ℚ) (hK : 0 < K) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    γ / (K + γ) ≤ 1 / (K + 1) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hK.le]

/-- Theorem `thm:ratio`, arithmetic of the two branches on the cubic formula `T_H`
(`B = 4n + m`, `2m = 3n`): the Berman--Fujito branch is assumed to return `s` with
`5999993 α ≤ 7000000 s` when `20000 α ≤ 9999 n`, and the near-bipartite branch `37 n ≤ 80 s`
otherwise. Lean does not prove that either algorithm attains its guarantee. -/
theorem ratio_83_84_two_branch (n m a s : ℕ)
    (hm : 2 * m = 3 * n) (hn : 2 * a ≤ n)
    (hBF : 20000 * a ≤ 9999 * n → 5999993 * a ≤ 7000000 * s)
    (hNB : 9999 * n < 20000 * a → 37 * n ≤ 80 * s) :
    84 * (4 * n + m + s) ≥ 83 * (4 * n + m + a) := by
  by_cases h : 20000 * a ≤ 9999 * n
  · have := hBF h
    omega
  · have := hNB (by omega)
    omega

/-- Table of `1 - (d-2)/(3(d+1)(d+3))` for `d = 4, 5, 6, 20`. -/
theorem bf_limit_table :
    (1 : ℚ) - 2 / (3 * 5 * 7) = 103 / 105 ∧ (1 : ℚ) - 3 / (3 * 6 * 8) = 47 / 48 ∧
      (1 : ℚ) - 4 / (3 * 7 * 9) = 185 / 189 ∧ (1 : ℚ) - 18 / (3 * 21 * 23) = 159 / 161 := by
  norm_num

/-- Table of `(3d+2)/(3d+3)` for `d = 4, 5, 6, 20`. -/
theorem baseline_table :
    (3 * 4 + 2 : ℚ) / (3 * 4 + 3) = 14 / 15 ∧ (3 * 5 + 2 : ℚ) / (3 * 5 + 3) = 17 / 18 ∧
      (3 * 6 + 2 : ℚ) / (3 * 6 + 3) = 20 / 21 ∧ (3 * 20 + 2 : ℚ) / (3 * 20 + 3) = 62 / 63 := by
  norm_num

/-- Remark `rem:cutclass-range`: the ratios `104/105` and `440/441`, the constant `B + m = 29 m`
for `D = 4`, and the cut `49 m / 105` recovered when `maxcut = 3m/4`. -/
theorem cutclass_range_example :
    (21 * 4 + 20 : ℚ) / (21 * 4 + 21) = 104 / 105 ∧
      (21 * 20 + 20 : ℚ) / (21 * 20 + 21) = 440 / 441 ∧
      (6 * 4 + 5 : ℚ) = 29 ∧ (104 / 105 : ℚ) * (3 / 4) - 29 / 105 = 49 / 105 := by
  norm_num

end PalomaMax2SAT.PaperArithmetic
