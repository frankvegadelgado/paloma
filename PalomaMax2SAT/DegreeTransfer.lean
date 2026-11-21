module

public import Mathlib

@[expose] public section

namespace PalomaMax2SAT.DegreeTransfer

/-- Degree-`d` baseline: with `2m = d n` and `2α ≤ n`, the lift of the empty
independent set, of value `(d+1) n + m`, is a `(3d+2)/(3d+3)` approximation. -/
theorem baseline_degree_d_proof (d n m a : ℕ) (hm : 2 * m = d * n) (hn : 2 * a ≤ n) :
    (3 * d + 2) * ((d + 1) * n + m + a) ≤ (3 * d + 3) * ((d + 1) * n + m) := by
  have h1 : (3 * d + 2) * (2 * a) ≤ (3 * d + 2) * n := Nat.mul_le_mul_left _ hn
  have h2 : 2 * ((d + 1) * n + m) = (3 * d + 2) * n := by nlinarith [hm]
  nlinarith [h1, h2]

/-- For `d ≥ 27` the empty independent set already gives the ratio `83/84`. -/
theorem baseline_exceeds_83_84_proof (d n m a : ℕ) (hd : 27 ≤ d)
    (hm : 2 * m = d * n) (hn : 2 * a ≤ n) :
    83 * ((d + 1) * n + m + a) ≤ 84 * ((d + 1) * n + m) := by
  have h1 : (3 * d + 2) * (2 * a) ≤ (3 * d + 2) * n := Nat.mul_le_mul_left _ hn
  have h2 : 2 * ((d + 1) * n + m) = (3 * d + 2) * n := by nlinarith [hm]
  have h4 : 27 * a ≤ d * a := Nat.mul_le_mul_right a hd
  nlinarith [h1, h2, h4]

/-- Arithmetic transfer of a `6/7` independent-set guarantee to the degree-`d`
ratio `(21d+20)/(21d+21)`. Lean does not prove that an algorithm attains the
guarantee. -/
theorem ratio_degree_d_from_mis_proof (d n m a s : ℕ) (hm : 2 * m = d * n)
    (hn : 2 * a ≤ n) (hs : 6 * a ≤ 7 * s) :
    (21 * d + 20) * ((d + 1) * n + m + a) ≤
      (21 * d + 21) * ((d + 1) * n + m + s) := by
  have h1 : (3 * d + 2) * (2 * a) ≤ (3 * d + 2) * n := Nat.mul_le_mul_left _ hn
  have h2 : 2 * ((d + 1) * n + m) = (3 * d + 2) * n := by nlinarith [hm]
  have h3 : (3 * d + 3) * (6 * a) ≤ (3 * d + 3) * (7 * s) := Nat.mul_le_mul_left _ hs
  nlinarith [h1, h2, h3]

/-- Berman--Fujito `(d+3)/5` transfer: for `d ≥ 22`, an independent set with
`5α ≤ (d+3)|I|` lifts to the ratio `83/84` on the `d`-regular family. Lean does
not prove that an algorithm attains the guarantee. -/
theorem bf_degree_d_proof (d n m a s : ℕ) (hd : 22 ≤ d) (hm : 2 * m = d * n)
    (hn : 2 * a ≤ n) (hs : 5 * a ≤ (d + 3) * s) :
    83 * ((d + 1) * n + m + a) ≤ 84 * ((d + 1) * n + m + s) := by
  have h2 : 2 * ((d + 1) * n + m) = (3 * d + 2) * n := by nlinarith [hm]
  have h1 : (d + 3) * (3 * d + 2) * (2 * a) ≤ (d + 3) * (3 * d + 2) * n :=
    Nat.mul_le_mul_left _ hn
  have h5 : 84 * (5 * a) ≤ 84 * ((d + 3) * s) := Nat.mul_le_mul_left _ hs
  have hq : 72 * d ≤ 3 * d * d + 177 := by nlinarith [hd]
  have hq' : (72 * d) * a ≤ (3 * d * d + 177) * a := Nat.mul_le_mul_right a hq
  have hB : (d + 3) * (2 * ((d + 1) * n + m)) = (d + 3) * ((3 * d + 2) * n) := by
    rw [h2]
  have key : (d + 3) * (83 * ((d + 1) * n + m + a)) ≤
      (d + 3) * (84 * ((d + 1) * n + m + s)) := by
    nlinarith [h1, h5, hq', hB]
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-- Degree `21`: if `α ≤ 99n/200` a Berman--Fujito set with `50α ≤ 241|I|` suffices,
and if `α > 99n/200` a cut-rounding set with `3n ≤ 25|I|` suffices; either lifts to
the ratio `83/84`. Lean does not prove that an algorithm attains either guarantee. -/
theorem two_branch_degree_21_proof (n m a s : ℕ) (hm : 2 * m = 21 * n) (hn : 2 * a ≤ n)
    (hbf : 200 * a ≤ 99 * n → 50 * a ≤ 241 * s)
    (hcut : 99 * n < 200 * a → 3 * n ≤ 25 * s) :
    83 * (22 * n + m + a) ≤ 84 * (22 * n + m + s) := by
  by_cases h : 200 * a ≤ 99 * n
  · have h1 := hbf h
    omega
  · have h2 : 99 * n < 200 * a := by omega
    have h3 := hcut h2
    omega

/-- Threshold form of the degree-`d` transfer: an independent set `I` with
`28|I| + dα ≥ 27α`, that is `|I| ≥ ((27-d)/28) α`, lifts to the ratio `83/84` on
the `d`-regular family. Lean does not prove that an algorithm attains the
guarantee. This statement concerns the bounded-degree class only; the
Unique-Games thresholds quantify over all instances and are not touched by it. -/
theorem threshold_degree_d_proof (d n m a s : ℕ) (hm : 2 * m = d * n) (hn : 2 * a ≤ n)
    (hs : 27 * a ≤ 28 * s + d * a) :
    83 * ((d + 1) * n + m + a) ≤ 84 * ((d + 1) * n + m + s) := by
  have h2 : 2 * ((d + 1) * n + m) = (3 * d + 2) * n := by nlinarith [hm]
  have h1 : (3 * d + 2) * (2 * a) ≤ (3 * d + 2) * n := Nat.mul_le_mul_left _ hn
  nlinarith [h1, h2, hs]

/-- Degree `21`, Berman--Fujito branch: if `α ≤ 99n/200` and `50α ≤ 241|I|`, the lift
has ratio `83/84`. Lean does not prove that an algorithm attains the guarantee. -/
theorem bf_branch_degree_21 (n m a s : ℕ) (hm : 2 * m = 21 * n) (hn : 2 * a ≤ n)
    (hle : 200 * a ≤ 99 * n) (hbf : 50 * a ≤ 241 * s) :
    83 * (22 * n + m + a) ≤ 84 * (22 * n + m + s) := by
  omega

/-- The numerical comparison `(15803/241)·(99/200) < 65/2` used in the degree-`21`
Berman--Fujito branch, where `B = (65/2) n`. -/
theorem bf_branch_numeric_21 : (15803 : ℚ) / 241 * (99 / 200) < 65 / 2 := by
  norm_num

/-- Degree `21`, cut branch: if `α > 99n/200` and `3n ≤ 25|I|`, the lift has ratio
`83/84`. Lean does not prove that an algorithm attains the guarantee. -/
theorem cut_branch_degree_21 (n m a s : ℕ) (hm : 2 * m = 21 * n) (hn : 2 * a ≤ n)
    (hgt : 99 * n < 200 * a) (hcut : 3 * n ≤ 25 * s) :
    83 * (22 * n + m + a) ≤ 84 * (22 * n + m + s) := by
  omega

/-- Degree `21`: when `α > 99n/200`, an independent set of size `α` cuts `21α` edges,
and `21α · 100 > 99 m`, i.e. more than `99%` of the `m` edges. -/
theorem cut_fraction_degree_21 (n m a : ℕ) (hm : 2 * m = 21 * n) (hgt : 99 * n < 200 * a) :
    99 * m < 100 * (21 * a) := by
  omega

/-- Degree `21`: if at most `7m/100` edges are uncut and one side loses one endpoint of
every uncut edge, the remaining independent set `I` satisfies `3n ≤ 25|I|`. Here `u`
is the number of uncut edges and `n ≤ 2s + u` says the larger side after deletion has
at least `(n - u)/2` vertices. -/
theorem cut_to_independent_degree_21 (n m u s : ℕ) (hm : 2 * m = 21 * n)
    (hu : 100 * u ≤ 7 * m) (hs : n ≤ 2 * s + u) : 3 * n ≤ 25 * s := by
  omega

/-- The values of the threshold `ρ(d) = (27 - d)/28` listed in the text. -/
theorem threshold_table :
    ((27 : ℚ) - 3) / 28 = 6 / 7 ∧ ((27 : ℚ) - 4) / 28 = 23 / 28 ∧
    ((27 : ℚ) - 5) / 28 = 11 / 14 ∧ ((27 : ℚ) - 6) / 28 = 3 / 4 ∧
    ((27 : ℚ) - 8) / 28 = 19 / 28 ∧ ((27 : ℚ) - 10) / 28 = 17 / 28 ∧
    ((27 : ℚ) - 12) / 28 = 15 / 28 ∧ ((27 : ℚ) - 16) / 28 = 11 / 28 := by
  norm_num

/-- The values of the endpoint ratio `(21d+20)/(21d+21)` listed in the text. -/
theorem endpoint_ratio_table :
    (21 * (3 : ℚ) + 20) / (21 * 3 + 21) = 83 / 84 ∧
    (21 * (4 : ℚ) + 20) / (21 * 4 + 21) = 104 / 105 ∧
    (21 * (5 : ℚ) + 20) / (21 * 5 + 21) = 125 / 126 ∧
    (21 * (6 : ℚ) + 20) / (21 * 6 + 21) = 146 / 147 ∧
    (21 * (8 : ℚ) + 20) / (21 * 8 + 21) = 188 / 189 ∧
    (21 * (10 : ℚ) + 20) / (21 * 10 + 21) = 230 / 231 ∧
    (21 * (12 : ℚ) + 20) / (21 * 12 + 21) = 272 / 273 := by
  norm_num

end PalomaMax2SAT.DegreeTransfer
