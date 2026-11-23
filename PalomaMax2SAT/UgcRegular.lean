module

public import Mathlib
public import PalomaMax2SAT.DegreeFormula
public import PalomaMax2SAT.DegreeTransfer
public import PalomaMax2SAT.RegularLemmas

@[expose] public section

/-!
# Theorem `thm:all-degd`: the complete `d`-regular classification for all `d ≥ 1`

The formalized parts of the theorem, for the formula `T_H` of a `d`-regular port graph:

1. the optimum is `(d+1) n + m + α`, `2 m = d n` and `2 α ≤ n`;
2. every assignment is repaired to an independent set `R(z)` with `score ≤ (d+1) n + m + |R(z)|`;
3. the lift of an independent set `I` has value `(d+1) n + m + |I|`;
4. the all-true assignment has ratio `(3d+2)/(3d+3)` for every `d ≥ 1`, and `83/84` for
   `d ≥ 27`;
5. a `6/7`-approximate independent set lifts to `(21d+20)/(21d+21)` for every `d ≥ 1`;
6. the threshold transfer `27 α ≤ 28 |I| + d α` gives `83/84` for every `d ≥ 1`;
7. the Berman--Fujito transfer gives `83/84` for `d ≥ 22`, and the `ε = 1/c` form holds for
   every degree `e + 2`;
8. the two-branch transfer gives `83/84` for `d = 21`;
9. for `d = 1` the independence number is `m` and the optimum is `3 n`; for `d = 2` the
   optimum is `4 n + α`.

The polynomial running times, the exact computation of a maximum independent set on paths and
cycles, and the Berman--Fujito, Trevisan and Goemans--Williamson guarantees are not formalized.
-/

namespace PalomaMax2SAT.UgcRegular

theorem all_degd :
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 0 < d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G))
            ((d + 1) * n + m + alpha) ∧
          2 * m = d * n ∧ 2 * alpha ≤ n) ∧
    (∀ {d n m : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m)
        (z : Fin n → Fin (d + 1) → Bool),
      PalomaMax2SAT.DegreeFormula.Independent G
          (PalomaMax2SAT.DegreeFormula.repairedSet G z) ∧
        PalomaMax2SAT.DegreeFormula.score G z ≤
          (d + 1) * n + m + (PalomaMax2SAT.DegreeFormula.repairedSet G z).card) ∧
    (∀ {d n m : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m) (I : Finset (Fin n)),
      PalomaMax2SAT.DegreeFormula.Independent G I →
        PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
              Fin n → Fin (d + 1) → Bool) = (d + 1) * n + m + I.card) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 0 < d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        (3 * d + 2) * ((d + 1) * n + m + alpha) ≤
          (3 * d + 3) * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent (∅ : Finset (Fin n)) :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 27 ≤ d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        83 * ((d + 1) * n + m + alpha) ≤
          84 * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent (∅ : Finset (Fin n)) :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 0 < d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I → 6 * alpha ≤ 7 * I.card →
        (21 * d + 20) * ((d + 1) * n + m + alpha) ≤
          (21 * d + 21) * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 0 < d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I → 27 * alpha ≤ 28 * I.card + d * alpha →
        83 * ((d + 1) * n + m + alpha) ≤
          84 * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 22 ≤ d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I → 5 * alpha ≤ (d + 3) * I.card →
        83 * ((d + 1) * n + m + alpha) ≤
          84 * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 21 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I →
        (200 * alpha ≤ 99 * n → 50 * alpha ≤ 241 * I.card) →
        (99 * n < 200 * alpha → 3 * n ≤ 25 * I.card) →
          83 * ((21 + 1) * n + m + alpha) ≤
            84 * PalomaMax2SAT.DegreeFormula.satCount G
              (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
                Fin n → Fin (21 + 1) → Bool)) ∧
    (∀ {e n m alpha c : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph (e + 2) n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I →
        5 * c * alpha ≤ (((e + 2) + 3) * c + 1) * I.card →
          (3 * (e + 2) + 3) * (((e + 2) + 3) * c + 1) * ((e + 2 + 1) * n + m + alpha) ≤
            (3 * (e + 2) + 3) * (((e + 2) + 3) * c + 1) *
                PalomaMax2SAT.DegreeFormula.satCount G
                  (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
                    Fin n → Fin (e + 2 + 1) → Bool) +
              (e * c + 1) * ((e + 2 + 1) * n + m + alpha)) ∧
    (∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 1 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        alpha = m ∧
          IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G)) (3 * n)) ∧
    (∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 2 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        m = n ∧
          IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G)) (4 * n + alpha)) :=
  ⟨fun G hd ha => ⟨PalomaMax2SAT.DegreeFormula.optimum_identity_proof G ha,
      PalomaMax2SAT.DegreeFormula.two_mul_edges_eq G,
      PalomaMax2SAT.DegreeFormula.independence_number_le_half G hd ha⟩,
    fun G z => ⟨PalomaMax2SAT.DegreeFormula.repairedSet_independent_proof G z,
      PalomaMax2SAT.DegreeFormula.repairedSet_card_lower_bound_proof G z⟩,
    fun G I hI => PalomaMax2SAT.DegreeFormula.lift_satCount G I hI,
    fun G hd ha => PalomaMax2SAT.DegreeFormula.baseline_ratio G hd ha,
    fun G hd ha => PalomaMax2SAT.DegreeFormula.baseline_ratio_83_84 G hd ha,
    fun G hd ha I hI hs => PalomaMax2SAT.DegreeFormula.lift_ratio_from_mis G hd ha I hI hs,
    fun G hd ha I hI hs => PalomaMax2SAT.DegreeFormula.lift_ratio_threshold G hd ha I hI hs,
    fun G hd ha I hI hs => PalomaMax2SAT.DegreeFormula.lift_ratio_bf G hd ha I hI hs,
    fun G ha I hI h1 h2 => PalomaMax2SAT.DegreeFormula.lift_ratio_degree_21 G ha I hI h1 h2,
    fun G ha I hI hs => PalomaMax2SAT.DegreeFormula.lift_ratio_bf_general G ha I hI hs,
    fun G ha => PalomaMax2SAT.RegularLemmas.opt_deg_one G ha,
    fun G ha => PalomaMax2SAT.RegularLemmas.opt_deg_two G ha⟩

end PalomaMax2SAT.UgcRegular
