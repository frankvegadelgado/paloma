module

public import Mathlib
public import PalomaMax2SAT.DegreeFormula
public import PalomaMax2SAT.CutTransfer

@[expose] public section

/-!
# Published results used as explicit hypotheses

Some steps of the paper rest on published theorems whose proofs (semidefinite
programming, randomized rounding, the Unique Games Conjecture) are not formalized here.
This module states exactly what the paper uses from them, as hypotheses with references,
and proves everything that follows from them.

* `CutGuarantee`: the cut produced by the Goemans--Williamson semidefinite rounding
  [Goemans and Williamson, J. ACM 42 (1995)], derandomized by the method of conditional
  expectations of Mahajan and Ramesh [SIAM J. Comput. 28 (1999)]. The paper uses it on
  `21`-regular graphs with `α > 99n/200`: such a graph has a cut of `≥ 99%` of the edges, so
  the semidefinite value is `≥ 0.989`, and rounding gives a cut of `≥ 93%` of the edges.
  Lean states the existence of that cut; the polynomial running time and the rounding
  analysis are in the references.
* `BFGuarantee`: a Berman--Fujito independent set of size `≥ 50α/241` on `21`-regular
  graphs [Berman and Fujito, 1999]; again only existence is stated.

* `GWCut`, `GammaCut`, `BoundedCut`: the cut guarantees of the MAX-CUT part of the paper,
  stated for a given cut of `k` edges in a graph of maximum cut `c` and `m` edges.
  `GWCut` is `cut ≥ 0.8785 · maxcut` (Goemans--Williamson, with the semidefinite error
  `10⁻⁵`; Mahajan--Ramesh derandomization). `GammaCut` is `maxcut - cut ≤ 0.1053 m`, which
  follows from the Goemans--Williamson analysis through the convex envelope of
  `arccos(1 - 2x)/π` and the numerical maximum `0.10526` of `γ - h(γ)` computed in the
  paper. `BoundedCut p q` is `(p/q) · maxcut ≤ cut`, the guarantee `c_d = p/q` on graphs of
  maximum degree `d`: Feige--Karpinski--Langberg, J. Algorithms 43 (2002) 201--219;
  Halperin--Livnat--Zwick, J. Algorithms 53 (2004) 169--185 (an *expected* ratio `0.9326`
  for maximum degree `3`); Hsieh--Kothari, ICALP 2023, arXiv:2206.09204. For a randomized
  algorithm these are statements about the expected cut.

The Unique Games Conjecture, the threshold `α_GW ≈ 0.87856` for MAX-CUT
(Khot--Kindler--Mossel--O'Donnell, SIAM J. Comput. 37 (2007) 319--357), and the hardness thresholds `0.94615981` and `0.94016567`
(Brakensiek--Huang--Zwick; Lewin--Livnat--Zwick) are statements about all instances of
MAX-HORN-SAT / MAX 2-SAT and are not used by any Lean statement; they appear only in the
documentation (`doc/formalization.md`).
-/

namespace PalomaMax2SAT.CitedResults

open PalomaMax2SAT.DegreeFormula

/-- Edges with both endpoints in `A`. -/
def sideEdges {d n m : ℕ} (G : PortGraph d n m) (A : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun e => G.left e ∈ A ∧ G.right e ∈ A

/-- Deleting the left endpoint of every edge inside `A` leaves an independent set. -/
theorem side_independent {d n m : ℕ} (G : PortGraph d n m) (A : Finset (Fin n)) :
    Independent G (A \ (sideEdges G A).image G.left) := by
  intro e he
  rcases he with ⟨hl, hr⟩
  have hlA : G.left e ∈ A := (Finset.mem_sdiff.mp hl).1
  have hrA : G.right e ∈ A := (Finset.mem_sdiff.mp hr).1
  exact (Finset.mem_sdiff.mp hl).2
    (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlA, hrA⟩, rfl⟩)

theorem side_card {d n m : ℕ} (G : PortGraph d n m) (A : Finset (Fin n)) :
    A.card ≤ (A \ (sideEdges G A).image G.left).card + (sideEdges G A).card := by
  have h1 := Finset.card_le_card_sdiff_add_card (s := A) (t := (sideEdges G A).image G.left)
  have h2 : ((sideEdges G A).image G.left).card ≤ (sideEdges G A).card :=
    Finset.card_image_le
  omega

/-- From a cut `(A, Aᶜ)` with `u` uncut edges one obtains an independent set `I` with
`n ≤ 2|I| + u`. -/
theorem independent_from_cut {d n m : ℕ} (G : PortGraph d n m) (A : Finset (Fin n)) :
    ∃ I : Finset (Fin n), Independent G I ∧
      n ≤ 2 * I.card + ((sideEdges G A).card + (sideEdges G Aᶜ).card) := by
  have hA := side_card G A
  have hB := side_card G Aᶜ
  have h1 := Finset.card_compl A
  have h2 := Finset.card_le_univ A
  simp only [Fintype.card_fin] at h1 h2
  by_cases h : (A \ (sideEdges G A).image G.left).card ≥
      (Aᶜ \ (sideEdges G Aᶜ).image G.left).card
  · exact ⟨_, side_independent G A, by omega⟩
  · exact ⟨_, side_independent G Aᶜ, by omega⟩

/-- Cited: Goemans--Williamson rounding with derandomization (Mahajan--Ramesh). On a graph
with independence number `α > 99n/200` the rounding returns a cut with at most `7m/100`
uncut edges. Lean states only the existence of the cut. -/
def CutGuarantee {d n m : ℕ} (G : PortGraph d n m) (alpha : ℕ) : Prop :=
  99 * n < 200 * alpha →
    ∃ A : Finset (Fin n), 100 * ((sideEdges G A).card + (sideEdges G Aᶜ).card) ≤ 7 * m

/-- Cited: Berman--Fujito. On a graph of degree `21` there is an independent set `I`
with `50α ≤ 241|I|`. Lean states only the existence of the set. -/
def BFGuarantee {d n m : ℕ} (G : PortGraph d n m) (alpha : ℕ) : Prop :=
  ∃ I : Finset (Fin n), Independent G I ∧ 50 * alpha ≤ 241 * I.card

/-- The cut guarantee yields an independent set with `3n ≤ 25|I|` on `21`-regular graphs. -/
theorem independent_from_cut_guarantee {n m alpha : ℕ} (G : PortGraph 21 n m)
    (hcut : CutGuarantee G alpha) (hgt : 99 * n < 200 * alpha) :
    ∃ I : Finset (Fin n), Independent G I ∧ 3 * n ≤ 25 * I.card := by
  obtain ⟨A, hA⟩ := hcut hgt
  obtain ⟨I, hI, hn⟩ := independent_from_cut G A
  have hm := two_mul_edges_eq G
  exact ⟨I, hI, by omega⟩

/-- Degree `21`, end to end: given the two cited guarantees there is an independent set
whose lift satisfies at least `83/84` of the optimum `(21+1)n + m + α` of `T_H`. -/
theorem degree_21_end_to_end {n m alpha : ℕ} (G : PortGraph 21 n m)
    (halpha : IsIndependenceNumber G alpha)
    (hbf : BFGuarantee G alpha) (hcut : CutGuarantee G alpha) :
    ∃ I : Finset (Fin n), Independent G I ∧
      83 * ((21 + 1) * n + m + alpha) ≤
        84 * satCount G (assignmentOfIndependent I : Fin n → Fin (21 + 1) → Bool) := by
  by_cases h : 200 * alpha ≤ 99 * n
  · obtain ⟨I, hI, hs⟩ := hbf
    exact ⟨I, hI, lift_ratio_degree_21 G halpha I hI (fun _ => hs)
      (fun h' => absurd h (by omega))⟩
  · have h' : 99 * n < 200 * alpha := by omega
    obtain ⟨I, hI, hs⟩ := independent_from_cut_guarantee G hcut h'
    exact ⟨I, hI, lift_ratio_degree_21 G halpha I hI (fun h'' => absurd h'' h)
      (fun _ => hs)⟩

/-! ### Cut guarantees of the MAX-CUT part -/

/-- Cited: Goemans--Williamson cut, `0.8785 · maxcut ≤ cut`. -/
def GWCut (c k : ℕ) : Prop := 8785 * c ≤ 10000 * k

/-- Cited/computed: `maxcut - cut ≤ 0.1053 m` (convex-envelope form of the
Goemans--Williamson analysis). -/
def GammaCut (m c k : ℕ) : Prop := 10000 * c ≤ 10000 * k + 1053 * m

/-- Cited: a cut guarantee `p/q` on graphs of bounded degree (Feige--Karpinski--Langberg,
Halperin--Livnat--Zwick, Hsieh--Kothari). -/
def BoundedCut (p q c k : ℕ) : Prop := p * c ≤ q * k

/-- A Goemans--Williamson cut gives the independent set of Theorem `thm:cutclass`:
`18785 α ≤ 20000 |I|` with `α = m + maxcut` and `|I| = m + cut`. -/
theorem independent_of_GWCut {m c k : ℕ} (hc : c ≤ m) (h : GWCut c k) :
    18785 * (m + c) ≤ 20000 * (m + k) :=
  PalomaMax2SAT.CutTransfer.independent_ratio_from_cut m c k hc h

/-- A bounded-degree guarantee `p/q = 1 - a/q` (`q = p + a`) in the form needed below:
with `c = k + g`, `2 q g ≤ a (m + c)`. -/
theorem gap_of_BoundedCut {p a k g m : ℕ} (hcut : BoundedCut p (p + a) (k + g) k)
    (hc : k + g ≤ m) : 2 * (p + a) * g ≤ a * (m + (k + g)) := by
  unfold BoundedCut at hcut
  nlinarith [Nat.mul_le_mul_left a hc]

/-- Proposition `prop:bounded-cut`, division-free: the loss `g = maxcut - cut` satisfies
`2 q (3d+6) g ≤ a (B + m + maxcut)` with `B + m = (6d+11) m`, i.e. the lift of the cut has
ratio at least `1 - (1 - p/q)/(6d + 12)` with `a = q - p`. -/
theorem bounded_cut_ratio {d q a m c g : ℕ} (hg : 2 * q * g ≤ a * (m + c)) (hc : c ≤ m) :
    2 * q * (3 * d + 6) * g ≤ a * ((6 * d + 11) * m + c) := by
  have h1 : (3 * d + 6) * (2 * q * g) ≤ (3 * d + 6) * (a * (m + c)) :=
    Nat.mul_le_mul_left _ hg
  have h2 : (3 * d + 6) * (a * (m + c)) ≤ a * ((6 * d + 11) * m + c) := by
    nlinarith [Nat.mul_le_mul_left (a * (3 * d + 5)) hc]
  calc 2 * q * (3 * d + 6) * g = (3 * d + 6) * (2 * q * g) := by ring
    _ ≤ a * ((6 * d + 11) * m + c) := h1.trans h2

end PalomaMax2SAT.CitedResults
