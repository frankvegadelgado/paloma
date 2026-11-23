# Formalization notes

This document states what the Lean development proves, what it takes from the
literature as explicit hypotheses, and what it does not touch.

## Main result: ratio above the Unique Games thresholds

Theorem `thm:ugc-class` of the paper: on the class `{T_{H(G)}}` of three-occurrence Horn formulas obtained from MAX-CUT instances, the polynomial-time factor `83/84` exceeds the Unique Games thresholds `0.94615981` (Brakensiek, Huang, Zwick) and `0.94016567` (Lewin, Livnat, Zwick), which hold for all instances. The main theorem in Lean for graphs of bounded degree is `PalomaMax2SAT.UgcBounded.ugc_bounded`: thresholds and `83/84 < 0.9932`; `selSet` and `alpha(H(G)) = m + maxcut(G)`; maximum degree at most `d+1` of `H(G)` when `G` has maximum degree at most `d`; the degree sum `4m + 2 sum deg(v)^2` of `H(G)`; the arithmetic `9932 (B+alpha) <= 10000 (B+|I|)` from `B >= 8 alpha`; and, for the formula `T_H` of every port-labelled graph with degrees `d_v` (`GeneralDegreeFormula`), `sum d_v = 2m`, `OPT = sum (d_v+1) + m + alpha` and the value of the lift of an independent set. The identification of `T_{H(G)}` with a port-labelled graph is not formalized. The regular-graph counterpart is `PalomaMax2SAT.UgcClass.ugc_class`, a conjunction of: `83/84 > 0.94615981 > 0.94016567`; the independent set `selSet` of the conflict graph has size `m + cut(S)`; `alpha(H(G)) = m + maxcut(G)`; `H(G)` is `(d+1)`-regular with `4m` vertices; `8785 c <= 10000 cut` implies `18785 (m+c) <= 20000 (m+cut)`; and the lift of an independent set `I` with `18785 alpha <= 20000 |I|` satisfies at least `83/84` of the optimum of `T_H`, for every degree `D >= 1`. Lean proves the arithmetic of the lift (`CutLift`, `CutTransfer`, `CitedResults`); the Goemans-Williamson cut guarantee and the thresholds are the cited hypotheses listed below.

## Prove2.me and toolchain

The development builds with Lean `v4.35.0-rc2` and the Mathlib tag `v4.35.0-rc2`, as the Palomar comparator requires. The Prove2.me submissions (`ugc_broken`, `ugc_class`, `ugc_bounded`, `all_degd`) are generated in their own branches on Lean `v4.33.1`, together with the tools `prove2me/generate.py` and `prove2me/upload.py`; the generated files carry no `module` header, so none of these files is part of `main`, which Palomar checks.

## Proved in Lean

* `CubicThreeOccurrence`, `SemanticHorn` (degree 3) and `DegreeFormula` (every degree `d`):
  the formula `T_H` as an explicit list of clauses with at most one negative literal (`IsDualHorn`),
  the complement-variable translation to standard Horn clauses with at most one positive literal
  (`IsHorn`, `Clause.compl`; `formula_horn`, `complement_satisfied`), the number of satisfied clauses,
  the exact optimum `(d+1)n + m + alpha`, `2m = dn`, `2 alpha <= n`, and that every variable
  occurs exactly three times.
* `DegreeTransfer`: the arithmetic of Proposition 3 (baseline, `d >= 27`, Berman--Fujito for
  `d >= 22`, the `6/7` set, the threshold `(27-d)/28`, and the two branches at `d = 21`).
* `DegreeFormula`: the same arithmetic stated about `T_H` itself, through the value
  `(d+1)n + m + |I|` of the lift of an independent set `I`.
* `CitedResults`: the combinatorial step from a cut with at most `7m/100` uncut edges to an
  independent set with `3n <= 25|I|`, and the end-to-end degree-21 statement.

* `CutTransfer`: the number of clauses of `F_G` satisfied by an assignment equals `m + cut(S)`, and the arithmetic of the ratio transfer from `F_G` and from `T_H` to the cut (Corollary `cor:cutratio`). The conflict-graph identity `alpha(H) = m + maxcut(G)` is proved in `ConflictGraph`.



* `CitedResults` (MAX-CUT part): `GWCut` and `BoundedCut` state the cited cut guarantees as numerical hypotheses; `independent_of_GWCut`, `gap_of_BoundedCut` and `bounded_cut_ratio` prove what follows (Theorem `thm:cutclass` step and Proposition `prop:bounded-cut`, division-free).


* `ConflictGraph`: the literal occurrences of `F_G` are `Fin m x Bool x Bool` (edge, sign of the clause, endpoint); two are adjacent when distinct and in the same clause, or on the same variable with opposite signs. `alpha_eq` proves that the independence number is `m + maxcut(G)` for every graph given by its edge list: `selSet` turns a vertex set `S` into an independent set of size `m + cut(S)` (`card_selSet`, `selSet_independent`) and `cutOf` turns an independent set `I` into a set `S` with `|I| <= m + cut(S)` (`card_le_edgeValues`).
* `ConflictDegree`: the neighbours of `(e, s, b)` are its partner in the clause and the opposite-sign occurrences of the same variable (`nbrs_eq`, `card_nbrs`); hence `(d+1)`-regularity (`card_nbrs_regular`), `2 deg(v)` occurrences per variable (`occurrences_eq`), `4m` vertices (`card_occ`).
* `LReduction`: `exists_large_independent` (greedy bound), `opt_le_const` (first constant for degree `d`), `cubic_opt_le` (`OPT <= 23 alpha`), `repair_le` and `repair_abs_le` (second constant `1`). The APX-completeness of cubic MIS is cited.
* `GeneralDegreeFormula`: `T_H` for a per-vertex degree function (`GPortGraph`, `sum_deg_eq`, `constant_eq`, `satCount_eq_score`, `score_le`, `optimum_identity`, `lift_satCount`).
* `UgcBounded`: the theorem `ugc_bounded` (Theorem `thm:ugc-class`, bounded degree), combining `PaperArithmetic.ugc_thresholds`, the conflict-graph lemmas, `sum_nbrs`, `edges_ge`, `ratio_nonregular` and the `GeneralDegreeFormula` identities.
* `RegularLemmas`: for a `1`-regular port graph `α = m` and the optimum of `T_H` is `3 n`; for a `2`-regular port graph `m = n` and the optimum is `4 n + α`.
* `UgcRegular`: the theorem `all_degd` (Theorem `thm:all-degd`), combining `DegreeFormula.optimum_identity_proof`, `two_mul_edges_eq`, `independence_number_le_half`, `repairedSet_independent_proof`, `repairedSet_card_lower_bound_proof`, `lift_satCount`, `baseline_ratio`, `baseline_ratio_83_84`, `lift_ratio_from_mis`, `lift_ratio_threshold`, `lift_ratio_bf`, `lift_ratio_degree_21`, `lift_ratio_bf_general` and `RegularLemmas.opt_deg_one`, `opt_deg_two`. The independent-set guarantees are hypotheses; the polynomial running times and the exact computation of a maximum independent set on paths and cycles are not formalized.
* `UgcClass`: the main theorem `ugc_class` (Theorem `thm:ugc-class`), the conjunction of `PaperArithmetic.ugc_thresholds`, `ConflictGraph.selSet_independent` with `card_selSet` and `CutTransfer.value_eq_edges_add_cut`, `ConflictGraph.alpha_eq`, `ConflictDegree.card_nbrs_regular` and `card_occ`, `CutTransfer.independent_ratio_from_cut`, and `CutLift.lift_ratio_from_cut`. The Goemans-Williamson guarantee is not part of the statement.
* `UgcBroken`: the theorem `ugc_broken` (Theorem `thm:ugc-broken`, item 3 and the threshold comparison): `beta* < alpha* < 19/20 < 83/84`, `19(3d+3) < 20(3d+2)` for `d >= 6`, and the `83/84` lift of an independent set with `6 alpha <= 7 |I|` for every degree `D >= 3`.
* `CutLift`: an independent set `I` of `H` with `18785 alpha <= 20000 |I|` lifts to ratio `83/84` on `T_H` for every degree (the last step of Theorem `thm:cutclass`). The construction of `I` from a cut is in `ConflictGraph` (`selSet`, `alpha_eq`); the cut guarantee `cut >= 0.8785 maxcut` is the cited Goemans-Williamson/Mahajan-Ramesh result.

* `DegreeTransfer.bf_general_degree_d_proof` and `DegreeFormula.lift_ratio_bf_general`: the Berman-Fujito transfer for every degree with `epsilon = 1/c`, in division-free form (seventh claim of Proposition `prop:degd`).

* `DegreeTransfer.bf_loss_bound`: `63 d <= 4 (d+1)(d+3) + 126`, the inequality behind the statement that the Berman-Fujito ratio exceeds `0.97` for every `d >= 4` (and so every regular class with `d >= 3` has a factor above the Brakensiek-Huang-Zwick constant). These are statements about three-occurrence classes, not about all instances.


* `Solution.ratio_at_least_83_84_general` and `Solution.general_endpoint_ratio`: the transfer `84((d+1)n + m + |I|) >= 83((d+1)n + m + alpha)` for every `d >= 3` and the monotone endpoint ratio `(beta + 3/7)/(beta + 1/2) >= 83/84`, proved directly in `Solution.lean`.

* `PaperArithmetic`: the comparison `83/84 > 0.94615981 > 0.94016567` (Theorem `thm:ugc-class`), `(3d+2)/(3d+3) > 0.95` for `d >= 6`, strict monotonicity of `(21d+20)/(21d+21)`, the two-branch arithmetic `84(4n+m+s) >= 83(4n+m+alpha)` of Theorem `thm:ratio` from the two branch guarantees as hypotheses, the constants of Theorem `thm:cutclass` and of Proposition `prop:bounded-cut` (`0.9977`), and the tabulated values.

## Taken from the literature (hypotheses, not proved)

| Result | Reference | Lean form |
| --- | --- | --- |
| Semidefinite rounding of Max Cut; cut fraction at least `arccos(1-2c)/pi` for SDP value `c >= 0.845` | Goemans and Williamson, J. ACM 42 (1995) | `CutGuarantee` |
| Derandomization of the rounding in polynomial time | Mahajan and Ramesh, SIAM J. Comput. 28 (1999) | `CutGuarantee` |
| Independent set in degree-`Delta` graphs within `(Delta+3)/5 + epsilon` | Berman and Fujito (1999) | `BFGuarantee`, and the hypothesis `5 alpha <= (d+3)|I|` |
| Near-bipartite branch for cubic graphs | Trevisan | hypotheses of the two-branch arithmetic in `PaperArithmetic` |
| Max Cut on graphs of maximum degree `d` above the Goemans-Williamson constant (expected ratio `0.9326` for `d = 3`) | Feige-Karpinski-Langberg, J. Algorithms 43 (2002); Halperin-Livnat-Zwick, J. Algorithms 53 (2004); Hsieh-Kothari, ICALP 2023 | `BoundedCut` |
| UG-hardness of Max Cut above `0.87856`, and of MAX 2-SAT and Horn-2SAT above the Lewin-Livnat-Zwick and Brakensiek-Huang-Zwick constants | Khot-Kindler-Mossel-O'Donnell, SIAM J. Comput. 37 (2007); Brakensiek-Huang-Zwick (SODA 2024) | not stated in Lean |
| `L`-reduction and APX-completeness for cubic graphs | Alimonti and Kann (2000) | text only |

Lean states the existence of the cut or independent set; the algorithms, their running
times and their analyses are in the references and are not formalized. The theorems
`degree_21_end_to_end`, `lift_ratio_bf`, `lift_ratio_from_mis` and `lift_ratio_threshold`
therefore say: if the cited guarantee holds on an instance, the lifted assignment has the
stated ratio on `T_H`.

## Not formalized

* The Unique Games Conjecture and the hardness thresholds `0.94615981`
  (Brakensiek, Huang, Zwick) and `0.94016567` (Lewin, Livnat, Zwick). They are statements
  about all instances of MAX-HORN-SAT and MAX 2-SAT. No Lean statement uses them; the
  comparison `83/84 > 0.94615981 > 0.94016567` of Theorem `thm:ugc-class` is in the paper.
* The bounded-occurrence approximation of Ghoshal, Huang, Lee, Makarychev and Makarychev,
  and the Raman, Ravikumar and Rao classification of two- and three-occurrence MAX 2-SAT.
* Statements of the paper that are not stated in Lean:
  - Theorem `thm:apx`: the APX-completeness statement (only the `L`-reduction constants are proved).
  - Proposition `prop:cutconflict`: the consequence `OPT(T_H) = B + m + maxcut(G)` for the conflict graph `H = H(G)` and the extraction of a cut from an assignment of `T_H` as one statement; its ingredients are `alpha_eq`, `exact_degree_identity_proof` and `cut_from_TH_value`.
  - Proposition `prop:cutconflict`: simplicity of `H(G)` (no loops or repeated edges) is not a separate lemma; the neighbour counts behind `(d+1)`-regularity are `nbrs_eq`, `card_nbrs`, `card_nbrs_regular`.
  - Proposition `prop:cut2sat`: `OPT(F_G) = m + maxcut(G)` is not one statement; it is `value_eq_edges_add_cut` together with `alpha_eq`. Corollary `cor:cutratio` is proved division-free (`cut_from_2sat_value`, `cut_from_TH_value`), not with real `gamma` and `rho`.
  - Section on Unique Games thresholds: the decimal remarks `19/20 > 0.94615981`, `r(3) - 0.94016567 ~ 0.04793` and `(d-2)/(3(d+1)(d+3)) < 0.022` are not stated; `ugc_thresholds`, `endpoint_increasing`, `baseline_above_095` and the bound `63 (d-2) <= 4 (d+1)(d+3)` are.
  - Theorem `thm:ratio` and Proposition `prop:degd` (5): the Trevisan bound `1 - 4 sqrt(eps) + 8 eps > 0.95`, the Goemans-Williamson bound `arccos(1-2c)/pi` for `c >= 0.845` and the exhaustive solution of small orders are cited or in the text only; Lean has the arithmetic consequences (`bf_branch_numeric_21`, `cut_fraction_degree_21`, `ratio_83_84_two_branch`).
  - Every polynomial-time statement: Theorems `thm:ratio`, `thm:cutclass`, `thm:ugc-class`, and Proposition `prop:degd` (5), (7) assert algorithms; Lean proves the ratio of the lift of a given independent set or cut, and the algorithms are cited.
* Conditional statements: the threshold results for `4 <= d <= 20` hold only for an
  independent-set algorithm of ratio `(27-d)/28`, which is not proved.
