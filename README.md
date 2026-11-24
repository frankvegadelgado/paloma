# Paloma: MAX-HORN-2SAT and MAX-CUT formalization

Lean 4 formalization for *An 83/84 approximation for a cubic three-occurrence Horn class* (`doc/paper.tex`). The paper also covers degree-d graphs, MAX 2-SAT, MAX-CUT through the conflict graph, and the Unique Games thresholds. `formalization.yaml` is the machine-readable inventory; this file explains it.

## Main result: ratio above the Unique Games thresholds

On the class `{T_{H(G)}}` of three-occurrence Horn formulas obtained from MAX-CUT instances (Theorem `thm:ugc-class`, from Theorem `thm:cutclass`), the polynomial-time factor `83/84` exceeds the Unique Games thresholds `α* ≈ 0.94616` (Brakensiek–Huang–Zwick, weighted MAX-HORN-2SAT) and `β* ≈ 0.94017` (Lewin–Livnat–Zwick, MAX 2-SAT), which hold for all instances. A Goemans–Williamson cut lifted to `T_{H(G)}` gives the factor `1 − (1 − α_ε)/(6d + 12) ≥ 83/84` for every `d ≥ 1`, and the cut recovered is the Goemans–Williamson cut, so the MAX-CUT guarantee itself is not improved. A bounded-degree cut guarantee `c_d` gives `1 − (1 − c_d)/(6d + 12)` (Proposition `prop:bounded-cut`), above `0.9977` in expectation for `d = 3`. The class has three occurrences per variable, so the result is consistent with the conjecture. The main theorem in Lean is `PalomaMax2SAT.UgcBounded.ugc_bounded` (Theorem `thm:ugc-class` for graphs of bounded degree), with `PalomaMax2SAT.UgcClass.ugc_class` its regular-graph counterpart. `ugc_class` states: `83/84 > 0.94615981 > 0.94016567`; the independent set `selSet` of the conflict graph has size `m + cut(S)`; `α(H(G)) = m + maxcut(G)`; `H(G)` is `(d+1)`-regular with `4m` vertices; `8785c ≤ 10000cut` implies `18785(m+c) ≤ 20000(m+cut)`; and the lift of an independent set `I` with `18785α ≤ 20000|I|` satisfies at least `83/84` of the optimum of `T_H`, for every degree `D ≥ 1`. Lean proves the arithmetic of the lift (`CutLift`, `CutTransfer`); the Goemans–Williamson guarantee and the thresholds are cited (`CitedResults`).

## Repository layout

| Path | Content |
| --- | --- |
| `doc/paper.tex` | The manuscript. |
| `doc/formalization.md` | What Lean proves, what is cited, what is not formalized. |
| `formalization.yaml` | Module inventory with status of each module. |
| `PalomaMax2SAT/` | Lean 4 modules (table below). |
| `scripts/` | `check-lean-sources.py`, `verify-comparator.sh`. |

## Lean modules

| Module | Status | What it contains |
| --- | --- | --- |
| `CubicThreeOccurrence` | formalized | Cubic 3-port construction, repair, optimum `4n + m + α`, `83/84` transfer arithmetic. |
| `SemanticHorn` | formalized | Explicit clauses with at most one negative literal, complement-variable translation to standard Horn clauses (`formula_horn`, `complement_satisfied`), score decomposition, `5n + m` clauses, three occurrences per variable. |
| `DegreeTransfer` | formalized (arithmetic) | Degree-`d` ratio inequalities, `d = 21` two-branch arithmetic, `ρ(d)` and `(21d+20)/(21d+21)` bounds, Berman–Fujito form for every degree, `63d ≤ 4(d+1)(d+3)+126`. |
| `DegreeFormula` | formalized | Uniform degree-`d` formula `T_H`, optimum `(d+1)n + m + α`, `2m = dn`, `2α ≤ n`, dual-Horn property and complement-variable translation to Horn clauses, `(d+2)n + m` clauses, three occurrences, lift of an independent set. |
| `CutTransfer` | formalized | MAX-CUT as MAX 2-SAT: satisfied clauses of `F_G` equal `m + cut(S)`; arithmetic of the ratio transfer to the cut. |
| `PaperArithmetic` | formalized | Numerical statements of the paper: `83/84 > 0.94615981 > 0.94016567`, two-branch arithmetic of Theorem `thm:ratio`, constants of `thm:cutclass` and `prop:bounded-cut`, value tables. |
| `GeneralDegreeFormula` | formalized | `T_H` for a port-labelled graph with a degree `d_v` at every vertex: `Σd_v = 2m`, `Σ(d_v+1)+m = n+3m`, satisfied clauses, repair, `OPT = Σ(d_v+1)+m+α`, value of the lift of an independent set. |
| `UgcBounded` | formalized | Main theorem `ugc_bounded` (Theorem `thm:ugc-class`, bounded degree): thresholds and `83/84 < 0.9932`, `selSet` and `α(H(G)) = m + maxcut(G)`, maximum degree `≤ d+1` of `H(G)`, degree sum `4m + 2Σdeg²`, the arithmetic `9932(B+α) ≤ 10000(B+|I|)`, and the identities and ratio for `T_H` of every port-labelled graph. |
| `RegularLemmas` | formalized | Degrees `1` and `2` of `T_H`: `α = m` and optimum `3 n` for `d = 1`, optimum `4 n + α` for `d = 2`. |
| `UgcRegular` | formalized | Main theorem `all_degd` (Theorem `thm:all-degd`): the optimum `(d+1) n + m + α`, the repair, the lift, the all-true ratio `(3d+2)/(3d+3)`, the `6/7`, threshold, Berman--Fujito and `d = 21` transfers, and the exact optima for `d = 1, 2`, for every `d ≥ 1`. |
| `StrongLemmas` | formalized | Arithmetic of Theorem `thm:strong-ugc-broken`: `1 − (1 − α_ε)/18` and `1 − (1 − α_ε)/(6d + 12)` exceed `0.9932`, the latter tends to `1`, and the division-free ratio `1 − (1 − p/q)/(6d + 12)` of a cut guarantee `p/q` on a `d`-regular graph. |
| `UgcStrong` | formalized | Main theorem `strong_ugc_broken` (Theorem `thm:strong-ugc-broken`, item 2): `α_GW < β* < α* < 83/84 < 0.9932`, the lifted ratios above any threshold `τ ≤ 0.9932`, `0.9326 − 0.87856 = 0.05404`, `α(H(G)) = m + maxcut(G)`, maximum degree `≤ d+1` of `H(G)`, and the exact optima of `T_H` for `d = 1, 2`. |
| `UgcClass` | formalized | Main theorem `ugc_class` (Theorem `thm:ugc-class`): thresholds, size `m + cut(S)` of `selSet`, `α(H(G)) = m + maxcut(G)`, regularity and `4m` vertices of `H(G)`, the arithmetic `8785c ≤ 10000cut ⇒ 18785(m+c) ≤ 20000(m+cut)`, and the `83/84` lift for every `D ≥ 1`. |
| `UgcBarrier` | formalized | Theorem `ugc_barrier`: `83/84` above the Unique Games thresholds, and the `83/84` ratio of the lift of an independent set with `18785α ≤ 20000|I|`. |
| `UgcBroken` | formalized | Theorem `ugc_broken` (Theorem `thm:ugc-broken`, item 3): `β* < α* < 19/20 < 83/84`, `19(3d+3) < 20(3d+2)` for `d ≥ 6`, and the `83/84` lift of an independent set with `6α ≤ 7|I|` for every `D ≥ 3`. |
| `CutLift` | formalized | Lifting step of Theorem `thm:cutclass`: `18785α(H) ≤ 20000|I|` gives `83/84` on `T_H`. |
| `LReduction` | formalized | Greedy independent set `n ≤ (Δ+1)|I|`, `L`-reduction constants of Theorem `thm:apx` (`OPT ≤ 23α` for `d = 3`, second constant `1`). |
| `ConflictGraph` | formalized | Conflict graph of `F_G` and `α(H(G)) = m + maxcut(G)` (Proposition `prop:cutconflict`). |
| `ConflictDegree` | formalized | `(d+1)`-regularity of the conflict graph, `2 deg(v)` occurrences of `x_v`, and `4m` vertices of the conflict graph. |
| `SignedGraph` | formalized | Theorem `thm:signed`: weight `D·M + OPT(F)` of the signed graph for weighted width-two inputs. |
| `CitedResults` | hypotheses | Explicit hypotheses for the Goemans–Williamson/Mahajan–Ramesh cut bound and the Berman–Fujito independent-set bound, and the end-to-end degree-21 statement. |

## Cited, not proved

- Goemans–Williamson rounding and Mahajan–Ramesh derandomization (cut `≥ 0.8785 · maxcut`).
- Berman–Fujito independent-set approximation.
- Trevisan's bounded-degree independent-set results.
- Unique Games thresholds: Brakensiek–Huang–Zwick, Lewin–Livnat–Zwick, Ghoshal et al., Khot–Kindler–Mossel–O'Donnell for MAX-CUT. The Unique Games Conjecture is not formalized.

## Not formalized in Lean

- Theorem `thm:apx`: the `L`-reduction constants are in `LReduction`; the APX-hardness of cubic Maximum Independent Set is cited and the APX-completeness statement itself is not stated in Lean.
- Theorem `thm:signed`: the weight identity `D·M + OPT(F)` of the signed graph is in `SignedGraph`; the vertex count and maximum degree of the signed graph are in the paper only.
- Proposition `prop:cutconflict`: the identity `α(H(G)) = m + maxcut(G)` is in `ConflictGraph`, and regularity and occurrence counts are in `ConflictDegree`.
- Proposition `prop:cutconflict`: the consequence `OPT(T_H) = B + m + maxcut(G)` as a single statement (its ingredients are in `ConflictGraph`, `DegreeFormula` and `CutTransfer`).
- Feige–Karpinski–Langberg, Halperin–Livnat–Zwick and Hsieh–Kothari bounded-degree MAX-CUT guarantees (expected ratio `0.9326` for `d = 3`), stated in `CitedResults` as `BoundedCut`.
- Proposition `prop:cutconflict`: simplicity of `H(G)` (no loops or repeated edges) is not stated as a separate lemma; the neighbour counts that give `(d+1)`-regularity are in `ConflictDegree`.
- Proposition `prop:cut2sat` and Corollary `cor:cutratio`: `OPT(F_G) = m + maxcut(G)` is available through `value_eq_edges_add_cut` and `alpha_eq`, not as one statement; Corollary `cor:cutratio` is proved in division-free form (`cut_from_2sat_value`, `cut_from_TH_value`), not with real `γ` and `ρ`.
- Section on Unique Games thresholds: the decimal remarks `19/20 > α*`, `r(3) − β* ≈ 0.04793` and `(d−2)/(3(d+1)(d+3)) < 0.022` are not stated; the comparison `83/84 > α* > β*`, the monotonicity of `r(d)` and the bound `63(d−2) ≤ 4(d+1)(d+3)` are.
- Section on signed graphs: the unary-terminal path example (maximum weights `1,1,1,2`) and the example of `k = 82` positive unit clauses are not stated.
- Theorem `thm:ratio` and Proposition `prop:degd`(5): the Trevisan bound `1 − 4√ε + 8ε > 0.95`, the Goemans–Williamson bound `arccos(1−2c)/π` and the exhaustive solution of small orders are cited or in the text only; Lean has the arithmetic consequences.
- The Unique Games thresholds, and all polynomial-time statements: Lean proves the ratio of the lift of a given independent set or cut, not that an algorithm produces it.

## Building and verifying

```bash
lake build
python3 scripts/check-lean-sources.py
bash scripts/verify-comparator.sh
```
