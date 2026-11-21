# Paloma: MAX-HORN-2SAT and MAX-CUT formalization

Lean 4 formalization and computational checks for *An 83/84 approximation for a cubic three-occurrence Horn class* (`doc/paper.tex`). The paper also covers degree-d graphs, non-regular graphs, MAX 2-SAT, MAX-CUT through the conflict graph, and the Unique Games thresholds. `formalization.yaml` is the machine-readable inventory; this file explains it.

## Repository layout

| Path | Content |
| --- | --- |
| `doc/paper.tex` | The manuscript. |
| `doc/formalization.md` | What Lean proves, what is cited, what is not formalized. |
| `formalization.yaml` | Module inventory with status of each module. |
| `PalomaMax2SAT/` | Lean 4 modules (table below). |
| `experiments/` | Python verification scripts (`coverage.py`, `graph_transfer.py`, `weighted_test_horn_split.py`). |
| `scripts/` | `check-lean-sources.py`, `verify-comparator.sh`. |

## Lean modules

| Module | Status | What it contains |
| --- | --- | --- |
| `CubicThreeOccurrence` | formalized | Cubic 3-port construction, repair, optimum `4n + m + α`, `83/84` transfer arithmetic. |
| `SemanticHorn` | formalized | Explicit Horn clauses, score decomposition, `5n + m` clauses, three occurrences per variable. |
| `DegreeTransfer` | formalized (arithmetic) | Degree-`d` ratio inequalities, `d = 21` two-branch arithmetic, `ρ(d)` and `(21d+20)/(21d+21)` bounds, Berman–Fujito form for every degree, `63d ≤ 4(d+1)(d+3)+126`. |
| `DegreeFormula` | formalized | Uniform degree-`d` formula `T_H`, optimum `(d+1)n + m + α`, `2m = dn`, `2α ≤ n`, Horn property, `(d+2)n + m` clauses, three occurrences, lift of an independent set. |
| `GeneralDegreeFormula` | formalized | Arbitrary degrees `d_v` with `(d_v+1)`-cycles: repair inequality, lift of an independent set, optimum `B + α` with `B = Σ(d_v+1) + m` (`= n + 3m` when degrees sum to `2m`), and the step `8α ≤ B`, `18785α ≤ 20000|I|` ⇒ `0.9932` ratio. |
| `HardOccurrenceSplit` | formalized | Hard-cycle consistency for the occurrence split `P(F)`. |
| `GraphTransfer` | formalized with hypotheses | Hard optima `4m + α` and `m + α`, `257/260` and `77/80` transfers, `27/28` branch arithmetic from numerical hypotheses. |
| `CutTransfer` | formalized | MAX-CUT as MAX 2-SAT: satisfied clauses of `F_G` equal `m + cut(S)`; arithmetic of the ratio transfer to the cut. |
| `CutLift` | formalized | Lifting step of Theorem `thm:cutclass`: `18785α(H) ≤ 20000|I|` gives `83/84` on `T_H`. |
| `CitedResults` | hypotheses | Explicit hypotheses for the Goemans–Williamson/Mahajan–Ramesh cut bound and the Berman–Fujito independent-set bound, and the end-to-end degree-21 statement. |

## Cited, not proved

- Goemans–Williamson rounding and Mahajan–Ramesh derandomization (cut `≥ 0.8785 · maxcut`).
- Berman–Fujito independent-set approximation.
- Trevisan's bounded-degree independent-set results.
- Unique Games thresholds: Brakensiek–Huang–Zwick, Lewin–Livnat–Zwick, Ghoshal et al., Khot–Kindler–Mossel–O'Donnell for MAX-CUT. The Unique Games Conjecture is not formalized.

## In the paper only

- L-reductions and APX-completeness.
- The signed-graph construction (Theorem `thm:signed`).
- The conflict-graph identity `α(H(G)) = m + maxcut(G)` and the non-regular family bound `B ≥ 16m ≥ 8α` (Theorem `thm:nonreg-cutclass`).

## Building and verifying

```bash
lake build
python3 scripts/check-lean-sources.py
bash scripts/verify-comparator.sh
python3 experiments/coverage.py
python3 experiments/graph_transfer.py
python3 experiments/weighted_test_horn_split.py
```
