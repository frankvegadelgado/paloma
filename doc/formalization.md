# Formalization notes

This document states what the Lean development proves, what it takes from the
literature as explicit hypotheses, and what it does not touch.

## Proved in Lean

* `CubicThreeOccurrence`, `SemanticHorn` (degree 3) and `DegreeFormula` (every degree `d`):
  the formula `T_H` as an explicit list of Horn clauses, the number of satisfied clauses,
  the exact optimum `(d+1)n + m + alpha`, `2m = dn`, `2 alpha <= n`, and that every variable
  occurs exactly three times.
* `DegreeTransfer`: the arithmetic of Proposition 3 (baseline, `d >= 27`, Berman--Fujito for
  `d >= 22`, the `6/7` set, the threshold `(27-d)/28`, and the two branches at `d = 21`).
* `DegreeFormula`: the same arithmetic stated about `T_H` itself, through the value
  `(d+1)n + m + |I|` of the lift of an independent set `I`.
* `CitedResults`: the combinatorial step from a cut with at most `7m/100` uncut edges to an
  independent set with `3n <= 25|I|`, and the end-to-end degree-21 statement.

## Taken from the literature (hypotheses, not proved)

| Result | Reference | Lean form |
| --- | --- | --- |
| Semidefinite rounding of Max Cut; cut fraction at least `arccos(1-2c)/pi` for SDP value `c >= 0.845` | Goemans and Williamson, J. ACM 42 (1995) | `CutGuarantee` |
| Derandomization of the rounding in polynomial time | Mahajan and Ramesh, SIAM J. Comput. 28 (1999) | `CutGuarantee` |
| Independent set in degree-`Delta` graphs within `(Delta+3)/5 + epsilon` | Berman and Fujito (1999) | `BFGuarantee`, and the hypothesis `5 alpha <= (d+3)|I|` |
| Near-bipartite branch for cubic graphs | Trevisan | hypotheses of the `GraphTransfer` bridge |
| `L`-reduction and APX-completeness for cubic graphs | Alimonti and Kann (2000) | text only |

Lean states the existence of the cut or independent set; the algorithms, their running
times and their analyses are in the references and are not formalized. The theorems
`degree_21_end_to_end`, `lift_ratio_bf`, `lift_ratio_from_mis` and `lift_ratio_threshold`
therefore say: if the cited guarantee holds on an instance, the lifted assignment has the
stated ratio on `T_H`.

## Not formalized

* The Unique Games Conjecture and the hardness thresholds `0.94615981`
  (Brakensiek, Huang, Zwick) and `0.94016567` (Lewin, Livnat, Zwick). They are statements
  about all instances of MAX-HORN-SAT and MAX 2-SAT. No Lean statement uses them, and no
  claim about them is made.
* The bounded-occurrence approximation of Ghoshal, Huang, Lee, Makarychev and Makarychev,
  and the Raman, Ravikumar and Rao classification of two- and three-occurrence MAX 2-SAT.
* Conditional statements: the threshold results for `4 <= d <= 20` hold only for an
  independent-set algorithm of ratio `(27-d)/28`, which is not proved.
