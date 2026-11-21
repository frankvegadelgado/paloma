# An 83/84 approximation for a cubic three-occurrence Horn class

This repository formalizes Frank Vega's cubic-graph construction for an
unweighted MAX-HORN-2SAT subclass in which every variable occurs exactly three
times, together with the hard-score graph transfers for the hard four-port
cycle formulation.

The Lean development contains two groups of results:

1. the cubic construction: the four-clone score, the constructive repair, the
   exact optimum identity `4*|V| + |E| + alpha(H)`, and the arithmetic
   transfer of a `7/6` MIS guarantee to `83/84`; and
2. the hard-score graph transfers in `GraphTransfer.lean`: the exact hard
   optima `4m + alpha` (edge weight four) and `m + alpha` (unit weights), the
   `257/260` and `77/80` transfers from a `17/20` independent set, and the
   conditional `27/28` arithmetic.

For a simple cubic graph `H=(V,E)`, the formula `T_H` has four clones per
vertex, one source clause per clone, and four cyclic consistency implications.
Its exact optimum is

```text
OPT(T_H) = 4*|V| + |E| + alpha(H).
```

Every assignment of value `A` is repaired in polynomial time to an independent
set of size at least

```text
A - (4*|V| + |E|).
```

## Summary of the paper

The paper is `doc/paper.tex`. Everything below is proved there; the last section lists what Lean covers.

**Class and exact identity.** For a simple cubic graph `H=(V,E)`, `T_H` has four Boolean clones `z_{v,0..3}` per vertex, a unit clause `(not z_{v,0})`, an edge clause `(z_{u,p} or z_{v,q})` for every edge, and four cyclic implications `(not z_{v,i} or z_{v,i+1})`. It has `4n` variables, `5n+m` clauses, at most one negative literal per clause, and every variable occurs exactly three times. The satisfied-clause count is `U(z) + (m - F(z)) + (4n - T(z))`, and `OPT(T_H) = 4n + m + alpha(H)`. Every assignment of value `A` is repaired in polynomial time to an independent set of size at least `A - (4n + m)` (delete the left endpoint of every edge induced by the clean selected vertices).

**83/84 for cubic graphs.** Put `B = 4n + m = 11n/2`; since `alpha <= n/2`, a `6/7`-approximate independent set gives `(11 + 6/7)/12 = 83/84`. The algorithm returns the better lift of two sets: a Berman-Fujito run with solution fraction `6/7 - 10^-6`, which suffices when `2 alpha/n <= 9999/10000`, and a set from Trevisan's near-satisfiable Max Cut guarantee (`epsilon = 10^-4`, cut fraction above `0.95`), which has size at least `37n/80 > 3n/7` in the remaining case.

**Degree `d`.** For a simple `d`-regular graph, `d+1` clones per vertex give `OPT(T_H) = (d+1)n + m + alpha(H)`, with `B = (d+1)n + m = (3d+2)n/2` and `alpha <= n/2`. Proved ratios:

- the all-true assignment has value `B` and gives `(3d+2)/(3d+3)`, which is at least `83/84` for `d >= 27`, and exceeds `0.94615981` for `d >= 6`;
- a Berman-Fujito set with `5 alpha <= (d+3)|I|` gives `83/84` for `d >= 22`;
- for `d = 21`, a Berman-Fujito run (`epsilon = 1/50`, used when `alpha <= 99n/200`) combined with a derandomized Goemans-Williamson cut rounding (used otherwise, giving a set of size above `0.12 n`) gives `83/84`;
- an independent set with `|I| >= ((27-d)/28) alpha` gives `83/84`; the threshold is `6/7` at `d = 3`, `23/28` at `d = 4`, and `1/4` at `d = 20`;
- a `6/7`-approximate independent set gives `(21d+20)/(21d+21)`, which is strictly increasing in `d` and tends to `1`.

For `4 <= d <= 20` the paper proves the conditional statements above; it does not claim an independent-set algorithm that meets the thresholds.

**APX-completeness.** The map from cubic MIS is an `L`-reduction with constants `23` and `1`, so the cubic class is APX-complete. For fixed `d >= 3` the first constant is `O(d^2)` and the second is `1`.

**Forced-equality occurrence split.** For a weighted MAX-HORN-2SAT instance, every literal occurrence gets a clone and every variable gets a directed hard cycle of implications with zero weight. Hard cycles force all clones of a variable to agree, the optimum is preserved exactly, and a `rho`-approximation for the split image gives a `rho`-approximation for the source.

**Hard-split family.** For a cubic graph with unit vertex rewards and edge-clause weights `w_e >= 1`, the feasible optimum is `W + alpha`. There is a polynomial-time `27/28` approximation for all `w_e >= 1`, and `257/260` when `W >= 6n` (for example all edge weights four). A single cubic MIS run with `20|I| >= 17 alpha` gives `77/80`. A counterexample built from four copies of the cube `Q_3` shows that hardening changes the ratio: `190/192` on `T_H` against `62/64` on the hard split.

**Signed graphs.** The unsigned construction fails already on `K_4`. For any weighted source of width at most two, a simple vertex-weighted graph of maximum degree three has `alpha_w(J) = D M + OPT(F)`, with `M = W + 1`, and independent sets decode to split assignments of score at least `A - D M`. This preserves guarantees only on the excess `A - D M`.

**UGC.** The Brakensiek-Huang-Zwick constant `0.94615981` (weighted MAX `{1,2}`-HORN-SAT) and the Lewin-Livnat-Zwick constant `0.94016567` (MAX 2-SAT) are UG-hardness thresholds over all instances. On the class where every variable occurs exactly three times, `83/84` lies above both. The `d`-regular ratios above (`(3d+2)/(3d+3)` for `d >= 6`, `83/84` for `d = 3`, `d >= 21`) are statements about bounded-occurrence classes; they are consistent with Ghoshal-Huang-Lee-Makarychev-Makarychev's `0.94016567 + Omega~(1/d^2)` for bounded-occurrence MAX 2-SAT and give no information about all instances. A guarantee above the thresholds on all instances is not claimed. Conditionally on an independent-set algorithm of ratio `(27-d)/28` on `d`-regular graphs, the class for that `d` would also reach `83/84`.

**Lean.** The Lean development formalizes `T_H` as an explicit list of clauses, the score decomposition, repair, exact optimum identity, Horn property, clause count and three-occurrence property, all arithmetic transfers listed above, the hard-score optima `4m + alpha` and `m + alpha` with their `257/260` and `77/80` transfers, and the `27/28` arithmetic from numerical hypotheses. The Berman-Fujito, Trevisan and Goemans-Williamson guarantees, the `L`-reduction, the weighted and signed-graph theorems and the UGC discussion are proved in the paper and are not formalized.

## The 83/84 guarantee

For the original soft class the endpoint proof in the revised paper combines a fixed-parameter Berman–Fujito run with Trevisan’s near-bipartite cut guarantee. The arithmetic lemma takes a 6/7 independent set as input. For every fixed degree \(d\ge 3\), a 6/7 independent set gives at least \(83/84\): the function \((\beta+3/7)/(\beta+1/2)\) with \(\beta=3d/2+1\) is minimized at \(d=3\) and equals \(83/84\). Lean has this arithmetic; that such an independent set can be computed for every \(d\) is not proved.

With the original unit weights the hard cubic-source family has optimum `m + alpha`. A single cubic MIS run yields `77/80`; adding the near-bipartite branch gives `27/28`. Both exceed 0.94615981. The unit-score declarations are included in the public comparison. The Lean theorem `unit_endpoint_arithmetic` is conditional: it proves only the arithmetic `28(m+s) >= 27(m+alpha)` from the numerical hypothesis `6 alpha <= 7 s` or from the pair `20000 alpha <= 9999 n`, `5999993 alpha <= 7000000 s`. Lean does not prove that an independent-set algorithm supplies either hypothesis; the branch that supplies them (Berman--Fujito and Trevisan) is proved in the paper.

For the hard split of a cubic graph source with weight-one negative units and positive edge clauses of weight four, the feasible optimum is exactly `4m + alpha`. The lift of a 17/20 independent set attains at least 257/260 of this optimum. The new `GraphTransfer.lean` contains the concrete hard score, its repair, the optimum identity, and the division-free transfer. External graph algorithms are used through their published guarantees. The unrestricted signed graph result is a paper proof with a Python audit.

Run `python3 experiments/graph_transfer.py` for the exhaustive graph, unary-gadget, weighted-formula and cube checks. Run `lake build` for the Lean source. The new module is included by the default library target.


## Lean formalization

`PalomaMax2SAT/CubicThreeOccurrence.lean` contains:

- the port-labelled cubic graph representation, in which every one of the three
  ports of every vertex is used by exactly one edge endpoint (parallel edges
  are not excluded by the interface);
- the three-occurrence score decomposition;
- the explicit deletion repair and proof that it is independent;
- the repair cardinality bound;
- the matching assignment induced by an independent set;
- the exact optimum identity; and
- the division-free arithmetic transfer from the `7/6` MIS guarantee to
  `83/84`.

The implementation modules, `Solution.lean`, and the standalone canonical
`Challenge.lean` contain no admitted placeholders. In particular, the cubic
repair, cardinality bound, and exact optimum identity are proved directly in
the canonical challenge. GitHub Actions installs the pinned Lean toolchain,
builds the project, and runs Comparator on the public theorems. Lean is
intentionally not built locally.

## Hard-consistency formulation

Every cyclic implication `(not x_i or x_(i+1))` of the occurrence split is a
mandatory hard clause with zero objective contribution. The paper proves in
text that hard cycles force all clones of a variable to agree and that encoding
and decoding preserve the weighted objective pointwise.
`PalomaMax2SAT/HardOccurrenceSplit.lean` contains only the definitions and the
cycle-consistency lemma used by `GraphTransfer.lean`,.

`experiments/weighted_test_horn_split.py` checks 16,314 small Horn formula
shapes. It verifies equality of the optima and equality of all attainable
objective-value sets between source assignments and feasible split
assignments.

## UGC barrier and the P versus NP implication

Brakensiek, Huang, and Zwick prove that the approximation ratio
`0.94615981` for weighted MAX `{1,2}`-HORN-SAT is tight under the Unique Games
Conjecture (UGC). Since

```text
83/84 = 0.988095238... > 0.94615981,
```

the cubic `83/84` result is above the UGC-hard threshold. The `83/84`
algorithm proved here is established for the cubic subfamily `{T_H}`; it is
not an algorithm for the entire hard-split image `{P(F)}`.

OpenAI released on 6 October 2026 a manuscript claiming a proof of the UGC; this claim has not been peer reviewed (see the references).

The paper's approach to the UGC is as follows. Both UG-hardness thresholds (`0.94615981` for weighted MAX `{1,2}`-HORN-SAT and `0.94016567` for MAX 2-SAT) quantify over all instances, so they say nothing about the class where every variable occurs exactly three times, where `83/84` exceeds both. For each fixed occurrence bound `d`, MAX 2-SAT instances admit a `0.94016567 + Omega~(1/d^2)` approximation (Ghoshal, Huang, Lee, Makarychev, Makarychev, arXiv:2607.11050), which is consistent with the UGC. MAX 2-SAT with at most two occurrences per variable is solvable in linear time and with three occurrences it is NP-complete (Raman, Ravikumar, Rao, 1998). For `d`-regular graphs the lift of the empty independent set already gives `(3d+2)/(3d+3)`, which exceeds `83/84` for `d >= 27`; a Berman-Fujito set gives `83/84` for `d >= 22`, a two-branch Berman-Fujito and Goemans-Williamson argument for `d = 21`, and an independent set of ratio `(27-d)/28` for any `d`. The Lean module `DegreeTransfer` formalizes this arithmetic and `DegreeFormula` formalizes the degree-`d` formula `T_H`, its optimum `(d+1)n+m+alpha`, `2m = dn`, `2 alpha <= n` and the transfer of independent-set guarantees to `T_H`. The module `CitedResults` states the Goemans-Williamson/Mahajan-Ramesh and Berman-Fujito guarantees as explicit hypotheses with references; `doc/formalization.md` lists what is proved, what is cited and what is not formalized (the UGC and its thresholds). These statements concern bounded-degree classes; the UG-hardness thresholds quantify over all instances. A guarantee above these constants on all instances would not be consistent with the UGC, and the paper does not claim one.

A conditional chain is therefore recorded for context only:

```text
UGC
+ a polynomial 83/84-approximation for the full hard-split image
+ exact ratio-preserving decoding
=> a polynomial algorithm exceeding the UGC-hard Horn threshold
=> P = NP.
```

The step that is missing, and that would be required for the chain to fire, is
an algorithmic extension of the `83/84` guarantee from the cubic subfamily to
every instance of the full hard-split image. We do not claim that step here,
and the present repository does not supply it.

## Paper

The source is `doc/paper.tex` and the compiled paper is `doc/paper.pdf`.

Repository: [frankvegadelgado/paloma](https://github.com/frankvegadelgado/paloma)

## References

- P. Berman and T. Fujito, “On Approximation Properties of the Independent Set
  Problem for Low Degree Graphs,” *Theory of Computing Systems* 32 (1999),
  115–132. [DOI](https://doi.org/10.1007/s002240000113)
- P. Alimonti and V. Kann, “Some APX-completeness Results for Cubic Graphs,”
  *Theoretical Computer Science* 237 (2000), 123–134.
  [DOI](https://doi.org/10.1016/S0304-3975(98)00158-3)
- J. Brakensiek, N. Huang, and U. Zwick, “Tight Approximability of MAX 2-SAT
  and Relatives, under UGC,” *SODA 2024*, 1328–1344.
  [DOI](https://doi.org/10.1137/1.9781611977912.53) ·
  [arXiv](https://arxiv.org/abs/2310.12911)
- OpenAI, “Proof of Khot's Unique Games Conjecture” (entry 102 of the OpenAI
  mathematics release, 6 October 2026), GitHub repository
  [openai/math](https://github.com/openai/math). Not peer reviewed.
- V. Raman, B. Ravikumar, and S. Srinivasa Rao, “A simplified NP-complete MAXSAT
  problem,” *Information Processing Letters* 65 (1998), 1–6.
- M. X. Goemans and D. P. Williamson, “Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming,” *Journal of the ACM* 42 (1995), 1115–1145.
- S. Mahajan and H. Ramesh, “Derandomizing approximation algorithms based on semidefinite programming,” *SIAM Journal on Computing* 28 (1999), 1641–1663.
- S. Ghoshal, N. Huang, E. Lee, K. Makarychev, and Y. Makarychev, “Threshold
  rounding and bounded-degree Boolean MAX 2-CSP,” arXiv:2607.11050 (2026).