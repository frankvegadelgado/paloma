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

## The 83/84 guarantee

For the original soft class the endpoint proof in the revised paper combines a fixed-parameter Berman–Fujito run with Trevisan’s near-bipartite cut guarantee. The older arithmetic lemma takes a 6/7 independent set as input.

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
