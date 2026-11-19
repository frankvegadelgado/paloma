# An 83/84 approximation for a cubic three-occurrence Horn class

This repository formalizes Frank Vega's cubic-graph construction for an
unweighted MAX-HORN-2SAT subclass in which every variable occurs exactly three
times, together with supporting material on the standard hard-consistency
occurrence split.

The Lean development contains two groups of results:

1. the main contribution: the cubic construction — the four-clone score, the
   constructive repair, the exact optimum identity `4*|V| + |E| + alpha(H)`,
   and the arithmetic transfer of the Berman--Fujito `7/6` guarantee to
   `83/84`; and
2. a supporting formalization of the standard forced-equality occurrence
   split: propagation of hard implications around a directed cycle, abstract
   transfer lemmas, and a concrete weighted Horn occurrence-split model. These
   results formalize a routine consistency gadget for verification and reuse;
   they are **not** claimed as an independent research contribution.

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

Berman and Fujito's `7/6` approximation for independent set on cubic graphs
returns `|I| >= 6*alpha/7`. For a cubic graph, `m=3n/2` and `alpha<=n/2`, so

```text
(4n + m + |I|)/(4n + m + alpha)
    >= (11 + 6/7)/12
    = 83/84.
```

Thus the exact cubic image class has a polynomial-time `83/84` approximation.
The repair also gives an L-reduction with constants 23 and 1, proving
APX-completeness.

`83/84` is the solution/optimum ratio.

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

## Supporting: the hard-consistency occurrence split

The general weighted occurrence split keeps every source-clause weight and
makes every cyclic implication

```text
(not x_i or x_(i+1))
```

a mandatory hard clause with zero objective contribution. This is a
**standard forced-equality gadget**: hard implication cycles force every
occurrence clone of a variable to agree, after which encoding and decoding
preserve the weighted objective pointwise. It is included here because the
Lean development formalizes its encode/decode score equalities and their
optimum-preservation and feasible-solution value-preservation consequences as
a reusable interface and sanity check.

We do not advertise the split as a novel mathematical result. The specific
informal claims in the literature that motivated us to formalize it are:

```text
OPT_partial(split(F)) = OPT(F)
```

with no additive offset, and pointwise preservation of every feasible
solution's objective value under decoding.

`PalomaMax2SAT/HardOccurrenceSplit.lean` formalizes the directed-cycle
consistency lemma, two abstract transfer lemmas, and the exact comparison
`83/84 > 0.94615981`.

The concrete weighted Horn occurrence split is formalized in
`PalomaMax2SAT.ConcreteHardSplit`. The model uses occurrence-indexed literals,
weighted Horn clauses, and hard cyclic implications. Feasible split assignments
are exactly consistent lifts. Lean proves that every encoded source assignment
is feasible, that encoding preserves score, and that decoding any feasible
split assignment preserves score. Consequently,
`concrete_exact_hard_occurrence_split` proves
`OPT_partial(split(F)) = OPT(F)` with no additive offset, and
`concrete_feasible_solution_ratio_preserved` proves every feasible solution has
exactly the objective value of its decoded source assignment. The earlier
abstract transfer lemmas remain as reusable interface lemmas; they are not
selected as a hard-split contribution.

`experiments/weighted_test_horn_split.py` checks 16,314 small Horn formula
shapes. It verifies equality of the optima and, more strongly, equality of all
attainable objective-value sets between source assignments and feasible split
assignments.

## UGC barrier and the P versus NP implication

Brakensiek, Huang, and Zwick prove that the approximation ratio
`0.94615981` for weighted MAX `{1,2}`-HORN-SAT is tight under the Unique Games
Conjecture (UGC). Since

```text
83/84 = 0.988095238... > 0.94615981,
```

the cubic `83/84` result is nominally above the UGC-hard threshold. The
`83/84` algorithm proved here, however, is only established for the cubic
subfamily `{T_H}`; it is **not** an algorithm for the entire hard-split image
`{P(F)}`. The hard-split construction itself is a routine forced-equality
gadget, not a novel reduction, and does not by itself provide any algorithmic
gain beyond what the cubic construction already supplies.

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

OpenAI's 2026 preprint *The Unique Games Theorem* claims a deterministic
polynomial-time reduction from 3SAT to Unique Games with the completeness and
soundness gap required by UGC. The preprint is public and includes associated
formal artifacts, but it has not yet been peer reviewed. If that claimed proof
is accepted, the first premise in the chain above becomes a theorem rather
than a conjectural assumption. The rest of the chain is unaffected by that
acceptance; it still requires the algorithmic extension described above.

The present repository proves the `83/84` algorithm for the cubic subfamily
`{T_H}` and proves exact ratio preservation for the full hard-consistency
image `{P(F)}`. The mathematical content of the hard-split material is a
standard consistency argument; the contribution of the repository is the cubic
repair, the exact `4n+m+α(H)` identity, and the arithmetic transfer to
`83/84`.

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
- OpenAI, *The Unique Games Theorem*, OpenAI Math Release preprint,
  September 23, 2026. This manuscript claims a proof of UGC and is not yet
  peer reviewed.
  [Preprint and source](https://github.com/openai/math/tree/main/preprints/The-Unique-Games-Theorem-September-23-2026)

## License

MIT License. See `LICENSE`.
