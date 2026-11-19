# A weighted three-occurrence MAX-HORN-2SAT image class

This repository focuses on one result: a dominant-weight occurrence split
whose image is a special weighted three-occurrence MAX-HORN-2SAT class with a
polynomial `18/19` approximation and, more generally, a PTAS.

**Author:** Frank Vega  
**Affiliation:** Information Physics Institute, 840 W 67th St, Hialeah, FL
33012, USA  
**Email:** [vega.frank@gmail.com](mailto:vega.frank@gmail.com)

## Construction and exact identity

For a weighted MAX-HORN-2SAT instance `F`, let `W` be its total clause weight
and `C` its number of literal occurrences. Split every occurrence into a clone.
For the clones of each original variable, add a directed cycle of consistency
implications, each of weight `M > W` (for example, `M = W + 1`).

Each clone then occurs exactly three times: once in its source clause, once
negatively in its outgoing implication, and once positively in its incoming
implication. The resulting instance `T_M(F)` satisfies

```text
OPT(T_M(F)) = C*M + OPT(F).
```

An inconsistent assignment loses at least one clause of weight `M`; all source
clauses together have weight at most `W < M`. Hence every optimum is consistent
and the identity follows.

## Approximation result

The image class has a polynomial `18/19` approximation:

- If `C <= 17`, enumerate at most `2^17` clone assignments and solve exactly.
- If `C >= 18`, set every clone to false. This satisfies all consistency
  implications and earns at least `C*M`.

Since `OPT(F) <= W < M`, the second branch has ratio

```text
C*M / (C*M + OPT(F)) > C/(C+1) >= 18/19
```

and `18/19 = 0.947368421... > 0.94615981`.

The same dichotomy is a PTAS: for fixed `epsilon`, enumerate when
`C < 1/epsilon`; otherwise the all-false assignment has ratio greater than
`1 - epsilon`. The running time is
`2^O(1/epsilon) * poly(input size)`.

The comparison is with the tight UGC threshold reported for the unrestricted
weighted MAX `{1,2}`-HORN-SAT language. A better algorithm on this proper image
class does not contradict that general hardness result, and the additive
offset `C*M` cannot in general be subtracted from a multiplicative guarantee
to recover the same ratio for the source instance.

## Verification

`PalomaMax2SAT/WeightedSplit.lean` contains only the formal numerical core:

- the dominant-weight optimum identity;
- the division-free `18/19` baseline inequality; and
- the exact comparison `18/19 > 0.94615981`.

`experiments/weighted_test_horn_split.py` independently checks the optimum
identity on 4,218 small weighted formula shapes and prints the ratio comparison.

The Lean sources contain no admitted placeholders. GitHub Actions is the verification
authority: it installs the pinned toolchain, builds the focused library, runs
the source-policy check, and compares the public `Challenge.lean` and
`Solution.lean` statements through Comparator and its independent kernels.

The paper is `doc/paper.tex`, with its compiled artifact at `doc/paper.pdf`.

## Build

```sh
python experiments/weighted_test_horn_split.py
```

Lean is intentionally checked by `.github/workflows/palomar.yml` rather than
by a local build that could download a toolchain.

## Reference

J. Brakensiek, N. Huang, and U. Zwick, “Tight approximability of MAX 2-SAT
and relatives, under UGC,” SODA 2024.

Repository: [frankvegadelgado/paloma](https://github.com/frankvegadelgado/paloma)

## License

MIT License. See `LICENSE`.
