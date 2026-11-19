# An 83/84 approximation for a cubic three-occurrence Horn class

This repository formalizes Frank Vega's cubic-graph construction for an
unweighted MAX-HORN-2SAT subclass in which every variable occurs exactly three
times.

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

`83/84` is the solution/optimum ratio. `83/64` is greater than one and cannot
be that ratio for a maximization problem.

## Lean formalization

`PalomaMax2SAT/CubicThreeOccurrence.lean` contains:

- the port-labelled cubic graph representation;
- the three-occurrence score decomposition;
- the explicit deletion repair and proof that it is independent;
- the repair cardinality bound;
- the matching assignment induced by an independent set;
- the exact optimum identity; and
- the division-free arithmetic transfer from the `7/6` MIS guarantee to
  `83/84`.

There are no admitted placeholders. GitHub Actions installs the pinned Lean
toolchain, builds the project, and runs Comparator on the public theorems.
Lean is intentionally not built locally.

## Hard-consistency weighted occurrence split

The general weighted occurrence split keeps every source-clause weight and
makes every cyclic implication

```text
(not x_i or x_(i+1))
```

a mandatory hard clause with zero objective contribution. Feasible split
assignments are therefore exactly the consistent lifts of source assignments,
so

```text
OPT_partial(split(F)) = OPT(F)
```

with no additive offset. Every feasible solution has exactly the objective
value of its decoded source assignment, so multiplicative approximation ratios
are preserved.

`PalomaMax2SAT/HardOccurrenceSplit.lean` formalizes the directed-cycle
consistency lemma, exact hard-split optimum preservation, feasible-solution
value preservation, and the exact comparison
`83/84 > 0.94615981`.

`experiments/weighted_test_horn_split.py` checks 16,314 small Horn formula
shapes. It verifies equality of the optima and, more strongly, equality of all
attainable objective-value sets between source assignments and feasible split
assignments.

## Paper

The source is `doc/paper.tex` and the compiled paper is `doc/paper.pdf`.

Repository: [frankvegadelgado/paloma](https://github.com/frankvegadelgado/paloma)

## References

- P. Berman and T. Fujito, “On Approximation Properties of the Independent Set
  Problem for Low Degree Graphs,” *Theory of Computing Systems* 32 (1999).
- P. Alimonti and V. Kann, “Some APX-completeness Results for Cubic Graphs,”
  *Theoretical Computer Science* 237 (2000).

## License

MIT License. See `LICENSE`.
