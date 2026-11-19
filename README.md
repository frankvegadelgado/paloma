# Exact MAX-2SAT assignment--witness identity

This standalone Lean 4 project formalizes an exact reduction from MAX-2SAT to
Maximum Independent Set (MIS), together with its SAT threshold, conditional
approximation consequence, and finite gadget audit.

**Author:** Frank Vega<br>
**Affiliation:** Information Physics Institute, 840 W 67th St, Hialeah, FL
33012, USA<br>
**Email:** [vega.frank@gmail.com](mailto:vega.frank@gmail.com)

## Main result

For a 2-CNF formula `φ` on `N` variables, with every clause copied `K` times,
the assignment--witness conflict graph satisfies

```text
α(G_{φ,K}) = N + K * OPT_MAX2SAT(φ).
```

The graph has two adjacent assignment values for each variable, one witness
for each literal occurrence in each clause-copy, a clique on the witnesses of
each clause-copy, edges between complementary witnesses, and an edge from each
witness to the assignment value that falsifies it.

The identity has matching constructive bounds. From an assignment satisfying
`r` clauses, select all `N` corresponding assignment vertices and one true
witness from every copy of each satisfied clause, obtaining an independent set
of size `N + K*r`. Conversely, the witnesses of any independent set have
consistent signs. They determine a partial assignment that can be completed
without invalidating a selected witness. Each clause-copy contributes at most
one witness, so a set decoded to an assignment satisfying `r` clauses has size
at most `N + K*r`. Taking the best assignment proves equality.

`PalomaMax2SAT/Identity.lean` formalizes:

- finite MAX-2SAT syntax, literal evaluation, satisfaction, and optimum;
- the four conflict constraints defining graph-independent selections;
- construction of a total decoded assignment from any independent selection;
- truth of every selected witness under that assignment;
- the exact identity and the target `N + Kq` characterization of SAT;
- the exact powered-integer conditional approximation implication;
- the binary clause-gadget truth table;
- the audit cardinality `2(1 + 10 + 10^2 + 10^3) = 2222`; and
- exhaustive local gadget enumeration through arity three, proving minimum
  auxiliary orders `1,2,3` and labelled minimum counts `1,2,6`.

## Consequences and limits

The reduction is affine and optimum-preserving. Given an exact MIS optimum,

```text
OPT_MAX2SAT(φ) = (α(G_{φ,K}) - N) / K.
```

For `K > 0`, satisfiability is characterized exactly by the graph threshold
`α(G_{φ,K}) = N + K*q`. Reaching only the `N` assignment vertices is not a
SAT certificate; a positive certificate must provide an assignment satisfying
all `q` clauses.

The formalization also proves a conditional approximation test using exact
natural-number arithmetic. If a claimed MIS guarantee would imply

```text
(N + K*q)^b ≤ score^b * graphOrder^(b-a)
```

on satisfiable instances, observing the strict reverse inequality establishes
unsatisfiability under that guarantee. Without the guarantee, the observation
instead exposes a failed approximation claim and is not by itself an UNSAT
proof.

Uniformly copying each clause supplies integer weights and an additive gap,
but does not create the polynomial multiplicative gap needed for an
`n^(1-ε)` MIS inapproximability result: the satisfiable/unsatisfiable ratio
approaches only `q/(q-1)`. The repository claims the exact identity and its
stated consequences, not such a gap amplification.

## Independent finite evidence

The repository also contains a separate Python bit-mask checker:

- `experiments/max2sat_exhaustive.py`
- `experiments/results/max2sat_exhaustive.json`

It calls neither NetworkX nor the Lean development. It independently enumerates
truth assignments, constructs integer edge masks, enumerates every graph vertex
subset, and checks the exact identity. The recorded two-variable audit covers
2,222 ordered formula/multiplicity instances with zero counterexamples.

The Lean theorem does not import or assume those finite outcomes. It imports
only Mathlib and proves the identity for every finite instance represented by
its definitions and every natural multiplicity `K`.

The separate local gadget search enumerates every auxiliary graph and terminal
attachment through arity three. It proves minimum auxiliary orders `1,2,3`
and labelled minimum counts `1,2,6`: the clause clique with one-to-one
falsifying-terminal attachments, up to relabelling.

## Formal proof and trust boundary

`GraphIndependentSet` is an extensional encoding of independent selections.
Finite-set indexing enforces the assignment-pair and clause-copy clique
constraints; explicit fields enforce complementary-witness consistency and
assignment--witness compatibility. Witness truth is derived by the decoder,
not assumed as part of the structure.

`Challenge.lean` intentionally retains one `sorry` placeholder for the main
exact-identity theorem that Comparator asks `Solution.lean` to prove; the
short supporting results are proved directly, minimizing placeholder warnings.
That remaining warning belongs to the challenge interface and is not an
admitted proof in the submitted solution. The implementation in
`PalomaMax2SAT/Identity.lean` and every theorem in `Solution.lean` contain no
`sorry`; Comparator replays them through
Lean's kernel and the toolchain's NanoDa and con-ron independent kernels. The
permitted foundational axioms are limited to `propext`, `Quot.sound`, and
`Classical.choice`.

## Standalone paper

`doc/paper.tex` is a self-contained AMS note. It introduces MIS and MAX-2SAT,
proves the identity, explains exact optimization transfer, SAT certification,
the conditional approximation test, the limitation of uniform replication,
and cites the standard complexity and approximation literature.
This README summarizes its main technical content; the paper supplies the
continuous mathematical exposition and bibliography.

## Project layout

- `Challenge.lean` is the small, Mathlib-only public statement surface.
- `Solution.lean` supplies proofs from `PalomaMax2SAT/Identity.lean`.
- `comparator.json` selects every public theorem for comparison.
- `formalization.yaml` records scope, provenance, and theorem alignment.
- `scripts/check-lean-sources.py` performs source-policy checks.
- `.github/workflows/palomar.yml` builds and runs Comparator remotely.

## Remote verification

The GitHub Actions workflow installs the pinned toolchain and Mathlib, builds
the project, checks source policy, and runs Comparator. A public immutable
commit can then be submitted to Palomar for Lean, Comparator, and independent
kernel verification.

The equivalent commands are:

```sh
lake build
python3 scripts/check-lean-sources.py
bash scripts/verify-comparator.sh
```

## License

MIT License. See `LICENSE`.
