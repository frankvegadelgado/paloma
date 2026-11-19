# Exact MAX-2SAT assignment--witness identity

This standalone Lean 4 project formalizes an exact reduction from MAX-2SAT to
Maximum Independent Set (MIS), together with its SAT threshold, conditional
approximation consequence, and finite gadget audit.

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

## Standalone paper

`doc/paper.tex` is a self-contained AMS note. It introduces MIS and MAX-2SAT,
proves the identity, explains exact optimization transfer, SAT certification,
the conditional approximation test, the limitation of uniform replication,
and cites the standard complexity and approximation literature.

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
