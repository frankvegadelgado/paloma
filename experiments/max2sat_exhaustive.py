"""Exhaustively verify the small MAX-2SAT-to-MIS reduction.

This script answers two separate questions.

* Which small auxiliary graphs realize a clause OR when the selected terminal
  for a literal means that the literal is false?
It also enumerates small 2-CNF formulae and independently checks the global
identity alpha(G_K) = N + K * OPT_MAX2SAT(phi).
"""

from __future__ import annotations

import argparse
import json
from itertools import combinations, product
from pathlib import Path


def independence_number(order: int, edges: tuple[tuple[int, int], ...]) -> int:
    """Return alpha of a graph represented by vertices 0..order-1."""
    adjacency = [0] * order
    for left, right in edges:
        adjacency[left] |= 1 << right
        adjacency[right] |= 1 << left
    best = 0
    for chosen in range(1 << order):
        size = chosen.bit_count()
        if size <= best:
            continue
        if all(not (chosen & (1 << vertex) and chosen & adjacency[vertex])
               for vertex in range(order)):
            best = size
    return best


def auxiliary_profile(
    arity: int,
    auxiliary_vertices: int,
    internal_mask: int,
    attachment_mask: int,
) -> tuple[int, ...]:
    """Maximum auxiliary reward for every set of false literal terminals."""
    pairs = tuple(combinations(range(auxiliary_vertices), 2))
    internal = tuple(pair for bit, pair in enumerate(pairs) if internal_mask >> bit & 1)
    profile: list[int] = []
    for false_terminals in range(1 << arity):
        available = [
            aux for aux in range(auxiliary_vertices)
            if not any(
                false_terminals >> terminal & 1
                and attachment_mask >> (aux * arity + terminal) & 1
                for terminal in range(arity)
            )
        ]
        relabel = {old: new for new, old in enumerate(available)}
        induced = tuple((relabel[u], relabel[v]) for u, v in internal
                        if u in relabel and v in relabel)
        profile.append(independence_number(len(available), induced))
    return tuple(profile)


def is_clause_or_profile(profile: tuple[int, ...], arity: int) -> bool:
    """Whether reward is c+1 iff at least one clause literal is true."""
    all_false = (1 << arity) - 1
    baseline = profile[all_false]
    return all(value == baseline + (mask != all_false)
               for mask, value in enumerate(profile))


def exhaustive_or_gadgets(arity: int, max_auxiliary: int) -> tuple[int | None, int]:
    """Return the minimum auxiliary order and number of labelled realizations."""
    for auxiliary in range(max_auxiliary + 1):
        internal_bits = auxiliary * (auxiliary - 1) // 2
        attachment_bits = auxiliary * arity
        count = 0
        for internal_mask in range(1 << internal_bits):
            for attachment_mask in range(1 << attachment_bits):
                profile = auxiliary_profile(
                    arity, auxiliary, internal_mask, attachment_mask)
                count += is_clause_or_profile(profile, arity)
        if count:
            return auxiliary, count
    return None, 0


def canonical_clause_gadget_profile(arity: int) -> tuple[int, ...]:
    """Profile of an arity-clique, each vertex blocked by one false terminal."""
    auxiliary = arity
    internal_mask = (1 << (auxiliary * (auxiliary - 1) // 2)) - 1
    attachment_mask = sum(1 << (index * arity + index) for index in range(arity))
    return auxiliary_profile(arity, auxiliary, internal_mask, attachment_mask)


def max2sat_optimum(formula: tuple[tuple[int, ...], ...], variables: int) -> int:
    return max(
        sum(any(values[abs(literal) - 1] == (literal > 0) for literal in clause)
            for clause in formula)
        for values in product((False, True), repeat=variables)
    )


def conflict_graph_bits(
    formula: tuple[tuple[int, ...], ...], variables: int, copies: int
) -> tuple[int, tuple[tuple[int, int], ...]]:
    """Independent implementation of the assignment-occurrence graph."""
    edges: set[tuple[int, int]] = set()
    for variable in range(variables):
        edges.add((2 * variable, 2 * variable + 1))
    occurrences: list[tuple[int, int, int, int]] = []
    next_vertex = 2 * variables
    for clause_index, clause in enumerate(formula):
        for copy in range(copies):
            clause_vertices = []
            for literal in clause:
                vertex = next_vertex
                next_vertex += 1
                clause_vertices.append(vertex)
                occurrences.append((vertex, clause_index, copy, literal))
                variable = abs(literal) - 1
                falsifying_assignment = 2 * variable + int(literal > 0)
                edges.add(tuple(sorted((vertex, falsifying_assignment))))
            for left, right in combinations(clause_vertices, 2):
                edges.add((left, right))
    for (left, _, _, literal_left), (right, _, _, literal_right) in combinations(occurrences, 2):
        if literal_left == -literal_right:
            edges.add((left, right))
    return next_vertex, tuple(sorted(edges))


def exhaustive_global_check(
    variables: int = 2, max_clauses: int = 3, copies_values: tuple[int, ...] = (1, 2)
) -> int:
    """Check every short formula over all nonempty width-one/two clauses."""
    literals = tuple(range(1, variables + 1)) + tuple(range(-1, -variables - 1, -1))
    clauses = tuple((literal,) for literal in literals) + tuple(combinations(literals, 2))
    checked = 0
    for clause_count in range(max_clauses + 1):
        for formula in product(clauses, repeat=clause_count):
            frozen = tuple(tuple(clause) for clause in formula)
            optimum = max2sat_optimum(frozen, variables)
            for copies in copies_values:
                order, edges = conflict_graph_bits(frozen, variables, copies)
                exact = independence_number(order, edges)
                expected = variables + copies * optimum
                if exact != expected:
                    raise AssertionError(
                        f"counterexample: phi={frozen}, K={copies}, "
                        f"alpha={exact}, expected={expected}"
                    )
                checked += 1
    return checked


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-arity", type=int, default=3)
    parser.add_argument("--global-check", action="store_true")
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parent / "results" / "max2sat_exhaustive.json",
    )
    args = parser.parse_args()
    gadgets = []
    for arity in range(1, args.max_arity + 1):
        minimum, count = exhaustive_or_gadgets(arity, arity)
        profile = canonical_clause_gadget_profile(arity)
        gadgets.append({
            "arity": arity,
            "minimum_auxiliary": minimum,
            "labelled_minimum_gadgets": count,
            "canonical_profile": list(profile),
        })
        print(f"OR arity={arity}: minimum_auxiliary={minimum}, labelled_gadgets={count}")
        print(f"  canonical_profile={profile}")
    checked = 0
    if args.global_check:
        checked = exhaustive_global_check()
        print(f"global identity: verified {checked} formula/copy instances")
    payload = {
        "problem": "MAX-2SAT-to-MIS",
        "gadget_model": "arbitrary auxiliary graph with falsifying-terminal attachments",
        "gadgets": gadgets,
        "global_identity_instances": checked,
        "counterexamples": 0,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
