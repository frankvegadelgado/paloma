"""Partial Weighted MAX-HORN-2SAT occurrence-splitting test.

Source clauses retain their original objective weights.  The cyclic clauses
    (not x_i or x_{i+1})
are mandatory hard constraints and contribute zero to the objective.

Under this hard-clause semantics, feasible clone assignments are exactly the
consistent lifts of source assignments, so the transformation is exactly
objective- and approximation-ratio preserving.
"""

from itertools import combinations, combinations_with_replacement, product

Literal = tuple[int, bool]
Clause  = tuple[Literal, ...]

SOURCE_WEIGHT = 1


def satisfied(clause, assignment):
    return any(assignment[v] == s for v, s in clause)


def feasible_assignments(n, hard_clauses=()):
    return (
        assignment
        for assignment in product((False, True), repeat=n)
        if all(satisfied(clause, assignment) for clause in hard_clauses)
    )


def objective_value(weighted_clauses, assignment):
    return sum(w for clause, w in weighted_clauses if satisfied(clause, assignment))


def weighted_optimum(n, weighted_clauses, hard_clauses=()):
    return max(
        objective_value(weighted_clauses, assignment)
        for assignment in feasible_assignments(n, hard_clauses)
    )


def attainable_values(n, weighted_clauses, hard_clauses=()):
    return {
        objective_value(weighted_clauses, assignment)
        for assignment in feasible_assignments(n, hard_clauses)
    }


def split_formula(variable_count, clauses):
    occurrences   = [[] for _ in range(variable_count)]
    split_clauses = []
    clone_count   = 0
    for clause in clauses:
        sc = []
        for v, s in clause:
            occurrences[v].append((clone_count, s))
            sc.append((clone_count, s))
            clone_count += 1
        split_clauses.append(tuple(sc))
    n_source = len(split_clauses)

    n_cons = 0
    for signed in occurrences:
        if not signed:
            continue
        negative = [c for c, s in signed if not s]
        positive = [c for c, s in signed if s]
        clones   = []
        while negative or positive:
            if negative:
                clones.append(negative.pop())
            if positive:
                clones.append(positive.pop())
        for i, c in enumerate(clones):
            successor = clones[(i + 1) % len(clones)]
            split_clauses.append(((c, False), (successor, True)))
            n_cons += 1

    return clone_count, tuple(split_clauses), n_source, n_cons


def horn_clause_types(variable_count):
    lits  = tuple(product(range(variable_count), (False, True)))
    unary = [(l,) for l in lits]
    binary = []
    for a, b in combinations(lits, 2):
        if a[0] == b[0]:
            continue
        if sum(not s for _, s in (a, b)) <= 1:
            binary.append((a, b))
    return tuple(unary + binary)


def main():
    tested = 0
    for nv in (1, 2, 3):
        types = horn_clause_types(nv)
        for nc in range(1, 6):
            for clauses in combinations_with_replacement(types, nc):
                tested += 1

                src_opt = weighted_optimum(
                    nv, tuple((c, SOURCE_WEIGHT) for c in clauses)
                )
                nclones, split, nsrc, ncons = split_formula(nv, clauses)

                source_weighted = tuple((c, SOURCE_WEIGHT) for c in clauses)
                split_weighted = tuple(
                    (c, SOURCE_WEIGHT) for c in split[:nsrc]
                )
                hard_consistency = split[nsrc:]
                spl_opt = weighted_optimum(
                    nclones, split_weighted, hard_consistency
                )
                expected = src_opt

                # Equality of all attainable objective values is stronger than
                # equality of optima and directly checks ratio preservation.
                source_values = attainable_values(nv, source_weighted)
                split_values = attainable_values(
                    nclones, split_weighted, hard_consistency
                )

                if spl_opt != expected or split_values != source_values:
                    print("COUNTEREXAMPLE")
                    print("variables:", nv)
                    print("clauses:", clauses)
                    print("source optimum:", src_opt)
                    print("hard consistency clauses:", ncons)
                    print("split partial-weighted optimum:", spl_opt)
                    print("expected:", expected)
                    print("source attainable values:", sorted(source_values))
                    print("split attainable values:", sorted(split_values))
                    return
    print("NO HARD-CONSISTENCY COUNTEREXAMPLE", tested)
    print("OPTIMUM AND ALL ATTAINABLE OBJECTIVE VALUES PRESERVED")


if __name__ == "__main__":
    main()
