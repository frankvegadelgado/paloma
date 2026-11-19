"""Exhaustively test quantitative cyclic occurrence splitting for MAX-HORN-2SAT.

Polarity convention: a Horn clause contains at most one negative literal.
Every source occurrence receives a fresh clone, and the clones of each source
variable are linked by the directed implication cycle
    (not z_i or z_(i+1)).
Thus every clone occurs once in a source clause and twice in the cycle.
"""

from itertools import combinations, combinations_with_replacement, product


Literal = tuple[int, bool]  # (variable, satisfying Boolean value)
Clause = tuple[Literal, ...]


def satisfied(clause: Clause, assignment: tuple[bool, ...]) -> bool:
    return any(assignment[var] == sign for var, sign in clause)


def optimum(variable_count: int, clauses: tuple[Clause, ...]) -> int:
    return max(
        sum(satisfied(clause, assignment) for clause in clauses)
        for assignment in product((False, True), repeat=variable_count)
    )


def best_assignment(variable_count: int, clauses: tuple[Clause, ...]):
    return max(
        product((False, True), repeat=variable_count),
        key=lambda assignment: sum(
            satisfied(clause, assignment) for clause in clauses
        ),
    )


def split_formula(variable_count: int, clauses: tuple[Clause, ...]):
    occurrences: list[list[tuple[int, bool]]] = [[] for _ in range(variable_count)]
    split_clauses: list[Clause] = []
    clone_count = 0
    for clause in clauses:
        split_clause = []
        for variable, sign in clause:
            clone = clone_count
            clone_count += 1
            occurrences[variable].append((clone, sign))
            split_clause.append((clone, sign))
        split_clauses.append(tuple(split_clause))

    consistency_count = 0
    for signed_clones in occurrences:
        if not signed_clones:
            continue
        negative = [clone for clone, sign in signed_clones if not sign]
        positive = [clone for clone, sign in signed_clones if sign]
        clones = []
        while negative or positive:
            if negative:
                clones.append(negative.pop())
            if positive:
                clones.append(positive.pop())
        for index, clone in enumerate(clones):
            successor = clones[(index + 1) % len(clones)]
            split_clauses.append(((clone, False), (successor, True)))
            consistency_count += 1
    return clone_count, tuple(split_clauses), consistency_count


def horn_clause_types(variable_count: int) -> tuple[Clause, ...]:
    literals = tuple(product(range(variable_count), (False, True)))
    unary = [(literal,) for literal in literals]
    binary = []
    for left, right in combinations(literals, 2):
        if left[0] == right[0]:
            continue
        clause = (left, right)
        if sum(not sign for _, sign in clause) <= 1:
            binary.append(clause)
    return tuple(unary + binary)


def main() -> None:
    tested = 0
    for variable_count in (1, 2, 3):
        types = horn_clause_types(variable_count)
        for clause_count in range(1, 6):
            for clauses in combinations_with_replacement(types, clause_count):
                tested += 1
                source_optimum = optimum(variable_count, clauses)
                clone_count, split, consistency_count = split_formula(
                    variable_count, clauses
                )
                split_optimum = optimum(clone_count, split)
                expected = consistency_count + source_optimum
                if split_optimum != expected:
                    print("COUNTEREXAMPLE")
                    print("variables:", variable_count)
                    print("clauses:", clauses)
                    print("source optimum:", source_optimum)
                    print("consistency clauses:", consistency_count)
                    print("split optimum:", split_optimum)
                    witness = best_assignment(clone_count, split)
                    print("split witness:", witness)
                    print(
                        "split clause values:",
                        tuple(satisfied(clause, witness) for clause in split),
                    )
                    print("expected:", expected)
                    return
    print("NO COUNTEREXAMPLE", tested)


if __name__ == "__main__":
    main()
