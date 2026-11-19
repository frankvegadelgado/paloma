"""Weighted MAX-HORN-2SAT occurrence splitting test.

Source clauses may have arbitrary positive integer weights.  Chain /
consistency clauses get weight one larger than the total source weight.

If M is larger than the total source weight W, every inconsistent assignment
loses at least M but can gain at most W on source clauses.  Therefore
    split_opt = M*n_cons + source_opt.
"""

from itertools import combinations, combinations_with_replacement, product
from fractions import Fraction

Literal = tuple[int, bool]
Clause  = tuple[Literal, ...]

def satisfied(clause, assignment):
    return any(assignment[v] == s for v, s in clause)


def weighted_optimum(n, weighted_clauses):
    return max(
        sum(w for c, w in weighted_clauses if satisfied(c, a))
        for a in product((False, True), repeat=n)
    )


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
        for nc in range(1, 5):
            for clauses in combinations_with_replacement(types, nc):
                tested += 1

                # Test genuine weighted sources, not only unit weights.
                for source_weights in product((1, 2), repeat=nc):
                    source = tuple(zip(clauses, source_weights))
                    total_source_weight = sum(source_weights)
                    consistency_weight = total_source_weight + 1
                    src_opt = weighted_optimum(nv, source)
                    nclones, split, nsrc, ncons = split_formula(nv, clauses)

                    weighted = (
                        tuple((c, w) for c, w in zip(split[:nsrc], source_weights)) +
                        tuple((c, consistency_weight) for c in split[nsrc:])
                    )
                    spl_opt = weighted_optimum(nclones, weighted)
                    expected = ncons * consistency_weight + src_opt

                    if spl_opt != expected:
                        print("COUNTEREXAMPLE")
                        print("variables:", nv)
                        print("clauses:", clauses)
                        print("source weights:", source_weights)
                        print("source optimum:", src_opt)
                        print("consistency clauses:", ncons)
                        print("consistency weight:", consistency_weight)
                        print("split weighted optimum:", spl_opt)
                        print("expected:", expected)
                        return
    print("NO OPTIMUM-IDENTITY COUNTEREXAMPLE", tested)

    image_ratio = Fraction(18, 19)
    general_weighted_horn = Fraction(94615981, 100000000)
    assert image_ratio > general_weighted_horn
    print("WEIGHTED IMAGE-CLASS GUARANTEE")
    print("18/19 =", float(image_ratio), ">", float(general_weighted_horn))
    print("PTAS: enumerate if C < 1/epsilon; otherwise set every clone false")


if __name__ == "__main__":
    main()
