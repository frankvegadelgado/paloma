"""Exhaustive audits for the graph-transfer section. Standard Python 3."""
from itertools import combinations, product
from collections import defaultdict, Counter


def independent_sets(n, edges):
    conflicts = [(1 << i) | (1 << j) for i, j in edges]
    for mask in range(1 << n):
        if all(mask & pair != pair for pair in conflicts):
            yield mask


def unary_search():
    # Two labelled terminals 0,1. Profile includes selected terminals.
    for n in range(2, 6):
        pairs = list(combinations(range(n), 2))
        matches = 0
        total = 0
        for flags in range(1 << len(pairs)):
            edges = [e for k, e in enumerate(pairs) if flags >> k & 1]
            deg = Counter(i for e in edges for i in e)
            if max(deg.values(), default=0) > 3:
                continue
            total += 1
            profile = [-1] * 4
            for mask in independent_sets(n, edges):
                state = mask & 3
                profile[state] = max(profile[state], mask.bit_count())
            if profile == [1, 1, 1, 2]:
                matches += 1
        print(f'{n} vertices: {matches}/{total} have the path profile')


def weighted_graph(clauses):
    weights, edges, rings, witnesses = [], set(), defaultdict(list), []
    heavy = 1 + sum(w for w, _ in clauses)
    def edge(i, j):
        assert i != j
        edges.add(tuple(sorted((i, j))))
    for w, clause in clauses:
        row = []
        for literal in clause:
            f = len(weights)
            t, witness = f + 1, f + 2
            weights.extend([heavy, heavy, w])
            rings[abs(literal)].append((f, t))
            edge(f, t)
            edge(witness, f if literal > 0 else t)
            row.append(witness)
        if len(row) == 2:
            edge(*row)
        witnesses.append(row)
    for ring in rings.values():
        for i, (_, t) in enumerate(ring):
            edge(t, ring[(i + 1) % len(ring)][0])
    assert max(Counter(i for e in edges for i in e).values(), default=0) <= 3
    return weights, edges, rings, heavy


def audit(clauses):
    weights, edges, rings, heavy = weighted_graph(clauses)
    base = heavy * sum(map(len, rings.values()))
    def score(x):
        return sum(w for w, c in clauses if any(x[abs(l)] == (l > 0) for l in c))
    opt = max(score(dict(zip(rings, a))) for a in product([False, True], repeat=len(rings)))
    best = 0
    for mask in independent_sets(len(weights), edges):
        value = sum(w for i, w in enumerate(weights) if mask >> i & 1)
        # An incomplete ring permits any decoded assignment globally.
        full = all(mask & ((1 << f) | (1 << t)) for ring in rings.values() for f,t in ring)
        x = {v: bool(full and mask >> ring[0][1] & 1) for v, ring in rings.items()}
        assert base + score(x) >= value
        best = max(best, value)
    assert best == base + opt


def cubes():
    edges = [(u, u ^ bit) for u in range(8) for bit in (1,2,4) if u < u ^ bit]
    sets = list(independent_sets(8, edges))
    maximal = [s for s in sets if all((s | (1 << u)) not in sets for u in range(8) if not s >> u & 1)]
    assert 129 in maximal and max(s.bit_count() for s in sets) == 4
    assert 7*14 >= 6*16 and 84*190 >= 83*192 and 84*62 < 83*64


if __name__ == '__main__':
    unary_search()
    cubes()
    literals = [-2, -1, 1, 2]
    shapes = [(l,) for l in literals] + [(u,v) for u in literals for v in literals if max(u,v)>0]
    for c, d in product(shapes, repeat=2):
        audit([(1,c),(3,d)])
    audit([])
    audit([(0,(1,)),(2,(-1,)),(3,(1,))])
    print(f'Checked {len(shapes)**2 + 2} weighted formulas and the four-cube witness.')

    for n, edges in [
        (4, list(combinations(range(4), 2))),
        (6, [(i,j) for i in range(3) for j in range(3,6)]),
        (8, [(u,u ^ b) for u in range(8) for b in (1,2,4) if u < u ^ b]),
    ]:
        for weights in [[1]*len(edges), [4]*len(edges), [1 if i%2 else 9 for i in range(len(edges))]]:
            W = sum(weights)
            alpha = max(s.bit_count() for s in independent_sets(n,edges))
            best = 0
            for mask in range(1 << n):
                internal = [(i,j,w) for (i,j),w in zip(edges,weights)
                            if mask >> i & 1 and mask >> j & 1]
                score = W + mask.bit_count() - sum(w for _,_,w in internal)
                repaired = mask
                for i,_,_ in internal:
                    repaired &= ~(1 << i)
                assert W + repaired.bit_count() >= score
                assert all(not (repaired >> i & repaired >> j & 1) for i,j in edges)
                best = max(score,best)
            assert best == W + alpha
            for mask in independent_sets(n,edges):
                if 20*mask.bit_count() >= 17*alpha:
                    assert 80*(W+mask.bit_count()) >= 77*best
                    if W >= 6*n:
                        assert 260*(W+mask.bit_count()) >= 257*best
    print('Checked all assignments for nine cubic weighted source instances.')
