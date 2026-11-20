"""Certify the assignment of a weighted width-two formula by a switched min cut.

Input (weight, literals) pairs use signed DIMACS integers. Use int or Fraction
weights for exact arithmetic. The returned bounds are in original score units.
"""
from collections import defaultdict, deque
from fractions import Fraction


def forest_switch(pairs, variables):
    parent = {v: v for v in variables}
    adjacent = defaultdict(list)

    def root(v):
        while v != parent[v]:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for weight, (a, b) in sorted(pairs, reverse=True):
        i, j = abs(a), abs(b)
        ri, rj = root(i), root(j)
        if ri == rj:
            continue
        parent[ri] = rj
        parity = (a > 0) == (b > 0)
        adjacent[i].append((j, parity))
        adjacent[j].append((i, parity))

    flip = {}
    for v in sorted(variables):
        if v in flip:
            continue
        flip[v] = False
        stack = [v]
        while stack:
            i = stack.pop()
            for j, parity in adjacent[i]:
                if j not in flip:
                    flip[j] = flip[i] ^ parity
                    stack.append(j)
    return flip


def mincut(capacity, source, sink):
    """Edmonds--Karp. Return reachable vertices and exact maximum flow."""
    total = 0
    while True:
        prior = {source: source}
        queue = deque([source])
        while queue and sink not in prior:
            u = queue.popleft()
            for v, available in capacity[u].items():
                if available > 0 and v not in prior:
                    prior[v] = u
                    queue.append(v)
        if sink not in prior:
            return prior.keys(), total
        path = []
        v = sink
        while v != source:
            path.append((prior[v], v))
            v = prior[v]
        delta = min(capacity[u][v] for u,v in path)
        for u,v in path:
            capacity[u][v] -= delta
            capacity[v][u] += delta
        total += delta


def certify(clauses):
    """Return (assignment, achieved score, upper bound, dropped weight)."""
    rows = []
    variables = set()
    constant = 0
    for w, literals in clauses:
        if not isinstance(w, (int, Fraction)) or w < 0:
            raise ValueError('weights must be nonnegative exact rationals')
        literals = tuple(literals)
        if len(literals) > 2 or any(type(l) is not int or not l for l in literals):
            raise ValueError('expected at most two nonzero signed integers')
        variables.update(map(abs, literals))
        c = tuple(dict.fromkeys(literals))
        if len(c) == 2 and c[0] == -c[1]:
            constant += w
        elif c and w:
            rows.append((w,c))

    flip = forest_switch([(w,c) for w,c in rows if len(c)==2], variables)
    source, sink = 0, -1
    capacity = defaultdict(lambda: defaultdict(int))
    upper = constant + sum(w for w,c in rows)
    dropped = 0
    for w,c in rows:
        d = tuple(-l if flip[abs(l)] else l for l in c)
        if len(d) == 1:
            a = d[0]
            u,v = (source,a) if a > 0 else (-a,sink)
        elif (d[0]>0) == (d[1]>0):
            dropped += w
            continue
        else:
            neg, pos = sorted(d)
            u,v = -neg,pos
        capacity[u][v] += w
        capacity[v][u] += 0
    side, flow = mincut(capacity,source,sink)
    assignment = {v: (v in side) ^ flip[v] for v in variables}
    def value(x):
        return constant + sum(w for w,c in rows if any(x[abs(l)] == (l>0) for l in c))

    candidates = (assignment, dict.fromkeys(variables, True), dict.fromkeys(variables, False))
    best = max(candidates, key=value)
    return best, value(best), upper-flow, dropped
