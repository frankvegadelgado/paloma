"""Compare the source certificate with exhaustive assignment enumeration."""
from fractions import Fraction
from itertools import combinations, product
from source_certificate import certify


def audit(rows):
    variables = sorted({abs(l) for w,c in rows for l in c})
    def score(x):
        return sum(w for w,c in rows if any(x[abs(l)] == (l>0) for l in c))
    x, achieved, upper, dropped = certify(rows)
    optimum = max(score(dict(zip(variables, bits)))
                  for bits in product([False,True],repeat=len(variables)))
    assert score(x) == achieved <= optimum <= upper
    assert upper-achieved <= dropped
    assert 20*achieved < 19*upper or 20*achieved >= 19*optimum
    return achieved, upper, optimum


if __name__ == '__main__':
    shapes = [(1,2),(1,3),(2,3),(-1,2),(-2,1),(-3,1),(-1,3),
              (-2,3),(-3,2),(1,),(2,),(3,),(-1,),(-2,),(-3,)]
    count = 0
    for size in range(5):
        for cs in combinations(shapes,size):
            for weights in ([1]*size, [Fraction(i+1,3) for i in range(size)]):
                audit(list(zip(weights,cs)))
                count += 1
    audit([(2,()),(3,(1,-1)),(0,(1,2)),(4,(1,1)),(5,(-1,)),(1,(-1,))])
    witness = [(1,(1,3)),(1,(-2,)),(1,(-3,1))]
    assert audit(witness) == (2,3,3)
    assert audit(witness+[(17,(4,))]) == (19,20,20)
    print(f'{count+3} source certificates checked against exhaustive optima.')
