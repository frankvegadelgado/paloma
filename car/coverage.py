"""Which values a = alpha/n are covered for 83/84 on d-regular T_H, d = 3..30?

An independent set of size s works when  B + 84 s >= 83 alpha,  B = beta*n,
beta = (3d+2)/2, a = alpha/n in [0, 1/2].  Branches (all proved bounds):
  trivial : s = 0                      -> 83 a <= beta
  BF      : s >= 5 alpha/(d+3)         -> 84*5a/(d+3) >= 83a - beta
  cut     : Goemans-Williamson rounding of the SDP (opt cut fraction >= 2a):
            cut fraction f >= arccos(1-4a)/pi  (valid for 2a >= 0.845),
            then |I|/n >= (1-(1-f)d/2)/2       -> 84*that >= 83a - beta
Prints, for each d, the uncovered intervals of a (empty list = fully covered).
Usage: python coverage.py [step]       (default step 1e-5)
"""
import math
import sys

STEP = float(sys.argv[1]) if len(sys.argv) > 1 else 1e-5
X0 = 0.845


def covered(d, a):
    beta = (3 * d + 2) / 2
    need = 83 * a - beta
    if need <= 0:
        return True
    if 84 * 5 * a / (d + 3) >= need:
        return True
    if 2 * a >= X0:
        f = math.acos(1 - 4 * a) / math.pi
        s = (1 - (1 - f) * d / 2) / 2
        if 84 * s >= need:
            return True
    return False


for d in range(3, 31):
    gaps, start, a, k = [], None, 0.0, 0
    while a <= 0.5 + 1e-12:
        c = covered(d, a)
        if not c and start is None:
            start = a
        if c and start is not None:
            gaps.append((start, a - STEP)); start = None
        k += 1
        a = k * STEP
    if start is not None:
        gaps.append((start, 0.5))
    print(f"d={d:2d}  uncovered: " +
          (", ".join(f"[{x:.4f},{y:.4f}]" for x, y in gaps) if gaps else "none"))
