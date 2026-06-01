"""
Validate a CONTINGENCY-TABLE closed form for the single-orbit core sum

    S(alpha, beta) := sum_{p in orbit(alpha)} prod_i (p_i + beta_i)!

(orbit = distinct rearrangements of the length-k vector alpha, beta FIXED), against
brute force. This is the object the Lean tower reduced everything to
(orbitPair_core_const + orbitPair_denominator_eq + group_sum_eq_stab_smul_orbitSum).

Claim:
    S(alpha,beta) = sum_X  [ prod_t  n_t! / prod_u x_{u,t}! ] * prod_{u,t} ((c_u+b_t)!)^{x_{u,t}}
where
    c_u (mult m_u) = distinct alpha-values over all k slots (INCLUDING 0),
    b_t (mult n_t) = distinct beta-values over all k slots (INCLUDING 0),
    X ranges over r x s nonneg-int matrices with column sums n_t and row sums m_u
      (x_{u,t} = #slots with alpha-value c_u AND beta-value b_t).
    count(X) = prod_t multinomial(n_t; x_{.,t})   [ways to fill each beta-group]

If this matches brute, the Lean kernel should target the contingency-table form
(margin-constrained nat matrices) rather than the bespoke partial-matching type.
"""
from fractions import Fraction as F
from math import factorial as fac
from collections import Counter
import itertools


def brute(alpha, beta):
    k = len(alpha)
    total = 0
    seen = set()
    for p in set(itertools.permutations(alpha)):  # distinct rearrangements
        w = 1
        for i in range(k):
            w *= fac(p[i] + beta[i])
        total += w
    return total


def column_fillings(n_t, r):
    """All length-r nonneg vectors summing to n_t (one beta-group's column of X)."""
    if r == 1:
        yield (n_t,)
        return
    for first in range(n_t + 1):
        for rest in column_fillings(n_t - first, r - 1):
            yield (first,) + rest


def contingency(alpha, beta):
    cval = sorted(set(alpha)); r = len(cval)
    bval = sorted(set(beta));  s = len(bval)
    m = [sum(1 for a in alpha if a == cval[u]) for u in range(r)]  # row sums
    n = [sum(1 for b in beta  if b == bval[t]) for t in range(s)]  # col sums
    total = F(0)
    # choose each column (beta-group t) independently, then enforce row-sum margins
    for cols in itertools.product(*[list(column_fillings(n[t], r)) for t in range(s)]):
        # cols[t][u] = x_{u,t}
        row = [sum(cols[t][u] for t in range(s)) for u in range(r)]
        if row != m:
            continue
        term = F(1)
        for t in range(s):
            mult = fac(n[t])
            for u in range(r):
                mult //= fac(cols[t][u])
            term *= mult
        for t in range(s):
            for u in range(r):
                term *= fac(cval[u] + bval[t]) ** cols[t][u]
        total += term
    return total


def rand_vec(k, vals, rng):
    return tuple(rng.choice(vals) for _ in range(k))


if __name__ == "__main__":
    import random
    rng = random.Random(12345)
    cases = [
        ((1, 0, 0), (1, 0, 0)),
        ((2, 1, 0, 0), (1, 1, 0, 0)),
        ((1, 1, 0, 0, 0), (2, 0, 0, 0, 0)),
        ((3, 1, 0, 0), (2, 1, 1, 0)),
        ((1, 1, 1, 0, 0), (1, 1, 0, 0, 0)),
    ]
    # plus random small cases
    for _ in range(20):
        k = rng.randint(3, 6)
        a = rand_vec(k, [0, 0, 1, 2], rng)
        b = rand_vec(k, [0, 0, 1, 3], rng)
        cases.append((a, b))

    allok = True
    for alpha, beta in cases:
        bf = brute(alpha, beta)
        cf = contingency(alpha, beta)
        ok = (F(bf) == cf)
        allok = allok and ok
        print(f"{'OK ' if ok else 'BAD'} alpha={alpha} beta={beta}  brute={bf}  closed={cf}")
    print("ALL MATCH" if allok else "MISMATCH FOUND")
