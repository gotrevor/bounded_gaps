"""
Symmetric-function reduction for polynomialMkF via a CLOSED FORM in k.

Reduces the Maynard Rayleigh quotient M_k(F) over symmetric polynomials F of
degree <= D to a (#orbits)x(#orbits) generalized eigenproblem whose matrix
entries are closed forms in k (falling factorials over a factorial). No monomial
enumeration -> scales to any k. This is the prototype of the Lean reduction:
each entry below corresponds to one combinatorial identity a Lean port must prove.

The orbit-sum closed forms (the heart of it). Place labelled parts of partitions
lam, mu into distinct slots of Fin k. The integrand depends only on the OVERLAP
pattern = a partial matching M pairing some lam-parts with some mu-parts (same
slot). With T = r_lam + r_mu - |M| occupied slots:

  denom entry  Mr[lam][mu](k) = (1/aut) * sum_M ff(k,T) * W(M)  /  (k+|lam|+|mu|)!
  numer entry  Ar[lam][mu](k) = (1/aut) * sum_M ff(k,T) * W(M)
                                  * ( Gocc(M) + (k-T)*g(0,0) )  /  (k+|lam|+|mu|+1)!

where
  aut    = aut(lam)*aut(mu)            (over-count of labelled vs unordered orbit)
  ff(k,T)= k*(k-1)*...*(k-T+1)         (ways to place T tokens in distinct slots)
  W(M)   = prod_{paired (a,b)} (a+b)! * prod_{lam-only a} a! * prod_{mu-only b} b!
  g(a,b) = (a+b+2)! / ((a+1)(b+1)(a+b)!)
  Gocc(M)= sum over occupied tokens of g(content)   [paired->g(a,b), solo->g(a,0)/g(0,b)]
  g(0,0) = 2   (every empty slot contributes the i = empty-coordinate term)

Validated against the brute monomial reduction (tools/mk/mk5_sym.py) at small k.

Usage:  python3 mk_sym.py [K] [DEG]   (default 50 3)
        python3 mk_sym.py validate    (cross-check vs brute at k=5..9)
"""
from fractions import Fraction as F
from math import factorial as fac
from functools import lru_cache
import itertools, sys


# ----- partitions / orbits ------------------------------------------------
def partitions_upto(D):
    out = [()]
    def parts(n, mx):
        if n == 0:
            yield (); return
        for first in range(min(n, mx), 0, -1):
            for rest in parts(n - first, first):
                yield (first,) + rest
    for n in range(1, D + 1):
        out.extend(parts(n, n))
    return out


def aut(lam):
    """Order of the stabilizer permuting equal parts: prod_v (mult_v)!."""
    from collections import Counter
    a = 1
    for c in Counter(lam).values():
        a *= fac(c)
    return a


def ff(k, t):
    """Falling factorial k*(k-1)*...*(k-t+1)."""
    r = 1
    for j in range(t):
        r *= (k - j)
    return r


def g(a, b):
    return F(fac(a + b + 2), (a + 1) * (b + 1) * fac(a + b))


def matchings(rl, rm):
    """Yield partial matchings between [0,rl) and [0,rm) as lists of (a,b) pairs."""
    for t in range(min(rl, rm) + 1):
        for La in itertools.combinations(range(rl), t):
            for Mb in itertools.combinations(range(rm), t):
                for perm in itertools.permutations(Mb):
                    yield list(zip(La, perm))


def _entry_sums(lam, mu, k):
    """Return (Sden, Snum) integer/rational orbit-sums (before the factorial div).
       Sden = sum_M ff(k,T) W(M);  Snum = sum_M ff(k,T) W(M) (Gocc + (k-T) g00)."""
    rl, rm = len(lam), len(mu)
    Sden = F(0); Snum = F(0)
    g00 = g(0, 0)
    for Mp in matchings(rl, rm):
        paired_l = {a for a, _ in Mp}
        paired_m = {b for _, b in Mp}
        t = len(Mp); T = rl + rm - t
        W = 1; Gocc = F(0)
        for a, b in Mp:
            W *= fac(lam[a] + mu[b]); Gocc += g(lam[a], mu[b])
        for a in range(rl):
            if a not in paired_l:
                W *= fac(lam[a]); Gocc += g(lam[a], 0)
        for b in range(rm):
            if b not in paired_m:
                W *= fac(mu[b]); Gocc += g(0, mu[b])
        f = ff(k, T)
        Sden += f * W
        Snum += f * W * (Gocc + (k - T) * g00)
    return Sden, Snum


def reduced_closed(orbs, k):
    """(#orbits)x(#orbits) reduced numerator Ar and denominator Mr at k, closed form."""
    m = len(orbs)
    A = [[F(0)] * m for _ in range(m)]
    Mm = [[F(0)] * m for _ in range(m)]
    au = [aut(o) for o in orbs]
    sz = [sum(o) for o in orbs]
    for a in range(m):
        for b in range(m):
            Sden, Snum = _entry_sums(orbs[a], orbs[b], k)
            dendiv = au[a] * au[b] * fac(k + sz[a] + sz[b])
            numdiv = au[a] * au[b] * fac(k + sz[a] + sz[b] + 1)
            Mm[a][b] = F(Sden) / F(dendiv)
            A[a][b] = F(Snum) / F(numdiv)
    return A, Mm


# ----- generalized Rayleigh sup (largest gen. eigenvalue), float ----------
def rayleigh_sup(A, M, want_vec=False):
    m = len(A)
    def gsolve(Mx, b):
        nn = len(b)
        Aug = [[float(Mx[i][j]) for j in range(nn)] + [float(b[i])] for i in range(nn)]
        for c in range(nn):
            piv = max(range(c, nn), key=lambda r: abs(Aug[r][c]))
            Aug[c], Aug[piv] = Aug[piv], Aug[c]
            pv = Aug[c][c]
            for r in range(nn):
                if r != c and Aug[r][c] != 0:
                    fr = Aug[r][c] / pv
                    for j in range(c, nn + 1):
                        Aug[r][j] -= fr * Aug[c][j]
        return [Aug[i][nn] / Aug[i][i] for i in range(nn)]
    def mv(Q, v):
        return [sum(float(Q[i][j]) * v[j] for j in range(m)) for i in range(m)]
    v = [1.0] * m; last = 0.0; cur = 0.0
    for _ in range(5000):
        w = gsolve(M, mv(A, v))
        nrm = max(abs(x) for x in w) or 1.0
        v = [x / nrm for x in w]
        num = sum(v[i] * float(A[i][j]) * v[j] for i in range(m) for j in range(m))
        den = sum(v[i] * float(M[i][j]) * v[j] for i in range(m) for j in range(m))
        cur = num / den
        if abs(cur - last) < 1e-14:
            break
        last = cur
    return (cur, v) if want_vec else cur


# ----- brute oracle (monomial enumeration, small k only) ------------------
def _brute(orbs, k):
    def mono_int(a):
        num = 1
        for x in a: num *= fac(x)
        return F(num, fac(k + sum(a)))
    def dir_slack(a, beta):
        n = len(a); num = 1
        for x in a: num *= fac(x)
        num *= fac(beta)
        return F(num, fac(n + sum(a) + beta))
    def numer(p, q):
        tot = F(0)
        for i in range(k):
            rem = [p[j] + q[j] for j in range(k) if j != i]
            tot += F(1, (p[i] + 1) * (q[i] + 1)) * dir_slack(rem, p[i] + q[i] + 2)
        return tot
    def reps(lam):
        if len(lam) > k: return []
        s = set()
        for sl in itertools.permutations(range(k), len(lam)):
            v = [0] * k
            for x, val in zip(sl, lam): v[x] = val
            s.add(tuple(v))
        return list(s)
    m = len(orbs); R = [reps(o) for o in orbs]
    A = [[F(0)] * m for _ in range(m)]; Mm = [[F(0)] * m for _ in range(m)]
    for a in range(m):
        for b in range(m):
            sn = F(0); sd = F(0)
            for p in R[a]:
                for q in R[b]:
                    sn += numer(p, q); sd += mono_int([p[i] + q[i] for i in range(k)])
            A[a][b] = sn; Mm[a][b] = sd
    return A, Mm


def validate():
    for D in (2, 3):
        orbs = partitions_upto(D)
        for k in range(max(2, max((len(o) for o in orbs), default=1)), 10):
            Ac, Mc = reduced_closed(orbs, k)
            Ab, Mb = _brute(orbs, k)
            ok = (Ac == Ab) and (Mc == Mb)
            print(f"D={D} k={k}: closed==brute {ok}"
                  + ("" if ok else f"  (A {Ac==Ab}, M {Mc==Mb})"))


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "validate":
        validate(); return
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    D = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    orbs = partitions_upto(D)
    A, Mm = reduced_closed(orbs, K)
    sup = rayleigh_sup(A, Mm)
    print(f"k={K}  deg<={D}  #orbits={len(orbs)}  ==>  M_{K} sup ≈ {sup:.6f}"
          f"   (need >4 for DHL[{K},2])")
    return sup


if __name__ == "__main__":
    main()
