from fractions import Fraction as F
from math import factorial as fac
import itertools
k=5
def mono_int(a):
    num=1
    for x in a: num*=fac(x)
    return F(num,fac(k+sum(a)))
def dir_slack(a,beta):
    n=len(a); num=1
    for x in a: num*=fac(x)
    num*=fac(beta)
    return F(num,fac(n+sum(a)+beta))
def numer(p,q):
    tot=F(0); pq=[p[i]+q[i] for i in range(k)]
    for i in range(k):
        rem=pq[:i]+pq[i+1:]
        tot+=F(1,(p[i]+1)*(q[i]+1))*dir_slack(rem,p[i]+q[i]+2)
    return tot
def denom(p,q): return mono_int([p[i]+q[i] for i in range(k)])
def basis(D):
    out=set()
    for deg in range(D+1):
        for c in itertools.combinations_with_replacement(range(k),deg):
            e=[0]*k
            for j in c: e[j]+=1
            out.add(tuple(e))
    return sorted(out)
B=basis(3); n=len(B)
# orbit = sorted nonzero-exponent multiset (partition)
def orbit(m): return tuple(sorted([x for x in m if x>0],reverse=True))
orbs=sorted(set(orbit(m) for m in B))
oidx={o:i for i,o in enumerate(orbs)}
print("orbits:",orbs)
# symmetric subspace: coeff vector c over orbits -> full vector v[m]=c[orbit(m)]
def full(c): return [c[oidx[orbit(m)]] for m in B]
Aq=[[numer(B[a],B[b]) for b in range(n)] for a in range(n)]
Mq=[[denom(B[a],B[b]) for b in range(n)] for a in range(n)]
m=len(orbs)
# reduced forms on symmetric space
def reduced(Q):
    R=[[F(0)]*m for _ in range(m)]
    for a in range(n):
        oa=oidx[orbit(B[a])]
        for b in range(n):
            ob=oidx[orbit(B[b])]
            R[oa][ob]+=Q[a][b]
    return R
# Wait: quadratic form v^T Q v with v=full(c) = sum_{a,b} c[oa]c[ob] Q[a][b] = c^T R c with R as above
Ar=reduced(Aq); Mr=reduced(Mq)
# float solve generalized eig on m-dim
def gsolve(M,b):
    nn=len(b); Aug=[[float(M[i][j]) for j in range(nn)]+[float(b[i])] for i in range(nn)]
    for c in range(nn):
        piv=max(range(c,nn),key=lambda r:abs(Aug[r][c])); Aug[c],Aug[piv]=Aug[piv],Aug[c]
        pv=Aug[c][c]
        for r in range(nn):
            if r!=c and Aug[r][c]!=0:
                f=Aug[r][c]/pv
                for j in range(c,nn+1): Aug[r][j]-=f*Aug[c][j]
    return [Aug[i][nn]/Aug[i][i] for i in range(nn)]
def mv(Q,v): return [sum(float(Q[i][j])*v[j] for j in range(len(v))) for i in range(len(v))]
v=[1.0]*m
for _ in range(500):
    w=gsolve(Mr,mv(Ar,v)); nrm=max(abs(x) for x in w); v=[x/nrm for x in w]
num=sum(v[i]*float(Ar[i][j])*v[j] for i in range(m) for j in range(m))
den=sum(v[i]*float(Mr[i][j])*v[j] for i in range(m) for j in range(m))
print(f"symmetric M5 sup ≈ {num/den:.6f}")
# try rationalizations at increasing denominators until exact ratio>2 with small denom
for Dl in [10,12,15,20,24,30,40,60]:
    cr=[F(x).limit_denominator(Dl) for x in v]
    Nr=sum(cr[i]*Ar[i][j]*cr[j] for i in range(m) for j in range(m))
    Dr=sum(cr[i]*Mr[i][j]*cr[j] for i in range(m) for j in range(m))
    r=Nr/Dr
    ok=r>2
    if ok:
        # clear denominators -> integer coeffs
        from math import lcm
        L=1
        for x in cr: L=lcm(L,x.denominator)
        ic=[int(x*L) for x in cr]
        print(f"denom<= {Dl}: ratio={r} ≈{float(r):.6f} >2 ✓  orbit coeffs(scaled x{L}): {dict(zip(orbs,ic))}")
        break
    else:
        print(f"denom<= {Dl}: ratio≈{float(r):.6f} >2? {ok}")
