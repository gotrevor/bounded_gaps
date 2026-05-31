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
def gsolve(M,b):  # float Gaussian elim, M list-of-lists
    n=len(b); A=[row[:]+[b[i]] for i,row in enumerate(M)]
    for c in range(n):
        piv=max(range(c,n),key=lambda r:abs(A[r][c])); A[c],A[piv]=A[piv],A[c]
        pv=A[c][c]
        for r in range(n):
            if r!=c and A[r][c]!=0:
                f=A[r][c]/pv
                for j in range(c,n+1): A[r][j]-=f*A[c][j]
    return [A[i][n]/A[i][i] for i in range(n)]
def matvec(Mf,v): return [sum(Mf[i][j]*v[j] for j in range(len(v))) for i in range(len(v))]
for D in [1,2,3]:
    B=basis(D); n=len(B)
    Aq=[[numer(B[a],B[b]) for b in range(n)] for a in range(n)]
    Mq=[[denom(B[a],B[b]) for b in range(n)] for a in range(n)]
    Af=[[float(x) for x in row] for row in Aq]
    Mf=[[float(x) for x in row] for row in Mq]
    v=[1.0]*n
    for _ in range(300):
        w=gsolve(Mf,matvec(Af,v))
        nrm=max(abs(x) for x in w); v=[x/nrm for x in w]
    num=sum(v[i]*Af[i][j]*v[j] for i in range(n) for j in range(n))
    den=sum(v[i]*Mf[i][j]*v[j] for i in range(n) for j in range(n))
    print(f"D={D} dim={n} M5_sup≈{num/den:.6f}")
    if D==2:
        # rationalize witness, verify exactly
        vr=[F(x).limit_denominator(60) for x in v]
        Nr=sum(vr[i]*Aq[i][j]*vr[j] for i in range(n) for j in range(n))
        Dr=sum(vr[i]*Mq[i][j]*vr[j] for i in range(n) for j in range(n))
        ratio=Nr/Dr
        print(f"  exact rational ratio = {ratio} = {float(ratio):.6f}  >2? {ratio>2}")
        terms=[(B[i],vr[i]) for i in range(n) if vr[i]!=0]
        print(f"  witness terms ({len(terms)}):")
        for mi,co in terms: print(f"    {mi}: {co}")
