import sys; sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
from math import factorial as fac

def inertia(B):
    """Exact LDL inertia (pos,neg,zero) of symmetric rational matrix B."""
    n=len(B); A=[[F(B[i][j]) for j in range(n)] for i in range(n)]
    d=[]
    for j in range(n):
        if A[j][j]==0:
            sw=next((k for k in range(j+1,n) if A[k][k]!=0),None)
            if sw is None: d.append(F(0)); continue
            A[j],A[sw]=A[sw],A[j]
            for r in range(n): A[r][j],A[r][sw]=A[r][sw],A[r][j]
        dj=A[j][j]; d.append(dj)
        for i in range(j+1,n):
            f=A[i][j]/dj
            if f==0: continue
            for c in range(j,n): A[i][c]-=f*A[j][c]
    return sum(1 for x in d if x>0),sum(1 for x in d if x<0),sum(1 for x in d if x==0)

def reaches4(orbs,k):
    A,Mm=M.reduced_closed(orbs,k)
    n=len(orbs); B=[[A[i][j]-4*Mm[i][j] for j in range(n)] for i in range(n)]
    p,ng,z=inertia(B); return p>=1,(p,ng,z)

def exact_sup(orbs,k,lo=F(1),hi=F(6),tol=F(1,50)):
    A,Mm=M.reduced_closed(orbs,k); n=len(orbs)
    def reach(c):
        B=[[A[i][j]-c*Mm[i][j] for j in range(n)] for i in range(n)]
        return inertia(B)[0]>=1   # exists eigenvalue > c  => sup > c
    while hi-lo>tol:
        mid=(lo+hi)/2
        if reach(mid): lo=mid
        else: hi=mid
    return (lo+hi)/2

K=int(sys.argv[1]) if len(sys.argv)>1 else 50
print(f"--- k={K}: corrected EXACT symmetric sups (low deg) ---")
for D in (1,2,3,4,5):
    orbs=M.partitions_upto(D)
    s=exact_sup(orbs,K)
    print(f"  deg<={D} (#orb={len(orbs)}): M_{K} sup ≈ {float(s):.3f}")
print(f"--- k={K}: does deg<=D reach 4? (exact inertia of A-4M) ---")
for D in (6,7,8,9,10,11,12):
    orbs=M.partitions_upto(D)
    ok,iner=reaches4(orbs,K)
    print(f"  deg<={D} (#orb={len(orbs)}): reaches 4 = {ok}   inertia(A-4M)={iner}")
    if ok: break
