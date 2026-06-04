import sys; sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
from math import factorial as fac
import time
exec(open('frontier.py').read().split('print("Mapping')[0])  # reuse helpers

def mk_value(A,Mm,n,lo=F(2),hi=F(12)):
    # bisect largest gen-eigenvalue: M_k = max lambda with inertia_pos(A-lam M)>=1
    for _ in range(22):
        mid=(lo+hi)/2
        B=[[A[i][j]-mid*Mm[i][j] for j in range(n)] for i in range(n)]
        if inertia_pos(B)>=1: lo=mid
        else: hi=mid
    return float((lo+hi)/2)

for D in (5,6,7):
    orbs=M.partitions_upto(D); n=len(orbs)
    t=time.time(); cache=precompute(orbs)
    out=[]
    for K in (105,150,200,300,500,1000,5000):
        A,Mm=gram_at(orbs,cache,K)
        out.append(f"k{K}:{mk_value(A,Mm,n):.3f}")
    print(f"D={D} n={n}: "+"  ".join(out)+f"   [{time.time()-t:.0f}s]", flush=True)
