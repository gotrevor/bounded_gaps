import sys; sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
import time

def inertia_pos(B):
    """Return number of positive pivots of symmetric B via LDL (exact)."""
    n=len(B); A=[[F(B[i][j]) for j in range(n)] for i in range(n)]
    d=[F(0)]*n
    for j in range(n):
        if A[j][j]==0:
            sw=next((k for k in range(j,n) if A[k][k]!=0),None)
            if sw is None: d[j]=F(0); continue
            if sw!=j:
                A[j],A[sw]=A[sw],A[j]
                for r in range(n): A[r][j],A[r][sw]=A[r][sw],A[r][j]
        d[j]=A[j][j]
        for i in range(j+1,n):
            f=A[i][j]/d[j]
            for c in range(j,n): A[i][c]-=f*A[j][c]
    return sum(1 for x in d if x>0)

for D in (9,11,13):
  for K in (54,):
    t=time.time()
    orbs=M.partitions_upto(D); n=len(orbs)
    A,Mm=M.reduced_closed(orbs,K)
    B=[[A[i][j]-4*Mm[i][j] for j in range(n)] for i in range(n)]
    p=inertia_pos(B)
    print(f"k={K} D={D} n={n}: pos-pivots(A-4M)={p}  => M_{K}>4: {p>=1}   [{time.time()-t:.1f}s]", flush=True)
