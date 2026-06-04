import sys; sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
from math import factorial as fac, lcm
import time
exec(open('frontier.py').read().split('print("Mapping')[0])  # precompute, gram_at, inertia_pos
from _ldl import ldl_inertia

D=7
orbs=M.partitions_upto(D); n=len(orbs)
print(f"D={D} n={n} orbs precompute...", flush=True)
t=time.time(); cache=precompute(orbs); print(f"  prep {time.time()-t:.0f}s", flush=True)

best=None
for K in (160,180,200,220,250,300,350):
    A,Mm=gram_at(orbs,cache,K)
    B=[[A[i][j]-4*Mm[i][j] for j in range(n)] for i in range(n)]
    pos,neg,zero,wit=ldl_inertia(B)
    if wit is None:
        print(f"K={K}: no positive pivot (M_K<=4)", flush=True); continue
    Nr=sum(wit[i]*A[i][j]*wit[j] for i in range(n) for j in range(n))
    Dr=sum(wit[i]*Mm[i][j]*wit[j] for i in range(n) for j in range(n))
    q=Nr/Dr
    print(f"K={K}: pos={pos} quotient={float(q):.5f}", flush=True)
    if best is None or q>best[1]:
        best=(K,q,wit,A,Mm)
print("BEST K=",best[0]," quotient=",float(best[1]),"=",best[1], flush=True)
