import sys; sys.argv=['x']
import mk_sym as M
from _ldl import ldl_inertia
from fractions import Fraction as F
for K in (50,54):
  for D in (3,5,7):
    orbs=M.partitions_upto(D); n=len(orbs)
    A,Mm=M.reduced_closed(orbs,K)
    pa,na,za,_=ldl_inertia(Mm)
    pb,nb,zb,_=ldl_inertia(A)
    B=[[A[i][j]-4*Mm[i][j] for j in range(n)] for i in range(n)]
    pc,nc,zc,_=ldl_inertia(B)
    print(f"k={K} D={D} n={n}: M inertia(+{pa},-{na},0:{za})  A inertia(+{pb},-{nb},0:{zb})  A-4M inertia(+{pc},-{nc},0:{zc})")
