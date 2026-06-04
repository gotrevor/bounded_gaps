import sys; sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
exec(open('frontier.py').read().split('print("Mapping')[0])

def distinct_nonzero(p): return len(set(p))  # parts are nonzero
# img size = distinct nonzero values + 1 (for the 0). img<=3  <=> distinct nonzero <=2.
for D in (7,9,11):
    full=M.partitions_upto(D)
    orbs=[p for p in full if distinct_nonzero(p)<=2]
    n=len(orbs)
    cache=precompute(orbs)
    res=[]
    for K in (200,300,500,1000,2000):
        A,Mm=gram_at(orbs,cache,K)
        B=[[A[i][j]-4*Mm[i][j] for j in range(n)] for i in range(n)]
        res.append(f"k{K}:{'Y' if inertia_pos(B)>=1 else '.'}")
    print(f"D={D} img<=3 orbs={n}/{len(full)}: "+" ".join(res), flush=True)
