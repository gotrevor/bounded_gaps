import sys; sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
exec(open('frontier.py').read().split('print("Mapping')[0])

def inertia_pos(B):
    n=len(B); A=[[F(B[i][j]) for j in range(n)] for i in range(n)]; d=[F(0)]*n
    for j in range(n):
        if A[j][j]==0:
            sw=next((kk for kk in range(j,n) if A[kk][kk]!=0),None)
            if sw is None: d[j]=F(0); continue
            if sw!=j:
                A[j],A[sw]=A[sw],A[j]
                for r in range(n): A[r][j],A[r][sw]=A[r][sw],A[r][j]
        d[j]=A[j][j]
        for i in range(j+1,n):
            f=A[i][j]/d[j]
            for c in range(j,n): A[i][c]-=f*A[j][c]
    return sum(1 for x in d if x>0)

def mk_sup(orbs, K, cache_full, idx):
    sub=[orbs[i] for i in idx]
    n=len(sub)
    A=[[0]*n for _ in range(n)];Mm=[[0]*n for _ in range(n)]
    Af,Mf=cache_full
    for x,i in enumerate(idx):
        for y,j in enumerate(idx):
            A[x][y]=Af[i][j];Mm[x][y]=Mf[i][j]
    lo,hi=F(2),F(12)
    for _ in range(20):
        mid=(lo+hi)/2
        B=[[A[i][j]-mid*Mm[i][j] for j in range(n)] for i in range(n)]
        if inertia_pos(B)>=1: lo=mid
        else: hi=mid
    return float((lo+hi)/2)

D=7; orbs=M.partitions_upto(D); n=len(orbs)
def dn(p): return len(set(p))
img4=[i for i in range(n) if dn(orbs[i])>=3]   # >=3 distinct nonzero -> img>=4
print("img>=4 orbits:", [orbs[i] for i in img4])
K=300
cache=precompute(orbs)
Af,Mf=gram_at(orbs,cache,K)
# greedy: start from img4 (essential), add orbits that most raise the sup
chosen=list(img4)
import itertools
# try: img4 + all 1-value orbits (single part, [d]) + 2-value
singles=[i for i in range(n) if dn(orbs[i])==1]   # [a^j] one distinct value
twos=[i for i in range(n) if dn(orbs[i])==2]
print(f"counts: singles={len(singles)} twos={len(twos)} img4={len(img4)}")
# greedy add
pool=[i for i in range(n) if i not in chosen]
cur=mk_sup(orbs,K,(Af,Mf),chosen)
print(f"start (img4 only, {len(chosen)} orbs): sup={cur:.4f}")
while cur<=4.0 and pool:
    best=None
    for i in pool:
        s=mk_sup(orbs,K,(Af,Mf),chosen+[i])
        if best is None or s>best[1]: best=(i,s)
    chosen.append(best[0]); pool.remove(best[0]); cur=best[1]
    print(f"  +{orbs[best[0]]} ({len(chosen)} orbs): sup={cur:.4f}", flush=True)
print(f"MIN SUBSET: {len(chosen)} orbits clear 4 at K={K}: {[orbs[i] for i in chosen]}")
