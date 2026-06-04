# Parametric witness emitter: emit_lean_param.py <k> <D> [outpath]
# Emits a Lean `List (List ℕ × ℚ)` LCs literal for the minimal-degree-D, k-tuple witness.
import sys
K=int(sys.argv[1]); D=int(sys.argv[2])
out=sys.argv[3] if len(sys.argv)>3 else f"/tmp/witnessLCs_k{K}_D{D}.lean"
sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
from math import factorial as fac, gcd
exec(open('frontier.py').read().split('print("Mapping')[0])
from _ldl import ldl_inertia
orbs=M.partitions_upto(D); n=len(orbs)
cache=precompute(orbs); A,Mm=gram_at(orbs,cache,K)
B=[[A[i][j]-4*Mm[i][j] for j in range(n)] for i in range(n)]
pos,neg,zero,wit=ldl_inertia(B)
assert wit is not None, f"M_{K}({D}) <= 4 (no positive pivot)"
Nr=sum(wit[i]*A[i][j]*wit[j] for i in range(n) for j in range(n))
Dr=sum(wit[i]*Mm[i][j]*wit[j] for i in range(n) for j in range(n))
q=Nr/Dr; assert q>4
dens=[w.denominator for w in wit]; L=1
for d in dens: L=L*d//gcd(L,d)
witI=[int(w*L) for w in wit]
def lparts(o): return "["+", ".join(str(x) for x in o)+"]"
body=",\n".join(f"  ({lparts(o)}, ({c} : ℚ))" for o,c in zip(orbs,witI))
open(out,"w").write(f"-- AUTO k={K} D={D} n={n} quotient={float(q):.6f}>4\n[\n{body}\n]\n")
print(f"wrote {out}  k={K} D={D} n={n} quotient={float(q):.6f} maxdigits={max(len(str(abs(x))) for x in witI)}")
