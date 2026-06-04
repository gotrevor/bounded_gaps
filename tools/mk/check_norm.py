import sys; sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
orbs = [(2,1),(1,1)]
A,Mm = M.reduced_closed(orbs, 3)
print("den (2,1)x(1,1) k=3 =", Mm[0][1], " expect 11/3360:", Mm[0][1]==F(11,3360))
print("num (2,1)x(1,1) k=3 =", A[0][1],  " expect 7/2160:",  A[0][1]==F(7,2160))
print("den diag (2,1):", Mm[0][0], " num diag:", A[0][0])
