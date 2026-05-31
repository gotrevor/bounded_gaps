import itertools
k=5
orb_coeff={ ():14960, (1,):-40392, (1,1):62832, (1,1,1):-39984, (2,):59136, (2,1):-43197, (3,):-31416 }
def orbit(m): return tuple(sorted([x for x in m if x>0],reverse=True))
mons=set()
for deg in range(4):
    for c in itertools.combinations_with_replacement(range(k),deg):
        e=[0]*k
        for j in c: e[j]+=1
        mons.add(tuple(e))
mons=sorted(mons)
terms=[]
for m in mons:
    c=orb_coeff[orbit(m)]
    vec="![%s]"%(", ".join(str(x) for x in m))
    terms.append(f"    ({vec}, ({c} : ℚ))")
print(f"-- {len(terms)} terms")
body=",\n".join(terms)
print("def P5terms : List (MultiIndex 5 × ℚ) := [\n"+body+"]")
