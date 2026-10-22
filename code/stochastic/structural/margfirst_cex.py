# H.5: a PF mixture (hence purifiable, C.1) that is marginally first in A but has invalid conditionals. Exact arithmetic.
from fractions import Fraction as Fr; import itertools as it
B=(0,1); F2=list(it.product(B,repeat=2))
def p(a,b,c,x,y,z): return Fr(1,4)*(a==(b^c^y^z))
# (1) decomposition: for each (beta,gamma) the deterministic map b=beta, c=gamma, a=beta^gamma^y^z, weight 1/4
def w(bt,gm): return lambda x,y,z:(bt^gm^y^z,bt,gm)
def is_pf(t):
    return all(sum(1 for o in it.product(B,repeat=3) if all(f[k][t(*o)[k]]==o[k] for k in range(3)))==1 for f in it.product(F2,repeat=3))
assert all(is_pf(w(bt,gm)) for bt in B for gm in B)
for a,b,c,x,y,z in it.product(B,repeat=6):
    assert p(a,b,c,x,y,z)==sum(Fr(1,4)*(w(bt,gm)(x,y,z)==(a,b,c)) for bt in B for gm in B)
# (2) validity of p
for f in it.product(F2,repeat=3):
    assert sum(p(a,b,c,f[0][a],f[1][b],f[2][c]) for a,b,c in it.product(B,repeat=3))==1
# (3) A marginally first
for x,y,z in it.product(B,repeat=3):
    for a in B: assert sum(p(a,b,c,x,y,z) for b in B for c in B)==Fr(1,2)
# (4) conditional q_{a,x}(b,c|y,z)=2p is invalid: N(g,h) for g=h=identity
for a in B:
    N=sum(2*p(a,b,c,0,g,h) for b in B for c in B for g,h in [(b,c)])
    print('a=%d: sum_bc q(b,c|y=b,z=c) ='%a,N)
print('all exact checks passed')
