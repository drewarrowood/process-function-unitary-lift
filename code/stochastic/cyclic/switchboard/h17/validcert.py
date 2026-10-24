"""H.17.5 exact certificates: for each never-crossed orbit except 92, an exact rational point of Valid (nonnegative,
normalised, every deterministic intervention has fixed-point probability 1) at which the facet functional is negative.
The facet functional g on p is rationalised and checked EXACTLY to reproduce the integer facet values on all 744 PFs."""
import numpy as np
from fractions import Fraction as Fr
exec(open('validlp.py').read().split('res={}')[0])
NC=[4,5,6,7,8,9,10,11,14,25,26,28,30,31,53,54,57,66,69,75,79,81]
Aq=[[Fr(int(a)) for a in r] for r in Aeq]
out={}
for orb in NC:
    f=int(np.nonzero(canon==orb)[0][0]); h=Hm[f]; v=[int(x) for x in Zc@h[:37]+h[37]]
    g=np.linalg.lstsq(X.astype(float),np.array(v,float),rcond=None)[0]
    gq=[Fr(x).limit_denominator(10**4) for x in g]
    assert all(sum(gq[j]*int(X[r,j]) for j in range(65) if X[r,j])==v[r] for r in range(744)), 'g not exact'
    lp=linprog(g[:64],A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*64,method='highs-ds')
    x=[Fr(t).limit_denominator(1000) for t in lp.x]
    assert all(t>=0 for t in x) and all(sum(a*t for a,t in zip(r,x))==1 for r in Aq), 'point not exactly valid'
    val=sum(a*t for a,t in zip(gq[:64],x))+gq[64]; rng_=max(v)
    assert val<0
    out[orb]=str(val/rng_)
print('exact relative facet values at certified Valid points:',out)
