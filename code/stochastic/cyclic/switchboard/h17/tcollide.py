"""EXACT: which collided strings of W = V'V^dag can vanish, for all pairs of classes with 2 or 3 terms (63 + 1,008 classes).
x = (a, i b, i c) for V = a + i(b A + c B); conj(x) = (a, -i b, -i c).  A string with exactly two contributions
phi1 x'_{u'} conj(x_u) + phi2 x'_{w'} conj(x_w) vanishes for some nonzero reals iff rho = -(phi1 t'_{u'} tb_u)/(phi2 t'_{w'} tb_w)
is real.  Two such strings vanish together iff both rho are real and the sign condition holds: with the four real unknowns
the two equations r'_{w'} r_w = rho1 r'_{u'} r_u and r'_{w'} r_u = rho2 r'_{u'} r_w (after matching index roles) need
(r_w/r_u)^2 = rho1/rho2 > 0.  Strings with three contributions occur only for K=K' (H.17.12b, proved analytically)."""
import numpy as np, itertools as it, collections
from lib3 import *
PH=np.zeros((64,64),complex)
for s in range(64):
    for t in range(64):
        M=HM[s]@HM[t]; R=HM[s^t]; j=np.unravel_index(np.argmax(np.abs(R)),R.shape); PH[s,t]=np.round(M[j]/R[j],12)
classes=[(a,) for a in range(1,64)]+[(a,b) for a in range(1,64) for b in range(a+1,64) if anti(a,b)]
cnt=collections.Counter(); bad=[]
for g in classes:
    L=[0]+list(g); tb={0:1,**{x:-1j for x in g}}
    for g2 in classes:
        L2=[0]+list(g2); tp={0:1,**{x:1j for x in g2}}
        terms=collections.defaultdict(list)
        for u2 in L2:
            for u in L: terms[u2^u].append((u2,u,PH[u2,u]*tp[u2]*tb[u]))
        two=[s for s in terms if len(terms[s])==2]; three=[s for s in terms if len(terms[s])>2]
        if three:
            cnt[('K=Kprime-type',len(g),len(g2))]+=1; continue
        if not two: cnt[('none',len(g),len(g2))]+=1; continue
        kill={}
        for s in two:
            (a2,a,p1),(b2,b,p2)=terms[s]; rho=-p1/p2
            kill[s]=(abs(rho.imag)<1e-9, rho.real, (a2,a,b2,b))
        single=sum(k[0] for k in kill.values())
        both=False
        if len(two)==2 and all(k[0] for k in kill.values()):
            (s1,k1),(s2,k2)=kill.items()
            # general solve: unknown logs of |r|; equations: r'_{b2} r_b / (r'_{a2} r_a) = rho  -> exponent vectors mod sign
            # sign feasibility: product of all equations' rho must match the sign of the product of the squared monomials
            v1=collections.Counter({('p',k1[2][2]):1,('q',k1[2][3]):1}); v1.subtract({('p',k1[2][0]):1,('q',k1[2][1]):1})
            v2=collections.Counter({('p',k2[2][2]):1,('q',k2[2][3]):1}); v2.subtract({('p',k2[2][0]):1,('q',k2[2][1]):1})
            # signs: need nonzero reals r with prod r^v1 = rho1, prod r^v2 = rho2. If v1 = +-v2 (dependent) consistency needs rho2 = rho1^{+-1};
            # otherwise v1+v2 or v1-v2 has all-even exponents for some unknowns -> sign constraint on rho1*rho2 or rho1/rho2.
            keys=set(v1)|set(v2); A=np.array([[v1[k],v2[k]] for k in keys])
            if np.linalg.matrix_rank(A)<2:
                c=1 if all(v1[k]==v2[k] for k in keys) else -1
                both = abs(k2[1]-k1[1]**c)<1e-9
            else:
                ok=False
                for sgn in it.product([1,-1],repeat=len(keys)):
                    S=dict(zip(keys,sgn)); s1_=np.prod([S[k]**abs(v1[k]) for k in keys]); s2_=np.prod([S[k]**abs(v2[k]) for k in keys])
                    if s1_==np.sign(k1[1]) and s2_==np.sign(k2[1]): ok=True;break
                both=ok
        cnt[('two-term collisions',len(g),len(g2),len(two),single,both)]+=1
        if both: bad.append((g,g2))
for k,v in sorted(cnt.items(),key=str): print(k,v)
print('pairs where two collided strings can vanish together:',len(bad),bad[:5])
