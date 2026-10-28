"""Round 33 (H.38): direct check of orbit 30's negative transverse coefficient at the h33_g2.py minimiser, from the eigenvalues of M itself:
g ~ lambda_min(M(a,t)) / sin^2 t0 as t0 -> 0, M = Mh * prod_k cos^2(t_k/2) (h33_g.build), in mpmath (40 digits)."""
import sys, numpy as np, sympy as sp, mpmath as mp
from h33_g import build
mp.mp.dps=40
for orb,z in [(30,[2.2609,3.6572,4.0635,0.9734,1.3554]),(28,[2.2609,3.6572,4.0635,0.9734,1.3554])]:
    M,y,u,T,c=build(orb); f=sp.lambdify((u,y),M,'mpmath')
    a=[mp.mpf(str(v)) for v in z[:3]]; t1,t2=mp.mpf(str(z[3])),mp.mpf(str(z[4]))
    for t0 in [mp.mpf('1e-2'),mp.mpf('1e-3'),mp.mpf('1e-4')]:
        tt=[t0,t1,t2]; Mh=mp.matrix(f([mp.expj(v) for v in a],[mp.tan(x/2) for x in tt]))
        Mm=Mh*mp.fprod([mp.cos(x/2)**2 for x in tt]); ev=mp.eighe(Mm,eigvals_only=True) if hasattr(mp,'eighe') else mp.eigh(Mm,eigvals_only=True)
        lam=min(ev); print(orb,f't0={mp.nstr(t0,2)}: lambda_min = {mp.nstr(lam,10)}, lambda/sin^2 t0 = {mp.nstr(lam/mp.sin(t0)**2,10)}',flush=True)
