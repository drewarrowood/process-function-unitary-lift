"""Explicit PF decomposition of two-term boards (Theorem H.10.6), checked numerically on random pairs, phi, t.
lambda(j,sigma) = mu_j prod_classes pi_k(j, h_sigma(k)) / mu_j ; PF for (j,sigma): o -> j ^ m_sigma(o)."""
import json, itertools as it, numpy as np
from coset_check import isPF
rng=np.random.default_rng(3); P=[p for p in json.load(open('twoterm_pairs.json')) if p[0]!=p[1]]
worst=0
for trial in range(300):
    w1,w2=P[rng.integers(len(P))]; t=rng.uniform(0,np.pi/2); c,s=np.cos(t),np.sin(t)
    phi=rng.normal(size=8)+1j*rng.normal(size=8); phi/=np.linalg.norm(phi); mu=abs(phi)**2
    d=[a^b for a,b in zip(w1,w2)]; cl=sorted(set(d))
    p=np.zeros((8,8))
    for o in range(8):
        X=lambda x: np.eye(8)[[j^x for j in range(8)]]
        U=X(w1[o])@(c*np.eye(8)+1j*s*X(d[o])); p[:,o]=abs(U@phi)**2
    pi={}
    for k in cl:
        G=c*np.eye(8)+1j*s*np.eye(8)[[j^k for j in range(8)]]; r=abs(G@phi)**2
        for j in range(8):
            if k==0: pi[(k,j,0)]=mu[j]; pi[(k,j,1)]=0; continue
            # transport on coset {j, j^k}: pi(j->j)=x, pi(j->j^k)=mu_j-x; need x + pi(j^k->j) = r_j
            jj=j^k
            if j<jj:
                x=max(0.0,mu[j]-r[jj]); y=r[j]-x            # y = pi(jj->j)
                pi[(k,j,0)]=x; pi[(k,j,1)]=mu[j]-x; pi[(k,jj,1)]=y; pi[(k,jj,0)]=mu[jj]-y
    q=np.zeros((8,8)); tot=0; mn=0
    for j in range(8):
        for sig in it.product((0,1),repeat=len(cl)):
            lam=mu[j]
            for k,sg in zip(cl,sig): lam*=pi[(k,j,sg)]/mu[j]
            mn=min(mn,lam); tot+=lam
            m=[(w2[o] if sig[cl.index(d[o])] else w1[o])^j for o in range(8)]
            assert isPF(m)
            for o in range(8): q[m[o],o]+=lam
    worst=max(worst,abs(q-p).max(),abs(tot-1),-mn)
print('300 random (pair, phi, t): max |decomposition - p|, |sum-1|, negativity:',worst)
