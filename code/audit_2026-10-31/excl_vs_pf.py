"""Item 3 check of the proof: (a) row Gram identity (M M^dag)[s,s'] = prod_k (V_k T^{w_k(s)-w_k(s')} V_k^dag)[s_k,s'_k];
(b) pairwise exclusivity <=> PF, exhaustively for 3-party binary (8^8 maps) and 2-party binary, sampled 2-party ternary."""
import numpy as np, itertools as it
rng=np.random.default_rng(7)
def haar(m):
    z=rng.normal(size=(m,m))+1j*rng.normal(size=(m,m)); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
def setup(n,d): S=np.array(list(it.product(range(d),repeat=n))); return S
# (a)
for n,d in [(2,2),(3,2),(2,3),(2,4)]:
    S=setup(n,d); N=len(S); err=0
    for _ in range(20):
        w=S[rng.integers(0,N,N)]; V=[haar(d) for _ in range(n)]
        M=np.ones((N,N),complex)
        for k in range(n): M*=V[k][S[:,k][:,None],(w[:,k][:,None]+S[None,:,k])%d]
        T=np.roll(np.eye(d),1,0)
        G=np.ones((N,N),complex)
        for k in range(n):
            for a in range(N):
                for b in range(N):
                    G[a,b]*=(V[k]@np.linalg.matrix_power(T,(w[a,k]-w[b,k])%d)@V[k].conj().T)[S[a,k],S[b,k]]
        err=max(err,abs(M@M.conj().T-G).max())
    print(f'(a) n={n} d={d}: max |MM^dag - prod_k G_k| over 20 random (w,V) = {err:.2e}')
# (b)
def excl_and_pf(maps,n,d):
    S=setup(n,d); N=len(S); W=S[maps]
    pairs=[(a,b) for a in range(N) for b in range(N) if a<b]
    ex=np.ones(len(maps),bool)
    for a,b in pairs:
        ok=np.zeros(len(maps),bool)
        for k in range(n):
            if S[a,k]!=S[b,k]: ok|=(W[:,a,k]==W[:,b,k])
        ex&=ok
    locs=list(it.product(range(d),repeat=d)); pf=np.ones(len(maps),bool)
    for f in it.product(locs,repeat=n):
        fa=np.array(f); img=np.stack([fa[k][W[:,:,k]] for k in range(n)],-1)
        pf&=((img==S[None]).all(-1).sum(1)==1)
    return ex,pf
for n,d in [(2,2)]:
    ex,pf=excl_and_pf(np.array(list(it.product(range(d**n),repeat=d**n))),n,d)
    print(f'(b) n={n} d={d} exhaustive: PF {pf.sum()}, exclusive {ex.sum()}, mismatches {(ex!=pf).sum()}')
allm=np.array(list(it.product(range(8),repeat=4)))
tp=te=mm=0
for a in range(4096):
    ch=np.concatenate([np.repeat(allm[a][None],4096,0),allm],1); ex,pf=excl_and_pf(ch,3,2)
    tp+=pf.sum(); te+=ex.sum(); mm+=(ex!=pf).sum()
print(f'(b) n=3 d=2 exhaustive (16,777,216 maps): PF {tp}, exclusive {te}, mismatches {mm}')
smp=rng.integers(0,9,(300000,9)); ex,pf=excl_and_pf(smp,2,3)
print(f'(b) n=2 d=3 random 300k: PF {pf.sum()}, exclusive {ex.sum()}, mismatches {(ex!=pf).sum()}')
