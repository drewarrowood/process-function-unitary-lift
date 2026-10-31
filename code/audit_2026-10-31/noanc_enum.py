"""Item 3: converse WITHOUT ancillas, exhaustive for n-party binary (n=1,2,3) and 2-party ternary (sampled+structured).
Ancilla-free closed loop: M[s,e] = prod_k V_k[s_k, w_k(s) + e_k], V_k unitary d x d.
Step A: screen all maps w by permutation interventions only (V_k permutation matrices are unitary; column norm of M
        = #fixed points of the induced bijective intervention).  Step B: survivors that are non-PF get Haar draws."""
import numpy as np, itertools as it, sys
rng=np.random.default_rng(20261031)
def haar(m):
    z=rng.normal(size=(m,m))+1j*rng.normal(size=(m,m)); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
def run(n,d,maps=None,label=''):
    S=list(it.product(range(d),repeat=n)); N=len(S); Sa=np.array(S)          # N x n
    code=lambda t: sum(int(t[k])*d**(n-1-k) for k in range(n))
    # all interventions f = (f_k: Z_d -> Z_d); bijective ones = permutations
    locs=list(it.product(range(d),repeat=d)); perms=[f for f in locs if len(set(f))==d]
    allF=list(it.product(locs,repeat=n)); bijF=list(it.product(perms,repeat=n))
    if maps is None: maps=np.array(list(it.product(range(N),repeat=N)),dtype=np.int16)  # w as array of input-codes
    W=Sa[maps.astype(np.int64)].astype(np.int8)                                                                       # M x N x n (input string per s)
    def counts(F):
        out=np.zeros((len(maps),len(F)),dtype=np.int8)
        for j,f in enumerate(F):
            fa=np.array(f)                                                            # n x d
            img=np.stack([fa[k][W[:,:,k]] for k in range(n)],-1)                     # f(w(s))
            out[:,j]=(img==Sa[None]).all(-1).sum(1)
        return out
    cb=counts(bijF); bij_ok=(cb==1).all(1)
    ca=counts(allF); pf=(ca==1).all(1)
    surv=np.where(bij_ok & ~pf)[0]
    print(f'[{label}] n={n} d={d}: maps {len(maps)}, PFs {pf.sum()}, non-PF caught by a permutation intervention {(~bij_ok).sum()}, '
          f'non-PF passing all {len(bijF)} permutation interventions: {len(surv)}')
    worst=[]
    for idx in surv:
        w=W[idx]; best=0
        for trial in range(20):
            V=[haar(d) for _ in range(n)]
            M=np.ones((N,N),complex)
            for k in range(n):
                M*=V[k][Sa[:,k][:,None], (w[:,k][:,None]+Sa[None,:,k])%d]
            best=max(best,np.linalg.norm(M@M.conj().T-np.eye(N)))
            if best>1e-3: break
        worst.append(best)
    if surv.size: print(f'   Haar: min over survivors of max residual = {min(worst):.3g} (all survivors broken: {min(worst)>1e-3})')
    # sanity: PFs unitary
    for idx in np.where(pf)[0][:50]:
        w=W[idx]; V=[haar(d) for _ in range(n)]; M=np.ones((N,N),complex)
        for k in range(n): M*=V[k][Sa[:,k][:,None], (w[:,k][:,None]+Sa[None,:,k])%d]
        assert np.linalg.norm(M@M.conj().T-np.eye(N))<1e-10
    return surv, W
import contextlib, io
def run_quiet(ch):
    with contextlib.redirect_stdout(io.StringIO()) as buf: r=run(3,2,ch,label='q')
    out=buf.getvalue()
    if 'Haar' in out or 'passing all 8 permutation interventions: 0' not in out: print(out,end='')
    return r
if __name__=='__main__':
    run(1,2,label='exh'); run(1,3,label='exh'); run(1,4,label='exh')
    run(2,2,label='exh')
    allm=np.array(list(it.product(range(8),repeat=4)),dtype=np.int16)   # chunk over first 4 entries
    tot=0
    for a in range(4096):
        hi=np.repeat(allm[a][None],4096,0); ch=np.concatenate([hi,allm],1)
        s,W=run(3,2,ch,label=f'exh chunk {a}') if a%512==0 else run_quiet(ch)
        tot+=len(s)
    print('3-party binary exhaustive (8^8 maps): non-PF passing all permutation interventions, total =',tot)
    # 2-party ternary: 9^9 too many for one pass; random sample + all maps with w_k independent of o_k (3^3)^2... 
    smp=rng.integers(0,9,size=(2_000_000,9)).astype(np.int16); run(2,3,smp,label='rand2M')
