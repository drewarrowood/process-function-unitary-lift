import numpy as np, numpy.linalg as la, json, sys
import fast2
def prep(E):
    d=fast2.diagW(E); supp=np.nonzero(d>1e-12)[0]; r=len(supp)
    emb=np.zeros((4096,64*r))
    for k,p in enumerate(supp):
        for row in range(64): emb[row*64+p,row*r+k]=1
    N,_=fast2.null(fast2.L@emb); m=N.shape[1]
    Xs=np.array([(emb@N[:,a]).reshape(64,64) for a in range(m)])
    Lam=np.zeros(64); Lam[supp]=1/d[supp]
    return d,supp,r,m,Xs,Lam
def forms(Xs,Lam):
    m=len(Xs); XL=Xs*Lam[None,None,:]
    T=np.zeros((m,m,4096),np.float32)
    for a in range(m):
        Y=np.einsum('ij,bkj->bik',XL[a],Xs).reshape(m,4096)   # X_a Lam X_b^T
        T[a]=(fast2.L@Y.T).T
    return T
def analyse(E,trials=600,seed=0):
    d,supp,r,m,Xs,Lam=prep(E); res={'rank':int(r),'dimVW':int(m),'nec_ok':bool(m>=r)}
    if m<r: return res
    T=forms(Xs,Lam); used=np.nonzero(np.abs(T).sum(axis=(0,1))>1e-6)[0]; Tu=T[:,:,used]
    rng=np.random.default_rng(seed); best=m
    for t in range(trials):
        phi=rng.normal(size=len(used))*(rng.random(len(used))<max(0.02,3/len(used)))
        S=np.tensordot(Tu,phi,axes=([2],[0])); S=S+S.T
        if not S.any(): continue
        e=la.eigvalsh(S); sc=max(1e-6,1e-6*abs(e).max())
        best=min(best,int(np.sum(abs(e)<sc)+min(np.sum(e>sc),np.sum(e<-sc))))
        if best<r: break
    res.update(iso_bound=int(best),ruled_out=bool(best<r))
    return res
if __name__=='__main__':
    R=json.load(open('reps.json')); fn='reps_results.jsonl'
    try: done={json.loads(l)['i'] for l in open(fn)}
    except FileNotFoundError: done=set()
    for i,(k,cnt) in enumerate(R):
        if i in done: continue
        res=analyse(np.array(k).reshape(8,8)); res.update(i=i,count=cnt,vals=sorted(set(round(v,4) for v in k if v>1e-9)))
        open(fn,'a').write(json.dumps(res)+'\n'); print(res,flush=True)
