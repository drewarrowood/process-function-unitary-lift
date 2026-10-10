import numpy as np, itertools as it
rng=np.random.default_rng(1)
def strs(n,d=2): return list(it.product(range(d),repeat=n))
def is_pf(w,n,d=2):
    S=strs(n,d); locs=list(it.product(range(d),repeat=d))
    for f in it.product(locs,repeat=n):
        c=sum(1 for o in S if all(f[k][w[o][k]]==o[k] for k in range(n)))
        if c!=1: return False
    return True
def disagree(w,n,d=2):
    S=strs(n,d)
    return all(any(s[k]!=t[k] and w[s][k]==w[t][k] for k in range(n)) for s in S for t in S if s!=t)
def haar(m):
    z=rng.normal(size=(m,m))+1j*rng.normal(size=(m,m)); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
def induced(w,n,Vs,d=2,a=1):
    # Vs[k]: (d*a)x(d*a), index (x,anc); M: (e,ain)->(s,aout)
    S=strs(n,d); A=strs(n,a); D=len(S)*len(A)
    M=np.zeros((D,D),complex)
    for si,s in enumerate(S):
      for ei,e in enumerate(S):
        i=[(w[s][k]+e[k])%d for k in range(n)]
        for ao_i,ao in enumerate(A):
          for ai_i,ai in enumerate(A):
            amp=1
            for k in range(n): amp*=Vs[k][s[k]*a+ao[k], i[k]*a+ai[k]]
            M[si*len(A)+ao_i, ei*len(A)+ai_i]+=amp
    return M
def dev(M): return np.linalg.norm(M@M.conj().T-np.eye(len(M)))
def maxdev(w,n,trials,a=1,d=2):
    return max(dev(induced(w,n,[haar(d*a) for _ in range(n)],d,a)) for _ in range(trials))
for n in (2,3):
    S=strs(n); fns=[]
    # all maps with w_k independent of o_k (necessary for PF)
    choices=[]
    for k in range(n):
        others=strs(n-1)
        choices.append(list(it.product((0,1),repeat=len(others))))
    for tab in it.product(*choices):
        w={o:tuple(tab[k][strs(n-1).index(o[:k]+o[k+1:])] for k in range(n)) for o in S}
        fns.append(w)
    pf=[w for w in fns if is_pf(w,n)]
    agree=all(is_pf(w,n)==disagree(w,n) for w in fns)
    print(n,"candidates",len(fns),"process functions",len(pf),"PF<=>disagreement:",agree)
    worst=max(maxdev(w,n,3) for w in pf); print("  max dev over all PFs, 3 Haar each:",worst)
    if n==2:
        print("  with qubit ancilla:",max(maxdev(w,n,2,a=2) for w in pf))
        allmaps=[dict(zip(S,v)) for v in it.product(S,repeat=len(S))]
        print("  all 256 maps: PF count",sum(is_pf(w,2) for w in allmaps))
        nonpf=[w for w in allmaps if not is_pf(w,2)]
        print("  min over non-PFs of maxdev(5 Haar):",min(maxdev(w,2,5) for w in nonpf))
    else:
        print("  ancilla sample (20 PFs):",max(maxdev(w,n,1,a=2) for w in pf[:20]))
        nonpf=[w for w in fns if not is_pf(w,n)]
        print("  min over non-PFs maxdev(3 Haar):",min(maxdev(w,n,3) for w in nonpf))
# ternary 2-party sample
n,d=2,3; S=strs(n,d)
lug=lambda o:((1-o[1])&o[2],(1-o[2])&o[0],(1-o[0])&o[1])
# random ternary 2-party one-way PFs: w_A const-ish, w_B depends on o_A
cnt=0;w2=None
for _ in range(200):
    gA=rng.integers(3); tb=rng.integers(3,size=3)
    w={o:(int(gA),int(tb[o[0]])) for o in S}
    assert is_pf(w,2,3); cnt=max(cnt,maxdev(w,2,2,d=3))
print("ternary 2-party one-way PFs maxdev",cnt)
