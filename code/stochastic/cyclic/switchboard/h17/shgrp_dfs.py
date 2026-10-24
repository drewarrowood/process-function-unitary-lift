"""H.17.9d [EXHAUSTIVE, EXACT; generic-support model]: full cube search for the 288 survivors of shgrp_cube.
WLOG o=0 (class c, P=0, sigma=0) and q=7 (class c', P=R, sigma=0).  Every other vertex v gets a state (P_v in 64, class k in all
1,072 options, sign pattern sigma).  Two states are compatible across D=v xor w iff the generic support avoids the forbidden
strings: different classes -> P+P'+T_k+T_k';  if k == k' they may also be the SAME class (sign change ds) -> P+P'+S(ds).
Both readings are allowed (over-approximation, so 'no extension' is a proof; any extension found is re-checked).
Method: domains filtered against o and q, then arc consistency over the 6x6 intermediate pairs, then DFS."""
import numpy as np, json, time, sys
from lib3 import FORB, anti, px, pz
CL=[(1,)]+[(2,a) for a in range(1,64)]+[(3,a,b) for a in range(1,64) for b in range(a+1,64) if anti(a,b)]
IDX={c:i for i,c in enumerate(CL)}; N=len(CL)
NS=np.array([{1:1,2:2,3:4}[c[0]] for c in CL])
T=np.array([([0]+list(c[1:])+[0,0])[:3] for c in CL])
def Ssame(c,ds):
    if c[0]==1 or ds==0: return [0]
    if c[0]==2: return [0,c[1]]
    a,b=c[1],c[2]; return {1:[0,a,a^b],2:[0,b,a^b],3:[0,a,b]}[ds]
# allowed-R tables
t0=time.time()
AD=np.zeros((8,N,N,64),bool)
R=np.arange(64)
for i in range(N):
    M=(T[i][:,None,None]^T[None,:,:]).transpose(1,0,2).reshape(N,9)
    S=R[None,:,None]^M[:,None,:]
    for D in range(1,8): AD[D,i]=~FORB[D][S].any(-1)
AS=np.zeros((8,N,4,64),bool)
for k,c in enumerate(CL):
    for ds in range(4 if c[0]==3 else 2 if c[0]==2 else 1):
        Ss=np.array(Ssame(c,ds))
        for D in range(1,8): AS[D,k,ds]=~FORB[D][R[:,None]^Ss[None,:]].any(-1)
print('tables',round(time.time()-t0),flush=True)
# all states
ST=np.array([(P,k,s) for k in range(N) for s in range(NS[k]) for P in range(64)])
def compat(a,b,D):   # a: (n,3) states, b: single state or (n,3) broadcast
    Pa,ka,sa=a[...,0],a[...,1],a[...,2]; Pb,kb,sb=b[...,0],b[...,1],b[...,2]
    r=Pa^Pb
    ok=AD[D,ka,kb,r]
    same=(ka==kb)
    ok2=np.where(same,AS[D,ka,(sa^sb)&3,r],False)
    # sign mismatch index for types<3 is harmless: AS rows beyond NS are False except ds=0 handled
    return ok|ok2
def solve(c,cq,Rq):
    o=np.array([0,IDX[c],0]); q=np.array([Rq,IDX[cq],0])
    # q must be compatible with o (sanity)
    assert compat(q[None],o[None],7)[0]
    dom={}
    for v in range(1,7):
        m=compat(ST,o[None],v)&compat(ST,q[None],v^7); dom[v]=ST[m]
    changed=True
    while changed:
        changed=False
        for v in range(1,7):
            keep=np.ones(len(dom[v]),bool)
            for w in range(1,7):
                if w==v: continue
                # each state of v needs a support in dom[w]
                dv=dom[v]; dw=dom[w]
                sup=np.zeros(len(dv),bool)
                for s in range(0,len(dw),4000):
                    sup|=compat(dv[:,None,:],dw[None,s:s+4000,:],v^w).any(1)
                keep&=sup
            if not keep.all(): dom[v]=dom[v][keep]; changed=True
            if len(dom[v])==0: return 'none',{u:len(dom[u]) for u in dom}
    # DFS
    order=sorted(range(1,7),key=lambda v:len(dom[v])); asg={}
    def rec(i):
        if i==6: return True
        v=order[i]; cand=dom[v]; m=np.ones(len(cand),bool)
        for w,st in asg.items(): m&=compat(cand,st[None],v^w)
        for st in cand[m]:
            asg[v]=st
            if rec(i+1): return True
            del asg[v]
        return False
    return ('found' if rec(0) else 'none'),{u:len(dom[u]) for u in dom}
S=json.load(open('shgrp_cube_survivors.json'))
out=[]; t1=time.time()
start=int(sys.argv[1]) if len(sys.argv)>1 else 0
for n,(a,b,r,d) in enumerate(S):
    if n<start: continue
    res,ds=solve(tuple(a),tuple(b),r)
    out.append(dict(n=n,c=a,cq=b,R=r,result=res,domains=ds)); print(n,a,b,r,res,ds,round(time.time()-t1),flush=True)
    json.dump(out,open('shgrp_dfs_%d.json'%start,'w'))
print('SUMMARY found=',sum(x['result']=='found' for x in out),'none=',sum(x['result']=='none' for x in out),flush=True)
