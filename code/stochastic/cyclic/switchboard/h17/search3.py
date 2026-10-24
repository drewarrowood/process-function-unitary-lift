"""H.17 goal 4 [numerical + per-structure exact SH check]: random structures with <=3 Pauli terms per U_o."""
import sys, json, time
from struct3 import *
seed=int(sys.argv[1]); N=int(sys.argv[2]); random.seed(seed); rng=np.random.default_rng(seed)
T,canon=load_facets()
res=dict(complete=0,hard=0,sh_ok=0,sh_fail=0,best_shok=-1.,best_shfail=-1.,maxrule=0.,ex_fail=[],ex_ok=[])
t0=time.time()
for n in range(N):
    r=random_structure(pnew=random.random())
    if r is None: continue
    A,C=r; res['complete']+=1
    if not any(c[0]==3 for c in C): continue
    L_,F_=first_last(A,C)
    if L_ or F_: continue
    res['hard']+=1
    bad=SH(A,C); key='sh_ok' if not bad else 'sh_fail'; res[key]+=1
    best=-1
    for _ in range(3):
        U=build(A,C,rng=rng); res['maxrule']=max(res['maxrule'],rule_residual(U))
        best=max(best,float(facet_viol(U,T).max()))
    bk='best_shok' if not bad else 'best_shfail'; res[bk]=max(res[bk],best)
    ex='ex_ok' if not bad else 'ex_fail'
    if len(res[ex])<200: res[ex].append([{str(o):A[o] for o in A},C,best])
    if n%100==0:
        print(n,round(time.time()-t0),json.dumps({k:v for k,v in res.items() if not k.startswith('ex')}),flush=True)
        json.dump(res,open('s3_%d.json'%seed,'w'))
print('final',json.dumps({k:v for k,v in res.items() if not k.startswith('ex')}),flush=True)
json.dump(res,open('s3_%d.json'%seed,'w'))
