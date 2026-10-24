"""H.17 goal 4, non-generic part [numerical]: <=3-term boards whose classes are TUNED so that products U_o U_q^dag lose terms
(possible only when the groups <A,B>, <A',B'> intersect).  Supports are computed numerically from the matrices, so every
cancellation the tuned parameters produce is seen by the Pauli rule.  New class options at a vertex:
  generic (fresh A,B, random parameters);  sign variant of an old class;  tuned: gens (g1,g2) whose group meets an old class's
  group (incl. identical gens), parameters chosen in the null space of the map p -> coefficient of a collided product in V_c V'^dag.
Reports hard (>=3 terms somewhere, no operator-first/last party) complete boards, conservative SH status, best facet violation."""
import sys, json, time, random, itertools as it
from lib3 import *
seed=int(sys.argv[1]); N=int(sys.argv[2]); random.seed(seed); rng=np.random.default_rng(seed)
T,canon=load_facets()
I8=np.eye(8,dtype=complex)
def supp_of(K,tol=1e-9): c=pauli_coeffs(K); return [s for s in range(64) if abs(c[s])>tol]
def mkV(g,p): return p[0]*I8+sum(1j*p[m+1]*HM[g[m]] for m in range(len(g)))
def grp(g): 
    if len(g)==1: return {g[0]}
    return {g[0],g[1],g[0]^g[1]}
def tuned(c,g):
    """parameters p for V'=mkV(g,p) killing one collided product of V_c V'^dag; None if impossible with all p_m != 0."""
    Vc=c['V']; Es=[I8]+[1j*HM[x] for x in g]
    cols=[pauli_coeffs(Vc@E.conj().T) for E in Es]
    coll=[s for s in range(64) if sum(abs(col[s])>1e-9 for col in cols)>=2]
    random.shuffle(coll)
    for s in coll[:3]:
        M=np.array([[col[s].real for col in cols],[col[s].imag for col in cols]])
        u,sv,vt=np.linalg.svd(M); r=(sv>1e-9).sum(); ns=vt[r:]
        if len(ns)==0: continue
        p=ns.T@rng.normal(size=len(ns)); p/=np.linalg.norm(p)
        if np.all(np.abs(p)>0.05): return p
    return None
ORDER=[0,4,2,1,6,5,3,7]
class Done(Exception): pass
def newclasses(i,G,classes):
    out=[]
    pairs=[(a,b) for a in G for b in G if a<b and anti(a,b)]
    for a,b in random.sample(pairs,min(len(pairs),6)):
        th,f=rng.uniform(0.15,1.4,2); out.append(dict(g=(a,b),V=mkV((a,b),(np.cos(th),np.sin(th)*np.cos(f),np.sin(th)*np.sin(f)))))
    for c in classes:
        if len(c['g'])==2:
            for sg in (1,2,3):
                p=np.linalg.svd(np.array([pauli_coeffs(c['V'])[[0,c['g'][0],c['g'][1]]]]))[2][0] if False else None
        cg=grp(c['g'])
        cand=[(a,b) for a,b in pairs if grp((a,b))&cg]
        for g in random.sample(cand,min(len(cand),4)):
            p=tuned(c,g)
            if p is not None: out.append(dict(g=g,V=mkV(g,p),t=1))
        cand=[(a,) for a in G if a in cg]
        for g in cand[:1]:
            p=tuned(c,g)
            if p is not None: out.append(dict(g=g,V=mkV(g,p),t=1))
    return out
def rdfs(i,assign,classes,cnt,maxnodes):
    cnt[0]+=1
    if cnt[0]>maxnodes: raise Done
    if i==8: raise Done(dict(assign),list(classes))
    o=ORDER[i]; prev=ORDER[:i]
    G=[s for s in range(1,64) if all(not FORB[o^q][s] for q in prev if bin(o^q).count('1')==1)]
    if i==0: Pdom=[0]
    if i==0: G=[s for s in range(1,64)]
    else: Pdom=[P for P in range(64) if all(not FORB[o^q][P^assign[q][0]] for q in prev)]
    new=newclasses(i,G,classes) if len(classes)<4 else []
    opts=[(P,('old',k)) for P in Pdom for k in range(len(classes))]+[(P,('new',c)) for P in random.sample(Pdom,min(len(Pdom),8)) for c in new]
    random.shuffle(opts); pn=PNEW[0]; opts.sort(key=lambda x:(x[1][0]!='new') != (random.random()<pn))
    for P,ch in opts[:300]:
        if ch[0]=='old': k=ch[1]; add=False
        else: classes.append(ch[1]); k=len(classes)-1; add=True
        U=PM[P]@classes[k]['V']
        if all(not any(FORB[o^q][s] for s in supp_of(U@assign[q][2].conj().T)) for q in prev):
            assign[o]=(P,k,U); rdfs(i+1,assign,classes,cnt,maxnodes); del assign[o]
        if add: classes.pop()
def SHc(assign,classes):
    sh=[sorted({px(s) for s in supp_of(c['V'])}) for c in classes]; bad=0
    for o in range(8):
        for q in range(o+1,8):
            D=o^q; a=px(assign[o][0])^px(assign[q][0]); k,k2=assign[o][1],assign[q][1]
            combos=[(0,0)] if (k==k2 or (sh[k]==[0] and sh[k2]==[0])) else it.product(sh[k],sh[k2])
            if any(((a^t^t2)&D)==D for t,t2 in combos): bad+=1
    return bad
res=dict(complete=0,hard=0,tunedcanc=0,sh_fail=0,best=-1.,best_shfail=-1.,maxrule=0.); ex=[]
t0=time.time()
PNEW=[0.5]
for n in range(N):
    PNEW[0]=random.random()
    try: rdfs(0,{},[],[0],3000); continue
    except Done as e:
        if not e.args: continue
        A,C=e.args
    res['complete']+=1
    res['tuned_used']=res.get('tuned_used',0)+any(C[A[o][1]].get('t',0) for o in range(8))
    U=np.array([A[o][2] for o in range(8)])
    if not any(len(supp_of(c['V']))>=3 for c in C): continue
    S={(o,q):supp_of(U[o]@U[q].conj().T) for o in range(8) for q in range(8) if o!=q}
    last=any(all(S[(o,o^(1<<j))]==[0] for o in range(8)) for j in range(3))
    first=any(all(((px(s)|pz(s))>>j)&1==0 for v in S.values() for s in v) for j in range(3))
    if last or first: continue
    res['hard']+=1
    # did tuning remove a product that generic parameters would give?
    canc=0
    for o in range(8):
        for q in range(o+1,8):
            k,k2=A[o][1],A[q][1]
            if k!=k2:
                gen={A[o][0]^A[q][0]^x^y for x in [0]+list(C[k]['g']) for y in [0]+list(C[k2]['g'])}
                if len(gen-set(S[(o,q)])): canc+=1
    res['tunedcanc']+=canc>0
    res['maxrule']=max(res['maxrule'],rule_residual(U))
    v=float(facet_viol(U,T).max()); b=SHc(A,C)
    res['best']=max(res['best'],v)
    if b: res['sh_fail']+=1; res['best_shfail']=max(res['best_shfail'],v)
    if canc and len(ex)<30: ex.append(dict(P=[int(A[o][0]) for o in range(8)],k=[int(A[o][1]) for o in range(8)],g=[list(map(int,c['g'])) for c in C],shbad=b,viol=v))
    if v>1e-6: np.save('nviol_%d_%d.npy'%(seed,n),U); print('VIOLATION',v,flush=True)
    if res['hard']%20==0: print(n,round(time.time()-t0),json.dumps(res),flush=True); json.dump(dict(res=res,ex=ex),open('ns_%d.json'%seed,'w'))
print('final',json.dumps(res),flush=True); json.dump(dict(res=res,ex=ex),open('ns_%d.json'%seed,'w'))
