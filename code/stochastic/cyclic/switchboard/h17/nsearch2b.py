"""[nsearch2b = nsearch2 + saves U, structure and worst-case source state of every tuned-cancellation board to tb_<seed>_<n>.npz]
[nsearch2: new classes get the most general LINEAR REPAIR of their parameters against all placed vertices]\nH.17 goal 4, non-generic part [numerical]: <=3-term boards whose classes are TUNED so that products U_o U_q^dag lose terms
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
def solve_new(P,g,o,prev,assign):
    """most general linear repair: parameters p of V'=mkV(g,p) such that every forbidden Pauli coefficient of
    P V' U_q^dag vanishes for all placed q; returns (p, tuned?) or None."""
    Es=[I8]+[1j*HM[x] for x in g]; rows=[]
    for q in prev:
        Uq=assign[q][2]; cols=np.array([pauli_coeffs(PM[P]@E@Uq.conj().T) for E in Es])   # (m, s)
        for s_ in np.nonzero(FORB[o^q])[0]:
            c=cols[:,s_]
            if np.abs(c).max()>1e-12: rows+= [c.real,c.imag]
    if not rows: p=rng.normal(size=len(Es)); return p/np.linalg.norm(p),False
    M=np.array(rows); u,sv,vt=np.linalg.svd(M); r=(sv>1e-9).sum(); ns=vt[r:]
    if len(ns)==0: return None
    p=ns.T@rng.normal(size=len(ns)); p/=np.linalg.norm(p)
    if np.abs(p).min()<0.05: return None
    return p,True
def rdfs(i,assign,classes,cnt,maxnodes):
    cnt[0]+=1
    if cnt[0]>maxnodes: raise Done
    if i==8: raise Done(dict(assign),list(classes))
    o=ORDER[i]; prev=ORDER[:i]
    G=[s for s in range(1,64) if all(not FORB[o^q][s] for q in prev if bin(o^q).count('1')==1)]
    pairs=[(a,b) for a in G for b in G if a<b and anti(a,b)]
    opts=[(P,('old',k)) for P in range(64) for k in range(len(classes))]
    if len(classes)<4 and pairs:
        opts+=[(random.randrange(64) if i else 0,('new',random.choice(pairs))) for _ in range(60)]
        opts+=[(random.randrange(64) if i else 0,('new',(random.choice(G),))) for _ in range(10)]
    random.shuffle(opts); pn=PNEW[0]; opts.sort(key=lambda x:(x[1][0]!='new') != (random.random()<pn))
    for P,ch in opts[:400]:
        if ch[0]=='old':
            k=ch[1]; U=PM[P]@classes[k]['V']
            if not all(not any(FORB[o^q][s] for s in supp_of(U@assign[q][2].conj().T)) for q in prev): continue
            assign[o]=(P,k,U); rdfs(i+1,assign,classes,cnt,maxnodes); del assign[o]
        else:
            r=solve_new(P,ch[1],o,prev,assign)
            if r is None: continue
            p,t=r; V=mkV(ch[1],p); U=PM[P]@V
            if not all(not any(FORB[o^q][s] for s in supp_of(U@assign[q][2].conj().T)) for q in prev): continue
            classes.append(dict(g=ch[1],V=V,t=int(t))); assign[o]=(P,len(classes)-1,U)
            rdfs(i+1,assign,classes,cnt,maxnodes); del assign[o]; classes.pop()
def SHplus(U):
    """H.17.1 with the finest monomial grouping: o~q iff U_o U_q^dag is monomial (all Pauli terms share one X-part);
    class representative r, G=U_r, M_o=U_o U_r^dag monomial with X-part a(o); T = X-parts of the terms of G=U_r."""
    rep={}; a={}
    for o in range(8):
        for r in sorted(set(rep.values())):
            xs={px(s) for s in supp_of(U[o]@U[r].conj().T)}
            if len(xs)==1: rep[o]=r; a[o]=xs.pop(); break
        else: rep[o]=o; a[o]=0
    sh={r:sorted({px(s) for s in supp_of(U[r])}) for r in set(rep.values())}
    bad=0
    for o in range(8):
        for q in range(o+1,8):
            D=o^q; combos=[(0,0)] if rep[o]==rep[q] else it.product(sh[rep[o]],sh[rep[q]])
            if any(((a[o]^a[q]^t^t2)&D)==D for t,t2 in combos): bad+=1
    return bad
def SHplus2(U):
    """H.17.1 applied to W_o = U_o U_r^dag (common right unitary absorbed into the source state), best r."""
    return min(SHplus(np.einsum('oij,kj->oik',U,U[r].conj())) for r in range(8))
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
    bp=SHplus(U); res['shplus_fail']=res.get('shplus_fail',0)+(bp>0)
    if bp:
        bp2=SHplus2(U); res['shplus2_fail']=res.get('shplus2_fail',0)+(bp2>0)
        if bp2: np.save('shp2_%d_%d.npy'%(seed,n),U)
    if b: res['sh_fail']+=1; res['best_shfail']=max(res['best_shfail'],v)
    if canc:
        Pm=projectors(U); Mf=np.einsum('fr,rst->fst',T[:,:64],Pm)+T[:,64,None,None]*np.eye(8)
        ev,evec=np.linalg.eigh(Mf); f0=int(np.argmin(ev[:,0]))
        np.savez('tb_%d_%d.npz'%(seed,n),U=U,P=np.array([A[o][0] for o in range(8)]),k=np.array([A[o][1] for o in range(8)]),
                 g=json.dumps([list(map(int,c['g'])) for c in C]),phi=evec[f0][:,0],f0=f0,viol=v,shbad=b)
        print('TUNED',seed,n,'shbad',b,'viol',v,flush=True)
    if canc and len(ex)<30: ex.append(dict(P=[int(A[o][0]) for o in range(8)],k=[int(A[o][1]) for o in range(8)],g=[list(map(int,c['g'])) for c in C],shbad=b,viol=v))
    if v>1e-6: np.save('n2viol_%d_%d.npy'%(seed,n),U); print('VIOLATION',v,flush=True)
    if res['hard']%20==0: print(n,round(time.time()-t0),json.dumps(res),flush=True); json.dump(dict(res=res,ex=ex),open('ns2b_%d.json'%seed,'w'))
print('final',json.dumps(res),flush=True); json.dump(dict(res=res,ex=ex),open('ns2b_%d.json'%seed,'w'))
