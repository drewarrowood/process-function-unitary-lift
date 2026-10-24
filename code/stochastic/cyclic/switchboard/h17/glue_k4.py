"""H.17.17(e): EXHAUSTIVE search of all admissible <=3-term boards with exactly four classes [exact over F2, in the
per-class-pair model of H.17.13-H.17.16 with over-approximating H.17.12 supports; 'no candidate' is a proof].
Input: glue_k4_tuples.json from glue_k4enum.py = every labelled geometry (class of every vertex) a 4-class board can have
(Lemma H: each class on exactly two vertices; Lemma B adjacency; vertex 0 carries a G48-orbit representative).
Per geometry: every assignment of one H.17.12 pattern to each class pair, filtered by Lemma A (|S| >= 2), the exact K = K' list of H.17.12(b) (no {1, C}), Lemma B
(a pair adjacent along q has a q-constant support) and Lemma C (triple consistency).  Per assignment: P_0 = 0 (common left
Pauli, PROVED harmless), P_o for the other 7 vertices over all 64 Paulis with arc consistency on the Pauli rule; root =
a pair (o,q) at which SH_grp^r fails for the absorbed class r = class of vertex 0 (every counterexample has one); leaf =
no W-level-last party (H.1), no operator-first party (H.6.2), and SH_grp^r fails for every absorbed
class (Lemma D local test).  LOOSEN=1: control run whose leaf only asks for a hard board (no root, no SH test).  Checkpoint glue_k4_done.jsonl (resumable)."""
import os, sys, json, ast, time, itertools as it, numpy as np
from multiprocessing import Pool
from tclose2 import FORB
from tclose3 import patterns
from t3sym import Kof
BUDGET=int(os.environ.get('BUDGET','2000000')); LOOSEN=os.environ.get('LOOSEN')=='1'
def qp(s,p): return ((s>>p)&1,(s>>(3+p))&1)
def qconst(S,q): return len({qp(s,q) for s in S})==1
def aff(xs):
    xs=list(xs); x0=xs[0]; H={0}
    for x in xs: H|={h^x^x0 for h in H}
    return sorted({x0^h for h in H})
XOR=np.arange(64)[:,None]^np.arange(64)[None,:]
def assignments(L,cid):
    prs=list(it.combinations(range(4),2))
    adj={p:set() for p in prs}
    for v in range(8):
        for q in range(3):
            w=v^(1<<q)
            if cid[v]!=cid[w]: adj[tuple(sorted((cid[v],cid[w])))].add(q)
    pl=[]
    for c,d in prs:
        Ss=[]
        same=len(L[c])==2 and len(L[d])==2 and Kof(L[c])==Kof(L[d])
        for S in dict.fromkeys(tuple(S) for S in patterns(L[c],L[d]) if len(S)>=2):
            if same and len(S)==2 and 0 in S: continue     # H.17.12(b): K = K' never gives {1, C}
            if all(qconst(S,q) for q in adj[(c,d)]): Ss.append(frozenset(S))
        pl.append(Ss)
    for combo in it.product(*pl):
        Sd=dict(zip(prs,combo))
        ok=True
        for a,b,c in it.combinations(range(4),3):
            A,B,C=Sd[(a,b)],Sd[(a,c)],Sd[(b,c)]
            if not (B<={x^y for x in A for y in C} and A<={x^y for x in B for y in C} and C<={x^y for x in A for y in B}): ok=False; break
        if ok: yield Sd
def solve(cid,Sd):
    SS={}
    for c in range(4):
        SS[(c,c)]=[0]
        for d in range(4):
            if c<d: SS[(c,d)]=SS[(d,c)]=sorted(Sd[(c,d)])
    AL={}
    for u in range(8):
        for w in range(8):
            if u==w: continue
            D=u^w; ok=np.ones((64,64),bool)
            for s in SS[(cid[u],cid[w])]: ok&=~FORB[D][XOR^s]
            AL[(u,w)]=ok
    mono={(c,d):len({s&7 for s in SS[(c,d)]})==1 for c in range(4) for d in range(4)}
    FA={}   # FA[r][(u,w)] : bool array over a = x(P_u ^ P_w) in 0..7
    for r in range(4):
        Af={c:aff([s&7 for s in SS[(c,r)]]) for c in range(4)}
        for u in range(8):
            for w in range(u+1,8):
                c,d=cid[u],cid[w]; D=u^w
                FA[(r,u,w)]=np.array([(not mono[(c,d)]) and any(((a^x^y)&D)==D for x in Af[c] for y in Af[d]) for a in range(8)])
    def nonhard(P):
        # W-level last party p (H.1): every p-edge ratio K has X-part set {0}; operator-first party p (H.6.2): every
        # ratio K_{u,w} acts trivially on qubit p.  Either one makes the board a PF blend, so such leaves are discarded.
        for p in range(3):
            if all(((P[u]^P[u^(1<<p)]^s)&7)==0 for u in range(8) for s in SS[(cid[u],cid[u^(1<<p)])]): return True
            if all(qp(P[u]^P[w]^s,p)==(0,0) for u in range(8) for w in range(8) if u!=w for s in SS[(cid[u],cid[w])]): return True
        return False
    def fails_all(P):
        if nonhard(P): return False
        for r in range(4):
            if not any(FA[(r,u,w)][(P[u]^P[w])&7] for u in range(8) for w in range(u+1,8)): return False
        return True
    r0=cid[0]; budget=[BUDGET]; found=[None]
    # quick exit: no admissible Pauli assignment at all (plain arc consistency, P_0 = 0)
    dom={v:np.ones(64,bool) for v in range(8)}; dom[0]=np.zeros(64,bool); dom[0][0]=True; ch=True
    while ch:
        ch=False
        for v in range(8):
            for w in range(8):
                if v==w: continue
                nd=dom[v]&AL[(v,w)][:,dom[w]].any(1)
                if not nd.any(): return None
                if (nd!=dom[v]).any(): dom[v]=nd; ch=True
    for u0,w0 in it.combinations(range(8),2):
        if LOOSEN and (u0,w0)!=(0,1): continue
        if not LOOSEN and not FA[(r0,u0,w0)].any(): continue
        C=dict(AL); fm=np.ones((64,64),bool) if LOOSEN else FA[(r0,u0,w0)][XOR&7]
        C[(u0,w0)]=AL[(u0,w0)]&fm; C[(w0,u0)]=C[(u0,w0)].T
        dom={v:np.ones(64,bool) for v in range(8)}; dom[0]=np.zeros(64,bool); dom[0][0]=True
        def ac(dom):
            ch=True
            while ch:
                ch=False
                for v in range(8):
                    for w in range(8):
                        if v==w: continue
                        nd=dom[v]&C[(v,w)][:,dom[w]].any(1)
                        if not nd.any(): return False
                        if (nd!=dom[v]).any(): dom[v]=nd; ch=True
            return True
        if not ac(dom): continue
        P={}
        def dfs(dom):
            budget[0]-=1
            if budget[0]<0: raise TimeoutError
            free=[v for v in range(8) if v not in P]
            if not free: return (not nonhard(P)) if LOOSEN else fails_all(P)
            v=min(free,key=lambda v:dom[v].sum())
            for x in np.nonzero(dom[v])[0]:
                nd={w:dom[w].copy() for w in dom}; nd[v]=np.zeros(64,bool); nd[v][x]=True
                if not ac(nd): continue
                P[v]=int(x)
                if dfs(nd): return True
                del P[v]
            return False
        try:
            if dfs(dom): return dict(root=(u0,w0),P=P)
        except TimeoutError: return 'UNRESOLVED'
    return None
def work(item):
    gi,L,cid=item; n=0; cand=[]; unr=0
    for Sd in assignments(L,cid):
        n+=1; r=solve(cid,Sd)
        if r=='UNRESOLVED': unr+=1
        elif r is not None: cand.append(dict(sup={'%d,%d'%k:sorted(v) for k,v in Sd.items()},sol=r))
    return dict(g=gi,jobs=n,cand=cand,unres=unr)
def items():
    T=json.load(open('glue_k4_tuples.json'))
    for gi,t in enumerate(T):
        pr=ast.literal_eval(t['geo'][0]); cid={v:i for i,p in enumerate(pr) for v in p}
        order=[cid[0]]+[i for i in range(4) if i!=cid[0]]
        L={order[j]:tuple(t['cls'][j]) for j in range(4)}
        yield gi,L,cid
if __name__=='__main__':
    NP=int(os.environ.get('NPROC','2')); lim=int(sys.argv[1]) if len(sys.argv)>1 else None
    CK='glue_k4_loose.jsonl' if LOOSEN else 'glue_k4_done.jsonl'; done=set()
    if os.path.exists(CK):
        for l in open(CK): done.add(json.loads(l)['g'])
    keep=set(json.load(open('glue_k4_canon.json')))   # one geometry per symmetry orbit (glue_k4canon.py)
    todo=[it_ for it_ in items() if it_[0] in keep and it_[0] not in done][:lim]
    print('geometries',len(todo),'to do; budget',BUDGET,flush=True); t0=time.time(); J=C=U=0
    with Pool(NP) as pool, open(CK,'a') as f:
        for n,res in enumerate(pool.imap_unordered(work,todo,chunksize=4)):
            f.write(json.dumps(res)+'\n'); f.flush(); J+=res['jobs']; C+=len(res['cand']); U+=res['unres']
            if res['cand'] or res['unres']: print('g',res['g'],'CAND',len(res['cand']),'UNRES',res['unres'],flush=True)
            if n%200==0: print(n,'geometries',J,'jobs',C,'cand',U,'unres',round(time.time()-t0),'s',flush=True)
    print('SUMMARY geometries',len(todo),'jobs',J,'cand',C,'unres',U,round(time.time()-t0),'s',flush=True)
