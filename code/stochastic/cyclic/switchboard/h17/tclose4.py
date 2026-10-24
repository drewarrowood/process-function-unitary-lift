"""H.17.16 part (2): tuned closure with k >= 4 classes, k-class generalisation of tclose3g.solve [exhaustive exact F2 on the
family searched; over-approximating per-class-pair supports, so 'no candidate' is a proof for that family].
Family KC ("Klein cluster", the most cancellation-rich family): all classes lie inside one Klein group K = {1,A,B,AB}
(A,B anticommuting): the 2-term classes (A),(B),(AB) and the 3-term classes (A,B),(A,AB),(B,AB).  K runs over the G48-orbit
representatives of Klein groups (t3sym action), the class set over all k-subsets (k=4,5,6) containing a 3-term class
(the absorbed class 0).  Pair supports from tclose3.patterns (H.17.12; any nonempty subset of K when K=K').
Job filters, both PROVED necessary: (A) no pair support is a single string (else the two classes are one unitary up to a left
Pauli and the board has fewer classes); (B) triple consistency S_ik within S_ij + S_jk for every triple (H.17.15 lemma).
Root and leaf exactly as tclose3g (root: absorbed class 0 fails SH_grp^r at (0,D); leaf: all k classes present and SH_grp^r
fails for every absorbed class, groups merging on X-monomial supports).  Checkpoint tclose4_done.txt.gz (resumable:
rerun the same command; finished (K,k) blocks are skipped)."""
import os, sys, json, gzip, itertools as it, numpy as np, time
from multiprocessing import Pool
from tclose2 import FORB
from tclose3 import patterns, span
from t3sym import G, act
BUDGET=200000
def solve(job, loosen=False):
    k=len(job['cls']); Sup={tuple(map(int,p.split(','))):S for p,S in job['sup'].items()}
    ST=[(P,c) for c in range(k) for P in range(64)]; Pa=np.array([p for p,c in ST]); n=64*k
    SS={(i,i):[0] for i in range(k)}
    for (i,j),S in Sup.items(): SS[(i,j)]=list(S); SS[(j,i)]=list(S)
    X=Pa[:,None]^Pa[None,:]; C={}
    for D in range(1,8):
        M=np.zeros((n,n),bool)
        for a in range(k):
            for b in range(k):
                blk=(slice(64*a,64*a+64),slice(64*b,64*b+64)); x=X[blk]
                if a==b: ok=~FORB[D][x]
                else:
                    ok=np.ones((64,64),bool)
                    for s in SS[(a,b)]: ok&=~FORB[D][x^s]
                M[blk]=ok
        C[D]=M
    def groups(c):
        rep={};sh={}
        for a in range(k):
            for r in sorted(set(rep.values())):
                if len({x&7 for x in SS[(a,r)]})==1: rep[a]=r; sh[a]=SS[(a,r)][0]&7; break
            else: rep[a]=a; sh[a]=0
        x0={r:SS[(r,c)][0]&7 for r in set(rep.values())}
        Hc={r:span([(x&7)^x0[r] for x in SS[(r,c)]]) for r in set(rep.values())}
        return rep,sh,x0,Hc
    G0=groups(0)
    def failpair(i,j,D,g=G0):
        rep,sh,x0,Hc=g; (P1,k1),(P2,k2)=ST[i],ST[j]
        if rep[k1]==rep[k2]: return False
        if loosen: return True
        a=(P1&7)^(P2&7)^sh[k1]^sh[k2]^x0[rep[k1]]^x0[rep[k2]]
        return any(((a^h^h2)&D)==D for h in Hc[rep[k1]] for h2 in Hc[rep[k2]])
    GA=[groups(c) for c in range(k)]
    def fails_all(sol):
        if len({ST[sol[v]][1] for v in range(8)})<k: return False
        if loosen=='hard' and any(all(sol[o]==sol[o^(1<<j)] for o in range(8)) for j in range(3)): return False
        if loosen: return True
        for g in GA:
            if not any(failpair(sol[o],sol[q],o^q,g) for o in range(8) for q in range(o+1,8)): return False
        return True
    budget=[BUDGET]
    for k0 in range(k):
        i0=64*k0
        for D in range(1,8):
            dom={v:np.ones(n,bool) for v in range(8)}; dom[0]=np.zeros(n,bool); dom[0][i0]=True
            dom[D]=np.array([C[D][i0,j] and failpair(i0,j,D) for j in range(n)])
            if not dom[D].any(): continue
            for v in range(1,8):
                if v!=D: dom[v]&=C[v][i0]
            changed=True; dead=False
            while changed and not dead:
                changed=False
                for v in range(1,8):
                    for w in range(8):
                        if v==w: continue
                        nd=dom[v]&C[v^w][:,dom[w]].any(1)
                        if (nd!=dom[v]).any(): dom[v]=nd; changed=True
                        if not nd.any(): dead=True; break
                    if dead: break
            if dead: continue
            # every class must still be available somewhere
            if any(not any(dom[v][64*c:64*c+64].any() for v in range(8)) for c in range(k)): continue
            order=sorted(range(8),key=lambda v:dom[v].sum()); sol={}
            def dfs(i,doms):
                budget[0]-=1
                if budget[0]<0: raise TimeoutError
                if i==8: return fails_all(sol)
                v=order[i]
                for x in np.nonzero(doms[v])[0]:
                    nd={w:(doms[w]&C[v^w][x]) if (w not in sol and w!=v) else doms[w] for w in doms}
                    if any(not nd[w].any() for w in nd if w not in sol and w!=v): continue
                    sol[v]=x
                    if dfs(i+1,nd): return True
                    del sol[v]
                return False
            try:
                if dfs(0,dom): return dict(k0=k0,D=D,board=[ST[sol[v]] for v in range(8)])
            except TimeoutError: return 'UNRESOLVED'
    return None
def sums(A,B): return {a^b for a in A for b in B}
def klein_reps():
    Ks=set()
    for A in range(1,64):
        for B in range(A+1,64):
            from tclose2 import anti
            if anti(A,B): Ks.add(frozenset((A,B,A^B)))
    reps=sorted({min(tuple(sorted(act(s,*g) for s in K)) for g in G) for K in Ks})
    return reps,len(Ks)
def cluster(K):
    A,B,C_=K; two=[(A,),(B,),(C_,)]; three=[tuple(sorted(p)) for p in ((A,B),(A,C_),(B,C_))]
    return three+two
def gen_jobs(K,k):
    cl=cluster(K); out=[]; seen=set()
    for sub in it.combinations(range(6),k):
        if sub[0]>2: continue                      # class 0 must be 3-term (absorbed at the root)
        cls=[cl[i] for i in sub]; prs=list(it.combinations(range(k),2))
        pl=[patterns(cls[i],cls[j]) for i,j in prs]
        for choice in it.product(*pl):
            sup=dict(zip(prs,choice))
            if any(len(S)==1 for S in choice): continue
            ok=True
            for i,j,l in it.combinations(range(k),3):
                a,b,c=set(sup[(i,j)]),set(sup[(i,l)]),set(sup[(j,l)])
                if not (b<=sums(a,c) and a<=sums(b,c) and c<=sums(a,b)): ok=False; break
            if not ok: continue
            key=(tuple(sub),tuple(choice))
            if key in seen: continue
            seen.add(key); out.append(dict(cls=cls,sup={'%d,%d'%p:list(S) for p,S in sup.items()}))
    return out
if __name__=='__main__':
    CK='tclose4_done.txt.gz'; done=set()
    if os.path.exists(CK):
        for l in gzip.open(CK,'rt'): done.add(tuple(json.loads(l)['blk']))
    reps,nK=klein_reps(); print('Klein groups',nK,'G48 orbits',len(reps),reps,flush=True)
    ks=[int(a) for a in sys.argv[1:]] or [4,5,6]
    t0=time.time()
    with Pool(int(os.environ.get('NPROC','3'))) as pool:
        for k in ks:
            for ki,K in enumerate(reps):
                if (ki,k) in done: continue
                J=gen_jobs(K,k); res=pool.map(solve,J,chunksize=20)
                cand=[(j,r) for j,r in zip(J,res) if r and r!='UNRESOLVED']; unr=[j for j,r in zip(J,res) if r=='UNRESOLVED']
                with gzip.open(CK,'at') as fo: fo.write(json.dumps(dict(blk=[ki,k],K=K,jobs=len(J),cand=cand,unresolved=unr))+'\n')
                print('k',k,'K',ki,K,'jobs',len(J),'cand',len(cand),'unres',len(unr),round(time.time()-t0),flush=True)
    rows=[json.loads(l) for l in gzip.open(CK,'rt')]
    print('SUMMARY blocks',len(rows),'jobs',sum(r['jobs'] for r in rows),'cand',sum(len(r['cand']) for r in rows),'unres',sum(len(r['unresolved']) for r in rows),flush=True)
