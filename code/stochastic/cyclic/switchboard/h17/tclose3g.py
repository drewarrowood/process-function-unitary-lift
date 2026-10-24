"""Tuned closure, THREE NON-IDENTITY classes {V_a,V_b,V_c} with at least one tuned pair [exhaustive exact F2 over
symmetry-reduced class triples; over-approximating supports].  Job = (S_ab, S_ac, S_bc), pair supports fixed per class pair
(H.17.12 lists; any nonempty subset of K for K=K').  Root: absorb V_a (H.17.11a, translation-normalised groups, monomial merges)
and require a failing pair at o=0 (cube translation + global left Pauli).  Leaf: all three classes present and SH_grp^r fails for
every absorbed class.  Jobs: a over the 61 class orbits of (qubit permutations x diagonal S-gates) (t3sym.py), b over all classes
with (a,b) tuned, c over all classes, every pattern triple; duplicates (same supports up to the translations
(S_ab,S_ac,S_bc) -> (S_ab+t_b, S_ac+t_c, S_bc+t_b+t_c)) are solved once.  Checkpoint tclose3g_done.txt.gz (resumable)."""
import os, sys, json, gzip, itertools as it, collections, numpy as np, time
from multiprocessing import Pool
from tclose2 import FORB
from tclose3 import patterns, span, ST, Pa, Ka
from t3sym import reps, nonid, tuned
def solve(job, loosen=False):
    Sab,Sac,Sbc=job       # class 0=a (absorbed at the root), 1=b, 2=c
    Sup={(0,1):list(Sab),(0,2):list(Sac),(1,2):list(Sbc)}
    X=Pa[:,None]^Pa[None,:]; C={}
    for D in range(1,8):
        M=np.zeros((192,192),bool)
        for k in range(3):
            for l in range(3):
                blk=(slice(64*k,64*k+64),slice(64*l,64*l+64)); x=X[blk]
                if k==l: ok=~FORB[D][x]
                else:
                    ok=np.ones((64,64),bool)
                    for s in Sup[(min(k,l),max(k,l))]: ok&=~FORB[D][x^s]
                M[blk]=ok
        C[D]=M
    # group data for SH_grp^r: (group id, X-shift, H)
    def ns(S): x0=S[0]&7; return x0, span([(x&7)^x0 for x in S])
    mono=lambda S: len({x&7 for x in S})==1
    grp={0:(0,0,[0])}
    for k,S in ((1,Sab),(2,Sac)):
        x0,Hk=ns(list(S)); grp[k]=((0,x0,[0]) if mono(S) else (k,x0,Hk))
    if grp[1][0]==1 and grp[2][0]==2 and mono(Sbc): grp[2]=(1,grp[1][1]^(Sbc[0]&7),grp[1][2])
    def failpair(i,j,D):
        (P1,k1),(P2,k2)=ST[i],ST[j]; g1,s1,H1=grp[k1]; g2,s2,H2=grp[k2]
        if g1==g2: return False
        if loosen: return True
        a=(P1&7)^(P2&7)^s1^s2
        return any(((a^h^h2)&D)==D for h in H1 for h2 in H2)
    SS={(0,0):[0],(1,1):[0],(2,2):[0],(0,1):Sup[(0,1)],(1,0):Sup[(0,1)],(0,2):Sup[(0,2)],(2,0):Sup[(0,2)],(1,2):Sup[(1,2)],(2,1):Sup[(1,2)]}
    def fails_all(board):
        if len({k for P,k in board})<3: return False
        if loosen: return True
        for c in range(3):
            # groups: classes k,l merge when supp(V_k V_l^dag) is monomial; shift = its X-part (relative to rep)
            rep={};sh={}
            for k in range(3):
                for r in sorted(set(rep.values())):
                    if len({x&7 for x in SS[(k,r)]})==1: rep[k]=r; sh[k]=SS[(k,r)][0]&7; break
                else: rep[k]=k; sh[k]=0
            # H.17.11(a) with the monomial X^{x0} factored out of G_r: H = <x ^ x0>, shift x0 (translation-normalised support)
            x0={r:SS[(r,c)][0]&7 for r in set(rep.values())}
            Hc={r:span([(x&7)^x0[r] for x in SS[(r,c)]]) for r in set(rep.values())}
            bad=False
            for o in range(8):
                for q in range(o+1,8):
                    (P1,k1),(P2,k2)=board[o],board[q]
                    if rep[k1]==rep[k2]: continue
                    a=(P1&7)^(P2&7)^sh[k1]^sh[k2]^x0[rep[k1]]^x0[rep[k2]]; D=o^q
                    if any(((a^h^h2)&D)==D for h in Hc[rep[k1]] for h2 in Hc[rep[k2]]): bad=True; break
                if bad: break
            if not bad: return False
        return True
    budget=[200000]
    for k0 in range(3):
        i0=64*k0
        for D in range(1,8):
            dom={v:np.ones(192,bool) for v in range(8)}; dom[0]=np.zeros(192,bool); dom[0][i0]=True
            dom[D]=np.array([C[D][i0,j] and failpair(i0,j,D) for j in range(192)])
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
            order=sorted(range(8),key=lambda v:dom[v].sum()); sol={}
            def dfs(i,doms):
                budget[0]-=1
                if budget[0]<0: raise TimeoutError
                if i==8: return fails_all([ST[sol[v]] for v in range(8)])
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

def canon(Sab,Sac,Sbc):
    best=None
    for tb in Sab:
        for tc in Sac:
            k=(tuple(sorted(s^tb for s in Sab)),tuple(sorted(s^tc for s in Sac)),tuple(sorted(s^tb^tc for s in Sbc)))
            if best is None or k<best: best=k
    return best
def gen_jobs(ai):
    a=reps[ai]; seen=set(); out=[]
    for b in nonid:
        if not tuned(a,b): continue
        for c in nonid:
            for Sab in patterns(a,b):
                for Sac in patterns(a,c):
                    for Sbc in patterns(b,c):
                        k=canon(Sab,Sac,Sbc)
                        if k not in seen: seen.add(k); out.append(k)
    return out
if __name__=='__main__':
    CK='tclose3g_done.txt.gz'; done=set()
    if os.path.exists(CK):
        for l in gzip.open(CK,'rt'): done.add(int(l.split('\t')[0]))
    t0=time.time()
    with Pool(8) as pool:
        for ai in range(len(reps)):
            if ai in done: continue
            J=gen_jobs(ai); res=pool.map(solve,J,chunksize=200)
            cand=[(j,r) for j,r in zip(J,res) if r and r!='UNRESOLVED']; unr=[j for j,r in zip(J,res) if r=='UNRESOLVED']
            with gzip.open(CK,'at') as fo: fo.write('%d\t%s\n'%(ai,json.dumps(dict(rep=reps[ai],jobs=len(J),cand=cand,unresolved=unr))))
            print('orbit',ai,reps[ai],'jobs',len(J),'cand',len(cand),'unres',len(unr),round(time.time()-t0),flush=True)
    rows=[json.loads(l.split('\t')[1]) for l in gzip.open(CK,'rt')]
    print('SUMMARY orbits',len(rows),'of',len(reps),'jobs',sum(r['jobs'] for r in rows),'cand',sum(len(r['cand']) for r in rows),'unres',sum(len(r['unresolved']) for r in rows),flush=True)
