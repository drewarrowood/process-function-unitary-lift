"""Tuned closure, THREE-CLASS boards {1, V_a, V_b} (identity class plus any two <=3-term classes, any tuning) [exhaustive exact F2].
Absorb the identity class (c = identity): G_0 = 1, G_a = V_a, G_b = V_b.  Pair supports, fixed per class pair:
  (0,a): supp V_a (no cancellation possible);  (0,b): supp V_b;  (a,b): S_ab from H.17.12 (generic / generic minus one collided
  string / any nonempty subset of K when K=K' -- the last an over-approximation, sound).
Groups: identity (H={0}); a (H_a=<X(gens a)>); b (H_b); a and b merge when S_ab is monomial (V_b = M V_a, M monomial with X-part m;
then a class-b vertex is treated as a class-a vertex with X-shift m).  Counterexample must fail SH_grp^r for this absorbed class
(necessary condition, so 'none' is a proof).  WLOG (cube translation, global left Pauli) the failing pair is o=0 with P=0.
States (P,k), k in {0,a,b}: 192 per vertex.  AC + DFS.  Leaf test (exact): a complete board counts as a candidate only if all three classes occur (otherwise it is a two-class
board, H.17.13) and it fails SH_grp^r for EVERY absorbed class c in {1, V_a, V_b}.  DFS node limit per job; jobs that hit it
are reported as UNRESOLVED.  Checkpoint tclose3_done.txt (resumable)."""
import os, sys, json, itertools as it, collections, numpy as np, time
from multiprocessing import Pool
from tclose2 import FORB, anti, classes
def patterns(g,g2):
    m=collections.Counter(u2^u for u2 in (0,)+g2 for u in (0,)+g); gen=set(m)
    if max(m.values())>=3:
        K=sorted(gen); return [tuple(sorted(c)) for r in range(1,len(K)+1) for c in it.combinations(K,r)]
    coll=[s for s in m if m[s]==2]; return [tuple(sorted(gen))]+[tuple(sorted(gen-{s})) for s in coll]
def span(xs):
    H={0}
    for x in xs: H|={h^x for h in H}
    return sorted(H)
ST=[(P,k) for k in range(3) for P in range(64)]
Pa=np.array([p for p,k in ST]); Ka=np.array([k for p,k in ST])
def solve(job, loosen=False):
    ga,gb,Sab=job
    Sup={(0,1):[0]+list(ga),(0,2):[0]+list(gb),(1,2):list(Sab)}
    merged=len({s&7 for s in Sab})==1
    H={0:[0],1:span([s&7 for s in ga]),2:span([s&7 for s in gb])}
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
    m=(Sab[0]&7) if merged else 0
    grp={0:(0,0,H[0]),1:(1,0,H[1]),2:((1,m,H[1]) if merged else (2,0,H[2]))}
    def failpair(i,j,D):
        (P1,k1),(P2,k2)=ST[i],ST[j]; g1,s1,H1=grp[k1]; g2,s2,H2=grp[k2]
        if g1==g2: return False
        if loosen: return True
        a=(P1&7)^(P2&7)^s1^s2
        return any(((a^h^h2)&D)==D for h in H1 for h2 in H2)
    SS={(0,0):[0],(1,1):[0],(2,2):[0],(0,1):Sup[(0,1)],(1,0):Sup[(0,1)],(0,2):Sup[(0,2)],(2,0):Sup[(0,2)],(1,2):list(Sab),(2,1):list(Sab)}
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
def jobs():
    nonid=classes[1:]; out=[]
    for ga in nonid:
        for gb in nonid:
            if ga>gb: continue
            Ka={0,*ga,*( [ga[0]^ga[1]] if len(ga)==2 else [])}; Kb={0,*gb,*( [gb[0]^gb[1]] if len(gb)==2 else [])}
            if len(Ka&Kb)==1 and ga!=gb: continue        # untuned pair: generic boards, covered by H.17.9
            for S in patterns(ga,gb): out.append((ga,gb,S))
    return out
if __name__=='__main__':
    t0=time.time(); J=jobs(); print('jobs',len(J),flush=True)
    done=set()
    if os.path.exists('tclose3_done.txt'):
        for l in open('tclose3_done.txt'): done.add(l.split('\t')[0])
    todo=[j for j in J if str(j) not in done]
    with Pool(8) as pool, open('tclose3_done.txt','a') as fo:
        for n,(j,r) in enumerate(zip(todo,pool.imap(solve,todo,chunksize=50))):
            fo.write(str(j)+'\t'+json.dumps(r)+'\n')
            if r: print('CANDIDATE' if r!='UNRESOLVED' else 'UNRESOLVED',j,r,flush=True)
            if n%5000==0: fo.flush(); print(n,len(todo),round(time.time()-t0),flush=True)
    res=[l.split('\t')[1].strip() for l in open('tclose3_done.txt')]
    print('SUMMARY jobs',len(J),'checked',len(res),'candidates',sum(r not in ('null','"UNRESOLVED"') for r in res),'unresolved',sum(r=='"UNRESOLVED"' for r in res),flush=True)
