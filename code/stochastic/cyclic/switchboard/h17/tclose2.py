"""Tuned closure, TWO-CLASS boards [exhaustive, exact F2; over-approximating supports].
A board with exactly two distinct unitaries (up to left Paulis): U_o = P_o V or P_o V'.  Absorb V into the source (H.17.11a):
W_o = P_o G^{b(o)}, G = V'V^dag, b in {0,1}.  Everything (admissibility and SH_grp^r) depends only on S = supp(G).
S ranges over all supports allowed by H.17.12 for all ordered pairs of <=3-term classes (identity, 63 two-term, 1,008 three-term):
  no collision -> generic product support;  two-contribution collisions -> generic, or generic minus exactly one collided string
  (H.17.12c, proved);  K=K' type -> ANY nonempty subset of K (over-approximation of H.17.12b, sound).
Monomial S (one X-part) merges the classes -> PF blend; skipped.  Normalise S by a left translation so that 0 in S.
Search: WLOG (cube translation, global left Pauli, G<->G^dag) the failing pair is o=0 with state (P=0,b=0) and q=D with b=1.
Pair compat: same b -> P^P' allowed for D; different b -> every P^P'^s (s in S) allowed.  SH_grp^r fails at (o,q) iff
some h in H=<X(S)> has ((x(P_o^P_q)^h)&D)==D.  Arc consistency + DFS over the six other vertices (128 states each).
Checkpoint: tclose2_done.txt (one canonical S per line with result); resumable."""
import sys, os, json, itertools as it, collections, numpy as np, time
from multiprocessing import Pool
def anti(s,t): return (bin((s&7)&(t>>3)).count('1')+bin((s>>3)&(t&7)).count('1'))%2
def forb(s,D): return (((s&7)|(s>>3))&D)==D
FORB=np.array([[forb(s,D) if D else False for s in range(64)] for D in range(8)])
classes=[()]+[(a,) for a in range(1,64)]+[(a,b) for a in range(1,64) for b in range(a+1,64) if anti(a,b)]
def canon(S):
    best=None
    for t in S:
        c=tuple(sorted(s^t for s in S))
        if best is None or c<best: best=c
    return best
def supports():
    out=set()
    for g in classes:
        for g2 in classes:
            m=collections.Counter(u2^u for u2 in (0,)+g2 for u in (0,)+g)
            gen=set(m)
            if max(m.values())>=3:
                K=sorted(gen); cand=[set(c) for r in range(1,len(K)+1) for c in it.combinations(K,r)]
            else:
                coll=[s for s in m if m[s]==2]; cand=[gen]+[gen-{s} for s in coll]
            for S in cand:
                if len({s&7 for s in S})>1: out.add(canon(S))
    return sorted(out)
ST=[(P,b) for b in (0,1) for P in range(64)]   # index i -> state
def solve(S):
    S=list(S); H={0}
    for s in S: H|={h^(s&7) for h in H}
    Pa=np.array([p for p,b in ST]); Ba=np.array([b for p,b in ST]); X=Pa[:,None]^Pa[None,:]; same=Ba[:,None]==Ba[None,:]
    C={}
    for D in range(1,8):
        ok_same=~FORB[D][X]
        ok_diff=np.ones_like(ok_same)
        for s in S: ok_diff&=~FORB[D][X^s]
        C[D]=np.where(same,ok_same,ok_diff)
    fail={}
    for D in range(1,8):
        f=np.zeros(128,bool)
        for i,(P,b) in enumerate(ST):
            if b==1: f[i]=any((((P&7)^h)&D)==D for h in H)
        fail[D]=f
    for D in range(1,8):
        dom={v:np.ones(128,bool) for v in range(8)}
        dom[0]=np.zeros(128,bool); dom[0][0]=True
        dom[D]=fail[D]&C[D][0]
        if not dom[D].any(): continue
        for v in range(1,8):
            if v!=D: dom[v]&=C[v][0]
        # arc consistency
        changed=True
        while changed:
            changed=False
            for v in range(8):
                for w in range(8):
                    if v==w: continue
                    nd=dom[v]&(C[v^w][:,dom[w]].any(1))
                    if (nd!=dom[v]).any(): dom[v]=nd; changed=True
                    if not nd.any(): break
                if not dom[v].any(): break
            if not dom[v].any(): break
        if any(not dom[v].any() for v in range(8)): continue
        # DFS
        order=sorted(range(8),key=lambda v:dom[v].sum())
        sol={}
        def dfs(i,doms):
            if i==8: return True
            v=order[i]
            for x in np.nonzero(doms[v])[0]:
                nd={w:(doms[w]&C[v^w][x]) if w not in sol and w!=v else doms[w] for w in doms}
                if any(not nd[w].any() for w in nd if w not in sol and w!=v): continue
                sol[v]=x
                if dfs(i+1,nd): return True
                del sol[v]
            return False
        if dfs(0,dom): return dict(D=D,board=[ST[sol[v]] for v in range(8)])
    return None
if __name__=='__main__':
    t0=time.time(); Ss=supports(); print('canonical non-monomial supports',len(Ss),round(time.time()-t0),'s',flush=True)
    done={}
    if os.path.exists('tclose2_done.txt'):
        for l in open('tclose2_done.txt'): k,v=l.split('\t'); done[k]=v
    todo=[S for S in Ss if str(S) not in done]
    with Pool(8) as pool, open('tclose2_done.txt','a') as fo:
        for n,(S,r) in enumerate(zip(todo,pool.imap(solve,todo,chunksize=20))):
            fo.write(str(S)+'\t'+json.dumps(r)+'\n')
            if r: print('CANDIDATE',S,r,flush=True)
            if n%2000==0: fo.flush(); print(n,len(todo),round(time.time()-t0),flush=True)
    res=[json.loads(l.split('\t')[1]) for l in open('tclose2_done.txt')]
    print('SUMMARY supports',len(Ss),'checked',len(res),'candidates',sum(r is not None for r in res),flush=True)
