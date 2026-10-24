"""Symmetry group for the tuned closure: qubit permutations (acting on Pauli strings and cube labels together) x diagonal
S-gate conjugations on each qubit (z ^= x on that qubit).  S-conjugation: left S is diagonal (does not change p(i|o)), right S^dag
is absorbed into the source state; it preserves X-parts and the support-nontriviality pattern, hence the Pauli rule and SH_grp^r."""
import itertools as it, collections
from tclose3 import classes, patterns
def pbits(v,pi): return sum(((v>>i)&1)<<pi[i] for i in range(3))
def act(s,pi,m):
    x=s&7; z=s>>3; z^=x&m; return pbits(x,pi)|(pbits(z,pi)<<3)
G=[(pi,m) for pi in it.permutations(range(3)) for m in range(8)]
def cls_act(g,c): return tuple(sorted(act(s,*g) for s in c))
def Kof(c): return {0,*c,*([c[0]^c[1]] if len(c)==2 else [])}
nonid=classes[1:]; idx={c:i for i,c in enumerate(nonid)}
orb={}; reps=[]
for c in nonid:
    r=min(cls_act(g,c) for g in G); orb[c]=r
    if r==c: reps.append(c)
def tuned(a,b): return a==b or len(Kof(a)&Kof(b))>1
if __name__=='__main__':
    print('class orbits',len(reps))
    tot=0; tp=0
    for a in reps:
        part=[b for b in nonid if tuned(a,b)]
        tp+=len(part)
        for b in part:
            pab=len(patterns(a,b))
            for c in nonid:
                tot+=pab*len(patterns(a,c))*len(patterns(b,c))
    print('tuned partners',tp,'jobs (pattern products)',tot)
