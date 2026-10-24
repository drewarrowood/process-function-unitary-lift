"""H.17.2 [exhaustive, exact; generic-support model]: a sign-variant pair (o,q) of one type-3 class that fails SH
pairwise can never be completed to an admissible cube.  For each pairwise-admissible SH-failing configuration
(class (A,B), sign change ds, R = P_o xor P_q, D = o xor q) we test necessary conditions on the intermediate vertices:
  |D|=2: some common neighbour m (= o xor e_k, k in D) must be compatible with o (edge k) and q (edge k');
  |D|=3: some path o - m1 - m2 - q with all six pairwise constraints among {o,m1,m2,q} (generic supports).
An intermediate vertex is either in the same class (sign pattern s, left Pauli P; all 4*64 options enumerated)
or in another class; for another class we use only the necessary edge conditions (both A and B trivial on the edge
party, which is required because every term of K across a cube edge must be trivial on that party) and ignore its
other constraints (over-approximation, so 'infeasible' is a proof)."""
from struct3 import *
def triv(s,t): return ((px(s)|pz(s))>>(2-t))&1==0
def parties(D): return [t for t in range(3) if (D>>(2-t))&1]
def same_ok(P1,s1,P2,s2,c,D): return not any(FORB[D][P1^P2^x] for x in S_same(c,s1^s2))
total=0;feasible=[]
for a,b in ANTI:
    c=(3,a,b)
    for ds in (1,2,3):
        for R in range(64):
            for D in range(1,8):
                if bin(D).count('1')<2: continue
                if any(FORB[D][R^s] for s in S_same(c,ds)): continue
                sh={0,px(a),px(b)}
                if not any((px(R)^t^u)&D==D for t in sh for u in sh): continue
                total+=1
                # place o at vertex 0 with P=0, sigma=0; q at vertex D with P=R, sigma=ds
                ks=parties(D); found=False
                if len(ks)==2:
                    for k in ks:
                        e=1<<(2-k); m=e; Dq=m^D   # m = o xor e_k ; edge m-q has direction the other party
                        other=all(triv(a,t) and triv(b,t) for t in ks)
                        ok_same=any(same_ok(0,0,P,s,c,m) and same_ok(P,s,R,ds,c,Dq) for P in range(64) for s in range(4))
                        if not (other or ok_same): break
                    else: found=True
                else:
                    for k1 in ks:
                        for k2 in ks:
                            if k2==k1: continue
                            m1=1<<(2-k1); m2=m1|(1<<(2-k2))
                            # options for m1, m2: ('s',P,s) same class or ('x',) other class
                            def opts(m,nbrs):
                                out=[('s',P,s) for P in range(64) for s in range(4)]
                                if all(triv(a,t) and triv(b,t) for t in range(3) if any((m^n)==(1<<(2-t)) for n in nbrs)): out.append(('x',))
                                return out
                            pos={0:('s',0,0),D:('s',R,ds)}
                            def cons(u,vu,v,vv):
                                Dd=u^v
                                if vu[0]=='s' and vv[0]=='s': return same_ok(vu[1],vu[2],vv[1],vv[2],c,Dd)
                                if bin(Dd).count('1')==1:
                                    t=parties(Dd)[0]; return triv(a,t) and triv(b,t)
                                return True
                            O1=[x for x in opts(m1,[0,m2]) if cons(0,pos[0],m1,x) and cons(m1,x,D,pos[D])]
                            O2=[y for y in opts(m2,[m1,D]) if cons(0,pos[0],m2,y) and cons(m2,y,D,pos[D])]
                            if any(cons(m1,x,m2,y) for x in O1 for y in O2): found=True;break
                        if found: break
                if found: feasible.append((a,b,ds,R,D))
print('pairwise-admissible SH-failing configurations:',total)
print('locally completable:',len(feasible)); print(feasible[:20])
# ---- full-cube check for the |D|=3 survivors: fill all six other vertices (same-class options exact, other-class over-approx)
def cube_completable(a,b,ds,R):
    c=(3,a,b)
    pos={0:('s',0,0),7:('s',R,ds)}
    def cons(u,vu,v,vv):
        Dd=u^v
        if vu[0]=='s' and vv[0]=='s': return same_ok(vu[1],vu[2],vv[1],vv[2],c,Dd)
        if vu[0]=='x' and vv[0]=='x': return True
        if bin(Dd).count('1')==1:
            t=parties(Dd)[0]; return triv(a,t) and triv(b,t)
        return True
    allopts=[('s',P,s) for P in range(64) for s in range(4)]+[('x',)]
    order=[4,2,1,6,5,3]
    dom={m:[x for x in allopts if cons(0,pos[0],m,x) and cons(m,x,7,pos[7])] for m in order}
    def rec(i):
        if i==len(order): return True
        m=order[i]
        for x in dom[m]:
            if all(cons(m,x,n,pos[n]) for n in order[:i]):
                pos[m]=x
                if rec(i+1): return True
                del pos[m]
        return False
    return rec(0), dict(pos)
surv=[]
for f in feasible:
    ok,pos=cube_completable(f[0],f[1],f[2],f[3])
    if ok: surv.append((f,pos))
print('|D|=3 survivors completable on the full cube (over-approx):',len(surv))
for f,pos in surv[:5]: print(f,pos)
