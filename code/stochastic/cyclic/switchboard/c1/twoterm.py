"""C1 exact family: two-term Pauli-superposition boards U_o = cos(t) X^{w1(o)} + i sin(t) X^{w2(o)}, 0<t<pi/2.
(Unitary for all w1,w2 since X-strings commute and are Hermitian.)  Pauli rule (H.8.1), for o != o', D=supp(o^o'):
K = c^2 X^{a^a'} + s^2 X^{b^b'} + i s c (X^{b^a'} - X^{a^b'}) (a=w1(o), b=w2(o), a'=w1(o'), b'=w2(o')).
Allowed: string x is allowed iff x_k=0 for some k in D. Terms with distinct strings cannot cancel except the two
cross terms, which cancel iff b^a' == a^b'.  Enumerate all exclusive maps w (8^8 search by backtracking), then pairs."""
import itertools as it, json, numpy as np
B3=list(it.product((0,1),repeat=3))
D={(o,q):[k for k in range(3) if B3[o][k]!=B3[q][k]] for o in range(8) for q in range(8)}
def ok(x,Dl): return any(((x>>(2-k))&1)==0 for k in Dl)
def excl():
    out=[]; w=[0]*8
    def rec(o):
        if o==8: out.append(tuple(w)); return
        for v in range(8):
            if all(ok(v^w[q],D[(o,q)]) for q in range(o)):
                w[o]=v; rec(o+1)
    rec(0); return out
E=excl(); print('exclusive maps',len(E))
pairs=[]
for w1 in E:
    for w2 in E:
        good=True
        for o in range(8):
            for q in range(o):
                a,b,a2,b2=w1[o],w2[o],w1[q],w2[q]
                if (b^a2)==(a^b2): continue
                if not (ok(b^a2,D[(o,q)]) and ok(a^b2,D[(o,q)])): good=False;break
            if not good: break
        if good: pairs.append((w1,w2))
print('admissible (w1,w2) pairs',len(pairs), 'with w1!=w2',sum(1 for a,b in pairs if a!=b))
json.dump([list(map(list,p)) for p in pairs],open('twoterm_pairs.json','w'))
