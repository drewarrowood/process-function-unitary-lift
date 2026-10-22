"""Coset-transport theorem (H.10.6) hypothesis check for all admissible two-term boards (exact, combinatorial).
For U_o = X^{w1(o)}(c + i s X^{d(o)}), d = w1^w2: classes = level sets of d. Hypothesis: for every choice
sigma: classes -> {0,1}, the map m(o) = w1(o) if sigma(class(o))=0 else w2(o) is a PF (pairwise exclusive, H.10.3)."""
import json, itertools as it
B3=list(it.product((0,1),repeat=3))
D={(o,q):[k for k in range(3) if B3[o][k]!=B3[q][k]] for o in range(8) for q in range(8)}
def okx(x,Dl): return any(((x>>(2-k))&1)==0 for k in Dl)
def isPF(m): return all(okx(m[o]^m[q],D[(o,q)]) for o in range(8) for q in range(o))
P=json.load(open('twoterm_pairs.json')); bad=0; full=0; n=0
for w1,w2 in P:
    if w1==w2: continue
    n+=1; d=[a^b for a,b in zip(w1,w2)]; cl=sorted(set(d))
    ok=all(isPF([w2[o] if sig[cl.index(d[o])] else w1[o] for o in range(8)]) for sig in it.product((0,1),repeat=len(cl)))
    bad+= not ok
    full+= all(isPF([w2[o] if S>>o&1 else w1[o] for o in range(8)]) for S in range(256))
print('nontrivial pairs',n,'class-mixture hypothesis fails for',bad,'| all 256 free mixtures PF for',full)
