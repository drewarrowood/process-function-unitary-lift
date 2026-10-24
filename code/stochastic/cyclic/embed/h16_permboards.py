"""Round 16: reversible classical boards beyond XOR: V|o,s> = |f_s(o)>_AI |o>_F with every f_s a PF and s -> f_s(o) a bijection
for each o.  Check quantum validity (Araujo projector penalty) of Tr_F|V>><<V|."""
import numpy as np, torch, sys
sys.argv=[sys.argv[0],'0','0']
from h16_gen_search import penalty, violations
P=np.load('../pfs744.npy')
fn=P.argmax(1)            # fn[k,o] = i
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def sample():
    ch=[]; used=np.zeros((8,8),bool)
    def rec(s):
        if s==8: return True
        for k in rng.permutation(744):
            if not used[np.arange(8),fn[k]].any():
                used[np.arange(8),fn[k]]=True; ch.append(k)
                if rec(s+1): return True
                used[np.arange(8),fn[k]]=False; ch.pop()
        return False
    rec(0); return ch
def Vof(ch):
    V=np.zeros((64,64))
    for s,k in enumerate(ch):
        for o in range(8): V[8*fn[k,o]+o,8*o+s]=1
    return V
stats={'xor':0,'nonxor':0,'valid_nonxor':0}; pens=[]
for t in range(200):
    ch=sample(); V=Vof(ch); pen=float(penalty(torch.tensor(V,dtype=torch.complex128)))
    xor=all(len({fn[k,o]^s for s,k in enumerate(ch)})==1 for o in range(8))
    stats['xor' if xor else 'nonxor']+=1; pens.append(pen)
    if not xor and pen<1e-9: stats['valid_nonxor']+=1; print('VALID non-XOR board',ch)
    if t<10: print(t,ch,'pen',pen,'xor',xor)
print(stats,'residual min %.4g max %.4g'%(min(pens),max(pens)))
