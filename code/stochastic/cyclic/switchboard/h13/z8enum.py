"""H.14: exhaustive enumeration of Z_N X-type pure switchboards (N=8 default), exact integer Pauli-rule test.
U_o = Hd diag(zeta^{m_o(z)}) Hd, zeta = e^{2 pi i/N}; gauge m_000=0, m_o(000)=0.  zeta^k represented exactly
in the integer basis {1,zeta,...,zeta^{N/2-1}} (zeta^{N/2}=-1)."""
import numpy as np, itertools as it, sys
N=int(sys.argv[1]) if len(sys.argv)>1 else 8; h=N//2
B3=list(it.product((0,1),repeat=3)); H=np.array([[(-1)**(sum(a*b for a,b in zip(x,y))%2) for y in B3] for x in B3])
Zb=np.zeros((N,h),np.int64)
for k in range(N): Zb[k,k%h]=1 if k<h else -1
def allowed(Dm,delta):  # delta [n,8] ints mod N -> bool [n]
    D=[t for t in range(3) if (Dm>>(2-t))&1]; bad=[ai for ai,a in enumerate(B3) if all(a[t] for t in D)]
    V=Zb[delta%N]                       # [n,8,h]
    C=np.einsum('az,nzc->nac',H[bad],V)  # exact integer Fourier coefficients
    return ~(C!=0).any((1,2))
# edge differences: functions of z independent of z_k, normalized value 0 at z=000
def edgeset(k):
    others=[t for t in range(3) if t!=k]; out=[]
    for vals in it.product(range(N),repeat=3):
        f=dict(zip([(0,1),(1,0),(1,1)],vals)); f[(0,0)]=0
        out.append([f[(z[others[0]],z[others[1]])] for z in B3])
    return np.array(out)
E={k:edgeset(k) for k in range(3)}
order=[0b000,0b100,0b010,0b001,0b110,0b101,0b011,0b111]
parts=np.zeros((1,8,8),np.int64)
for step,o in enumerate(order[1:],1):
    prev=order[:step]; nb=next(q for q in prev if bin(o^q).count('1')==1); k=[t for t in range(3) if (o^nb)>>(2-t)&1][0]
    res=[]
    for ch in np.array_split(parts,max(1,len(parts)//300)):
        new=(ch[:,nb][:,None,:]+E[k][None])%N
        cand=np.broadcast_to(ch[:,None],(len(ch),len(E[k]),8,8)).copy(); cand[:,:,o]=new
        cand=cand.reshape(-1,8,8); ok=np.ones(len(cand),bool)
        for q in prev:
            if q==nb: continue
            idx=np.nonzero(ok)[0]; ok[idx]=allowed(o^q,cand[idx,o]-cand[idx,q])
        res.append(cand[ok].astype(np.uint8))
    parts=np.concatenate(res).astype(np.int64); print('N',N,'after',format(o,'03b'),len(parts),flush=True)
np.save('xboards_z%d_full.npy'%N,parts.astype(np.uint8))
