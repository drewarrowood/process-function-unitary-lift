"""H.13: exhaustive enumeration of Z_4 X-type switchboards U_o = Hd diag(i^{m_o(z)}) Hd (three binary parties).
Gauge: m_000 = 0 (common right factor absorbed into source), each m_o(z=000)=0 (global phase).
Pauli rule H.8.1 for X-type K = Hd diag(i^{m_o-m_o'}) Hd: Fourier coeff of i^{Delta} vanishes at every a >= D(o,o').
Exact: coefficients are Gaussian integers / 8; tested via integer arithmetic."""
import numpy as np, itertools as it
B3=list(it.product((0,1),repeat=3))
D4=np.array(list(it.product(range(4),repeat=8)),dtype=np.int64)   # [65536,8], index = base-4 digits
W=4**np.arange(7,-1,-1)
H=np.array([[(-1)**(sum(a*b for a,b in zip(x,y))%2) for y in B3] for x in B3])
# i^d as Gaussian integer (re,im)
RE=np.array([1,0,-1,0]);IM=np.array([0,1,0,-1])
CR=D4.__array__(); cr=RE[D4]@H.T; ci=IM[D4]@H.T        # [65536, 8 (a)]  8*c_a exactly (integers)
nz=(cr!=0)|(ci!=0)
ALLOW={}
for Dm in range(1,8):
    D=[t for t in range(3) if (Dm>>(2-t))&1]
    bad=[ai for ai,a in enumerate(B3) if all(a[t] for t in D)]
    ALLOW[Dm]=~nz[:,bad].any(1)
def sub(x,y): return ((D4[x]-D4[y])%4)@W
order=[0b000,0b100,0b010,0b001,0b110,0b101,0b011,0b111]
norm0=D4[:,0]==0
if __name__=='__main__':
    parts=np.zeros((1,8),dtype=np.int64)   # m indices per board o (int code)
    cand0=np.nonzero(norm0)[0]
    for step,o in enumerate(order[1:],1):
        prev=order[:step]
        out=[]
        for chunk in np.array_split(parts,max(1,len(parts)//2000)):
            # candidates: all normalized m (16384) filtered against each previous board
            ok=np.ones((len(chunk),len(cand0)),bool)
            for q in prev:
                Dm=o^q
                d=((D4[cand0][None,:,:]-D4[chunk[:,q]][:,None,:])%4)@W
                ok&=ALLOW[Dm][d]
            r,c=np.nonzero(ok)
            new=chunk[r].copy(); new[:,o]=cand0[c]; out.append(new)
        parts=np.concatenate(out); print('after board',format(o,'03b'),'partial solutions',len(parts),flush=True)
    np.save('xboards_z4.npy',parts.astype(np.uint16))
