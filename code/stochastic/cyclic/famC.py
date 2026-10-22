"""Family C ('noisy-PF / contextual-source' purifications).
Source P = S (x) T (8 x 8), sink F = O (x) E' (8 x 8):
    V|o, s, t> = sum_e C_o[e, s] |e>_I |o>_F |e + t>_F     (C_o: 8x8 unitaries, one per joint output o)
V is unitary for any C_o; the sink records (o, i), so W is diagonal with p(i|o) = |C_o[i, 0]|^2 (source |0,0>).
Every classical p(i|o) arises this way for SOME C_o; purity is the constraint. We optimise the C_o for purity
(sampled local unitaries with qubit ancillas), optionally pushing p across a PF-hull facet.
argv: seed steps lam(facet weight) [init: rand|lug|exid]"""
import sys, json, torch, numpy as np, itertools as it
torch.set_num_threads(1)
seed=int(sys.argv[1]); steps=int(sys.argv[2]); lam=float(sys.argv[3]); init=sys.argv[4] if len(sys.argv)>4 else 'rand'
torch.manual_seed(seed); np.random.seed(seed); c=torch.complex128
B3=list(it.product((0,1),repeat=3)); IX={t:n for n,t in enumerate(B3)}
def haar(n):
    z=torch.randn(n,n,dtype=c); q,r=torch.linalg.qr(z); d=torch.diagonal(r); return q*(d/d.abs())
def Vfull(Vs,d):
    T=torch.einsum('ab,cd,ef->acebdf',*Vs).reshape(2,d,2,d,2,d,2,d,2,d,2,d).permute(0,2,4,1,3,5,6,8,10,7,9,11)
    return T.reshape(8,d**3,8,d**3)  # [o,y,i,x]
def buildV(C):  # C[o,e,s] -> V[i,(o',t'),o,(s,t)]
    V=torch.zeros(8,8,8,8,8,8,dtype=c)  # i, o', t', o, s, t
    for o in range(8):
        for e in range(8):
            for t in range(8):
                V[e,o,e^t,o,:,t]=C[o,e,:]
    return V.reshape(8,64,8,64)
# facet orbit 82 representative (as hunt.py), random symmetry image
fac=[(1,'000','000')]+[(-1,i,o) for i,o in [('000','001'),('010','001'),('000','100'),('010','110'),('011','111')]]
perm=list(np.random.permutation(3)); fi=np.random.randint(0,2,3); fo=np.random.randint(0,2,3)
def tr(s,fl): b=[int(ch) for ch in s]; b=[b[perm[k]] for k in range(3)]; return tuple(int(b[k]^fl[k]) for k in range(3))
facet=[(s,IX[tr(i,fi)],IX[tr(o,fo)]) for s,i,o in fac]
noise=float(sys.argv[5]) if len(sys.argv)>5 else (1.0 if init=='rand' else 0.05)
H=torch.randn(8,8,8,dtype=c)*noise; H=(H+H.conj().transpose(1,2))/2; H.requires_grad_()
C0=torch.eye(8,dtype=c).repeat(8,1,1)
if init=='lug':  # C_o = shift by w(o): reproduces the Lugano lift
    lug=lambda o:((1-o[1])&o[2],(1-o[2])&o[0],(1-o[0])&o[1])
    for o in B3:
        P=torch.zeros(8,8,dtype=c)
        for e in B3: P[IX[tuple(a^b for a,b in zip(lug(o),e))],IX[e]]=1
        C0[IX[o]]=P
def purity(V,ns,d):
    T=V.reshape(8,64,8,64); L=0
    for _ in range(ns):
        Vs=[haar(2*d) for _ in range(3)]; Vl=Vfull(Vs,d)
        M=torch.einsum('ifos,oyix->fysx',T,Vl).reshape(64*d**3,64*d**3)
        L=L+((M@M.conj().T-torch.eye(64*d**3,dtype=c)).abs()**2).sum()/(64*d**3)
    return L/ns
opt=torch.optim.Adam([H],lr=0.02)
for t in range(steps):
    C=C0@torch.matrix_exp(1j*(H+H.conj().transpose(1,2))/2); V=buildV(C)
    pur=purity(V,2,1 if t%2 else 2)
    p=(C[:,:,0].abs()**2).T   # p[i,o]
    f=sum(s*p[i,o] for s,i,o in facet)
    loss=pur-lam*f
    opt.zero_grad(); loss.backward(); opt.step()
    if t%500==0: print(seed,t,'pur %.3g facet %.3g'%(float(pur.detach()),float(f.detach()) if torch.is_tensor(f) else f),flush=True)
with torch.no_grad():
    C=C0@torch.matrix_exp(1j*(H+H.conj().transpose(1,2))/2); V=buildV(C); pa=float(purity(V,20,2)); pn=float(purity(V,20,1)); p=(C[:,:,0].abs()**2).T
np.save('C_%s_%g_%d%s.npy'%(init,lam,seed,'' if len(sys.argv)<=5 else '_n'+sys.argv[5]),C.numpy())
print('FINAL',json.dumps(dict(seed=seed,lam=lam,init=init,pur_anc=pa,pur_noanc=pn,facet=float(sum(s*p[i,o] for s,i,o in facet)))),flush=True)
