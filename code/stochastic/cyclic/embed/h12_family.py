"""Round 14, item 4: a one-parameter family of pure boards through H.12 (H.21.2).
L_phi = Lugano purification with Bob's flip X replaced by G_phi = (1+e^{i phi})/2 1 + (1-e^{i phi})/2 X  (G_pi = X, G_{pi/2} = sqrt X, G_0 = 1).
V_phi = (Hd X_C)_AI (Hd X_A)_F L_phi^T (Hd)_AO (X_C Pre Hd)_P ; V_{pi/2} = V_H12 (tds_h12.py (5)).
For each phi: (i) purity check (cyclic composition with Haar agent unitaries + qubit ancillas is unitary) [NUMERICAL];
(ii) classical process in the computational frame, max over source states of each conv(PF) facet violation, per facet orbit [NUMERICAL].
Orbit labels as in switchboard/h13/xviol.npz (canon), the numbering of H.13.4 / Appendix J."""
import itertools as it, numpy as np, gzip
rng=np.random.default_rng(7)
F='../../physics/facets/'
B3=list(it.product((0,1),repeat=3))
PF=np.load('../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]; A=np.c_[PF.reshape(744,-1),np.ones(744)]; T=np.linalg.lstsq(A,vals,rcond=None)[0].T; Tn=T/vals.max(0)[:,None]
X=np.load('../switchboard/h13/xviol.npz'); canon=X['canon'].astype(int); xv=X['viol']
norb=canon.max()+1; never=[o for o in range(norb) if xv[:,o].max()<=1e-7]
OPEN22=[4,5,6,7,8,9,10,11,14,25,26,28,30,31,53,54,57,66,69,75,79,81]
print('never-crossed orbits in xviol.npz (Z_4 X-type):',never)
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
h=np.array([[1,1],[1,-1]])/np.sqrt(2); Xp=np.array([[0,1],[1,0]]); I2=np.eye(2)
k3=lambda a,b,c:np.kron(np.kron(a,b),c); mp=np.linalg.matrix_power
H3=k3(h,h,h); Xc=k3(I2,I2,Xp); XA=k3(Xp,I2,I2)
Pre=np.diag([1j**(3*z[2]+2*z[0]+z[1]*z[2]+3*z[0]*z[2]+z[0]*z[1]+2*z[0]*z[1]*z[2]) for z in B3])
def Gphi(p): e=np.exp(1j*p); return (1+e)/2*I2+(1-e)/2*Xp
def Vphi(p):
    G=Gphi(p); LG=np.zeros((64,64),complex)
    for o in range(8):
        a,b,c=lug(*B3[o]); g=k3(mp(Xp,a),mp(G,b),mp(Xp,c))
        for s in range(8):
            for i in range(8): LG[8*i+o,8*o+s]=g[i,s]
    return np.kron(H3@Xc,H3@XA)@LG.T@np.kron(H3,Xc@Pre@H3)
def haar(n):
    z=(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))/np.sqrt(2); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
def cyc(M,UA,UB,UC):
    t=M.reshape((2,)*12); u=[U.reshape(2,2,2,2) for U in (UA,UB,UC)]
    return np.einsum('abcFGHxyzPQR,xAaD,yBbE,zCcK->FGHABCPQRDEK',t,*u,optimize=True).reshape(64,64)
def forms(V):   # P[i*8+o][s,t] = sum_f conj V[8i+f,8o+s] V[8i+f,8o+t]
    W=V.reshape(8,8,8,8)   # i f o s
    return np.einsum('ifos,ifot->iost',W.conj(),W).reshape(64,8,8)
def orbit_viol(P):
    Fm=np.einsum('fr,rst->fst',Tn[:,:64],P)+Tn[:,64,None,None]*np.eye(8); v=-np.linalg.eigvalsh(Fm)[:,0]
    out=np.full(norb,-9.); np.maximum.at(out,canon,v); return out
V12=Vphi(np.pi/2)
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
Hd8=H3; Vref=np.zeros((64,64),complex)
for o in range(8):
    U8=Hd8@np.diag([1j**MT[o][z] for z in range(8)])@Hd8
    for i in range(8):
        for s in range(8): Vref[8*i+o,8*o+s]=U8[i,s]
print('V_{pi/2} == V_H12: dev %.1e'%abs(V12-Vref).max())
rows=[]
for p in np.linspace(0,np.pi,25):
    V=Vphi(p); un=max(abs(C.conj().T@C-np.eye(64)).max() for C in [cyc(V,haar(4),haar(4),haar(4)) for _ in range(5)])
    P=forms(V); assert np.allclose(P.reshape(8,8,8,8).sum(0),np.eye(8)[None])
    ov=orbit_viol(P); rows.append((p,ov))
    viol=[o for o in range(norb) if ov[o]>1e-9]
    print(f'phi/pi={p/np.pi:.4f} purity dev {un:.1e}  max viol {ov.max():+.6f} (orbit {ov.argmax()})  #orbits violated {len(viol)}  open-22 violated: {[o for o in OPEN22 if ov[o]>1e-9]}',flush=True)
np.save('h12_family_viol.npy',np.array([[p]+list(ov) for p,ov in rows]))
