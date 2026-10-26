"""Round 21 (H.28.1): independent float check of a time-reversed PF-lift point from the explicit unitary (not the Gram formula).
Forward lift V|s>|a> = (x)_k U~_{k,w_k(a)}|s> (x) |a>_F with U~ = U^T; T := V^T.  In T the past is old F (source psi), agent k's input
is the binary a_k wire (measured in the frame conj(E_k)), its output is the D_k node wire (prepared phi_k(o_k)), the future is old s.
Checks: V unitary; T a valid pure process numerically (closed loop with random agent unitaries C^2 (x) C^{D/2} -> C^D is unitary);
p(i|o) from T equals the Gram-formula p; facet value.  usage: params.npy W ORB"""
import sys, numpy as np, torch
pf=sys.argv[1]; W=int(sys.argv[2]); ORB=int(sys.argv[3])
src=open('h20_trev_search.py').read().split('rng=np.random')[0]
sys.argv=['x',str(W),'1','1',str(ORB)]; exec(src)
th=np.load(pf); parts=maxi[W]; nb=[max(p)+1 for p in parts]; D=[2*n for n in nb]
sizes=[nb[k]*2*D[k]*D[k]+2*2*D[k]+3 for k in range(3)]; xa=[[parts[k][others(k,a)] for a in range(8)] for k in range(3)]
off=0; Us=[]; phis=[]; Es=[]
for k in range(3):
    n=nb[k]; d=D[k]; t=torch.tensor(th[off:off+sizes[k]]); off+=sizes[k]
    Us.append([torch.linalg.matrix_exp(1j*herm(t[2*d*d*x:2*d*d*(x+1)],d)).numpy() for x in range(n)])
    ph=t[2*d*d*n:2*d*d*n+4*d].numpy(); v=[ph[2*d*o:2*d*o+d]+1j*ph[2*d*o+d:2*d*o+2*d] for o in range(2)]; phis.append([x/np.linalg.norm(x) for x in v])
    Es.append(su2(t[-3:]).numpy())
Ds=int(np.prod(D))
# V[(s_out, f), (s_in, a)] ; s_out = agent inputs in the forward picture (node wires), f = copy of a
V=np.zeros((Ds*8,Ds*8),complex)
for a in range(8):
    K=np.ones((1,1))
    for k in range(3): K=np.kron(K,Us[k][xa[k][a]].T)
    for f in [a]:
        V[f::8,a::8]=K          # rows s_out*8+f, cols s_in*8+a
print('V unitary:',np.abs(V.conj().T@V-np.eye(Ds*8)).max())
T=V.T   # T[(s_in,a),(s_out,f)] : input (node wires = agent outputs, f = past) -> output (s_in = future, a = agent inputs)
T6=T.reshape(D[0],D[1],D[2],2,2,2,D[0],D[1],D[2],8)   # [S0,S1,S2,a0,a1,a2,o0,o1,o2,f]
rng=np.random.default_rng(0); worst=0
for r in range(20):   # closed loop: agent k unitary A_k: (a_k (x) m_k) -> node wire, m_k of dim D_k/2
    A=[np.linalg.qr(rng.normal(size=(D[k],D[k]))+1j*rng.normal(size=(D[k],D[k])))[0].reshape(D[k],2,D[k]//2) for k in range(3)]
    C=np.einsum('xyzabcuvwf,uaj,vbk,wcl->xyzfjkl',T6,*A).reshape(Ds,8*Ds//8)
    worst=max(worst,np.abs(C.conj().T@C-np.eye(C.shape[1])).max())
print('closed loops (20 random agent unitaries) unitary to: %.2e'%worst)
psi_set={}
# p from T: agents prepare phi_k(o_k) on the node wire, measure a_k in basis vectors conj(E_k[:,i]) (see docstring), future traced
Gf=[]
for i in range(8):
    row=[]
    for o in range(8):
        ph=np.einsum('u,v,w->uvw',*[phis[k][B3[o][k]] for k in range(3)])
        amp=np.einsum('xyzabcuvwf,uvw->xyzabcf',T6,ph)            # [S,a,f]
        e=np.einsum('a,b,c->abc',*[Es[k][:,B3[i][k]] for k in range(3)])   # <conj(E)| = E^T
        amp=np.einsum('xyzabcf,abc->xyzf',amp,e).reshape(Ds,8)       # [S, f]
        row.append(amp.conj().T@amp)   # quadratic form in psi: p = psi^dag (amp^dag amp) psi
    Gf.append(row)
Gf=np.array(Gf)
fi=REP[ORB]; M=np.einsum('r,rab->ab',Tn[fi,:64],Gf.reshape(64,8,8))+Tn[fi,64]*np.eye(8); w,Ue=np.linalg.eigh(M)
print('relative facet value (explicit unitary): %.10e   orbit %d facet %d'%(w[0],ORB,fi))
psi=Ue[:,0]; p=np.einsum('a,ioab,b->io',psi.conj(),Gf,psi).real
print('sum_i p(i|o) - 1: %.1e'%np.abs(p.sum(0)-1).max())
