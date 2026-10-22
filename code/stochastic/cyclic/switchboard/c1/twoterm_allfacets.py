"""All 29,344 hull facets (normaliz, physics/facets/pf.out.gz) against two-term boards, one rep per symmetry orbit
of (w1,w2) under party permutations and input/output bit flips (both preserve the Pauli rule and the hull).
Facet in p-coordinates: g(p)=sum g[i,o] p(i|o) + g0 >= 0; operator test lambda_min(sum g[i,o] P_oi + g0*1) >= 0."""
import json, gzip, itertools as it, numpy as np
B3=list(it.product((0,1),repeat=3)); IX={b:n for n,b in enumerate(B3)}
Z=np.load('../../../physics/facets/Z.npy').astype(float); PF=np.load('../../pfs744.npy').reshape(744,-1).astype(float)
A1=np.c_[PF,np.ones(744)]; T=np.linalg.lstsq(A1,Z,rcond=None)[0]        # z = p.T[:64] + T[64]
L=gzip.open('../../../physics/facets/pf.out.gz','rt').read().split('\n')
k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:')); n=int(L[k].split()[0])
H=np.array([list(map(int,L[k+1+j].split())) for j in range(n)],float); Af,bf=H[:,:37],H[:,37]
g=(T[:64]@Af.T).T.reshape(n,8,8); g0=T[64]@Af.T+bf                           # g[f,i,o]
assert (np.einsum('fio,mio->fm',g,PF.reshape(744,8,8))+g0[:,None]).min()>-1e-9
P=np.array(json.load(open('twoterm_pairs.json'))); P=P[[not np.array_equal(a,b) for a,b in P]]
def act(w,pi,fi,fo):
    out=[0]*8
    for o in range(8):
        ob=B3[o]; src=tuple(ob[pi.index(k)] for k in range(3)); src=tuple(src[k]^fo[k] for k in range(3))
        v=B3[w[IX[src]]]; v=tuple(v[pi[k]] for k in range(3)); v=tuple(v[k]^fi[k] for k in range(3)); out[o]=IX[v]
    return tuple(out)
G=[(pi,fi,fo) for pi in it.permutations(range(3)) for fi in B3 for fo in B3]
seen=set(); reps=[]
for w1,w2 in P.tolist():
    key=(tuple(w1),tuple(w2))
    if key in seen: continue
    orb={(act(w1,*h),act(w2,*h)) for h in G}; seen|=orb; reps.append(key)
print('pairs',len(P),'orbit reps',len(reps),flush=True)
R=np.array(reps); worst=9; arg=None
for t in [np.pi/12,np.pi/8,np.pi/6,np.pi/4,np.pi/3,3*np.pi/8,5*np.pi/12]:
    c,s=np.cos(t),np.sin(t)
    # V[r,o,i,:] = c e_{i^a} - i s e_{i^b}
    V=np.zeros((len(R),8,8,8),complex)
    for o in range(8):
        for i in range(8):
            V[np.arange(len(R)),o,i,i^R[:,0,o]]+=c; V[np.arange(len(R)),o,i,i^R[:,1,o]]+=-1j*s
    Pr=np.einsum('roia,roib->roiab',V,V.conj())                                # projectors P_{o,i}
    for f0 in range(0,n,2000):
        gg=g[f0:f0+2000]; M=np.einsum('fio,roiab->frab',gg,Pr)+(g0[f0:f0+2000])[:,None,None,None]*np.eye(8)
        lm=np.linalg.eigvalsh(M)[...,0]; j=np.unravel_index(lm.argmin(),lm.shape)
        if lm[j]<worst: worst=float(lm[j]); arg=(t,int(f0+j[0]),reps[j[1]])
    print('t %.4f running min lambda_min %.3e'%(t,worst),flush=True)
print('RESULT min over reps, facets, t of lambda_min: %.3e'%worst, json.dumps(arg))
