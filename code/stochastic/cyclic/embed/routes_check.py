"""H.15.7(A): route (support) structure of the purifying unitaries V: |o>_AO|s>_P -> sum_i U_o[i,s] |i>_AI |o>_F.
Sectorisation 1 = computational values on all wires; sectorisation 2 = Hadamard (Fourier) basis z on the loop medium.
Reports whether the station route (o,s) -> i is a function (univocal, as for PFs / Lugano) or a relation."""
import json, itertools as it, numpy as np
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/np.sqrt(8)
m=json.load(open('../switchboard/h13/min_cex.json'))['m']
U13=np.array([Hd@np.diag([(-1)**(m[o][x]//2) for x in range(8)])@Hd for o in range(8)])
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U12=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
UL=np.zeros((8,8,8))       # Lugano purification (AFNB/BCRWZ): |o,s> -> |w(o) xor s>, s = source bits
for o in range(8):
    for s in range(8): UL[o][B3.index(tuple(a^b for a,b in zip(lug(*B3[o]),B3[s])))][s]=1
for name,U in [('Lugano PF',UL),('H.12 switchboard',U12),('H.13.2 rational',U13)]:
    nz=[(abs(U[o][:,s])>1e-12).sum() for o in range(8) for s in range(8)]
    Ft=[Hd@U[o]@Hd for o in range(8)]; diag=all(np.allclose(F,np.diag(np.diag(F))) for F in Ft)
    flips=sorted({int(np.count_nonzero(np.abs(np.array([U[o][s^e][s] if True else 0 for s in range(8)]))>1e-12)>0) for o in range(8) for e in range(8)})
    # X-pattern expansion: U_o = sum_e c_e(o) X^e  (c_e(o) = U_o[e,0] if U_o is X-type, i.e. U_o[i,s] depends on i xor s)
    xtype=all(np.allclose(U[o][i^s if False else i][s],U[o][i^s][0]) for o in range(8) for i in range(8) for s in range(8))
    nterms=max(int((np.abs(U[o][:,0])>1e-12).sum()) for o in range(8))
    print(f'{name}: route (o,s)->i univocal: {set(nz)=={1}} (support sizes {sorted(set(nz))}); X-type: {xtype}; '
          f'flip patterns per transition <= {nterms}; diagonal in Fourier sectors z (o enters only as a phase): {diag}')
mz=[[0,0,0,0,0,0,0,0],[0,0,1,1,1,1,1,1],[0,0,0,0,1,0,1,0],[0,0,1,1,2,1,2,1],[0,0,0,1,0,0,0,1],[0,0,1,2,1,1,1,2],[0,0,0,1,1,0,1,1],[0,0,1,2,2,1,2,2]]
UZ=np.array([Hd@np.diag([np.exp(2j*np.pi*mz[o][z]/8) for z in range(8)])@Hd for o in range(8)])
nz=sorted({int((abs(UZ[o][:,s])>1e-12).sum()) for o in range(8) for s in range(8)})
print(f'Z8 class 10515 (H.14.2): route univocal: {nz==[1]} (support sizes {nz}); diagonal in Fourier sectors: True by construction')
