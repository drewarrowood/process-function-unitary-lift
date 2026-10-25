# Round 18 (H.25.4): validity (Araujo et al. projector penalty, h16_gen_search.penalty) of Lugano boards dressed with an ENTANGLING
# gate G on the three input wires: |s>_P|o> -> G (U_A^{lug_A(o)} x U_B^{lug_B(o)} x U_C^{lug_C(o)}) |s>_I |o>_F.  Non-XOR, non-product family.
import numpy as np, torch, sys, itertools as it
sys.argv=[sys.argv[0],'0','0']
from h16_gen_search import penalty
rng=np.random.default_rng(18); B3=list(it.product((0,1),repeat=3))
def haar(n=2):
    q,r=np.linalg.qr(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))); return q*np.diag(r)/abs(np.diag(r))
k3=lambda a,b,c:np.kron(np.kron(a,b),c)
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
I2=np.eye(2)
def Vb(G,U):
    V=np.zeros((64,64),complex)
    for o in range(8):
        g=G@k3(*[np.linalg.matrix_power(U[k],lug(*B3[o])[k]) for k in range(3)])
        for s in range(8):
            for i in range(8): V[8*i+o,8*o+s]=g[i,s]
    return V
pen=lambda G,U: float(penalty(torch.tensor(Vb(G,U))))
X=np.array([[0,1],[1,0]]); CZ=np.diag([1,1,1,-1])
for t in range(3):
    U=[haar() for _ in range(3)]; UX=[X]*3
    print(f'trial {t}: G=1 (control) {pen(np.eye(8),U):.3g}; G=Haar(8) {pen(haar(8),U):.3g}; G=Haar(4) on AB {pen(np.kron(haar(4),I2),U):.3g};',
          f'G=random diagonal phases {pen(np.diag(np.exp(1j*rng.uniform(0,6.3,8))),U):.3g}; G=CZ_AB {pen(np.kron(CZ,I2),U):.3g};',
          f'Lugano (U=X) with G=CZ_AB {pen(np.kron(CZ,I2),UX):.3g}; with G=Haar(4) on AB {pen(np.kron(haar(4),I2),UX):.3g}',flush=True)
