# Round 17: validity (Araujo et al. projector penalty, h16_gen_search.penalty) of classically controlled qubit boards i_k = U_{k,o_{-k}} s_k
import numpy as np, torch, sys, itertools as it
sys.argv=[sys.argv[0],'0','0']
from h16_gen_search import penalty
rng=np.random.default_rng(3); B3=list(it.product((0,1),repeat=3))
def haar():
    q,r=np.linalg.qr(rng.normal(size=(2,2))+1j*rng.normal(size=(2,2))); return q*np.diag(r)/abs(np.diag(r))
k3=lambda a,b,c:np.kron(np.kron(a,b),c)
def Vb(Uf):
    V=np.zeros((64,64),complex)
    for o in range(8):
        g=k3(*[Uf(k,o) for k in range(3)])
        for s in range(8):
            for i in range(8): V[8*i+o,8*o+s]=g[i,s]
    return V
for trial in range(3):
    T={(k,a,b):haar() for k in range(3) for a in (0,1) for b in (0,1)}
    oth=lambda k,o:tuple(B3[o][j] for j in range(3) if j!=k)
    print('generic 4-per-party', float(penalty(torch.tensor(Vb(lambda k,o:T[(k,)+oth(k,o)])))))
    # one-party-dependence only (causal-like): U_k depends on one other party's output
    print('depends on next party only', float(penalty(torch.tensor(Vb(lambda k,o:T[(k,B3[o][(k+1)%3],0)])))))
    # Lugano-shaped with arbitrary unitary in the active cell and arbitrary different unitary otherwise
    lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
    print('lugano two-valued', float(penalty(torch.tensor(Vb(lambda k,o:T[(k,lug(*B3[o])[k],0)])))))
print('--- refinements of the Lugano cells')
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
for trial in range(2):
    T={(k,a,b):haar() for k in range(3) for a in (0,1) for b in (0,1)}; Ua={k:haar() for k in range(3)}
    oth=lambda k,o:tuple(B3[o][j] for j in range(3) if j!=k)
    f=lambda k,o: Ua[k] if lug(*B3[o])[k] else T[(k,)+oth(k,o)]
    print('inactive cells distinct', float(penalty(torch.tensor(Vb(f)))))
    # inactive cells: depend only on the 'controlling' party whose value disables (A disabled by oB=1 or oC=0)
    for k in range(3): pass
    # diagonal (phase) unitaries in inactive cells: commute with each other
    D={(k,a,b):np.diag(np.exp(1j*rng.uniform(0,6.3,2))) for k in range(3) for a in (0,1) for b in (0,1)}
    f2=lambda k,o: Ua[k] if lug(*B3[o])[k] else D[(k,)+oth(k,o)]
    print('inactive cells distinct diagonal', float(penalty(torch.tensor(Vb(f2)))))
