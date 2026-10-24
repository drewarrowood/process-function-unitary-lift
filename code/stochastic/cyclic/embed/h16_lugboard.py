import itertools as it, numpy as np
B3=list(it.product((0,1),repeat=3))
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
def su2(t):
    a,b,c=t; return np.array([[np.cos(a)*np.exp(1j*b),np.sin(a)*np.exp(1j*c)],[-np.sin(a)*np.exp(-1j*c),np.cos(a)*np.exp(-1j*b)]])
def u2(t): return np.exp(1j*t[3])*su2(t[:3])
k3=lambda a,b,c:np.kron(np.kron(a,b),c)
def board(th,rev):
    U=[u2(th[4*j:4*j+4]) for j in range(3)]; fr=[su2(th[12+3*j:15+3*j]) for j in range(6)]
    Lm=np.zeros((64,64),complex)
    for o in range(8):
        e=lug(*B3[o]); g=k3(*[np.linalg.matrix_power(U[j],e[j]) for j in range(3)])
        for s in range(8):
            for i in range(8): Lm[8*i+o,8*o+s]=g[i,s]
    if rev: Lm=Lm.T
    FI=k3(*fr[:3]); FO=k3(*fr[3:])
    return np.kron(FI,np.eye(8))@Lm@np.kron(FO,np.eye(8))
