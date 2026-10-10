import numpy as np, itertools as it
from scipy.optimize import linprog
B3=list(it.product((0,1),repeat=3))
def P(w):
    M=np.zeros((8,8))
    for a in B3: M[B3.index(w(a)),B3.index(a)]=1
    return M
def is_pf(t):
    fs=list(it.product((0,1),repeat=2))
    for f in it.product(fs,repeat=3):
        c=sum(1 for o in B3 if all(f[k][t[o][k]]==o[k] for k in range(3)))
        if c!=1: return False
    return True
others=list(it.product((0,1),repeat=2)); PFs=[]
for tab in it.product(list(it.product((0,1),repeat=4)),repeat=3):
    t={o:tuple(tab[k][others.index(o[:k]+o[k+1:])] for k in range(3)) for o in B3}
    if is_pf(t): PFs.append(P(lambda o,t=t:t[o]))
PFs=np.array(PFs); print('PFs',len(PFs))
def in_hull(E):
    n=len(PFs); A=np.vstack([PFs.reshape(n,-1).T,np.ones(n)]); b=np.append(E.ravel(),1)
    r=linprog(np.zeros(n),A_eq=A,b_eq=b,bounds=(0,None),method='highs'); return r.status==0
np.save('pfs.npy',PFs)
