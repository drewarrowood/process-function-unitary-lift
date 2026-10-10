import numpy as np, itertools as it
B=list(it.product((0,1),repeat=3))
def P(w): # P[x,a] as 8x8
    M=np.zeros((8,8))
    for a in B: M[B.index(w(a)),B.index(a)]=1
    return M
C=lambda o:(o[2],o[0],o[1]); Cb=lambda o:(1-o[2],1-o[0],1-o[1])
E=(P(C)+P(Cb))/2
fs=list(it.product((0,1),repeat=2)); rows=[]
for f in it.product(fs,repeat=3):  # sum_x P(x | a=f(x)) = 1
    r=np.zeros((8,8))
    for x in B: r[B.index(x),B.index(tuple(f[k][x[k]] for k in range(3)))]+=1
    rows.append(r.ravel())
A=np.array(rows); print('consistent',np.allclose(A@E.ravel(),1))
Z=[np.eye(64)[i] for i in range(64) if E.ravel()[i]==0]
M=np.vstack([A]+Z); print('rank',np.linalg.matrix_rank(M),'of 64 -> vertex' if np.linalg.matrix_rank(M)==64 else '')
# 2-party: enumerate vertices by brute force over supports is heavy; check deterministic count
