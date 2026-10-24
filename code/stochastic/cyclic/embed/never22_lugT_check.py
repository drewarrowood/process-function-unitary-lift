"""Round 15, H.22.2: the optimised generalised-Lugano board (never22_best.npy) has node unitaries U_k = e^{i a_k} R_k X R_k^dag (eigenphase gap pi),
so L_U = (R)_AI (D)_F L_X (R^dag)_P, i.e. up to local unitaries it is the Lugano purification; the hit is a framed time-reversed Lugano. [NUMERICAL, to the Powell tolerance]"""
# Is the hit LU-equivalent to Lugano^T?  (a) exact structural check: U_k = e^{ia} Q X Q^dag at the optimum;
# (b) build Lugano^T with frames FI'=FI.(conj Q stuff) numerically and compare classical processes.
import sys,numpy as np
sys.argv=['x','1','0','0']
exec(open('never22_lugU.py').read().split('best=[]')[0])
d=np.load('never22_best.npy'); rev=int(d[0]); th=d[1:]
X=np.array([[0,1],[1,0]],complex)
Us=[u2(th[4*j:4*j+4]) for j in range(3)]; Qs=[];als=[]
for U in Us:
    ev,Q=np.linalg.eig(U); # U = Q diag(ev) Q^dag ; want U = e^{ia} R X R^dag with X = h Z h
    a=np.angle(ev[0]); Z=np.diag(ev*np.exp(-1j*a))   # = diag(1,-1) when the eigenphase gap is pi
    if Z[0,0].real<0: Q=Q[:,::-1]; Z=Z[::-1,::-1]
    h=np.array([[1,1],[1,-1]])/2**.5; R=Q@h       # U = e^{ia} Q Z Q^dag = e^{ia} R X R^dag
    Qs.append(R); als.append(a); print('U = e^{ia} R X R^dag dev %.1e'%abs(U-np.exp(1j*a)*R@X@R.conj().T).max())
Ux=[np.exp(1j*a)*X for a in als]
# L_U = (R x3)_AI L_{e^{ia}X} (R^dag x3)_P ; with rows (AI,F) cols (AO,P)
R3=k3(*Qs)
def Lmat(U):
    M=np.zeros((64,64),complex)
    for o in range(8):
        g=k3(*[np.linalg.matrix_power(U[k],lug(*B3[o])[k]) for k in range(3)])
        for s in range(8):
            for i in range(8): M[8*i+o,8*o+s]=g[i,s]
    return M
LUm=Lmat(Us); LX=Lmat([X,X,X])
# phases e^{i sum a_k lug_k(o)} sit on F (row index f=o): D_F
DF=np.diag([np.exp(1j*sum(als[k]*lug(*B3[o])[k] for k in range(3))) for o in range(8)])
rhs=np.kron(R3,DF)@LX@np.kron(np.eye(8),R3.conj().T)
print('L_U == (R)_AI (D)_F L_X (R^dag)_P : dev %.1e'%abs(LUm-rhs).max())
