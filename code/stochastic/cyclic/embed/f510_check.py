"""Round 16 (F.5.10): numerical sanity check of the countably controlled example.
omega: Z^3 -> Z^3, omega_A(c) = [c_B even and c_C odd]*(2c_B+1), omega_B(c) = [c_C even and c_A odd]*(2c_C+1),
omega_C(c) = [c_A even and c_B odd]*(2c_A+1) (Lugano on parities, unbounded odd translation amounts).
Check: for random local maps f_k: Z -> Z (values in a window), c -> f(omega(c)) has exactly one fixed point in the window
(every fixed point lies in the window because it is a value of f).  [NUMERICAL]"""
import numpy as np
rng=np.random.default_rng(16); R=40; win=np.arange(-R,R+1)
def omega(cA,cB,cC):
    ev=lambda x:(x%2)==0
    return ((ev(cB)&~ev(cC))*(2*cB+1),(ev(cC)&~ev(cA))*(2*cC+1),(ev(cA)&~ev(cB))*(2*cA+1))
A,Bm,C=np.meshgrid(win,win,win,indexing='ij'); A,Bm,C=A.ravel(),Bm.ravel(),C.ravel()
iA,iB,iC=omega(A,Bm,C); IN=4*R+3                  # inputs lie in [-(2R+1), 2R+1]
bad=0; T=3000; counts=np.zeros(4,int)
for t in range(T):
    f=[rng.integers(-R,R+1,size=2*IN+1) for _ in range(3)]   # f_k(i) = f[k][i+IN]
    fix=(f[0][iA+IN]==A)&(f[1][iB+IN]==Bm)&(f[2][iC+IN]==C)
    n=int(fix.sum()); bad+=(n!=1)
    if n==1:
        k=np.flatnonzero(fix)[0]; counts[[iA[k]!=0,iB[k]!=0,iC[k]!=0].index(True)+1 if (iA[k] or iB[k] or iC[k]) else 0]+=1
print(f'trials {T}, window [-{R},{R}]^3, trials without exactly one fixed point: {bad}')
print('fixed point type counts (all inputs 0 / A / B / C nonzero):',counts.tolist())
print('distinct |input| values seen up to', 2*R+1, '(range of omega unbounded on Z^3)')
