"""Round 27 (H.34.4): one facial-reduction step. From a margin solve of h27_face.py (out.npz) whose optimum t~0, read the dual PSD blocks Z, take their range
(complex vectors g in face coordinates), map y=N g, and append conj(y) to the kernel rows of the zeros npz. usage: face_out.npz zeros.npz new_zeros.npz"""
import numpy as np, json, sys
D=None; F=np.load(sys.argv[1]); Zz=dict(np.load(sys.argv[2])); d=F['d']; z=F['z']; x=F['x']; mk=int(F['mk'])
def unsvec(v,m):
    X=np.zeros((m,m)); k=0
    for j in range(m):
        for i in range(j+1):
            X[i,j]=X[j,i]=v[k]*(1 if i==j else 1/np.sqrt(2)); k+=1
    return X
zo=mk+1; xo=1
for b in range(len(d)):
    if d[b]==0: continue
    db=d[b]; m=2*db; s=m*(m+1)//2
    Z=unsvec(z[zo:zo+s],m); X=unsvec(x[xo:xo+s],m); zo+=s; xo+=s
    ez,V=np.linalg.eigh(Z)
    if ez[-1]<1e-7: continue
    G=X[:db,:db]+X[db:,db:]+1j*(X[db:,:db]-X[:db,db:]); N=F[f'N{b}']
    for k in np.where(ez>1e-7)[0][::2]:
        g=V[:db,k]+1j*V[db:,k]; g/=np.linalg.norm(g)
        r1=np.linalg.norm(G@g); r2=np.linalg.norm(G@g.conj())
        gg=g if r1<r2 else g.conj(); y=N@gg
        print(b,'|Gg|',f'{r1:.1e}','|G conj g|',f'{r2:.1e}', 'kernel vec (normalised by max):', np.round(y/y[np.argmax(abs(y))],6))
        Zz[f'W{b}']=np.vstack([Zz[f'W{b}'], y.conj()[None]])
np.savez_compressed(sys.argv[3],**Zz)
