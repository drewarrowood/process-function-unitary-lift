"""Round 33 (H.38): second-order kernel candidates for the t0 = 0 face: d/da2 V_b on F1 = {u2 = 1, y2 = 0} (H vanishes to
fourth order in a2 there: H(y2 = 0) = 2 y1^2 (1+y1^2)^2 |1-u2|^4) and d/dt1 V_b on YE.  Writes /tmp/h33_ex_<orb>.pkl for h33_facesolve.py."""
import sys
orb=sys.argv[1]; sys.argv=['h33_face.py',orb]
src=open('h33_face.py').read(); exec(src.split("Hs=sp.expand")[0])
exec("rng=np.random.default_rng(5)\n"+src[src.index("def pt(fam):"):src.index("for fam in fams:")])
def dV(b,z,k,h=1e-5):
    e=np.zeros(5); e[k]=h
    return (V(b,(z+e)[:3],(z+e)[3:])-V(b,(z-e)[:3],(z-e)[3:]))/(2*h)
EX={}
for kb,b in basis.items():
    EX[kb]=[dV(b,np.r_[pt('F1')],2) for r in range(150)]+[dV(b,np.r_[pt('YE')],3) for r in range(20)]
pickle.dump(EX,open(f'/tmp/h33_ex_{orb}.pkl','wb')); print('ok')
