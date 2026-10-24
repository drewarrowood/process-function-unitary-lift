import sys,numpy as np
from scipy.optimize import minimize
sys.argv=['x','1','0','0']
exec(open('never22_lugU.py').read().split('best=[]')[0])
d=np.load('never22_hit_draw.npy'); rev=int(d[0]); th=d[1:]
sel_idx=np.where(sel)[0]
def fviol(th,fs):
    P=forms(board(th,rev)); Fm=np.einsum('fr,rst->fst',Tn[fs,:64],P)+Tn[fs,64,None,None]*np.eye(8)
    return (-np.linalg.eigvalsh(Fm)[:,0]).max()
# the orbit-14 and orbit-25 facets
f14=sel_idx[cs==14]; f25=sel_idx[cs==25]
print('n facets orbit14',len(f14),'orbit25',len(f25))
for name,fs in (('orbit14',f14),('orbit25',f25)):
    x=th.copy(); v=fviol(x,fs)
    for rnd in range(3):
        res=minimize(lambda t:-fviol(t,fs),x,method='Powell',options={'maxiter':20000,'xtol':1e-8,'ftol':1e-12}); x=res.x
        print(name,'round',rnd,'viol',-res.fun,flush=True)
    np.save(f'/tmp/r15/hitopt_{name}.npy',np.r_[rev,x])
