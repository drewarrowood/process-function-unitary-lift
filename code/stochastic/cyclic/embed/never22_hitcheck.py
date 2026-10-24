import sys,numpy as np
sys.argv=['x','1','0','0']
src=open('never22_lugU.py').read().split('best=[]')[0]
exec(src)
best=(-9,)
for r in range(4000):
    rev=r%2; th=rng.uniform(0,2*np.pi,30); v=viol(th,rev)
    if v>best[0]: best=(v,r,rev,th)
v,r,rev,th=best; print('best',v,'draw',r,'rev',rev)
np.save('never22_hit_draw.npy',np.r_[rev,th])
ov=viol(th,rev,True); print([(o,ov[o]) for o in OPEN22 if ov[o]>1e-9])
