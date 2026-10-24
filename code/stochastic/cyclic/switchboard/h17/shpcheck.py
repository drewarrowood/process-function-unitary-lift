"""H.17 wrap-up: SH+ / SH++ status of the one SH+-failing board saved by nsearch2 seed 11 (shp_11_3339.npy)."""
import numpy as np, itertools as it
from lib3 import *
src=open('nsearch2.py').read().split('\n')
exec('\n'.join(src[11:12])); exec('\n'.join(src[70:89]))
U=np.load('shp_11_3339.npy')
print('unitary residual',max(np.abs(U[o]@U[o].conj().T-np.eye(8)).max() for o in range(8)))
print('SH+ bad pairs',SHplus(U)); print('SH++ bad pairs (best r)',SHplus2(U))
