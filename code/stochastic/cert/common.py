import json, os, sys, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'gpu'))
import gpusearch as gs
B3 = gs.B3
def _P(w):
    M = np.zeros((8, 8))
    for o in B3: M[B3.index(w(o)), B3.index(o)] = 1
    return M
def load(name):
    if name == 'lugano': return _P(lambda o: ((1 - o[1]) & o[2], (1 - o[2]) & o[0], (1 - o[0]) & o[1]))
    if name == 'eex1': return (_P(lambda o: (o[2], o[0], o[1])) + _P(lambda o: (1 - o[2], 1 - o[0], 1 - o[1]))) / 2
    R = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'reps.json')))
    return np.array(R[int(name.replace('orbit', ''))][0]).reshape(8, 8)
