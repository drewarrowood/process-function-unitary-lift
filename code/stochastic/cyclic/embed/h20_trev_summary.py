"""Round 20 (H.27.2): summarise the time-reversed PF-lift searches on the 10 open orbits (h20_trev_open_*.log) and pack the best
parameter vectors of seed 7 into one file h20_trev_best.npz (the per-run .npy files are not committed)."""
import re, glob, ast, numpy as np
from h20_common import OPEN
rows={}
for f in sorted(glob.glob('h20_trev_open_*.log')):
    for l in open(f):
        if l.startswith('w '):
            wi=int(l.split()[1]); d=ast.literal_eval(l[l.index('{'):l.index('}')+1]); rows[wi]=d
print('refined PFs searched (index into h20_fwd_enum.json maximal):',sorted(rows),'of 20')
best={o:min((rows[w][o],w) for w in rows) for o in OPEN}
for o in OPEN: print(f'orbit {o}: best relative facet value {best[o][0]:+.3e} (refined PF {best[o][1]}); crossed: {best[o][0]<-1e-7}')
np.savez_compressed('h20_trev_best.npz',**{f'w{w}_o{o}':np.load(f'h20_trev_best_w{w}_o{o}_s7.npy',allow_pickle=True) for w in rows for o in OPEN})
