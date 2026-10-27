#!/bin/bash
# Round 25 (H.32.2): for every facet of an orbit: zero set (400 starts) + first facial-reduction step; report margins / VALID.
# usage: h25_facetscan.sh orbit
orb=$1
for f in $(PYTHONPATH=. /workspace/venv-cvx/bin/python -c "from h20_common import canon; import numpy as np; print(' '.join(map(str,np.where(canon==$orb)[0])))"); do
  PYTHONPATH=. timeout 600 /workspace/venv-cvx/bin/python -u h25_zeroset.py $orb 400 1 $f 2>&1 | grep -v Warn | grep "span rank" | awk '{print $4,$5,$6,$7}' | tr '\n' ' ' | sed "s/^/facet $f zero-set: /"; echo
  RATD=64 PYTHONPATH=. timeout 900 /workspace/venv-cvx/bin/python -u h25_cert.py $orb /tmp/r25/h25_zs_o${orb}f$f.npz f$f SCS $f 2>&1 | grep -v Warn | grep "margin\|VALID\|Error" | sed "s/^/facet $f: /"
done
