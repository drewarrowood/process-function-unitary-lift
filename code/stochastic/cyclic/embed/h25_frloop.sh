#!/bin/bash
# Round 25 (H.32.2): iterate facial reduction for one orbit until a strictly feasible certificate is found (or 10 steps).
# usage: h25_frloop.sh orbit   (needs /tmp/r25/h25_zs_o<orbit>.npz from h25_zeroset.py)
orb=$1; prev=""
for k in 1 2 3 4 5 6 7 8 9 10; do
  echo "=== facial-reduction step $k (extra kernel file: ${prev:-none})"
  RATD=${RATD:-1000} KEXTRA=$prev PYTHONPATH=. timeout 900 /workspace/venv-cvx/bin/python -u h25_cert.py $orb /tmp/r25/h25_zs_o$orb.npz s$k 2>&1 | grep -v Warn
  if grep -q "certificate VALID" <(ls h25_cert_o${orb}s$k.json 2>/dev/null && echo) ; then :; fi
  [ -f /tmp/r25/h25_fr_o${orb}s$k.npz ] || break
  prev=/tmp/r25/h25_fr_o${orb}s$k.npz
done
