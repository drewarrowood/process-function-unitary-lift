#!/bin/bash
# Round 25 (H.32.2): iterate facial reduction for one orbit until a strictly feasible certificate is found (or NSTEP steps).
# usage: h25_frloop.sh orbit [first_step] [extra_kernel_npz] [nstep]   (needs /tmp/r25/h25_zs_o<orbit>.npz from h25_zeroset.py)
orb=$1; k=${2:-1}; prev=${3:-}; last=$(( k + ${4:-10} - 1 ))
while [ $k -le $last ]; do
  echo "=== facial-reduction step $k (extra kernel file: ${prev:-none})"
  RATD=${RATD:-1000} KEXTRA=$prev PYTHONPATH=. timeout 1200 /workspace/venv-cvx/bin/python -u h25_cert.py $orb /tmp/r25/h25_zs_o$orb.npz s$k 2>&1 | grep --line-buffered -v Warn
  [ -f /tmp/r25/h25_fr_o${orb}s$k.npz ] || break
  prev=/tmp/r25/h25_fr_o${orb}s$k.npz; k=$((k+1))
done
