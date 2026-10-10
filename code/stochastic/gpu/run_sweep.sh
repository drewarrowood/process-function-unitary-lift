#!/bin/bash
# Usage: ./run_sweep.sh [orbit ids...]   (default: all 49 open orbits). Resumes from results/*.json.
cd "$(dirname "$0")"
IDS=${@:-$(cat open_orbits.txt)}
for i in $IDS; do python3 gpusearch.py $i --restarts 64 --batch 16 --iters 2000 --out results 2>&1 | tail -1; done
