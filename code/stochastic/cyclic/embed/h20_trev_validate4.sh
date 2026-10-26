#!/bin/bash
# Round 20 (H.27.2) validation with the Rayleigh objective (default MODE=ray) on crossed orbits, 300 starts.
P=/workspace/venv-cvx/bin/python
$P h20_trev_search.py 10 8 300 14,25 2>&1 | grep "^w"
$P h20_trev_search.py 4 9 300 53,79 2>&1 | grep "^w"
