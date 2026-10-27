#!/bin/bash
# Round 24 (H.31.1): numerical check of the rule reduction: exact search on each Lugano-type rule (env LUGRULE), orbits 30, 54, 66.
for r in 5 6 7 10 11 14 15; do echo "== rule $r"; LUGRULE=$r /workspace/venv-cvx/bin/python h24_lugsearch.py 30,54,66 400 $r 2>&1 | grep "^orbit" | cut -c1-120; done
