#!/usr/bin/env bash
# Usage: run_pipeline.sh OUTDIR NAME... [env STEPS=400 BATCH=8 CHUNK=540 ROUNDS=20]
# Per orbit: certsearch in time-boxed chunks (resumes from best theta, new seed each chunk) until float-certified
# or ROUNDS exhausted; then exact verification. Writes OUTDIR/NAME.{search,verify}.json and OUTDIR/status.jsonl.
set -u
cd "$(dirname "$0")"; OUT=$1; shift; mkdir -p "$OUT"
PY=${PY:-python3}; STEPS=${STEPS:-400}; BATCH=${BATCH:-8}; CHUNK=${CHUNK:-540}; ROUNDS=${ROUNDS:-20}
for N in "$@"; do
  [ -f "$OUT/$N.verify.json" ] && { echo "$N already verified"; continue; }
  for ((k=0; k<ROUNDS; k++)); do
    timeout "$CHUNK" $PY certsearch.py "$N" --out "$OUT" --steps "$STEPS" --batch "$BATCH" --seed "$k" >> "$OUT/$N.log" 2>&1
    grep -q '"certified_float": true' "$OUT/$N.search.json" 2>/dev/null && break
  done
  if grep -q '"certified_float": true' "$OUT/$N.search.json" 2>/dev/null; then
    timeout 3000 $PY verify.py "$N" "$OUT/$N.theta.npy" >> "$OUT/$N.log" 2>&1
    $PY -c "import json;print(json.dumps(json.load(open('$OUT/$N.verify.json'))))" >> "$OUT/status.jsonl"
  else
    echo "{\"name\": \"$N\", \"certified\": false, \"note\": \"no single-form certificate found\"}" >> "$OUT/status.jsonl"
  fi
done
