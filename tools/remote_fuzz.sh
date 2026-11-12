#!/usr/bin/env bash
# Usage: tools/remote_fuzz.sh N SEED...
# Copies the release binary and fuzz.py to the compute server and runs fuzz.py against z3 there,
# one process per seed, N problems each. Prints each run's result.
set -euo pipefail
N=$1; shift
HERE=$(cd "$(dirname "$0")/.." && pwd)
NAME=$(sed -n 's/^session "\([A-Za-z0-9_]*\)".*/\1/p' "$HERE/urust/ROOT" | head -1)
BIN=$(echo "$NAME" | tr '[:upper:]' '[:lower:]')
W=/disk/scratch/s2982359/$BIN-fuzz
Z3=/disk/scratch/s2982359/z3venv/bin/z3
tar -czf - -C "$HERE/target/release" "$BIN" -C "$HERE/tools" fuzz.py | \
  ssh -o ConnectTimeout=15 -o "ProxyCommand=ssh -q s2982359@ssh.inf.ed.ac.uk nc -4 s2982359.pgr.inf.ed.ac.uk 22" \
    s2982359@s2982359.pgr.inf.ed.ac.uk \
  "mkdir -p $W && tar -C $W -xzf - && cd $W && \
   for s in $*; do timeout 3000 python3 fuzz.py ./$BIN $Z3 $N \$s > out\$s.txt 2>&1 & done; wait; \
   for s in $*; do echo \"seed \$s: \$(head -c 3000 out\$s.txt)\"; done" 2>&1 \
  | grep -v -i "post-quantum\|store now\|upgraded\|pq.html"
