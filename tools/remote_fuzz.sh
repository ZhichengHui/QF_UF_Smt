#!/usr/bin/env bash
# Usage: tools/remote_fuzz.sh N SEED...
# Copies the release binary and fuzz.py to the checking machine and runs fuzz.py against z3 there,
# one process per seed, N problems each. Prints each run's result.
# Configuration (not in this repository), as for tools/check.sh: CHECK_HOST (ssh destination;
# unset: this machine), CHECK_WORK (work directory there) and Z3 (the z3 executable there), from the
# environment or the file $SOLVER_ENV (default ~/.config/verified-solvers.env).
set -euo pipefail
N=$1; shift
ENVF=${SOLVER_ENV:-$HOME/.config/verified-solvers.env}
if [ -f "$ENVF" ]; then . "$ENVF"; fi
: "${CHECK_WORK:?not set: see the header of tools/remote_fuzz.sh}"
: "${Z3:?not set: see the header of tools/remote_fuzz.sh}"
HERE=$(cd "$(dirname "$0")/.." && pwd)
NAME=$(sed -n 's/^session "\([A-Za-z0-9_]*\)".*/\1/p' "$HERE/urust/ROOT" | head -1)
BIN=$(echo "$NAME" | tr '[:upper:]' '[:lower:]')
W=$CHECK_WORK/$BIN-fuzz
if [ -n "${CHECK_HOST:-}" ]; then RUN=(ssh -o ConnectTimeout=15 "$CHECK_HOST"); else RUN=(bash -c); fi
tar -czf - -C "$HERE/target/release" "$BIN" -C "$HERE/tools" fuzz.py | "${RUN[@]}" \
  "mkdir -p $W && tar -C $W -xzf - && cd $W && \
   for s in $*; do timeout 3000 python3 fuzz.py ./$BIN $Z3 $N \$s > out\$s.txt 2>&1 & done; wait; \
   for s in $*; do echo \"seed \$s: \$(head -c 3000 out\$s.txt)\"; done" 2>&1 \
  | grep -v -i "post-quantum\|store now\|upgraded\|pq.html"
