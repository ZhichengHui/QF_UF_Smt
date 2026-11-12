#!/usr/bin/env bash
# Usage: tools/check.sh SESSION [MINUTES]
# Copies urust/, spec/ and proof/ to this project's directory on the compute server (registered in
# the ROOTS file of the Isabelle installation there) and builds SESSION (e.g. BVSmt_Top or
# QFUF_Top) and its ancestors with `isabelle build -b`, in a systemd scope limited to MINUTES
# minutes (default 120) and 96 GB. Prints the sessions built and Isabelle's errors; the full log
# stays in $RT/work/isabuild/check-SESSION.log on the server.
set -euo pipefail
S=$1; M=${2:-120}
HERE=$(cd "$(dirname "$0")/.." && pwd)
NAME=$(sed -n 's/^session "\([A-Za-z0-9_]*\)".*/\1/p' "$HERE/urust/ROOT" | head -1)
P=$(echo "$NAME" | tr '[:upper:]' '[:lower:]')
RT=/disk/scratch/s2982359
SSH=(ssh -o ConnectTimeout=15 -o ServerAliveInterval=15 -o ServerAliveCountMax=40
     -o "ProxyCommand=ssh -q s2982359@ssh.inf.ed.ac.uk nc -4 s2982359.pgr.inf.ed.ac.uk 22"
     s2982359@s2982359.pgr.inf.ed.ac.uk)
tar -C "$HERE" -czf - urust spec proof | "${SSH[@]}" "
  set -e; D=$RT/home/projects/$P; mkdir -p \$D && cd \$D && rm -rf urust spec proof && tar -xzf -
  L=$RT/work/isabuild/check-$S.log; mkdir -p $RT/work/isabuild
  HOME=$RT/home systemd-run --user --scope --slice=check-$P -p MemoryMax=96G -p RuntimeMaxSec=$((M * 60)) \
    $RT/isabelle/Isabelle2026/bin/isabelle build -b -o threads=8 $S > \$L 2>&1; R=\$?
  grep -E '^(Building|Finished|Unfinished|\*\*\*)' \$L | head -60; echo EXIT \$R" 2>&1 \
  | grep --line-buffered -v -i "post-quantum\|store now\|upgraded\|pq.html"
