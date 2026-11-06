#!/usr/bin/env bash
# Checks the Isabelle theories on the compute host (Isabelle2026, AutoCorrode in ~/builds/AutoCorrode).
# Each call works in its own directory on the host, so calls can run concurrently.
# TIMEOUT (seconds, default 400) bounds each proof file in mode proof; each check runs in its own process
# group, which is killed (prover included) when the time is up.
# Usage:
#   tools/check.sh build            build the heaps QFUF, QFUF_Spec and QFUF_Pure
#   tools/check.sh proof [FILE...]  process proof theories on the QFUF_Pure heap and print their messages
#                                   (default proof/QFUF_Proof.thy; paths relative to the repo; a directory
#                                   stands for its */*.thy). The heaps are rebuilt first if needed.
#   tools/check.sh session          build the session QFUF_Proof without quick_and_dirty (final check)
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
# The gateway forwards to the host's IPv6 address, which is unreachable; nc -4 goes over IPv4.
host() {
  ssh -o ConnectTimeout=15 -o ServerAliveInterval=15 -o ServerAliveCountMax=8 \
    -o ProxyCommand='ssh -q s2982359@ssh.inf.ed.ac.uk nc -4 s2982359.pgr.inf.ed.ac.uk 22' \
    s2982359@s2982359.pgr.inf.ed.ac.uk "$@"
}
R=/disk/scratch/s2982359/qfuf
I='~/isabelle/Isabelle2026/bin/isabelle'
B=$R/base
DIRS="-d ~/builds/AutoCorrode -d $B/urust -d $B/spec -d $B/pure -d proof"
BUILD="$I build -b -o threads=16 -d ~/builds/AutoCorrode -d $B/urust -d $B/spec -d $B/pure QFUF_Pure"
mode=${1:-proof}; shift || true
case $mode in
  build) cmd="$BUILD 2>&1 | tail -40; " ;;
  session) cmd="$I build -o threads=16 $DIRS QFUF_Proof 2>&1 | tail -60; " ;;
  proof)
    files=""
    for a in ${*:-proof/QFUF_Proof.thy}; do
      if [ -d "$ROOT/$a" ]; then for f in "$ROOT/$a"/*/*.thy; do files+=" ${f#$ROOT/}"; done; else files+=" $a"; fi
    done
    cmd="$BUILD > build.log 2>&1 || { tail -40 build.log; exit 1; }; "
    n=0
    for f in $files; do
      n=$((n+1))
      cmd+="( setsid $I process_theories -l QFUF_Pure $DIRS -O -U -m 150 -o threads=4 -o quick_and_dirty -f $f < /dev/null > out$n.txt 2>&1 & J=\$!; ( sleep ${TIMEOUT:-400}; kill -- -\$J 2>/dev/null && echo TIMEOUT >> out$n.txt ) < /dev/null > /dev/null 2>&1 & T=\$!; wait \$J; echo \"EXIT \$?\" >> out$n.txt; kill \$T 2>/dev/null ) & "
    done
    cmd+="wait; "
    n=0
    for f in $files; do
      n=$((n+1))
      cmd+="echo \"=== $f\"; awk '/^EXIT/{print; next} /^Output \\(/{s=1} /^\$/{s=0} !s' out$n.txt | grep -v '^Loading\\|^Running\\|^Finished\\|^Building\\|^Build started\\|^Draft FAILED\\|^Unfinished\\|^Proofs for\\|^\$' ; "
    done ;;
  *) echo "unknown mode $mode"; exit 2 ;;
esac
W=$R/run-$$-$RANDOM
tar -C "$ROOT" -czf - urust spec pure proof | host "mkdir -p $W $B && tar -C $W -xzf - && rsync -a --delete $W/urust/ $B/urust/ && rsync -a --delete $W/spec/ $B/spec/ && rsync -a --delete $W/pure/ $B/pure/ && cd $W && { $cmd true; }; rm -rf $W" 2>&1 | grep -v 'post-quantum\|store now, decrypt\|server may need\|openssh.com/pq'
