#!/usr/bin/env bash
# Run a benchmark suite (PLAN.md, Benchmarks).
#
# Usage: bench/run.sh SUITE [SOLVER]
#
# SUITE is a directory bench/SUITE/ whose suite.sh sets ARCHIVE_URL, ARCHIVE_NAME, ARCHIVE_MD5,
# ARCHIVE_PREFIX, TIME_LIMIT (seconds), MEMORY_LIMIT (KiB) and INSTANCES (lines "answer sha256
# path", the path below ARCHIVE_PREFIX in the archive). SOLVER defaults to target/release/qfuf.
# The archive is fetched once into BENCH_CACHE (default bench/.cache), checked by md5, and the
# instances are extracted and checked by sha256. JOBS (default 4) instances run at once; Z3
# (default z3) checks the models of sat answers.
#
# Each instance gets one line: path, expected answer, result, seconds. Results: `ok` (answer as
# expected; for sat the model checked), `timeout`, `error` (no answer: memory limit, crash, ...),
# `WRONG` (answer differs, or a bad model). A summary follows; the exit status is 1 when any
# answer is WRONG.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
suite=${1:?usage: bench/run.sh SUITE [SOLVER]}
solver=$(realpath "${2:-$here/../target/release/qfuf}")
cache=${BENCH_CACHE:-$here/.cache}
jobs=${JOBS:-4}
z3=$(command -v "${Z3:-z3}") || { echo "z3 not found (needed to check models)" >&2; exit 2; }
[ -f "$here/$suite/suite.sh" ] || { echo "no suite $suite" >&2; exit 2; }
[ -x "$solver" ] || { echo "no solver $solver (cargo build --release)" >&2; exit 2; }
# shellcheck source=/dev/null
source "$here/$suite/suite.sh"

mkdir -p "$cache"
archive=$cache/$ARCHIVE_NAME
if ! [ -f "$archive" ] || ! echo "$ARCHIVE_MD5  $archive" | md5sum -c --status; then
  echo "fetching $ARCHIVE_URL" >&2
  curl -fsSL -o "$archive.part" "$ARCHIVE_URL"
  echo "$ARCHIVE_MD5  $archive.part" | md5sum -c --status || { echo "md5 mismatch: $ARCHIVE_URL" >&2; exit 2; }
  mv "$archive.part" "$archive"
fi
inst=$cache/$suite
mkdir -p "$inst"
list=$(mktemp)
trap 'rm -f "$list"' EXIT
echo "$INSTANCES" | awk 'NF == 3' > "$list"
missing=$(while read -r _ sha path; do
  [ -f "$inst/$path" ] && echo "$sha  $inst/$path" | sha256sum -c --status || echo "$ARCHIVE_PREFIX/$path"
done < "$list")
if [ -n "$missing" ]; then
  echo "$missing" | tar --zstd -xf "$archive" -C "$inst" --strip-components="$(echo "$ARCHIVE_PREFIX" | awk -F/ '{print NF}')" -T -
fi
while read -r _ sha path; do
  echo "$sha  $inst/$path" | sha256sum -c --status || { echo "sha256 mismatch: $path" >&2; exit 2; }
done < "$list"

run_one() {
  local expected=$1 path=$2 file=$inst/$2 out start end status result
  out=$(mktemp)
  start=$(date +%s.%N)
  status=0
  (sed 's/(check-sat)/(check-sat)\n(get-model)/' "$file" |
    (ulimit -v "$MEMORY_LIMIT"; timeout -s KILL "$TIME_LIMIT" "$solver")) > "$out" 2>/dev/null || status=$?
  end=$(date +%s.%N)
  local answer
  answer=$(head -n 1 "$out")
  if [ "$status" = 137 ]; then
    result=timeout
  elif [ "$answer" != sat ] && [ "$answer" != unsat ]; then
    result=error
  elif [ "$answer" != "$expected" ]; then
    result=WRONG
  elif [ "$answer" = sat ] && ! python3 "$here/check_model.py" "$file" <(tail -n +2 "$out") "$z3" > /dev/null; then
    result=WRONG
  else
    result=ok
  fi
  rm -f "$out"
  printf '%s %s %s %.2f\n' "$path" "$expected" "$result" "$(echo "$end - $start" | bc)"
}
export -f run_one
export inst solver z3 here TIME_LIMIT MEMORY_LIMIT

results=$(awk '{print $1, $3}' "$list" | xargs -P "$jobs" -L 1 bash -c 'run_one "$0" "$1"' | sort)
echo "$results"
echo "$results" | awk -v suite="$suite" -v limit="$TIME_LIMIT" '
  { n++; c[$3]++; if ($3 == "ok") { t += $4; s[$2]++ } }
  END {
    printf "suite %s: %d of %d solved (sat %d, unsat %d), %d timeout, %d error, %d WRONG; %.2f s on the solved\n",
      suite, c["ok"], n, s["sat"], s["unsat"], c["timeout"], c["error"], c["WRONG"], t
  }'
! echo "$results" | grep -q ' WRONG '
