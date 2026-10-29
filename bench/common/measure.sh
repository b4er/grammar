#!/usr/bin/env bash
# measure.sh CASE PARSER CMD...
#
# The cost of one parse by CMD, which parses its input REPS times when given
# REPS as its last argument (0: start-up, reading and lexing only).  Prints
# TSV rows CASE PARSER METRIC VALUE:
#
#   tokens        $TOKENS, if set
#   ms            wall-clock: median over RUNS of (t(REPS) - t(0)) / REPS
#   instructions  with IR=1: callgrind's instruction count Ir(1) - Ir(0)

set -euo pipefail
export LC_ALL=C   # EPOCHREALTIME's decimal point

case_=$1 parser=$2
shift 2
REPS=${REPS:-20} RUNS=${RUNS:-5} IR=${IR:-0}

row() { printf '%s\t%s\t%s\t%s\n' "$case_" "$parser" "$1" "$2"; }

secs() {
  local s=$EPOCHREALTIME
  "$@" > /dev/null
  local e=$EPOCHREALTIME
  awk -v s="$s" -v e="$e" 'BEGIN { printf "%.6f\n", e - s }'
}

ir() {
  local f
  f=$(mktemp)
  valgrind -q --tool=callgrind --fair-sched=yes --callgrind-out-file="$f" "$@" > /dev/null
  awk '/^(summary|totals):/ { print $2; exit }' "$f"
  rm -f "$f"
}

[[ -z ${TOKENS:-} ]] || row tokens "$TOKENS"

for ((i = 0; i < RUNS; i++)); do
  t0=$(secs "$@" 0)
  t1=$(secs "$@" "$REPS")
  awk -v a="$t0" -v b="$t1" -v n="$REPS" 'BEGIN { printf "%.4f\n", (b - a) * 1000 / n }'
done | sort -g | awk '{ x[NR] = $1 } END { print x[int((NR + 1) / 2)] }' |
  { read -r ms; row ms "$ms"; }

if [[ $IR == 1 ]]; then
  i0=$(ir "$@" 0)
  i1=$(ir "$@" 1)
  row instructions $((i1 - i0))
fi
