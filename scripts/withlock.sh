#!/usr/bin/env bash
# Run a command while holding one of $LEAN_SLOTS (default 2) machine-wide Lean slots, so that
# several agents working in parallel never run more than that many Lean processes at once.
# usage: bash scripts/withlock.sh <command> [args...]
ROOT=$(cd "$(dirname "$0")/.." && pwd)
SLOTS=${LEAN_SLOTS:-2}
LOCKDIR="$ROOT/.lake/leanlocks"
mkdir -p "$LOCKDIR"
while :; do
  for i in $(seq 0 $((SLOTS - 1))); do
    d="$LOCKDIR/slot$i"
    if mkdir "$d" 2>/dev/null; then
      echo $$ > "$d/pid"
      trap 'rm -rf "$d"' EXIT INT TERM HUP
      "$@"
      exit $?
    fi
    # Reclaim a slot whose holder has died, or that is older than 40 minutes.
    pid=$(cat "$d/pid" 2>/dev/null)
    if [ -n "$pid" ] && ! kill -0 "$pid" 2>/dev/null; then rm -rf "$d"; continue; fi
    if [ -n "$(find "$d" -maxdepth 0 -mmin +40 2>/dev/null)" ]; then rm -rf "$d"; fi
  done
  sleep 7
done
