#!/usr/bin/env bash
# Times `Tn count` for n in 2 60 300 and count in 0 and COUNT, in randomised blocks.
# Usage: bench/tables/run.sh OUTDIR BLOCKS COUNT   (after `./gen.sh && lake build`)
# Writes OUTDIR/runs.tsv (block, order, tables, count, user s, sys s, max RSS KiB, load1) and OUTDIR/env.txt.
out=$1; blocks=$2; count=$3
[ -n "$out" ] && [ -n "$blocks" ] && [ -n "$count" ] || { echo "usage: run.sh OUTDIR BLOCKS COUNT" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$out" || exit 1
{
  echo "date: $(date --iso-8601=seconds)"
  echo "command: $0 $*"
  echo "library commit: $(git -C "$here" rev-parse HEAD) ($(git -C "$here" status --short --untracked-files=no | wc -l) changed files)"
  echo "lean: $(cd "$here" && lake env lean --version)"
  for n in 2 60 300; do echo "sha256 T$n: $(sha256sum "$here/.lake/build/bin/T$n" | cut -d' ' -f1)"; done
  echo "machine: $(uname -srm), $(nproc) cpus"
} > "$out/env.txt"
printf 'block\torder\ttables\tcount\tuser\tsys\tmaxrss\tload1\n' > "$out/runs.tsv"
for b in $(seq 1 "$blocks"); do
  order=0
  for cell in $(for n in 2 60 300; do for c in 0 "$count"; do echo "$n:$c"; done; done | shuf); do
    IFS=: read -r n c <<< "$cell"
    order=$((order+1))
    load=$(cut -d' ' -f1 /proc/loadavg)
    t=$( { /usr/bin/time -f '%U %S %M' "$here/.lake/build/bin/T$n" "$c" > /dev/null; } 2>&1 | tail -n 1)
    read -r u s m <<< "$t"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$order" "$n" "$c" "$u" "$s" "$m" "$load" >> "$out/runs.tsv"
  done
done
echo done >> "$out/env.txt"
