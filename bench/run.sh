#!/usr/bin/env bash
# Times `appendbench n` for each size in randomised blocks: every size once per block, in a fresh random order.
# Usage: [SIZES="1000 4000 ..."] bench/run.sh OUTDIR BLOCKS
# Writes OUTDIR/runs.tsv (block, order, n, user s, sys s, max RSS KiB, load1) and OUTDIR/env.txt.
# Build first with `cd bench && lake build`.  Keep OUTDIR outside the repository.
out=$1; blocks=$2
[ -n "$out" ] && [ -n "$blocks" ] || { echo "usage: run.sh OUTDIR BLOCKS" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
lib=$here/..
bin=$here/.lake/build/bin/appendbench
[ -x "$bin" ] || { echo "build first: (cd $here && lake build)" >&2; exit 1; }
mkdir -p "$out" || exit 1
{
  echo "date: $(date --iso-8601=seconds)"
  echo "command: $0 $*"
  echo "library commit: $(git -C "$lib" rev-parse HEAD) ($(git -C "$lib" status --short --untracked-files=no | wc -l) changed files)"
  echo "lean: $(cd "$here" && lake env lean --version)"
  echo "binary sha256: $(sha256sum "$bin" | cut -d' ' -f1)"
  echo "machine: $(uname -srm), $(nproc) cpus"
} > "$out/env.txt"
printf 'block\torder\tn\tuser\tsys\tmaxrss\tload1\n' > "$out/runs.tsv"
for b in $(seq 1 "$blocks"); do
  order=0
  for n in $(printf '%s\n' ${SIZES:-1000 4000 16000 256000 1024000} | shuf); do
    order=$((order+1))
    load=$(cut -d' ' -f1 /proc/loadavg)
    t=$( { /usr/bin/time -f '%U %S %M' "$bin" "$n" > /dev/null; } 2>&1 | tail -n 1)
    read -r u s m <<< "$t"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$order" "$n" "$u" "$s" "$m" "$load" >> "$out/runs.tsv"
  done
done
echo done >> "$out/env.txt"
