#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
#
# Regenerates docs/figures/*.png and docs/figures/*.svg from measured data only:
#   - per-step traces dumped by bqn/checked/dump_traces.bqn (CBQN run),
#   - the MAlonzo-extracted extract/torus_path.h,
#   - the AVX-512 timing and tie lines in docs/measurements/bqn.txt.
#   BQN=... scripts/figures.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
bqn=${BQN:-/workspace/_tools_cbqn/CBQN/BQN}
b=$root/build/figures
data=$root/build/bqn/data
mkdir -p "$b" "$data" "$root/docs/figures"
[ -f "$data/shape.txt" ] || "$bqn" "$root/bqn/checked/gen_inputs.bqn" "$data" 7386 512 64
"$bqn" "$root/bqn/checked/dump_traces.bqn" "$data" "$b/traces.tsv"
m=$root/docs/measurements/bqn.txt
# program  base_ms  avx512_ms
sed -n 's/^\([a-z_]*\) outputs=identical median_wall_ms base=\([0-9]*\) avx512=\([0-9]*\).*/\1 \2 \3/p' "$m" > "$b/timings.dat"
# trace  exact_argmin_ties
sed -n 's/^\([a-z_]*\) argmin_ties \([0-9]*\)$/\1 \2/p' "$m" | awk '!s[$1]++' > "$b/ties.dat"
# t  m=89t  l=2462t  (rows of the extracted table)
sed -n 's/^ *{ *\([0-9]*\)ULL, *\([0-9]*\)ULL *},.*/\1 \2/p' "$root/extract/torus_path.h" | awk '{print NR-1, $1, $2}' > "$b/torus.dat"
[ -s "$b/timings.dat" ] && [ -s "$b/ties.dat" ] && [ -s "$b/torus.dat" ]
for ext in png svg; do
  gnuplot -e "b='$b'; out='$root/docs/figures'; ext='$ext'" "$root/scripts/figures.gp"
done
ls -l "$root/docs/figures"
