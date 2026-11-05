#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
#
# Runs the checked BQN programs on a baseline CBQN and an AVX-512 CBQN,
# checks the AVX-512 binary contains zmm instructions, checks both builds
# print identical deterministic output, and reports median timings.
#   BQN_BASE=... BQN_AVX512=... scripts/bqn_avx512.sh [OUTDIR] [RUNS]
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
base=${BQN_BASE:-/workspace/_tools_cbqn/CBQN/BQN}
avx=${BQN_AVX512:-/workspace/_tools_cbqn/CBQN-avx512/BQN}
out=${1:-$root/build/bqn}
runs=${2:-3}
data=$out/data
mkdir -p "$data"
echo "zmm_count base=$(objdump -d "$base" | grep -c zmm || true) avx512=$(objdump -d "$avx" | grep -c zmm || true)"
echo "cpu_avx512f=$(grep -c -m1 avx512f /proc/cpuinfo || true)"
"$base" "$root/bqn/checked/gen_inputs.bqn" "$data" 7386 512 64
fail=0
for p in omega_tensor phi_replay twin_xgraph init_teleo; do
  for b in base avx; do
    bin=${!b}
    : > "$out/$p.$b.times"
    for i in $(seq "$runs"); do
      s=$(date +%s%N)
      "$bin" "$root/bqn/checked/${p}_checked.bqn" "$data" > "$out/$p.$b.raw"
      e=$(date +%s%N)
      echo $(( (e - s) / 1000000 )) >> "$out/$p.$b.times"
    done
    grep -v '^time_ms' "$out/$p.$b.raw" > "$out/$p.$b.out"
  done
  if cmp -s "$out/$p.base.out" "$out/$p.avx.out"; then same=identical; else same=DIFFERENT; fail=1; fi
  mb=$(sort -n "$out/$p.base.times" | sed -n "$(( (runs + 1) / 2 ))p")
  ma=$(sort -n "$out/$p.avx.times" | sed -n "$(( (runs + 1) / 2 ))p")
  echo "$p outputs=$same median_wall_ms base=$mb avx512=$ma runs=$runs"
done
exit $fail
