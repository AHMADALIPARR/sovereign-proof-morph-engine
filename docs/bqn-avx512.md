<!-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 -->
<!-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab -->
# CBQN with AVX-512 (Singeli)

Two builds of CBQN at the same commit (b62079a), with GCC 14.2.0:

| build | command | `objdump -d BQN \| grep -c zmm` |
|---|---|---|
| baseline | `make o3` | 0 |
| AVX-512 | `make o3n f="-mprefer-vector-width=512"` | 4557 |

The benchmarked AVX-512 binary is the `-mprefer-vector-width=512` build. For comparison, a plain `make o3n` build (native target, default 256-bit vector preference) contains 572 zmm instructions and is a different binary. A fresh rebuild with `make o3n f="-mprefer-vector-width=512"` reproduces the benchmarked binary byte for byte (4557 zmm). See `docs/measurements/cbqn-zmm.txt`.
CPU: Intel Xeon with avx512f/bw/cd/dq/vl/ifma/vbmi, 8 cores.

`make bqn-avx512` (which runs `scripts/bqn_avx512.sh`) does the following:

1. Counts zmm instructions in both binaries.
2. Runs each checked program 3 times on each build.
3. Compares the deterministic stdout byte for byte.
4. Reports the median wall time.

Measured on 2026-11-04 (load average about 1.0):

| program | outputs | median ms base | median ms AVX-512 |
|---|---|---|---|
| omega_tensor | identical | 5 | 4 |
| phi_replay | identical | 6841 | 7743 |
| twin_xgraph | identical | 20336 | 23207 |
| init_teleo | identical | 17593 | 19319 |

On this workload the AVX-512 build is 11–14% slower on the three trace programs. These programs are scans with a small per-step body (512×64 distance plus grade), so interpreter overhead per step dominates the vector width.
