<!-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 -->
<!-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab -->
# Torus invariant

The knot coordinate at integer time t is (m, l) = (89·t, 2462·t). The invariant
is 2462·m = 89·l.

- [agda/TorusInvariant.agda](../agda/TorusInvariant.agda) defines `Invariant`, `project` and
  `path-proof : (t : ℕ) → Invariant (project t)`, and
  `VerifiedState = Σ KnotCoord Invariant`.
- [agda/ExtractTorusPath.agda](../agda/ExtractTorusPath.agda) is compiled through MAlonzo.
  [extract/gen_torus_path.sh](../extract/gen_torus_path.sh) runs the binary and writes
  [extract/torus_path.h](../extract/torus_path.h): 4096 rows, t = 0..4095. Each row is the
  first projection of `collapseToVerified t`. The header records the sha256 of both Agda sources.
- The Rust torus engine ([rust/src/torus.rs](../rust/src/torus.rs)) reads that table.
  It rejects a corrupted or short table (test `g01_negative_corrupted_table_rejected`).
  `spme torus` prints `torus table: 4096 rows, header sha256 7eea5d0f…; phase over t=0..2461 is a permutation: true`.
- The gate re-checks m = 89t, l = 2462t and phase = 89t mod 2462 for every candidate.
  It also checks t > last_t.

gcd(89, 2462) = 1, so the phase map t ↦ 89t mod 2462 is a permutation of
Z₂₄₆₂. The winding first closes at t = 2462
([lean/PhaseNormalization.lean](../lean/PhaseNormalization.lean); tests `g01`, `g02`).
See [figures/torus_path.png](figures/torus_path.png).
