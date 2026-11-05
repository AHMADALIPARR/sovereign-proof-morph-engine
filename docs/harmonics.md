<!-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 -->
<!-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab -->
# Harmonics

The BQN replay uses the harmonic scalar of the sampled torus phase:

    h(t) = cos(φ · π · x / 2462),  x = 89·t mod 2462,  φ = (1 + √5) / 2

This is how `Harmonic_Map` in the original parses, and
[bqn/checked/lib.bqn](../bqn/checked/lib.bqn) keeps that meaning.

## What is proved

[agda/PhiHarmonics.agda](../agda/PhiHarmonics.agda) (`--safe`, no postulates) proves the integer structure:

- `phase-lt`: phase t < 2462;
- `phase-period`: phase (t + 2462) ≡ phase t;
- `roundtrip`: phaseInv (phase t) ≡ t mod 2462, where the inverse multiplier is 83 (89·83 ≡ 1 mod 2462);
- `antipode-involutive`: p ↦ p + 1231 mod 2462 is an involution on phases, and `antipode-of-origin`: antipode 0 ≡ 1231;
- `cassini`: Cassini's identity for every n; 89 is F₁₁.

[lean/HarmonicAperiodic_Checked.lean](../lean/HarmonicAperiodic_Checked.lean) proves `harmonic_never_loops`, using
φ irrational from [lean/TwinAnchor_Checked.lean](../lean/TwinAnchor_Checked.lean) (√5 irrational).
[lean/PhaseNormalization.lean](../lean/PhaseNormalization.lean) proves gcd(89, 2462) = 1, the winding closes
first at 2462, and two samples collide iff their times agree mod 2462.

## What is measured

The values in [figures/harmonic_scalars.png](figures/harmonic_scalars.png) are the CBQN values at every phase
0..2461. The measured range is ¯0.9999996584275549 to 1.

A harmonic value depends only on the phase, and the phase has period 2462. So the
(token, phase) trace is a finite deterministic system, and it must become
periodic. The measured period is λ = 2462 for every trace
([measurements/bqn.txt](measurements/bqn.txt)). The harmonic function of the
continuous time never repeats exactly; the sampled phase does.
