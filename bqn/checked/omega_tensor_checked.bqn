# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
# Checked variant of ../omega_tensor.bqn (original kept verbatim).
#   BQN omega_tensor_checked.bqn DIR      (DIR from gen_inputs.bqn)
# Lines starting with "time" are timings; every other line is deterministic.
lib ← •Import "lib.bqn"
dir ← ⊑ •args
t0 ← •MonoTime @

# 1. Ingestion (i64 read via 32-bit halves; CBQN •bit._cast has no i64)
e_tensor ← lib.Tensor dir
n ← ≠ e_tensor
q_intensity ← 0 ⊏˘ e_tensor
r_phase     ← 1 ⊏˘ e_tensor

# 2. Z_2462 quotient
torus_phase ← 2462 | r_phase

# 3. Ring delta. The original {2462|𝕩-𝕪} names 𝕪, which is not a BQN
# special name; 𝕨 is the left argument. ¯1⌽ rotates RIGHT, so
# (¯1⌽T)[n] = T[n-1] and the delta is T[n] - T[n-1] (mod 2462).
Ring_Delta ← {2462 | 𝕩 - 𝕨}
phase_interference ← (¯1 ⌽ torus_phase) Ring_Delta torus_phase

# 4. Coherence mask
coherence_mask ← q_intensity ≤ torus_phase
coherent_states ← coherence_mask / e_tensor
t1 ← •MonoTime @

•Out "omega_tensor n " ∾ •Repr n
•Out "torus_phase_min_max " ∾ •Repr (⌊´ torus_phase)‿(⌈´ torus_phase)
•Out "torus_phase_in_range " ∾ •Repr ∧´ (0 ≤ torus_phase) ∧ torus_phase < 2462
•Out "phase_is_permutation_of_first_2462 " ∾ •Repr (2462 ≤ n) ∧ (↕2462) ≡ ∧ 2462 ↑ torus_phase
•Out "delta_eq_89_count " ∾ •Repr +´ 89 = phase_interference
•Out "delta_at_0 " ∾ •Repr ⊑ phase_interference
•Out "coherent_count " ∾ •Repr ≠ coherent_states
•Out "coherent_checksum " ∾ •Repr lib.Checksum ⥊ coherent_states
•Out "time_ms omega_tensor " ∾ •Repr 1000 × t1 - t0
