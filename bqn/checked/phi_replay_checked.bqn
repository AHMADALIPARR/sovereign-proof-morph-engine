# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
# Checked variant of ../phi_replay.bqn (original kept verbatim).
#   BQN phi_replay_checked.bqn DIR
lib ← •Import "lib.bqn"
dir ← ⊑ •args
t0 ← •MonoTime @
g_embs ← lib.Embeddings dir
v_size‿d_size ← ≢ g_embs
torus_phase ← lib.TorusPhase lib.Tensor dir
harmonic_scalars ← lib.HarmonicMap torus_phase
init_state ← 0 ⊏ g_embs
experiential_trace ← g_embs‿init_state lib.Trace harmonic_scalars
token_sequence ← g_embs lib.Tokens experiential_trace
t1 ← •MonoTime @
ties ← g_embs‿init_state‿experiential_trace lib.Ties harmonic_scalars
cyc ← torus_phase lib.Cycle token_sequence

•Out "phi_replay V D " ∾ •Repr v_size‿d_size
•Out "steps " ∾ •Repr ≠ token_sequence
•Out "harmonic_min_max " ∾ •Repr (⌊´ harmonic_scalars)‿(⌈´ harmonic_scalars)
•Out "distinct_tokens " ∾ •Repr ≠ ⍷ token_sequence
•Out "longest_run " ∾ •Repr lib.LongestRun token_sequence
•Out "argmin_ties " ∾ •Repr ties
•Out "cycle found,mu,lambda " ∾ •Repr cyc
•Out "first_32_tokens " ∾ •Repr 32 ↑ token_sequence
•Out "token_checksum " ∾ •Repr lib.Checksum token_sequence
•Out "time_ms phi_replay_trace " ∾ •Repr 1000 × t1 - t0
