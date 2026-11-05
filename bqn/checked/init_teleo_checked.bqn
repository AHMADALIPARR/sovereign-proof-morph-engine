# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
# Checked variant of ../init_teleo.bqn (original kept verbatim).
#   BQN init_teleo_checked.bqn DIR [M]
# Active_Memory (undefined in the original) is taken as the last M (default
# 16) states of the forward trace. Compares the twin trace launched from the
# antipodal anchor with the one launched from <EOS>.
lib ← •Import "lib.bqn"
dir ← ⊑ •args
m ← •BQN ⊑ 1 ↓ •args ∾ <"16"
t0 ← •MonoTime @
g_embs ← lib.Embeddings dir
torus_phase ← lib.TorusPhase lib.Tensor dir
harmonic_scalars ← lib.HarmonicMap torus_phase
forward_trace ← g_embs‿(0 ⊏ g_embs) lib.Trace harmonic_scalars

# 1. Context vector: mean over the M axis (+˝, since +´ needs a list)
active_memory ← > (-m) ↑ forward_trace
ctx_vector ← (+˝ active_memory) ÷ ≠ active_memory
# 2. Antipode
antipode_phase ← 1231
# 3. Harmonic projection of the antipode
teleo_resonance ← lib.HarmonicMap antipode_phase
# 4. Anchor
init_teleo ← ctx_vector × teleo_resonance
# 5. Twin traces (scan order over reversed scalars)
rev ← ⌽ harmonic_scalars
anti_scan ← g_embs‿init_teleo lib.Trace rev
eos_scan ← g_embs‿(¯1 ⊏ g_embs) lib.Trace rev
twin_trace ← ⌽ anti_scan
t1 ← •MonoTime @

anti ← g_embs lib.Tokens anti_scan
eos ← g_embs lib.Tokens eos_scan
same ← anti = eos
•Out "init_teleo m " ∾ •Repr m
•Out "teleo_resonance " ∾ •Repr teleo_resonance
•Out "init_teleo_is_vocab_row " ∾ •Repr ∨´ g_embs ≡⎉1 init_teleo
•Out "antipodal cycle found,mu,lambda " ∾ •Repr (⌽ torus_phase) lib.Cycle anti
•Out "eos cycle found,mu,lambda " ∾ •Repr (⌽ torus_phase) lib.Cycle eos
•Out "antipodal argmin_ties " ∾ •Repr g_embs‿init_teleo‿anti_scan lib.Ties rev
•Out "eos argmin_ties " ∾ •Repr g_embs‿(¯1 ⊏ g_embs)‿eos_scan lib.Ties rev
•Out "antipodal distinct,longest_run " ∾ •Repr (≠⍷anti)‿(lib.LongestRun anti)
•Out "eos distinct,longest_run " ∾ •Repr (≠⍷eos)‿(lib.LongestRun eos)
•Out "antipodal_vs_eos agree_steps " ∾ •Repr +´ same
•Out "antipodal_vs_eos merge_step " ∾ •Repr ⊑ (/ ∧` ⌾ ⌽ same) ∾ ≠ same
•Out "antipodal checksum " ∾ •Repr lib.Checksum anti
•Out "time_ms init_teleo " ∾ •Repr 1000 × t1 - t0
