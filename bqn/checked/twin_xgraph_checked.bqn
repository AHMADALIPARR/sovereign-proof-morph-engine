# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
# Checked variant of ../twin_xgraph.bqn (original kept verbatim).
#   BQN twin_xgraph_checked.bqn DIR
lib ← •Import "lib.bqn"
dir ← ⊑ •args
t0 ← •MonoTime @
g_embs ← lib.Embeddings dir
torus_phase ← lib.TorusPhase lib.Tensor dir
harmonic_scalars ← lib.HarmonicMap torus_phase

# Forward (causal) trace from <BOS> = row 0
init_causal ← 0 ⊏ g_embs
forward_trace ← g_embs‿init_causal lib.Trace harmonic_scalars

# Twin (teleological) trace from <EOS> = last row, over reversed scalars
init_teleo ← ¯1 ⊏ g_embs
twin_scan ← g_embs‿init_teleo lib.Trace ⌽ harmonic_scalars
twin_trace ← ⌽ twin_scan

x_superposition ← (forward_trace + twin_trace) ÷ 2
Snap_Kernel ← {⊑ ⍋ g_embs lib.SqDists 𝕩}
bidirectional_tokens ← Snap_Kernel¨ x_superposition
t1 ← •MonoTime @

fwd ← g_embs lib.Tokens forward_trace
twn ← g_embs lib.Tokens twin_scan
•Out "twin_xgraph steps " ∾ •Repr ≠ fwd
•Out "forward cycle found,mu,lambda " ∾ •Repr torus_phase lib.Cycle fwd
•Out "twin_eos cycle found,mu,lambda " ∾ •Repr (⌽ torus_phase) lib.Cycle twn
•Out "forward argmin_ties " ∾ •Repr g_embs‿init_causal‿forward_trace lib.Ties harmonic_scalars
•Out "twin_eos argmin_ties " ∾ •Repr g_embs‿init_teleo‿twin_scan lib.Ties ⌽ harmonic_scalars
•Out "snap argmin_ties " ∾ •Repr +´ {1 < +´ d = ⌊´ d ← g_embs lib.SqDists 𝕩}¨ x_superposition
•Out "forward distinct,longest_run " ∾ •Repr (≠⍷fwd)‿(lib.LongestRun fwd)
•Out "twin_eos distinct,longest_run " ∾ •Repr (≠⍷twn)‿(lib.LongestRun twn)
•Out "bidirectional distinct " ∾ •Repr ≠ ⍷ bidirectional_tokens
•Out "bidirectional = forward, = twin " ∾ •Repr (+´ bidirectional_tokens = fwd)‿(+´ bidirectional_tokens = ⌽ twn)
•Out "forward_ne_twin steps " ∾ •Repr +´ fwd ≠ ⌽ twn
•Out "bidirectional checksum " ∾ •Repr lib.Checksum bidirectional_tokens
•Out "time_ms twin_xgraph " ∾ •Repr 1000 × t1 - t0
