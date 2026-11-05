# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
# Writes the per-step traces used by the figures, as tab-separated text:
#   step  phase  harmonic  forward_token  twin_token  snap_token  snap_tied
# twin_token is the EOS twin trace re-aligned to forward time (⌽ of the scan).
#   BQN dump_traces.bqn DIR OUT.tsv
lib ← •Import "lib.bqn"
dir‿out ← •args
g ← lib.Embeddings dir
ph ← lib.TorusPhase lib.Tensor dir
h ← lib.HarmonicMap ph
fwd_tr ← g‿(0 ⊏ g) lib.Trace h
twn_scan ← g‿(¯1 ⊏ g) lib.Trace ⌽ h
x ← (fwd_tr + ⌽ twn_scan) ÷ 2
dists ← g⊸lib.SqDists¨ x
snap ← {⊑ ⍋ 𝕩}¨ dists
tied ← {1 < +´ 𝕩 = ⌊´ 𝕩}¨ dists
fwd ← g lib.Tokens fwd_tr
twn ← ⌽ g lib.Tokens twn_scan
Num ← {s ← •Fmt 𝕩 ⋄ ('-'¨⌾((s = '¯')⊸/) s)}
rows ← {∾ ⟨Num 𝕩, @+9, Num 𝕩 ⊑ ph, @+9, Num 𝕩 ⊑ h, @+9, Num 𝕩 ⊑ fwd, @+9, Num 𝕩 ⊑ twn, @+9, Num 𝕩 ⊑ snap, @+9, Num 𝕩 ⊑ tied⟩}¨ ↕≠ph
out •FLines ⟨"# step	phase	harmonic	forward_token	twin_token	snap_token	snap_tied"⟩ ∾ rows
•Out "wrote " ∾ (•Repr ≠rows) ∾ " rows"
