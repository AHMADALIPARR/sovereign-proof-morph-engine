# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
# Shared, corrected definitions for the *_checked scripts. Each fix relative
# to the original scripts is listed in docs/bqn-checked.md.
pi ⇐ π   # CBQN has no •math.pi; π is the BQN constant
phi ⇐ (1 + √5) ÷ 2   # •math has no Sqrt; √ is the primitive

# CBQN has no 64-bit integer cast: read i64 as (low u32, high i32) pairs;
# exact for |value| < 2^53
FromI64 ⇐ {
  w ← ⟨8‿'c', 32‿'i'⟩ •bit._cast 𝕩
  lo‿hi ← <˘⍉ (2 ÷˜ ≠w)‿2 ⥊ w
  (4294967296 × hi) + lo + 4294967296 × lo < 0
}
FromF64 ⇐ ⟨8‿'c', 64‿'f'⟩ •bit._cast

# dir → n‿v‿d
Shape ⇐ {•BQN •FChars 𝕩 ∾ "/shape.txt"}

# N×2 tensor of (intensity, raw phase)
Tensor ⇐ {
  raw ← FromI64 •FBytes 𝕩 ∾ "/phenomenal_tensor.bin"
  (2 ÷˜ ≠ raw)‿2 ⥊ raw
}

# V×D embedding matrix (the flat file carries no shape: D comes from shape.txt)
Embeddings ⇐ {
  n‿v‿d ← Shape 𝕩
  v‿d ⥊ FromF64 •FBytes 𝕩 ∾ "/gaussian_embeddings.bin"
}

TorusPhase ⇐ {2462 | 1 ⊏˘ 𝕩}

# As written in the original: cos applied to (φ·π·x)/2462
HarmonicMap ⇐ {•math.Cos (phi × pi × 𝕩) ÷ 2462}

# Replay kernel over embedding matrix g: 𝕨 previous state (vector), 𝕩 scalar
SqDists ⇐ {g 𝕊 s: +˝˘ ⋆⟜2 g -⎉1 s}
Step ⇐ {g 𝕊 p‿s: (⊑ ⍋ g SqDists p × s) ⊏ g}

# Trace from initial state 𝕨 over scalars 𝕩: list of embedding vectors
Trace ⇐ {g‿init 𝕊 s: (<init) {g Step 𝕨‿𝕩}` s}

# Token ids of a trace (row index in g; first match)
Tokens ⇐ {g 𝕊 tr: g ⊐ > tr}

# Exact argmin ties: number of steps whose minimum distance is attained by
# more than one vocabulary row. 𝕨: g‿init‿trace, 𝕩: scalars (scan order).
Ties ⇐ {g‿init‿tr 𝕊 s:
  prev ← (<init) ∾ ¯1 ↓ tr
  +´ {p 𝕊 x: dd ← g SqDists p × x ⋄ 1 < +´ dd = ⌊´ dd}´¨ prev ⋈¨ s
}

# Cycle detection on the deterministic finite-state system (token, phase
# index mod 2462). 𝕨: phase index per step, 𝕩: token per step.
# Result: ⟨found, μ (first state of the cycle), λ (period)⟩; λ=0 if none
# within the trace.
Cycle ⇐ {ph 𝕊 tok:
  key ← (2462 × tok) + 2462 | ph
  first ← key ⊐ key
  j ← ⊑ (/ first ≠ ↕≠key) ∾ ≠key
  mu ← j ⊑ first ∾ j
  ⟨j < ≠key, (j < ≠key) ⊑ ¯1‿mu, j - mu⟩
}

LongestRun ⇐ {⌈´ ≠¨ (+` 1 ∾ ≠´˘ 2 ↕ 𝕩) ⊔ 𝕩}

# exact checksum of a token list
Checksum ⇐ {1000000007 | +´ 𝕩 × 1 + 1000 | ↕≠𝕩}
