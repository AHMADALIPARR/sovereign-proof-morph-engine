# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
# Deterministic synthetic inputs for the *_checked BQN scripts.
# These are generated test data (Park-Miller LCG), not trained weights.
#   BQN gen_inputs.bqn DIR N V D
#   writes DIR/phenomenal_tensor.bin  i64, N×2 (intensity, raw phase 89·t)
#          DIR/gaussian_embeddings.bin f64, V×D, entries in [-1, 1)
#          DIR/shape.txt               "N V D"
dir‿ns‿vs‿ds ← •args
n‿v‿d ← •ParseFloat¨ ns‿vs‿ds
Lcg ← {2147483647 | 16807 × 𝕨}
Stream ← {𝕨 Lcg` 𝕩⥊0}               # 𝕨 seed, 𝕩 count
intensity ← 2462 | 12345 Stream n
phase_raw ← 89 × ↕n
tensor ← ⥊ intensity ≍˘ phase_raw
emb ← ¯1 + 2 × (2147483647 ÷˜ 777 Stream v × d)
# CBQN has no 64-bit integer cast: write little-endian i64 as (low u32, high i32)
I64 ← {
  hi ← ⌊ 𝕩 ÷ 4294967296
  lo ← 𝕩 - 4294967296 × hi
  lo -↩ 4294967296 × lo ≥ 2147483648
  ⟨32‿'i', 8‿'c'⟩ •bit._cast ⥊ lo ≍˘ hi
}
F64 ← ⟨64‿'f', 8‿'c'⟩ •bit._cast
(dir ∾ "/phenomenal_tensor.bin") •FBytes I64 tensor
(dir ∾ "/gaussian_embeddings.bin") •FBytes F64 emb
(dir ∾ "/shape.txt") •FChars •Repr n‿v‿d
•Out "generated N=" ∾ (•Repr n) ∾ " V=" ∾ (•Repr v) ∾ " D=" ∾ •Repr d
