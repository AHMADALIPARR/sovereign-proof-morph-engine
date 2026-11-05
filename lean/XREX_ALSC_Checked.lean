-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Checked companion of XREX_ALSC.lean (that file is kept unmodified).
-- Minimal fixes: (1) `toNat_add_le` is a theorem, not an axiom;
-- (2) the log bound is an explicit hypothesis of the theorem (a doc comment
-- cannot precede `variable`, and an unused section variable is not included);
-- (3) the `if` is eliminated with by_cases/if_pos/if_neg instead of `split`.
import Mathlib.Data.BitVec
import Mathlib.Tactic

namespace XREX_ALSC_Checked

open BitVec

/-- FP16 maximum representable finite value (65504) modeled in 64-bit register space -/
def fp16_max : BitVec 64 := 65504#64

/-- ALSC Cap Threshold (C = 4) -/
def alsc_cap : BitVec 64 := 4#64

/-- BitVec addition upper bound (proved: toNat of a sum is the sum mod 2^64). -/
theorem toNat_add_le (a b : BitVec 64) : (a + b).toNat ≤ a.toNat + b.toNat := by
  rw [BitVec.toNat_add]
  exact Nat.mod_le _ _

/-- The ALSC function: identity up to the cap, cap + log(1 + x - cap) above it. -/
def alsc_payload (hw_log : BitVec 64 → BitVec 64) (x : BitVec 64) : BitVec 64 :=
  if x.toNat ≤ alsc_cap.toNat then
    x
  else
    alsc_cap + hw_log (1#64 + x - alsc_cap)

/-- ALSC output never exceeds the FP16 maximum, for every 64-bit input,
    given a hardware log whose output is bounded by 64. -/
theorem alsc_fp16_safe (hw_log : BitVec 64 → BitVec 64)
    (hw_log_bound : ∀ v, (hw_log v).toNat ≤ 64) (x : BitVec 64) :
    (alsc_payload hw_log x).toNat ≤ fp16_max.toNat := by
  have hcap : alsc_cap.toNat = 4 := rfl
  have hmax : fp16_max.toNat = 65504 := rfl
  unfold alsc_payload
  rw [hmax]
  by_cases h : x.toNat ≤ alsc_cap.toNat
  · simp only [h, ↓reduceIte]
    omega
  · simp only [h, ↓reduceIte]
    have h1 := toNat_add_le alsc_cap (hw_log (1#64 + x - alsc_cap))
    have h2 := hw_log_bound (1#64 + x - alsc_cap)
    omega

end XREX_ALSC_Checked
