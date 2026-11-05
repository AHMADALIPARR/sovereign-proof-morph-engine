-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Checked companion of SovereignSuperposition.lean (kept unmodified).
-- Minimal fixes: `toNat_add_le` proved instead of postulated; the log bound
-- is an explicit hypothesis threaded through alsc_fp16_safe and
-- extract_verified_agent; ω_m/ω_l unfolded before omega; `if` eliminated by
-- by_cases instead of `split`.
import Mathlib.Data.BitVec
import Mathlib.Tactic

namespace SovereignSuperposition_Checked

open BitVec

/-- Topological fingerprint parameters -/
def ω_m : Nat := 89
def ω_l : Nat := 2462

/-- Hardware constraints -/
def fp16_max : BitVec 64 := 65504#64
def alsc_cap : BitVec 64 := 4#64

theorem toNat_add_le (a b : BitVec 64) : (a + b).toNat ≤ a.toNat + b.toNat := by
  rw [BitVec.toNat_add]
  exact Nat.mod_le _ _

/-- ALSC engine -/
def alsc_payload (hw_log : BitVec 64 → BitVec 64) (x : BitVec 64) : BitVec 64 :=
  if x.toNat ≤ alsc_cap.toNat then
    x
  else
    alsc_cap + hw_log (1#64 + x - alsc_cap)

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

/-- An agent state carries proofs of both its knot and energy invariants. -/
structure VerifiedAgentState where
  m : Nat
  l : Nat
  knot_invariant : 2462 * m = 89 * l
  energy : BitVec 64
  alsc_invariant : energy.toNat ≤ 65504

/-- Project step t onto the knot and cap the raw energy, with both proofs. -/
def extract_verified_agent (hw_log : BitVec 64 → BitVec 64)
    (hw_log_bound : ∀ v, (hw_log v).toNat ≤ 64)
    (t : Nat) (raw_energy : BitVec 64) : VerifiedAgentState :=
  { m := ω_m * t,
    l := ω_l * t,
    knot_invariant := by
      unfold ω_m ω_l
      omega,
    energy := alsc_payload hw_log raw_energy,
    alsc_invariant := alsc_fp16_safe hw_log hw_log_bound raw_energy }

end SovereignSuperposition_Checked
