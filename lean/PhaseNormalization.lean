-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Phase normalization on Z_2462 with step 89 (the torus used by omega_tensor
-- and the morph torus layer). Zero sorry, zero user axioms.
import Mathlib.Tactic

namespace PhaseNormalization

/-- 89 and 2462 are coprime, so the step-89 walk visits all of Z_2462. -/
theorem coprime_89_2462 : Nat.gcd 89 2462 = 1 := by norm_num

/-- Phase of sample t. -/
def phase (t : ℕ) : ℕ := (89 * t) % 2462

/-- Inverse map: 83 * 89 = 7387 = 3 * 2462 + 1. -/
def phaseInv (p : ℕ) : ℕ := (83 * p) % 2462

theorem inverse_const : (83 * 89) % 2462 = 1 := by norm_num

theorem phase_lt (t : ℕ) : phase t < 2462 := Nat.mod_lt _ (by norm_num)

/-- Roundtrip: phaseInv (phase t) = t mod 2462. -/
theorem roundtrip (t : ℕ) : phaseInv (phase t) = t % 2462 := by
  unfold phaseInv phase
  omega

theorem roundtrip' (p : ℕ) (hp : p < 2462) : phase (phaseInv p) = p := by
  unfold phaseInv phase
  omega

/-- Injectivity on [0, 2462). -/
theorem phase_injective_on (a b : ℕ) (ha : a < 2462) (hb : b < 2462)
    (h : phase a = phase b) : a = b := by
  have := congrArg phaseInv h
  rw [roundtrip, roundtrip, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

/-- The phase has period 2462. -/
theorem phase_period (t : ℕ) : phase (t + 2462) = phase t := by
  unfold phase
  omega

/-- Sampling collisions happen exactly when the sample indices agree mod 2462. -/
theorem collision_iff (a b : ℕ) : phase a = phase b ↔ a % 2462 = b % 2462 := by
  constructor
  · intro h
    have := congrArg phaseInv h
    rwa [roundtrip, roundtrip] at this
  · intro h
    unfold phase
    rw [Nat.mul_mod, h, ← Nat.mul_mod]

/-- Minimal winding: the curve (89 t, 2462 t) closes only when 2462 ∣ l. -/
theorem winding_closes (l : ℕ) : 2462 ∣ 89 * l ↔ 2462 ∣ l := by
  constructor
  · intro h
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 2462 89) h)
  · intro h
    exact Dvd.dvd.mul_left h 89

/-- Any 2463 samples contain a collision. -/
theorem sampling_collision (f : Fin 2463 → ℕ) :
    ∃ i j, i ≠ j ∧ phase (f i) = phase (f j) := by
  have hcard : Fintype.card (Fin 2462) < Fintype.card (Fin 2463) := by simp
  obtain ⟨i, j, hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k => (⟨phase (f k), phase_lt _⟩ : Fin 2462)) hcard
  exact ⟨i, j, hne, by simpa using h⟩

end PhaseNormalization

#print axioms PhaseNormalization.coprime_89_2462
#print axioms PhaseNormalization.roundtrip
#print axioms PhaseNormalization.roundtrip'
#print axioms PhaseNormalization.phase_injective_on
#print axioms PhaseNormalization.phase_period
#print axioms PhaseNormalization.collision_iff
#print axioms PhaseNormalization.winding_closes
#print axioms PhaseNormalization.sampling_collision
