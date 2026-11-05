-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Checked companion of HarmonicAperiodic.lean (kept unmodified; it does not
-- build). Zero sorry, zero user axioms: φ's irrationality comes from
-- TwinAnchor_Checked (proved from Mathlib's Nat.Prime.irrational_sqrt), and
-- the cosine fact is Mathlib's Real.cos_eq_one_iff.
-- Scope: the real-valued projection n ↦ cos(c·n·φ·π) has no nonzero integer
-- period. This says nothing about the snapped (finite-vocabulary) token trace.
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TwinAnchor_Checked

namespace HarmonicAperiodic_Checked

open ConsciousOmega_Checked (phi phi_irr)

/-- The map from the user's file: n ↦ cos(n·φ·π). -/
noncomputable def harmonic_map (n : ℤ) : ℝ := Real.cos ((n : ℝ) * phi * Real.pi)

/-- The map the BQN kernels evaluate: n ↦ cos(n·φ·π / 2462). -/
noncomputable def bqn_harmonic_map (n : ℤ) : ℝ := Real.cos ((n : ℝ) * phi * Real.pi / 2462)

/-- Core lemma: if cos(p·φ·π / d) = 1 with p ≠ 0 and d ≠ 0 integers, φ is rational. -/
theorem phi_rational_of_cos_one (p d : ℤ) (hp : p ≠ 0) (hd : d ≠ 0)
    (h : Real.cos ((p : ℝ) * phi * Real.pi / d) = 1) : False := by
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp h
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hphi : phi = ((2 * k * d / p : ℚ) : ℝ) := by
    push_cast
    field_simp at hk ⊢
    linear_combination -hk
  exact phi_irr ⟨_, hphi.symm⟩

theorem harmonic_never_loops (p : ℤ)
    (h_period : ∀ n : ℤ, harmonic_map (n + p) = harmonic_map n) : p = 0 := by
  by_contra hp
  have h1 : harmonic_map p = 1 := by
    have := h_period 0
    simpa [harmonic_map] using this
  exact phi_rational_of_cos_one p 1 hp one_ne_zero (by simpa [harmonic_map] using h1)

theorem bqn_harmonic_never_loops (p : ℤ)
    (h_period : ∀ n : ℤ, bqn_harmonic_map (n + p) = bqn_harmonic_map n) : p = 0 := by
  by_contra hp
  have h1 : bqn_harmonic_map p = 1 := by
    have := h_period 0
    simpa [bqn_harmonic_map] using this
  exact phi_rational_of_cos_one p 2462 hp (by norm_num) (by simpa [bqn_harmonic_map] using h1)

end HarmonicAperiodic_Checked

#print axioms HarmonicAperiodic_Checked.harmonic_never_loops
#print axioms HarmonicAperiodic_Checked.bqn_harmonic_never_loops
