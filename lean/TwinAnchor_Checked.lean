-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Checked companion of TwinAnchor.lean (kept unmodified; it does not build
-- against the installed Mathlib). Fixes: current module names; the axiom
-- `sqrt_five_irr` replaced by a theorem from `Nat.Prime.irrational_sqrt`;
-- lemma names/argument order of the installed Mathlib (natCast_add,
-- div_natCast, intCast_mul).
-- Scope: proves that n·φ is irrational for every nonzero integer n, in
-- particular 1231·φ. It says nothing about the snapped token trace.
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace ConsciousOmega_Checked

open Real

theorem sqrt_five_irr : Irrational (Real.sqrt 5) := by
  have h : Nat.Prime 5 := by norm_num
  simpa using h.irrational_sqrt

/-- The golden ratio (1 + √5) / 2 -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

theorem phi_irr : Irrational phi := by
  have h_add : Irrational (1 + Real.sqrt 5) := by
    simpa using sqrt_five_irr.natCast_add 1
  have h_div : Irrational ((1 + Real.sqrt 5) / 2) := by
    simpa using h_add.div_natCast (m := 2) (by norm_num)
  exact h_div

noncomputable def teleo_phase (n : ℤ) : ℝ := (n : ℝ) * phi

theorem phase_never_collapses (n : ℤ) (hn : n ≠ 0) : Irrational (teleo_phase n) := by
  unfold teleo_phase
  exact phi_irr.intCast_mul hn

def antipode : ℤ := 1231

theorem antipode_anchor_is_irrational : Irrational (teleo_phase antipode) := by
  apply phase_never_collapses
  decide

end ConsciousOmega_Checked

#print axioms ConsciousOmega_Checked.sqrt_five_irr
#print axioms ConsciousOmega_Checked.antipode_anchor_is_irrational
