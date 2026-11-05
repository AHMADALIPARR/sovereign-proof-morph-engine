-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Demonstration that the axiom in SnapUnique.lean is inconsistent.
-- SnapUnique.lean itself does not elaborate (see docs/verification-report.md),
-- so it cannot be imported; this file states the axiom exactly as it would
-- elaborate with the section variables made explicit (abbrev TokenSpace so
-- the statement typechecks) and derives False from it with no sorry.
import Mathlib.Tactic

namespace SnapUniqueInconsistent

abbrev TokenSpace (N : ℕ) := Fin N

/-- The user's `x_graph_injective`, with its section variables
    {N} [NeZero N] (sq_dist) universally quantified as Lean does. -/
axiom x_graph_injective :
  ∀ {N : ℕ} [NeZero N] (sq_dist : TokenSpace N → ℝ), Function.Injective sq_dist

/-- Counterexample: N = 2 and the constant distance function. -/
theorem inconsistent : False := by
  have h := x_graph_injective (N := 2) (fun _ => (0 : ℝ))
  have : (0 : Fin 2) = 1 := h rfl
  exact absurd this (by decide)

end SnapUniqueInconsistent

#print axioms SnapUniqueInconsistent.inconsistent
