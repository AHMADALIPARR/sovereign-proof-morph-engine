-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- SnapUniqueFixed.lean does not elaborate (missing module Mathlib.Order.Bounds;
-- and `def TokenSpace := Fin N` leaves N uninferable), so it cannot be imported.
-- This file uses the same section variables, with TokenSpace taking N
-- explicitly so the axiom elaborates. `#check` shows Lean drops the unused
-- `[NeZero N]` instance, so the axiom is stated for N = 0, where Fin 0 is
-- empty: it is inconsistent.
import Mathlib.Tactic

namespace SnapUniqueFixedInconsistent

variable {N : ℕ} [NeZero N]
abbrev TokenSpace (N : ℕ) := Fin N
variable (sq_dist : TokenSpace N → ℝ)

axiom exists_min_dist :
  ∃ min_tok : TokenSpace N, ∀ tok : TokenSpace N, sq_dist min_tok ≤ sq_dist tok

#check @exists_min_dist

theorem inconsistent : False := by
  obtain ⟨t, -⟩ := exists_min_dist (N := 0) (fun _ => (0 : ℝ))
  exact Fin.elim0 t

end SnapUniqueFixedInconsistent

#print axioms SnapUniqueFixedInconsistent.inconsistent
