-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
/-
Negative input for Engine A: valid Lean that lies outside the translated
subset. Engine A must reject each declaration with an explicit reason.
-/
namespace EngineAUnsupported

def half (x : Nat) : Nat := x / 2

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem exists_succ : ∃ n : Nat, n + 1 = 2 := ⟨1, rfl⟩

theorem and_stmt : ∀ (x : Nat), x + 0 = x ∧ 0 + x = x := by
  intro x; omega

def compose (f : Nat → Nat) (x : Nat) : Nat := f (f x)

end EngineAUnsupported
