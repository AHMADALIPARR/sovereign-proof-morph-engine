-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
/-
Engine A input. Lean subset: first-order, non-recursive definitions over
Nat, Int and Bool, and theorems of the form `∀ binders, lhs = rhs`.
Lean checks every proof here; Engine A translates the definitions and the
propositions to the typed IR and re-proves them in Agda.
-/
namespace EngineA

def scale (x : Int) : Int := x * 1 + 0

def poly (x : Int) : Int := (x + 0) * 1 + 2 * 3

def twice (x : Nat) : Nat := let y := x * 1; y + 0 + (3 - 3)

def pick (b : Bool) (x : Nat) : Nat := if b && true then x * 1 else x + 0

def mix (x : Nat) (y : Int) : Int := (y * 1 + 0) + ((x : Int) * 0)

theorem scale_id : ∀ (x : Int), scale x = x := by
  intro x; simp [scale]

theorem poly_eq : ∀ (x : Int), poly x = x + 6 := by
  intro x; simp [poly]

theorem twice_id : ∀ (x : Nat), twice x = x := by
  intro x; simp [twice]

theorem pick_id : ∀ (b : Bool) (x : Nat), pick b x = x := by
  intro b x; cases b <;> simp [pick]

theorem mix_eq : ∀ (x : Nat) (y : Int), mix x y = y := by
  intro x y; simp [mix]

theorem lit_arith : (2 : Nat) * 3 + 4 = 10 := by decide

end EngineA
