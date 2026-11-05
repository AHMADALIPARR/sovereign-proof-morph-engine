-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Torus topology used by the morph engine: knot coordinates (89t, 2462t)
-- (re-exported from TorusInvariant), the phase map t ↦ 89·t mod 2462, its
-- bound, and its injectivity on one period via the inverse 83
-- (89 · 83 = 3 · 2462 + 1).
{-# OPTIONS --safe #-}
module Morph.Topology where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties using (*-assoc; *-comm)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Same definitions as TorusInvariant.agda (that module is kept verbatim and
-- is not --safe only because it lacks the pragma); Morph/TorusBridge.agda
-- checks that the two agree definitionally.
record KnotCoord : Set where
  constructor coord
  field
    m : ℕ
    l : ℕ

Invariant : KnotCoord → Set
Invariant (coord m l) = 2462 * m ≡ 89 * l

project : ℕ → KnotCoord
project t = coord (89 * t) (2462 * t)

phase : ℕ → ℕ
phase t = (89 * t) % 2462

phase< : ∀ t → phase t < 2462
phase< t = m%n<n (89 * t) 2462

phase⁻¹ : ℕ → ℕ
phase⁻¹ p = (83 * p) % 2462

private
  mul-mod : ∀ a x d .{{_ : NonZero d}} → (a * (x % d)) % d ≡ (a * x) % d
  mul-mod a x d = begin
    (a * (x % d)) % d               ≡⟨ %-distribˡ-* a (x % d) d ⟩
    ((a % d) * (x % d % d)) % d     ≡⟨ cong (λ y → ((a % d) * y) % d) (m%n%n≡m%n x d) ⟩
    ((a % d) * (x % d)) % d         ≡⟨ sym (%-distribˡ-* a x d) ⟩
    (a * x) % d                     ∎

  unit : ∀ t → 83 * (89 * t) ≡ t + (3 * t) * 2462
  unit = solve-∀

phase-inverse : ∀ t → t < 2462 → phase⁻¹ (phase t) ≡ t
phase-inverse t t<n = begin
  (83 * ((89 * t) % 2462)) % 2462   ≡⟨ mul-mod 83 (89 * t) 2462 ⟩
  (83 * (89 * t)) % 2462            ≡⟨ cong (_% 2462) (unit t) ⟩
  (t + (3 * t) * 2462) % 2462       ≡⟨ [m+kn]%n≡m%n t (3 * t) 2462 ⟩
  t % 2462                          ≡⟨ m<n⇒m%n≡m t<n ⟩
  t                                 ∎

phase-injective : ∀ {t₁ t₂} → t₁ < 2462 → t₂ < 2462 → phase t₁ ≡ phase t₂ → t₁ ≡ t₂
phase-injective {t₁} {t₂} h₁ h₂ eq = begin
  t₁                 ≡⟨ sym (phase-inverse t₁ h₁) ⟩
  phase⁻¹ (phase t₁) ≡⟨ cong phase⁻¹ eq ⟩
  phase⁻¹ (phase t₂) ≡⟨ phase-inverse t₂ h₂ ⟩
  t₂                 ∎

-- The coordinates of every projected step satisfy the knot invariant.
knot-valid : ∀ t → Invariant (project t)
knot-valid t = begin
  2462 * (89 * t)   ≡⟨ sym (*-assoc 2462 89 t) ⟩
  (2462 * 89) * t   ≡⟨ cong (_* t) (*-comm 2462 89) ⟩
  (89 * 2462) * t   ≡⟨ *-assoc 89 2462 t ⟩
  89 * (2462 * t)   ∎
