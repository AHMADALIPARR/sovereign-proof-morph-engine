-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Discrete facts behind the φ-harmonic replay (bqn/checked/lib.bqn).
-- --safe, no postulates. The real-valued cosine is not modelled; what is
-- proved is the integer structure the harmonic scalars are sampled on:
--   * the sampled phase 89·t mod 2462 has period 2462 and inverse 83,
--   * the antipode p ↦ p + 1231 mod 2462 is an involution,
--   * 89 is the Fibonacci number F₁₁ and Cassini's identity holds for
--     every n (the Fibonacci ratios that converge to φ).
{-# OPTIONS --safe #-}
module PhiHarmonics where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Nat.Tactic.RingSolver using (solve-∀)

-- Phase sampling ------------------------------------------------------------

phase : ℕ → ℕ
phase t = (89 * t) % 2462

phaseInv : ℕ → ℕ
phaseInv p = (83 * p) % 2462

phase-lt : ∀ t → phase t < 2462
phase-lt t = m%n<n (89 * t) 2462

phase-period : ∀ t → phase (t + 2462) ≡ phase t
phase-period t = begin
  (89 * (t + 2462)) % 2462        ≡⟨ cong (_% 2462) (*-distribˡ-+ 89 t 2462) ⟩
  (89 * t + 89 * 2462) % 2462     ≡⟨ [m+kn]%n≡m%n (89 * t) 89 2462 ⟩
  (89 * t) % 2462                 ∎

private
  inv-expand : ∀ t → 83 * (89 * t) ≡ t + (3 * t) * 2462
  inv-expand = solve-∀

roundtrip : ∀ t → phaseInv (phase t) ≡ t % 2462
roundtrip t = begin
  (83 * ((89 * t) % 2462)) % 2462                    ≡⟨ sym (%-distribˡ-* 83 (89 * t) 2462) ⟩
  (83 * (89 * t)) % 2462                        ≡⟨ cong (_% 2462) (inv-expand t) ⟩
  (t + (3 * t) * 2462) % 2462                   ≡⟨ [m+kn]%n≡m%n t (3 * t) 2462 ⟩
  t % 2462                                      ∎

-- The antipode ----------------------------------------------------------------

antipode : ℕ → ℕ
antipode p = (p + 1231) % 2462

antipode-involutive : ∀ p → p < 2462 → antipode (antipode p) ≡ p
antipode-involutive p p<L = begin
  ((p + 1231) % 2462 + 1231) % 2462                   ≡⟨ %-distribˡ-+ ((p + 1231) % 2462) 1231 2462 ⟩
  ((p + 1231) % 2462 % 2462 + 1231 % 2462) % 2462     ≡⟨ cong (λ x → (x + 1231 % 2462) % 2462) (m%n%n≡m%n (p + 1231) 2462) ⟩
  ((p + 1231) % 2462 + 1231 % 2462) % 2462            ≡⟨ sym (%-distribˡ-+ (p + 1231) 1231 2462) ⟩
  (p + 1231 + 1231) % 2462                            ≡⟨ cong (_% 2462) (+-assoc p 1231 1231) ⟩
  (p + 2462) % 2462                                   ≡⟨ [m+n]%n≡m%n p 2462 ⟩
  p % 2462                                            ≡⟨ m<n⇒m%n≡m p<L ⟩
  p                                                   ∎

antipode-of-origin : antipode 0 ≡ 1231
antipode-of-origin = refl

antipode-half-turn : 1231 + 1231 ≡ 2462
antipode-half-turn = refl

-- Fibonacci and Cassini ---------------------------------------------------------

fib : ℕ → ℕ
fib zero          = 0
fib (suc zero)    = 1
fib (suc (suc n)) = fib (suc n) + fib n

fib-11 : fib 11 ≡ 89
fib-11 = refl

fib-12 : fib 12 ≡ 144
fib-12 = refl

private
  split-l : ∀ a b → ((b + a) + b) * b ≡ (b + a) * b + b * b
  split-l = solve-∀
  join-l : ∀ a b → (b + a) * b + ((b + a) * a + 1) ≡ (b + a) * (b + a) + 1
  join-l = solve-∀
  split-r : ∀ a b → ((b + a) + b) * b + 1 ≡ (b + a) * b + (b * b + 1)
  split-r = solve-∀
  join-r : ∀ a b → (b + a) * b + (b + a) * a ≡ (b + a) * (b + a)
  join-r = solve-∀

-- Cassini, F(n+2)·F(n) − F(n+1)² = (−1)^(n+1), stated over ℕ as a disjunction.
Cassini : ℕ → Set
Cassini n = (fib (2 + n) * fib n + 1 ≡ fib (1 + n) * fib (1 + n))
          ⊎ (fib (2 + n) * fib n ≡ fib (1 + n) * fib (1 + n) + 1)

cassini : ∀ n → Cassini n
cassini zero = inj₁ refl
cassini (suc n) with cassini n
... | inj₁ h = inj₂ (begin
      ((b + a) + b) * b                    ≡⟨ split-l a b ⟩
      (b + a) * b + b * b                  ≡⟨ cong ((b + a) * b +_) (sym h) ⟩
      (b + a) * b + ((b + a) * a + 1)      ≡⟨ join-l a b ⟩
      (b + a) * (b + a) + 1                ∎)
  where a = fib n ; b = fib (suc n)
... | inj₂ h = inj₁ (begin
      ((b + a) + b) * b + 1                ≡⟨ split-r a b ⟩
      (b + a) * b + (b * b + 1)            ≡⟨ cong ((b + a) * b +_) (sym h) ⟩
      (b + a) * b + (b + a) * a            ≡⟨ join-r a b ⟩
      (b + a) * (b + a)                    ∎)
  where a = fib n ; b = fib (suc n)

-- At n = 10: 144·55 + 1 = 89².
cassini-89 : fib 12 * fib 10 + 1 ≡ 89 * 89
cassini-89 = refl
