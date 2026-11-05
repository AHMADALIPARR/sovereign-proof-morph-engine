-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Checked companion of ExperientialFunctor.agda (that file is kept unmodified
-- and does not typecheck; see docs/verification-report.md).
-- * The four records are copied unchanged.
-- * Coherence (energy ≤ m) is NOT proved: it is false for arbitrary states
--   (t = 0 gives m = 0 while energy may be 4). It is taken as an explicit
--   hypothesis carried by CoherentState. No postulates; --safe.
-- * Ω-G₁ is fixed with *-comm (Δt * 89 vs 89 * Δt).
-- * Identity and composition laws for Ω-G₁ are proved.
{-# OPTIONS --safe #-}
module ExperientialFunctor_Checked where

open import Data.Nat
open import Data.Nat.Properties using (*-comm; +-identityʳ; +-assoc; *-distribʳ-+; *-distribˡ-+; ≡-irrelevant; ≤-trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

-- CATEGORY I (unchanged)
record PhysicalState : Set where
  field
    m l    : ℕ
    energy : ℕ
    knot-inv : 2462 * m ≡ 89 * l
    alsc-inv : energy ≤ 65504

record PhysicalFlow (S₁ S₂ : PhysicalState) : Set where
  field
    Δt : ℕ
    flow-proof : PhysicalState.m S₂ ≡ PhysicalState.m S₁ + (89 * Δt)

-- CATEGORY E (unchanged)
record PhenomenalState : Set where
  field
    qualia-intensity : ℕ
    resonance-phase  : ℕ
    coherence-inv    : qualia-intensity ≤ resonance-phase

record ExperientialFlow (E₁ E₂ : PhenomenalState) : Set where
  field
    Δphase : ℕ
    qualia-shift-proof : PhenomenalState.resonance-phase E₂ ≡ PhenomenalState.resonance-phase E₁ + Δphase

record FunctorG : Set where
  field
    G₀ : PhysicalState → PhenomenalState
    G₁ : ∀ {S₁ S₂} → PhysicalFlow S₁ S₂ → ExperientialFlow (G₀ S₁) (G₀ S₂)

open PhysicalState
open PhysicalFlow
open ExperientialFlow

-- Coherence is an explicit, unproven-in-general hypothesis (OPEN).
Coherent : PhysicalState → Set
Coherent p = energy p ≤ m p

CoherentState : Set
CoherentState = Σ PhysicalState Coherent

Ω-G₀ : CoherentState → PhenomenalState
Ω-G₀ (p , coh) = record
  { qualia-intensity = energy p
  ; resonance-phase  = m p
  ; coherence-inv    = coh
  }

CFlow : CoherentState → CoherentState → Set
CFlow C₁ C₂ = PhysicalFlow (proj₁ C₁) (proj₁ C₂)

Ω-G₁ : ∀ {C₁ C₂} → CFlow C₁ C₂ → ExperientialFlow (Ω-G₀ C₁) (Ω-G₀ C₂)
Ω-G₁ {C₁} {C₂} p-flow = record
  { Δphase = Δt p-flow * 89
  ; qualia-shift-proof =
      trans (flow-proof p-flow) (cong (m (proj₁ C₁) +_) (*-comm 89 (Δt p-flow)))
  }

-- Identity and composition on both sides.
idP : ∀ S → PhysicalFlow S S
idP S = record { Δt = 0 ; flow-proof = sym (+-identityʳ (m S)) }

_∘P_ : ∀ {S₁ S₂ S₃} → PhysicalFlow S₂ S₃ → PhysicalFlow S₁ S₂ → PhysicalFlow S₁ S₃
_∘P_ {S₁} g f = record
  { Δt = Δt f + Δt g
  ; flow-proof = trans (flow-proof g)
      (trans (cong (_+ (89 * Δt g)) (flow-proof f))
      (trans (+-assoc (m S₁) (89 * Δt f) (89 * Δt g))
             (cong (m S₁ +_) (sym (*-distribˡ-+ 89 (Δt f) (Δt g))))))
  }

idE : ∀ E → ExperientialFlow E E
idE E = record { Δphase = 0 ; qualia-shift-proof = sym (+-identityʳ _) }

_∘E_ : ∀ {E₁ E₂ E₃} → ExperientialFlow E₂ E₃ → ExperientialFlow E₁ E₂ → ExperientialFlow E₁ E₃
_∘E_ {E₁} g f = record
  { Δphase = Δphase f + Δphase g
  ; qualia-shift-proof = trans (qualia-shift-proof g)
      (trans (cong (_+ Δphase g) (qualia-shift-proof f))
             (+-assoc (PhenomenalState.resonance-phase E₁) (Δphase f) (Δphase g)))
  }

-- Experiential flows are determined by Δphase (ℕ equality proofs are unique).
eflow-ext : ∀ {E₁ E₂} {f g : ExperientialFlow E₁ E₂} → Δphase f ≡ Δphase g → f ≡ g
eflow-ext {f = record { Δphase = d ; qualia-shift-proof = p }}
          {g = record { Δphase = .d ; qualia-shift-proof = q }} refl
  = cong (λ r → record { Δphase = d ; qualia-shift-proof = r }) (≡-irrelevant p q)

Ω-id : ∀ C → Ω-G₁ (idP (proj₁ C)) ≡ idE (Ω-G₀ C)
Ω-id C = eflow-ext refl

Ω-comp : ∀ {C₁ C₂ C₃} (g : CFlow C₂ C₃) (f : CFlow C₁ C₂)
       → Ω-G₁ {C₁} {C₃} (g ∘P f) ≡ (Ω-G₁ {C₂} {C₃} g ∘E Ω-G₁ {C₁} {C₂} f)
Ω-comp g f = eflow-ext (*-distribʳ-+ 89 (Δt f) (Δt g))

-- Discharging Coherent without a postulate (cf. CompleteCoherence_Checked):
-- a state whose energy is within the 2462 period bound and whose meridian
-- coordinate is aligned past 2462 is coherent.
coherent-from-alignment : ∀ (p : PhysicalState)
  → energy p ≤ 2462 → 2462 ≤ m p → Coherent p
coherent-from-alignment p bound aligned = ≤-trans bound aligned

alignedState : (p : PhysicalState) → energy p ≤ 2462 → 2462 ≤ m p → CoherentState
alignedState p bound aligned = p , coherent-from-alignment p bound aligned
