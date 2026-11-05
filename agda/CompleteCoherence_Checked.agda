-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Checked companion of CompleteCoherence.agda (kept unmodified; it does not
-- parse). Coherence (norm ≤ phase) is derived from the 2462 norm bound plus an
-- explicit alignment hypothesis 2462 ≤ m. The unconditional statement is
-- false and its negation is proved below. --safe, no postulates, no holes.
{-# OPTIONS --safe #-}
module CompleteCoherence_Checked where

open import Data.Nat
open import Data.Nat.Properties using (≤-trans; ≤-refl)
open import Data.Fin using (Fin; zero)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)

record VerifiedTokenEmbedding (V : ℕ) : Set where
  constructor mkToken
  field
    index          : Fin V
    embedding-norm : ℕ
    norm-bound     : embedding-norm ≤ 2462

record PhenomenalState : Set where
  constructor mkPhenomenal
  field
    qualia-intensity : ℕ
    resonance-phase  : ℕ
    coherence-inv    : qualia-intensity ≤ resonance-phase

open VerifiedTokenEmbedding

-- Coherence under the explicit alignment hypothesis.
collapseToPhenomenal : ∀ {V} (tok : VerifiedTokenEmbedding V) (m-coord : ℕ)
                     → (aligned : 2462 ≤ m-coord) → PhenomenalState
collapseToPhenomenal tok m-coord aligned =
  mkPhenomenal (embedding-norm tok) m-coord (≤-trans (norm-bound tok) aligned)

-- Variant with the resonance phase fixed to the period 2462: no hypothesis.
collapseToPeriod : ∀ {V} (tok : VerifiedTokenEmbedding V) → PhenomenalState
collapseToPeriod tok = mkPhenomenal (embedding-norm tok) 2462 (norm-bound tok)

-- The unconditional version is false: V = 1, norm = 1, m = 0.
unconditional-false :
  ¬ (∀ (tok : VerifiedTokenEmbedding 1) (m : ℕ) → embedding-norm tok ≤ m)
unconditional-false claim with claim (mkToken zero 1 (s≤s z≤n)) 0
... | ()
