-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Definitional agreement between Morph.Topology and the verbatim
-- TorusInvariant module (which has no --safe pragma, hence this separate,
-- non-safe bridge; it contains no postulates).
module Morph.TorusBridge where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import TorusInvariant as TI
import Morph.Topology as T

invariant-agrees : ∀ m l → T.Invariant (T.coord m l) ≡ TI.Invariant (TI.coord m l)
invariant-agrees m l = refl

project-agrees-m : ∀ t → T.KnotCoord.m (T.project t) ≡ TI.KnotCoord.m (TI.project t)
project-agrees-m t = refl

project-agrees-l : ∀ t → T.KnotCoord.l (T.project t) ≡ TI.KnotCoord.l (TI.project t)
project-agrees-l t = refl
