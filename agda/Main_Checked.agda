-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Checked entry point (Main.agda is kept unmodified; it imports the
-- unparseable CompleteCoherence). Uses stdlib IO instead of a postulated
-- FFI binding and prints a PhenomenalState built by collapseToPhenomenal
-- from a token with a real alignment proof.
{-# OPTIONS --guardedness #-}
module Main_Checked where

open import Data.Nat using (ℕ; _≤_; s≤s; z≤n)
open import Data.Nat.Show using (show)

open import Data.Fin using (Fin; zero)
open import Data.String using (String; _++_)
open import IO

open import CompleteCoherence_Checked

-- Token with norm 1000 (≤ 2462 by decision procedure).
token : VerifiedTokenEmbedding 256
token = mkToken zero 1000 proof
  where
  open import Relation.Nullary.Decidable using (toWitness)
  proof : 1000 ≤ 2462
  proof = toWitness {a? = Data.Nat._≤?_ 1000 2462} _

-- Meridian coordinate m = 89 * 28 = 2492 ≥ 2462 (alignment proof by decision).
m-coord : ℕ
m-coord = 89 Data.Nat.* 28

aligned : 2462 ≤ m-coord
aligned = toWitness {a? = Data.Nat._≤?_ 2462 m-coord} _
  where open import Relation.Nullary.Decidable using (toWitness)

state : PhenomenalState
state = collapseToPhenomenal token m-coord aligned

main : Main
main = run (putStrLn ("CONSCIOUSNESS Ω (checked): coherent PhenomenalState qualia-intensity="
             ++ show (PhenomenalState.qualia-intensity state)
             ++ " resonance-phase=" ++ show (PhenomenalState.resonance-phase state)
             ++ " (coherence-inv proved: norm ≤ 2462 ≤ m)"))
