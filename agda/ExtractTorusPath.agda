-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Extraction driver for the verified 89/2462 path.
-- Every row printed is the first projection of a VerifiedState built by
-- TorusInvariant.verifySuperposition / collapseToVerified, so each (m , l)
-- carries a checked proof of 2462 * m ≡ 89 * l at type level (erased at
-- runtime by MAlonzo).
-- Usage: extract-torus-path N   prints C rows for t = 0 .. N-1.
{-# OPTIONS --guardedness #-}
module ExtractTorusPath where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show; readMaybe)
open import Data.List using (List; []; _∷_; upTo)
open import Data.Product using (_,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String; _++_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (0ℓ)
open import Function using (case_of_)
open import IO
open import System.Environment using (getArgs)
open import System.Exit using (exitFailure)

open import TorusInvariant

row : VerifiedState → String
row (coord m l , _) = "  { " ++ show m ++ "ULL, " ++ show l ++ "ULL },"

emitAll : List VerifiedState → IO {0ℓ} (⊤ {0ℓ})
emitAll []       = pure _
emitAll (s ∷ ss) = putStrLn (row s) >> emitAll ss

emit : ℕ → IO {0ℓ} (⊤ {0ℓ})
emit n = do
  putStrLn ("#define SPME_TORUS_PATH_COUNT " ++ show n ++ "u")
  putStrLn "static const spme_knot_coord_t SPME_TORUS_PATH[SPME_TORUS_PATH_COUNT] = {"
  emitAll (verifySuperposition (upTo n))
  putStrLn "};"

usage : IO {0ℓ} (⊤ {0ℓ})
usage = putStrLn "usage: extract-torus-path N   (N a decimal natural number)" >> exitFailure

dispatch : List String → IO {0ℓ} (⊤ {0ℓ})
dispatch (a ∷ []) = case readMaybe 10 a of λ where
  (just n) → emit n
  nothing  → usage
dispatch _ = usage

main : Main
main = run (getArgs >>= dispatch)
