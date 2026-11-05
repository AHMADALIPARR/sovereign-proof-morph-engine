-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- L1: LiquidHaskell refinement contracts for the reference model of the
-- runtime's arithmetic, torus, gate and fixed-point helpers. Checked with
-- LiquidHaskell (SMT: z3). These are refinement-type obligations
-- discharged by an SMT solver; they are recorded as checks, never as
-- proof authority (only Agda and Lean results feed the gate's
-- proof_checked relation).
module Contracts where

-- ℕ subtraction in the IR is truncated (Agda `_∸_`).
{-@ type N = {v:Integer | 0 <= v} @-}

{-@ subN :: a:N -> b:N -> {v:N | (a >= b => v == a - b) && (a < b => v == 0)} @-}
subN :: Integer -> Integer -> Integer
subN a b = if a >= b then a - b else 0

{-@ addN :: a:N -> b:N -> {v:N | v == a + b} @-}
addN :: Integer -> Integer -> Integer
addN a b = a + b

-- Torus knot 89/2462: the coordinate at step t lies on the line
-- 2462·m = 89·l (the invariant re-proved per coordinate in Agda).
data Pt = Pt Integer Integer

{-@ measure ptM @-}
ptM :: Pt -> Integer
ptM (Pt m _) = m

{-@ measure ptL @-}
ptL :: Pt -> Integer
ptL (Pt _ l) = l

{-@ coord :: t:N -> {v:Pt | 2462 * ptM v == 89 * ptL v && ptM v == 89 * t} @-}
coord :: Integer -> Pt
coord t = Pt (89 * t) (2462 * t)

-- Phase normalization: always in [0, 2462).
{-@ phase :: t:N -> {v:N | v < 2462 && v == (89 * t) mod 2462} @-}
phase :: Integer -> Integer
phase t = (89 * t) `mod` 2462

-- 83 is the inverse of 89 modulo 2462 (83·89 = 7387 = 3·2462 + 1).
{-@ phaseInv :: p:{Integer | 0 <= p && p < 2462} -> {v:N | v < 2462 && v == (83 * p) mod 2462} @-}
phaseInv :: Integer -> Integer
phaseInv p = (83 * p) `mod` 2462

{-@ inverseConst :: {v:Integer | v == 1} @-}
inverseConst :: Integer
inverseConst = (83 * 89) `mod` 2462

-- Datalog gate: COMMIT iff every required relation holds; anything else
-- is SILENCE.
{-@ commit :: proof:Bool -> sem:Bool -> topo:Bool -> rt:Bool -> policy:Bool
           -> {v:Bool | v <=> (proof && sem && topo && rt && policy)} @-}
commit :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool
commit p s t r q = p && s && t && r && q

-- On SILENCE the active executable is the last accepted one.
{-@ nextActive :: c:Bool -> cand:N -> prev:N -> {v:N | (not c => v == prev) && (c => v == cand)} @-}
nextActive :: Bool -> Integer -> Integer -> Integer
nextActive c cand prev = if c then cand else prev

-- Annealer (integer energies): a non-increasing move is always accepted.
{-@ accept :: dE:Integer -> u:N -> thr:N -> {v:Bool | dE <= 0 => v} @-}
accept :: Integer -> Integer -> Integer -> Bool
accept dE u thr = dE <= 0 || u < thr

-- Discrete monotone fixed point on the finite chain [x, top]:
-- an inflationary step bounded above terminates (measure top - x) and
-- the result stays in range. No metric / Banach contraction is assumed.
{-@ lfp :: top:N -> f:(y:{Integer | 0 <= y && y <= top} -> {w:Integer | y <= w && w <= top})
        -> x:{Integer | 0 <= x && x <= top} -> {v:Integer | x <= v && v <= top} / [top - x] @-}
lfp :: Integer -> (Integer -> Integer) -> Integer -> Integer
lfp top f x = let y = f x in if y == x then x else lfp top f y

-- phaseInv undoes phase on every step: phaseInv (phase t) == t mod 2462.
{-@ roundTrip :: t:N -> {v:Bool | v} @-}
roundTrip :: Integer -> Bool
roundTrip t = phaseInv (phase t) == t `mod` 2462
