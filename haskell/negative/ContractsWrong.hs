-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Negative control: false contracts that LiquidHaskell must reject.
module ContractsWrong where

-- Wrong bound: phase can exceed 88.
{-@ phase :: t:{Integer | 0 <= t} -> {v:Integer | v < 89} @-}
phase :: Integer -> Integer
phase t = (89 * t) `mod` 2462

-- Wrong gate: commits without the proof relation.
{-@ commit :: proof:Bool -> sem:Bool -> {v:Bool | v => proof} @-}
commit :: Bool -> Bool -> Bool
commit _ s = s

-- Non-terminating fixed point (no inflationary bound) must fail the
-- termination check.
{-@ spin :: x:Integer -> Integer @-}
spin :: Integer -> Integer
spin x = if x == 0 then 0 else spin (x + 1)
