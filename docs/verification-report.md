<!-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 -->
<!-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab -->
# Verification report

Every checker line below is copied from `docs/measurements/lean.txt` and
`docs/measurements/agda.txt`, which are the outputs of `scripts/check_lean.sh`
and `scripts/check_agda.sh`. Toolchain: Lean 4.35.0 with the Mathlib pinned in
`lean/lake-manifest.json`, Agda 2.6.4.3 with standard library 2.1,
Soufflé 2.5, LiquidHaskell 0.9.6.3.1 (GHC 9.6.3 plugin), GHC 9.6.6 and rustc 1.85.1.

The originals are kept byte for byte apart from the licence header. Each fix is
in a `_Checked` file next to the original.

## Lean

| file | exit | result (exact checker lines) |
|---|---|---|
| [SnapUnique.lean](../lean/SnapUnique.lean) | 1 | `13:80: error: unexpected token 'variable'; expected 'lemma'`; `17:77` same; `29:26`, `18:20`, `35:24`, `35:56`, `35:36`, `47:2`, `47:48`, `47:36`, `47:16`: `don't know how to synthesize implicit argument`; `89:5: error: unknown tactic` |
| [SnapUnique_Checked.lean](../lean/SnapUnique_Checked.lean) | 0 | `exists_min_dist`, `snap_unique`, `snap_kernel_unique`, `midpoint_tie`: `[propext, Classical.choice, Quot.sound]` |
| [SnapUnique_Inconsistent.lean](../lean/SnapUnique_Inconsistent.lean) | 0 | `inconsistent` (a proof of `False`) depends on `[propext, Classical.choice, Quot.sound, SnapUniqueInconsistent.x_graph_injective]`: the original's axiom is contradictory |
| [SnapUniqueFixed.lean](../lean/SnapUniqueFixed.lean) | 1 | `3:0: error: object file '…/Mathlib/Order/Bounds.olean' of module Mathlib.Order.Bounds does not exist` (this Mathlib has `Mathlib.Order.Bounds.Defs`) |
| [SnapUniqueFixed_Inconsistent.lean](../lean/SnapUniqueFixed_Inconsistent.lean) | 0 | `inconsistent` depends on `[propext, Classical.choice, Quot.sound, SnapUniqueFixedInconsistent.exists_min_dist]`: the axiom `exists_min_dist` is contradictory at N = 0 |
| [HarmonicAperiodic.lean](../lean/HarmonicAperiodic.lean) | 1 | `3:0: error: object file '…/Mathlib/Data/Real/Irrational.olean' of module Mathlib.Data.Real.Irrational does not exist` (moved to `Mathlib.NumberTheory.Real.Irrational`); the file also contains 2 `sorry` and 2 `axiom` |
| [HarmonicAperiodic_Checked.lean](../lean/HarmonicAperiodic_Checked.lean) | 0 | `harmonic_never_loops`, `bqn_harmonic_never_loops`: `[propext, Classical.choice, Quot.sound]` |
| [TwinAnchor.lean](../lean/TwinAnchor.lean) | 1 | `3:0: error: object file '…/Mathlib/Data/Real/Irrational.olean' … does not exist` |
| [TwinAnchor_Checked.lean](../lean/TwinAnchor_Checked.lean) | 0 | `sqrt_five_irr`, `antipode_anchor_is_irrational`: `[propext, Classical.choice, Quot.sound]` |
| [SovereignSuperposition.lean](../lean/SovereignSuperposition.lean) | 1 | `41:2: error: Tactic 'split' failed: Could not split an 'if' or 'match' expression in the goal`; `86:6: error: omega could not prove the goal` (counterexample `89*a - 2462*b ≥ 1`) |
| [SovereignSuperposition_Checked.lean](../lean/SovereignSuperposition_Checked.lean) | 0 | `alsc_fp16_safe`, `extract_verified_agent`: `[propext, Quot.sound]` (printed by `Audit.lean`) |
| [XREX_ALSC.lean](../lean/XREX_ALSC.lean) | 1 | `20:2: error: unexpected token 'variable'; expected 'lemma'`; `47:2: error: Tactic 'split' failed` |
| [XREX_ALSC_Checked.lean](../lean/XREX_ALSC_Checked.lean) | 0 | `toNat_add_le`: `[propext]`; `alsc_fp16_safe`: `[propext, Quot.sound]` (printed by `Audit.lean`) |
| [XGraph.lean](../lean/XGraph.lean) | 0 | `eventually_periodic`, `period_multiple`, `midpoint_tie`: `[propext, Classical.choice, Quot.sound]`; `merge`: `[propext]` |
| [PhaseNormalization.lean](../lean/PhaseNormalization.lean) | 0 | 8 theorems; `coprime_89_2462`, `winding_closes`, `sampling_collision`: `[propext, Classical.choice, Quot.sound]`; `roundtrip`, `roundtrip'`, `phase_injective_on`, `phase_period`, `collision_iff`: `[propext, Quot.sound]` |
| [Audit.lean](../lean/Audit.lean) | 0 | `#print axioms` for the two ALSC files |
| [EngineAArith.lean](../lean/EngineAArith.lean) | 0 | Engine A input (see below) |
| [EngineAUnsupported.lean](../lean/EngineAUnsupported.lean) | 0 | Engine A negative input (see below) |

No `_Checked` file and no new file contains `sorry` or a user `axiom`. The
only axioms reported are Lean's three standard ones.

## Agda

| file | postulates | exit | result |
|---|---|---|---|
| [CompleteCoherence.agda](../agda/CompleteCoherence.agda) | 0 | 42 | `CompleteCoherence.agda:15,13: Parse error` at ` ℕ}` |
| [CompleteCoherence_Checked.agda](../agda/CompleteCoherence_Checked.agda) | 0 | 0 | checked |
| [ExperientialFunctor.agda](../agda/ExperientialFunctor.agda) | 2 | 42 | `79,7-26: The following names are declared but not accompanied by a definition: postulate-coherence`; `87,7-37: PhysicalFlow.Δt p-flow + 88 * PhysicalFlow.Δt p-flow != PhysicalFlow.Δt p-flow * 89 of type ℕ` |
| [ExperientialFunctor_Checked.agda](../agda/ExperientialFunctor_Checked.agda) | 0 | 0 | checked |
| [Main.agda](../agda/Main.agda) | 1 | 42 | fails on its import: `CompleteCoherence.agda:15,13: Parse error` |
| [Main_Checked.agda](../agda/Main_Checked.agda) | 0 | 0 | checked; compiled to `snap-omega-engine` |
| [TorusInvariant.agda](../agda/TorusInvariant.agda) | 0 | 0 | checked |
| [ExtractTorusPath.agda](../agda/ExtractTorusPath.agda) | 0 | 0 | checked; MAlonzo driver for `extract/torus_path.h` |
| [PhiHarmonics.agda](../agda/PhiHarmonics.agda) | 0 | 0 | checked, `--safe` |
| [Morph/IR.agda](../agda/Morph/IR.agda), [Rewrite](../agda/Morph/Rewrite.agda), [Subst](../agda/Morph/Subst.agda), [Topology](../agda/Morph/Topology.agda), [TorusBridge](../agda/Morph/TorusBridge.agda) | 0 | 0 | checked; certificate library |

The postulate column is `grep -c '^ *postulate'`: lines that start with the word,
including identifiers such as `postulate-coherence`. Files with `--safe` cannot contain a postulate.

Options: `--safe` in CompleteCoherence_Checked, ExperientialFunctor_Checked, PhiHarmonics, Morph/IR, Morph/Rewrite, Morph/Subst and Morph/Topology. The MAlonzo entry points ExtractTorusPath and Main_Checked use `--guardedness` for IO. TorusInvariant and Morph/TorusBridge have no pragma and no postulates.

## LiquidHaskell (L1, recorded, never proof authority)

| file | result |
|---|---|
| [haskell/Contracts.hs](../haskell/Contracts.hs) | SAFE |
| [haskell/negative/ContractsWrong.hs](../haskell/negative/ContractsWrong.hs) | UNSAFE, error lines 10, 15, 21 |

The gate only counts proof results whose checker starts with `agda-` or
`lean-`. A LiquidHaskell result submitted as a proof gives SILENCE
(test `g10_liquidhaskell_is_not_proof_authority`).

## Engine A (Lean statement → IR → Agda certificate)

`spme engine-a lean/EngineAArith.lean` (Lean exit 0):

| theorem | status | Lean/IR agreement | LiquidHaskell |
|---|---|---|---|
| scale_id | PROVED (Agda) | 4/4 | SAFE |
| poly_eq | PROVED (Agda) | 4/4 | SAFE |
| twice_id | PROVED (Agda) | 4/4 | SAFE |
| pick_id | UNPROVED: `Engine B normal forms differ after 4 rounds: lhs (if (fst #0) (snd #0) (snd #0)) vs rhs (snd #0)` | 4/4 | SAFE |
| mix_eq | PROVED (Agda) | 4/4 | SAFE |
| lit_arith | PROVED (Agda) | 1/1 | SAFE |

`lean/EngineAUnsupported.lean`, all REJECTED:

| decl | reason |
|---|---|
| half | `line 9: division / has no IR operator` |
| fact | `line 11: function types / implications → are not in the subset (first-order ∀ binders only)` |
| exists_succ | `line 15: existential quantifier ∃ …` |
| and_stmt | `line 17: conjunction ∧ …` |
| compose | `line 20: function types …` |

## Gate (L3) and order of checks

[datalog/gate.dl](../datalog/gate.dl) commits a candidate only when all of these hold:

- the five obligations `typed_ir_preservation`, `rewrite_correctness`,
  `execution_correspondence`, `knot_validity` and `phase_normalization` each
  have a passing `agda-*` or `lean-*` proof result with the matching hash;
- `topology_valid`: t > last_t, m = 89t, l = 2462t, phase = 89t mod 2462;
- `runtime_authorized`: `differential_samples = pass`, `state_migration = pass`, no `fail`;
- the SYNTH flag is `clean` and nothing else (`rh_assertion`, `contaminated`,
  `ambiguous`, `pending` → SILENCE; `pending` maps to ADR-062 `SILENCE_PENDING`;
  no flag at all is `unclassified` → SILENCE);
- `chain_composition` is present when the source is itself a morph output.

ADR-055 is a fact in the gate: RH = `OPEN_CRUX`. Nothing in this repository proves it.

The controller order is LOAD → GENERATE → EXPLORE torus → ENERGY → SELECT →
OBLIGATIONS → CHECK → DATALOG → COMPILE → VALIDATE → ATOMIC ACTIVATE →
EXECUTE/MEASURE → LEDGER. Native validation runs after the gate as a second,
independent check; a failure there, or after activation, re-activates the
previous version and is written to the ledger.

Contractivity is a discrete monotone fixed point: when the annealer finds no
lower energy the target equals the source, the torus coordinate does not
advance (t = last_t), and the gate returns SILENCE. The demo reaches that
point at generation 2 (`docs/measurements/demo.txt`).

## Trusted computing base

- Lean 4 kernel + Mathlib, the Agda type checker (`--safe`) and its standard library.
- Soufflé, for evaluating the gate rules.
- rustc, which compiles the engine and every native candidate.
- GHC, for MAlonzo output (`torus_path.h`, `snap-omega-engine`) and the reference model.
- The Rust certificate emitter is **not** trusted: Agda re-checks each certificate,
  and `spme replay --recheck` re-checks every stored certificate from the ledger.
- The ledger is a SHA-256 hash chain plus a head file. It detects edits,
  reordering, truncation and torn writes (test `g13`), but whoever can rewrite
  the whole file and the head can rebuild a consistent chain. Anchor the head
  hash outside the box for stronger guarantees.

## Substrate files named in the spec that are not in this repository

- `lean-substrate/src/Substrate.lean`
- `packages/lh-theorems/src/Veneer/Contractivity.hs`
- `packages/datalog`
- `packages/probe-gate`

The layers that would use them are implemented here from scratch:
[lean/](../lean), [haskell/](../haskell), [datalog/gate.dl](../datalog/gate.dl)
and [rust/src/gate.rs](../rust/src/gate.rs).
