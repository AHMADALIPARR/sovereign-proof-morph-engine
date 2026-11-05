<!-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 -->
<!-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab -->
# Architecture: L0–L9 mapped to files

| layer | role | files |
|---|---|---|
| L0 Lean 4 | formal substrate, theorem authority | [lean/](../lean): `PhaseNormalization`, `XGraph`, the `_Checked` files, `Audit`; Engine A inputs `EngineAArith` and `EngineAUnsupported` |
| L1 LiquidHaskell | refinement contracts (recorded, never Lean authority) | [haskell/Contracts.hs](../haskell/Contracts.hs), [haskell/negative/ContractsWrong.hs](../haskell/negative/ContractsWrong.hs), [rust/src/liquid.rs](../rust/src/liquid.rs) |
| L2 Agda | dependent proofs, morph certificates | [agda/Morph/](../agda/Morph) (IR, Subst, Rewrite, Topology, TorusBridge), [agda/TorusInvariant.agda](../agda/TorusInvariant.agda), [agda/PhiHarmonics.agda](../agda/PhiHarmonics.agda), [rust/src/agda.rs](../rust/src/agda.rs), [rust/src/engine_a.rs](../rust/src/engine_a.rs) |
| L3 Datalog | evidence and policy gate | [datalog/gate.dl](../datalog/gate.dl), [rust/src/gate.rs](../rust/src/gate.rs) |
| L4 Morph Core | typed IR, rewrite, execution | [rust/src/ir.rs](../rust/src/ir.rs), [parse.rs](../rust/src/parse.rs), [typecheck.rs](../rust/src/typecheck.rs), [rewrite.rs](../rust/src/rewrite.rs), [eval.rs](../rust/src/eval.rs), [vm.rs](../rust/src/vm.rs), [sexp.rs](../rust/src/sexp.rs) |
| L5 Torus Engine | 89/2462 topological search | [rust/src/torus.rs](../rust/src/torus.rs), [extract/torus_path.h](../extract/torus_path.h), [agda/ExtractTorusPath.agda](../agda/ExtractTorusPath.agda) |
| L6 Annealer | temperature, entropy, selection | [rust/src/anneal.rs](../rust/src/anneal.rs), [rust/src/energy.rs](../rust/src/energy.rs) (ALSC from `XREX_ALSC_Checked.lean`, cap 4) |
| L7 Runtime | compile, execute, measure | [rust/src/native.rs](../rust/src/native.rs), [rust/src/runtime.rs](../rust/src/runtime.rs), [rust/src/refmodel.rs](../rust/src/refmodel.rs), [haskell/Ref.hs](../haskell/Ref.hs) |
| L8 WORM ledger | certificates, provenance, history | [rust/src/ledger.rs](../rust/src/ledger.rs), [rust/src/sha256.rs](../rust/src/sha256.rs), [rust/src/json.rs](../rust/src/json.rs) |
| L9 Controller | lifecycle, scheduling, orchestration | [rust/src/controller.rs](../rust/src/controller.rs), [rust/src/main.rs](../rust/src/main.rs) (`spme`) |

Side pipeline: the X-graph and BQN replay. BQN is never proof authority.

- [bqn/](../bqn) holds the four originals, which are kept unchanged.
- [bqn/checked/](../bqn/checked) holds the runnable versions; [docs/bqn-checked.md](bqn-checked.md) lists the changes.
- [bqn/checked/gen_inputs.bqn](../bqn/checked/gen_inputs.bqn) generates the inputs with the same 89t law. They are not read from `torus_path.h`; that file is checked by Rust `t01` and `spme torus`.
- [scripts/bqn_avx512.sh](../scripts/bqn_avx512.sh) compares the base and AVX-512 CBQN interpreters ([bqn-avx512.md](bqn-avx512.md)). The `.bqn` scripts are interpreted; they are not compiled to machine code.

Runtime layout on disk: `WORK/runtime/versions/vNNNN/` (manifest, IR, native
binary), the `WORK/runtime/active` symlink, and `WORK/ledger.jsonl` with its head file.
