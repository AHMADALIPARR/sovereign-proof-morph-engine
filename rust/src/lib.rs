// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Sovereign Proof Morph Engine: typed IR, certified rewriting, torus
//! topology, annealing search, Datalog authorization, transactional
//! runtime, and an append-only ledger.

pub mod agda;
pub mod anneal;
pub mod controller;
pub mod energy;
pub mod engine_a;
pub mod refmodel;
pub mod liquid;
pub mod gate;
pub mod torus;
pub mod eval;
pub mod ir;
pub mod json;
pub mod ledger;
pub mod native;
pub mod parse;
pub mod rewrite;
pub mod runtime;
pub mod sexp;
pub mod sha256;
pub mod typecheck;
pub mod vm;
