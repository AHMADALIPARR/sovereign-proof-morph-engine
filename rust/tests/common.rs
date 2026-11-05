// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Shared helpers for the integration tests.
#![allow(dead_code)]
use std::path::PathBuf;

pub fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// Fresh scratch directory under the system temp dir.
pub fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("spme-test-{}-{}", name, std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

pub fn gen0() -> spme::ir::Prog {
    let t = std::fs::read_to_string(repo().join("examples/gen0.morph")).unwrap();
    spme::parse::parse_surface(&t).unwrap()
}
