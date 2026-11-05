// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Differential check against the Haskell reference model
//! (`haskell/Ref.hs`, built to `haskell/build/ref`).
//!
//! The reference evaluates with unbounded integers. Inputs on which the Rust
//! interpreter traps on 64-bit overflow are counted separately and excluded
//! from the comparison; every other input must produce the identical printed
//! value. This is testing evidence, not proof authority.
use crate::eval;
use crate::ir::{Prog, Val};
use std::path::Path;
use std::process::Command;

#[derive(Debug, Clone, PartialEq)]
pub struct RefReport {
    pub inputs: usize,
    pub agree: usize,
    pub rust_overflow: usize,
    pub disagreements: Vec<String>,
}

pub fn check(ref_bin: &Path, p: &Prog, inputs: &[Val]) -> Result<RefReport, String> {
    let dir = std::env::temp_dir().join(format!("spme-ref-{}-{}", std::process::id(), p.hash()));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let pf = dir.join("program.ir");
    let inf = dir.join("inputs.txt");
    std::fs::write(&pf, p.canonical()).map_err(|e| e.to_string())?;
    let txt: String = inputs.iter().map(|v| format!("{}\n", v)).collect();
    std::fs::write(&inf, txt).map_err(|e| e.to_string())?;
    let out = Command::new(ref_bin).arg(&pf).arg(&inf).output().map_err(|e| format!("{}: {}", ref_bin.display(), e))?;
    let _ = std::fs::remove_dir_all(&dir);
    if !out.status.success() {
        return Err(format!("reference model failed: {}", String::from_utf8_lossy(&out.stderr).trim()));
    }
    let lines: Vec<String> = String::from_utf8_lossy(&out.stdout).lines().map(String::from).collect();
    if lines.len() != inputs.len() {
        return Err(format!("reference model printed {} results for {} inputs", lines.len(), inputs.len()));
    }
    let mut r = RefReport { inputs: inputs.len(), agree: 0, rust_overflow: 0, disagreements: vec![] };
    for (v, h) in inputs.iter().zip(lines) {
        match eval::run_main(p, v.clone()) {
            Ok(x) if x.to_string() == h => r.agree += 1,
            Ok(x) => r.disagreements.push(format!("input {}: rust {} vs haskell {}", v, x, h)),
            Err(eval::EvalError::Overflow(_)) => r.rust_overflow += 1,
            Err(e) => r.disagreements.push(format!("input {}: rust error {:?} vs haskell {}", v, e, h)),
        }
    }
    Ok(r)
}
