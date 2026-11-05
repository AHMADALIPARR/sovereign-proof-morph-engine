// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! The 89/2462 torus-knot path, loaded from the table extracted from
//! agda/TorusInvariant.agda (extract/torus_path.h) and re-validated row by
//! row before use. The table is data; the Agda certificate re-proves the
//! invariant for every coordinate a candidate uses.

use std::path::Path;

pub const MERIDIAN: u64 = 89;
pub const LONGITUDE: u64 = 2462;

#[derive(Clone, Debug)]
pub struct Torus {
    pub rows: Vec<(u64, u64)>,
    pub header_sha256: String,
}

pub fn invariant(m: u64, l: u64) -> bool {
    (LONGITUDE as u128) * (m as u128) == (MERIDIAN as u128) * (l as u128)
}

pub fn phase(t: u64) -> u64 {
    ((MERIDIAN as u128 * t as u128) % LONGITUDE as u128) as u64
}

/// Inverse of `phase` on 0..2462 (83 * 89 ≡ 1 mod 2462), as in Morph.Topology.
pub fn phase_inv(p: u64) -> u64 {
    ((83u128 * p as u128) % LONGITUDE as u128) as u64
}

impl Torus {
    pub fn load(path: &Path) -> Result<Torus, String> {
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {}", path.display(), e))?;
        let header_sha256 = crate::sha256::hex(text.as_bytes());
        let body = text
            .split_once("SPME_TORUS_PATH[SPME_TORUS_PATH_COUNT] = {")
            .ok_or("torus table not found")?
            .1;
        let body = body.split_once("};").ok_or("unterminated table")?.0;
        let mut rows = Vec::new();
        for line in body.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let inner = line
                .trim_end_matches(',')
                .trim()
                .strip_prefix('{')
                .and_then(|s| s.strip_suffix('}'))
                .ok_or_else(|| format!("bad row: {}", line))?;
            let (a, c) = inner.split_once(',').ok_or("bad row")?;
            let p = |s: &str| s.trim().trim_end_matches("ULL").parse::<u64>().map_err(|e| e.to_string());
            rows.push((p(a)?, p(c)?));
        }
        let declared: usize = text
            .lines()
            .find_map(|l| l.strip_prefix("#define SPME_TORUS_PATH_COUNT "))
            .and_then(|s| s.trim().trim_end_matches('u').parse().ok())
            .ok_or("count not declared")?;
        if rows.len() != declared {
            return Err(format!("row count {} != declared {}", rows.len(), declared));
        }
        for (t, &(m, l)) in rows.iter().enumerate() {
            let t = t as u64;
            if m != MERIDIAN * t || l != LONGITUDE * t || !invariant(m, l) {
                return Err(format!("row {} = ({}, {}) is off the 89/2462 path", t, m, l));
            }
        }
        Ok(Torus { rows, header_sha256 })
    }

    pub fn coord(&self, t: u64) -> Option<(u64, u64)> {
        self.rows.get(t as usize).copied()
    }
}
