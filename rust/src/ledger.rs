// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! L8 evidence ledger: a hash-linked, append-only JSON-lines log.
//!
//! Record k is `{"seq":k,"prev":H(k-1),"body":{...},"hash":H(k)}` with
//! `H(k) = sha256(H(k-1) ‖ "\n" ‖ k ‖ "\n" ‖ canonical(body))` and
//! `H(-1) = 64 zeros`. Appends use O_APPEND and fsync; the head hash is
//! also written to `<ledger>.head` so truncation of the log is detected as
//! long as the head file is intact. A hash chain detects modification; it
//! does not make storage physically immutable (see docs/ledger.md).

use crate::json::Json;
use crate::sha256;
use std::io::Write;
use std::path::{Path, PathBuf};

pub const GENESIS: &str = "0000000000000000000000000000000000000000000000000000000000000000";

pub fn link_hash(prev: &str, seq: u64, body: &Json) -> String {
    sha256::hex(format!("{}\n{}\n{}", prev, seq, body.dump()).as_bytes())
}

pub struct Ledger {
    pub path: PathBuf,
}

#[derive(Debug, Clone)]
pub struct Record {
    pub seq: u64,
    pub prev: String,
    pub body: Json,
    pub hash: String,
}

fn head_path(p: &Path) -> PathBuf {
    let mut s = p.as_os_str().to_owned();
    s.push(".head");
    PathBuf::from(s)
}

impl Ledger {
    pub fn open(path: &Path) -> Ledger {
        Ledger { path: path.to_path_buf() }
    }

    /// Read and verify the whole chain. Err names the first broken record.
    pub fn verify(&self) -> Result<Vec<Record>, String> {
        let text = match std::fs::read_to_string(&self.path) {
            Ok(t) => t,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
            Err(e) => return Err(format!("ledger unreadable: {}", e)),
        };
        if !text.is_empty() && !text.ends_with('\n') {
            return Err("ledger: last record is not newline-terminated (torn write)".into());
        }
        let mut prev = GENESIS.to_string();
        let mut out = Vec::new();
        for (k, line) in text.lines().enumerate() {
            let j = Json::parse(line).map_err(|e| format!("record {}: unparsable: {}", k, e))?;
            let seq = j.get("seq").and_then(Json::u64).ok_or(format!("record {}: no seq", k))?;
            let p = j.get("prev").and_then(Json::str).ok_or(format!("record {}: no prev", k))?;
            let h = j.get("hash").and_then(Json::str).ok_or(format!("record {}: no hash", k))?;
            let body = j.get("body").cloned().ok_or(format!("record {}: no body", k))?;
            if seq != k as u64 {
                return Err(format!("record {}: sequence number {} out of order", k, seq));
            }
            if p != prev {
                return Err(format!("record {}: prev link {} does not match {}", k, p, prev));
            }
            let want = link_hash(&prev, seq, &body);
            if want != h {
                return Err(format!("record {}: hash mismatch (stored {}, recomputed {})", k, h, want));
            }
            prev = h.to_string();
            out.push(Record { seq, prev: p.to_string(), body, hash: h.to_string() });
        }
        match std::fs::read_to_string(head_path(&self.path)) {
            Ok(head) => {
                if head.trim() != prev {
                    return Err(format!("head file {} does not match chain tip {} (truncation or rewrite)", head.trim(), prev));
                }
            }
            Err(_) if out.is_empty() => {}
            Err(e) => return Err(format!("head file unreadable: {}", e)),
        }
        Ok(out)
    }

    /// Verify, then append one record. Returns its hash.
    pub fn append(&self, body: Json) -> Result<Record, String> {
        let recs = self.verify()?;
        let (seq, prev) = match recs.last() {
            Some(r) => (r.seq + 1, r.hash.clone()),
            None => (0, GENESIS.to_string()),
        };
        let hash = link_hash(&prev, seq, &body);
        let line = Json::obj()
            .with("seq", seq)
            .with("prev", prev.as_str())
            .with("body", body.clone())
            .with("hash", hash.as_str())
            .dump();
        if let Some(d) = self.path.parent() {
            std::fs::create_dir_all(d).map_err(|e| e.to_string())?;
        }
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)
            .map_err(|e| format!("ledger open: {}", e))?;
        f.write_all(format!("{}\n", line).as_bytes()).map_err(|e| e.to_string())?;
        f.sync_all().map_err(|e| e.to_string())?;
        let hp = head_path(&self.path);
        let tmp = hp.with_extension("head.tmp");
        std::fs::write(&tmp, format!("{}\n", hash)).map_err(|e| e.to_string())?;
        std::fs::rename(&tmp, &hp).map_err(|e| e.to_string())?;
        Ok(Record { seq, prev, body, hash })
    }
}
