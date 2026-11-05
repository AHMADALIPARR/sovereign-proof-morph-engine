// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! L7 transactional runtime: an immutable version store, atomic activation
//! by symlink replacement (rename(2) of a fresh link over `active`),
//! rollback to the previous version, state snapshots, and the
//! state-migration check required for hot-swapping stateful programs.
//!
//! Layout under the runtime directory:
//!   versions/vNNNN/{program.ir, program.rs, program, manifest.json}
//!   active -> versions/vNNNN
//!   state/NNNNNN.val, state/current -> NNNNNN.val   (stateful programs)
//! Versions are written once, then made read-only; activation never edits a
//! version or the active executable in place.

use crate::ir::*;
use crate::json::Json;
use std::path::{Path, PathBuf};

pub struct Runtime {
    pub dir: PathBuf,
}

#[derive(Debug, Clone)]
pub struct Version {
    pub id: u64,
    pub dir: PathBuf,
    pub ir_sha256: String,
    pub binary_sha256: String,
}

fn vname(id: u64) -> String {
    format!("v{:04}", id)
}

fn set_readonly(p: &Path) {
    if let Ok(m) = std::fs::metadata(p) {
        let mut perm = m.permissions();
        perm.set_readonly(true);
        let _ = std::fs::set_permissions(p, perm);
    }
}

/// Atomically point `link` at `target`: create a temporary symlink and
/// rename it over the old one (rename is atomic on POSIX filesystems).
pub fn atomic_symlink(target: &Path, link: &Path) -> Result<(), String> {
    let tmp = link.with_extension("swap");
    let _ = std::fs::remove_file(&tmp);
    std::os::unix::fs::symlink(target, &tmp).map_err(|e| format!("symlink: {}", e))?;
    std::fs::rename(&tmp, link).map_err(|e| format!("rename: {}", e))
}

impl Runtime {
    pub fn new(dir: &Path) -> Runtime {
        Runtime { dir: dir.to_path_buf() }
    }

    pub fn versions(&self) -> PathBuf {
        self.dir.join("versions")
    }

    pub fn next_id(&self) -> u64 {
        std::fs::read_dir(self.versions())
            .map(|rd| {
                rd.filter_map(|e| e.ok())
                    .filter_map(|e| e.file_name().to_str().and_then(|s| s.strip_prefix('v')).and_then(|s| s.parse::<u64>().ok()))
                    .max()
                    .map(|m| m + 1)
                    .unwrap_or(0)
            })
            .unwrap_or(0)
    }

    /// Write a new immutable version from a program and its built binary.
    pub fn stage(&self, p: &Prog, built: &crate::native::Built, meta: Json) -> Result<Version, String> {
        let id = self.next_id();
        let dir = self.versions().join(vname(id));
        if dir.exists() {
            return Err(format!("version {} already exists", id));
        }
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        let ir = p.canonical();
        std::fs::write(dir.join("program.ir"), &ir).map_err(|e| e.to_string())?;
        std::fs::copy(&built.source, dir.join("program.rs")).map_err(|e| e.to_string())?;
        std::fs::copy(&built.binary, dir.join("program")).map_err(|e| e.to_string())?;
        let bin_sha = crate::sha256::file_hex(&dir.join("program")).map_err(|e| e.to_string())?;
        if bin_sha != built.binary_sha256 {
            return Err("binary changed while staging".into());
        }
        let manifest = Json::obj()
            .with("version", id)
            .with("ir_sha256", p.hash())
            .with("binary_sha256", bin_sha.as_str())
            .with("source_sha256", built.source_sha256.as_str())
            .with("meta", meta);
        std::fs::write(dir.join("manifest.json"), manifest.dump() + "\n").map_err(|e| e.to_string())?;
        for f in ["program.ir", "program.rs", "program", "manifest.json"] {
            set_readonly(&dir.join(f));
        }
        Ok(Version { id, dir, ir_sha256: p.hash(), binary_sha256: bin_sha })
    }

    pub fn active_link(&self) -> PathBuf {
        self.dir.join("active")
    }

    pub fn active(&self) -> Option<Version> {
        let target = std::fs::read_link(self.active_link()).ok()?;
        let dir = if target.is_absolute() { target } else { self.dir.join(target) };
        let id = dir.file_name()?.to_str()?.strip_prefix('v')?.parse().ok()?;
        let m = Json::parse(&std::fs::read_to_string(dir.join("manifest.json")).ok()?).ok()?;
        Some(Version {
            id,
            ir_sha256: m.get("ir_sha256")?.str()?.to_string(),
            binary_sha256: m.get("binary_sha256")?.str()?.to_string(),
            dir,
        })
    }

    /// Load the active program and check it against its manifest hashes.
    pub fn load_active(&self) -> Result<(Version, Prog), String> {
        let v = self.active().ok_or("no active version")?;
        let p = crate::parse::parse_canonical(&std::fs::read_to_string(v.dir.join("program.ir")).map_err(|e| e.to_string())?)?;
        crate::typecheck::check_prog(&p)?;
        if p.hash() != v.ir_sha256 {
            return Err("active IR does not match its manifest hash".into());
        }
        let b = crate::sha256::file_hex(&v.dir.join("program")).map_err(|e| e.to_string())?;
        if b != v.binary_sha256 {
            return Err("active binary does not match its manifest hash".into());
        }
        Ok((v, p))
    }

    pub fn activate(&self, v: &Version) -> Result<(), String> {
        atomic_symlink(Path::new(&format!("versions/{}", vname(v.id))), &self.active_link())
    }

    /// Re-activate a previous version (rollback). The rolled-back-from
    /// version stays in the store for audit.
    pub fn rollback_to(&self, v: &Version) -> Result<(), String> {
        self.activate(v)
    }

    pub fn state_dir(&self) -> PathBuf {
        self.dir.join("state")
    }

    pub fn snapshot_state(&self, s: &Val) -> Result<PathBuf, String> {
        let d = self.state_dir();
        std::fs::create_dir_all(&d).map_err(|e| e.to_string())?;
        let n = std::fs::read_dir(&d).map(|r| r.count()).unwrap_or(0);
        let f = d.join(format!("{:06}.val", n));
        std::fs::write(&f, s.to_string()).map_err(|e| e.to_string())?;
        set_readonly(&f);
        atomic_symlink(Path::new(f.file_name().unwrap()), &d.join("current"))?;
        Ok(f)
    }

    pub fn current_state(&self) -> Option<Val> {
        let t = std::fs::read_to_string(self.state_dir().join("current")).ok()?;
        crate::parse::parse_val_str(t.trim()).ok()
    }
}

/// State type of a stateful program: main : σ ⊗ a → σ ⊗ b.
pub fn state_type(p: &Prog) -> Option<Ty> {
    let m = p.main();
    match (&m.arg, &m.ret) {
        (Ty::Prod(s1, _), Ty::Prod(s2, _)) if s1 == s2 => Some((**s1).clone()),
        _ => None,
    }
}

/// Migration relation for hot swap. For stateless programs none is needed.
/// For stateful programs the only migration this runtime accepts is the
/// identity on an unchanged state type: then `tgt ≈ src` (proved for every
/// input, including every state component) is exactly the obligation that
/// the new version behaves as the old one from every reachable state. A
/// changed state type would need an explicit migration function with its own
/// proof; none is supported, so that is rejected.
pub fn migration(old: &Prog, new: &Prog, stateful: bool) -> Result<&'static str, String> {
    if old.main().arg != new.main().arg || old.main().ret != new.main().ret {
        return Err(format!(
            "main type changed from {} -> {} to {} -> {}: no checked migration relation",
            old.main().arg,
            old.main().ret,
            new.main().arg,
            new.main().ret
        ));
    }
    if !stateful {
        return Ok("none_required");
    }
    match (state_type(old), state_type(new)) {
        (Some(a), Some(b)) if a == b => Ok("identity_on_unchanged_state_type"),
        (a, b) => Err(format!("state type {:?} -> {:?}: no checked migration relation", a, b)),
    }
}
