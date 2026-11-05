// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! L3 gate driver: writes the evidence facts, runs Soufflé on
//! datalog/gate.dl and reads the verdict. Any failure to run the gate, any
//! malformed output, or anything other than exactly one COMMIT row for the
//! candidate is SILENCE (fail closed).

use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Debug, Default)]
pub struct ProofFact {
    pub obligation: String,
    pub checker: String,
    pub outcome: String,
    pub sha256: String,
}

#[derive(Clone, Debug, Default)]
pub struct Facts {
    pub candidate: String,
    pub source: String,
    pub target: String,
    pub active: String,
    pub proofs: Vec<ProofFact>,
    pub observations: Vec<(String, String)>,
    pub topology: Option<(u64, u64, u64, u64)>,
    pub last_t: u64,
    pub policy_flags: Vec<String>,
    pub chain_required: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Verdict {
    Commit,
    Silence,
}

#[derive(Clone, Debug)]
pub struct GateResult {
    pub verdict: Verdict,
    pub reasons: Vec<String>,
    pub derived: Vec<String>,
    pub facts_sha256: String,
    pub souffle: String,
}

fn clean(s: &str) -> String {
    s.chars().map(|c| if c == '\t' || c == '\n' || c == '\r' { ' ' } else { c }).collect()
}

pub fn souffle_version() -> Option<String> {
    let o = Command::new("souffle").arg("--version").output().ok()?;
    String::from_utf8_lossy(&o.stdout).lines().find(|l| l.starts_with("Version")).map(|l| l.trim().to_string())
}

pub fn write_facts(f: &Facts, dir: &Path) -> std::io::Result<String> {
    std::fs::create_dir_all(dir)?;
    let c = clean(&f.candidate);
    let mut files: Vec<(&str, String)> = vec![
        ("candidate", format!("{}\n", c)),
        ("source_artifact", format!("{}\t{}\n", c, clean(&f.source))),
        ("target_artifact", format!("{}\t{}\n", c, clean(&f.target))),
        ("active", format!("{}\n", clean(&f.active))),
        ("last_t", format!("{}\n", f.last_t)),
    ];
    let mut pr = String::new();
    for p in &f.proofs {
        pr.push_str(&format!("{}\t{}\t{}\t{}\t{}\n", c, clean(&p.obligation), clean(&p.checker), clean(&p.outcome), clean(&p.sha256)));
    }
    files.push(("proof_result", pr));
    let mut ob = String::new();
    for (k, o) in &f.observations {
        ob.push_str(&format!("{}\t{}\t{}\n", c, clean(k), clean(o)));
    }
    files.push(("observation", ob));
    files.push((
        "topology",
        match f.topology {
            Some((t, m, l, p)) => format!("{}\t{}\t{}\t{}\t{}\n", c, t, m, l, p),
            None => String::new(),
        },
    ));
    files.push(("policy_flag", f.policy_flags.iter().map(|x| format!("{}\t{}\n", c, clean(x))).collect()));
    files.push(("chain_required", if f.chain_required { format!("{}\n", c) } else { String::new() }));
    let mut all = String::new();
    for (name, body) in &files {
        std::fs::write(dir.join(format!("{}.facts", name)), body)?;
        all.push_str(name);
        all.push('\n');
        all.push_str(body);
    }
    Ok(crate::sha256::hex(all.as_bytes()))
}

pub fn evaluate(rules: &Path, f: &Facts, dir: &Path) -> GateResult {
    let silence = |why: String, sha: String| GateResult {
        verdict: Verdict::Silence,
        reasons: vec![why],
        derived: vec![],
        facts_sha256: sha,
        souffle: String::new(),
    };
    let sha = match write_facts(f, dir) {
        Ok(s) => s,
        Err(e) => return silence(format!("gate: cannot write facts: {}", e), String::new()),
    };
    let out: PathBuf = dir.join("out");
    let _ = std::fs::create_dir_all(&out);
    let r = Command::new("souffle").arg("-F").arg(dir).arg("-D").arg(&out).arg(rules).output();
    let o = match r {
        Ok(o) => o,
        Err(e) => return silence(format!("gate: souffle not runnable: {}", e), sha),
    };
    let log = format!("{}{}", String::from_utf8_lossy(&o.stdout), String::from_utf8_lossy(&o.stderr));
    if !o.status.success() {
        let mut g = silence(format!("gate: souffle failed: {}", log.trim()), sha);
        g.souffle = log;
        return g;
    }
    let read = |n: &str| std::fs::read_to_string(out.join(format!("{}.csv", n))).unwrap_or_default();
    let verdicts: Vec<String> = read("policy_verdict").lines().map(String::from).collect();
    let reasons: Vec<String> = read("silence_reason")
        .lines()
        .filter_map(|l| l.split_once('\t').map(|(_, r)| r.to_string()))
        .collect();
    let mut derived = Vec::new();
    for n in ["proof_checked", "semantic_preservation", "topology_valid", "runtime_authorized"] {
        for l in read(n).lines() {
            derived.push(format!("{}({})", n, l.replace('\t', ", ")));
        }
    }
    let c = clean(&f.candidate);
    let commit = verdicts.len() == 1 && verdicts[0] == format!("{}\tCOMMIT", c) && reasons.is_empty();
    GateResult {
        verdict: if commit { Verdict::Commit } else { Verdict::Silence },
        reasons: if commit || !reasons.is_empty() { reasons } else { vec![format!("gate output not a single COMMIT: {:?}", verdicts)] },
        derived,
        facts_sha256: sha,
        souffle: log,
    }
}
