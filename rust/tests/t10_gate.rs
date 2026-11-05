// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Group 10: the Soufflé gate accepts only a fully evidenced candidate and
//! answers SILENCE for every missing or failed premise.
mod common;
use spme::gate::{self, Facts, ProofFact, Verdict};

const OBLIGATIONS: [&str; 5] =
    ["typed_ir_preservation", "rewrite_correctness", "execution_correspondence", "knot_validity", "phase_normalization"];

fn full() -> Facts {
    let t = 5u64;
    Facts {
        candidate: "c1".into(),
        source: "src-sha".into(),
        target: "tgt-sha".into(),
        active: "src-sha".into(),
        proofs: OBLIGATIONS
            .iter()
            .map(|o| ProofFact { obligation: o.to_string(), checker: "agda-2.6.4.3".into(), outcome: "checked".into(), sha256: "h".into() })
            .collect(),
        observations: vec![("differential_samples".into(), "pass".into()), ("state_migration".into(), "pass".into())],
        topology: Some((t, 89 * t, 2462 * t, (89 * t) % 2462)),
        last_t: 4,
        policy_flags: vec!["clean".into()],
        chain_required: false,
    }
}

fn run(name: &str, f: &Facts) -> gate::GateResult {
    let d = common::scratch(&format!("gate-{}", name));
    gate::evaluate(&common::repo().join("datalog/gate.dl"), f, &d)
}

fn silent(name: &str, f: Facts, reason: &str) {
    let g = run(name, &f);
    assert_eq!(g.verdict, Verdict::Silence, "{} unexpectedly committed", name);
    assert!(g.reasons.iter().any(|r| r.contains(reason)), "{}: reasons {:?} lack {}", name, g.reasons, reason);
}

#[test]
fn g10_accepts_complete_evidence() {
    let g = run("full", &full());
    assert_eq!(g.verdict, Verdict::Commit, "{:?}\n{}", g.reasons, g.souffle);
    assert!(g.reasons.is_empty());
    assert!(g.derived.iter().any(|d| d.starts_with("semantic_preservation(c1")));
    assert!(g.derived.iter().any(|d| d.starts_with("topology_valid(c1")));
    assert!(g.derived.iter().any(|d| d.starts_with("runtime_authorized(c1")));
    // facts hash is deterministic
    assert_eq!(g.facts_sha256, run("full2", &full()).facts_sha256);
}

#[test]
fn g10_rejects_each_missing_obligation() {
    for o in OBLIGATIONS {
        let mut f = full();
        f.proofs.retain(|p| p.obligation != o);
        silent(o, f, &format!("missing:{}", o));
    }
}

#[test]
fn g10_rejects_failed_proof() {
    let mut f = full();
    f.proofs[1].outcome = "rejected".into();
    silent("failed", f, "failed:rewrite_correctness");
}

#[test]
fn g10_liquidhaskell_is_not_proof_authority() {
    let mut f = full();
    for p in f.proofs.iter_mut() {
        p.checker = "liquidhaskell-0.9.6".into();
    }
    silent("lh", f, "missing:");
}

#[test]
fn g10_topology_and_runtime_premises() {
    let mut f = full();
    f.last_t = 5; // t must strictly advance
    silent("t-not-advanced", f, "topology_invalid");
    let mut f = full();
    f.topology = Some((5, 445, 12310, 0)); // wrong normalized phase
    silent("bad-phase", f, "topology_invalid");
    let mut f = full();
    f.topology = Some((5, 446, 12310, 445)); // off the knot
    silent("off-knot", f, "topology_invalid");
    let mut f = full();
    f.topology = None;
    silent("no-topology", f, "topology_invalid");
    let mut f = full();
    f.observations.push(("native_validation".into(), "fail".into()));
    assert_eq!(run("obs-fail", &f).verdict, Verdict::Silence);
    let mut f = full();
    f.observations.retain(|(k, _)| k != "state_migration");
    assert_eq!(run("no-migration", &f).verdict, Verdict::Silence);
    let mut f = full();
    f.target = f.source.clone(); // no change is not a morph
    silent("same", f, "no_semantic_preservation");
    let mut f = full();
    f.active = "other".into(); // source must be the active version
    silent("not-active", f, "no_semantic_preservation");
    let mut f = full();
    f.chain_required = true;
    silent("chain", f, "missing:chain_composition");
}

#[test]
fn g10_synth_fails_closed() {
    for (flag, why) in [("rh_assertion", "rh_assertion"), ("contaminated", "contaminated"), ("ambiguous", "ambiguous"), ("pending", "SILENCE_PENDING")] {
        let mut f = full();
        f.policy_flags = vec![flag.into()];
        assert_eq!(run(flag, &f).verdict, Verdict::Silence, "{}", why);
    }
    let mut f = full();
    f.policy_flags.clear();
    assert_eq!(run("unclassified", &f).verdict, Verdict::Silence);
    let mut f = full();
    f.policy_flags.push("pending".into()); // clean + pending is still SILENCE
    assert_eq!(run("clean-pending", &f).verdict, Verdict::Silence);
}

#[test]
fn g10_broken_rules_fail_closed() {
    let d = common::scratch("gate-badrules");
    std::fs::write(d.join("bad.dl"), ".decl x(a: symbol)\nx(a) :- y(a).\n").unwrap();
    let g = gate::evaluate(&d.join("bad.dl"), &full(), &d.join("facts"));
    assert_eq!(g.verdict, Verdict::Silence);
}
