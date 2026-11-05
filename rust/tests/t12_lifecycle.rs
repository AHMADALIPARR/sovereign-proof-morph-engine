// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Groups 12, 13, 14 and the invalid-migration negative: the full
//! controller lifecycle with fault injection, rollback, ledger tamper
//! detection, recursive chain preservation and audited replay.
mod common;
use spme::controller::{self, Config, Fault};
use spme::json::Json;
use spme::ledger::Ledger;
use spme::parse;
use spme::runtime;

fn cfg(work: &std::path::Path, fault: Fault) -> Config {
    let mut c = Config::new(&common::repo(), work);
    c.bench_calls = 10_000;
    c.bench_reps = 1;
    c.iterations = 200;
    c.fault = fault;
    c
}

fn active_id(c: &Config) -> u64 {
    c.runtime().active().unwrap().id
}

#[test]
fn g13_ledger_unit_tamper_and_truncation() {
    let d = common::scratch("ledger");
    let l = Ledger::open(&d.join("l.jsonl"));
    for k in 0..4u64 {
        l.append(Json::obj().with("k", k).with("decision", "COMMIT")).unwrap();
    }
    let recs = l.verify().unwrap();
    assert_eq!(recs.len(), 4);
    let text = std::fs::read_to_string(&l.path).unwrap();
    // edit a body field
    std::fs::write(&l.path, text.replacen("\"k\":2", "\"k\":7", 1)).unwrap();
    let e = l.verify().unwrap_err();
    assert!(e.contains("record 2") && e.contains("hash mismatch"), "{}", e);
    assert!(l.append(Json::obj().with("k", 9u64)).is_err(), "append onto a tampered chain");
    // drop the last record: the head file catches truncation
    let lines: Vec<&str> = text.lines().collect();
    std::fs::write(&l.path, lines[..3].join("\n") + "\n").unwrap();
    assert!(l.verify().unwrap_err().contains("head file"));
    // reorder two records
    let mut sw = lines.clone();
    sw.swap(1, 2);
    std::fs::write(&l.path, sw.join("\n") + "\n").unwrap();
    assert!(l.verify().is_err());
    // torn write
    std::fs::write(&l.path, text.trim_end()).unwrap();
    assert!(l.verify().unwrap_err().contains("torn"));
    std::fs::write(&l.path, &text).unwrap();
    assert_eq!(l.verify().unwrap().len(), 4);
}

#[test]
fn negative_invalid_migrations() {
    let a = parse::parse_surface("(def main (x int) int x)").unwrap();
    let b = parse::parse_surface("(def main (x int) (* int int) (pair x x))").unwrap();
    assert!(runtime::migration(&a, &b, false).unwrap_err().contains("main type changed"));
    assert_eq!(runtime::migration(&a, &a, false).unwrap(), "none_required");
    // stateful: σ ⊗ a → σ ⊗ b with unchanged σ is the identity migration
    let s = parse::parse_surface("(def main (p (* nat int)) (* nat int) (pair (fst p) (add (snd p) (int 1))))").unwrap();
    assert_eq!(runtime::migration(&s, &s, true).unwrap(), "identity_on_unchanged_state_type");
    // a stateful program whose type is not σ ⊗ a → σ ⊗ b has no migration
    assert!(runtime::migration(&a, &a, true).is_err());
}

#[test]
fn g12_g14_lifecycle_faults_rollback_chain_replay_tamper() {
    let work = common::scratch("lifecycle");
    let src = std::fs::read_to_string(common::repo().join("examples/gen0.morph")).unwrap();
    let c0 = cfg(&work, Fault::None);
    let o = controller::load(&c0, &src).unwrap();
    assert!(o.committed);
    assert!(controller::load(&c0, &src).unwrap_err().contains("already initialised"));
    let v0 = active_id(&c0);
    let bin0 = std::fs::read(c0.runtime().active_link().join("program")).unwrap();

    // every fault ends in SILENCE / rollback with the active version kept
    for (f, why) in [
        (Fault::TamperCertificate, "SILENCE"),
        (Fault::WrongNative, "native validation failed"),
        (Fault::FailAfterActivate, "rolled back"),
        (Fault::ChangeStateType, "SILENCE"),
    ] {
        let o = controller::generation(&cfg(&work, f.clone())).unwrap();
        println!("{:?}: committed={} reason={}", f, o.committed, o.reason);
        assert!(!o.committed, "{:?} committed", f);
        assert!(o.reason.contains(why), "{:?}: {}", f, o.reason);
        assert_eq!(active_id(&c0), v0, "{:?} changed the active version", f);
        assert_eq!(std::fs::read(c0.runtime().active_link().join("program")).unwrap(), bin0);
        if f == Fault::FailAfterActivate {
            assert!(o.body.get("rollback").is_some());
        }
        assert_ne!(o.body.get("decision").and_then(|x| x.str()), Some("COMMIT"));
    }

    // a clean generation commits and changes the active version
    let o1 = controller::generation(&c0).unwrap();
    println!("gen clean 1: committed={} reason={}", o1.committed, o1.reason);
    assert!(o1.committed, "{}", o1.reason);
    let v1 = active_id(&c0);
    assert_ne!(v1, v0);
    // behaviour preserved end to end: the new active program agrees with the root
    let root = controller::root_program(&c0.runtime()).unwrap();
    let (_, now) = c0.runtime().load_active().unwrap();
    for x in -30i64..=30 {
        let x = spme::ir::Val::Int(x);
        assert_eq!(spme::eval::run_main(&root, x.clone()), spme::eval::run_main(&now, x));
    }

    // a second generation either commits with a chain certificate back to the
    // root, or is SILENCE (no further improvement); either way the chain of
    // committed versions stays anchored at version 0
    let o2 = controller::generation(&c0).unwrap();
    println!("gen clean 2: committed={} reason={}", o2.committed, o2.reason);
    if o2.committed {
        let chain = o2.body.get("checker").and_then(|c| c.get("chain"));
        assert!(chain.is_some(), "second commit has no chain certificate");
        assert_eq!(chain.unwrap().get("ok").and_then(|x| x.boolean()), Some(true));
    } else {
        assert_eq!(active_id(&c0), v1);
    }

    // replay with Agda re-checking every certificate in a fresh directory
    let rep = controller::replay(&c0, true);
    for l in &rep.lines {
        println!("{}", l);
    }
    assert!(rep.failures.is_empty(), "{:?}", rep.failures);
    assert_eq!(rep.records, c0.ledger().verify().unwrap().len());

    // tamper with a committed record: verify, replay and the next generation all refuse
    let lp = work.join("ledger.jsonl");
    let text = std::fs::read_to_string(&lp).unwrap();
    let forged = text.replacen("\"decision\":\"REJECT\"", "\"decision\":\"COMMIT\"", 1);
    assert_ne!(forged, text);
    std::fs::write(&lp, forged).unwrap();
    assert!(c0.ledger().verify().is_err());
    assert!(!controller::replay(&c0, false).failures.is_empty());
    assert!(controller::generation(&c0).unwrap_err().contains("ledger verification failed"));
    std::fs::write(&lp, &text).unwrap();
    assert!(c0.ledger().verify().is_ok());

    // tamper with a certificate file: replay detects the hash change
    let cert = std::fs::read_dir(c0.certs()).unwrap().filter_map(|e| e.ok()).map(|e| e.path())
        .find(|p| p.extension().map(|x| x == "agda").unwrap_or(false) && !p.to_string_lossy().contains("Load")).unwrap();
    let ct = std::fs::read_to_string(&cert).unwrap();
    std::fs::write(&cert, ct.clone() + "\n-- edited\n").unwrap();
    let rep = controller::replay(&c0, false);
    assert!(rep.failures.iter().any(|f| f.contains("hash")), "{:?}", rep.failures);
    std::fs::write(&cert, ct).unwrap();
}
