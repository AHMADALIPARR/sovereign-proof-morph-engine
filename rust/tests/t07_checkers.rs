// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Groups 7, 8, 9, 11: Lean checking (Engine A), Agda checking, LiquidHaskell
//! refinement checking, invalid-certificate rejection; negatives for
//! malformed proofs and unsupported translations.
mod common;
use spme::agda;
use spme::anneal;
use spme::engine_a::{self, Status};
use spme::liquid;
use spme::rewrite;

fn safe(module: &str, body: &str) -> String {
    format!("{{-# OPTIONS --safe #-}}\nmodule {} where\nopen import Relation.Binary.PropositionalEquality\nopen import Data.Nat\n{}\n", module, body)
}

#[test]
fn g07_lean_engine_a_proves_supported_theorems() {
    let d = common::scratch("engine-a-arith");
    let r = engine_a::translate_file(&common::repo().join("lean/EngineAArith.lean"), &d, &common::repo().join("agda"), true).unwrap();
    assert_eq!(r.lean_exit, Some(0), "{}", r.lean_output);
    let thms: Vec<_> = r.decls.iter().filter(|x| x.kind == "theorem").collect();
    assert!(!thms.is_empty());
    for t in &thms {
        println!("{} {:?}", t.name, t.status);
        if let Status::Proved = t.status {
            assert!(t.samples.iter().all(|s| s.agree), "{}: Lean/IR sample disagreement", t.name);
        }
    }
    assert_eq!(thms.iter().filter(|t| matches!(t.status, Status::Proved)).count(), 5);
    let pick = thms.iter().find(|t| t.name == "pick_id").unwrap();
    assert!(matches!(pick.status, Status::Unproved(_)), "pick_id must stay unclaimed");
}

#[test]
fn g07_negative_lean_rejects_wrong_and_sorry() {
    let d = common::scratch("lean-neg");
    // a false theorem: Lean itself rejects the file, so Engine A refuses it
    std::fs::write(d.join("Wrong.lean"), "theorem bad : (2 : Nat) + 2 = 5 := by decide\n").unwrap();
    let e = match engine_a::translate_file(&d.join("Wrong.lean"), &d.join("out"), &common::repo().join("agda"), false) {
        Ok(_) => panic!("false Lean theorem accepted"),
        Err(e) => e,
    };
    assert!(e.contains("Lean rejected"), "{}", e);
    // sorry: Lean accepts with a warning, but Engine A rejects the declaration
    let decls = engine_a::translate_source("theorem s : ∀ (x : Nat), x + 0 = x := by sorry\n").unwrap();
    assert!(decls.iter().all(|x| matches!(x.status, Status::Rejected(_))), "{:?}", decls.iter().map(|x| &x.status).collect::<Vec<_>>());
    let decls = engine_a::translate_source("axiom a : ∀ (x : Nat), x = 0\n").unwrap_or_default();
    assert!(decls.iter().all(|x| !matches!(x.status, Status::Proved)));
}

#[test]
fn g07_negative_unsupported_translations() {
    let d = common::scratch("engine-a-unsup");
    let r = engine_a::translate_file(&common::repo().join("lean/EngineAUnsupported.lean"), &d, &common::repo().join("agda"), true).unwrap();
    assert_eq!(r.lean_exit, Some(0), "{}", r.lean_output);
    assert!(!r.decls.is_empty());
    for x in &r.decls {
        println!("{} {:?}", x.name, x.status);
        assert!(!matches!(x.status, Status::Proved), "{} must not be claimed", x.name);
    }
    assert!(r.decls.iter().any(|x| matches!(x.status, Status::Rejected(_))));
}

#[test]
fn g08_agda_accepts_valid_and_rejects_malformed() {
    let d = common::scratch("agda");
    let root = common::repo().join("agda");
    let ok = agda::check(&root, &d, "Good", &safe("Good", "p : 2 + 2 ≡ 4\np = refl"));
    assert!(ok.ok, "{}", ok.output);
    // false proposition
    let bad = agda::check(&root, &d, "Bad", &safe("Bad", "p : 2 + 2 ≡ 5\np = refl"));
    assert!(!bad.ok);
    assert!(bad.output.contains("!="), "{}", bad.output);
    // syntax error
    let syn = agda::check(&root, &d, "Syn", &safe("Syn", "p : 2 + 2 ≡ 4\np = refl )"));
    assert!(!syn.ok);
    // postulate / hole / missing --safe: refused before Agda runs
    for (m, t) in [
        ("Post", safe("Post", "postulate p : 2 + 2 ≡ 5")),
        ("Hole", safe("Hole", "p : 2 + 2 ≡ 4\np = {!!}")),
        ("Unsafe", "module Unsafe where\n".to_string()),
    ] {
        let r = agda::check(&root, &d, m, &t);
        assert!(!r.ok && r.output.contains("rejected"), "{}: {}", m, r.output);
    }
}

#[test]
fn g09_liquidhaskell_safe_and_unsafe() {
    let repo = common::repo();
    let d = common::scratch("lh");
    let good = liquid::check_file(&repo.join("haskell/Contracts.hs"), &d.join("good"));
    assert!(good.ok, "{}", good.output);
    let bad = liquid::check_file(&repo.join("haskell/negative/ContractsWrong.hs"), &d.join("bad"));
    assert!(!bad.ok);
    assert!(bad.output.contains("LIQUID: UNSAFE") || !bad.error_lines.is_empty(), "{}", bad.output);
    println!("ContractsWrong error lines: {:?}", bad.error_lines);
    assert!(!bad.error_lines.is_empty());
}

#[test]
fn g11_invalid_certificate_rejected() {
    let d = common::scratch("cert");
    let root = common::repo().join("agda");
    let src = common::gen0();
    let script = rewrite::parse_script("cf;alg;dce;fuse;pe4").unwrap();
    let c = anneal::evaluate(&src, &script).unwrap();
    let spec = agda::CertSpec { id: "t11ok".into(), src: &src, script: &c.script, tgt: &c.tgt, knot_t: 3, samples: &c.io };
    let text = agda::emit_cert(&spec);
    let m = agda::module_name("t11ok");
    let r = agda::check(&root, &d, &m, &text);
    assert!(r.ok, "valid certificate rejected:\n{}", r.output);
    // a target that is not the result of the script
    let wrong = spme::controller::tamper(&c.tgt);
    let spec = agda::CertSpec { id: "t11bad".into(), src: &src, script: &c.script, tgt: &wrong, knot_t: 3, samples: &c.io };
    let m = agda::module_name("t11bad");
    let r = agda::check(&root, &d, &m, &agda::emit_cert(&spec));
    assert!(!r.ok, "tampered certificate accepted");
    // an edited certificate text (proof term replaced) is rejected
    let edited = text.replacen("refl", "λ ()", 1);
    let m2 = agda::module_name("t11ok");
    let r = agda::check(&root, &d.join("edit"), &m2, &edited);
    assert!(!r.ok, "edited certificate accepted");
}
