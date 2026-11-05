// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Groups 5, 6, 15: IR parse / typecheck / eval, every rewrite pass,
//! executable before/after behaviour (VM, native rustc build, Haskell
//! reference model).
mod common;
use spme::anneal;
use spme::eval;
use spme::ir::{Prog, Ty, Val};
use spme::parse;
use spme::rewrite::{self, Pass, Step};
use spme::typecheck;

fn ints() -> Vec<Val> {
    (-50i64..=50).map(Val::Int).collect()
}

fn same_behaviour(a: &Prog, b: &Prog) {
    for x in ints() {
        assert_eq!(eval::run_main(a, x.clone()), eval::run_main(b, x.clone()), "differs on {}", x);
    }
}

#[test]
fn g05_parse_typecheck_eval() {
    let p = common::gen0();
    assert_eq!(p.defs.len(), 3);
    assert_eq!(typecheck::check_prog(&p).unwrap(), (Ty::Int, Ty::Int));
    let f0 = match eval::run_main(&p, Val::Int(0)).unwrap() {
        Val::Int(n) => n,
        v => panic!("{}", v),
    };
    // main x = (x + 3 + 4) + 5x + iter-sum: linear with slope 6
    for x in -20i64..=20 {
        assert_eq!(eval::run_main(&p, Val::Int(x)).unwrap(), Val::Int(f0 + 6 * x));
    }
    // canonical round trip
    let c = p.canonical();
    let q = parse::parse_canonical(&c).unwrap();
    assert_eq!(q.canonical(), c);
    assert_eq!(q.hash(), p.hash());
}

#[test]
fn g05_negative_malformed_programs() {
    for bad in [
        "(def main (x int) int (add x",                 // unbalanced
        "(def main (x int) int (frobnicate x))",         // unknown operator
        "(def main (x int) int (call nosuch x))",        // unknown callee
        "(def main (x int) int y)",                      // unbound variable
        "",                                              // empty
    ] {
        let r = parse::parse_surface(bad).and_then(|p| typecheck::check_prog(&p).map(|_| p));
        assert!(r.is_err(), "accepted malformed program: {:?}", bad);
    }
    // ill-typed: bool body for an int result, int + bool
    for bad in [
        "(def main (x int) int (bool true))",
        "(def main (x int) int (add x (bool true)))",
        "(def main (x nat) int x)",
    ] {
        let p = parse::parse_surface(bad);
        if let Ok(p) = p {
            assert!(typecheck::check_prog(&p).is_err(), "ill-typed program typechecked: {}", bad);
        }
    }
}

#[test]
fn g05_machine_overflow_traps_not_wraps() {
    let p = parse::parse_surface("(def main (x int) int (mul x x))").unwrap();
    assert!(eval::run_main(&p, Val::Int(i64::MAX)).is_err());
    assert_eq!(eval::run_main(&p, Val::Int(-7)).unwrap(), Val::Int(49));
}

#[test]
fn g06_every_pass_preserves_semantics() {
    let p = common::gen0();
    for pass in [Pass::Cf, Pass::Alg, Pass::Dce, Pass::Fuse, Pass::Pe(1), Pass::Pe(2), Pass::Pe(4)] {
        let q = rewrite::run_passes(&[pass], &p).unwrap();
        typecheck::check_prog(&q).unwrap();
        same_behaviour(&p, &q);
    }
}

#[test]
fn g06_each_pass_does_its_rewrite() {
    let p = common::gen0();
    let canon = |q: &Prog, s: &str| rewrite::apply_script(q, &rewrite::parse_script(s).unwrap()).unwrap().canonical();
    let s0 = p.canonical();
    // alg: x*1 -> x and x*0 -> 0
    assert!(s0.contains("(mulZ #1 (int 1))") && s0.contains("(mulZ #0 (int 0))"));
    let a = canon(&p, "alg");
    assert!(!a.contains("(mulZ #1 (int 1))") && !a.contains("(mulZ #0 (int 0))"), "{}", a);
    // dce: the unused (mulZ #0 (int 7)) binding is dropped
    assert!(s0.contains("(let (mulZ #0 (int 7))"));
    assert!(!canon(&p, "dce").contains("(let (mulZ #0 (int 7))"));
    // fuse: (e + 3) + 4 -> e + 7
    let f = canon(&p, "fuse");
    assert!(f.contains("(int 7))") && !f.contains("(int 3)"), "{}", f);
    // pe4: the constant 3-step loop is unrolled
    assert!(s0.contains("(iter (nat 3)") && !canon(&p, "pe4").contains("iter"));
    // cf: constant subterms fold
    let k = parse::parse_surface("(def main (x int) int (add x (mul (int 2) (int 3))))").unwrap();
    assert!(canon(&k, "cf").contains("(addZ #0 (int 6))"), "{}", canon(&k, "cf"));
    same_behaviour(&k, &rewrite::run_passes(&[Pass::Cf], &k).unwrap());
    let full = rewrite::apply_script(&p, &rewrite::parse_script("cf;alg;dce;fuse;pe4").unwrap()).unwrap();
    assert!(full.size() < p.size());
    same_behaviour(&p, &full);
}

#[test]
fn g06_specialization() {
    let p = common::gen0();
    // main calls scale (call index 1 from main) with literal 5
    let mut ok = false;
    for j in 0..2 {
        if let Ok(q) = rewrite::spec(&p, j, &Val::Int(5)) {
            typecheck::check_prog(&q).unwrap();
            same_behaviour(&p, &q);
            assert_eq!(q.defs.len(), p.defs.len() + 1);
            ok = true;
        }
    }
    assert!(ok, "no specialization site accepted");
    // negative: a value of the wrong type is refused
    assert!(rewrite::spec(&p, 1, &Val::Bool(true)).is_err());
    assert!(rewrite::spec(&p, 99, &Val::Int(5)).is_err());
}

#[test]
fn g06_negative_bad_scripts() {
    assert!(rewrite::parse_script("cf;frob").is_err());
    assert!(rewrite::parse_script("peX").is_err());
    assert!(rewrite::parse_script("spec:1").is_err());
    let s = rewrite::parse_script("cf,alg;spec:1:(int 5)").unwrap();
    assert_eq!(s.len(), 2);
    assert!(matches!(s[1], Step::Spec { j: 1, .. }));
}

#[test]
fn g15_vm_matches_reference_before_and_after() {
    let p = common::gen0();
    let script = rewrite::parse_script("cf;alg;dce;fuse;pe4").unwrap();
    let c = anneal::evaluate(&p, &script).unwrap();
    assert!(!c.io.is_empty());
    for (u, out) in &c.io {
        assert_eq!(&eval::run_main(&p, u.clone()).unwrap(), out);
    }
    let base = anneal::evaluate(&p, &vec![]).unwrap();
    assert!(c.cost.instructions < base.cost.instructions, "{} !< {}", c.cost.instructions, base.cost.instructions);
}

#[test]
fn g15_native_binary_before_and_after() {
    let p = common::gen0();
    let tgt = rewrite::apply_script(&p, &rewrite::parse_script("cf;alg;dce;fuse;pe4").unwrap()).unwrap();
    let d = common::scratch("native");
    let inputs = spme::controller::validation_inputs(&Ty::Int, 0x5eed);
    for (stem, prog) in [("before", &p), ("after", &tgt)] {
        let b = spme::native::compile(prog, &d, stem).unwrap();
        let v = spme::native::validate(&b.binary, &p, prog, &inputs).unwrap();
        assert!(v.mismatches.is_empty(), "{}: {:?}", stem, v.mismatches);
        assert_eq!(v.agree_vm, v.inputs);
        assert_eq!(v.agree_reference + v.reference_trapped, v.inputs);
    }
}

#[test]
fn g15_haskell_reference_model_agrees() {
    let bin = common::repo().join("haskell/build/ref");
    if !bin.exists() {
        panic!("haskell/build/ref not built: run `make ref`");
    }
    let p = common::gen0();
    let tgt = rewrite::apply_script(&p, &rewrite::parse_script("cf;alg;dce;fuse;pe4").unwrap()).unwrap();
    let inputs = spme::controller::validation_inputs(&Ty::Int, 0x5eed);
    for prog in [&p, &tgt] {
        let r = spme::refmodel::check(&bin, prog, &inputs).unwrap();
        assert!(r.disagreements.is_empty(), "{:?}", r.disagreements);
        assert_eq!(r.agree + r.rust_overflow, r.inputs);
    }
}
