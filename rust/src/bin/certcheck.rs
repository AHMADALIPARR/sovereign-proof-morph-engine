// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! `certcheck FILE.morph SCRIPT OUTDIR`: apply a rewrite script, emit the
//! Agda certificate and check it. Diagnostic entry point for step 03.
use spme::*;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 4 {
        eprintln!("usage: certcheck FILE.morph SCRIPT OUTDIR");
        std::process::exit(2);
    }
    let src = parse::parse_surface(&std::fs::read_to_string(&a[1]).expect("read")).expect("parse");
    let script = rewrite::parse_script(&a[2]).expect("script");
    let tgt = rewrite::apply_script(&src, &script).expect("rewrite");
    println!("src: {}\ntgt: {}", src.canonical(), tgt.canonical());
    let code = vm::compile(&tgt);
    let mut samples = Vec::new();
    for u in [-3i64, 0, 1, 7] {
        let (r, st) = vm::run(&code, tgt.defs.len() - 1, ir::Val::Int(u), 1 << 20);
        let r = r.expect("vm");
        assert_eq!(Ok(r.clone()), eval::run_main(&src, ir::Val::Int(u)));
        println!("u={} out={} instr={}", u, r, st.instructions);
        samples.push((ir::Val::Int(u), r));
    }
    let spec = agda::CertSpec { id: "Diag".into(), src: &src, script: &script, tgt: &tgt, knot_t: 7, samples: &samples };
    let text = agda::emit_cert(&spec);
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../agda");
    let r = agda::check(&root, std::path::Path::new(&a[3]), "CertDiag", &text);
    println!("agda ok={} ms={}\n{}", r.ok, r.millis, r.output);
}
