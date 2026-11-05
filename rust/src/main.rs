// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! `spme` command line.
//!
//!   spme load FILE.morph --work DIR
//!   spme run --work DIR [--generations N] [--seed S] [--iterations K] [--flags a,b]
//!   spme replay --work DIR [--recheck]
//!   spme verify-ledger --work DIR
//!   spme exhaustive FILE.morph [--depth D]
//!   spme engine-a FILE.lean --out DIR [--no-agda]
//!   spme ref-check FILE.morph | --work DIR [--ref BIN]
//!   spme torus
//!   spme versions
use spme::controller::{self, Config};
use spme::json::Json;
use spme::*;
use std::path::PathBuf;

fn opt(a: &[String], k: &str) -> Option<String> {
    a.iter().position(|x| x == k).and_then(|i| a.get(i + 1)).cloned()
}

fn die(m: String) -> ! {
    eprintln!("error: {}", m);
    std::process::exit(1)
}

fn cfg(a: &[String]) -> Config {
    let repo = opt(a, "--repo").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(".."));
    let work = PathBuf::from(opt(a, "--work").unwrap_or_else(|| die("--work DIR required".into())));
    let mut c = Config::new(&repo, &work);
    if let Some(s) = opt(a, "--seed") {
        c.seed = s.parse().unwrap_or_else(|_| die("bad --seed".into()));
    }
    if let Some(s) = opt(a, "--iterations") {
        c.iterations = s.parse().unwrap_or_else(|_| die("bad --iterations".into()));
    }
    if let Some(s) = opt(a, "--flags") {
        c.policy_flags = s.split(',').map(String::from).collect();
    }
    if let Some(s) = opt(a, "--bench-calls") {
        c.bench_calls = s.parse().unwrap_or_else(|_| die("bad --bench-calls".into()));
    }
    c
}

fn g<'a>(j: &'a Json, path: &[&str]) -> Option<&'a Json> {
    let mut x = j;
    for p in path {
        x = x.get(p)?;
    }
    Some(x)
}

fn s(j: &Json, path: &[&str]) -> String {
    match g(j, path) {
        Some(Json::Str(x)) => x.clone(),
        Some(Json::Num(x)) => x.clone(),
        Some(Json::Bool(b)) => b.to_string(),
        Some(Json::Null) | None => "-".into(),
        Some(o) => o.dump(),
    }
}

fn print_outcome(o: &controller::Outcome) {
    let b = &o.body;
    println!("== generation {} : {} ==", o.generation, if o.committed { "COMMIT" } else { "REJECT" });
    println!("candidate        {}", s(b, &["candidate"]));
    println!("source sha256    {}", s(b, &["source_sha256"]));
    println!("target sha256    {}", s(b, &["target_sha256"]));
    println!("script           {}", s(b, &["transformation", "script"]));
    println!(
        "anneal           seed={} proposed={} valid={} accepted={} uphill={} improved={} E0={} E*={} Tfinal={} stop={}",
        s(b, &["anneal", "seed"]),
        s(b, &["anneal", "proposed"]),
        s(b, &["anneal", "valid"]),
        s(b, &["anneal", "accepted"]),
        s(b, &["anneal", "uphill_accepted"]),
        s(b, &["anneal", "improved"]),
        s(b, &["anneal", "initial_energy"]),
        s(b, &["anneal", "best_energy"]),
        s(b, &["anneal", "final_temperature"]),
        s(b, &["anneal", "stop"])
    );
    println!("torus            t={} coord={} phase={}", s(b, &["anneal", "knot_t"]), s(b, &["anneal", "knot_coord"]), s(b, &["anneal", "phase"]));
    if let Some(r) = g(b, &["anneal", "ranking"]).and_then(|x| x.arr()) {
        println!("ranking (distinct targets, best first):");
        for (i, c) in r.iter().enumerate() {
            println!("  {}. E={} instr={} size={} script={}", i + 1, s(c, &["energy"]), s(c, &["instructions"]), s(c, &["size"]), s(c, &["script"]));
        }
    }
    println!("agda             {} {} in {} ms ({})", s(b, &["checker", "module"]), s(b, &["checker", "outcome"]), s(b, &["checker", "ms"]), s(b, &["checker", "agda"]));
    if g(b, &["checker", "chain", "module"]).is_some() {
        println!("chain            {} ok={} in {} ms", s(b, &["checker", "chain", "module"]), s(b, &["checker", "chain", "ok"]), s(b, &["checker", "chain", "ms"]));
    }
    println!("datalog          {} reasons={} ({})", s(b, &["datalog", "verdict"]), s(b, &["datalog", "silence_reasons"]), s(b, &["datalog", "souffle"]));
    println!("migration        {}", s(b, &["state_migration"]));
    if g(b, &["native"]).is_some() {
        println!(
            "native           inputs={} agree_vm={} agree_reference={} reference_trapped={} binary={}",
            s(b, &["native", "validated_inputs"]),
            s(b, &["native", "agree_vm"]),
            s(b, &["native", "agree_reference"]),
            s(b, &["native", "reference_trapped"]),
            s(b, &["native", "binary_sha256"])
        );
    }
    if g(b, &["measurement", "before"]).is_some() {
        for w in ["before", "after"] {
            println!(
                "measure {:6}   vm_instr={} ir_size={} native median {} ns / {} calls ({} ns/call) runs={}",
                w,
                s(b, &["measurement", w, "vm_instructions_total"]),
                s(b, &["measurement", w, "ir_size"]),
                s(b, &["measurement", w, "native_median_ns"]),
                s(b, &["measurement", w, "native_calls"]),
                s(b, &["measurement", w, "native_ns_per_call_median"]),
                s(b, &["measurement", w, "native_runs_ns"])
            );
        }
    }
    if g(b, &["rollback"]).is_some() {
        println!("rollback         {}", s(b, &["rollback"]));
    }
    println!("version          v{:04}", s(b, &["execution_version"]).parse::<u64>().unwrap_or(0));
    println!("reason           {}", o.reason);
    println!("ledger           {}", o.record_hash);
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let cmd = a.get(1).map(String::as_str).unwrap_or("");
    match cmd {
        "load" => {
            let file = a.get(2).unwrap_or_else(|| die("load FILE.morph".into()));
            let c = cfg(&a);
            let text = std::fs::read_to_string(file).unwrap_or_else(|e| die(e.to_string()));
            let o = controller::load(&c, &text).unwrap_or_else(|e| die(e));
            println!("== load ==\nsource sha256    {}\nagda             {} {}\nversion          v0000 active\nmeasure          vm_instr={} native median {} ns / {} calls\nledger           {}",
                s(&o.body, &["source_sha256"]), s(&o.body, &["checker", "agda"]), s(&o.body, &["checker", "outcome"]),
                s(&o.body, &["measurement", "vm_instructions_total"]), s(&o.body, &["measurement", "native_median_ns"]), s(&o.body, &["measurement", "native_calls"]), o.record_hash);
        }
        "run" => {
            let c = cfg(&a);
            let n: u64 = opt(&a, "--generations").map(|x| x.parse().unwrap_or(1)).unwrap_or(1);
            for _ in 0..n {
                let o = controller::generation(&c).unwrap_or_else(|e| die(e));
                print_outcome(&o);
            }
        }
        "replay" => {
            let c = cfg(&a);
            let r = controller::replay(&c, a.iter().any(|x| x == "--recheck"));
            for l in &r.lines {
                println!("{}", l);
            }
            if r.failures.is_empty() {
                println!("replay: OK ({} records)", r.records);
            } else {
                for f in &r.failures {
                    println!("FAIL {}", f);
                }
                std::process::exit(1);
            }
        }
        "verify-ledger" => {
            let c = cfg(&a);
            match c.ledger().verify() {
                Ok(r) => println!("ledger OK: {} records, head {}", r.len(), r.last().map(|x| x.hash.clone()).unwrap_or_default()),
                Err(e) => {
                    println!("ledger INVALID: {}", e);
                    std::process::exit(1)
                }
            }
        }
        "exhaustive" => {
            let file = a.get(2).unwrap_or_else(|| die("exhaustive FILE.morph".into()));
            let d: usize = opt(&a, "--depth").map(|x| x.parse().unwrap_or(2)).unwrap_or(2);
            let p = parse::parse_surface(&std::fs::read_to_string(file).unwrap_or_else(|e| die(e.to_string()))).unwrap_or_else(|e| die(e));
            let alphabet = rewrite::parse_script("cf;alg;dce;fuse;pe4").unwrap();
            let (best, visited) = anneal::exhaustive(&p, &alphabet, d).unwrap_or_else(|e| die(e));
            println!("exhaustive depth={} visited={} best script={} energy={} cost={:?}", d, visited, rewrite::script_text(&best.script), best.energy, best.cost);
        }
        "engine-a" => {
            let f = PathBuf::from(a.get(2).cloned().unwrap_or_else(|| die("usage: spme engine-a FILE.lean --out DIR".into())));
            let out = PathBuf::from(opt(&a, "--out").unwrap_or_else(|| die("--out DIR required".into())));
            let c = Config::new(&PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(".."), &out);
            let f = std::fs::canonicalize(&f).unwrap_or_else(|e| die(format!("{}: {}", f.display(), e)));
            let r = engine_a::translate_file(&f, &out, &c.agda_root(), !a.iter().any(|x| x == "--no-agda")).unwrap_or_else(|e| die(e));
            println!("{}", r.lean_version);
            println!("{}", r.agda_version);
            println!("{} (refinement checks are recorded, not proof authority)", r.lh_version);
            for d in &r.decls {
                let (st, why) = match &d.status {
                    engine_a::Status::Proved => ("PROVED (Agda)", String::new()),
                    engine_a::Status::Definition => ("translated", String::new()),
                    engine_a::Status::Unproved(m) => ("UNPROVED", m.clone()),
                    engine_a::Status::Rejected(m) => ("REJECTED", m.clone()),
                };
                let agree = d.samples.iter().filter(|s| s.agree).count();
                let ev = if d.samples.is_empty() { String::new() } else { format!(" lean/ir agreement {}/{}", agree, d.samples.len()) };
                println!("{:8} {:14} {:14}{} {}", d.kind, d.name, st, ev, why);
                if let Some(l) = &d.lh {
                    println!("{:8} {:14} liquidhaskell: {}", "", "", l);
                }
            }
            println!("report: {}", out.join("report.json").display());
        }
        "ref-check" => {
            // Differential check of every stored version (or one .morph file)
            // against the Haskell reference model.
            let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
            let bin = opt(&a, "--ref").map(PathBuf::from).unwrap_or_else(|| repo.join("haskell/build/ref"));
            let mut progs: Vec<(String, ir::Prog)> = Vec::new();
            if let Some(w) = opt(&a, "--work") {
                let vd = PathBuf::from(w).join("runtime").join("versions");
                let mut ds: Vec<_> = std::fs::read_dir(&vd).unwrap_or_else(|e| die(format!("{}: {}", vd.display(), e))).filter_map(|e| e.ok()).map(|e| e.path()).collect();
                ds.sort();
                for d in ds {
                    if let Ok(t) = std::fs::read_to_string(d.join("program.ir")) {
                        let p = parse::parse_canonical(&t).unwrap_or_else(|e| die(e));
                        progs.push((d.file_name().unwrap().to_string_lossy().into_owned(), p));
                    }
                }
            } else {
                let f = a.get(2).filter(|x| !x.starts_with("--")).unwrap_or_else(|| die("usage: spme ref-check FILE.morph | --work DIR".into()));
                let p = parse::parse_surface(&std::fs::read_to_string(f).unwrap_or_else(|e| die(e.to_string()))).unwrap_or_else(|e| die(e));
                progs.push((f.clone(), p));
            }
            let mut bad = false;
            for (name, p) in &progs {
                let t = p.defs.last().unwrap().arg.clone();
                let inputs = controller::validation_inputs(&t, 0x5eed);
                let r = refmodel::check(&bin, p, &inputs).unwrap_or_else(|e| die(e));
                println!("{:24} inputs={} agree={} rust_overflow_excluded={} disagree={}", name, r.inputs, r.agree, r.rust_overflow, r.disagreements.len());
                for d in &r.disagreements {
                    println!("  {}", d);
                }
                bad |= !r.disagreements.is_empty();
            }
            if bad {
                std::process::exit(1)
            }
        }
        "torus" => {
            let c = Config::new(&PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(".."), &PathBuf::from("."));
            let t = torus::Torus::load(&c.torus_table()).unwrap_or_else(|e| die(e));
            let mut seen = vec![false; 2462];
            for k in 0..2462u64 {
                seen[torus::phase(k) as usize] = true;
            }
            println!("torus table: {} rows, header sha256 {}; phase over t=0..2461 is a permutation: {}", t.rows.len(), t.header_sha256, seen.iter().all(|x| *x));
        }
        _ => {
            eprintln!("usage: spme load|run|replay|verify-ledger|exhaustive|torus ...");
            std::process::exit(2)
        }
    }
}
