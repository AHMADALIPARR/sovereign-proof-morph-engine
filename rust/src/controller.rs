// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! L9 controller: the self-modification lifecycle.
//!
//! LOAD → GENERATE → EXPLORE torus → ENERGY → SELECT → OBLIGATIONS → CHECK
//! → DATALOG → COMPILE → VALIDATE → ATOMIC ACTIVATE → EXECUTE/MEASURE
//! → LEDGER → REPEAT.
//!
//! Order decision: the Datalog gate runs before native compilation. Its
//! runtime evidence is the VM differential test and the state-migration
//! check, both available before compiling. Native validation is a second,
//! independent runtime check after the gate; if it fails the candidate is not
//! activated (or, if the post-activation check fails, the previous version is
//! re-activated) and the rejection is recorded in the ledger.

use crate::agda;
use crate::anneal::{self, Params, Proposal, SplitMix64};
use crate::energy;
use crate::gate::{self, Facts, ProofFact, Verdict};
use crate::ir::*;
use crate::json::Json;
use crate::ledger::Ledger;
use crate::native;
use crate::rewrite;
use crate::runtime::{self, Runtime};
use crate::torus::{self, Torus};
use std::path::{Path, PathBuf};

/// Faults injected by the test-suite to exercise the rejection paths.
#[derive(Clone, Debug, PartialEq)]
pub enum Fault {
    None,
    /// Emit a certificate whose `tgt` differs from what the script produces.
    TamperCertificate,
    /// Replace the compiled target with the binary of a different program.
    WrongNative,
    /// Fail the post-activation check, forcing a rollback.
    FailAfterActivate,
    /// Present a candidate whose main type differs (needs a migration).
    ChangeStateType,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub repo: PathBuf,
    pub work: PathBuf,
    pub seed: u64,
    pub iterations: u32,
    pub policy_flags: Vec<String>,
    pub stateful: bool,
    pub bench_calls: u64,
    pub bench_reps: usize,
    pub fault: Fault,
}

impl Config {
    pub fn new(repo: &Path, work: &Path) -> Config {
        Config {
            repo: repo.to_path_buf(),
            work: work.to_path_buf(),
            seed: Params::default().seed,
            iterations: Params::default().iterations,
            policy_flags: vec!["clean".into()],
            stateful: false,
            bench_calls: 1_000_000,
            bench_reps: 5,
            fault: Fault::None,
        }
    }
    pub fn agda_root(&self) -> PathBuf {
        self.repo.join("agda")
    }
    pub fn rules(&self) -> PathBuf {
        self.repo.join("datalog/gate.dl")
    }
    pub fn torus_table(&self) -> PathBuf {
        self.repo.join("extract/torus_path.h")
    }
    pub fn runtime(&self) -> Runtime {
        Runtime::new(&self.work.join("runtime"))
    }
    pub fn certs(&self) -> PathBuf {
        self.work.join("certs")
    }
    pub fn ledger(&self) -> Ledger {
        Ledger::open(&self.work.join("ledger.jsonl"))
    }
    pub fn params(&self, generation: u64, last_t: u64) -> Params {
        Params {
            seed: self.seed ^ generation.wrapping_mul(0x9E37_79B9_7F4A_7C15),
            iterations: self.iterations,
            proposal: Proposal::Torus { t0: last_t },
            ..Params::default()
        }
    }
}

/// Inputs for native validation: the annealer's samples plus seeded random
/// values and extremes (traps must agree too).
pub fn validation_inputs(t: &Ty, seed: u64) -> Vec<Val> {
    let mut v = anneal::samples(t);
    let mut rng = SplitMix64(seed);
    fn gen(t: &Ty, r: &mut SplitMix64, k: u64) -> Val {
        match t {
            Ty::Nat => Val::Nat(match k % 4 {
                0 => r.below(1000),
                1 => r.below(1 << 32),
                2 => u64::MAX - r.below(4),
                _ => r.next_u64(),
            }),
            Ty::Int => Val::Int(match k % 4 {
                0 => r.below(2001) as i64 - 1000,
                1 => (r.below(1 << 32) as i64) - (1 << 31),
                2 => if r.below(2) == 0 { i64::MAX - r.below(4) as i64 } else { i64::MIN + r.below(4) as i64 },
                _ => r.next_u64() as i64,
            }),
            Ty::Bool => Val::Bool(r.below(2) == 1),
            Ty::Prod(a, b) => Val::Pair(Box::new(gen(a, r, k)), Box::new(gen(b, r, k / 2))),
            Ty::Sum(a, b) => {
                if r.below(2) == 0 {
                    Val::Inl(Box::new(gen(a, r, k)))
                } else {
                    Val::Inr(Box::new(gen(b, r, k)))
                }
            }
        }
    }
    for k in 0..64u64 {
        v.push(gen(t, &mut rng, k));
    }
    v
}

fn reference_io(p: &Prog) -> Vec<(Val, Val)> {
    anneal::samples(&p.main().arg)
        .into_iter()
        .filter_map(|u| crate::eval::run_main(p, u.clone()).ok().map(|o| (u, o)))
        .collect()
}

fn median(mut v: Vec<u128>) -> u128 {
    v.sort();
    v[v.len() / 2]
}

/// Measured cost: VM instruction counts on the samples and native
/// wall-clock time (median of `reps` runs of `calls` calls on `x`).
pub fn measure(p: &Prog, binary: &Path, x: &Val, calls: u64, reps: usize) -> Result<Json, String> {
    let code = crate::vm::compile(p);
    let mut instr = 0u64;
    let mut peak = 0usize;
    let mut n = 0u64;
    for u in anneal::samples(&p.main().arg) {
        let (r, st) = crate::vm::run(&code, p.defs.len() - 1, u, anneal::FUEL);
        if r.is_ok() {
            instr += st.instructions;
            peak = peak.max(st.peak_stack);
            n += 1;
        }
    }
    let mut runs = Vec::new();
    let mut out = String::new();
    for _ in 0..reps {
        let (ns, o) = native::bench(binary, calls, x)?;
        runs.push(ns);
        out = o;
    }
    let med = median(runs.clone());
    Ok(Json::obj()
        .with("vm_instructions_total", instr)
        .with("vm_samples", n)
        .with("vm_peak_stack", peak)
        .with("ir_size", p.size())
        .with("native_input", x.to_string())
        .with("native_output", out)
        .with("native_calls", calls)
        .with("native_runs_ns", Json::Arr(runs.iter().map(|r| Json::Num(r.to_string())).collect()))
        .with("native_median_ns", Json::Num(med.to_string()))
        .with("native_ns_per_call_median", med as f64 / calls as f64)
        .with("provenance", "measured on this host: VM instruction counter (rust/src/vm.rs); std::time::Instant around a black_box loop in the generated binary"))
}

fn bench_input(t: &Ty) -> Val {
    let s = anneal::samples(t);
    s.iter().find(|v| !matches!(v, Val::Nat(0) | Val::Int(0))).cloned().unwrap_or_else(|| s[0].clone())
}

#[derive(Debug, Clone)]
pub struct Outcome {
    pub generation: u64,
    pub committed: bool,
    pub reason: String,
    pub record_hash: String,
    pub body: Json,
}

fn cert_manifest(cfg: &Config, module: &str, file: &Path, props: &[&str], src: &Prog, tgt: &Prog, r: &agda::CheckResult) -> Json {
    let deps: Vec<Json> = agda::dependencies(&cfg.agda_root())
        .into_iter()
        .map(|(f, h)| Json::obj().with("file", f).with("sha256", h))
        .collect();
    Json::obj()
        .with("module", module)
        .with("file", file.display().to_string())
        .with("certificate_sha256", crate::sha256::file_hex(file).unwrap_or_default())
        .with("propositions", Json::Arr(props.iter().map(|p| Json::from(*p)).collect()))
        .with("src_sha256", src.hash())
        .with("tgt_sha256", tgt.hash())
        .with("checker", agda::agda_version().unwrap_or_else(|| "agda not found".into()))
        .with("checker_flags", "--safe; no postulates, no holes")
        .with("stdlib", agda::stdlib_identity())
        .with("dependencies", Json::Arr(deps))
        .with("result", if r.ok { "checked" } else { "rejected" })
        .with("check_ms", r.millis as u64)
        .with("checker_output", r.output.clone())
}

fn write_json(p: &Path, j: &Json) -> Result<(), String> {
    std::fs::write(p, j.dump() + "\n").map_err(|e| e.to_string())
}

/// LOAD: typecheck the source, check its load certificate with Agda,
/// compile and validate it natively, stage it as version 0, activate, and
/// write the genesis ledger record.
pub fn load(cfg: &Config, src_text: &str) -> Result<Outcome, String> {
    let p = crate::parse::parse_surface(src_text)?;
    crate::typecheck::check_prog(&p)?;
    let rt = cfg.runtime();
    if rt.active().is_some() {
        return Err("runtime already initialised".into());
    }
    let io = reference_io(&p);
    let module = agda::module_name("Load");
    let text = agda::emit_load("Load", &p, &io);
    let r = agda::check(&cfg.agda_root(), &cfg.certs(), &module, &text);
    let file = cfg.certs().join(format!("{}.agda", module));
    let man = cert_manifest(cfg, &module, &file, &["src : Prog Σ (typed IR)", "sound : tgt ≈ src (identity)", "exec-k : runMain src u ≡ v"], &p, &p, &r);
    write_json(&cfg.certs().join(format!("{}.json", module)), &man)?;
    if !r.ok {
        return Err(format!("load certificate rejected:\n{}", r.output));
    }
    let built = native::compile(&p, &cfg.work.join("build"), "g0")?;
    let val = native::validate(&built.binary, &p, &p, &validation_inputs(&p.main().arg, cfg.seed))?;
    if !val.mismatches.is_empty() {
        return Err(format!("native validation of loaded program failed: {:?}", val.mismatches));
    }
    let meta = Json::obj().with("generation", 0u64).with("cert_module", module.as_str()).with("knot_t", 0u64).with("script", "");
    let v = rt.stage(&p, &built, meta)?;
    rt.activate(&v)?;
    let x = bench_input(&p.main().arg);
    let m = measure(&p, &rt.active_link().join("program"), &x, cfg.bench_calls, cfg.bench_reps)?;
    let body = Json::obj()
        .with("kind", "load")
        .with("generation", 0u64)
        .with("source_sha256", p.hash())
        .with("target_sha256", p.hash())
        .with("transformation", "identity (load)")
        .with("obligations", Json::Arr(vec![Json::obj().with("module", module.as_str()).with("sha256", man.get("certificate_sha256").cloned().unwrap_or(Json::Null))]))
        .with("checker", Json::obj().with("agda", man.get("checker").cloned().unwrap_or(Json::Null)).with("outcome", "checked").with("ms", r.millis as u64))
        .with("datalog", Json::obj().with("verdict", "NOT_APPLICABLE (initial load)"))
        .with("native", Json::obj().with("rustc", native::rustc_version().unwrap_or_default()).with("binary_sha256", v.binary_sha256.as_str()).with("validated_inputs", val.inputs).with("agree_vm", val.agree_vm).with("agree_reference", val.agree_reference))
        .with("measurement", m)
        .with("execution_version", v.id)
        .with("decision", "COMMIT")
        .with("reason", "initial verified program loaded");
    let rec = cfg.ledger().append(body.clone())?;
    Ok(Outcome { generation: 0, committed: true, reason: "loaded".into(), record_hash: rec.hash, body })
}

fn meta_of(v: &runtime::Version) -> Json {
    std::fs::read_to_string(v.dir.join("manifest.json"))
        .ok()
        .and_then(|s| Json::parse(&s).ok())
        .and_then(|m| m.get("meta").cloned())
        .unwrap_or(Json::Null)
}

/// One generation of the lifecycle. Returns the ledger outcome; the active
/// executable changes only on COMMIT with all checks passed.
pub fn generation(cfg: &Config) -> Result<Outcome, String> {
    let rt = cfg.runtime();
    let ledger = cfg.ledger();
    let records = ledger.verify().map_err(|e| format!("ledger verification failed before generation: {}", e))?;
    // LOAD
    let (active, src) = rt.load_active()?;
    let meta = meta_of(&active);
    // attempt number = ledger sequence number, so every attempt (committed or
    // rejected) has its own certificate, gate and build files.
    let g = records.len() as u64;
    let last_t = meta.get("knot_t").and_then(|x| x.u64()).unwrap_or(0);
    let prev_module = meta.get("cert_module").and_then(|x| x.str()).unwrap_or("").to_string();
    let tor = Torus::load(&cfg.torus_table())?;
    // GENERATE / EXPLORE / ENERGY / SELECT
    let prm = cfg.params(g, last_t);
    let (best, trace) = anneal::anneal(&src, &prm)?;
    let mut tgt = best.tgt.clone();
    let mut script = best.script.clone();
    if cfg.fault == Fault::ChangeStateType {
        // a hand-built candidate whose main returns a pair instead
        let mut t2 = src.clone();
        let m = t2.defs.len() - 1;
        let old = t2.defs[m].body.clone();
        t2.defs[m].body = Expr::Pair(b(old), b(Expr::Lit(Val::Bool(true))));
        t2.defs[m].ret = Ty::prod(t2.defs[m].ret.clone(), Ty::Bool);
        tgt = t2;
        script = Vec::new();
    }
    let ranking: Vec<Json> = trace
        .ranking(5)
        .into_iter()
        .map(|(h, s, e, c)| Json::obj().with("tgt_sha256", h).with("script", s).with("energy", e).with("instructions", c.instructions).with("size", c.size as u64))
        .collect();
    let id = format!("G{}x{}", g, &tgt.hash()[..12]);
    let module = agda::module_name(&id);
    let knot_t = trace.best_t;
    // OBLIGATIONS / CHECK
    let mut cert_tgt = tgt.clone();
    if cfg.fault == Fault::TamperCertificate {
        cert_tgt = tamper(&tgt);
    }
    let io: Vec<(Val, Val)> = best.io.clone();
    let spec = agda::CertSpec { id: id.clone(), src: &src, script: &script, tgt: &cert_tgt, knot_t, samples: &io };
    let text = agda::emit_cert(&spec);
    let r = agda::check(&cfg.agda_root(), &cfg.certs(), &module, &text);
    let file = cfg.certs().join(format!("{}.agda", module));
    let props = [
        "tgt-is : tgt ≡ (rewrite script applied to src)",
        "sound : tgt ≈ src  (∀ u → runMain tgt u ≡ runMain src u)",
        "knot : Invariant (coord (89·t) (2462·t))",
        "on-path : project t ≡ coord (89·t) (2462·t)",
        "phase-is : phase t ≡ 89·t mod 2462; phase-bound : phase t < 2462; phase-unique (t < 2462)",
        "exec-k : runMain tgt u ≡ v on sampled inputs",
    ];
    let man = cert_manifest(cfg, &module, &file, &props, &src, &cert_tgt, &r);
    write_json(&cfg.certs().join(format!("{}.json", module)), &man)?;
    let cert_sha = man.get("certificate_sha256").and_then(|x| x.str()).unwrap_or("").to_string();
    let checker = format!("agda-{}", agda::agda_version().unwrap_or_default().replace("Agda version ", ""));
    let outcome = if r.ok { "checked" } else { "rejected" };
    let mut proofs: Vec<ProofFact> = ["typed_ir_preservation", "rewrite_correctness", "execution_correspondence", "knot_validity", "phase_normalization"]
        .iter()
        .map(|o| ProofFact { obligation: o.to_string(), checker: checker.clone(), outcome: outcome.into(), sha256: cert_sha.clone() })
        .collect();
    // chain composition with the previous certificate (generation ≥ 2)
    let chain_required = !prev_module.is_empty() && prev_module != agda::module_name("Load");
    let mut chain_json = Json::Null;
    let mut chain_module: Option<String> = None;
    if chain_required {
        let cid = format!("Chain{}", g);
        let cmod = agda::module_name(&cid);
        let root = root_program(&rt)?;
        let pc = meta.get("chain_module").and_then(|x| x.str()).map(|s| s.trim_start_matches("Cert").to_string());
        let ct = agda::emit_chain(&cid, prev_module.trim_start_matches("Cert"), &id, pc.as_deref(), &agda::sig(&root));
        chain_module = Some(cmod.clone());
        let cr = if r.ok { agda::check(&cfg.agda_root(), &cfg.certs(), &cmod, &ct) } else { agda::CheckResult { ok: false, output: "not attempted: step certificate rejected".into(), millis: 0 } };
        let cfile = cfg.certs().join(format!("{}.agda", cmod));
        if !cfile.exists() {
            let _ = std::fs::write(&cfile, &ct);
        }
        let cm = cert_manifest(cfg, &cmod, &cfile, &["link : B.src ≡ A.tgt", "chain : B.tgt ≈ A.src", "root : B.tgt ≈ root-src (loaded program)"], &src, &tgt, &cr);
        write_json(&cfg.certs().join(format!("{}.json", cmod)), &cm)?;
        proofs.push(ProofFact {
            obligation: "chain_composition".into(),
            checker: checker.clone(),
            outcome: if cr.ok { "checked" } else { "rejected" }.into(),
            sha256: cm.get("certificate_sha256").and_then(|x| x.str()).unwrap_or("").to_string(),
        });
        chain_json = Json::obj().with("module", cmod).with("previous", prev_module.as_str()).with("ok", cr.ok).with("ms", cr.millis as u64).with("sha256", cm.get("certificate_sha256").cloned().unwrap_or(Json::Null));
    }
    // DATALOG
    let mig = runtime::migration(&src, &tgt, cfg.stateful);
    let diff_ok = !io.is_empty() && cfg.fault != Fault::ChangeStateType;
    let coord = tor.coord(knot_t).ok_or_else(|| format!("t={} outside the extracted torus table", knot_t))?;
    let facts = Facts {
        candidate: id.clone(),
        source: src.hash(),
        target: tgt.hash(),
        active: active.ir_sha256.clone(),
        proofs: proofs.clone(),
        observations: vec![
            ("differential_samples".into(), if diff_ok { "pass" } else { "fail" }.into()),
            ("state_migration".into(), if mig.is_ok() { "pass" } else { "fail" }.into()),
        ],
        topology: Some((knot_t, coord.0, coord.1, torus::phase(knot_t))),
        last_t,
        policy_flags: cfg.policy_flags.clone(),
        chain_required,
    };
    let gdir = cfg.work.join("gate").join(format!("g{}", g));
    let gr = gate::evaluate(&cfg.rules(), &facts, &gdir);
    let mut body = Json::obj()
        .with("kind", "generation")
        .with("generation", g)
        .with("candidate", id.as_str())
        .with("candidate_origin", if cfg.fault == Fault::None { "annealer".to_string() } else { format!("fault-injection:{:?}", cfg.fault) })
        .with("source_sha256", src.hash())
        .with("target_sha256", tgt.hash())
        .with("transformation", Json::obj().with("script", rewrite::script_text(&script)).with("description", rewrite::describe(&script)))
        .with(
            "obligations",
            Json::Arr(proofs.iter().map(|p| Json::obj().with("obligation", p.obligation.as_str()).with("certificate_sha256", p.sha256.as_str())).collect()),
        )
        .with(
            "checker",
            Json::obj()
                .with("agda", man.get("checker").cloned().unwrap_or(Json::Null))
                .with("module", module.as_str())
                .with("outcome", if r.ok { "checked" } else { "rejected" })
                .with("ms", r.millis as u64)
                .with("output_sha256", crate::sha256::hex(r.output.as_bytes()))
                .with("chain", chain_json),
        )
        .with(
            "datalog",
            Json::obj()
                .with("souffle", gate::souffle_version().unwrap_or_default())
                .with("rules_sha256", crate::sha256::file_hex(&cfg.rules()).unwrap_or_default())
                .with("facts_dir", gdir.display().to_string())
                .with("facts_sha256", gr.facts_sha256.as_str())
                .with("verdict", if gr.verdict == Verdict::Commit { "COMMIT" } else { "SILENCE" })
                .with("silence_reasons", Json::Arr(gr.reasons.iter().map(|s| Json::from(s.as_str())).collect()))
                .with("derived", Json::Arr(gr.derived.iter().map(|s| Json::from(s.as_str())).collect())),
        )
        .with(
            "anneal",
            Json::obj()
                .with("seed", Json::Num(prm.seed.to_string()))
                .with("t0", prm.t0)
                .with("cooling", prm.cooling)
                .with("t_min", prm.t_min)
                .with("iterations", prm.iterations as u64)
                .with("patience", prm.patience as u64)
                .with("max_steps", prm.max_steps)
                .with("proposal", "torus")
                .with("torus_t0", last_t)
                .with("proposed", trace.proposed as u64)
                .with("valid", trace.valid as u64)
                .with("accepted", trace.accepted as u64)
                .with("uphill_accepted", trace.uphill_accepted as u64)
                .with("improved", trace.improved as u64)
                .with("initial_energy", trace.initial_energy)
                .with("best_energy", trace.best_energy)
                .with("final_temperature", trace.final_temperature)
                .with("stop", trace.stop.as_str())
                .with("knot_t", knot_t)
                .with("knot_coord", Json::Arr(vec![Json::from(coord.0), Json::from(coord.1)]))
                .with("phase", torus::phase(knot_t))
                .with("torus_table_sha256", tor.header_sha256.as_str())
                .with("energy_key", format!("{:?}", energy::energy(&best.cost)))
                .with("ranking", Json::Arr(ranking)),
        )
        .with("state_migration", match &mig { Ok(s) => s.to_string(), Err(e) => format!("REJECTED: {}", e) });
    let finish = |body: Json, committed: bool, reason: String, version: u64| -> Result<Outcome, String> {
        let body = body.with("execution_version", version).with("decision", if committed { "COMMIT" } else { "REJECT" }).with("reason", reason.as_str());
        let rec = ledger.append(body.clone())?;
        Ok(Outcome { generation: g, committed, reason, record_hash: rec.hash, body })
    };
    if gr.verdict != Verdict::Commit {
        return finish(body, false, format!("SILENCE: {}", gr.reasons.join("; ")), active.id);
    }
    // COMPILE / VALIDATE
    let bdir = cfg.work.join("build");
    let mut built = native::compile(&tgt, &bdir, &format!("g{}", g))?;
    if cfg.fault == Fault::WrongNative {
        let other = tamper(&tgt);
        built = native::compile(&other, &bdir, &format!("g{}_wrong", g))?;
    }
    let val = native::validate(&built.binary, &src, &tgt, &validation_inputs(&src.main().arg, prm.seed))?;
    body = body.with(
        "native",
        Json::obj()
            .with("rustc", native::rustc_version().unwrap_or_default())
            .with("flags", "-O --edition 2021 -C overflow-checks=on")
            .with("source_sha256", built.source_sha256.as_str())
            .with("binary_sha256", built.binary_sha256.as_str())
            .with("validated_inputs", val.inputs)
            .with("agree_vm", val.agree_vm)
            .with("agree_reference", val.agree_reference)
            .with("reference_trapped", val.reference_trapped)
            .with("mismatches", Json::Arr(val.mismatches.iter().take(5).map(|s| Json::from(s.as_str())).collect())),
    );
    if !val.mismatches.is_empty() {
        return finish(body, false, format!("native validation failed on {} inputs; active version kept", val.mismatches.len()), active.id);
    }
    // ATOMIC ACTIVATE
    let vmeta = Json::obj().with("generation", g).with("cert_module", module.as_str()).with("knot_t", knot_t).with("script", rewrite::script_text(&script)).with("chain_module", chain_module.clone().map(Json::from).unwrap_or(Json::Null));
    let v = rt.stage(&tgt, &built, vmeta)?;
    rt.activate(&v)?;
    // post-activation check through the `active` link
    let post = native::validate(&rt.active_link().join("program"), &src, &tgt, &anneal::samples(&src.main().arg));
    let post_ok = matches!(&post, Ok(p) if p.mismatches.is_empty()) && cfg.fault != Fault::FailAfterActivate;
    if !post_ok {
        rt.rollback_to(&active)?;
        let now = rt.active().map(|a| a.id).unwrap_or(u64::MAX);
        body = body.with("rollback", Json::obj().with("from_version", v.id).with("to_version", now));
        return finish(body, false, "post-activation check failed; rolled back".into(), now);
    }
    // EXECUTE / MEASURE
    let x = bench_input(&src.main().arg);
    let before = measure(&src, &active.dir.join("program"), &x, cfg.bench_calls, cfg.bench_reps)?;
    let after = measure(&tgt, &rt.active_link().join("program"), &x, cfg.bench_calls, cfg.bench_reps)?;
    body = body.with("measurement", Json::obj().with("before", before).with("after", after));
    finish(body, true, "all obligations checked, gate COMMIT, native validated, activated".into(), v.id)
}

/// A different program of the same type (first literal perturbed, or the
/// main body wrapped in an extra addition) used by fault injection.
pub fn tamper(p: &Prog) -> Prog {
    let mut q = p.clone();
    let m = q.defs.len() - 1;
    let body = q.defs[m].body.clone();
    q.defs[m].body = match q.defs[m].ret {
        Ty::Int => Expr::Op2(Op2::AddZ, b(body), b(Expr::Lit(Val::Int(1)))),
        Ty::Nat => Expr::Op2(Op2::AddN, b(body), b(Expr::Lit(Val::Nat(1)))),
        Ty::Bool => Expr::Op1(Op1::NotB, b(body)),
        _ => Expr::Pair(b(Expr::Fst(b(body.clone()))), b(Expr::Snd(b(body)))),
    };
    q
}

/// The originally loaded program (version 0).
pub fn root_program(rt: &Runtime) -> Result<Prog, String> {
    let t = std::fs::read_to_string(rt.versions().join("v0000/program.ir")).map_err(|e| format!("version 0: {}", e))?;
    crate::parse::parse_canonical(&t)
}

fn find_version(rt: &Runtime, ir_sha: &str) -> Option<(PathBuf, Prog)> {
    let rd = std::fs::read_dir(rt.versions()).ok()?;
    let mut ds: Vec<PathBuf> = rd.filter_map(|e| e.ok()).map(|e| e.path()).collect();
    ds.sort();
    for d in ds {
        if let Ok(t) = std::fs::read_to_string(d.join("program.ir")) {
            if let Ok(p) = crate::parse::parse_canonical(&t) {
                if p.hash() == ir_sha {
                    return Some((d, p));
                }
            }
        }
    }
    None
}

#[derive(Debug, Default)]
pub struct ReplayReport {
    pub records: usize,
    pub lines: Vec<String>,
    pub failures: Vec<String>,
}

/// Replay and audit: verify the hash chain, then for every record re-hash
/// its certificates, re-check them with Agda in a fresh directory, re-run
/// Soufflé on the stored facts, re-derive the target from the recorded
/// script, re-run the annealer from its recorded seed, and check the version
/// store against its manifests.
pub fn replay(cfg: &Config, recheck: bool) -> ReplayReport {
    let mut rep = ReplayReport::default();
    let recs = match cfg.ledger().verify() {
        Ok(r) => r,
        Err(e) => {
            rep.failures.push(format!("ledger: {}", e));
            return rep;
        }
    };
    rep.records = recs.len();
    rep.lines.push(format!("ledger: {} records, hash chain verified, head {}", recs.len(), recs.last().map(|r| r.hash.as_str()).unwrap_or("-")));
    let rt = cfg.runtime();
    let fresh = cfg.work.join("replay");
    let _ = std::fs::remove_dir_all(&fresh);
    let _ = std::fs::create_dir_all(&fresh);
    // copy all certificate sources (no interfaces) so Agda re-checks them
    if let Ok(rd) = std::fs::read_dir(cfg.certs()) {
        for e in rd.filter_map(|e| e.ok()) {
            let p = e.path();
            if p.extension().map(|x| x == "agda").unwrap_or(false) {
                let _ = std::fs::copy(&p, fresh.join(p.file_name().unwrap()));
            }
        }
    }
    let fail = |rep: &mut ReplayReport, s: String| rep.failures.push(s);
    for r in &recs {
        let b = &r.body;
        let kind = b.get("kind").and_then(|x| x.str()).unwrap_or("");
        let seq = r.seq;
        if kind != "generation" {
            rep.lines.push(format!("#{} {}: {}", seq, kind, b.get("reason").and_then(|x| x.str()).unwrap_or("")));
            continue;
        }
        let decision = b.get("decision").and_then(|x| x.str()).unwrap_or("");
        // certificates re-hashed
        let mut certs_ok = true;
        if let Some(obs) = b.get("obligations").and_then(|x| x.arr()) {
            for o in obs {
                let want = o.get("certificate_sha256").and_then(|x| x.str()).unwrap_or("");
                let ob = o.get("obligation").and_then(|x| x.str()).unwrap_or("");
                let module = if ob == "chain_composition" {
                    b.get("checker").and_then(|c| c.get("chain")).and_then(|c| c.get("module")).and_then(|x| x.str()).unwrap_or("").to_string()
                } else {
                    b.get("checker").and_then(|c| c.get("module")).and_then(|x| x.str()).unwrap_or("").to_string()
                };
                let got = crate::sha256::file_hex(&cfg.certs().join(format!("{}.agda", module))).unwrap_or_default();
                if got != want {
                    certs_ok = false;
                    fail(&mut rep, format!("#{} {}: certificate {} hash {} != recorded {}", seq, ob, module, got, want));
                }
            }
        }
        // re-check with Agda
        let mut agda_line = String::from("agda: skipped");
        if recheck {
            let module = b.get("checker").and_then(|c| c.get("module")).and_then(|x| x.str()).unwrap_or("").to_string();
            let recorded = b.get("checker").and_then(|c| c.get("outcome")).and_then(|x| x.str()).unwrap_or("");
            let mut mods = vec![(module, recorded == "checked")];
            if let Some(c) = b.get("checker").and_then(|c| c.get("chain")) {
                if let (Some(m), Some(ok)) = (c.get("module").and_then(|x| x.str()), c.get("ok").and_then(|x| x.boolean())) {
                    mods.push((m.to_string(), ok));
                }
            }
            let mut parts = Vec::new();
            for (m, want_ok) in mods {
                let text = std::fs::read_to_string(fresh.join(format!("{}.agda", m))).unwrap_or_default();
                let cr = agda::check(&cfg.agda_root(), &fresh, &m, &text);
                if cr.ok != want_ok {
                    fail(&mut rep, format!("#{} agda re-check of {}: ok={} but recorded ok={}\n{}", seq, m, cr.ok, want_ok, cr.output));
                }
                parts.push(format!("{} {} ({} ms)", m, if cr.ok { "checked" } else { "rejected" }, cr.millis));
            }
            agda_line = format!("agda: {}", parts.join(", "));
        }
        // re-run Soufflé on the stored facts
        let dl = b.get("datalog");
        let fdir = PathBuf::from(dl.and_then(|d| d.get("facts_dir")).and_then(|x| x.str()).unwrap_or(""));
        let want_v = dl.and_then(|d| d.get("verdict")).and_then(|x| x.str()).unwrap_or("").to_string();
        let out = fresh.join(format!("gate{}", seq));
        let _ = std::fs::create_dir_all(&out);
        let so = std::process::Command::new("souffle").arg("-F").arg(&fdir).arg("-D").arg(&out).arg(cfg.rules()).output();
        let pv = std::fs::read_to_string(out.join("policy_verdict.csv")).unwrap_or_default();
        let sr = std::fs::read_to_string(out.join("silence_reason.csv")).unwrap_or_default();
        let got_v = if so.map(|o| o.status.success()).unwrap_or(false) && pv.lines().count() == 1 && pv.contains("\tCOMMIT") && sr.trim().is_empty() { "COMMIT" } else { "SILENCE" };
        if got_v != want_v {
            fail(&mut rep, format!("#{} datalog re-run gave {} but recorded {}", seq, got_v, want_v));
        }
        // re-derive the target from the recorded script
        let src_sha = b.get("source_sha256").and_then(|x| x.str()).unwrap_or("");
        let tgt_sha = b.get("target_sha256").and_then(|x| x.str()).unwrap_or("");
        let script_s = b.get("transformation").and_then(|t| t.get("script")).and_then(|x| x.str()).unwrap_or("");
        let mut derive = String::from("script: source version not found");
        let mut anneal_line = String::new();
        if let Some((_, src)) = find_version(&rt, src_sha) {
            match rewrite::parse_script(script_s).and_then(|s| rewrite::apply_script(&src, &s)) {
                Ok(t) if t.hash() == tgt_sha => derive = "script reproduces target".into(),
                Ok(t) => {
                    if b.get("candidate_origin").and_then(|x| x.str()) == Some("annealer") {
                        fail(&mut rep, format!("#{} script gives {} not recorded target {}", seq, t.hash(), tgt_sha));
                    }
                    derive = "script does not reproduce target (hand-built candidate)".into()
                }
                Err(e) => fail(&mut rep, format!("#{} script replay: {}", seq, e)),
            }
            // annealer determinism
            let a = b.get("anneal");
            let seed: u64 = a.and_then(|a| a.get("seed")).and_then(|x| x.u64()).unwrap_or(0);
            let t0 = a.and_then(|a| a.get("torus_t0")).and_then(|x| x.u64()).unwrap_or(0);
            let it = a.and_then(|a| a.get("iterations")).and_then(|x| x.u64()).unwrap_or(0) as u32;
            let prm = Params { seed, iterations: it, proposal: Proposal::Torus { t0 }, ..Params::default() };
            match anneal::anneal(&src, &prm) {
                Ok((best, tr)) => {
                    let same = tr.best_t == a.and_then(|a| a.get("knot_t")).and_then(|x| x.u64()).unwrap_or(u64::MAX)
                        && tr.proposed as u64 == a.and_then(|a| a.get("proposed")).and_then(|x| x.u64()).unwrap_or(u64::MAX)
                        && tr.accepted as u64 == a.and_then(|a| a.get("accepted")).and_then(|x| x.u64()).unwrap_or(u64::MAX);
                    let tgt_same = best.tgt.hash() == tgt_sha;
                    if !same {
                        fail(&mut rep, format!("#{} annealer replay diverged (t={}, proposed={}, accepted={})", seq, tr.best_t, tr.proposed, tr.accepted));
                    }
                    anneal_line = format!("anneal replay: {} (best_t={}, proposed={}, accepted={}, target {})", if same { "identical" } else { "DIVERGED" }, tr.best_t, tr.proposed, tr.accepted, if tgt_same { "identical" } else { "differs (fault-injected candidate)" });
                }
                Err(e) => fail(&mut rep, format!("#{} anneal replay: {}", seq, e)),
            }
        } else {
            fail(&mut rep, format!("#{} source {} not in version store", seq, src_sha));
        }
        rep.lines.push(format!(
            "#{} {} {}: certificates {}; {}; datalog {} (recorded {}); {}; {}",
            seq,
            b.get("candidate").and_then(|x| x.str()).unwrap_or(""),
            decision,
            if certs_ok { "re-hashed OK" } else { "HASH MISMATCH" },
            agda_line,
            got_v,
            want_v,
            derive,
            anneal_line
        ));
    }
    // version store integrity
    if let Ok(rd) = std::fs::read_dir(rt.versions()) {
        let mut ds: Vec<PathBuf> = rd.filter_map(|e| e.ok()).map(|e| e.path()).collect();
        ds.sort();
        for d in ds {
            let m = std::fs::read_to_string(d.join("manifest.json")).ok().and_then(|s| Json::parse(&s).ok());
            let ir = std::fs::read_to_string(d.join("program.ir")).ok().and_then(|t| crate::parse::parse_canonical(&t).ok());
            let bin = crate::sha256::file_hex(&d.join("program")).unwrap_or_default();
            match (m, ir) {
                (Some(m), Some(p)) if m.get("ir_sha256").and_then(|x| x.str()) == Some(p.hash().as_str()) && m.get("binary_sha256").and_then(|x| x.str()) == Some(bin.as_str()) => {
                    rep.lines.push(format!("version {}: manifest, IR and binary hashes consistent", d.file_name().unwrap().to_string_lossy()));
                }
                _ => fail(&mut rep, format!("version {}: manifest does not match contents", d.display())),
            }
        }
    }
    if let Some(a) = rt.active() {
        rep.lines.push(format!("active: v{:04} ir {}", a.id, a.ir_sha256));
    }
    rep
}
