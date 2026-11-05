// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Agda certificate emission and checking.
//!
//! A morph certificate is an Agda module, compiled with `--safe` (so no
//! postulates, holes, or unsafe pragmas are accepted), containing:
//!   * `src`, `tgt` as intrinsically typed programs (typed IR preservation:
//!     both must check at the same main type);
//!   * `tgt-is : tgt ≡ <script> src` by `refl` (the Rust rewrite output is
//!     exactly what the Agda rewrite functions compute);
//!   * `sound : tgt ≈ src` composed from the general soundness lemmas of
//!     Morph.Rewrite (rewrite correctness);
//!   * `knot`, `on-path`, `phase-is`, `phase-bound`, `phase-unique`
//!     (knot validity and phase normalization of the candidate coordinate);
//!   * `exec-k : runMain tgt uₖ ≡ vₖ` by `refl` for the sampled inputs, where
//!     vₖ is what the Rust VM produced (execution correspondence on samples).
//! Chain modules compose consecutive certificates with ≈-trans.

use crate::ir::*;
use crate::rewrite::{Pass, Script, Step};
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn ty(t: &Ty) -> String {
    match t {
        Ty::Nat => "nat".into(),
        Ty::Int => "int".into(),
        Ty::Bool => "bool".into(),
        Ty::Prod(a, b) => format!("({} ⊗ {})", ty(a), ty(b)),
        Ty::Sum(a, b) => format!("({} ⊕ {})", ty(a), ty(b)),
    }
}

pub fn int_lit(i: i64) -> String {
    if i >= 0 {
        format!("(+ {})", i)
    } else {
        // -[1+ n ] denotes -(n+1)
        let n = (-(i as i128) - 1) as u128;
        format!("(-[1+ {} ])", n)
    }
}

pub fn val(v: &Val) -> String {
    match v {
        Val::Nat(n) => n.to_string(),
        Val::Int(i) => int_lit(*i),
        Val::Bool(b) => if *b { "true".into() } else { "false".into() },
        Val::Pair(a, c) => format!("({} , {})", val(a), val(c)),
        Val::Inl(a) => format!("(inj₁ {})", val(a)),
        Val::Inr(a) => format!("(inj₂ {})", val(a)),
    }
}

fn base_witness(v: &Val) -> &'static str {
    match v {
        Val::Nat(_) => "nat",
        Val::Int(_) => "int",
        Val::Bool(_) => "bool",
        _ => unreachable!("literals are base-typed"),
    }
}

pub fn mem(k: usize) -> String {
    let mut s = "here".to_string();
    for _ in 0..k {
        s = format!("(there {})", s);
    }
    s
}

pub fn expr(e: &Expr) -> String {
    use Expr::*;
    match e {
        Lit(v) => format!("(lit {} {})", base_witness(v), val(v)),
        Var(k) => format!("(var {})", mem(*k)),
        Op1(o, a) => format!("(op1 {} {})", o.name(), expr(a)),
        Op2(o, a, c) => format!("(op2 {} {} {})", o.name(), expr(a), expr(c)),
        Ite(c, x, y) => format!("(ite {} {} {})", expr(c), expr(x), expr(y)),
        Let(x, body) => format!("(let′ {} {})", expr(x), expr(body)),
        Pair(x, y) => format!("(pair {} {})", expr(x), expr(y)),
        Fst(x) => format!("(fst {})", expr(x)),
        Snd(x) => format!("(snd {})", expr(x)),
        Inl(t, x) => format!("(inl {{b = {}}} {})", ty(t), expr(x)),
        Inr(t, x) => format!("(inr {{a = {}}} {})", ty(t), expr(x)),
        Case(x, l, r) => format!("(case {} {} {})", expr(x), expr(l), expr(r)),
        Iter(n, z, s) => format!("(iter {} {} {})", expr(n), expr(z), expr(s)),
        Call(j, x) => format!("(call {} {})", mem(*j), expr(x)),
    }
}

pub fn sig(p: &Prog) -> String {
    let mut s = String::from("[]");
    for d in &p.defs {
        s = format!("(({} , {}) ∷ {})", ty(&d.arg), ty(&d.ret), s);
    }
    s
}

pub fn prog(p: &Prog) -> String {
    let mut s = String::from("[]");
    for d in &p.defs {
        s = format!("({}\n    ▷ {})", s, expr(&d.body));
    }
    s
}

fn passes(ps: &[Pass]) -> String {
    let mut s = String::from("[]");
    for p in ps.iter().rev() {
        s = format!("({} ∷ {})", p.agda(), s);
    }
    s
}

pub struct CertSpec<'a> {
    pub id: String,
    pub src: &'a Prog,
    pub script: &'a Script,
    pub tgt: &'a Prog,
    pub knot_t: u64,
    pub samples: &'a [(Val, Val)],
}

pub const HEADER: &str = "-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0\n-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab\n";

const IMPORTS: &str = "open import Data.Nat using (ℕ; _<_; _<?_)
open import Data.Integer using (+_; -[1+_])
open import Data.Bool using (true; false)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Relation.Nullary.Decidable using (toWitness)
open import Morph.IR
open import Morph.Rewrite
open import Morph.Topology
";

pub fn module_name(id: &str) -> String {
    format!("Cert{}", id)
}

pub fn emit_cert(c: &CertSpec) -> String {
    let mut o = String::new();
    o.push_str(HEADER);
    o.push_str("-- GENERATED morph certificate. Checked with --safe.\n");
    o.push_str(&format!("-- src sha256 {}\n-- tgt sha256 {}\n", c.src.hash(), c.tgt.hash()));
    o.push_str("{-# OPTIONS --safe #-}\n");
    o.push_str(&format!("module {} where\n\n", module_name(&c.id)));
    o.push_str(IMPORTS);
    o.push('\n');
    o.push_str(&format!("src : Prog {}\nsrc = {}\n\n", sig(c.src), prog(c.src)));
    // stages
    let mut prev = "src".to_string();
    let mut proofs: Vec<String> = Vec::new();
    for (k, st) in c.script.iter().enumerate() {
        let name = format!("stage{}", k + 1);
        match st {
            Step::Passes(ps) => {
                o.push_str(&format!("{} = runPasses {} {}\n", name, passes(ps), prev));
                proofs.push(format!("passes-≈ {} {}", passes(ps), prev));
            }
            Step::Spec { j, v } => {
                o.push_str(&format!("{} = specP {} {} {} {}\n", name, prev, mem(*j), base_witness(v), val(v)));
                proofs.push(format!("specP-≈ {} {} {} {}", prev, mem(*j), base_witness(v), val(v)));
            }
        }
        prev = name;
    }
    o.push('\n');
    o.push_str(&format!("tgt : Prog {}\ntgt = {}\n\n", sig(c.tgt), prog(c.tgt)));
    o.push_str(&format!("-- rewrite script reproduces the target exactly\ntgt-is : tgt ≡ {}\ntgt-is = refl\n\n", prev));
    // per-stage soundness, then left-nested ≈-trans with explicit programs
    // (≈ is a function type, so its program indices are not inferable).
    let sound = if proofs.is_empty() {
        "≈-refl {P = src}".to_string()
    } else {
        for (k, p) in proofs.iter().enumerate() {
            let here = format!("stage{}", k + 1);
            let before = if k == 0 { "src".to_string() } else { format!("stage{}", k) };
            o.push_str(&format!("step{k1} : {here} ≈ {before}\nstep{k1} = {p}\n\n", k1 = k + 1));
            if k == 0 {
                o.push_str("upto1 : stage1 ≈ src\nupto1 = step1\n\n");
            } else {
                o.push_str(&format!(
                    "upto{k1} : {here} ≈ src\nupto{k1} = ≈-trans {{P = {here}}} {{Q = {before}}} {{R = src}} step{k1} upto{k}\n\n",
                    k1 = k + 1,
                    k = k
                ));
            }
        }
        format!("upto{}", proofs.len())
    };
    o.push_str(&format!("-- semantic preservation (observational equivalence on main)\nsound : tgt ≈ src\nsound = {}\n\n", sound));
    let t = c.knot_t;
    let (m, l) = (89u128 * t as u128, 2462u128 * t as u128);
    let ph = (89u128 * t as u128) % 2462;
    o.push_str(&format!(
        "-- knot validity and phase normalization of the candidate coordinate\nknot : Invariant (coord {m} {l})\nknot = refl\n\non-path : project {t} ≡ coord {m} {l}\non-path = refl\n\nphase-is : phase {t} ≡ {ph}\nphase-is = refl\n\nphase-bound : phase {t} < 2462\nphase-bound = phase< {t}\n\n"
    ));
    if t < 2462 {
        o.push_str(&format!(
            "phase-unique : ∀ {{t′}} → t′ < 2462 → phase t′ ≡ {ph} → t′ ≡ {t}\nphase-unique h e = phase-injective h (toWitness {{a? = {t} <? 2462}} tt) (trans e (sym phase-is))\n\n"
        ));
    }
    o.push_str("-- execution correspondence on sampled inputs (outputs produced by the Rust VM)\n");
    for (k, (u, v)) in c.samples.iter().enumerate() {
        o.push_str(&format!("exec-{k} : runMain tgt {} ≡ {}\nexec-{k} = refl\n\n", val(u), val(v)));
    }
    o
}

pub fn emit_chain(id: &str, a: &str, bmod: &str, prev_chain: Option<&str>, root_sig: &str) -> String {
    // a: earlier certificate (src1 → tgt1); b: later (src2 = tgt1 → tgt2).
    // prev_chain: the chain module of the previous generation, whose `root`
    // relates tgt1 to the originally loaded program.
    let mut o = String::new();
    o.push_str(HEADER);
    o.push_str("-- GENERATED chain composition certificate.\n{-# OPTIONS --safe #-}\n");
    o.push_str(&format!("module {} where\n\n", module_name(id)));
    o.push_str("open import Data.Nat using (ℕ)\nopen import Data.Integer using (ℤ)\nopen import Data.Product using (_,_)\nopen import Data.List using ([]; _∷_)\nopen import Relation.Binary.PropositionalEquality using (_≡_; refl)\nopen import Morph.IR\nopen import Morph.Rewrite\n");
    o.push_str(&format!("import {} as A\nimport {} as B\n", module_name(a), module_name(bmod)));
    if let Some(pc) = prev_chain {
        o.push_str(&format!("import {} as PC\n", module_name(pc)));
    }
    o.push_str("\nlink : B.src ≡ A.tgt\nlink = refl\n\n");
    o.push_str("chain : B.tgt ≈ A.src\nchain = ≈-trans {P = B.tgt} {Q = B.src} {R = A.src} B.sound A.sound\n\n");
    o.push_str(&format!("root-src : Prog {}\n", root_sig));
    match prev_chain {
        None => {
            o.push_str("root-src = A.src\n\n-- the newest target is equivalent to the originally loaded program\nroot : B.tgt ≈ root-src\nroot = chain\n");
        }
        Some(_) => {
            o.push_str("root-src = PC.root-src\n\n-- the newest target is equivalent to the originally loaded program\nroot : B.tgt ≈ root-src\nroot = ≈-trans {P = B.tgt} {Q = A.tgt} {R = root-src} B.sound PC.root\n");
        }
    }
    o
}

#[derive(Clone, Debug)]
pub struct CheckResult {
    pub ok: bool,
    pub output: String,
    pub millis: u128,
}

pub fn agda_version() -> Option<String> {
    let o = Command::new("agda").arg("--version").output().ok()?;
    Some(String::from_utf8_lossy(&o.stdout).lines().next()?.trim().to_string())
}

/// Write `text` to `<dir>/<module>.agda` and check it with Agda.
pub fn check(agda_root: &Path, dir: &Path, module: &str, text: &str) -> CheckResult {
    let t0 = std::time::Instant::now();
    if let Err(e) = std::fs::create_dir_all(dir) {
        return CheckResult { ok: false, output: format!("mkdir: {}", e), millis: 0 };
    }
    if text.contains("postulate") || text.contains("{!") || !text.contains("{-# OPTIONS --safe #-}") {
        return CheckResult { ok: false, output: "certificate text rejected: postulate/hole/unsafe".into(), millis: 0 };
    }
    let path: PathBuf = dir.join(format!("{}.agda", module));
    if let Err(e) = std::fs::write(&path, text) {
        return CheckResult { ok: false, output: format!("write: {}", e), millis: 0 };
    }
    let out = Command::new("agda")
        .arg("-i")
        .arg(agda_root)
        .arg("-i")
        .arg(dir)
        .arg(&path)
        .current_dir(dir)
        .output();
    let millis = t0.elapsed().as_millis();
    match out {
        Err(e) => CheckResult { ok: false, output: format!("agda not runnable: {}", e), millis },
        Ok(o) => {
            let mut s = String::from_utf8_lossy(&o.stdout).into_owned();
            s.push_str(&String::from_utf8_lossy(&o.stderr));
            CheckResult { ok: o.status.success(), output: s, millis }
        }
    }
}

/// Certificate for LOAD: the source program is a well-typed term of the
/// intrinsically typed IR (typed_ir_preservation for the initial version),
/// and its main agrees with the reference outputs on the sampled inputs.
pub fn emit_load(id: &str, p: &Prog, samples: &[(Val, Val)]) -> String {
    let mut o = String::new();
    o.push_str(HEADER);
    o.push_str("-- GENERATED load certificate. Checked with --safe.\n");
    o.push_str(&format!("-- src sha256 {}\n", p.hash()));
    o.push_str("{-# OPTIONS --safe #-}\n");
    o.push_str(&format!("module {} where\n\n", module_name(id)));
    o.push_str(IMPORTS);
    o.push('\n');
    o.push_str(&format!("src : Prog {}\nsrc = {}\n\ntgt : Prog {}\ntgt = src\n\nsound : tgt ≈ src\nsound = ≈-refl {{P = src}}\n\n", sig(p), prog(p), sig(p)));
    for (k, (u, v)) in samples.iter().enumerate() {
        o.push_str(&format!("exec-{k} : runMain src {} ≡ {}\nexec-{k} = refl\n\n", val(u), val(v)));
    }
    o
}

/// sha256 of every Agda module a certificate depends on (dependency
/// identities recorded with each certificate).
pub fn dependencies(agda_root: &Path) -> Vec<(String, String)> {
    ["Morph/IR.agda", "Morph/Subst.agda", "Morph/Rewrite.agda", "Morph/Topology.agda"]
        .iter()
        .map(|f| (f.to_string(), crate::sha256::file_hex(&agda_root.join(f)).unwrap_or_else(|_| "missing".into())))
        .collect()
}

/// Version of the standard library found by Agda (from its .agda-lib file).
pub fn stdlib_identity() -> String {
    let home = std::env::var("HOME").unwrap_or_default();
    let libs = std::fs::read_to_string(format!("{}/.agda/libraries", home)).unwrap_or_default();
    for l in libs.lines() {
        let l = l.trim();
        if l.contains("standard-library") {
            if let Ok(t) = std::fs::read_to_string(l) {
                let name = t.lines().find(|x| x.starts_with("name:")).unwrap_or("").to_string();
                return format!("{} ({})", name.trim(), l);
            }
        }
    }
    "unknown".into()
}
