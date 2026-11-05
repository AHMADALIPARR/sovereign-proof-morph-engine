// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! L1 LiquidHaskell interface.
//!
//! Engine A emits, for each translated theorem whose binders and result are
//! first-order scalars or pairs of them, a Haskell function whose refinement
//! type states the proposition (`{v:Bool | v}` over `lhs == rhs`), and runs
//! the LiquidHaskell GHC plugin on the module. The outcome is recorded per
//! theorem as a refinement check. It never changes a theorem's proof
//! status: only Agda and Lean results are proof authority.
//!
//! Toolchain discovery (overridable by environment):
//!   SPME_LH_GHC     GHC the plugin was built with  (default ~/.ghcup/bin/ghc-9.6.3)
//!   SPME_LH_PKGDB   package db holding liquidhaskell (default ~/.local/state/cabal/store/ghc-9.6.3/package.db)
//!   SPME_Z3_DIR     directory containing z3 if it is not on PATH
use crate::ir::*;
use std::path::{Path, PathBuf};
use std::process::Command;

fn home() -> PathBuf {
    PathBuf::from(std::env::var("HOME").unwrap_or_else(|_| "/root".into()))
}

pub fn ghc() -> PathBuf {
    std::env::var("SPME_LH_GHC").map(PathBuf::from).unwrap_or_else(|_| home().join(".ghcup/bin/ghc-9.6.3"))
}

pub fn pkgdb() -> PathBuf {
    std::env::var("SPME_LH_PKGDB").map(PathBuf::from).unwrap_or_else(|_| home().join(".local/state/cabal/store/ghc-9.6.3/package.db"))
}

fn path_env() -> String {
    let mut p = std::env::var("PATH").unwrap_or_default();
    for d in [std::env::var("SPME_Z3_DIR").ok(), Some("/workspace/z3bin".into())].into_iter().flatten() {
        if Path::new(&d).join("z3").exists() {
            p = format!("{}:{}", d, p);
        }
    }
    p
}

/// `liquidhaskell-X` as registered in the package db, or None.
pub fn version() -> Option<String> {
    let db = pkgdb();
    let rd = std::fs::read_dir(&db).ok()?;
    let mut v: Vec<String> = rd
        .filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.starts_with("liquidhaskell-0") || (n.starts_with("liquidhaskell-") && n.as_bytes().get(14).map_or(false, |c| c.is_ascii_digit())))
        .map(|n| {
            let parts: Vec<&str> = n.trim_end_matches(".conf").split('-').collect();
            format!("{}-{}", parts[0], parts.get(1).unwrap_or(&"?"))
        })
        .collect();
    v.sort();
    v.pop()
}

#[derive(Debug, Clone)]
pub struct LhRun {
    pub ok: bool,
    pub exit: Option<i32>,
    pub output: String,
    pub error_lines: Vec<usize>,
}

/// Run the LiquidHaskell plugin on one module file.
pub fn check_file(file: &Path, build: &Path) -> LhRun {
    let _ = std::fs::create_dir_all(build);
    let r = Command::new(ghc())
        .env("PATH", path_env())
        .arg("-package-db")
        .arg(pkgdb())
        .args(["-package", "liquidhaskell", "-fplugin=LiquidHaskell", "-fforce-recomp", "-c"])
        .arg("-outputdir")
        .arg(build)
        .arg(file)
        .output();
    match r {
        Err(e) => LhRun { ok: false, exit: None, output: format!("cannot run {}: {}", ghc().display(), e), error_lines: vec![] },
        Ok(o) => {
            let out = format!("{}{}", String::from_utf8_lossy(&o.stdout), String::from_utf8_lossy(&o.stderr));
            let out = strip_ansi(&out);
            let name = file.file_name().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
            let mut lines = vec![];
            for l in out.lines() {
                if let Some(rest) = l.split(&format!("{}:", name)).nth(1) {
                    if rest.contains("error") {
                        if let Some(n) = rest.split(':').next().and_then(|x| x.parse().ok()) {
                            lines.push(n);
                        }
                    }
                }
            }
            let ok = o.status.success() && out.contains("LIQUID: SAFE");
            LhRun { ok, exit: o.status.code(), output: out, error_lines: lines }
        }
    }
}

fn strip_ansi(s: &str) -> String {
    let mut r = String::new();
    let mut it = s.chars().peekable();
    while let Some(c) = it.next() {
        if c == '\u{1b}' {
            for d in it.by_ref() {
                if d.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            r.push(c);
        }
    }
    r
}

pub fn lh_type(t: &Ty) -> Result<(String, String), String> {
    Ok(match t {
        Ty::Nat => ("N".into(), "Integer".into()),
        Ty::Int => ("Integer".into(), "Integer".into()),
        Ty::Bool => ("Bool".into(), "Bool".into()),
        Ty::Prod(a, b) => {
            let (la, ha) = lh_type(a)?;
            let (lb, hb) = lh_type(b)?;
            (format!("({}, {})", la, lb), format!("({}, {})", ha, hb))
        }
        Ty::Sum(..) => return Err("sum types are not representable as refinements here".into()),
    })
}

/// IR expression → Haskell expression; `env` innermost-last.
pub fn hs_expr(e: &Expr, env: &mut Vec<String>, fresh: &mut usize) -> Result<String, String> {
    use Expr::*;
    Ok(match e {
        Lit(Val::Nat(n)) => format!("({} :: Integer)", n),
        Lit(Val::Int(i)) => format!("({} :: Integer)", i),
        Lit(Val::Bool(b)) => (if *b { "True" } else { "False" }).into(),
        Lit(v) => return Err(format!("literal {} not representable", v)),
        Var(i) => env.get(env.len().wrapping_sub(1 + i)).cloned().ok_or("unbound variable")?,
        Op1(o, a) => {
            let x = hs_expr(a, env, fresh)?;
            match o {
                crate::ir::Op1::NegZ => format!("(negate {})", x),
                crate::ir::Op1::NotB => format!("(not {})", x),
                crate::ir::Op1::ToInt => x,
            }
        }
        Op2(o, a, b) => {
            let x = hs_expr(a, env, fresh)?;
            let y = hs_expr(b, env, fresh)?;
            use crate::ir::Op2::*;
            match o {
                SubN => format!("(subN {} {})", x, y),
                AddN | AddZ => format!("({} + {})", x, y),
                MulN | MulZ => format!("({} * {})", x, y),
                SubZ => format!("({} - {})", x, y),
                LtN | LtZ => format!("({} < {})", x, y),
                EqN | EqZ => format!("({} == {})", x, y),
                AndB => format!("({} && {})", x, y),
                OrB => format!("({} || {})", x, y),
            }
        }
        Ite(c, a, b) => format!("(if {} then {} else {})", hs_expr(c, env, fresh)?, hs_expr(a, env, fresh)?, hs_expr(b, env, fresh)?),
        Let(a, b) => {
            let x = hs_expr(a, env, fresh)?;
            *fresh += 1;
            let n = format!("l{}", fresh);
            env.push(n.clone());
            let r = hs_expr(b, env, fresh);
            env.pop();
            format!("(let {} = {} in {})", n, x, r?)
        }
        Pair(a, b) => format!("({}, {})", hs_expr(a, env, fresh)?, hs_expr(b, env, fresh)?),
        Fst(a) => format!("(fst {})", hs_expr(a, env, fresh)?),
        Snd(a) => format!("(snd {})", hs_expr(a, env, fresh)?),
        Inl(..) | Inr(..) | Case(..) => return Err("sum values are not representable as refinements here".into()),
        Iter(..) => return Err("iteration is not representable as a refinement (no loop invariant)".into()),
        Call(..) => return Err("calls between definitions are not representable here".into()),
    })
}

/// One lemma: `name u = lhs == rhs` with result refinement `{v:Bool | v}`.
pub fn lemma(name: &str, l: &Prog, r: &Prog) -> Result<String, String> {
    if l.defs.len() != 1 || r.defs.len() != 1 {
        return Err("multi-definition programs are not representable here".into());
    }
    let (ld, rd) = (&l.defs[0], &r.defs[0]);
    if matches!(ld.ret, Ty::Prod(..) | Ty::Sum(..)) {
        return Err("compound results are not compared by refinement here".into());
    }
    let (lt, ht) = lh_type(&ld.arg)?;
    let mut fresh = 0;
    let lhs = hs_expr(&ld.body, &mut vec!["u".into()], &mut fresh)?;
    let rhs = hs_expr(&rd.body, &mut vec!["u".into()], &mut fresh)?;
    Ok(format!("{{-@ {n} :: u:{lt} -> {{v:Bool | v}} @-}}\n{n} :: {ht} -> Bool\n{n} u = {lhs} == {rhs}\n", n = name, lt = lt, ht = ht, lhs = lhs, rhs = rhs))
}

pub fn module_header(module: &str) -> String {
    format!(
        "-- Generated by Engine A (spme). Refinement obligations only; not proof authority.\n{{-# OPTIONS_GHC -Wno-unused-matches #-}}\nmodule {} where\n\n{{-@ type N = {{v:Integer | 0 <= v}} @-}}\n\n{{-@ subN :: a:N -> b:N -> {{v:N | (a >= b => v == a - b) && (a < b => v == 0)}} @-}}\nsubN :: Integer -> Integer -> Integer\nsubN a b = if a >= b then a - b else 0\n\n",
        module
    )
}
