// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Engine B rewrites. Each function here is a transcription of the
//! corresponding definition in `agda/Morph/Rewrite.agda`, so that for every
//! candidate the Agda checker can confirm `tgt ≡ script src` by normalization
//! and then obtain `tgt ≈ src` from the general soundness lemmas. Rust is not
//! trusted here: if this file diverged from the Agda definitions the
//! certificate would fail to check and the candidate would be silenced.

use crate::eval::{ev1, ev2, EvalError};
use crate::ir::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Pass {
    Cf,
    Alg,
    Dce,
    Fuse,
    Pe(u64),
}

impl Pass {
    pub fn agda(&self) -> String {
        match self {
            Pass::Cf => "cf".into(),
            Pass::Alg => "alg".into(),
            Pass::Dce => "dce".into(),
            Pass::Fuse => "fuse".into(),
            Pass::Pe(k) => format!("(pe {})", k),
        }
    }
    pub fn name(&self) -> String {
        match self {
            Pass::Cf => "constant-folding".into(),
            Pass::Alg => "algebraic-simplification".into(),
            Pass::Dce => "dead-code-elimination".into(),
            Pass::Fuse => "expression-fusion".into(),
            Pass::Pe(k) => format!("partial-evaluation(k={})", k),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Step {
    Passes(Vec<Pass>),
    /// Specialize main's calls `call j (pair e (lit v))` to a new function.
    Spec { j: usize, v: Val },
}

pub type Script = Vec<Step>;

pub fn describe(s: &Script) -> String {
    s.iter()
        .map(|st| match st {
            Step::Passes(ps) => ps.iter().map(|p| p.name()).collect::<Vec<_>>().join(" ; "),
            Step::Spec { j, v } => format!("specialize(call {} , {})", j, v),
        })
        .collect::<Vec<_>>()
        .join(" ; ")
}

type RR = Result<Expr, EvalError>;

// ------------------------------------------------------------ substitution

pub fn shift(e: &Expr, by: usize, cutoff: usize) -> Expr {
    use Expr::*;
    let s = |x: &Expr, c: usize| b(shift(x, by, c));
    match e {
        Lit(v) => Lit(v.clone()),
        Var(k) => Var(if *k >= cutoff { k + by } else { *k }),
        Op1(o, a) => Op1(*o, s(a, cutoff)),
        Op2(o, a, x) => Op2(*o, s(a, cutoff), s(x, cutoff)),
        Ite(c, x, y) => Ite(s(c, cutoff), s(x, cutoff), s(y, cutoff)),
        Let(x, body) => Let(s(x, cutoff), s(body, cutoff + 1)),
        Pair(x, y) => Pair(s(x, cutoff), s(y, cutoff)),
        Fst(x) => Fst(s(x, cutoff)),
        Snd(x) => Snd(s(x, cutoff)),
        Inl(t, x) => Inl(t.clone(), s(x, cutoff)),
        Inr(t, x) => Inr(t.clone(), s(x, cutoff)),
        Case(x, l, r) => Case(s(x, cutoff), s(l, cutoff + 1), s(r, cutoff + 1)),
        Iter(n, z, st) => Iter(s(n, cutoff), s(z, cutoff), s(st, cutoff + 2)),
        Call(j, x) => Call(*j, s(x, cutoff)),
    }
}

/// `subst σ e` with σ given on free indices; binders use `exts`.
pub fn subst(e: &Expr, sigma: &dyn Fn(usize) -> Expr, depth: usize) -> Expr {
    use Expr::*;
    let s = |x: &Expr, d: usize| b(subst(x, sigma, d));
    match e {
        Lit(v) => Lit(v.clone()),
        Var(k) => {
            if *k < depth {
                Var(*k)
            } else {
                shift(&sigma(k - depth), depth, 0)
            }
        }
        Op1(o, a) => Op1(*o, s(a, depth)),
        Op2(o, a, x) => Op2(*o, s(a, depth), s(x, depth)),
        Ite(c, x, y) => Ite(s(c, depth), s(x, depth), s(y, depth)),
        Let(x, body) => Let(s(x, depth), s(body, depth + 1)),
        Pair(x, y) => Pair(s(x, depth), s(y, depth)),
        Fst(x) => Fst(s(x, depth)),
        Snd(x) => Snd(s(x, depth)),
        Inl(t, x) => Inl(t.clone(), s(x, depth)),
        Inr(t, x) => Inr(t.clone(), s(x, depth)),
        Case(x, l, r) => Case(s(x, depth), s(l, depth + 1), s(r, depth + 1)),
        Iter(n, z, st) => Iter(s(n, depth), s(z, depth), s(st, depth + 2)),
        Call(j, x) => Call(*j, s(x, depth)),
    }
}

/// `subst (sub1 v) b`
pub fn sub1(v: &Expr, body: &Expr) -> Expr {
    let v = v.clone();
    subst(body, &move |k| if k == 0 { v.clone() } else { Expr::Var(k - 1) }, 0)
}

/// `subst (stepSub i) s`
fn step_sub(i: u64, s: &Expr) -> Expr {
    subst(
        s,
        &move |k| match k {
            0 => Expr::Var(0),
            1 => Expr::Lit(Val::Nat(i)),
            k => Expr::Var(k - 1),
        },
        0,
    )
}

pub fn srename(e: &Expr, by: usize) -> Expr {
    use Expr::*;
    let s = |x: &Expr| b(srename(x, by));
    match e {
        Lit(v) => Lit(v.clone()),
        Var(k) => Var(*k),
        Op1(o, a) => Op1(*o, s(a)),
        Op2(o, a, x) => Op2(*o, s(a), s(x)),
        Ite(c, x, y) => Ite(s(c), s(x), s(y)),
        Let(x, body) => Let(s(x), s(body)),
        Pair(x, y) => Pair(s(x), s(y)),
        Fst(x) => Fst(s(x)),
        Snd(x) => Snd(s(x)),
        Inl(t, x) => Inl(t.clone(), s(x)),
        Inr(t, x) => Inr(t.clone(), s(x)),
        Case(x, l, r) => Case(s(x), s(l), s(r)),
        Iter(n, z, st) => Iter(s(n), s(z), s(st)),
        Call(j, x) => Call(j + by, s(x)),
    }
}

// --------------------------------------------------------------- traversal

pub fn bu(st: &dyn Fn(Expr) -> RR, e: &Expr) -> RR {
    use Expr::*;
    let r = |x: &Expr| -> Result<Box<Expr>, EvalError> { Ok(b(bu(st, x)?)) };
    let node = match e {
        Lit(v) => Lit(v.clone()),
        Var(k) => Var(*k),
        Op1(o, a) => Op1(*o, r(a)?),
        Op2(o, a, x) => Op2(*o, r(a)?, r(x)?),
        Ite(c, x, y) => Ite(r(c)?, r(x)?, r(y)?),
        Let(x, body) => Let(r(x)?, r(body)?),
        Pair(x, y) => Pair(r(x)?, r(y)?),
        Fst(x) => Fst(r(x)?),
        Snd(x) => Snd(r(x)?),
        Inl(t, x) => Inl(t.clone(), r(x)?),
        Inr(t, x) => Inr(t.clone(), r(x)?),
        Case(x, l, rr) => Case(r(x)?, r(l)?, r(rr)?),
        Iter(n, z, s) => Iter(r(n)?, r(z)?, r(s)?),
        Call(j, x) => Call(*j, r(x)?),
    };
    st(node)
}

fn is_nat(e: &Expr, k: u64) -> bool {
    matches!(e, Expr::Lit(Val::Nat(v)) if *v == k)
}
fn is_int(e: &Expr, k: i64) -> bool {
    matches!(e, Expr::Lit(Val::Int(v)) if *v == k)
}
fn is_bool(e: &Expr, k: bool) -> bool {
    matches!(e, Expr::Lit(Val::Bool(v)) if *v == k)
}
fn lit_of(e: &Expr) -> Option<&Val> {
    match e {
        Expr::Lit(v) => Some(v),
        _ => None,
    }
}

// --------------------------------------------------------- 1. cf-step

pub fn cf_step(e: Expr) -> RR {
    use Expr::*;
    Ok(match e {
        Op1(o, a) => match lit_of(&a) {
            Some(x) => Lit(ev1(o, x)?),
            None => Op1(o, a),
        },
        Op2(o, a, c) => match (lit_of(&a), lit_of(&c)) {
            (Some(x), Some(y)) => Lit(ev2(o, x, y)?),
            _ => Op2(o, a, c),
        },
        Ite(c, x, y) => match lit_of(&c) {
            Some(Val::Bool(true)) => *x,
            Some(Val::Bool(false)) => *y,
            _ => Ite(c, x, y),
        },
        Iter(n, z, s) => {
            if is_nat(&n, 0) {
                *z
            } else {
                Iter(n, z, s)
            }
        }
        e => e,
    })
}

// --------------------------------------------------------- 2. alg-step

pub fn alg_step(e: Expr) -> RR {
    use Expr::*;
    use crate::ir::Op2::{AddN, AddZ, AndB, MulN, MulZ, OrB, SubN, SubZ};
    Ok(match e {
        Op1(crate::ir::Op1::NotB, a) => match *a {
            Op1(crate::ir::Op1::NotB, x) => *x,
            a => Op1(crate::ir::Op1::NotB, b(a)),
        },
        Op1(crate::ir::Op1::NegZ, a) => match *a {
            Op1(crate::ir::Op1::NegZ, x) => *x,
            a => Op1(crate::ir::Op1::NegZ, b(a)),
        },
        Op2(AddN, a, c) => {
            if is_nat(&c, 0) {
                *a
            } else if is_nat(&a, 0) {
                *c
            } else {
                Op2(AddN, a, c)
            }
        }
        Op2(SubN, a, c) => {
            if is_nat(&c, 0) {
                *a
            } else if is_nat(&a, 0) {
                Lit(Val::Nat(0))
            } else {
                Op2(SubN, a, c)
            }
        }
        Op2(MulN, a, c) => {
            if is_nat(&c, 1) {
                *a
            } else if is_nat(&a, 1) {
                *c
            } else if is_nat(&c, 0) || is_nat(&a, 0) {
                Lit(Val::Nat(0))
            } else {
                Op2(MulN, a, c)
            }
        }
        Op2(AddZ, a, c) => {
            if is_int(&c, 0) {
                *a
            } else if is_int(&a, 0) {
                *c
            } else {
                Op2(AddZ, a, c)
            }
        }
        Op2(SubZ, a, c) => {
            if is_int(&c, 0) {
                *a
            } else {
                Op2(SubZ, a, c)
            }
        }
        Op2(MulZ, a, c) => {
            if is_int(&c, 1) {
                *a
            } else if is_int(&a, 1) {
                *c
            } else if is_int(&c, 0) || is_int(&a, 0) {
                Lit(Val::Int(0))
            } else {
                Op2(MulZ, a, c)
            }
        }
        Op2(AndB, a, c) => {
            if is_bool(&c, true) {
                *a
            } else if is_bool(&a, true) {
                *c
            } else if is_bool(&c, false) || is_bool(&a, false) {
                Lit(Val::Bool(false))
            } else {
                Op2(AndB, a, c)
            }
        }
        Op2(OrB, a, c) => {
            if is_bool(&c, false) {
                *a
            } else if is_bool(&a, false) {
                *c
            } else if is_bool(&c, true) || is_bool(&a, true) {
                Lit(Val::Bool(true))
            } else {
                Op2(OrB, a, c)
            }
        }
        e => e,
    })
}

// --------------------------------------------------------- 3. dce-step

pub fn occ(k: usize, e: &Expr) -> bool {
    use Expr::*;
    match e {
        Lit(_) => false,
        Var(x) => *x == k,
        Op1(_, a) | Fst(a) | Snd(a) | Inl(_, a) | Inr(_, a) | Call(_, a) => occ(k, a),
        Op2(_, a, c) | Pair(a, c) => occ(k, a) || occ(k, c),
        Ite(c, x, y) => occ(k, c) || occ(k, x) || occ(k, y),
        Let(x, body) => occ(k, x) || occ(k + 1, body),
        Case(x, l, r) => occ(k, x) || occ(k + 1, l) || occ(k + 1, r),
        Iter(n, z, s) => occ(k, n) || occ(k, z) || occ(k + 2, s),
    }
}

pub fn dce_step(e: Expr) -> RR {
    use Expr::*;
    Ok(match e {
        Let(x, body) => {
            if !occ(0, &body) {
                sub1(&x, &body)
            } else {
                Let(x, body)
            }
        }
        Fst(x) => match *x {
            Pair(a, _) => *a,
            x => Fst(b(x)),
        },
        Snd(x) => match *x {
            Pair(_, c) => *c,
            x => Snd(b(x)),
        },
        e => e,
    })
}

// --------------------------------------------------------- 4. pe-step

fn unroll(mut i: u64, r: u64, mut acc: Expr, s: &Expr) -> Expr {
    for _ in 0..r {
        acc = Expr::Let(b(acc), b(step_sub(i, s)));
        i += 1;
    }
    acc
}

pub fn pe_step(k: u64, e: Expr) -> RR {
    use Expr::*;
    Ok(match e {
        Let(x, body) => match *x {
            Lit(_) | Var(_) => sub1(&x, &body),
            x => Let(b(x), body),
        },
        Case(x, l, r) => match *x {
            Inl(_, a) => sub1(&a, &l),
            Inr(_, c) => sub1(&c, &r),
            x => Case(b(x), l, r),
        },
        Iter(n, z, s) => match *n {
            Lit(Val::Nat(m)) if m <= k => unroll(0, m, *z, &s),
            n => Iter(b(n), z, s),
        },
        e => e,
    })
}

// --------------------------------------------------------- 6. fuse-step

pub fn fuse_step(e: Expr) -> RR {
    use Expr::*;
    use crate::ir::Op2::{AddN, AddZ, MulN, MulZ, SubZ};
    let ov = |n| EvalError::Overflow(n);
    Ok(match e {
        Op2(o @ (AddN | MulN | AddZ | MulZ | SubZ), a, c) => {
            let inner = if o == SubZ { AddZ } else { o };
            match (&*a, lit_of(&c)) {
                (Op2(o2, x, cc), Some(d)) if *o2 == inner && lit_of(cc).is_some() => {
                    let cv = lit_of(cc).unwrap();
                    let v = match (o, cv, d) {
                        (AddN, Val::Nat(p), Val::Nat(q)) => Val::Nat(p.checked_add(*q).ok_or(ov("fuse addN"))?),
                        (MulN, Val::Nat(p), Val::Nat(q)) => Val::Nat(p.checked_mul(*q).ok_or(ov("fuse mulN"))?),
                        (AddZ, Val::Int(p), Val::Int(q)) => Val::Int(p.checked_add(*q).ok_or(ov("fuse addZ"))?),
                        (MulZ, Val::Int(p), Val::Int(q)) => Val::Int(p.checked_mul(*q).ok_or(ov("fuse mulZ"))?),
                        (SubZ, Val::Int(p), Val::Int(q)) => Val::Int(p.checked_sub(*q).ok_or(ov("fuse subZ"))?),
                        _ => return Err(EvalError::Stuck("ill-typed fusion".into())),
                    };
                    Op2(inner, x.clone(), b(Lit(v)))
                }
                _ => Op2(o, a, c),
            }
        }
        e => e,
    })
}

// --------------------------------------------------------- programs

pub fn pass_expr(p: Pass, e: &Expr) -> RR {
    match p {
        Pass::Cf => bu(&cf_step, e),
        Pass::Alg => bu(&alg_step, e),
        Pass::Dce => bu(&dce_step, e),
        Pass::Fuse => bu(&fuse_step, e),
        Pass::Pe(k) => bu(&move |x| pe_step(k, x), e),
    }
}

pub fn map_p(pass: Pass, prog: &Prog) -> Result<Prog, EvalError> {
    let mut defs = Vec::new();
    for d in &prog.defs {
        defs.push(FunDef { body: pass_expr(pass, &d.body)?, ..d.clone() });
    }
    Ok(Prog { defs })
}

pub fn run_passes(ps: &[Pass], prog: &Prog) -> Result<Prog, EvalError> {
    let mut p = prog.clone();
    for &x in ps {
        p = map_p(x, &p)?;
    }
    Ok(p)
}

/// `specP (P ▷ main) m t v`; `j` is the call index of the target as seen
/// from main. Fails (returns Err) if the target is not of shape a ⊗ base.
pub fn spec(prog: &Prog, j: usize, v: &Val) -> Result<Prog, String> {
    let n = prog.defs.len();
    let target = (n - 1).checked_sub(1 + j).ok_or("specialization target out of range")?;
    let td = &prog.defs[target];
    let (a, c) = match &td.arg {
        Ty::Prod(a, c) => ((**a).clone(), (**c).clone()),
        _ => return Err("specialization target argument is not a product".into()),
    };
    if !c.is_base() || !crate::typecheck::val_ty_check(v, &c) {
        return Err("specialization value is not a literal of the base second component".into());
    }
    // fbody: let (pair #0 (lit v)) (srename (j+1) body)
    let fbody = Expr::Let(
        b(Expr::Pair(b(Expr::Var(0)), b(Expr::Lit(v.clone())))),
        b(srename(&td.body, j + 1)),
    );
    let vv = v.clone();
    let respec = move |e: Expr| -> RR {
        if let Expr::Call(jj, x) = &e {
            if *jj == j + 1 {
                if let Expr::Pair(ea, ec) = &**x {
                    if let Expr::Lit(w) = &**ec {
                        if *w == vv {
                            return Ok(Expr::Call(0, ea.clone()));
                        }
                    }
                }
            }
        }
        Ok(e)
    };
    let main = prog.main();
    let new_main = bu(&respec, &srename(&main.body, 1)).map_err(|e| format!("{:?}", e))?;
    let mut defs: Vec<FunDef> = prog.defs[..n - 1].to_vec();
    defs.push(FunDef { name: format!("{}_spec_{}", td.name, v), arg: a, ret: td.ret.clone(), body: fbody });
    defs.push(FunDef { body: new_main, ..main.clone() });
    Ok(Prog { defs })
}

pub fn apply_script(prog: &Prog, s: &Script) -> Result<Prog, String> {
    let mut p = prog.clone();
    for st in s {
        p = match st {
            Step::Passes(ps) => run_passes(ps, &p).map_err(|e| format!("rewrite trapped: {:?}", e))?,
            Step::Spec { j, v } => spec(&p, *j, v)?,
        };
        crate::typecheck::check_prog(&p).map_err(|e| format!("rewrite broke typing: {}", e))?;
    }
    Ok(p)
}

/// Script syntax: steps separated by `;`. A step is either a comma-separated
/// pass list (`cf`, `alg`, `dce`, `fuse`, `peN`) or `spec:J:VALUE`.
pub fn parse_script(s: &str) -> Result<Script, String> {
    let mut out = Vec::new();
    for st in s.split(';').map(str::trim).filter(|x| !x.is_empty()) {
        if let Some(rest) = st.strip_prefix("spec:") {
            let (j, v) = rest.split_once(':').ok_or("spec:J:VALUE")?;
            out.push(Step::Spec {
                j: j.trim().parse().map_err(|_| "spec index")?,
                v: crate::parse::parse_val_str(v.trim())?,
            });
        } else {
            let mut ps = Vec::new();
            for p in st.split(',').map(str::trim) {
                ps.push(match p {
                    "cf" => Pass::Cf,
                    "alg" => Pass::Alg,
                    "dce" => Pass::Dce,
                    "fuse" => Pass::Fuse,
                    p if p.starts_with("pe") => Pass::Pe(p[2..].parse().map_err(|_| format!("bad pass {}", p))?),
                    p => return Err(format!("unknown pass {}", p)),
                });
            }
            out.push(Step::Passes(ps));
        }
    }
    Ok(out)
}

pub fn script_text(s: &Script) -> String {
    s.iter()
        .map(|st| match st {
            Step::Passes(ps) => ps
                .iter()
                .map(|p| match p {
                    Pass::Pe(k) => format!("pe{}", k),
                    p => p.agda(),
                })
                .collect::<Vec<_>>()
                .join(","),
            Step::Spec { j, v } => format!("spec:{}:{}", j, v),
        })
        .collect::<Vec<_>>()
        .join(";")
}
