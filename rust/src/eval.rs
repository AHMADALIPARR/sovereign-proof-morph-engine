// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Reference interpreter: big-step environment semantics, rule for rule the
//! Agda denotation `⟦_⟧` of Morph.IR. ℕ is u64 and ℤ is i64 with checked
//! arithmetic: whenever a result would leave the machine range the
//! interpreter returns `Overflow` (a trap), never a wrapped value. On every
//! non-trapping run the result equals the unbounded Agda semantics.

use crate::ir::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    Overflow(&'static str),
    Stuck(String),
}

pub type R<T> = Result<T, EvalError>;

pub fn ev1(o: Op1, v: &Val) -> R<Val> {
    match (o, v) {
        (Op1::NegZ, Val::Int(i)) => i.checked_neg().map(Val::Int).ok_or(EvalError::Overflow("negZ")),
        (Op1::NotB, Val::Bool(x)) => Ok(Val::Bool(!x)),
        (Op1::ToInt, Val::Nat(n)) => i64::try_from(*n).map(Val::Int).map_err(|_| EvalError::Overflow("toInt")),
        _ => Err(EvalError::Stuck(format!("{} applied to {}", o.name(), v))),
    }
}

pub fn ev2(o: Op2, a: &Val, c: &Val) -> R<Val> {
    use Op2::*;
    use Val::*;
    let ov = |n: &'static str| EvalError::Overflow(n);
    Ok(match (o, a, c) {
        (AddN, Nat(x), Nat(y)) => Nat(x.checked_add(*y).ok_or(ov("addN"))?),
        (SubN, Nat(x), Nat(y)) => Nat(x.saturating_sub(*y)), // monus: total, exact
        (MulN, Nat(x), Nat(y)) => Nat(x.checked_mul(*y).ok_or(ov("mulN"))?),
        (LtN, Nat(x), Nat(y)) => Bool(x < y),
        (EqN, Nat(x), Nat(y)) => Bool(x == y),
        (AddZ, Int(x), Int(y)) => Int(x.checked_add(*y).ok_or(ov("addZ"))?),
        (SubZ, Int(x), Int(y)) => Int(x.checked_sub(*y).ok_or(ov("subZ"))?),
        (MulZ, Int(x), Int(y)) => Int(x.checked_mul(*y).ok_or(ov("mulZ"))?),
        (LtZ, Int(x), Int(y)) => Bool(x < y),
        (EqZ, Int(x), Int(y)) => Bool(x == y),
        (AndB, Bool(x), Bool(y)) => Bool(*x && *y),
        (OrB, Bool(x), Bool(y)) => Bool(*x || *y),
        _ => return Err(EvalError::Stuck(format!("{} applied to {} {}", o.name(), a, c))),
    })
}

/// Evaluate `e` occurring in definition `di` of `p` under `env`
/// (`env.last()` is de Bruijn 0).
pub fn eval(p: &Prog, di: usize, e: &Expr, env: &mut Vec<Val>) -> R<Val> {
    use Expr::*;
    match e {
        Lit(v) => Ok(v.clone()),
        Var(i) => {
            let n = env.len();
            env.get(n.wrapping_sub(1 + i)).cloned().ok_or_else(|| EvalError::Stuck(format!("unbound #{}", i)))
        }
        Op1(o, a) => {
            let v = eval(p, di, a, env)?;
            ev1(*o, &v)
        }
        Op2(o, a, c) => {
            let x = eval(p, di, a, env)?;
            let y = eval(p, di, c, env)?;
            ev2(*o, &x, &y)
        }
        Ite(c, x, y) => match eval(p, di, c, env)? {
            Val::Bool(true) => eval(p, di, x, env),
            Val::Bool(false) => eval(p, di, y, env),
            v => Err(EvalError::Stuck(format!("if on {}", v))),
        },
        Let(x, body) => {
            let v = eval(p, di, x, env)?;
            env.push(v);
            let r = eval(p, di, body, env);
            env.pop();
            r
        }
        Pair(x, y) => {
            let a = eval(p, di, x, env)?;
            let c = eval(p, di, y, env)?;
            Ok(Val::Pair(Box::new(a), Box::new(c)))
        }
        Fst(x) => match eval(p, di, x, env)? {
            Val::Pair(a, _) => Ok(*a),
            v => Err(EvalError::Stuck(format!("fst of {}", v))),
        },
        Snd(x) => match eval(p, di, x, env)? {
            Val::Pair(_, c) => Ok(*c),
            v => Err(EvalError::Stuck(format!("snd of {}", v))),
        },
        Inl(_, x) => Ok(Val::Inl(Box::new(eval(p, di, x, env)?))),
        Inr(_, x) => Ok(Val::Inr(Box::new(eval(p, di, x, env)?))),
        Case(x, l, r) => match eval(p, di, x, env)? {
            Val::Inl(a) => {
                env.push(*a);
                let res = eval(p, di, l, env);
                env.pop();
                res
            }
            Val::Inr(c) => {
                env.push(*c);
                let res = eval(p, di, r, env);
                env.pop();
                res
            }
            v => Err(EvalError::Stuck(format!("case of {}", v))),
        },
        Iter(n, z, s) => {
            let k = match eval(p, di, n, env)? {
                Val::Nat(k) => k,
                v => return Err(EvalError::Stuck(format!("iter count {}", v))),
            };
            let mut acc = eval(p, di, z, env)?;
            for i in 0..k {
                env.push(Val::Nat(i));
                env.push(acc);
                let r = eval(p, di, s, env);
                env.pop();
                env.pop();
                acc = r?;
            }
            Ok(acc)
        }
        Call(j, x) => {
            let v = eval(p, di, x, env)?;
            let callee = p.callee(di, *j).ok_or_else(|| EvalError::Stuck(format!("bad call {}", j)))?;
            run_def(p, callee, v)
        }
    }
}

pub fn run_def(p: &Prog, di: usize, arg: Val) -> R<Val> {
    let mut env = vec![arg];
    eval(p, di, &p.defs[di].body, &mut env)
}

pub fn run_main(p: &Prog, arg: Val) -> R<Val> {
    run_def(p, p.defs.len() - 1, arg)
}
