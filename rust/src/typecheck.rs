// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Type synthesis for de Bruijn IR. Used on every program that enters the
//! engine (parsed, deserialized, or produced by a rewrite).

use crate::ir::*;

pub type Sig = Vec<(Ty, Ty)>; // index 0 = most recent definition

pub fn val_ty_check(v: &Val, t: &Ty) -> bool {
    match (v, t) {
        (Val::Nat(_), Ty::Nat) | (Val::Int(_), Ty::Int) | (Val::Bool(_), Ty::Bool) => true,
        (Val::Pair(a, c), Ty::Prod(ta, tc)) => val_ty_check(a, ta) && val_ty_check(c, tc),
        (Val::Inl(a), Ty::Sum(ta, _)) => val_ty_check(a, ta),
        (Val::Inr(a), Ty::Sum(_, tc)) => val_ty_check(a, tc),
        _ => false,
    }
}

pub fn synth(sig: &Sig, ctx: &[Ty], e: &Expr) -> Result<Ty, String> {
    use Expr::*;
    // ctx[0] is the innermost binder (de Bruijn 0)
    let need = |t: Ty, want: &Ty, what: &str| -> Result<(), String> {
        if &t == want {
            Ok(())
        } else {
            Err(format!("type mismatch in {}: expected {}, found {}", what, want, t))
        }
    };
    match e {
        Lit(v) => match v {
            Val::Nat(_) => Ok(Ty::Nat),
            Val::Int(_) => Ok(Ty::Int),
            Val::Bool(_) => Ok(Ty::Bool),
            _ => Err("literal must be of base type".into()),
        },
        Var(i) => ctx.get(*i).cloned().ok_or_else(|| format!("unbound variable #{}", i)),
        Op1(o, a) => {
            let (ti, to) = o.sig();
            need(synth(sig, ctx, a)?, &ti, o.name())?;
            Ok(to)
        }
        Op2(o, a, c) => {
            let (ta, tc, to) = o.sig();
            need(synth(sig, ctx, a)?, &ta, o.name())?;
            need(synth(sig, ctx, c)?, &tc, o.name())?;
            Ok(to)
        }
        Ite(c, x, y) => {
            need(synth(sig, ctx, c)?, &Ty::Bool, "if condition")?;
            let tx = synth(sig, ctx, x)?;
            need(synth(sig, ctx, y)?, &tx, "if branches")?;
            Ok(tx)
        }
        Let(x, body) => {
            let tx = synth(sig, ctx, x)?;
            let mut c2 = vec![tx];
            c2.extend_from_slice(ctx);
            synth(sig, &c2, body)
        }
        Pair(x, y) => Ok(Ty::prod(synth(sig, ctx, x)?, synth(sig, ctx, y)?)),
        Fst(x) => match synth(sig, ctx, x)? {
            Ty::Prod(a, _) => Ok(*a),
            t => Err(format!("fst of non-product {}", t)),
        },
        Snd(x) => match synth(sig, ctx, x)? {
            Ty::Prod(_, c) => Ok(*c),
            t => Err(format!("snd of non-product {}", t)),
        },
        Inl(other, x) => Ok(Ty::sum(synth(sig, ctx, x)?, other.clone())),
        Inr(other, x) => Ok(Ty::sum(other.clone(), synth(sig, ctx, x)?)),
        Case(x, l, r) => match synth(sig, ctx, x)? {
            Ty::Sum(ta, tb) => {
                let mut cl = vec![*ta];
                cl.extend_from_slice(ctx);
                let mut cr = vec![*tb];
                cr.extend_from_slice(ctx);
                let tl = synth(sig, &cl, l)?;
                need(synth(sig, &cr, r)?, &tl, "case branches")?;
                Ok(tl)
            }
            t => Err(format!("case of non-sum {}", t)),
        },
        Iter(n, z, s) => {
            need(synth(sig, ctx, n)?, &Ty::Nat, "iter count")?;
            let tz = synth(sig, ctx, z)?;
            let mut cs = vec![tz.clone(), Ty::Nat];
            cs.extend_from_slice(ctx);
            need(synth(sig, &cs, s)?, &tz, "iter step")?;
            Ok(tz)
        }
        Call(j, x) => {
            let (ta, tb) = sig.get(*j).cloned().ok_or_else(|| format!("call to unknown function {}", j))?;
            need(synth(sig, ctx, x)?, &ta, "call argument")?;
            Ok(tb)
        }
    }
}

/// Check every definition; returns the main type.
pub fn check_prog(p: &Prog) -> Result<(Ty, Ty), String> {
    if p.defs.is_empty() {
        return Err("empty program".into());
    }
    let mut sig: Sig = Vec::new();
    for d in &p.defs {
        let t = synth(&sig, &[d.arg.clone()], &d.body).map_err(|e| format!("in {}: {}", d.name, e))?;
        if t != d.ret {
            return Err(format!("in {}: declared {}, body has {}", d.name, d.ret, t));
        }
        sig.insert(0, (d.arg.clone(), d.ret.clone()));
    }
    let m = p.main();
    Ok((m.arg.clone(), m.ret.clone()))
}

pub fn sig_of(p: &Prog, upto: usize) -> Sig {
    p.defs[..upto].iter().rev().map(|d| (d.arg.clone(), d.ret.clone())).collect()
}

/// Synthesize the type of `e` appearing in definition `def_idx` under `ctx`.
pub fn synth_in(p: &Prog, def_idx: usize, ctx: &[Ty], e: &Expr) -> Result<Ty, String> {
    synth(&sig_of(p, def_idx), ctx, e)
}
