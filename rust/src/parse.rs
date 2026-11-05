// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Two readers: the named surface syntax (`.morph` files) elaborated with
//! type-directed operator resolution, and the canonical de Bruijn syntax
//! produced by `Prog::canonical` (used for deserialization and replay).

use crate::ir::*;
use crate::sexp::{self, Sx};
use crate::typecheck::{self, Sig};

fn err<T>(m: impl Into<String>) -> Result<T, String> {
    Err(m.into())
}

pub fn parse_ty(s: &Sx) -> Result<Ty, String> {
    match s {
        Sx::Atom(a) => match a.as_str() {
            "nat" => Ok(Ty::Nat),
            "int" => Ok(Ty::Int),
            "bool" => Ok(Ty::Bool),
            _ => err(format!("unknown type {}", a)),
        },
        Sx::List(v) if v.len() == 3 => {
            let a = parse_ty(&v[1])?;
            let c = parse_ty(&v[2])?;
            match v[0].atom() {
                Some("*") => Ok(Ty::prod(a, c)),
                Some("+") => Ok(Ty::sum(a, c)),
                _ => err("type constructor must be * or +"),
            }
        }
        _ => err("malformed type"),
    }
}

pub fn parse_val(s: &Sx) -> Result<Val, String> {
    match s {
        Sx::Atom(a) if a == "true" => Ok(Val::Bool(true)),
        Sx::Atom(a) if a == "false" => Ok(Val::Bool(false)),
        Sx::List(v) if v.len() == 2 && v[0].atom() == Some("nat") => {
            Ok(Val::Nat(v[1].atom().ok_or("nat literal")?.parse().map_err(|e| format!("nat literal: {}", e))?))
        }
        Sx::List(v) if v.len() == 2 && v[0].atom() == Some("int") => {
            Ok(Val::Int(v[1].atom().ok_or("int literal")?.parse().map_err(|e| format!("int literal: {}", e))?))
        }
        Sx::List(v) if v.len() == 3 && v[0].atom() == Some("pair") => {
            Ok(Val::Pair(Box::new(parse_val(&v[1])?), Box::new(parse_val(&v[2])?)))
        }
        Sx::List(v) if v.len() == 2 && v[0].atom() == Some("inl") => Ok(Val::Inl(Box::new(parse_val(&v[1])?))),
        Sx::List(v) if v.len() == 2 && v[0].atom() == Some("inr") => Ok(Val::Inr(Box::new(parse_val(&v[1])?))),
        _ => err("malformed value"),
    }
}

pub fn parse_val_str(s: &str) -> Result<Val, String> {
    parse_val(&sexp::parse(s)?)
}

// ---------------------------------------------------------------- surface

struct Elab<'a> {
    names: Vec<String>, // index 0 = innermost
    tys: Vec<Ty>,
    funs: &'a [(String, Ty, Ty)], // defined so far, in order
}

const RESERVED: &[&str] = &[
    "nat", "int", "true", "false", "add", "sub", "mul", "lt", "eq", "and", "or", "not", "neg", "toint", "if",
    "let", "pair", "fst", "snd", "inl", "inr", "case", "iter", "call", "def",
];

impl<'a> Elab<'a> {
    fn bind<T>(&mut self, n: &str, t: Ty, f: impl FnOnce(&mut Self) -> Result<T, String>) -> Result<T, String> {
        if RESERVED.contains(&n) {
            return err(format!("reserved word used as binder: {}", n));
        }
        self.names.insert(0, n.to_string());
        self.tys.insert(0, t);
        let r = f(self);
        self.names.remove(0);
        self.tys.remove(0);
        r
    }
    fn sig(&self) -> Sig {
        self.funs.iter().rev().map(|(_, a, r)| (a.clone(), r.clone())).collect()
    }
    fn ty_of(&self, e: &Expr) -> Result<Ty, String> {
        typecheck::synth(&self.sig(), &self.tys, e)
    }
    fn expr(&mut self, s: &Sx) -> Result<Expr, String> {
        use Expr::*;
        match s {
            Sx::Atom(a) if a == "true" => Ok(Lit(Val::Bool(true))),
            Sx::Atom(a) if a == "false" => Ok(Lit(Val::Bool(false))),
            Sx::Atom(a) => match self.names.iter().position(|n| n == a) {
                Some(i) => Ok(Var(i)),
                None => err(format!("unbound identifier {}", a)),
            },
            Sx::List(v) if v.is_empty() => err("empty application"),
            Sx::List(v) => {
                let head = v[0].atom().ok_or("head must be an atom")?;
                let arity = |n: usize| -> Result<(), String> {
                    if v.len() == n + 1 {
                        Ok(())
                    } else {
                        err(format!("{} expects {} arguments, got {}", head, n, v.len() - 1))
                    }
                };
                match head {
                    "nat" | "int" => Ok(Lit(parse_val(s)?)),
                    "add" | "sub" | "mul" | "lt" | "eq" => {
                        arity(2)?;
                        let x = self.expr(&v[1])?;
                        let y = self.expr(&v[2])?;
                        let t = self.ty_of(&x)?;
                        let o = match (head, &t) {
                            ("add", Ty::Nat) => crate::ir::Op2::AddN,
                            ("sub", Ty::Nat) => crate::ir::Op2::SubN,
                            ("mul", Ty::Nat) => crate::ir::Op2::MulN,
                            ("lt", Ty::Nat) => crate::ir::Op2::LtN,
                            ("eq", Ty::Nat) => crate::ir::Op2::EqN,
                            ("add", Ty::Int) => crate::ir::Op2::AddZ,
                            ("sub", Ty::Int) => crate::ir::Op2::SubZ,
                            ("mul", Ty::Int) => crate::ir::Op2::MulZ,
                            ("lt", Ty::Int) => crate::ir::Op2::LtZ,
                            ("eq", Ty::Int) => crate::ir::Op2::EqZ,
                            _ => return err(format!("{} not defined on {}", head, t)),
                        };
                        let e = Op2(o, b(x), b(y));
                        self.ty_of(&e)?;
                        Ok(e)
                    }
                    "and" | "or" => {
                        arity(2)?;
                        let o = if head == "and" { crate::ir::Op2::AndB } else { crate::ir::Op2::OrB };
                        let e = Op2(o, b(self.expr(&v[1])?), b(self.expr(&v[2])?));
                        self.ty_of(&e)?;
                        Ok(e)
                    }
                    "not" | "neg" | "toint" => {
                        arity(1)?;
                        let o = match head {
                            "not" => crate::ir::Op1::NotB,
                            "neg" => crate::ir::Op1::NegZ,
                            _ => crate::ir::Op1::ToInt,
                        };
                        let e = Op1(o, b(self.expr(&v[1])?));
                        self.ty_of(&e)?;
                        Ok(e)
                    }
                    "if" => {
                        arity(3)?;
                        let e = Ite(b(self.expr(&v[1])?), b(self.expr(&v[2])?), b(self.expr(&v[3])?));
                        self.ty_of(&e)?;
                        Ok(e)
                    }
                    "let" => {
                        arity(3)?;
                        let n = v[1].atom().ok_or("let binder")?;
                        let x = self.expr(&v[2])?;
                        let t = self.ty_of(&x)?;
                        let body = self.bind(n, t, |s| s.expr(&v[3]))?;
                        Ok(Let(b(x), b(body)))
                    }
                    "pair" => {
                        arity(2)?;
                        Ok(Pair(b(self.expr(&v[1])?), b(self.expr(&v[2])?)))
                    }
                    "fst" | "snd" => {
                        arity(1)?;
                        let x = self.expr(&v[1])?;
                        let e = if head == "fst" { Fst(b(x)) } else { Snd(b(x)) };
                        self.ty_of(&e)?;
                        Ok(e)
                    }
                    "inl" | "inr" => {
                        arity(2)?;
                        let t = parse_ty(&v[1])?;
                        let x = self.expr(&v[2])?;
                        Ok(if head == "inl" { Inl(t, b(x)) } else { Inr(t, b(x)) })
                    }
                    "case" => {
                        arity(3)?;
                        let x = self.expr(&v[1])?;
                        let (ta, tb) = match self.ty_of(&x)? {
                            Ty::Sum(a, c) => (*a, *c),
                            t => return err(format!("case of non-sum {}", t)),
                        };
                        let arm = |s: &Sx| -> Result<(String, Sx), String> {
                            match s {
                                Sx::List(w) if w.len() == 2 => {
                                    Ok((w[0].atom().ok_or("case binder")?.to_string(), w[1].clone()))
                                }
                                _ => err("case arm must be (name body)"),
                            }
                        };
                        let (nl, bl) = arm(&v[2])?;
                        let (nr, br) = arm(&v[3])?;
                        let l = self.bind(&nl, ta, |s| s.expr(&bl))?;
                        let r = self.bind(&nr, tb, |s| s.expr(&br))?;
                        let e = Case(b(x), b(l), b(r));
                        self.ty_of(&e)?;
                        Ok(e)
                    }
                    "iter" => {
                        arity(3)?;
                        let n = self.expr(&v[1])?;
                        let z = self.expr(&v[2])?;
                        let tz = self.ty_of(&z)?;
                        let (ni, na, bs) = match &v[3] {
                            Sx::List(w) if w.len() == 3 => (
                                w[0].atom().ok_or("iter index binder")?.to_string(),
                                w[1].atom().ok_or("iter acc binder")?.to_string(),
                                w[2].clone(),
                            ),
                            _ => return err("iter step must be (i acc body)"),
                        };
                        let s = self.bind(&ni, Ty::Nat, |st| st.bind(&na, tz.clone(), |st2| st2.expr(&bs)))?;
                        let e = Iter(b(n), b(z), b(s));
                        self.ty_of(&e)?;
                        Ok(e)
                    }
                    "call" => {
                        arity(2)?;
                        let f = v[1].atom().ok_or("call target")?;
                        let pos = self
                            .funs
                            .iter()
                            .position(|(n, _, _)| n == f)
                            .ok_or_else(|| format!("call to undefined (or later) function {}", f))?;
                        let j = self.funs.len() - 1 - pos;
                        let e = Call(j, b(self.expr(&v[2])?));
                        self.ty_of(&e)?;
                        Ok(e)
                    }
                    _ => err(format!("unsupported construct: {}", head)),
                }
            }
        }
    }
}

/// Surface program: a sequence of `(def name (arg type) ret-type body)`;
/// the last definition is main.
pub fn parse_surface(src: &str) -> Result<Prog, String> {
    let items = sexp::parse_all(src)?;
    let mut funs: Vec<(String, Ty, Ty)> = Vec::new();
    let mut defs = Vec::new();
    for it in &items {
        let v = match it {
            Sx::List(v) if v.len() == 5 && v[0].atom() == Some("def") => v,
            _ => return err("top level must be (def name (arg type) ret body)"),
        };
        let name = v[1].atom().ok_or("def name")?.to_string();
        if funs.iter().any(|(n, _, _)| *n == name) {
            return err(format!("duplicate definition {}", name));
        }
        let (an, at) = match &v[2] {
            Sx::List(w) if w.len() == 2 => (w[0].atom().ok_or("arg name")?.to_string(), parse_ty(&w[1])?),
            _ => return err("argument must be (name type)"),
        };
        let rt = parse_ty(&v[3])?;
        let mut el = Elab { names: vec![], tys: vec![], funs: &funs };
        let body = el.bind(&an, at.clone(), |s| s.expr(&v[4]))?;
        defs.push(FunDef { name: name.clone(), arg: at.clone(), ret: rt.clone(), body });
        funs.push((name, at, rt));
    }
    let p = Prog { defs };
    typecheck::check_prog(&p)?;
    Ok(p)
}

// -------------------------------------------------------------- canonical

fn op1_of(n: &str) -> Option<Op1> {
    [crate::ir::Op1::NegZ, crate::ir::Op1::NotB, crate::ir::Op1::ToInt].into_iter().find(|o| o.name() == n)
}
fn op2_of(n: &str) -> Option<Op2> {
    crate::ir::Op2::all().into_iter().find(|o| o.name() == n)
}

pub fn canon_expr(s: &Sx) -> Result<Expr, String> {
    use Expr::*;
    match s {
        Sx::Atom(a) if a.starts_with('#') => Ok(Var(a[1..].parse().map_err(|_| "bad variable")?)),
        Sx::Atom(_) => Ok(Lit(parse_val(s)?)),
        Sx::List(v) => {
            let h = v.first().and_then(|x| x.atom()).ok_or("malformed canonical expr")?;
            let e = |i: usize| canon_expr(&v[i]).map(Box::new);
            let n = v.len();
            Ok(match (h, n) {
                ("nat", 2) | ("int", 2) => Lit(parse_val(s)?),
                (o, 2) if op1_of(o).is_some() => Op1(op1_of(o).unwrap(), e(1)?),
                (o, 3) if op2_of(o).is_some() => Op2(op2_of(o).unwrap(), e(1)?, e(2)?),
                ("if", 4) => Ite(e(1)?, e(2)?, e(3)?),
                ("let", 3) => Let(e(1)?, e(2)?),
                ("pair", 3) => Pair(e(1)?, e(2)?),
                ("fst", 2) => Fst(e(1)?),
                ("snd", 2) => Snd(e(1)?),
                ("inl", 3) => Inl(parse_ty(&v[1])?, e(2)?),
                ("inr", 3) => Inr(parse_ty(&v[1])?, e(2)?),
                ("case", 4) => Case(e(1)?, e(2)?, e(3)?),
                ("iter", 4) => Iter(e(1)?, e(2)?, e(3)?),
                ("call", 3) => Call(v[1].atom().ok_or("call index")?.parse().map_err(|_| "call index")?, e(2)?),
                _ => return err(format!("malformed canonical expr head {}", h)),
            })
        }
    }
}

pub fn parse_canonical(src: &str) -> Result<Prog, String> {
    let s = sexp::parse(src)?;
    let v = match &s {
        Sx::List(v) if v.first().and_then(|x| x.atom()) == Some("prog") => v,
        _ => return err("canonical program must start with (prog"),
    };
    let mut defs = Vec::new();
    for (i, d) in v[1..].iter().enumerate() {
        match d {
            Sx::List(w) if w.len() == 4 && w[0].atom() == Some("def") => defs.push(FunDef {
                name: format!("f{}", i),
                arg: parse_ty(&w[1])?,
                ret: parse_ty(&w[2])?,
                body: canon_expr(&w[3])?,
            }),
            _ => return err("malformed canonical def"),
        }
    }
    if let Some(l) = defs.last_mut() {
        l.name = "main".into();
    }
    let p = Prog { defs };
    typecheck::check_prog(&p)?;
    Ok(p)
}
