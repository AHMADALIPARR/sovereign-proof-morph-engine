// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Typed Morph IR. Mirrors `agda/Morph/IR.agda` constructor for constructor:
//! intrinsically scoped de Bruijn variables (`Var(0)` = `here`), first-order
//! function calls into a signature where `Call(0, _)` is the most recently
//! defined function. Canonical serialization is an S-expression; artifact
//! identities are SHA-256 of that serialization.

use crate::sha256;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Nat,
    Int,
    Bool,
    Prod(Box<Ty>, Box<Ty>),
    Sum(Box<Ty>, Box<Ty>),
}

impl Ty {
    pub fn prod(a: Ty, b: Ty) -> Ty {
        Ty::Prod(Box::new(a), Box::new(b))
    }
    pub fn sum(a: Ty, b: Ty) -> Ty {
        Ty::Sum(Box::new(a), Box::new(b))
    }
    pub fn is_base(&self) -> bool {
        matches!(self, Ty::Nat | Ty::Int | Ty::Bool)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Val {
    Nat(u64),
    Int(i64),
    Bool(bool),
    Pair(Box<Val>, Box<Val>),
    Inl(Box<Val>),
    Inr(Box<Val>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op1 {
    NegZ,
    NotB,
    ToInt,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op2 {
    AddN,
    SubN,
    MulN,
    LtN,
    EqN,
    AddZ,
    SubZ,
    MulZ,
    LtZ,
    EqZ,
    AndB,
    OrB,
}

impl Op1 {
    pub fn sig(self) -> (Ty, Ty) {
        match self {
            Op1::NegZ => (Ty::Int, Ty::Int),
            Op1::NotB => (Ty::Bool, Ty::Bool),
            Op1::ToInt => (Ty::Nat, Ty::Int),
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Op1::NegZ => "negZ",
            Op1::NotB => "notB",
            Op1::ToInt => "toInt",
        }
    }
}

impl Op2 {
    pub fn sig(self) -> (Ty, Ty, Ty) {
        use Op2::*;
        match self {
            AddN | SubN | MulN => (Ty::Nat, Ty::Nat, Ty::Nat),
            LtN | EqN => (Ty::Nat, Ty::Nat, Ty::Bool),
            AddZ | SubZ | MulZ => (Ty::Int, Ty::Int, Ty::Int),
            LtZ | EqZ => (Ty::Int, Ty::Int, Ty::Bool),
            AndB | OrB => (Ty::Bool, Ty::Bool, Ty::Bool),
        }
    }
    pub fn name(self) -> &'static str {
        use Op2::*;
        match self {
            AddN => "addN",
            SubN => "subN",
            MulN => "mulN",
            LtN => "ltN",
            EqN => "eqN",
            AddZ => "addZ",
            SubZ => "subZ",
            MulZ => "mulZ",
            LtZ => "ltZ",
            EqZ => "eqZ",
            AndB => "andB",
            OrB => "orB",
        }
    }
    pub fn all() -> [Op2; 12] {
        use Op2::*;
        [AddN, SubN, MulN, LtN, EqN, AddZ, SubZ, MulZ, LtZ, EqZ, AndB, OrB]
    }
}

/// `Inl(other, e)` / `Inr(other, e)` carry the type of the absent side so
/// that every expression has a synthesizable type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Lit(Val),
    Var(usize),
    Op1(Op1, Box<Expr>),
    Op2(Op2, Box<Expr>, Box<Expr>),
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(Box<Expr>, Box<Expr>),
    Pair(Box<Expr>, Box<Expr>),
    Fst(Box<Expr>),
    Snd(Box<Expr>),
    Inl(Ty, Box<Expr>),
    Inr(Ty, Box<Expr>),
    Case(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `Iter(n, z, s)`: s is checked in context `acc :: i :: Γ`.
    Iter(Box<Expr>, Box<Expr>, Box<Expr>),
    Call(usize, Box<Expr>),
}

pub fn b(e: Expr) -> Box<Expr> {
    Box::new(e)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunDef {
    pub name: String,
    pub arg: Ty,
    pub ret: Ty,
    pub body: Expr,
}

/// Definitions in order; the last one is `main`. Inside definition `i`,
/// `Call(j, _)` targets definition `i - 1 - j`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Prog {
    pub defs: Vec<FunDef>,
}

impl Prog {
    pub fn main(&self) -> &FunDef {
        self.defs.last().expect("program has a main definition")
    }
    pub fn callee(&self, caller: usize, j: usize) -> Option<usize> {
        caller.checked_sub(1 + j)
    }
    /// Canonical serialization: names are excluded so identity is semantic
    /// structure only.
    pub fn canonical(&self) -> String {
        let mut s = String::from("(prog");
        for d in &self.defs {
            s.push_str(&format!(" (def {} {} {})", d.arg, d.ret, d.body));
        }
        s.push(')');
        s
    }
    pub fn hash(&self) -> String {
        sha256::hex(self.canonical().as_bytes())
    }
    pub fn size(&self) -> usize {
        self.defs.iter().map(|d| d.body.size()).sum()
    }
}

impl Expr {
    pub fn size(&self) -> usize {
        use Expr::*;
        1 + match self {
            Lit(_) | Var(_) => 0,
            Op1(_, a) | Fst(a) | Snd(a) | Inl(_, a) | Inr(_, a) | Call(_, a) => a.size(),
            Op2(_, a, c) | Let(a, c) | Pair(a, c) => a.size() + c.size(),
            Ite(a, c, d) | Case(a, c, d) | Iter(a, c, d) => a.size() + c.size() + d.size(),
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ty::Nat => write!(f, "nat"),
            Ty::Int => write!(f, "int"),
            Ty::Bool => write!(f, "bool"),
            Ty::Prod(a, c) => write!(f, "(* {} {})", a, c),
            Ty::Sum(a, c) => write!(f, "(+ {} {})", a, c),
        }
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Val::Nat(n) => write!(f, "(nat {})", n),
            Val::Int(i) => write!(f, "(int {})", i),
            Val::Bool(x) => write!(f, "{}", if *x { "true" } else { "false" }),
            Val::Pair(a, c) => write!(f, "(pair {} {})", a, c),
            Val::Inl(a) => write!(f, "(inl {})", a),
            Val::Inr(a) => write!(f, "(inr {})", a),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Expr::*;
        match self {
            Lit(v) => write!(f, "{}", v),
            Var(i) => write!(f, "#{}", i),
            Op1(o, a) => write!(f, "({} {})", o.name(), a),
            Op2(o, a, c) => write!(f, "({} {} {})", o.name(), a, c),
            Ite(a, c, d) => write!(f, "(if {} {} {})", a, c, d),
            Let(a, c) => write!(f, "(let {} {})", a, c),
            Pair(a, c) => write!(f, "(pair {} {})", a, c),
            Fst(a) => write!(f, "(fst {})", a),
            Snd(a) => write!(f, "(snd {})", a),
            Inl(t, a) => write!(f, "(inl {} {})", t, a),
            Inr(t, a) => write!(f, "(inr {} {})", t, a),
            Case(a, c, d) => write!(f, "(case {} {} {})", a, c, d),
            Iter(a, c, d) => write!(f, "(iter {} {} {})", a, c, d),
            Call(j, a) => write!(f, "(call {} {})", j, a),
        }
    }
}
