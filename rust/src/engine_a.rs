// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Engine A: Lean → IR → Agda.
//!
//! Input is a Lean 4 source file that Lean itself has accepted. Engine A
//! reads a first-order, non-recursive subset of it:
//!
//!   def NAME (x : T) (y : U) … : R := EXPR
//!   theorem NAME : ∀ (x : T) …, LHS = RHS := PROOF
//!   theorem NAME : LHS = RHS := PROOF
//!
//! with T ∈ {Nat, ℕ, Int, ℤ, Bool, A × B} and expressions built from numerals,
//! true/false, + - * (Nat subtraction is truncated, as in Lean), < ≤ > ≥ = ==
//! != ≠, && || ! ¬, unary minus on Int, `if … then … else …`,
//! `let x := e; body`, type ascription `(e : T)` (including the Nat→Int
//! cast), pairs `(a, b)` with `.1 .2 .fst .snd`, and application of earlier
//! definitions. Definitions are δ-unfolded (inlined through fresh `let`
//! bindings), which is the same unfolding Lean performs definitionally.
//!
//! Everything else is rejected with an explicit reason: ∃, ∧, ∨, ↔, →, /,
//! %, ^, ℝ/Real/Float, sorry, axiom, partial/noncomputable/unsafe, match and
//! equation-compiler definitions, fun/λ, higher-order binders, recursion,
//! and unknown identifiers. A theorem is never weakened: its proposition is
//! translated exactly as `∀ u → runMain L u ≡ runMain R u` where `u` packs
//! the ∀-binders right-nested, and Agda must prove that proposition.
//!
//! The Agda proof is by normalization: Engine B's verified passes (whose
//! soundness `passes-≈` is proved once in `Morph/Rewrite.agda`) are run on
//! both sides; if they reach the same normal form, the proposition follows.
//! If they do not, the theorem is reported as translated but unproved;
//! nothing is postulated.
//!
//! Correspondence evidence: for every theorem Lean's own `#eval` of both
//! sides on sampled inputs is compared with the IR interpreter, and the Lean
//! outputs are written into the Agda module as `refl` facts about the
//! translated programs, so Agda's evaluator independently agrees with Lean.

use crate::agda;
use crate::eval;
use crate::ir::*;
use crate::json::Json;
use crate::parse;
use crate::rewrite::{self, Pass};
use crate::sha256;
use std::path::{Path, PathBuf};
use std::process::Command;

// ------------------------------------------------------------------ lexer

#[derive(Clone, Debug, PartialEq)]
struct Tok {
    s: String,
    line: usize,
}

const SYMS: &[&str] = &[
    ":=", "<=", ">=", "==", "!=", "&&", "||", "=>", "(", ")", ",", ":", "+", "-", "*", "<", ">", "=", "!", ";", "/", "%", "^",
    "|", "[", "]", "{", "}", "⟨", "⟩", "∀", "∃", "→", "×", "ℕ", "ℤ", "ℝ", "≤", "≥", "≠", "¬", "∧", "∨", "↔", "λ", "↦", "·", "∘",
];

fn lex(src: &str) -> Result<Vec<Tok>, String> {
    let cs: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut line = 1;
    let mut out = Vec::new();
    while i < cs.len() {
        let c = cs[i];
        if c == '\n' {
            line += 1;
            i += 1;
        } else if c.is_whitespace() {
            i += 1;
        } else if c == '-' && cs.get(i + 1) == Some(&'-') {
            while i < cs.len() && cs[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && cs.get(i + 1) == Some(&'-') {
            let mut depth = 0usize;
            loop {
                if i + 1 >= cs.len() {
                    return Err("unterminated block comment".into());
                }
                if cs[i] == '/' && cs[i + 1] == '-' {
                    depth += 1;
                    i += 2;
                } else if cs[i] == '-' && cs[i + 1] == '/' {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    if cs[i] == '\n' {
                        line += 1;
                    }
                    i += 1;
                }
            }
        } else if c.is_ascii_digit() {
            let st = i;
            while i < cs.len() && cs[i].is_ascii_digit() {
                i += 1;
            }
            out.push(Tok { s: cs[st..i].iter().collect(), line });
        } else if c.is_alphabetic() || c == '_' || c == '#' {
            let st = i;
            i += 1;
            while i < cs.len() && (cs[i].is_alphanumeric() || cs[i] == '_' || cs[i] == '\'' || cs[i] == '.' || cs[i] == '!' || cs[i] == '?')
                && !matches!(cs[i], 'ℕ' | 'ℤ' | 'ℝ' | 'λ')
            {
                i += 1;
            }
            out.push(Tok { s: cs[st..i].iter().collect(), line });
        } else {
            let rest: String = cs[i..cs.len().min(i + 2)].iter().collect();
            match SYMS.iter().find(|s| rest.starts_with(**s)) {
                Some(s) => {
                    out.push(Tok { s: s.to_string(), line });
                    i += s.chars().count();
                }
                None => {
                    out.push(Tok { s: c.to_string(), line });
                    i += 1;
                }
            }
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------- surface

#[derive(Clone, Debug, PartialEq)]
pub enum LTy {
    Nat,
    Int,
    Bool,
    Prod(Box<LTy>, Box<LTy>),
}

impl LTy {
    fn morph(&self) -> String {
        match self {
            LTy::Nat => "nat".into(),
            LTy::Int => "int".into(),
            LTy::Bool => "bool".into(),
            LTy::Prod(a, b) => format!("(* {} {})", a.morph(), b.morph()),
        }
    }
    fn lean(&self) -> String {
        match self {
            LTy::Nat => "Nat".into(),
            LTy::Int => "Int".into(),
            LTy::Bool => "Bool".into(),
            LTy::Prod(a, b) => format!("({} × {})", a.lean(), b.lean()),
        }
    }
}

#[derive(Clone, Debug)]
enum LE {
    Num(u64),
    Bool(bool),
    Var(String),
    App(String, Vec<LE>),
    Bin(String, Box<LE>, Box<LE>),
    Neg(Box<LE>),
    Not(Box<LE>),
    If(Box<LE>, Box<LE>, Box<LE>),
    Let(String, Box<LE>, Box<LE>),
    Asc(Box<LE>, LTy),
    Pair(Box<LE>, Box<LE>),
    Proj(Box<LE>, u8),
}

fn reject_token(t: &str) -> Option<&'static str> {
    Some(match t {
        "∃" => "existential quantifier ∃ is not in the translated subset",
        "∧" => "conjunction ∧ in a proposition is not in the subset (state one equation per theorem)",
        "∨" => "disjunction ∨ is not in the subset",
        "↔" => "iff ↔ is not in the subset",
        "→" => "function types / implications → are not in the subset (first-order ∀ binders only)",
        "/" => "division / has no IR operator",
        "%" => "modulo % has no IR operator",
        "^" => "exponentiation ^ has no IR operator",
        "ℝ" | "Real" => "real numbers ℝ have no IR type",
        "Float" => "Float has no IR type",
        "sorry" => "sorry: the declaration is not proved",
        "fun" | "λ" | "↦" => "lambda abstractions are not in the first-order subset",
        "match" | "|" => "pattern matching / equation-compiler definitions are not in the subset",
        "⟨" | "⟩" => "anonymous constructors ⟨…⟩ are not in the subset",
        "∘" | "·" => "function composition / sections are not in the subset",
        "[" | "]" => "lists are not in the subset",
        "{" | "}" => "implicit binders / structures are not in the subset",
        "String" | "List" | "Array" | "Option" => "type has no IR counterpart",
        _ => return None,
    })
}

struct P<'a> {
    t: &'a [Tok],
    i: usize,
}

type PR<T> = Result<T, String>;

impl<'a> P<'a> {
    fn peek(&self) -> Option<&str> {
        self.t.get(self.i).map(|t| t.s.as_str())
    }
    fn line(&self) -> usize {
        self.t.get(self.i).or(self.t.last()).map(|t| t.line).unwrap_or(0)
    }
    fn next(&mut self) -> PR<String> {
        let t = self.t.get(self.i).ok_or("unexpected end of declaration")?.s.clone();
        if let Some(r) = reject_token(&t) {
            return Err(format!("line {}: {}", self.line(), r));
        }
        self.i += 1;
        Ok(t)
    }
    fn eat(&mut self, s: &str) -> bool {
        if self.peek() == Some(s) {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, s: &str) -> PR<()> {
        let l = self.line();
        let t = self.next()?;
        if t == s {
            Ok(())
        } else {
            Err(format!("line {}: expected `{}`, found `{}`", l, s, t))
        }
    }
    fn ident(&mut self) -> PR<String> {
        let l = self.line();
        let t = self.next()?;
        if t.chars().next().map(|c| c.is_alphabetic() || c == '_').unwrap_or(false) && !KEYWORDS.contains(&t.as_str()) {
            Ok(t)
        } else {
            Err(format!("line {}: expected identifier, found `{}`", l, t))
        }
    }
    fn ty(&mut self) -> PR<LTy> {
        let a = self.ty_atom()?;
        if self.eat("×") {
            let b = self.ty()?;
            return Ok(LTy::Prod(Box::new(a), Box::new(b)));
        }
        if let Some(r) = self.peek().and_then(reject_token) {
            if self.peek() == Some("→") {
                return Err(format!("line {}: {}", self.line(), r));
            }
        }
        Ok(a)
    }
    fn ty_atom(&mut self) -> PR<LTy> {
        let l = self.line();
        let t = self.next()?;
        match t.as_str() {
            "Nat" | "ℕ" => Ok(LTy::Nat),
            "Int" | "ℤ" => Ok(LTy::Int),
            "Bool" => Ok(LTy::Bool),
            "(" => {
                let x = self.ty()?;
                self.expect(")")?;
                Ok(x)
            }
            _ => Err(format!("line {}: type `{}` has no IR counterpart (Nat, Int, Bool, ×)", l, t)),
        }
    }
    fn binders(&mut self) -> PR<Vec<(String, LTy)>> {
        let mut bs = Vec::new();
        while self.peek() == Some("(") {
            self.i += 1;
            let mut names = vec![self.ident()?];
            while self.peek() != Some(":") {
                names.push(self.ident()?);
            }
            self.expect(":")?;
            let t = self.ty()?;
            self.expect(")")?;
            for n in names {
                bs.push((n, t.clone()));
            }
        }
        Ok(bs)
    }
    // precedence climbing
    fn expr(&mut self) -> PR<LE> {
        match self.peek() {
            Some("if") => {
                self.i += 1;
                let c = self.expr()?;
                self.expect("then")?;
                let a = self.expr()?;
                self.expect("else")?;
                let b = self.expr()?;
                Ok(LE::If(Box::new(c), Box::new(a), Box::new(b)))
            }
            Some("let") => {
                self.i += 1;
                let n = self.ident()?;
                let asc = if self.eat(":") { Some(self.ty()?) } else { None };
                self.expect(":=")?;
                let v = self.expr()?;
                let v = match asc {
                    Some(t) => LE::Asc(Box::new(v), t),
                    None => v,
                };
                self.eat(";");
                let body = self.expr()?;
                Ok(LE::Let(n, Box::new(v), Box::new(body)))
            }
            _ => self.bin(0),
        }
    }
    fn bin(&mut self, min: u8) -> PR<LE> {
        let mut lhs = self.unary()?;
        loop {
            let op = match self.peek() {
                Some(o) => o.to_string(),
                None => break,
            };
            if let Some(r) = reject_token(&op) {
                if !matches!(op.as_str(), "|" | "]" | "}" | "⟩") {
                    return Err(format!("line {}: {}", self.line(), r));
                }
            }
            let prec = match op.as_str() {
                "||" => 30,
                "&&" => 35,
                "=" | "==" | "!=" | "≠" | "<" | ">" | "<=" | ">=" | "≤" | "≥" => 50,
                "+" | "-" => 65,
                "*" => 70,
                _ => break,
            };
            if prec < min {
                break;
            }
            self.i += 1;
            let next_min = if prec == 50 { 51 } else { prec + 1 };
            let rhs = match self.peek() {
                Some("if") | Some("let") => self.expr()?,
                _ => self.bin(next_min)?,
            };
            lhs = LE::Bin(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }
    fn unary(&mut self) -> PR<LE> {
        if self.eat("-") {
            return Ok(LE::Neg(Box::new(self.bin(75)?)));
        }
        if self.eat("!") || self.eat("¬") {
            return Ok(LE::Not(Box::new(self.bin(75)?)));
        }
        self.app()
    }
    fn app(&mut self) -> PR<LE> {
        let l = self.line();
        let head = self.atom()?;
        if let LE::Var(f) = &head {
            let mut args = Vec::new();
            // arguments must start on the same line (Lean uses layout; the
            // subset requires single-line applications)
            while let Some(t) = self.t.get(self.i) {
                if t.line != l || !starts_atom(&t.s) {
                    break;
                }
                args.push(self.atom()?);
            }
            if !args.is_empty() {
                return Ok(LE::App(f.clone(), args));
            }
        }
        Ok(head)
    }
    fn atom(&mut self) -> PR<LE> {
        let l = self.line();
        let t = self.next()?;
        if t.chars().all(|c| c.is_ascii_digit()) {
            return t.parse().map(LE::Num).map_err(|e| format!("line {}: numeral {}: {}", l, t, e));
        }
        match t.as_str() {
            "true" => return Ok(LE::Bool(true)),
            "false" => return Ok(LE::Bool(false)),
            "(" => {
                let e = self.expr()?;
                if self.eat(":") {
                    let ty = self.ty()?;
                    self.expect(")")?;
                    return Ok(LE::Asc(Box::new(e), ty));
                }
                if self.eat(",") {
                    let b = self.expr()?;
                    self.expect(")")?;
                    let p = LE::Pair(Box::new(e), Box::new(b));
                    return Ok(self.projs(p));
                }
                self.expect(")")?;
                return Ok(self.projs(e));
            }
            _ => {}
        }
        if KEYWORDS.contains(&t.as_str()) || !t.chars().next().map(|c| c.is_alphabetic() || c == '_').unwrap_or(false) {
            return Err(format!("line {}: unexpected `{}`", l, t));
        }
        // x.1 / x.2 / x.fst / x.snd suffixes
        let mut parts = t.split('.');
        let base = parts.next().unwrap_or("").to_string();
        let mut e = LE::Var(base);
        let rest: Vec<&str> = parts.collect();
        let mut qualified = Vec::new();
        for r in rest {
            match r {
                "1" | "fst" => e = LE::Proj(Box::new(e), 1),
                "2" | "snd" => e = LE::Proj(Box::new(e), 2),
                other => qualified.push(other.to_string()),
            }
        }
        if !qualified.is_empty() {
            if let LE::Var(b) = &e {
                // a qualified name such as Namespace.f
                return Ok(LE::Var(format!("{}.{}", b, qualified.join("."))));
            }
            return Err(format!("line {}: unsupported projection in `{}`", l, t));
        }
        Ok(e)
    }
    fn projs(&mut self, mut e: LE) -> LE {
        // `(p).1` is lexed as `)` followed by an identifier-less `.`; the
        // subset only supports projections written as `x.1`.
        while let Some(t) = self.peek() {
            if t == "." {
                self.i += 1;
                match self.peek() {
                    Some("1") | Some("fst") => {
                        self.i += 1;
                        e = LE::Proj(Box::new(e), 1)
                    }
                    Some("2") | Some("snd") => {
                        self.i += 1;
                        e = LE::Proj(Box::new(e), 2)
                    }
                    _ => break,
                }
            } else {
                break;
            }
        }
        e
    }
}

const KEYWORDS: &[&str] = &["if", "then", "else", "let", "def", "theorem", "lemma", "by", "in", "do", "where", "fun", "match", "with"];

fn starts_atom(s: &str) -> bool {
    s == "(" || s == "true" || s == "false" || s.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false)
        || (s.chars().next().map(|c| c.is_alphabetic() || c == '_').unwrap_or(false) && !KEYWORDS.contains(&s) && reject_token(s).is_none())
}

// ------------------------------------------------------------- elaboration

#[derive(Clone, Debug)]
pub struct LDef {
    pub name: String,
    pub params: Vec<(String, LTy)>,
    pub ret: LTy,
    body: LE,
}

struct El<'a> {
    defs: &'a [LDef],
    fresh: usize,
    current: &'a str,
    namespaces: &'a [String],
}

/// Environment entry: Lean name → (surface expression, type).
type Env = Vec<(String, String, LTy)>;

fn lookup<'e>(env: &'e Env, n: &str) -> Option<&'e (String, String, LTy)> {
    env.iter().rev().find(|(m, _, _)| m == n)
}

fn is_numeral(e: &LE) -> bool {
    match e {
        LE::Num(_) => true,
        LE::Neg(a) => is_numeral(a),
        LE::Bin(o, a, b) if matches!(o.as_str(), "+" | "-" | "*") => is_numeral(a) && is_numeral(b),
        _ => false,
    }
}

impl<'a> El<'a> {
    fn find_def(&self, n: &str) -> Option<&'a LDef> {
        let mut cands = vec![n.to_string()];
        for k in 0..self.namespaces.len() {
            if let Some(stripped) = n.strip_prefix(&format!("{}.", self.namespaces[k..].join("."))) {
                cands.push(stripped.to_string());
            }
        }
        self.defs.iter().rev().find(|d| cands.contains(&d.name))
    }
    fn e(&mut self, env: &Env, e: &LE, want: Option<&LTy>) -> PR<(String, LTy)> {
        match e {
            LE::Num(n) => match want {
                Some(LTy::Int) => Ok((format!("(int {})", n), LTy::Int)),
                Some(LTy::Nat) | None => Ok((format!("(nat {})", n), LTy::Nat)),
                Some(t) => Err(format!("numeral {} used at type {}", n, t.lean())),
            },
            LE::Bool(b) => Ok((b.to_string(), LTy::Bool)),
            LE::Var(n) => {
                if let Some((_, s, t)) = lookup(env, n) {
                    return Ok((s.clone(), t.clone()));
                }
                if n == self.current {
                    return Err(format!("recursion: `{}` refers to itself", n));
                }
                if let Some(r) = reject_token(n) {
                    return Err(r.into());
                }
                match self.find_def(n) {
                    Some(d) if d.params.is_empty() => self.inline(env, d, &[]),
                    Some(d) => Err(format!("`{}` used without its {} arguments (partial application is not in the subset)", n, d.params.len())),
                    None => Err(format!("unknown identifier `{}`", n)),
                }
            }
            LE::App(f, args) => {
                if lookup(env, f).is_some() {
                    return Err(format!("`{}` is a variable, not a function (higher-order application)", f));
                }
                if f == self.current {
                    return Err(format!("recursion: `{}` calls itself", f));
                }
                match f.as_str() {
                    "Int.ofNat" | "Int.toNat" | "Nat.succ" if args.len() == 1 => {
                        let (s, t) = self.e(env, &args[0], None)?;
                        return match (f.as_str(), t) {
                            ("Int.ofNat", LTy::Nat) => Ok((format!("(toint {})", s), LTy::Int)),
                            ("Nat.succ", LTy::Nat) => Ok((format!("(add {} (nat 1))", s), LTy::Nat)),
                            ("Int.toNat", _) => Err("Int.toNat has no IR operator".into()),
                            (_, t) => Err(format!("{} applied to {}", f, t.lean())),
                        };
                    }
                    _ => {}
                }
                let d = self.find_def(f).ok_or_else(|| format!("unknown function `{}`", f))?;
                if d.params.len() != args.len() {
                    return Err(format!("`{}` expects {} arguments, got {}", f, d.params.len(), args.len()));
                }
                self.inline(env, d, args)
            }
            LE::Bin(o, a, b) => self.bin(env, o, a, b, want),
            LE::Neg(a) => {
                if let LE::Num(n) = **a {
                    if want == Some(&LTy::Int) || want.is_none() {
                        return Ok((format!("(int -{})", n), LTy::Int));
                    }
                }
                let (s, t) = self.e(env, a, Some(&LTy::Int))?;
                if t != LTy::Int {
                    return Err(format!("unary minus on {} (only Int)", t.lean()));
                }
                Ok((format!("(neg {})", s), LTy::Int))
            }
            LE::Not(a) => {
                let (s, t) = self.e(env, a, Some(&LTy::Bool))?;
                if t != LTy::Bool {
                    return Err(format!("negation of {}", t.lean()));
                }
                Ok((format!("(not {})", s), LTy::Bool))
            }
            LE::If(c, x, y) => {
                let (cs, ct) = self.e(env, c, Some(&LTy::Bool))?;
                if ct != LTy::Bool {
                    return Err("if-condition is not Bool or a decidable comparison".into());
                }
                let (xs, xt, ys) = if is_numeral(x) && !is_numeral(y) {
                    let (ys, yt) = self.e(env, y, want)?;
                    let (xs, _) = self.e(env, x, Some(&yt))?;
                    (xs, yt, ys)
                } else {
                    let (xs, xt) = self.e(env, x, want)?;
                    let (ys, _) = self.e(env, y, Some(&xt))?;
                    (xs, xt, ys)
                };
                Ok((format!("(if {} {} {})", cs, xs, ys), xt))
            }
            LE::Let(n, v, body) => {
                let (vs, vt) = self.e(env, v, None)?;
                let f = self.fresh_name();
                let mut env2 = env.clone();
                env2.push((n.clone(), f.clone(), vt));
                let (bs, bt) = self.e(&env2, body, want)?;
                Ok((format!("(let {} {} {})", f, vs, bs), bt))
            }
            LE::Asc(x, t) => {
                let (s, xt) = self.e(env, x, Some(t))?;
                if &xt == t {
                    Ok((s, xt))
                } else if xt == LTy::Nat && *t == LTy::Int {
                    Ok((format!("(toint {})", s), LTy::Int))
                } else {
                    Err(format!("ascription ({} : {}) needs a coercion with no IR counterpart", xt.lean(), t.lean()))
                }
            }
            LE::Pair(a, b) => {
                let (wa, wb) = match want {
                    Some(LTy::Prod(p, q)) => (Some(&**p), Some(&**q)),
                    _ => (None, None),
                };
                let (sa, ta) = self.e(env, a, wa)?;
                let (sb, tb) = self.e(env, b, wb)?;
                Ok((format!("(pair {} {})", sa, sb), LTy::Prod(Box::new(ta), Box::new(tb))))
            }
            LE::Proj(x, k) => {
                let (s, t) = self.e(env, x, None)?;
                match t {
                    LTy::Prod(a, b) => Ok(if *k == 1 { (format!("(fst {})", s), *a) } else { (format!("(snd {})", s), *b) }),
                    t => Err(format!("projection .{} of non-pair type {}", k, t.lean())),
                }
            }
        }
    }
    fn fresh_name(&mut self) -> String {
        self.fresh += 1;
        format!("v{}", self.fresh)
    }
    fn inline(&mut self, env: &Env, d: &LDef, args: &[LE]) -> PR<(String, LTy)> {
        // δ-unfold: bind each argument to a fresh name, then elaborate the
        // closed body of `d` in an environment of only those names.
        let mut binds = Vec::new();
        let mut inner: Env = Vec::new();
        for ((pn, pt), a) in d.params.iter().zip(args) {
            let (s, t) = self.e(env, a, Some(pt))?;
            let s = if &t == pt {
                s
            } else if t == LTy::Nat && *pt == LTy::Int {
                format!("(toint {})", s)
            } else {
                return Err(format!("argument of type {} passed to `{}` parameter `{}` of type {}", t.lean(), d.name, pn, pt.lean()));
            };
            if is_simple(&s) {
                // variables, projections of variables and literals are
                // substituted directly (pure and duplicable)
                inner.push((pn.clone(), s, pt.clone()));
                continue;
            }
            let f = self.fresh_name();
            binds.push((f.clone(), s));
            inner.push((pn.clone(), f, pt.clone()));
        }
        let saved = self.current;
        let defs = self.defs;
        let idx = defs.iter().position(|x| std::ptr::eq(x, d)).unwrap_or(defs.len());
        let mut sub = El { defs: &defs[..idx], fresh: self.fresh, current: &d.name, namespaces: self.namespaces };
        let (mut body, bt) = sub.e(&inner, &d.body, Some(&d.ret))?;
        self.fresh = sub.fresh;
        self.current = saved;
        if bt != d.ret {
            return Err(format!("body of `{}` has type {} but is declared {}", d.name, bt.lean(), d.ret.lean()));
        }
        for (f, s) in binds.into_iter().rev() {
            body = format!("(let {} {} {})", f, s, body);
        }
        Ok((body, bt))
    }
    fn bin(&mut self, env: &Env, o: &str, a: &LE, b: &LE, want: Option<&LTy>) -> PR<(String, LTy)> {
        let arith = matches!(o, "+" | "-" | "*");
        // operand typing: synthesize the non-numeral side first
        let operand_want = if arith { want } else { None };
        let (sa, ta, sb, tb) = if is_numeral(a) && !is_numeral(b) {
            let (sb, tb) = self.e(env, b, operand_want)?;
            let (sa, ta) = self.e(env, a, Some(&tb))?;
            (sa, ta, sb, tb)
        } else {
            let (sa, ta) = self.e(env, a, if is_numeral(a) && is_numeral(b) { operand_want } else { operand_want.filter(|_| arith) })?;
            let (sb, tb) = self.e(env, b, Some(&ta))?;
            (sa, ta, sb, tb)
        };
        // Lean's binop elaborator inserts ↑ (Nat → Int) on the Nat side
        let (sa, ta, sb, tb) = match (&ta, &tb) {
            (LTy::Nat, LTy::Int) => (format!("(toint {})", sa), LTy::Int, sb, tb),
            (LTy::Int, LTy::Nat) => (sa, ta, format!("(toint {})", sb), LTy::Int),
            _ => (sa, ta, sb, tb),
        };
        if ta != tb {
            return Err(format!("operator {} on {} and {}", o, ta.lean(), tb.lean()));
        }
        let num = matches!(ta, LTy::Nat | LTy::Int);
        let r = match o {
            "+" | "-" | "*" if num => {
                let n = match o {
                    "+" => "add",
                    "-" => "sub",
                    _ => "mul",
                };
                (format!("({} {} {})", n, sa, sb), ta)
            }
            "<" if num => (format!("(lt {} {})", sa, sb), LTy::Bool),
            ">" if num => (format!("(lt {} {})", sb, sa), LTy::Bool),
            "≤" | "<=" if num => (format!("(not (lt {} {}))", sb, sa), LTy::Bool),
            "≥" | ">=" if num => (format!("(not (lt {} {}))", sa, sb), LTy::Bool),
            "=" | "==" if num => (format!("(eq {} {})", sa, sb), LTy::Bool),
            "≠" | "!=" if num => (format!("(not (eq {} {}))", sa, sb), LTy::Bool),
            "&&" if ta == LTy::Bool => (format!("(and {} {})", sa, sb), LTy::Bool),
            "||" if ta == LTy::Bool => (format!("(or {} {})", sa, sb), LTy::Bool),
            "=" | "==" if ta == LTy::Bool => (format!("(not (or (and {a} (not {b})) (and (not {a}) {b})))", a = sa, b = sb), LTy::Bool),
            _ => return Err(format!("operator {} on {} has no IR counterpart", o, ta.lean())),
        };
        Ok(r)
    }
}

// ------------------------------------------------------------- declarations

#[derive(Clone, Debug)]
pub enum Status {
    /// Translated and the proposition re-proved in Agda.
    Proved,
    /// Translated faithfully, but Engine B normal forms differ, so Agda has
    /// no proof; the proposition is not claimed.
    Unproved(String),
    /// Outside the subset.
    Rejected(String),
    /// Definitions are translated (no proposition).
    Definition,
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub kind: String,
    pub name: String,
    pub line: usize,
    pub status: Status,
    pub binders: Vec<(String, LTy)>,
    pub lhs_morph: Option<String>,
    pub rhs_morph: Option<String>,
    pub lhs: Option<Prog>,
    pub rhs: Option<Prog>,
    pub normal_form_rounds: Option<usize>,
    pub agda_module: Option<String>,
    pub agda_output: Option<String>,
    pub agda_ms: Option<u128>,
    pub samples: Vec<Sample>,
    pub lean_lhs_text: Option<String>,
    pub lean_rhs_text: Option<String>,
    /// LiquidHaskell refinement check of the proposition (record only).
    pub lh: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Sample {
    pub input: Val,
    pub lean_lhs: Option<String>,
    pub lean_rhs: Option<String>,
    pub ir_lhs: Result<Val, String>,
    pub ir_rhs: Result<Val, String>,
    pub agree: bool,
}

fn split_decls(toks: &[Tok]) -> Vec<(usize, usize)> {
    // a declaration starts at a top-level command keyword
    const CMDS: &[&str] = &[
        "def", "theorem", "lemma", "example", "abbrev", "axiom", "instance", "structure", "inductive", "class", "partial",
        "noncomputable", "unsafe", "private", "protected", "namespace", "end", "open", "section", "variable", "import",
        "#eval", "#check", "#print", "#reduce", "set_option", "@[", "opaque", "macro", "syntax", "notation", "universe",
        "attribute", "mutual",
    ];
    let mut starts: Vec<usize> = Vec::new();
    for (i, t) in toks.iter().enumerate() {
        let first_on_line = i == 0 || toks[i - 1].line != t.line;
        if first_on_line && CMDS.contains(&t.s.as_str()) {
            starts.push(i);
        }
    }
    let mut out = Vec::new();
    for (k, s) in starts.iter().enumerate() {
        let e = starts.get(k + 1).copied().unwrap_or(toks.len());
        out.push((*s, e));
    }
    out
}

const ROUND: [Pass; 5] = [Pass::Pe(8), Pass::Cf, Pass::Alg, Pass::Dce, Pass::Fuse];

fn round_list(n: usize) -> Vec<Pass> {
    let mut v = Vec::new();
    for _ in 0..n {
        v.extend_from_slice(&ROUND);
    }
    v
}

/// Smallest number of Engine B rounds after which both sides have the
/// same normal form (checked again by Agda; Rust is not trusted).
fn common_nf(l: &Prog, r: &Prog, max: usize) -> Result<usize, String> {
    for n in 0..=max {
        let ps = round_list(n);
        let a = rewrite::run_passes(&ps, l).map_err(|e| format!("{:?}", e))?;
        let b = rewrite::run_passes(&ps, r).map_err(|e| format!("{:?}", e))?;
        if a == b {
            return Ok(n);
        }
    }
    let ps = round_list(max);
    let a = rewrite::run_passes(&ps, l).map_err(|e| format!("{:?}", e))?;
    let b = rewrite::run_passes(&ps, r).map_err(|e| format!("{:?}", e))?;
    Err(format!("Engine B normal forms differ after {} rounds: lhs {} vs rhs {}", max, a.main().body, b.main().body))
}

fn samples_for(t: &LTy) -> Vec<Val> {
    match t {
        LTy::Nat => vec![Val::Nat(0), Val::Nat(1), Val::Nat(7), Val::Nat(1000)],
        LTy::Int => vec![Val::Int(-5), Val::Int(0), Val::Int(3), Val::Int(1000)],
        LTy::Bool => vec![Val::Bool(false), Val::Bool(true)],
        LTy::Prod(a, b) => {
            let (x, y) = (samples_for(a), samples_for(b));
            (0..x.len().max(y.len())).map(|k| Val::Pair(Box::new(x[k % x.len()].clone()), Box::new(y[(k + 1) % y.len()].clone()))).collect()
        }
    }
}

fn pack(bs: &[(String, LTy)]) -> LTy {
    match bs.len() {
        0 => LTy::Nat,
        1 => bs[0].1.clone(),
        _ => LTy::Prod(Box::new(bs[0].1.clone()), Box::new(pack(&bs[1..]))),
    }
}

/// Split a packed input value back into one value per binder.
fn unpack(bs: &[(String, LTy)], v: &Val) -> Vec<Val> {
    match (bs.len(), v) {
        (0, _) => vec![],
        (1, v) => vec![v.clone()],
        (_, Val::Pair(a, rest)) => {
            let mut o = vec![(**a).clone()];
            o.extend(unpack(&bs[1..], rest));
            o
        }
        _ => vec![],
    }
}

fn lean_val(v: &Val, t: &LTy) -> String {
    match (v, t) {
        (Val::Nat(n), _) => format!("({} : Nat)", n),
        (Val::Int(i), _) => format!("({} : Int)", i),
        (Val::Bool(b), _) => b.to_string(),
        (Val::Pair(a, b), LTy::Prod(ta, tb)) => format!("({}, {})", lean_val(a, ta), lean_val(b, tb)),
        _ => "?".into(),
    }
}

fn val_lean_print(v: &Val) -> String {
    match v {
        Val::Nat(n) => n.to_string(),
        Val::Int(i) => i.to_string(),
        Val::Bool(b) => b.to_string(),
        Val::Pair(a, b) => format!("({}, {})", val_lean_print(a), val_lean_print(b)),
        Val::Inl(a) => format!("Sum.inl {}", val_lean_print(a)),
        Val::Inr(a) => format!("Sum.inr {}", val_lean_print(a)),
    }
}

fn main_program(bs: &[(String, LTy)], defs: &[LDef], current: &str, ns: &[String], e: &LE) -> PR<(String, LTy, Prog)> {
    let at = pack(bs);
    let mut env: Env = Vec::new();
    // binder k is reached through projections of the packed argument `u`
    let n = bs.len();
    for (k, (name, t)) in bs.iter().enumerate() {
        let mut path = "u".to_string();
        if n > 1 {
            for _ in 0..k {
                path = format!("(snd {})", path);
            }
            if k < n - 1 {
                path = format!("(fst {})", path);
            }
        }
        env.push((name.clone(), path, t.clone()));
    }
    let mut el = El { defs, fresh: 0, current, namespaces: ns };
    let (body, rt) = el.e(&env, e, None)?;
    let text = format!("(def main (u {}) {}\n  {})\n", at.morph(), rt.morph(), body);
    let p = parse::parse_surface(&text).map_err(|e| format!("translated program does not typecheck in the IR: {}", e))?;
    Ok((text, rt, p))
}

pub struct Report {
    pub file: PathBuf,
    pub file_sha256: String,
    pub lean_version: String,
    pub lean_exit: Option<i32>,
    pub lean_output: String,
    pub agda_version: String,
    pub lh_version: String,
    pub decls: Vec<Decl>,
}

pub fn lean_version() -> String {
    Command::new("lean")
        .arg("--version")
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "lean not found".into())
}

fn run_lean(file: &Path, cwd: &Path) -> (Option<i32>, String) {
    match Command::new("lean").arg(file).current_dir(cwd).output() {
        Err(e) => (None, format!("lean not runnable: {}", e)),
        Ok(o) => {
            let mut s = String::from_utf8_lossy(&o.stdout).into_owned();
            s.push_str(&String::from_utf8_lossy(&o.stderr));
            (o.status.code(), s)
        }
    }
}

/// Translate one Lean file. `out` receives the generated Agda modules, the
/// Lean evaluation file and `report.json`. `check_agda=false` skips Agda
/// (used by unit tests of the translator alone).
pub fn translate_file(file: &Path, out: &Path, agda_root: &Path, check_agda: bool) -> Result<Report, String> {
    let src = std::fs::read_to_string(file).map_err(|e| format!("read {}: {}", file.display(), e))?;
    std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
    let cwd = file.parent().unwrap_or(Path::new("."));
    let (lean_exit, lean_output) = run_lean(file, cwd);
    let mut rep = Report {
        file: file.to_path_buf(),
        file_sha256: sha256::hex(src.as_bytes()),
        lean_version: lean_version(),
        lean_exit,
        lean_output: lean_output.clone(),
        agda_version: agda::agda_version().unwrap_or_else(|| "agda not found".into()),
        lh_version: crate::liquid::version().unwrap_or_else(|| "liquidhaskell not found".into()),
        decls: Vec::new(),
    };
    if lean_exit != Some(0) {
        return Err(format!("Lean rejected {} (exit {:?}): {}", file.display(), lean_exit, lean_output.trim()));
    }
    let mut decls = translate_source(&src)?;
    let stem = file.file_stem().and_then(|s| s.to_str()).unwrap_or("Input").replace(|c: char| !c.is_alphanumeric(), "");

    // Lean #eval of both sides of every translated theorem on sampled inputs
    let mut evals: Vec<(usize, usize, bool)> = Vec::new(); // (decl, sample, is_lhs)
    let mut ev = String::new();
    ev.push_str(&src);
    ev.push_str("\n-- Engine A correspondence evaluations (generated)\nset_option linter.unusedVariables false\n");
    let nss = namespaces_at_end(&src);
    let open = if nss.is_empty() { String::new() } else { format!("open {} in ", nss.join(" ")) };
    let all_ns = all_namespaces(&src);
    let open_all = if all_ns.is_empty() { String::new() } else { format!("open {} in ", all_ns.join(" ")) };
    let _ = open;
    for (di, d) in decls.iter().enumerate() {
        if d.kind != "theorem" || d.lhs.is_none() {
            continue;
        }
        for (si, s) in d.samples.iter().enumerate() {
            let vals = unpack(&d.binders, &s.input);
            for (is_lhs, text) in [(true, d.lean_lhs_text.clone().unwrap_or_default()), (false, d.lean_rhs_text.clone().unwrap_or_default())] {
                let mut lets = String::new();
                for ((n, t), v) in d.binders.iter().zip(&vals) {
                    lets.push_str(&format!("let {} : {} := {}; ", n, t.lean(), lean_val(v, t)));
                }
                ev.push_str(&format!("{}#eval IO.println (\"EA:\" ++ toString ({}{}))\n", open_all, lets, text));
                evals.push((di, si, is_lhs));
            }
        }
    }
    let evf = out.join(format!("{}_eval.lean", stem));
    std::fs::write(&evf, &ev).map_err(|e| e.to_string())?;
    let (eexit, eout) = run_lean(&evf, cwd);
    let lines: Vec<&str> = eout.lines().filter_map(|l| l.strip_prefix("EA:")).collect();
    if eexit == Some(0) && lines.len() == evals.len() {
        for ((di, si, is_lhs), l) in evals.iter().zip(lines) {
            let s = &mut decls[*di].samples[*si];
            if *is_lhs {
                s.lean_lhs = Some(l.trim().to_string());
            } else {
                s.lean_rhs = Some(l.trim().to_string());
            }
        }
    } else {
        for d in decls.iter_mut() {
            if d.kind == "theorem" && d.lhs.is_some() {
                d.status = Status::Unproved(format!("Lean evaluation of the samples failed (exit {:?}): {}", eexit, eout.trim()));
            }
        }
    }
    for d in decls.iter_mut() {
        for s in d.samples.iter_mut() {
            let ok = |lean: &Option<String>, ir: &Result<Val, String>| match (lean, ir) {
                (Some(l), Ok(v)) => *l == val_lean_print(v),
                _ => false,
            };
            s.agree = ok(&s.lean_lhs, &s.ir_lhs) && ok(&s.lean_rhs, &s.ir_rhs);
        }
        if d.kind == "theorem" && d.lhs.is_some() && d.samples.iter().any(|s| !s.agree) {
            if !matches!(d.status, Status::Unproved(_)) {
                d.status = Status::Unproved("Lean #eval and the IR interpreter disagree on a sample (translation not faithful)".into());
            }
        }
    }

    // Agda: proposition and proof by common normal form
    for d in decls.iter_mut() {
        if d.kind != "theorem" {
            continue;
        }
        let (l, r) = match (&d.lhs, &d.rhs) {
            (Some(l), Some(r)) => (l.clone(), r.clone()),
            _ => continue,
        };
        if matches!(d.status, Status::Unproved(ref m) if m.starts_with("Lean")) {
            continue;
        }
        let module = format!("EngineA{}{}", stem, d.name.replace(|c: char| !c.is_alphanumeric(), ""));
        let rounds = match common_nf(&l, &r, 4) {
            Ok(n) => Some(n),
            Err(m) => {
                d.status = Status::Unproved(m);
                None
            }
        };
        d.normal_form_rounds = rounds;
        let text = emit_theorem(&module, d, &l, &r, rounds);
        d.agda_module = Some(module.clone());
        if !check_agda {
            std::fs::write(out.join(format!("{}.agda", module)), &text).map_err(|e| e.to_string())?;
            continue;
        }
        let res = agda::check(agda_root, out, &module, &text);
        d.agda_output = Some(res.output.trim().to_string());
        d.agda_ms = Some(res.millis);
        match (res.ok, rounds) {
            (true, Some(_)) => d.status = Status::Proved,
            (true, None) => {}
            (false, _) => d.status = Status::Unproved(format!("Agda rejected the module: {}", res.output.trim())),
        }
    }
    // L1: LiquidHaskell refinement check of each representable proposition.
    // Recorded only; the proof status above is not changed by it.
    let lh_module = format!("EngineA{}LH", stem);
    let mut lh_src = crate::liquid::module_header(&lh_module);
    let mut ranges: Vec<(usize, usize, usize)> = Vec::new(); // (decl, first line, last line)
    for (di, d) in decls.iter_mut().enumerate() {
        if d.kind != "theorem" {
            continue;
        }
        let (l, r) = match (&d.lhs, &d.rhs) {
            (Some(l), Some(r)) => (l, r),
            _ => continue,
        };
        let fname = format!("thm_{}", d.name.replace(|c: char| !c.is_ascii_alphanumeric(), "_"));
        match crate::liquid::lemma(&fname, l, r) {
            Ok(t) => {
                let first = lh_src.lines().count() + 1;
                lh_src.push_str(&t);
                lh_src.push('\n');
                ranges.push((di, first, lh_src.lines().count()));
            }
            Err(m) => d.lh = Some(format!("not representable: {}", m)),
        }
    }
    if !ranges.is_empty() {
        let lhf = out.join(format!("{}.hs", lh_module));
        std::fs::write(&lhf, &lh_src).map_err(|e| e.to_string())?;
        let run = crate::liquid::check_file(&lhf, &out.join("lh-build"));
        std::fs::write(out.join(format!("{}.lh.txt", lh_module)), &run.output).map_err(|e| e.to_string())?;
        for (di, a, b) in ranges {
            let bad = run.error_lines.iter().any(|n| *n >= a && *n <= b);
            decls[di].lh = Some(if run.ok {
                "SAFE".into()
            } else if bad {
                format!("UNSAFE (see {}.lh.txt)", lh_module)
            } else if run.error_lines.is_empty() {
                format!("ERROR: LiquidHaskell did not complete (exit {:?})", run.exit)
            } else {
                "SAFE (module UNSAFE elsewhere)".into()
            });
        }
    }
    rep.decls = decls;
    std::fs::write(out.join("report.json"), report_json(&rep).dump()).map_err(|e| e.to_string())?;
    Ok(rep)
}

fn namespaces_at_end(src: &str) -> Vec<String> {
    let mut st: Vec<String> = Vec::new();
    for l in src.lines() {
        let w: Vec<&str> = l.split_whitespace().collect();
        match w.as_slice() {
            ["namespace", n, ..] => st.push(n.to_string()),
            ["end", n, ..] if st.last().map(|s| s == n).unwrap_or(false) => {
                st.pop();
            }
            _ => {}
        }
    }
    st
}

fn all_namespaces(src: &str) -> Vec<String> {
    let mut st: Vec<String> = Vec::new();
    let mut full: Vec<String> = Vec::new();
    for l in src.lines() {
        let w: Vec<&str> = l.split_whitespace().collect();
        match w.as_slice() {
            ["namespace", n, ..] => {
                st.push(n.to_string());
                let f = st.join(".");
                if !full.contains(&f) {
                    full.push(f);
                }
            }
            ["end", n, ..] if st.last().map(|s| s == n).unwrap_or(false) => {
                st.pop();
            }
            _ => {}
        }
    }
    full
}

fn tok_text(toks: &[Tok]) -> String {
    let mut s = String::new();
    for (k, t) in toks.iter().enumerate() {
        if k > 0 {
            s.push(' ');
        }
        s.push_str(&t.s);
    }
    s
}

/// Translate declarations of an (already Lean-checked) source text. Each
/// declaration is independent: one rejection does not stop the others,
/// but anything depending on a rejected definition is rejected too.
pub fn translate_source(src: &str) -> Result<Vec<Decl>, String> {
    let toks = lex(src)?;
    let mut defs: Vec<LDef> = Vec::new();
    let mut rejected: Vec<String> = Vec::new();
    let mut out = Vec::new();
    let mut ns: Vec<String> = Vec::new();
    for (s, e) in split_decls(&toks) {
        let d = &toks[s..e];
        let kw = d[0].s.as_str();
        let line = d[0].line;
        let mk = |kind: &str, name: &str, status: Status| Decl {
            kind: kind.into(),
            name: name.into(),
            line,
            status,
            binders: vec![],
            lhs_morph: None,
            rhs_morph: None,
            lhs: None,
            rhs: None,
            normal_form_rounds: None,
            agda_module: None,
            agda_output: None,
            agda_ms: None,
            samples: vec![],
            lean_lhs_text: None,
            lean_rhs_text: None,
            lh: None,
        };
        match kw {
            "namespace" => {
                if let Some(n) = d.get(1) {
                    ns.push(n.s.clone());
                }
                continue;
            }
            "end" => {
                ns.pop();
                continue;
            }
            "open" | "section" | "import" | "set_option" | "universe" => continue,
            "#eval" | "#check" | "#print" | "#reduce" => continue,
            "def" | "theorem" | "lemma" => {}
            other => {
                let name = d.get(1).map(|t| t.s.clone()).unwrap_or_default();
                rejected.push(name.clone());
                out.push(mk(other, &name, Status::Rejected(format!("`{}` declarations are not in the translated subset", other))));
                continue;
            }
        }
        let name = d.get(1).map(|t| t.s.clone()).unwrap_or_default();
        let mut p = P { t: &d[2..], i: 0 };
        if kw == "def" {
            let r: PR<LDef> = (|| {
                let params = p.binders()?;
                p.expect(":")?;
                let ret = p.ty()?;
                p.expect(":=")?;
                let body = p.expr()?;
                if p.i != p.t.len() {
                    return Err(format!("line {}: unexpected `{}` after the definition body", p.line(), p.t[p.i].s));
                }
                Ok(LDef { name: name.clone(), params, ret, body })
            })();
            match r {
                Err(m) => {
                    rejected.push(name.clone());
                    out.push(mk("def", &name, Status::Rejected(m)));
                }
                Ok(ld) => {
                    // elaborate once in isolation to type-check and to catch
                    // recursion / unknown identifiers / rejected dependencies
                    let mut env: Env = Vec::new();
                    for (k, (pn, pt)) in ld.params.iter().enumerate() {
                        env.push((pn.clone(), format!("p{}", k), pt.clone()));
                    }
                    let dep = rejected.iter().find(|r| mentions(&ld.body, r)).cloned();
                    let mut el = El { defs: &defs, fresh: 0, current: &name, namespaces: &ns };
                    let chk = match dep {
                        Some(r) => Err(format!("depends on rejected declaration `{}`", r)),
                        None => el.e(&env, &ld.body, Some(&ld.ret)).and_then(|(_, t)| {
                            if t == ld.ret {
                                Ok(())
                            } else {
                                Err(format!("body has type {} but is declared {}", t.lean(), ld.ret.lean()))
                            }
                        }),
                    };
                    match chk {
                        Err(m) => {
                            rejected.push(name.clone());
                            out.push(mk("def", &name, Status::Rejected(m)));
                        }
                        Ok(()) => {
                            let mut dd = mk("def", &name, Status::Definition);
                            dd.binders = ld.params.clone();
                            out.push(dd);
                            defs.push(ld);
                        }
                    }
                }
            }
            continue;
        }
        // theorem NAME : [∀ binders,] lhs = rhs := proof
        let colon = d.iter().position(|t| t.s == ":");
        let assign = d.iter().position(|t| t.s == ":=");
        let r: PR<Decl> = (|| {
            let (c, a) = match (colon, assign) {
                (Some(c), Some(a)) if c < a => (c, a),
                _ => return Err("theorem must have the form `theorem n : prop := proof`".into()),
            };
            if let Some(t) = d[a + 1..].iter().find(|t| t.s == "sorry" || t.s == "admit" || t.s == "native_decide") {
                return Err(format!("line {}: proof uses `{}`; not a checked proof", t.line, t.s));
            }
            let stmt = &d[c + 1..a];
            let mut q = P { t: stmt, i: 0 };
            let mut binders = Vec::new();
            if q.eat("∀") {
                if q.peek() == Some("(") {
                    binders = q.binders()?;
                } else {
                    let mut names = vec![q.ident()?];
                    while q.peek() != Some(":") && q.peek() != Some(",") {
                        names.push(q.ident()?);
                    }
                    q.expect(":")?;
                    let t = q.ty()?;
                    for n in names {
                        binders.push((n, t.clone()));
                    }
                }
                q.expect(",")?;
            }
            // split at the top-level `=` of the proposition
            let rest = &stmt[q.i..];
            for t in rest {
                if let Some(r) = reject_token(&t.s) {
                    return Err(format!("line {}: {}", t.line, r));
                }
            }
            let mut depth = 0i32;
            let mut eq = None;
            for (k, t) in rest.iter().enumerate() {
                match t.s.as_str() {
                    "(" => depth += 1,
                    ")" => depth -= 1,
                    "=" if depth == 0 => {
                        if eq.is_some() {
                            return Err("proposition has more than one top-level `=`".into());
                        }
                        eq = Some(k)
                    }
                    _ => {}
                }
            }
            let eq = eq.ok_or("proposition must be an equation `lhs = rhs` (other propositions are not in the subset)")?;
            let (lt, rt) = (&rest[..eq], &rest[eq + 1..]);
            let parse_side = |ts: &[Tok]| -> PR<LE> {
                let mut s = P { t: ts, i: 0 };
                let e = s.expr()?;
                if s.i != ts.len() {
                    return Err(format!("line {}: unexpected `{}`", s.line(), ts[s.i].s));
                }
                Ok(e)
            };
            let le = parse_side(lt)?;
            let re = parse_side(rt)?;
            for r in &rejected {
                if mentions(&le, r) || mentions(&re, r) {
                    return Err(format!("depends on rejected declaration `{}`", r));
                }
            }
            // Lean elaborates `lhs = rhs` at one type: unify numerals
            let (ltext, lty, lp) = main_program(&binders, &defs, "", &ns, &le)?;
            let re2 = if is_numeral(&re) { LE::Asc(Box::new(re.clone()), lty.clone()) } else { re.clone() };
            let (rtext, rty, rp) = main_program(&binders, &defs, "", &ns, &re2)?;
            let (ltext, lp) = if lty != rty && is_numeral(&le) {
                let (t2, _, p2) = main_program(&binders, &defs, "", &ns, &LE::Asc(Box::new(le.clone()), rty.clone()))?;
                (t2, p2)
            } else if lty != rty {
                return Err(format!("sides have different types {} and {}", lty.lean(), rty.lean()));
            } else {
                (ltext, lp)
            };
            let mut dd = mk("theorem", &name, Status::Definition);
            dd.binders = binders.clone();
            dd.lean_lhs_text = Some(tok_text(lt));
            dd.lean_rhs_text = Some(tok_text(rt));
            let pk = pack(&binders);
            let ins = if binders.is_empty() { vec![Val::Nat(0)] } else { samples_for(&pk) };
            for u in ins {
                dd.samples.push(Sample {
                    input: u.clone(),
                    lean_lhs: None,
                    lean_rhs: None,
                    ir_lhs: eval::run_main(&lp, u.clone()).map_err(|e| format!("{:?}", e)),
                    ir_rhs: eval::run_main(&rp, u.clone()).map_err(|e| format!("{:?}", e)),
                    agree: false,
                });
            }
            dd.lhs_morph = Some(ltext);
            dd.rhs_morph = Some(rtext);
            dd.lhs = Some(lp);
            dd.rhs = Some(rp);
            dd.status = Status::Unproved("not yet checked".into());
            Ok(dd)
        })();
        match r {
            Ok(dd) => out.push(dd),
            Err(m) => out.push(mk("theorem", &name, Status::Rejected(m))),
        }
    }
    Ok(out)
}

fn mentions(e: &LE, n: &str) -> bool {
    match e {
        LE::Var(v) => v == n || v.ends_with(&format!(".{}", n)),
        LE::App(f, a) => f == n || f.ends_with(&format!(".{}", n)) || a.iter().any(|x| mentions(x, n)),
        LE::Bin(_, a, b) | LE::Pair(a, b) => mentions(a, n) || mentions(b, n),
        LE::Neg(a) | LE::Not(a) | LE::Asc(a, _) | LE::Proj(a, _) => mentions(a, n),
        LE::If(c, a, b) => mentions(c, n) || mentions(a, n) || mentions(b, n),
        LE::Let(_, v, b) => mentions(v, n) || mentions(b, n),
        LE::Num(_) | LE::Bool(_) => false,
    }
}

fn passes_agda(ps: &[Pass]) -> String {
    let mut s = String::from("[]");
    for p in ps.iter().rev() {
        s = format!("({} ∷ {})", p.agda(), s);
    }
    s
}

fn lean_out_to_val(s: &str, like: &Val) -> Option<Val> {
    match like {
        Val::Nat(_) => s.parse().ok().map(Val::Nat),
        Val::Int(_) => s.parse().ok().map(Val::Int),
        Val::Bool(_) => match s {
            "true" => Some(Val::Bool(true)),
            "false" => Some(Val::Bool(false)),
            _ => None,
        },
        _ => None,
    }
}

pub fn emit_theorem(module: &str, d: &Decl, l: &Prog, r: &Prog, rounds: Option<usize>) -> String {
    let mut o = String::new();
    o.push_str(agda::HEADER);
    o.push_str("-- GENERATED by Engine A (Lean → IR → Agda). Checked with --safe.\n");
    o.push_str(&format!("-- Lean theorem: {}\n", d.name));
    o.push_str(&format!(
        "-- Lean statement: ∀ {}, {} = {}\n",
        d.binders.iter().map(|(n, t)| format!("({} : {})", n, t.lean())).collect::<Vec<_>>().join(" "),
        d.lean_lhs_text.clone().unwrap_or_default(),
        d.lean_rhs_text.clone().unwrap_or_default()
    ));
    o.push_str("-- The ∀-binders are packed right-nested into the single argument u.\n");
    o.push_str(&format!("-- lhs sha256 {}\n-- rhs sha256 {}\n", l.hash(), r.hash()));
    o.push_str("{-# OPTIONS --safe #-}\n");
    o.push_str(&format!("module {} where\n\n", module));
    o.push_str("open import Data.Nat using (ℕ)\nopen import Data.Integer using (+_; -[1+_])\nopen import Data.Bool using (true; false)\nopen import Data.Product using (_,_)\nopen import Data.List using (List; []; _∷_)\nopen import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)\nopen import Morph.IR\nopen import Morph.Rewrite\n\n");
    o.push_str(&format!("lhs : Prog {}\nlhs = {}\n\n", agda::sig(l), agda::prog(l)));
    o.push_str(&format!("rhs : Prog {}\nrhs = {}\n\n", agda::sig(r), agda::prog(r)));
    if let Some(n) = rounds {
        let ps = passes_agda(&round_list(n));
        o.push_str(&format!("-- Engine B normalization script ({} rounds of pe 8, cf, alg, dce, fuse)\nnorm : List Pass\nnorm = {}\n\n", n, ps));
        o.push_str("-- both sides normalize to the same program\nnf-eq : runPasses norm lhs ≡ runPasses norm rhs\nnf-eq = refl\n\n");
        o.push_str("-- the translated Lean proposition\nprop : ∀ u → runMain lhs u ≡ runMain rhs u\nprop u = trans (sym (passes-≈ norm lhs u)) (trans (cong (λ P → runMain P u) nf-eq) (passes-≈ norm rhs u))\n\n");
    } else {
        o.push_str("-- No common Engine B normal form: the proposition is not proved here\n-- and is not stated as a theorem (no axioms are added).\n\n");
    }
    o.push_str("-- correspondence: Lean's #eval outputs, checked by Agda's evaluator\n");
    let mut k = 0;
    for s in &d.samples {
        for (lean, prog, ir) in [(&s.lean_lhs, "lhs", &s.ir_lhs), (&s.lean_rhs, "rhs", &s.ir_rhs)] {
            if let (Some(lv), Ok(iv)) = (lean, ir) {
                if let Some(v) = lean_out_to_val(lv, iv) {
                    o.push_str(&format!("lean-{k} : runMain {} {} ≡ {}\nlean-{k} = refl\n\n", prog, agda::val(&s.input), agda::val(&v)));
                    k += 1;
                }
            }
        }
    }
    o
}

fn status_json(s: &Status) -> (String, Option<String>) {
    match s {
        Status::Proved => ("proved_in_agda".into(), None),
        Status::Unproved(m) => ("translated_unproved".into(), Some(m.clone())),
        Status::Rejected(m) => ("rejected".into(), Some(m.clone())),
        Status::Definition => ("definition_translated".into(), None),
    }
}

pub fn report_json(r: &Report) -> Json {
    let decls: Vec<Json> = r
        .decls
        .iter()
        .map(|d| {
            let (st, reason) = status_json(&d.status);
            let mut j = Json::obj().with("kind", d.kind.as_str()).with("name", d.name.as_str()).with("line", d.line).with("status", st);
            if let Some(m) = reason {
                j = j.with("reason", m);
            }
            if let Some(m) = &d.agda_module {
                j = j.with("agda_module", m.as_str());
            }
            if let Some(m) = &d.lh {
                j = j.with("liquidhaskell", m.as_str());
            }
            if let Some(n) = d.normal_form_rounds {
                j = j.with("normal_form_rounds", n);
            }
            if let Some(ms) = d.agda_ms {
                j = j.with("agda_ms", ms as u64);
            }
            if let (Some(l), Some(rr)) = (&d.lhs, &d.rhs) {
                j = j.with("lhs_sha256", l.hash()).with("rhs_sha256", rr.hash());
            }
            if !d.samples.is_empty() {
                let ss: Vec<Json> = d
                    .samples
                    .iter()
                    .map(|s| {
                        Json::obj()
                            .with("input", s.input.to_string())
                            .with("lean_lhs", s.lean_lhs.clone().unwrap_or_default())
                            .with("lean_rhs", s.lean_rhs.clone().unwrap_or_default())
                            .with("ir_lhs", s.ir_lhs.as_ref().map(|v| v.to_string()).unwrap_or_else(|e| e.clone()))
                            .with("ir_rhs", s.ir_rhs.as_ref().map(|v| v.to_string()).unwrap_or_else(|e| e.clone()))
                            .with("agree", s.agree)
                    })
                    .collect();
                j = j.with("samples", ss);
            }
            j
        })
        .collect();
    Json::obj()
        .with("file", r.file.display().to_string())
        .with("file_sha256", r.file_sha256.as_str())
        .with("lean", r.lean_version.as_str())
        .with("lean_exit", r.lean_exit.map(|c| c as i64).unwrap_or(-1))
        .with("lean_output_sha256", sha256::hex(r.lean_output.as_bytes()))
        .with("agda", r.agda_version.as_str())
        .with("liquidhaskell", r.lh_version.as_str())
        .with("liquidhaskell_authority", "refinement check only; not proof authority")
        .with("declarations", decls)
}

/// A surface expression that is a variable, a projection path of one, or a
/// literal: substituting it for a parameter is exactly δβ-reduction.
fn is_simple(s: &str) -> bool {
    let s = s.trim();
    if s == "u" || s == "true" || s == "false" {
        return true;
    }
    if let Some(n) = s.strip_prefix('v') {
        return !n.is_empty() && n.chars().all(|c| c.is_ascii_digit());
    }
    for (pre, lit) in [("(fst ", false), ("(snd ", false), ("(nat ", true), ("(int ", true)] {
        if let Some(rest) = s.strip_prefix(pre).and_then(|r| r.strip_suffix(')')) {
            return if lit { rest.trim_start_matches('-').chars().all(|c| c.is_ascii_digit()) && !rest.is_empty() } else { is_simple(rest) };
        }
    }
    false
}
