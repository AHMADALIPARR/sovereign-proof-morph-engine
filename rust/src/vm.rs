// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Bytecode compiler and stack VM. The VM counts executed instructions and
//! peak stack depth; those counts are the measured cost used by the energy
//! function. VM/interpreter agreement is validated by execution, not proved.

use crate::eval::{ev1, ev2, EvalError, R};
use crate::ir::*;

#[derive(Clone, Debug, PartialEq)]
pub enum Ins {
    Push(Val),
    Load(usize),  // de Bruijn index into the local frame
    Bind,         // pop value into the local frame
    Unbind(usize),
    Un(Op1),
    Bin(Op2),
    JmpF(usize),  // pop bool; jump if false
    Jmp(usize),
    MkPair,
    Fst,
    Snd,
    MkInl,
    MkInr,
    CaseJ(usize), // pop sum; push payload into frame; jump to target if Inr
    IterInit,     // pop count; push iteration record
    IterTest(usize), // if done jump to target leaving acc on stack
    IterNext,
    Call(usize),  // absolute definition index
    Ret,
}

#[derive(Clone, Debug)]
pub struct Code {
    pub funcs: Vec<Vec<Ins>>,
}

pub fn compile(p: &Prog) -> Code {
    let mut funcs = Vec::new();
    for (di, d) in p.defs.iter().enumerate() {
        let mut c = Vec::new();
        emit(p, di, &d.body, &mut c);
        c.push(Ins::Ret);
        funcs.push(c);
    }
    Code { funcs }
}

fn emit(p: &Prog, di: usize, e: &Expr, c: &mut Vec<Ins>) {
    use Expr::*;
    match e {
        Lit(v) => c.push(Ins::Push(v.clone())),
        Var(i) => c.push(Ins::Load(*i)),
        Op1(o, a) => {
            emit(p, di, a, c);
            c.push(Ins::Un(*o));
        }
        Op2(o, a, x) => {
            emit(p, di, a, c);
            emit(p, di, x, c);
            c.push(Ins::Bin(*o));
        }
        Ite(cond, x, y) => {
            emit(p, di, cond, c);
            let jf = c.len();
            c.push(Ins::JmpF(0));
            emit(p, di, x, c);
            let j = c.len();
            c.push(Ins::Jmp(0));
            let else_at = c.len();
            emit(p, di, y, c);
            let end = c.len();
            c[jf] = Ins::JmpF(else_at);
            c[j] = Ins::Jmp(end);
        }
        Let(x, body) => {
            emit(p, di, x, c);
            c.push(Ins::Bind);
            emit(p, di, body, c);
            c.push(Ins::Unbind(1));
        }
        Pair(x, y) => {
            emit(p, di, x, c);
            emit(p, di, y, c);
            c.push(Ins::MkPair);
        }
        Fst(x) => {
            emit(p, di, x, c);
            c.push(Ins::Fst);
        }
        Snd(x) => {
            emit(p, di, x, c);
            c.push(Ins::Snd);
        }
        Inl(_, x) => {
            emit(p, di, x, c);
            c.push(Ins::MkInl);
        }
        Inr(_, x) => {
            emit(p, di, x, c);
            c.push(Ins::MkInr);
        }
        Case(x, l, r) => {
            emit(p, di, x, c);
            let cj = c.len();
            c.push(Ins::CaseJ(0));
            emit(p, di, l, c);
            let j = c.len();
            c.push(Ins::Jmp(0));
            let r_at = c.len();
            emit(p, di, r, c);
            let end = c.len();
            c.push(Ins::Unbind(1));
            c[cj] = Ins::CaseJ(r_at);
            c[j] = Ins::Jmp(end);
        }
        Iter(n, z, s) => {
            emit(p, di, z, c);
            emit(p, di, n, c);
            c.push(Ins::IterInit);
            let test = c.len();
            c.push(Ins::IterTest(0));
            emit(p, di, s, c);
            c.push(Ins::IterNext);
            c.push(Ins::Jmp(test));
            let end = c.len();
            c[test] = Ins::IterTest(end);
        }
        Call(j, x) => {
            emit(p, di, x, c);
            c.push(Ins::Call(p.callee(di, *j).expect("typechecked call")));
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    pub instructions: u64,
    pub peak_stack: usize,
    pub calls: u64,
}

struct IterRec {
    i: u64,
    k: u64,
}

pub fn run(code: &Code, fi: usize, arg: Val, fuel: u64) -> (R<Val>, Stats) {
    let mut st = Stats::default();
    let r = exec(code, fi, arg, fuel, &mut st, 0);
    (r, st)
}

fn exec(code: &Code, fi: usize, arg: Val, fuel: u64, st: &mut Stats, depth: usize) -> R<Val> {
    if depth > 10_000 {
        return Err(EvalError::Stuck("call depth".into()));
    }
    let f = &code.funcs[fi];
    let mut stack: Vec<Val> = Vec::new();
    let mut frame: Vec<Val> = vec![arg];
    let mut iters: Vec<IterRec> = Vec::new();
    let mut pc = 0usize;
    let stuck = |m: &str| EvalError::Stuck(m.to_string());
    loop {
        st.instructions += 1;
        if st.instructions > fuel {
            return Err(stuck("fuel exhausted"));
        }
        st.peak_stack = st.peak_stack.max(stack.len() + frame.len());
        let ins = &f[pc];
        pc += 1;
        match ins {
            Ins::Push(v) => stack.push(v.clone()),
            Ins::Load(i) => {
                let n = frame.len();
                stack.push(frame.get(n.wrapping_sub(1 + i)).cloned().ok_or_else(|| stuck("load"))?)
            }
            Ins::Bind => frame.push(stack.pop().ok_or_else(|| stuck("bind"))?),
            Ins::Unbind(k) => {
                for _ in 0..*k {
                    frame.pop();
                }
            }
            Ins::Un(o) => {
                let v = stack.pop().ok_or_else(|| stuck("un"))?;
                stack.push(ev1(*o, &v)?);
            }
            Ins::Bin(o) => {
                let y = stack.pop().ok_or_else(|| stuck("bin"))?;
                let x = stack.pop().ok_or_else(|| stuck("bin"))?;
                stack.push(ev2(*o, &x, &y)?);
            }
            Ins::JmpF(t) => match stack.pop() {
                Some(Val::Bool(false)) => pc = *t,
                Some(Val::Bool(true)) => {}
                _ => return Err(stuck("jmpf")),
            },
            Ins::Jmp(t) => pc = *t,
            Ins::MkPair => {
                let y = stack.pop().ok_or_else(|| stuck("pair"))?;
                let x = stack.pop().ok_or_else(|| stuck("pair"))?;
                stack.push(Val::Pair(Box::new(x), Box::new(y)));
            }
            Ins::Fst => match stack.pop() {
                Some(Val::Pair(a, _)) => stack.push(*a),
                _ => return Err(stuck("fst")),
            },
            Ins::Snd => match stack.pop() {
                Some(Val::Pair(_, c)) => stack.push(*c),
                _ => return Err(stuck("snd")),
            },
            Ins::MkInl => {
                let v = stack.pop().ok_or_else(|| stuck("inl"))?;
                stack.push(Val::Inl(Box::new(v)));
            }
            Ins::MkInr => {
                let v = stack.pop().ok_or_else(|| stuck("inr"))?;
                stack.push(Val::Inr(Box::new(v)));
            }
            Ins::CaseJ(t) => match stack.pop() {
                Some(Val::Inl(a)) => frame.push(*a),
                Some(Val::Inr(c)) => {
                    frame.push(*c);
                    pc = *t;
                }
                _ => return Err(stuck("case")),
            },
            Ins::IterInit => match stack.pop() {
                Some(Val::Nat(k)) => iters.push(IterRec { i: 0, k }),
                _ => return Err(stuck("iter")),
            },
            Ins::IterTest(t) => {
                let rec = iters.last().ok_or_else(|| stuck("itertest"))?;
                if rec.i >= rec.k {
                    iters.pop();
                    pc = *t;
                } else {
                    let acc = stack.pop().ok_or_else(|| stuck("iter acc"))?;
                    frame.push(Val::Nat(rec.i));
                    frame.push(acc);
                }
            }
            Ins::IterNext => {
                frame.pop();
                frame.pop();
                iters.last_mut().ok_or_else(|| stuck("iternext"))?.i += 1;
            }
            Ins::Call(g) => {
                let a = stack.pop().ok_or_else(|| stuck("call"))?;
                st.calls += 1;
                let r = exec(code, *g, a, fuel, st, depth + 1)?;
                stack.push(r);
            }
            Ins::Ret => return stack.pop().ok_or_else(|| stuck("ret")),
        }
    }
}
