// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! L7 native compilation: lower a typed IR program to a standalone Rust
//! source file, compile it with `rustc -O`, and validate the executable
//! against the reference interpreter and the VM. Machine arithmetic is
//! checked: an overflow prints `TRAP`, mirroring `EvalError::Overflow`.
//! The generated binary is a runtime artifact; nothing about it is proved.

use crate::ir::*;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn rty(t: &Ty) -> String {
    match t {
        Ty::Nat => "u64".into(),
        Ty::Int => "i64".into(),
        Ty::Bool => "bool".into(),
        Ty::Prod(a, b) => format!("({}, {})", rty(a), rty(b)),
        Ty::Sum(a, b) => format!("S<{}, {}>", rty(a), rty(b)),
    }
}

fn mangle(t: &Ty) -> String {
    match t {
        Ty::Nat => "n".into(),
        Ty::Int => "z".into(),
        Ty::Bool => "b".into(),
        Ty::Prod(a, b) => format!("P{}_{}E", mangle(a), mangle(b)),
        Ty::Sum(a, b) => format!("S{}_{}E", mangle(a), mangle(b)),
    }
}

fn lit(v: &Val) -> String {
    match v {
        Val::Nat(n) => format!("{}u64", n),
        Val::Int(i) => format!("({}i64)", i),
        Val::Bool(b) => b.to_string(),
        _ => unreachable!("literals are base-typed"),
    }
}

struct Gen<'a> {
    p: &'a Prog,
    di: usize,
    fresh: usize,
}

impl<'a> Gen<'a> {
    fn name(&mut self) -> String {
        self.fresh += 1;
        format!("v{}", self.fresh)
    }
    fn e(&mut self, e: &Expr, ctx: &mut Vec<String>) -> String {
        use Expr::*;
        match e {
            Lit(v) => lit(v),
            Var(k) => ctx[ctx.len() - 1 - k].clone(),
            Op1(o, a) => {
                let x = self.e(a, ctx);
                match o {
                    crate::ir::Op1::NegZ => format!("({}).checked_neg()?", x),
                    crate::ir::Op1::NotB => format!("(!{})", x),
                    crate::ir::Op1::ToInt => format!("i64::try_from({}).ok()?", x),
                }
            }
            Op2(o, a, c) => {
                let (x, y) = (self.e(a, ctx), self.e(c, ctx));
                use crate::ir::Op2 as O;
                let body = match o {
                    O::AddN | O::AddZ => "l.checked_add(r)?",
                    O::SubN => "l.saturating_sub(r)",
                    O::SubZ => "l.checked_sub(r)?",
                    O::MulN | O::MulZ => "l.checked_mul(r)?",
                    O::LtN | O::LtZ => "(l < r)",
                    O::EqN | O::EqZ => "(l == r)",
                    O::AndB => "(l & r)",
                    O::OrB => "(l | r)",
                };
                format!("{{ let l = {}; let r = {}; {} }}", x, y, body)
            }
            Ite(c, x, y) => {
                let c = self.e(c, ctx);
                let x = self.e(x, ctx);
                let y = self.e(y, ctx);
                format!("(if {} {{ {} }} else {{ {} }})", c, x, y)
            }
            Let(x, body) => {
                let xv = self.e(x, ctx);
                let n = self.name();
                ctx.push(n.clone());
                let bv = self.e(body, ctx);
                ctx.pop();
                format!("{{ let {} = {}; {} }}", n, xv, bv)
            }
            Pair(x, y) => {
                let (a, c) = (self.e(x, ctx), self.e(y, ctx));
                format!("{{ let l = {}; let r = {}; (l, r) }}", a, c)
            }
            Fst(x) => format!("({}).0", self.e(x, ctx)),
            Snd(x) => format!("({}).1", self.e(x, ctx)),
            Inl(_, x) => format!("S::L({})", self.e(x, ctx)),
            Inr(_, x) => format!("S::R({})", self.e(x, ctx)),
            Case(x, l, r) => {
                let xv = self.e(x, ctx);
                let n = self.name();
                ctx.push(n.clone());
                let lv = self.e(l, ctx);
                let rv = self.e(r, ctx);
                ctx.pop();
                format!("(match {} {{ S::L({n}) => {{ {} }}, S::R({n}) => {{ {} }} }})", xv, lv, rv, n = n)
            }
            Iter(n, z, s) => {
                let nv = self.e(n, ctx);
                let zv = self.e(z, ctx);
                let (i, acc) = (self.name(), self.name());
                ctx.push(i.clone());
                ctx.push(acc.clone());
                let sv = self.e(s, ctx);
                ctx.pop();
                ctx.pop();
                let a = self.name();
                format!(
                    "{{ let k: u64 = {}; let mut {a} = {}; for {i} in 0..k {{ let {acc} = {a}; {a} = {}; }} {a} }}",
                    nv,
                    zv,
                    sv,
                    a = a,
                    i = i,
                    acc = acc
                )
            }
            Call(j, x) => {
                let xv = self.e(x, ctx);
                let callee = self.p.callee(self.di, *j).expect("typed program");
                format!("f{}({})?", callee, xv)
            }
        }
    }
}

fn parse_fn(t: &Ty, out: &mut Vec<String>, seen: &mut Vec<String>) -> String {
    let name = format!("parse_{}", mangle(t));
    if seen.contains(&name) {
        return name;
    }
    seen.push(name.clone());
    let body = match t {
        Ty::Nat => "expect(tk, \"(\"); expect(tk, \"nat\"); let v = tk.next().unwrap().parse().unwrap(); expect(tk, \")\"); v".to_string(),
        Ty::Int => "expect(tk, \"(\"); expect(tk, \"int\"); let v = tk.next().unwrap().parse().unwrap(); expect(tk, \")\"); v".to_string(),
        Ty::Bool => "match tk.next().unwrap().as_str() { \"true\" => true, \"false\" => false, x => panic!(\"bad bool {}\", x) }".to_string(),
        Ty::Prod(a, b) => {
            let (pa, pb) = (parse_fn(a, out, seen), parse_fn(b, out, seen));
            format!("expect(tk, \"(\"); expect(tk, \"pair\"); let a = {}(tk); let b = {}(tk); expect(tk, \")\"); (a, b)", pa, pb)
        }
        Ty::Sum(a, b) => {
            let (pa, pb) = (parse_fn(a, out, seen), parse_fn(b, out, seen));
            format!("expect(tk, \"(\"); let r = match tk.next().unwrap().as_str() {{ \"inl\" => S::L({}(tk)), \"inr\" => S::R({}(tk)), x => panic!(\"bad tag {{}}\", x) }}; expect(tk, \")\"); r", pa, pb)
        }
    };
    out.push(format!("fn {}(tk: &mut std::vec::IntoIter<String>) -> {} {{ {} }}", name, rty(t), body));
    name
}

fn show_fn(t: &Ty, out: &mut Vec<String>, seen: &mut Vec<String>) -> String {
    let name = format!("show_{}", mangle(t));
    if seen.contains(&name) {
        return name;
    }
    seen.push(name.clone());
    let body = match t {
        Ty::Nat => "format!(\"(nat {})\", v)".to_string(),
        Ty::Int => "format!(\"(int {})\", v)".to_string(),
        Ty::Bool => "v.to_string()".to_string(),
        Ty::Prod(a, b) => {
            let (sa, sb) = (show_fn(a, out, seen), show_fn(b, out, seen));
            format!("format!(\"(pair {{}} {{}})\", {}(v.0), {}(v.1))", sa, sb)
        }
        Ty::Sum(a, b) => {
            let (sa, sb) = (show_fn(a, out, seen), show_fn(b, out, seen));
            format!("match v {{ S::L(x) => format!(\"(inl {{}})\", {}(x)), S::R(x) => format!(\"(inr {{}})\", {}(x)) }}", sa, sb)
        }
    };
    out.push(format!("fn {}(v: {}) -> String {{ {} }}", name, rty(t), body));
    name
}

pub const HEADER: &str = "// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0\n// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab\n";

/// Emit the standalone program. Usage of the binary:
///   `prog`              one value per stdin line → one result line (or TRAP)
///   `prog bench N VAL`  run main N times on VAL, print elapsed nanoseconds
pub fn emit(p: &Prog) -> String {
    let mut o = String::from(HEADER);
    o.push_str(&format!("// GENERATED from IR sha256 {}\n", p.hash()));
    o.push_str("#![allow(unused_parens, unused_variables, unused_braces, non_snake_case, dead_code, unused_mut)]\n");
    o.push_str("#[derive(Clone, Copy, Debug, PartialEq)]\nenum S<A, B> { L(A), R(B) }\n");
    for (di, d) in p.defs.iter().enumerate() {
        let mut g = Gen { p, di, fresh: 0 };
        let mut ctx = vec!["v0".to_string()];
        let body = g.e(&d.body, &mut ctx);
        o.push_str(&format!("#[inline(never)]\nfn f{}(v0: {}) -> Option<{}> {{ Some({}) }}\n", di, rty(&d.arg), rty(&d.ret), body));
    }
    let mut aux = Vec::new();
    let mut seen = Vec::new();
    let m = p.main();
    let pf = parse_fn(&m.arg, &mut aux, &mut seen);
    let sf = show_fn(&m.ret, &mut aux, &mut seen);
    for a in aux {
        o.push_str(&a);
        o.push('\n');
    }
    let mi = p.defs.len() - 1;
    o.push_str(&format!(
        r#"fn expect(tk: &mut std::vec::IntoIter<String>, s: &str) {{ let t = tk.next().unwrap(); assert_eq!(t, s); }}
fn tokens(s: &str) -> std::vec::IntoIter<String> {{
    s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(String::from).collect::<Vec<_>>().into_iter()
}}
fn main() {{
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 4 && args[1] == "bench" {{
        let n: u64 = args[2].parse().unwrap();
        let x = {pf}(&mut tokens(&args[3]));
        let t0 = std::time::Instant::now();
        let mut last = None;
        for _ in 0..n {{ last = std::hint::black_box(f{mi}(std::hint::black_box(x))); }}
        let ns = t0.elapsed().as_nanos();
        println!("{{}} {{}}", ns, match last {{ Some(v) => {sf}(v), None => "TRAP".to_string() }});
        return;
    }}
    let mut s = String::new();
    std::io::Read::read_to_string(&mut std::io::stdin(), &mut s).unwrap();
    for line in s.lines().filter(|l| !l.trim().is_empty()) {{
        let x = {pf}(&mut tokens(line));
        match f{mi}(x) {{ Some(v) => println!("{{}}", {sf}(v)), None => println!("TRAP") }}
    }}
}}
"#,
        pf = pf,
        sf = sf,
        mi = mi
    ));
    o
}

pub fn rustc_version() -> Option<String> {
    let o = Command::new("rustc").arg("--version").output().ok()?;
    Some(String::from_utf8_lossy(&o.stdout).trim().to_string())
}

#[derive(Debug, Clone)]
pub struct Built {
    pub source: PathBuf,
    pub binary: PathBuf,
    pub source_sha256: String,
    pub binary_sha256: String,
}

pub fn compile(p: &Prog, dir: &Path, stem: &str) -> Result<Built, String> {
    std::fs::create_dir_all(dir).map_err(|e| e.to_string())?;
    let source = dir.join(format!("{}.rs", stem));
    let binary = dir.join(stem);
    let text = emit(p);
    std::fs::write(&source, &text).map_err(|e| e.to_string())?;
    let o = Command::new("rustc")
        .args(["-O", "--edition", "2021", "-C", "overflow-checks=on", "-o"])
        .arg(&binary)
        .arg(&source)
        .output()
        .map_err(|e| format!("rustc not runnable: {}", e))?;
    if !o.status.success() {
        return Err(format!("rustc failed: {}", String::from_utf8_lossy(&o.stderr)));
    }
    Ok(Built {
        source_sha256: crate::sha256::hex(text.as_bytes()),
        binary_sha256: crate::sha256::file_hex(&binary).map_err(|e| e.to_string())?,
        source,
        binary,
    })
}

/// Run the binary on inputs; one output line per input ("TRAP" on overflow).
pub fn run(binary: &Path, inputs: &[Val]) -> Result<Vec<String>, String> {
    let mut ch = Command::new(binary)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;
    {
        let mut si = ch.stdin.take().ok_or("stdin")?;
        for u in inputs {
            writeln!(si, "{}", u).map_err(|e| e.to_string())?;
        }
    }
    let o = ch.wait_with_output().map_err(|e| e.to_string())?;
    if !o.status.success() {
        return Err(format!("native executable failed: {}", String::from_utf8_lossy(&o.stderr)));
    }
    Ok(String::from_utf8_lossy(&o.stdout).lines().map(String::from).collect())
}

/// Wall-clock nanoseconds for `n` calls of main on `x` (measured, one run).
pub fn bench(binary: &Path, n: u64, x: &Val) -> Result<(u128, String), String> {
    let o = Command::new(binary).arg("bench").arg(n.to_string()).arg(x.to_string()).output().map_err(|e| e.to_string())?;
    if !o.status.success() {
        return Err(String::from_utf8_lossy(&o.stderr).into_owned());
    }
    let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
    let (ns, v) = s.split_once(' ').ok_or("bench output")?;
    Ok((ns.parse().map_err(|_| "bench ns")?, v.to_string()))
}

#[derive(Debug, Clone)]
pub struct Validation {
    pub inputs: usize,
    pub agree_vm: usize,
    pub agree_reference: usize,
    pub reference_trapped: usize,
    pub mismatches: Vec<String>,
}

/// Validate the native executable of `tgt` against the VM on `tgt` (same
/// machine semantics, exact agreement including traps) and against the
/// reference interpreter on `src` (on inputs where the source does not trap).
pub fn validate(binary: &Path, src: &Prog, tgt: &Prog, inputs: &[Val]) -> Result<Validation, String> {
    let outs = run(binary, inputs)?;
    if outs.len() != inputs.len() {
        return Err(format!("native produced {} lines for {} inputs", outs.len(), inputs.len()));
    }
    let code = crate::vm::compile(tgt);
    let mut v = Validation { inputs: inputs.len(), agree_vm: 0, agree_reference: 0, reference_trapped: 0, mismatches: vec![] };
    for (u, got) in inputs.iter().zip(outs.iter()) {
        let (r, _) = crate::vm::run(&code, tgt.defs.len() - 1, u.clone(), crate::anneal::FUEL);
        let vm_s = match r {
            Ok(x) => x.to_string(),
            Err(_) => "TRAP".into(),
        };
        if &vm_s == got {
            v.agree_vm += 1;
        } else {
            v.mismatches.push(format!("{}: native {} vm {}", u, got, vm_s));
        }
        match crate::eval::run_main(src, u.clone()) {
            Ok(x) => {
                if &x.to_string() == got {
                    v.agree_reference += 1;
                } else {
                    v.mismatches.push(format!("{}: native {} reference {}", u, got, x));
                }
            }
            Err(_) => v.reference_trapped += 1,
        }
    }
    Ok(v)
}
