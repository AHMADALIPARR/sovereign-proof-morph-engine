// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Simulated annealing over rewrite scripts. The search is untrusted: it
//! only proposes a script; the winning candidate must still pass the Agda
//! certificate and the Datalog gate before it can become executable.

use crate::energy::{self, Cost};
use crate::eval;
use crate::ir::*;
use crate::rewrite::{self, Pass, Script, Step};
use crate::vm;

/// SplitMix64 (Steele, Lea, Flood 2014).
#[derive(Clone, Debug)]
pub struct SplitMix64(pub u64);

impl SplitMix64 {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n.max(1)
    }
    pub fn unit(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }
}

/// Deterministic sample inputs of a type (used for differential testing and
/// for the execution-correspondence facts in the certificate).
pub fn samples(t: &Ty) -> Vec<Val> {
    match t {
        Ty::Nat => [0u64, 1, 2, 7, 13].iter().map(|&n| Val::Nat(n)).collect(),
        Ty::Int => [-11i64, -3, 0, 1, 7].iter().map(|&n| Val::Int(n)).collect(),
        Ty::Bool => vec![Val::Bool(false), Val::Bool(true)],
        Ty::Prod(a, c) => {
            let (xs, ys) = (samples(a), samples(c));
            let mut out = Vec::new();
            for (k, x) in xs.iter().enumerate() {
                out.push(Val::Pair(Box::new(x.clone()), Box::new(ys[k % ys.len()].clone())));
                out.push(Val::Pair(Box::new(x.clone()), Box::new(ys[(k + 1) % ys.len()].clone())));
            }
            out.truncate(6);
            out
        }
        Ty::Sum(a, c) => {
            let mut out: Vec<Val> = samples(a).into_iter().take(3).map(|v| Val::Inl(Box::new(v))).collect();
            out.extend(samples(c).into_iter().take(3).map(|v| Val::Inr(Box::new(v))));
            out
        }
    }
}

#[derive(Clone, Debug)]
pub struct Candidate {
    pub script: Script,
    pub tgt: Prog,
    pub cost: Cost,
    pub energy: f64,
    /// (input, output) pairs produced by the VM on the target.
    pub io: Vec<(Val, Val)>,
}

pub const FUEL: u64 = 1 << 22;

/// Evaluate a script: rewrite, typecheck, differential-test the VM on the
/// target against the reference interpreter on the source, and measure.
pub fn evaluate(src: &Prog, script: &Script) -> Result<Candidate, String> {
    let tgt = rewrite::apply_script(src, script)?;
    let code = vm::compile(&tgt);
    let mut io = Vec::new();
    let (mut instr, mut peak) = (0u64, 0u64);
    let ins = samples(&src.main().arg);
    for u in &ins {
        let reference = eval::run_main(src, u.clone());
        let (r, st) = vm::run(&code, tgt.defs.len() - 1, u.clone(), FUEL);
        match (reference, r) {
            (Ok(a), Ok(c)) if a == c => io.push((u.clone(), c)),
            (Err(_), _) => continue, // source traps (machine overflow); no claim on this input
            (Ok(a), Ok(c)) => return Err(format!("differential mismatch on {}: src {} tgt {}", u, a, c)),
            (Ok(_), Err(e)) => return Err(format!("target trapped on {}: {:?}", u, e)),
        }
        instr += st.instructions;
        peak = peak.max(st.peak_stack as u64);
    }
    if io.is_empty() {
        return Err("no sample input executes without trapping".into());
    }
    let cost = Cost { instructions: instr / io.len() as u64, peak_stack: peak, size: tgt.size() as u64 };
    Ok(Candidate { energy: energy::scalar(&cost), script: script.clone(), tgt, cost, io })
}

fn spec_sites(p: &Prog) -> Vec<(usize, Val)> {
    fn walk(e: &Expr, out: &mut Vec<(usize, Val)>) {
        use Expr::*;
        match e {
            Call(j, x) => {
                if let Pair(_, c) = &**x {
                    if let Lit(v) = &**c {
                        out.push((*j, v.clone()));
                    }
                }
                walk(x, out)
            }
            Lit(_) | Var(_) => {}
            Op1(_, a) | Fst(a) | Snd(a) | Inl(_, a) | Inr(_, a) => walk(a, out),
            Op2(_, a, c) | Let(a, c) | Pair(a, c) => {
                walk(a, out);
                walk(c, out)
            }
            Ite(a, c, d) | Case(a, c, d) | Iter(a, c, d) => {
                walk(a, out);
                walk(c, out);
                walk(d, out)
            }
        }
    }
    let mut out = Vec::new();
    walk(&p.main().body, &mut out);
    out.dedup();
    out
}

fn random_passes(rng: &mut SplitMix64) -> Vec<Pass> {
    let n = 1 + rng.below(4) as usize;
    (0..n)
        .map(|_| match rng.below(5) {
            0 => Pass::Cf,
            1 => Pass::Alg,
            2 => Pass::Dce,
            3 => Pass::Fuse,
            _ => Pass::Pe(1 + rng.below(4)),
        })
        .collect()
}

/// Where proposals come from. `Torus` walks the verified 89/2462 path: at
/// iteration i the coordinate is t = t0 + i and the proposal is derived from
/// its normalized phase 89·t mod 2462 (a permutation of 0..2462 over any
/// 2462 consecutive steps). `Random` uses the PRNG alone. Both are seeded and
/// deterministic, so a run is replayable from its parameters.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Proposal {
    Random,
    Torus { t0: u64 },
}

#[derive(Clone, Debug)]
pub struct Params {
    pub seed: u64,
    pub iterations: u32,
    pub t0: f64,
    pub cooling: f64,
    pub t_min: f64,
    pub patience: u32,
    pub max_steps: usize,
    pub proposal: Proposal,
}

impl Default for Params {
    fn default() -> Self {
        Params {
            seed: 0x5EED_0089_2462,
            iterations: 400,
            t0: 2.0,
            cooling: 0.985,
            t_min: 1e-3,
            patience: 250,
            max_steps: 6,
            proposal: Proposal::Torus { t0: 1 },
        }
    }
}

#[derive(Clone, Debug)]
pub struct Event {
    pub iter: u32,
    pub t: u64,
    pub temperature: f64,
    pub energy: Option<f64>,
    pub accepted: bool,
    pub note: String,
}

#[derive(Clone, Debug, Default)]
pub struct Trace {
    pub proposed: u32,
    pub valid: u32,
    pub accepted: u32,
    pub uphill_accepted: u32,
    pub improved: u32,
    pub initial_energy: f64,
    pub best_energy: f64,
    pub best_t: u64,
    pub final_temperature: f64,
    pub stop: String,
    pub history: Vec<Event>,
    /// Distinct valid targets seen: (target sha256, script, energy, cost).
    pub distinct: Vec<(String, String, f64, Cost)>,
}

impl Trace {
    /// Distinct candidates ranked by energy (best first).
    pub fn ranking(&self, k: usize) -> Vec<(String, String, f64, Cost)> {
        let mut v = self.distinct.clone();
        v.sort_by(|a, b| energy::energy(&a.3).cmp(&energy::energy(&b.3)).then(a.1.len().cmp(&b.1.len())));
        v.truncate(k);
        v
    }
}

/// Boltzmann acceptance: downhill always, uphill with probability e^{-Δ/T}.
/// Numerically: Δ/T is clamped so exp never overflows, and T ≤ 0 means
/// greedy (uphill never accepted).
pub fn accept(delta: f64, temp: f64, u: f64) -> bool {
    if delta <= 0.0 {
        return true;
    }
    if !(temp > 0.0) || !delta.is_finite() {
        return false;
    }
    let x = (delta / temp).min(700.0);
    u < (-x).exp()
}

fn propose(cur: &Candidate, sel: u64, rng: &mut SplitMix64, max_steps: usize) -> Script {
    let mut s = cur.script.clone();
    match sel % 4 {
        0 | 1 if s.len() < max_steps => s.push(Step::Passes(random_passes(rng))),
        2 if !s.is_empty() => {
            let k = rng.below(s.len() as u64) as usize;
            if let Step::Passes(_) = s[k] {
                s[k] = Step::Passes(random_passes(rng));
            } else {
                s.remove(k);
            }
        }
        3 if s.len() < max_steps => {
            let sites = spec_sites(&cur.tgt);
            if sites.is_empty() {
                s.push(Step::Passes(random_passes(rng)));
            } else {
                let (j, v) = sites[rng.below(sites.len() as u64) as usize].clone();
                s.push(Step::Spec { j, v });
            }
        }
        _ => {
            s.pop();
        }
    }
    s
}

fn better(a: &Candidate, b: &Candidate) -> bool {
    let (ea, eb) = (energy::energy(&a.cost), energy::energy(&b.cost));
    ea < eb || (ea == eb && a.script.len() < b.script.len())
}

/// Stochastic annealing from the empty script.
pub fn anneal(src: &Prog, prm: &Params) -> Result<(Candidate, Trace), String> {
    let mut rng = SplitMix64(prm.seed);
    let mut cur = evaluate(src, &Vec::new())?;
    let mut best = cur.clone();
    let mut tr = Trace { initial_energy: cur.energy, best_energy: cur.energy, ..Default::default() };
    tr.distinct.push((cur.tgt.hash(), String::new(), cur.energy, cur.cost.clone()));
    let start_t = match prm.proposal {
        Proposal::Torus { t0 } => t0,
        Proposal::Random => 0,
    };
    tr.best_t = start_t;
    let mut temp = prm.t0;
    let mut stall = 0u32;
    tr.stop = "iteration budget".into();
    for i in 0..prm.iterations {
        if temp < prm.t_min {
            tr.stop = "temperature below t_min".into();
            break;
        }
        if stall >= prm.patience {
            tr.stop = "no improvement within patience".into();
            break;
        }
        let t = start_t + i as u64 + 1;
        let sel = match prm.proposal {
            Proposal::Torus { .. } => {
                let ph = crate::torus::phase(t);
                rng = SplitMix64(prm.seed ^ ph.wrapping_mul(0x9E37_79B9));
                ph
            }
            Proposal::Random => rng.next_u64(),
        };
        let s = propose(&cur, sel, &mut rng, prm.max_steps);
        tr.proposed += 1;
        let mut ev = Event { iter: i, t, temperature: temp, energy: None, accepted: false, note: String::new() };
        match evaluate(src, &s) {
            Err(e) => {
                ev.note = format!("rejected: {}", e);
                stall += 1;
            }
            Ok(cand) => {
                tr.valid += 1;
                let h = cand.tgt.hash();
                match tr.distinct.iter_mut().find(|d| d.0 == h) {
                    Some(d) => {
                        if cand.script.len() < d.1.split(';').count() {
                            d.1 = rewrite::script_text(&cand.script);
                        }
                    }
                    None => tr.distinct.push((h, rewrite::script_text(&cand.script), cand.energy, cand.cost.clone())),
                }
                let d = cand.energy - cur.energy;
                ev.energy = Some(cand.energy);
                if accept(d, temp, rng.unit()) {
                    tr.accepted += 1;
                    if d > 0.0 {
                        tr.uphill_accepted += 1;
                    }
                    ev.accepted = true;
                    cur = cand;
                    if better(&cur, &best) {
                        tr.improved += 1;
                        best = cur.clone();
                        tr.best_t = t;
                        stall = 0;
                    } else {
                        stall += 1;
                    }
                } else {
                    stall += 1;
                    ev.note = "boltzmann reject".into();
                }
            }
        }
        tr.history.push(ev);
        temp *= prm.cooling;
    }
    tr.final_temperature = temp;
    tr.best_energy = best.energy;
    Ok((best, tr))
}

/// Exhaustive deterministic traversal of all scripts of up to `depth`
/// steps over a fixed alphabet (for small finite spaces).
pub fn exhaustive(src: &Prog, alphabet: &[Step], depth: usize) -> Result<(Candidate, u64), String> {
    let mut best = evaluate(src, &Vec::new())?;
    let mut visited = 1u64;
    let mut frontier: Vec<Script> = vec![Vec::new()];
    for _ in 0..depth {
        let mut next = Vec::new();
        for s in &frontier {
            for a in alphabet {
                let mut s2 = s.clone();
                s2.push(a.clone());
                visited += 1;
                if let Ok(c) = evaluate(src, &s2) {
                    if better(&c, &best) {
                        best = c;
                    }
                    next.push(s2);
                }
            }
        }
        frontier = next;
    }
    Ok((best, visited))
}
