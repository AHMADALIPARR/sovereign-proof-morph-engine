// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Groups 3–4: deterministic replay, annealing acceptance and temperature.
mod common;
use spme::anneal::{self, Params, Proposal, SplitMix64};

#[test]
fn g03_prng_and_anneal_replay_deterministic() {
    let mut a = SplitMix64(42);
    let mut b = SplitMix64(42);
    for _ in 0..1000 {
        assert_eq!(a.next_u64(), b.next_u64());
    }
    let p = common::gen0();
    let prm = Params { iterations: 120, ..Params::default() };
    let (c1, t1) = anneal::anneal(&p, &prm).unwrap();
    let (c2, t2) = anneal::anneal(&p, &prm).unwrap();
    assert_eq!(c1.tgt.hash(), c2.tgt.hash());
    assert_eq!(c1.script, c2.script);
    assert_eq!((t1.proposed, t1.valid, t1.accepted, t1.best_t), (t2.proposed, t2.valid, t2.accepted, t2.best_t));
    assert_eq!(t1.best_energy.to_bits(), t2.best_energy.to_bits());
    // a different seed is a different run (not necessarily a different optimum)
    let (_, t3) = anneal::anneal(&p, &Params { seed: 7, iterations: 120, proposal: Proposal::Random, ..Params::default() }).unwrap();
    assert!(t3.proposed > 0);
}

#[test]
fn g04_acceptance_rule() {
    // downhill and flat always accepted, at any temperature and any u
    for &t in &[0.0, 1e-9, 1.0, 1e9] {
        for &u in &[0.0, 0.5, 0.999999] {
            assert!(anneal::accept(-1.0, t, u));
            assert!(anneal::accept(0.0, t, u));
        }
    }
    // T <= 0 is greedy; NaN/inf delta rejected
    assert!(!anneal::accept(1e-12, 0.0, 0.0));
    assert!(!anneal::accept(1.0, -1.0, 0.0));
    assert!(!anneal::accept(f64::INFINITY, 1.0, 0.0));
    assert!(!anneal::accept(f64::NAN, 1.0, 0.0));
    // Boltzmann threshold e^{-Δ/T}
    let th = (-1.0f64 / 2.0).exp();
    assert!(anneal::accept(1.0, 2.0, th - 1e-12));
    assert!(!anneal::accept(1.0, 2.0, th + 1e-12));
    // no overflow for huge Δ/T
    assert!(!anneal::accept(1e300, 1e-300, 1e-200));
    assert!((-700.0f64).exp() > 0.0);
}

#[test]
fn g04_acceptance_rate_monotone_in_temperature() {
    let rate = |t: f64| {
        let mut r = SplitMix64(9);
        (0..20000).filter(|_| anneal::accept(1.0, t, r.unit())).count()
    };
    let (a, b, c) = (rate(0.25), rate(1.0), rate(4.0));
    assert!(a < b && b < c, "{} {} {}", a, b, c);
    // e^{-1} ≈ 0.3679 at T = 1
    assert!((b as f64 / 20000.0 - (-1.0f64).exp()).abs() < 0.02);
}

#[test]
fn g04_temperature_schedule_cools() {
    let p = common::gen0();
    let prm = Params { iterations: 200, patience: 10_000, ..Params::default() };
    let (best, tr) = anneal::anneal(&p, &prm).unwrap();
    assert!(tr.final_temperature < prm.t0);
    assert!(tr.final_temperature >= prm.t_min * prm.cooling);
    let temps: Vec<f64> = tr.history.iter().map(|e| e.temperature).collect();
    assert!(temps.windows(2).all(|w| w[1] <= w[0]), "temperature must not increase");
    assert!(tr.best_energy <= tr.initial_energy);
    assert_eq!(best.energy.to_bits(), tr.best_energy.to_bits());
}
