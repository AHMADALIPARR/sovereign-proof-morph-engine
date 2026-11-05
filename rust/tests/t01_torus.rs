// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Groups 1–2: gcd / torus winding, phase wrapping and sampling collisions.
mod common;
use spme::torus;

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

#[test]
fn g01_gcd_and_minimal_winding() {
    assert_eq!(gcd(torus::MERIDIAN, torus::LONGITUDE), 1);
    // the curve (89 t, 2462 t) closes first at t = 2462: 2462 | 89 l iff 2462 | l
    let first = (1..=2 * torus::LONGITUDE).find(|l| (torus::MERIDIAN * l) % torus::LONGITUDE == 0).unwrap();
    assert_eq!(first, torus::LONGITUDE);
    for t in 0..5000u64 {
        assert!(torus::invariant(torus::MERIDIAN * t, torus::LONGITUDE * t));
    }
    assert!(!torus::invariant(90, 2462));
    assert!(!torus::invariant(89, 2461));
}

#[test]
fn g01_extracted_table_is_on_path() {
    let t = torus::Torus::load(&common::repo().join("extract/torus_path.h")).unwrap();
    assert!(!t.rows.is_empty());
    for (k, &(m, l)) in t.rows.iter().enumerate() {
        assert_eq!((m, l), (89 * k as u64, 2462 * k as u64));
    }
    assert_eq!(t.coord(t.rows.len() as u64), None);
}

#[test]
fn g01_negative_corrupted_table_rejected() {
    let src = std::fs::read_to_string(common::repo().join("extract/torus_path.h")).unwrap();
    let d = common::scratch("torus");
    // move row 1 off the path
    let bad = src.replacen("{ 89ULL, 2462ULL }", "{ 90ULL, 2462ULL }", 1);
    assert_ne!(bad, src, "fixture: row 1 literal not found");
    std::fs::write(d.join("bad.h"), &bad).unwrap();
    let e = torus::Torus::load(&d.join("bad.h")).unwrap_err();
    assert!(e.contains("off the 89/2462 path"), "{}", e);
    // drop a row: count mismatch
    let short = src.replacen("  { 89ULL, 2462ULL },\n", "", 1);
    std::fs::write(d.join("short.h"), &short).unwrap();
    assert!(torus::Torus::load(&d.join("short.h")).is_err());
}

#[test]
fn g02_phase_wraps_and_is_a_permutation() {
    let mut seen = vec![false; 2462];
    for t in 0..2462u64 {
        let p = torus::phase(t);
        assert!(p < 2462);
        assert!(!seen[p as usize], "collision inside one period at t={}", t);
        seen[p as usize] = true;
        assert_eq!(torus::phase_inv(p), t);
    }
    assert!(seen.iter().all(|x| *x));
    assert_eq!((83 * 89) % 2462, 1);
}

#[test]
fn g02_sampling_collisions_exactly_mod_2462() {
    for a in (0..20000u64).step_by(37) {
        for b in (0..20000u64).step_by(53) {
            assert_eq!(torus::phase(a) == torus::phase(b), a % 2462 == b % 2462);
        }
    }
    assert_eq!(torus::phase(u64::MAX), ((89u128 * u64::MAX as u128) % 2462) as u64);
    // 2463 samples always collide
    let ph: std::collections::HashSet<u64> = (0..2463u64).map(torus::phase).collect();
    assert_eq!(ph.len(), 2462);
}
