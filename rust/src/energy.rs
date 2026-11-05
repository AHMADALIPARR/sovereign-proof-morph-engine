// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Energy of a candidate. Each measured cost term is compressed with the
//! ALSC function of lean/XREX_ALSC_Checked.lean (64-bit wrapping arithmetic,
//! cap 4, hardware log = floor log2, bounded by 64), whose output is proved
//! there to stay ≤ 65504 for every input.

pub const ALSC_CAP: u64 = 4;
pub const FP16_MAX: u64 = 65504;

pub fn hw_log(v: u64) -> u64 {
    if v == 0 {
        0
    } else {
        63 - v.leading_zeros() as u64
    }
}

pub fn alsc_payload(x: u64) -> u64 {
    if x <= ALSC_CAP {
        x
    } else {
        ALSC_CAP.wrapping_add(hw_log(1u64.wrapping_add(x).wrapping_sub(ALSC_CAP)))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Cost {
    pub instructions: u64,
    pub peak_stack: u64,
    pub size: u64,
}

/// Lexicographic key used for annealing: the ALSC-compressed sum first,
/// then raw instruction count and size as tie-breakers.
pub fn energy(c: &Cost) -> (u64, u64, u64) {
    (
        alsc_payload(c.instructions) + alsc_payload(c.peak_stack) + alsc_payload(c.size),
        c.instructions,
        c.size,
    )
}

/// Scalar energy for the Boltzmann criterion.
pub fn scalar(c: &Cost) -> f64 {
    let (a, i, s) = energy(c);
    a as f64 + (i as f64).ln_1p() * 0.5 + (s as f64).ln_1p() * 0.25
}
