#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
#
# End-to-end run of the controller on examples/gen0.morph in a fresh work
# directory: load, N generations, ledger verification, replay with
# re-checking, Haskell reference check, Engine A and the exhaustive search.
#   scripts/demo.sh [WORKDIR] [GENERATIONS]
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
export PATH=$HOME/.elan/bin:$PATH
work=${1:-$root/build/demo}
gens=${2:-3}
spme=$root/rust/target/release/spme
rm -rf "$work"
mkdir -p "$work"
set -x
"$spme" load "$root/examples/gen0.morph" --work "$work" --seed 7386
"$spme" run --work "$work" --seed 7386 --generations "$gens"
"$spme" verify-ledger --work "$work"
"$spme" replay --work "$work" --recheck
"$spme" ref-check --work "$work"
"$spme" exhaustive "$root/examples/gen0.morph" --depth 2
"$spme" engine-a "$root/lean/EngineAArith.lean" --out "$work/engine-a"
