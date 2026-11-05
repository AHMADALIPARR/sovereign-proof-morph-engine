#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
#
# Writes notebooks/end_to_end.ipynb (bash kernel) with jq; `make notebook`
# then executes it in place with nbconvert.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=$root/notebooks/end_to_end.ipynb
cells=()
md()   { cells+=("$(jq -n --arg s "$1" '{cell_type:"markdown",metadata:{},source:$s}')"); }
code() { cells+=("$(jq -n --arg s "$1" '{cell_type:"code",metadata:{},execution_count:null,outputs:[],source:$s}')"); }

md '# Sovereign Proof Morph Engine: end to end

SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab

Every cell runs a real tool on this machine: Agda, Lean, Soufflé, CBQN, GHC, rustc and the engine controller.'

code 'cd "$(git rev-parse --show-toplevel 2>/dev/null || echo ..)"
export PATH=$HOME/.elan/bin:$PATH
export SPME=$PWD/rust/target/release/spme
pwd; git log --oneline -1
agda --version | head -1; lean --version; souffle --version | grep Version; rustc --version; ghc --version'

md '## L0–L1: build the engine and the Haskell reference model'
code 'make build ref 2>&1 | tail -3'

md '## Torus invariant: Agda knot → MAlonzo → `extract/torus_path.h`'
code 'sed -n "1,12p" extract/torus_path.h | cut -c1-120
$SPME torus'

md '## Agda: `--safe`, zero postulates'
code 'scripts/check_agda.sh TorusInvariant.agda PhiHarmonics.agda CompleteCoherence_Checked.agda'

md '## Lean 4 + Mathlib: X-graph model and `#print axioms`'
code 'scripts/check_lean.sh XGraph.lean PhaseNormalization.lean'

md '## BQN (CBQN interpreter, executable model): twin X-graph and antipodal init'
code 'D=$PWD/build/bqn/data; mkdir -p $D
B=/workspace/_tools_cbqn/CBQN/BQN
$B bqn/checked/gen_inputs.bqn $D 7386 512 64
$B bqn/checked/twin_xgraph_checked.bqn $D
$B bqn/checked/init_teleo_checked.bqn $D'

md '## AVX-512 build check (zmm count of both interpreters)'
code 'for b in /workspace/_tools_cbqn/CBQN/BQN /workspace/_tools_cbqn/CBQN-avx512/BQN; do echo "$b zmm=$(objdump -d $b | grep -c zmm)"; done
cat docs/measurements/cbqn-zmm.txt'

md '## snap-omega-engine (Agda → MAlonzo → GHC native)'
code 'make -s -C agda -f Makefile.checked >/dev/null && ./agda/snap-omega-engine'

md '## Soufflé gate: only COMMIT advances, everything else is SILENCE'
code '(cd rust && cargo test --release --test t10_gate -- --test-threads=1 2>&1 | grep -E "^test |test result")'

md '## Controller: load, generations, ledger, replay with re-checking, reference model'
code 'W=$PWD/build/nb-demo; rm -rf $W
$SPME load examples/gen0.morph --work $W --seed 7386
$SPME run --work $W --seed 7386 --generations 2 | grep -vE "^  [0-9]\."
$SPME verify-ledger --work $W
$SPME replay --work $W --recheck
$SPME ref-check --work $W'

md '## Figures (regenerated from the runs above)'
code 'scripts/figures.sh | tail -8'

md '## Full test suite (last recorded run)'
code 'grep -E "Running tests|test result" docs/measurements/tests.txt | grep -v " 0 passed"'

printf '%s\n' "${cells[@]}" | jq -s '{
  cells: .,
  metadata: {
    kernelspec: {display_name: "Bash", language: "bash", name: "bash"},
    language_info: {name: "bash", codemirror_mode: "shell", file_extension: ".sh", mimetype: "text/x-sh"}
  },
  nbformat: 4, nbformat_minor: 5
} | .cells |= [ to_entries[] | .value + {id: ("c" + (.key|tostring))} ]' > "$out"
echo "wrote $out"
