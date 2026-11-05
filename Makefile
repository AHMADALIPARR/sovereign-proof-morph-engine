# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
#
# Top-level build. Tool locations can be overridden on the command line,
# e.g. `make bqn BQN=/opt/cbqn/BQN`.

SHELL      := /bin/bash
ELAN_BIN   ?= $(HOME)/.elan/bin
export PATH := $(ELAN_BIN):$(PATH)
BQN        ?= /workspace/_tools_cbqn/CBQN/BQN
BQN_AVX512 ?= /workspace/_tools_cbqn/CBQN-avx512/BQN
LH_GHC     ?= $(HOME)/.ghcup/bin/ghc-9.6.3
LH_PKGDB   ?= $(HOME)/.local/state/cabal/store/ghc-9.6.3/package.db
Z3_DIR     ?= /workspace/z3bin
NBVENV     ?= /workspace/_nbtools
GENS       ?= 3
BQN_DATA   := $(CURDIR)/build/bqn/data

.PHONY: all build ref test lean agda agda-engine lh datalog bqn bqn-avx512 \
        torus demo figures notebook clean

all: build ref

build:
	cd rust && cargo build --release

ref: haskell/build/ref

haskell/build/ref: haskell/Ref.hs
	mkdir -p haskell/build/ref-obj
	ghc -O -outputdir haskell/build/ref-obj -o $@ $<

test: build ref
	cd rust && cargo test --release -- --test-threads=1

lean:
	scripts/check_lean.sh

agda:
	scripts/check_agda.sh

agda-engine:
	$(MAKE) -C agda -f Makefile.checked

lh:
	@for f in haskell/Contracts.hs haskell/negative/ContractsWrong.hs; do \
	  echo "== $$f"; mkdir -p build/lh; \
	  PATH=$(Z3_DIR):$$PATH $(LH_GHC) -package-db $(LH_PKGDB) -package liquidhaskell \
	    -fplugin=LiquidHaskell -fforce-recomp -c -outputdir build/lh $$f; \
	  echo "exit $$?"; done

datalog:
	cd rust && cargo test --release --test t10_gate -- --test-threads=1

torus: extract/torus_path.h

extract/torus_path.h: agda/ExtractTorusPath.agda extract/gen_torus_path.sh
	extract/gen_torus_path.sh

bqn:
	mkdir -p $(BQN_DATA)
	$(BQN) bqn/checked/gen_inputs.bqn $(BQN_DATA) 7386 512 64
	@for p in omega_tensor phi_replay twin_xgraph init_teleo; do \
	  echo "== $$p"; $(BQN) bqn/checked/$${p}_checked.bqn $(BQN_DATA); done

bqn-avx512:
	BQN_BASE=$(BQN) BQN_AVX512=$(BQN_AVX512) scripts/bqn_avx512.sh build/bqn 3

demo: build ref
	scripts/demo.sh build/demo $(GENS)

figures:
	BQN=$(BQN) scripts/figures.sh

notebook: build ref
	$(NBVENV)/bin/jupyter nbconvert --to notebook --execute --inplace \
	  --ExecutePreprocessor.timeout=3600 --ExecutePreprocessor.kernel_name=bash \
	  notebooks/end_to_end.ipynb

clean:
	rm -rf build haskell/build
	cd rust && cargo clean
