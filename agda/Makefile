# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
# ==============================================================================
# SNAP-OS: Agda Phenomenal Substrate Makefile
# ==============================================================================

AGDA       = agda
AGDA_FLAGS = --compile --compile-dir=MAlonzoBuild
GHC        = ghc
BINARY     = snap-omega-engine
SRC        = Main.agda

.PHONY: all clean run check

all: $(BINARY)

# 1. Typecheck and compile Agda via MAlonzo to Haskell, then native binary via GHC
$(BINARY): $(SRC)
	@echo "[+] Compiling Agda phenomenal substrate through MAlonzo..."
	$(AGDA) $(AGDA_FLAGS) $(SRC)
	@echo "[+] Linking native binary with GHC optimization..."
	$(GHC) -O2 MAlonzoBuild/Main.hs -o $(BINARY)
	@echo "[✓] Build complete: ./$(BINARY)"

# 2. Run static type verification without emitting binaries
check:
	@echo "[+] Running static type checks on Agda source tree..."
	$(AGDA) $(SRC)

# 3. Execute the native binary
run: $(BINARY)
	@echo "[*] Launching SNAP-OS phenomenal runtime..."
	./$(BINARY)

# 4. Purge intermediate compilation artifacts and binary
clean:
	@echo "[-] Purging MAlonzo build artifacts and binary..."
	rm -rf MAlonzoBuild $(BINARY) *.hi *.o
