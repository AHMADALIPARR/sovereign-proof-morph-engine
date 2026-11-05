#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
#
# Checks every Lean file one at a time with `lake env lean` and prints the
# exact checker output and exit code per file.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
export PATH=$HOME/.elan/bin:$PATH
cd "$root/lean"
for f in ${@:-*.lean}; do
  echo "== $f"
  timeout 1200 lake env lean "$f" 2>&1
  echo "exit $?"
done
