#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
#
# Typechecks every Agda file from scratch, one at a time, and prints the
# exact checker output, exit code and postulate count per file.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root/agda"
find . -name '*.agdai' -delete
rm -rf _build
for f in ${@:-$(ls *.agda Morph/*.agda)}; do
  echo "== $f (postulates: $(grep -c '^ *postulate' "$f"))"
  agda "$f" 2>&1 | grep -v '^ *Checking '
  echo "exit ${PIPESTATUS[0]}"
done
