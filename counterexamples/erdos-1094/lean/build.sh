#!/usr/bin/env bash
# Build the Lean formalization and print the axioms of the final theorems.
# Needs elan (https://github.com/leanprover/elan) on PATH; the toolchain is pinned in
# `lean-toolchain`, Mathlib in `lake-manifest.json`.
# On Windows: copy this folder to a Linux filesystem first (WSL: under ~, not /mnt/c).
# Mathlib is downloaded pre-built (`lake exe cache get`); it is never compiled from source.
set -euo pipefail
cd "$(dirname "$0")"
if [ ! -d ".lake/packages/mathlib" ]; then
  lake exe cache get
fi
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
time lake build
lake env lean Axioms.lean
if grep -nE '\b(sorry|admit)\b|^\s*axiom\b' Erdos1094/*.lean Erdos1094.lean Axioms.lean; then
  echo "FOUND sorry/axiom/admit"
  exit 1
else
  echo "grep: no sorry, axiom or admit in the Lean sources"
fi
if grep -nE '\bnative_decide\b' Erdos1094/*.lean Erdos1094.lean Axioms.lean; then
  echo "FOUND native_decide"
  exit 1
else
  echo "grep: no native_decide in the Lean sources"
fi
