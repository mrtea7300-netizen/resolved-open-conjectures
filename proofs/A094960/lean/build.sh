#!/usr/bin/env bash
# Build the Lean formalization and print the axioms of the final theorems.
# Needs elan (https://github.com/leanprover/elan) on PATH; the toolchain is pinned in
# `lean-toolchain`, Mathlib in `lake-manifest.json`.
# On Windows: copy this folder to a Linux filesystem first (WSL: under ~, not /mnt/c).
# Mathlib is downloaded pre-built (`lake exe cache get`); it is never compiled from source.
set -euo pipefail
cd "$(dirname "$0")"
lake exe cache get
time lake build
lake env lean Axioms.lean
if grep -nE '\b(sorry|admit)\b|^\s*axiom\b' Kellner/*.lean Kellner.lean Axioms.lean; then
  echo "FOUND sorry/axiom/admit"
  exit 1
else
  echo "grep: no sorry, axiom or admit in the Lean sources"
fi
echo "uses of the native_decide tactic (expected: Kellner/FiniteNative.lean only):"
grep -nE '^\s*native_decide\s*$|by native_decide' Kellner/*.lean Kellner.lean || true
