#!/bin/sh
# Build the split-prime sieve (Linux / WSL). Usage: sh build.sh
set -e
cd "$(dirname "$0")"
mkdir -p bin
gcc -O3 -march=native -o bin/split_sieve split_sieve.c -lm
