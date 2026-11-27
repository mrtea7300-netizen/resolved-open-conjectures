#!/bin/bash
# Build and run the finite check of proof.md, Proposition 9 (about 25 s on two cores).
# Needs gcc (we used gcc 13.3.0 under WSL2).  Run from this folder:  bash run_finite_check.sh
set -e
mkdir -p work data
gcc -O2 -Wall -o work/finite_check finite_check.c
./work/finite_check 1 2000001 > data/finite_check_1_2000001.txt
./work/finite_check 1 1800000000 > data/finite_check_1_1800000000.txt &
./work/finite_check 1800000000 3622113856 > data/finite_check_1800000000_3622113856.txt &
wait
grep -h -E 'summary|UNRESOLVED' data/finite_check_1_1800000000.txt data/finite_check_1800000000_3622113856.txt
