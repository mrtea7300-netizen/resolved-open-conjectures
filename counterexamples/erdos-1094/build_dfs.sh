#!/usr/bin/env bash
# Build the box-tree search and the brute-force reference (run inside WSL / Linux).
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p bin
gcc -O3 -Wall -Wextra -o bin/dfs64 dfs_1094.c
gcc -O3 -Wall -Wextra -DWIDE -o bin/dfs128 dfs_1094.c
gcc -O3 -Wall -Wextra -o bin/brute brute_1094.c
echo "built: bin/dfs64 bin/dfs128 bin/brute"
