#!/usr/bin/env python3
"""Driver for the box-tree search dfs_1094.c: split [4, NMAX] into n-ranges, run them with a
bounded number of worker processes, checkpoint each finished range to disk, merge the results.

Run inside WSL / Linux after `bash build_dfs.sh`:

    python3 run_dfs.py --nmax 10^18 --jobs 2

Resumable: a range whose file in the work directory ends with a "#DONE" line is not run again,
so the same command continues an interrupted run, and a larger --nmax reuses the ranges that
are already finished (the ranges are octaves [2^i, 2^(i+1)) cut into a fixed number of pieces).

Output:  <out>.tsv[.gz]   n, k, lpf, n_over_k for every pair with lpf(C(n,k)) > max(n/k, 13)
                          in the region 2 <= k, 2k <= n <= min(NMAX, B*k), sorted by n, k
                          (gzip files are build products: the repository does not take them)
         --plain-out      the first part of that list (n <= --plain-nmax) as plain text
         <out>.runs.tsv   one line per range: lo, hi, binary, nodes, leaves, records, seconds
"""
import argparse
import gzip
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))


def parse_int(s: str) -> int:
    s = s.replace("_", "").replace(",", "")
    if "^" in s:
        b, e = s.split("^")
        return int(b) ** int(e)
    return int(s)


def pieces_for_octave(i: int, split_from: int, pieces: int) -> int:
    return pieces if i >= split_from else 1


def make_ranges(nmax: int, split_from: int, pieces: int):
    """Octaves [2^i, 2^(i+1)-1] for i >= 2, the high ones cut into equal pieces; clipped to nmax."""
    out = []
    i = 2
    while (1 << i) <= nmax:
        lo, hi = 1 << i, (1 << (i + 1)) - 1
        m = pieces_for_octave(i, split_from, pieces)
        step = (hi - lo + 1) // m
        for j in range(m):
            a = lo + j * step
            b = hi if j == m - 1 else lo + (j + 1) * step - 1
            if a > nmax:
                break
            out.append((a, min(b, nmax), a, b))   # (run lo, run hi, full lo, full hi)
        i += 1
    return out


def is_done(path: str) -> bool:
    if not os.path.exists(path):
        return False
    with open(path, "rb") as f:
        f.seek(0, os.SEEK_END)
        size = f.tell()
        f.seek(max(0, size - 400))
        tail = f.read().decode("ascii", "replace").strip().splitlines()
    return bool(tail) and tail[-1].startswith("#DONE")


def run_range(args, lo, hi, path):
    binary = "dfs64" if hi.bit_length() <= 62 else "dfs128"
    cmd = ["nice", "-n", "10", os.path.join(HERE, "bin", binary), "search", str(lo), str(hi), str(args.B)]
    tmp = path + ".tmp"
    t0 = time.time()
    with open(tmp, "w") as f:
        subprocess.run(cmd, stdout=f, check=True)
    os.replace(tmp, path)
    return binary, time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", required=True, help="e.g. 10^18, 2^60 or a decimal integer")
    ap.add_argument("--B", type=int, default=64, help="ratio limit n <= B*k (default 64)")
    ap.add_argument("--jobs", type=int, default=2, help="worker processes (default 2)")
    ap.add_argument("--split-from", type=int, default=60, help="cut octaves 2^i with i >= this ...")
    ap.add_argument("--pieces", type=int, default=8, help="... into this many pieces")
    ap.add_argument("--workdir", default=None)
    ap.add_argument("--out", default=None, help="output prefix (default work/dfs_B<B>)")
    ap.add_argument("--gzip", action="store_true", help="write <out>.tsv.gz instead of <out>.tsv")
    ap.add_argument("--plain-nmax", default=None,
                    help="also write the rows with n <= this bound as plain text to --plain-out")
    ap.add_argument("--plain-out", default=None)
    args = ap.parse_args()
    nmax = parse_int(args.nmax)
    work = args.workdir or os.path.join(HERE, "work", f"dfs_B{args.B}")
    os.makedirs(work, exist_ok=True)
    outp = args.out or os.path.join(HERE, "work", f"dfs_B{args.B}")

    ranges = make_ranges(nmax, args.split_from, args.pieces)
    todo = []
    files = []
    for lo, hi, flo, fhi in ranges:
        # a clipped last range gets its own file name so that it is never mistaken for a full one
        path = os.path.join(work, f"part_{lo}_{hi}.txt")
        files.append((lo, hi, path))
        if not is_done(path):
            todo.append((lo, hi, path))
    print(f"nmax = {nmax} (~2^{nmax.bit_length() - 1}), B = {args.B}: {len(ranges)} ranges, "
          f"{len(ranges) - len(todo)} already done, {len(todo)} to run with {args.jobs} workers", flush=True)

    t_start = time.time()

    def work_one(job):
        lo, hi, path = job
        binary, secs = run_range(args, lo, hi, path)
        print(f"  done [{lo}, {hi}] (2^{lo.bit_length() - 1}) {binary} {secs:.1f}s "
              f"elapsed {time.time() - t_start:.0f}s", flush=True)

    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        list(ex.map(work_one, todo))

    # merge
    rows = []
    runs = []
    for lo, hi, path in files:
        if not is_done(path):
            sys.exit(f"range file not complete: {path}")
        with open(path) as f:
            for line in f:
                if line.startswith("#DONE"):
                    kv = dict(x.split("=") for x in line.split()[1:])
                    assert int(kv["nlo"]) == lo and int(kv["nhi"]) == hi and int(kv["B"]) == args.B, line
                    runs.append((lo, hi, kv["bits"], int(kv["nodes"]), int(kv["leaves"]),
                                 int(kv["records"]), float(kv["secs"])))
                elif not line.startswith("#"):
                    n, k, l = (int(x) for x in line.split())
                    assert lo <= n <= hi
                    rows.append((n, k, l))
    rows.sort()
    assert len(rows) == len(set(rows)) == sum(r[5] for r in runs)
    text = "n\tk\tlpf\tn_over_k\n" + "".join(
        f"{n}\t{k}\t{l}\t{float(Fraction(n, k)):.6f}\n" for n, k, l in rows)
    if args.gzip:
        name = outp + ".tsv.gz"
        with open(name, "wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as f:
            f.write(text.encode("ascii"))       # mtime=0: the file is reproducible byte for byte
    else:
        name = outp + ".tsv"
        with open(name, "w", newline="\n") as f:
            f.write(text)
    if args.plain_nmax:
        bound = parse_int(args.plain_nmax)
        with open(args.plain_out, "w", newline="\n") as f:
            f.write("n\tk\tlpf\tn_over_k\n")
            f.write("".join(f"{n}\t{k}\t{l}\t{float(Fraction(n, k)):.6f}\n" for n, k, l in rows if n <= bound))
    with open(outp + ".runs.tsv", "w", newline="\n") as f:
        f.write("n_lo\tn_hi\tbits\tnodes\tleaves\trecords\tcpu_seconds\n")
        for r in runs:
            f.write("\t".join(str(x) for x in r) + "\n")
    print(f"merged {len(rows)} pairs with n <= {nmax} into {name}; "
          f"total nodes {sum(r[3] for r in runs)}, total cpu {sum(r[6] for r in runs):.1f}s, "
          f"wall {time.time() - t_start:.1f}s")


if __name__ == "__main__":
    main()
