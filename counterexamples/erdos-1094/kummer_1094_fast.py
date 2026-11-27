"""Fast LLVM-compiled (Numba @njit) Kummer-theorem & Kummer-CRT engines for
Erdős Problem #1094 (Erdős-Lacampagne-Selfridge 1988, 1993; Selfridge 1977; Guy B31/B33).

Two complementary exact engines (both using <= 2 CPU threads):

1. `--scan-n N_max`:
   Enumerates ALL pairs (n, k) with 2 <= k <= n/2 and n <= N_max where 2 nmid C(n, k)
   using the exact binary submask bijection:
     2 nmid C(n, k) and k <= n/2  <==>  k is a binary submask of (n ^ highest_bit(n)).
   This cuts O(N^2) to O(N^{log_2(3)}) = O(N^{1.585}), plus O(1) unrolled base-3
   rejection (cuts another ~56% before any loop).
   Records every pair violating any of:
     (A) lpf(C(n, k)) <= max(n/k, k)   [ELS88 14-exception conjecture, Erdős #1094]
     (B) lpf(C(n, k)) <= max(n/k, 13)  [ELS93 stronger 12-exception remark]
     (C) n >= k^2 - 1 => lpf <= n/k    [Selfridge 1977 conjecture]
     (D) n > 17.125*k => lpf <= n/k    [Guy B31/B33 Selfridge conjecture]
     (E) lpf(C(n, k)) <= max(n/k, 17)  [threshold-17 check]
     (F) lpf(C(n, k)) <= max(n/k, 29)  [ELS93 main conjecture: lpf <= max(n/k, 29)]

2. `--regime1 K_max`:
   Exhaustively verifies Regime 1 (2k <= n <= k^2) for lpf(C(n, k)) <= k (i.e., g(k) > k^2)
   for ALL 2 <= k <= K_max (covering n <= K_max^2) using the exact Kummer-CRT reduction
   on consecutive composite moduli among {k+1, k+2, k+3, k+4}:
     - If p^a || (k + c) with p <= k, then p nmid C(n, k) forces n mod p^a to be
       base-p digitwise >= (k mod p^a), which restricts n mod p^a to a subset of
       [max(0, p^a - c), p^a - 1].
     - Intersecting two coprime composite moduli gives M > k^2 (or M >= k^2/4 for twin
       primes), reducing the k^2 candidates per k to O(log^c k) exact CRT candidates!
"""
import argparse
import os
import time
import numpy as np
from numba import njit, prange, set_num_threads


def build_spf_and_primes(limit: int):
    spf = np.zeros(limit + 1, dtype=np.int32)
    for i in range(2, int(limit ** 0.5) + 1):
        if spf[i] == 0:
            spf[i] = i
            spf[i * i : limit + 1 : i] = np.where(
                spf[i * i : limit + 1 : i] == 0, i, spf[i * i : limit + 1 : i]
            )
    for i in range(2, limit + 1):
        if spf[i] == 0:
            spf[i] = i
    primes = np.nonzero(spf == np.arange(limit + 1, dtype=np.int32))[0].astype(np.int32)
    primes = primes[primes >= 2]
    return spf, primes


@njit(inline="always")
def p_divides64(n: np.uint64, k: np.uint64, p: np.uint64) -> bool:
    nn = n
    kk = k
    while kk > 0:
        if (nn % p) < (kk % p):
            return True
        nn //= p
        kk //= p
    return False


@njit(inline="always")
def p_divides32(n: np.uint32, k: np.uint32, p: np.uint32) -> bool:
    nn = n
    kk = k
    while kk > 0:
        if (nn % p) < (kk % p):
            return True
        nn //= p
        kk //= p
    return False


@njit
def exact_lpf32(n: np.uint32, k: np.uint32, primes: np.ndarray) -> np.uint32:
    for i in range(primes.shape[0]):
        p = np.uint32(primes[i])
        if p > n:
            break
        if p_divides32(n, k, p):
            return p
    return n + np.uint32(1)


@njit
def scan_n_chunk(n_start: int, n_end: int, primes: np.ndarray):
    """Scan all n in [n_start, n_end] via binary submasks of (n ^ hi_bit(n)).
    Returns (submasks_checked, out_n, out_k, out_lpf, out_flags).
    Flag bits: 1=A(>max(n/k,k)), 2=B(>max(n/k,13)), 4=C(Selfridge k^2-1),
               8=D(>17.125k), 16=E(>max(n/k,17)), 32=F(>max(n/k,29)).
    """
    max_out = 4096
    out_n = np.empty(max_out, dtype=np.int64)
    out_k = np.empty(max_out, dtype=np.int64)
    out_lpf = np.empty(max_out, dtype=np.int64)
    out_flags = np.empty(max_out, dtype=np.int32)
    nout = 0
    submasks = np.int64(0)

    nprimes = primes.shape[0]
    hi = np.uint32(1)
    while (hi << np.uint32(1)) <= np.uint32(n_start):
        hi <<= np.uint32(1)

    for n_i in range(n_start, n_end + 1):
        n = np.uint32(n_i)
        if (hi << np.uint32(1)) <= n:
            hi <<= np.uint32(1)
        rem = n ^ hi
        if rem < np.uint32(2):
            continue

        # Precompute bottom 2 base-3 digits of n for O(1) rejection
        n_q3 = n // np.uint32(3)
        n_d0 = n - np.uint32(3) * n_q3
        n_q9 = n_q3 // np.uint32(3)
        n_d1 = n_q3 - np.uint32(3) * n_q9

        k = rem
        while k >= np.uint32(2):
            submasks += 1
            # Fast base-3 bottom-2-digit filter (kills 5/9 immediately)
            k_q3 = k // np.uint32(3)
            if (k - np.uint32(3) * k_q3) <= n_d0:
                k_q9 = k_q3 // np.uint32(3)
                if (k_q3 - np.uint32(3) * k_q9) <= n_d1:
                    # Finish base-3 check
                    if not p_divides32(n_q9, k_q9, np.uint32(3)):
                        q = n // k
                        lim_A = q if q > k else k
                        lim_B = q if q > np.uint32(13) else np.uint32(13)
                        need_C = (np.uint64(n) + np.uint64(1)) >= (np.uint64(k) * np.uint64(k))
                        need_D = (np.uint64(8) * np.uint64(n)) > (np.uint64(137) * np.uint64(k))

                        min_lim = lim_A if lim_A < lim_B else lim_B
                        if need_C and q < min_lim:
                            min_lim = q
                        if need_D and q < min_lim:
                            min_lim = q

                        # Check primes 5, 7, 11, 13
                        ok = True
                        if np.uint32(5) <= min_lim and p_divides32(n, k, np.uint32(5)):
                            ok = False
                        elif np.uint32(7) <= min_lim and p_divides32(n, k, np.uint32(7)):
                            ok = False
                        elif np.uint32(11) <= min_lim and p_divides32(n, k, np.uint32(11)):
                            ok = False
                        elif np.uint32(13) <= min_lim and p_divides32(n, k, np.uint32(13)):
                            ok = False

                        if ok:
                            for pi in range(6, nprimes):
                                p = np.uint32(primes[pi])
                                if p > min_lim:
                                    break
                                if p_divides32(n, k, p):
                                    ok = False
                                    break

                        if ok:
                            lpf = exact_lpf32(n, k, primes)
                            flags = np.int32(0)
                            if lpf > lim_A:
                                flags |= np.int32(1)
                            if lpf > lim_B:
                                flags |= np.int32(2)
                            if need_C and lpf > q:
                                flags |= np.int32(4)
                            if need_D and lpf > q:
                                flags |= np.int32(8)
                            lim_E = q if q > np.uint32(17) else np.uint32(17)
                            if lpf > lim_E:
                                flags |= np.int32(16)
                            lim_F = q if q > np.uint32(29) else np.uint32(29)
                            if lpf > lim_F:
                                flags |= np.int32(32)
                            if flags != 0 and nout < max_out:
                                out_n[nout] = np.int64(n)
                                out_k[nout] = np.int64(k)
                                out_lpf[nout] = np.int64(lpf)
                                out_flags[nout] = flags
                                nout += 1
            k = (k - np.uint32(1)) & rem

    return submasks, out_n[:nout], out_k[:nout], out_lpf[:nout], out_flags[:nout]


@njit(parallel=True)
def scan_n_parallel(n_start: int, n_end: int, primes: np.ndarray, n_chunks: int):
    """Run scan_n_chunk across n_chunks interleaved chunks using Numba threads."""
    total_sub = np.zeros(n_chunks, dtype=np.int64)
    # Fixed per-chunk output buffer (max 256 per chunk)
    cap = 256
    buf_n = np.zeros((n_chunks, cap), dtype=np.int64)
    buf_k = np.zeros((n_chunks, cap), dtype=np.int64)
    buf_lpf = np.zeros((n_chunks, cap), dtype=np.int64)
    buf_fl = np.zeros((n_chunks, cap), dtype=np.int32)
    buf_cnt = np.zeros(n_chunks, dtype=np.int32)

    span = (n_end - n_start + 1 + n_chunks - 1) // n_chunks
    for cid in prange(n_chunks):
        a = n_start + cid * span
        b = a + span - 1
        if b > n_end:
            b = n_end
        if a <= b:
            sub, on, ok, ol, of = scan_n_chunk(a, b, primes)
            total_sub[cid] = sub
            cnt = on.shape[0]
            if cnt > cap:
                cnt = cap
            buf_cnt[cid] = cnt
            for j in range(cnt):
                buf_n[cid, j] = on[j]
                buf_k[cid, j] = ok[j]
                buf_lpf[cid, j] = ol[j]
                buf_fl[cid, j] = of[j]

    return total_sub.sum(), buf_cnt, buf_n, buf_k, buf_lpf, buf_fl


# ===================== REGIME 1 KUMMER-CRT ENGINE =====================

@njit(inline="always")
def modinv64(a: np.uint64, m: np.uint64) -> np.uint64:
    """Modular inverse of a mod m (gcd(a, m) == 1) using iterative extended Euclid."""
    t = np.int64(0)
    newt = np.int64(1)
    r = np.int64(m)
    newr = np.int64(a % m)
    while newr != 0:
        q = r // newr
        t, newt = newt, t - q * newt
        r, newr = newr, r - q * newr
    if t < 0:
        t += np.int64(m)
    return np.uint64(t)


@njit(inline="always")
def is_exc_regime1(n: np.uint64, k: np.uint64, primes: np.ndarray) -> bool:
    if (n & k) != k:
        return False
    nprimes = primes.shape[0]
    for i in range(1, nprimes):
        p = np.uint64(primes[i])
        if p > k:
            break
        if p_divides64(n, k, p):
            return False
    return True


@njit
def factor_prime_powers(m: int, spf: np.ndarray):
    """Return prime powers p^a || m and corresponding base primes p (up to 12 factors)."""
    pps = np.empty(12, dtype=np.uint64)
    ps = np.empty(12, dtype=np.uint64)
    cnt = 0
    x = m
    while x > 1:
        p = spf[x]
        q = np.uint64(1)
        while x % p == 0:
            x //= p
            q *= np.uint64(p)
        pps[cnt] = q
        ps[cnt] = np.uint64(p)
        cnt += 1
    return cnt, pps, ps


@njit
def crt_intersect_modulus(
    k: np.uint64,
    m_target: int,
    delta_c: int,
    skip_two: bool,
    cur_res: np.ndarray,
    cur_n: int,
    cur_mod: np.uint64,
    spf: np.ndarray,
    max_buf: int,
):
    """Intersect existing residue list (mod cur_mod) with all prime powers p^a || m_target
    (skipping p=2 if skip_two is True so gcd(cur_mod, q) == 1).
    Uses exact Kummer digit-dominance on [max(0, q - delta_c), q - 1] — 100% airtight!
    """
    cnt, pps, ps = factor_prime_powers(m_target, spf)
    res = cur_res
    nr = cur_n
    mod = cur_mod

    for i in range(cnt):
        p = ps[i]
        if skip_two and p == np.uint64(2):
            continue
        q = pps[i]
        # Exact valid residues r in [0, q-1] with r >=_{base p} (k % q)
        k_mod_q = k % q
        # Note: since q | (k + delta_c), k_mod_q = (q - delta_c % q) % q.
        # In particular, if q > delta_c then k_mod_q == q - delta_c, so every valid r >= q - delta_c.
        # In ALL cases (even q <= delta_c), checking r in [k_mod_q, q-1] is 100% exact!
        valid_r = np.empty(8, dtype=np.uint64)
        n_valid = 0
        for r in range(k_mod_q, q):
            if not p_divides64(np.uint64(r), k_mod_q, p):
                valid_r[n_valid] = np.uint64(r)
                n_valid += 1
        # If every residue is valid (n_valid == q), skip (no constraint, avoids blowup)
        if np.uint64(n_valid) == q:
            continue
        inv = modinv64(mod % q, q)
        next_res = np.empty(nr * n_valid if nr * n_valid <= max_buf else max_buf, dtype=np.uint64)
        nnr = 0
        for j in range(nr):
            base_r = res[j]
            base_mod_q = base_r % q
            for vi in range(n_valid):
                vr = valid_r[vi]
                diff = (vr + q - base_mod_q) % q
                t = (diff * inv) % q
                if nnr < max_buf:
                    next_res[nnr] = base_r + mod * t
                    nnr += 1
        res = next_res
        nr = nnr
        mod *= q
    return res, nr, mod


@njit
def regime1_chunk(k_start: int, k_end: int, spf: np.ndarray, primes: np.ndarray):
    """Exhaustively check 2k <= n <= k^2 for lpf(C(n, k)) > k across k in [k_start, k_end]."""
    max_exc = 64
    exc_n = np.empty(max_exc, dtype=np.uint64)
    exc_k = np.empty(max_exc, dtype=np.uint64)
    nexc = 0
    cands = np.int64(0)
    overflow_flag = np.int32(0)

    max_buf = 524288
    init_res = np.empty(1, dtype=np.uint64)

    for k_i in range(k_start, k_end + 1):
        k = np.uint64(k_i)
        nmax = k * k
        nmin = np.uint64(2) * k

        if k_i < 20:
            for n in range(nmin, nmax + np.uint64(1)):
                cands += 1
                if is_exc_regime1(n, k, primes):
                    if nexc < max_exc:
                        exc_n[nexc] = n
                        exc_k[nexc] = k
                        nexc += 1
            continue

        if spf[k_i + 1] != k_i + 1:
            # Case 1: k+1 is composite => n == -1 (mod k+1) [1 residue!]
            init_res[0] = k
            mod = np.uint64(k_i + 1)
            if spf[k_i + 2] != k_i + 2:
                # Case 1a: k+2 composite, gcd(k+1, k+2)=1 => M = (k+1)(k+2) > k^2
                res, nr, mod = crt_intersect_modulus(
                    k, k_i + 2, 2, False, init_res, 1, mod, spf, max_buf
                )
            else:
                # Case 1b: k+2 is odd prime => k+1 is odd, k+3 is even composite, gcd(k+1, k+3)=1!
                # Every prime factor of k+3 is <= (k+3)/2 < k!
                res, nr, mod = crt_intersect_modulus(
                    k, k_i + 3, 3, False, init_res, 1, mod, spf, max_buf
                )
        else:
            # Case 2: k+1 is odd prime (k even >= 20), so k+2 is even composite!
            init_res[0] = np.uint64(0)
            res, nr, mod = crt_intersect_modulus(
                k, k_i + 2, 2, False, init_res, 1, np.uint64(1), spf, max_buf
            )
            if spf[k_i + 3] != k_i + 3:
                # Case 2a: k+3 is odd composite, gcd(k+2, k+3)=1, all prime factors <= (k+3)/3 < k!
                res, nr, mod = crt_intersect_modulus(
                    k, k_i + 3, 3, False, res, nr, mod, spf, max_buf
                )
            else:
                # Case 2b: twin primes (k+1, k+3)! k+4 is even composite; odd part of (k+4) is
                # coprime to k+2 (since gcd(k+2, k+4) = 2), and every prime factor <= (k+4)/2 < k!
                res, nr, mod = crt_intersect_modulus(
                    k, k_i + 4, 4, True, res, nr, mod, spf, max_buf
                )

        if nr >= max_buf:
            overflow_flag = np.int32(1)

        for j in range(nr):
            n = res[j]
            if n < nmin:
                need = nmin - n
                steps = (need + mod - np.uint64(1)) // mod
                n += steps * mod
            while n <= nmax:
                cands += 1
                if is_exc_regime1(n, k, primes):
                    if nexc < max_exc:
                        exc_n[nexc] = n
                        exc_k[nexc] = k
                        nexc += 1
                if nmax - n < mod:
                    break
                n += mod

    return cands, overflow_flag, exc_n[:nexc], exc_k[:nexc]


@njit(parallel=True)
def regime1_parallel(k_start: int, k_end: int, spf: np.ndarray, primes: np.ndarray, n_chunks: int):
    total_cands = np.zeros(n_chunks, dtype=np.int64)
    overflows = np.zeros(n_chunks, dtype=np.int32)
    cap = 64
    buf_n = np.zeros((n_chunks, cap), dtype=np.uint64)
    buf_k = np.zeros((n_chunks, cap), dtype=np.uint64)
    buf_cnt = np.zeros(n_chunks, dtype=np.int32)

    span = (k_end - k_start + 1 + n_chunks - 1) // n_chunks
    for cid in prange(n_chunks):
        a = k_start + cid * span
        b = a + span - 1
        if b > k_end:
            b = k_end
        if a <= b:
            cands, ovf, en, ek = regime1_chunk(a, b, spf, primes)
            total_cands[cid] = cands
            overflows[cid] = ovf
            cnt = en.shape[0]
            if cnt > cap:
                cnt = cap
            buf_cnt[cid] = cnt
            for j in range(cnt):
                buf_n[cid, j] = en[j]
                buf_k[cid, j] = ek[j]

    return total_cands.sum(), overflows.sum(), buf_cnt, buf_n, buf_k


def run_scan_n(n_max: int, threads: int, out_tsv: str | None):
    set_num_threads(threads)
    t0 = time.time()
    _, primes = build_spf_and_primes(n_max + 100)
    t_sieve = time.time() - t0
    print(f"[scan-n] Built {len(primes)} primes up to {n_max+100} in {t_sieve:.2f}s (threads={threads})")

    # Warmup JIT on tiny range
    _ = scan_n_parallel(4, 100, primes, 2)
    t_run = time.time()

    all_rows = []
    total_submasks = 0
    step = 250_000 if n_max >= 500_000 else n_max
    cur = 4
    while cur <= n_max:
        end = min(n_max, cur + step - 1)
        sub, cnts, bn, bk, bl, bf = scan_n_parallel(cur, end, primes, max(threads * 8, 8))
        total_submasks += int(sub)
        for cid in range(cnts.shape[0]):
            for j in range(int(cnts[cid])):
                all_rows.append((int(bn[cid, j]), int(bk[cid, j]), int(bl[cid, j]), int(bf[cid, j])))
        dt = time.time() - t_run
        cnt_B = sum(1 for r in all_rows if r[3] & 2)
        cnt_A = sum(1 for r in all_rows if r[3] & 1)
        cnt_E = sum(1 for r in all_rows if r[3] & 16)
        cnt_F = sum(1 for r in all_rows if r[3] & 32)
        print(
            f"  n <= {end:>9,d}: submasks={total_submasks:>13,d} | "
            f"A(max(n/k,k))={cnt_A} B(>13)={cnt_B} E(>17)={cnt_E} F(>29)={cnt_F} ({dt:.2f}s)",
            flush=True,
        )
        cur = end + 1

    all_rows.sort()
    if out_tsv:
        os.makedirs(os.path.dirname(out_tsv), exist_ok=True)
        with open(out_tsv, "w", encoding="utf-8") as f:
            f.write("n\tk\tlpf\tn_over_k\tflags\tclasses\n")
            for n, k, lpf, fl in all_rows:
                cls = []
                if fl & 1:
                    cls.append("A:max(n/k,k)")
                if fl & 2:
                    cls.append("B:max(n/k,13)")
                if fl & 4:
                    cls.append("C:Selfridge_k2m1")
                if fl & 8:
                    cls.append("D:Guy_17.125k")
                if fl & 16:
                    cls.append("E:max(n/k,17)")
                if fl & 32:
                    cls.append("F:max(n/k,29)")
                f.write(f"{n}\t{k}\t{lpf}\t{n/k:.6f}\t{fl}\t{','.join(cls)}\n")
        print(f"[scan-n] Wrote {len(all_rows)} rows to {out_tsv}")

    # Summary breakdown
    for bit, name in [
        (1, "A: lpf > max(n/k, k)  [Erdos #1094 / ELS88]"),
        (2, "B: lpf > max(n/k, 13) [ELS93 12-exception remark]"),
        (16, "E: lpf > max(n/k, 17)"),
        (32, "F: lpf > max(n/k, 29) [ELS93 main conjecture]"),
        (4, "C: n >= k^2-1 & lpf > n/k [Selfridge 1977]"),
        (8, "D: n > 17.125k & lpf > n/k [Guy B31/B33]"),
    ]:
        rows = [r for r in all_rows if r[3] & bit]
        print(f"\n=== {name}: {len(rows)} found (n <= {n_max:,d}) ===")
        if len(rows) <= 30:
            for n, k, lpf, _ in rows:
                print(f"  C({n}, {k}): lpf={lpf}, n/k={n/k:.4f}")
        else:
            for n, k, lpf, _ in rows[:15]:
                print(f"  C({n}, {k}): lpf={lpf}, n/k={n/k:.4f}")
            print(f"  ... ({len(rows) - 25} more in TSV) ...")
            for n, k, lpf, _ in rows[-10:]:
                print(f"  C({n}, {k}): lpf={lpf}, n/k={n/k:.4f}")


def run_regime1(k_max: int, threads: int):
    set_num_threads(threads)
    t0 = time.time()
    spf, primes = build_spf_and_primes(k_max + 20)
    t_sieve = time.time() - t0
    print(f"[regime1] Built spf & {len(primes)} primes up to {k_max+20} in {t_sieve:.2f}s (threads={threads})")

    # Warmup JIT
    _ = regime1_parallel(2, 100, spf, primes, 2)
    t_run = time.time()

    all_exc = []
    total_cands = 0
    total_ovf = 0
    step = 200_000 if k_max >= 200_000 else k_max
    cur = 2
    while cur <= k_max:
        end = min(k_max, cur + step - 1)
        cands, ovf, cnts, bn, bk = regime1_parallel(cur, end, spf, primes, max(threads * 16, 16))
        total_cands += int(cands)
        total_ovf += int(ovf)
        for cid in range(cnts.shape[0]):
            for j in range(int(cnts[cid])):
                all_exc.append((int(bn[cid, j]), int(bk[cid, j])))
        dt = time.time() - t_run
        print(
            f"  k <= {end:>9,d} (n <= {end*end:>15,d}): CRT_cands={total_cands:>12,d} "
            f"exc={len(all_exc)} ovf={total_ovf} ({dt:.2f}s)",
            flush=True,
        )
        cur = end + 1

    assert total_ovf == 0, f"ERROR: CRT buffer overflowed {total_ovf} times!"
    all_exc.sort()
    print(f"\n[regime1] DONE ALL 2k <= n <= k^2 for 2 <= k <= {k_max:,d} (n <= {k_max*k_max:,d})!")
    print(f"Total CRT candidates tested: {total_cands:,d}, exceptions found: {len(all_exc)}")
    for n, k in all_exc:
        print(f"  Regime-1 exception: C({n}, {k}) (n/k={n/k:.4f}, k^2={k*k})")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scan-n", type=int, default=0, help="Run base-2 submask scan up to N_max")
    ap.add_argument("--regime1", type=int, default=0, help="Run Kummer-CRT Regime 1 up to K_max")
    ap.add_argument("--threads", type=int, default=2, help="Max CPU threads (keep <= 2)")
    ap.add_argument("--out-tsv", type=str, default="data/exceptions_1094.tsv")
    args = ap.parse_args()
    if args.threads > 2:
        raise ValueError("Keep --threads <= 2 to respect CPU budget!")
    if args.regime1 > 0:
        run_regime1(args.regime1, args.threads)
    if args.scan_n > 0:
        run_scan_n(args.scan_n, args.threads, args.out_tsv)


if __name__ == "__main__":
    main()
