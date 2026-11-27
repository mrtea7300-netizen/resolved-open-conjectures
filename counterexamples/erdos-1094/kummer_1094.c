/*
 * Fast Kummer base-2 submask + base-p carry-free scanner for Erdős Problem #1094
 * (Erdős-Lacampagne-Selfridge 1988, 1993; Selfridge 1977; Guy B31/B33).
 *
 * Uses Kummer's theorem:
 *   2 nmid C(n, k)  <=>  (k & n) == k  (k is a binary submask of n!)
 * Enumerating only binary submasks k of n with 2 <= k <= n/2 reduces the search
 * space from O(N^2) to O(N^{log_2(3)}) = O(N^{1.585}) — over 500x faster at N=10^6!
 *
 * Checks ALL pairs (n, k) with 2 <= k <= n/2 and n <= N_max for:
 *   (A) lpf(C(n, k)) > max(n/k, k)   [ELS88 14-exception conjecture, Erdős #1094]
 *   (B) lpf(C(n, k)) > max(n/k, 13)  [ELS93 12-exception stronger conjecture]
 *   (C) n >= k^2 - 1 and lpf > n/k   [Selfridge 1977 conjecture]
 *   (D) n > 17.125*k and lpf > n/k   [Guy B31/B33 Selfridge conjecture]
 *
 * Compile: gcc -O3 -march=native kummer_1094.c -o bin/kummer_1094
 * Usage:   ./bin/kummer_1094 <N_max>
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int *primes;
static int nprimes;

static void build_primes(int lim) {
    uint8_t *isp = (uint8_t *)malloc((size_t)(lim + 1));
    memset(isp, 1, (size_t)(lim + 1));
    isp[0] = isp[1] = 0;
    for (int i = 2; (long long)i * i <= lim; i++) {
        if (isp[i]) {
            for (int j = i * i; j <= lim; j += i) isp[j] = 0;
        }
    }
    int cnt = 0;
    for (int i = 2; i <= lim; i++) if (isp[i]) cnt++;
    primes = (int *)malloc((size_t)cnt * sizeof(int));
    nprimes = 0;
    for (int i = 2; i <= lim; i++) if (isp[i]) primes[nprimes++] = i;
    free(isp);
}

/* Return 1 iff p divides C(n, k) by Kummer's theorem (carry in base p for k + (n-k) = n) */
static inline int p_divides(uint32_t n, uint32_t k, uint32_t p) {
    uint32_t nn = n, kk = k;
    while (kk > 0) {
        if ((nn % p) < (kk % p)) return 1;
        nn /= p;
        kk /= p;
    }
    return 0;
}

static uint32_t exact_lpf(uint32_t n, uint32_t k) {
    for (int i = 0; i < nprimes; i++) {
        uint32_t p = (uint32_t)primes[i];
        if (p > n) break;
        if (p_divides(n, k, p)) return p;
    }
    return n + 1;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <N_max>\n", argv[0]);
        return 1;
    }
    uint32_t N_max = (uint32_t)strtoul(argv[1], NULL, 10);
    build_primes((int)N_max);

    struct timespec ts0, ts1;
    clock_gettime(CLOCK_MONOTONIC, &ts0);

    long long cnt_A = 0, cnt_B = 0, cnt_C = 0, cnt_D = 0;
    long long submasks_checked = 0;

    for (uint32_t n = 4; n <= N_max; n++) {
        /* If 2 | C(n, k) is avoided, k must be a binary submask of n with 2 <= k <= n/2.
         * Fast trick: if top bit of n is B = 1 << (31 - clz(n)), then k <= n/2 implies
         * k does NOT have bit B set! So k is a submask of (n ^ B)!
         * Wait: if n = B + r with r < B, then any submask k of (n ^ B) = r has k <= r < B <= n/2!
         * Wait: could a submask with bit B set have 2*k <= n? NO, because k >= B => 2*k >= 2*B > n!
         * EXCEPT when n = 2*B? No, B is the highest set bit, so B <= n < 2*B, thus 2*B > n ALWAYS!
         * Therefore k <= n/2 AND (k & n) == k  <==>  k is ANY submask of (n ^ highest_bit(n))!! */
        uint32_t hi = 1u << (31 - __builtin_clz(n));
        uint32_t rem = n ^ hi;
        if (rem < 2) continue;

        /* Precompute base-3, base-5, base-7 digits of n? Simple p_divides is super fast! */
        for (uint32_t k = rem; k >= 2; k = (k - 1) & rem) {
            submasks_checked++;
            /* Quick filter: we want lpf > max(n/k, k) OR lpf > max(n/k, 13) OR
             * (n >= k^2 - 1 and lpf > n/k) OR (8*n > 137*k and lpf > n/k).
             * Notice: in ALL four cases, since n >= 2k:
             *   - for (A): need lpf > max(n/k, k) >= 3 (for k>=3); if k==2, lpf <= n/2 always!
             *   - for (B): need lpf > 13 => p=3,5,7,11,13 do NOT divide C(n,k)!
             *   - for (C): n >= k^2 - 1 => n/k >= k - 1/k; for k >= 4, n/k >= 3 => 3 nmid C(n,k)!
             *   - for (D): n > 17.125*k => n/k >= 17 => p=3,5,7,11,13,17 do NOT divide C(n,k)!
             * So first check p = 3! (Cuts 65% immediately!) */
            if (p_divides(n, k, 3)) continue;
            uint32_t q = n / k;
            uint32_t lim_A = (q > k) ? q : k;
            uint32_t lim_B = (q > 13) ? q : 13;
            int need_C = ((uint64_t)n + 1 >= (uint64_t)k * (uint64_t)k);
            int need_D = (8ULL * n > 137ULL * k);

            /* Minimum threshold among the four queries that can possibly trigger */
            uint32_t min_lim = lim_A < lim_B ? lim_A : lim_B;
            if (need_C && q < min_lim) min_lim = q;
            if (need_D && q < min_lim) min_lim = q;

            /* Fast check primes 5, 7, 11, 13 against min_lim */
            if (5 <= min_lim && p_divides(n, k, 5)) continue;
            if (7 <= min_lim && p_divides(n, k, 7)) continue;
            if (11 <= min_lim && p_divides(n, k, 11)) continue;
            if (13 <= min_lim && p_divides(n, k, 13)) continue;

            /* Check remaining primes up to min_lim */
            int ok = 1;
            for (int pi = 6; pi < nprimes; pi++) {
                uint32_t p = (uint32_t)primes[pi];
                if (p > min_lim) break;
                if (p_divides(n, k, p)) { ok = 0; break; }
            }
            if (!ok) continue;

            /* Compute exact lpf! */
            uint32_t lpf = exact_lpf(n, k);
            if (lpf > lim_A) {
                cnt_A++;
                printf("[A: >max(n/k,k) ] C(%u, %u) lpf=%u  n/k=%.4f\n", n, k, lpf, (double)n / k);
                fflush(stdout);
            }
            if (lpf > lim_B) {
                cnt_B++;
                printf("[B: >max(n/k,13)] C(%u, %u) lpf=%u  n/k=%.4f\n", n, k, lpf, (double)n / k);
                fflush(stdout);
            }
            if (need_C && lpf > q) {
                cnt_C++;
                printf("[C: Selfridge k^2-1] C(%u, %u) lpf=%u  n/k=%.4f\n", n, k, lpf, (double)n / k);
                fflush(stdout);
            }
            if (need_D && lpf > q) {
                cnt_D++;
                printf("[D: >17.125k    ] C(%u, %u) lpf=%u  n/k=%.4f\n", n, k, lpf, (double)n / k);
                fflush(stdout);
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &ts1);
    double dt = (ts1.tv_sec - ts0.tv_sec) + 1e-9 * (ts1.tv_nsec - ts0.tv_nsec);
    printf("\nDONE n <= %u in %.2fs (submasks checked: %lld)\n", N_max, dt, submasks_checked);
    printf("Totals: A(>max(n/k,k))=%lld, B(>max(n/k,13))=%lld, C(Selfridge k^2-1)=%lld, D(>17.125k)=%lld\n",
           cnt_A, cnt_B, cnt_C, cnt_D);
    return 0;
}
