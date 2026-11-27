/*
 * search.c -- targeted search for odd n that are NOT of the form p + 2^a + 2^b
 *             (p prime, a, b >= 1), restricted to one residue class n == R (mod Q).
 *
 * Greathouse's conjecture (OEIS A156695): every such n > 5 is divisible by 255.
 *
 *   gcc -O3 -march=native -fopenmp -o search.exe search.c
 *   search.exe Q R FROM TO THREADS [CKPT]
 *
 * Scans every odd n in [FROM, TO) with n == R (mod Q), n < 2^63.  Q must be odd.
 * For each n it looks for a prime m = n - 2^a - 2^b with 1 <= a <= b.
 *   - Pairs (a,b) whose m is divisible by a small odd prime q < 1024 are removed with
 *     precomputed bit masks (m == q itself is handled by a slow path, see below).
 *   - The remaining m get a strong probable prime test to base 2; a pass is confirmed
 *     with the 7-base deterministic Miller-Rabin test for 64-bit integers
 *     (bases 2, 325, 9375, 28178, 450775, 9780504, 1795265022).
 *   - If no pair gives a prime, n is printed as "HIT n" (to be verified independently).
 * Slow path: when n is within 1024 of a number with at most two 1-bits, some m could be a
 * small prime; then every pair is tested directly with no sieve.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;

#define MAXB 62
#define NPAIR (MAXB * (MAXB + 1) / 2)
#define W ((NPAIR + 63) / 64)
#define PMAX 200

static int pa[NPAIR], pb[NPAIR];
static u64 psum[NPAIR];

/* ---------- 64-bit Montgomery Miller-Rabin ---------- */
static inline u64 mont_inv(u64 n) { u64 x = n; for (int i = 0; i < 5; i++) x *= 2 - n * x; return x; }
static inline u64 mont_mul(u64 a, u64 b, u64 n, u64 ninv) {
    u128 t = (u128)a * b;
    u64 m = (u64)t * ninv;
    u64 hi = (u64)(t >> 64), mh = (u64)(((u128)m * n) >> 64);
    return hi >= mh ? hi - mh : hi - mh + n;
}
static int sprp(u64 n, u64 base) { /* n odd > 2 */
    u64 ninv = mont_inv(n);
    u64 one = (u64)(((u128)1 << 64) % n);
    u64 r2 = (u64)(((u128)one * one) % n);
    u64 mone = n - one;
    base %= n;
    if (base == 0) return 1;
    u64 x = mont_mul(base, r2, n, ninv);
    u64 d = n - 1; int s = __builtin_ctzll(d); d >>= s;
    u64 y = one;
    while (d) { if (d & 1) y = mont_mul(y, x, n, ninv); x = mont_mul(x, x, n, ninv); d >>= 1; }
    if (y == one || y == mone) return 1;
    for (int i = 1; i < s; i++) { y = mont_mul(y, y, n, ninv); if (y == mone) return 1; if (y == one) return 0; }
    return 0;
}
static int is_prime64(u64 n) {
    if (n < 2) return 0;
    static const u64 sp[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (int i = 0; i < 12; i++) { if (n == sp[i]) return 1; if (n % sp[i] == 0) return 0; }
    static const u64 bs[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
    for (int i = 0; i < 7; i++) if (!sprp(n, bs[i])) return 0;
    return 1;
}
static inline int confirm(u64 m) { /* m passed sprp base 2 */
    static const u64 bs[] = {325, 9375, 28178, 450775, 9780504, 1795265022};
    for (int i = 0; i < 6; i++) if (!sprp(m, bs[i])) return 0;
    return 1;
}

/* ---------- sieve tables ---------- */
static int nsp; static int sp[64]; static u64 *kill[64]; /* kill[i][r*W .. ] */

static int has_rep_slow(u64 n) {
    for (int i = 0; i < NPAIR; i++) {
        if (psum[i] + 2 > n) continue;
        if (is_prime64(n - psum[i])) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: search Q R FROM TO THREADS [CKPT]\n"); return 2; }
    u64 Q = strtoull(argv[1], 0, 10), R = strtoull(argv[2], 0, 10);
    u64 FROM = strtoull(argv[3], 0, 10), TO = strtoull(argv[4], 0, 10);
    int threads = atoi(argv[5]);
    const char *ckpt = argc > 6 ? argv[6] : NULL;
    if (Q % 2 == 0 || TO > ((u64)1 << 63)) { fprintf(stderr, "Q must be odd, TO <= 2^63\n"); return 2; }
    if (R % 2 == 0) R += Q; /* odd representative mod 2Q */
    u64 step = 2 * Q;

    int k = 0;
    for (int a = 1; a <= MAXB; a++) for (int b = a; b <= MAXB; b++) { pa[k] = a; pb[k] = b; psum[k] = ((u64)1 << a) + ((u64)1 << b); k++; }

    /* sieve primes: odd primes <= PMAX not dividing Q (those are folded into a base mask) plus
       the prime factors of Q below 1024 */
    static u64 base[W]; memset(base, 0, sizeof base);
    nsp = 0;
    for (int q = 3; q < 1024; q += 2) {
        int pr = 1; for (int d = 3; d * d <= q; d += 2) if (q % d == 0) pr = 0;
        if (!pr) continue;
        int forced = (Q % q == 0);
        if (!forced && q > PMAX) continue;
        if (forced) {
            int r = (int)(R % q);
            for (int i = 0; i < NPAIR; i++) if ((int)(psum[i] % q) == r) base[i >> 6] |= (u64)1 << (i & 63);
        } else {
            kill[nsp] = calloc((size_t)q * W, 8);
            for (int i = 0; i < NPAIR; i++) { int r = (int)(psum[i] % q); kill[nsp][(size_t)r * W + (i >> 6)] |= (u64)1 << (i & 63); }
            sp[nsp++] = q;
        }
    }

    /* first candidate index */
    u64 k0 = FROM <= R ? 0 : (FROM - R + step - 1) / step;
    u64 k1 = TO <= R ? 0 : (TO - R + step - 1) / step; /* n = R + step*k, k in [k0,k1) */
    if (ckpt) { FILE *f = fopen(ckpt, "r"); if (f) { u64 kk; if (fscanf(f, "%llu", (unsigned long long *)&kk) == 1 && kk > k0) k0 = kk; fclose(f); } }
    fprintf(stderr, "Q=%llu R=%llu step=%llu k in [%llu,%llu) sieve primes=%d threads=%d\n",
            (unsigned long long)Q, (unsigned long long)R, (unsigned long long)step, (unsigned long long)k0, (unsigned long long)k1, nsp, threads);
    omp_set_num_threads(threads);
    const u64 BLK = (u64)1 << 20, SUPER = (u64)1 << 28;
    double t0 = omp_get_wtime();
    u64 tot = 0, tests = 0, hits = 0, maxtests = 0, maxn = 0, slow = 0;
    for (u64 ks = k0; ks < k1; ks += SUPER) {
        u64 ke = ks + SUPER < k1 ? ks + SUPER : k1;
        long long nblk = (long long)((ke - ks + BLK - 1) / BLK);
        #pragma omp parallel for schedule(dynamic, 1) reduction(+ : tot, tests, hits, slow)
        for (long long bi = 0; bi < nblk; bi++) {
            u64 ka = ks + (u64)bi * BLK, kb = ka + BLK < ke ? ka + BLK : ke;
            int res[64], inc[64];
            u64 n = R + step * ka;
            for (int i = 0; i < nsp; i++) { res[i] = (int)(n % sp[i]); inc[i] = (int)(step % sp[i]); }
            u64 lmax = 0, lmaxn = 0;
            for (u64 kk = ka; kk < kb; kk++, n += step) {
                tot++;
                u64 al[W];
                for (int w = 0; w < W; w++) al[w] = base[w];
                for (int i = 0; i < nsp; i++) {
                    const u64 *km = kill[i] + (size_t)res[i] * W;
                    for (int w = 0; w < W; w++) al[w] |= km[w];
                    res[i] += inc[i]; if (res[i] >= sp[i]) res[i] -= sp[i];
                }
                u64 h = n >> 10;
                int found = 0; u64 nt = 0;
                if (__builtin_popcountll(h) <= 2 || __builtin_popcountll(h - 1) <= 2) {
                    slow++; found = has_rep_slow(n);
                } else {
                    for (int w = W - 1; w >= 0 && !found; w--) {
                        u64 x = ~al[w]; if (w == W - 1 && (NPAIR & 63)) x &= (((u64)1 << (NPAIR & 63)) - 1);
                        while (x) {
                            int i = (w << 6) + (63 - __builtin_clzll(x)); x &= ~((u64)1 << (i & 63));
                            if (psum[i] + 2 > n) continue;
                            u64 m = n - psum[i];
                            nt++;
                            if (sprp(m, 2) && confirm(m)) { found = 1; break; }
                        }
                    }
                }
                tests += nt;
                if (nt > lmax) { lmax = nt; lmaxn = n; }
                if (!found) {
                    hits++;
                    #pragma omp critical
                    { printf("HIT %llu  mod17=%d mod255=%d\n", (unsigned long long)n, (int)(n % 17), (int)(n % 255)); fflush(stdout); }
                }
            }
            #pragma omp critical
            { if (lmax > maxtests) { maxtests = lmax; maxn = lmaxn; } }
        }
        u64 nlast = R + step * ke;
        fprintf(stderr, "done n < %llu (%.3e)  cand %llu  hits %llu  avg tests %.2f  max tests %llu at n=%llu  slow %llu  %.0f s\n",
                (unsigned long long)nlast, (double)nlast, (unsigned long long)tot, (unsigned long long)hits,
                (double)tests / (double)(tot ? tot : 1), (unsigned long long)maxtests, (unsigned long long)maxn, (unsigned long long)slow, omp_get_wtime() - t0);
        if (ckpt) { FILE *f = fopen(ckpt, "w"); if (f) { fprintf(f, "%llu\n", (unsigned long long)ke); fclose(f); } }
    }
    printf("FINISHED Q=%llu R=%llu [%llu,%llu): candidates %llu, hits %llu\n", (unsigned long long)Q, (unsigned long long)R,
           (unsigned long long)FROM, (unsigned long long)TO, (unsigned long long)tot, (unsigned long long)hits);
    return 0;
}
