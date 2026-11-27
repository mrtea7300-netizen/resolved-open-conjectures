/*
 * split_sieve.c -- finite check for the exponent-3 theorem (see proof.md, Step 5).
 *
 * For every prime p with p = 3 (mod 4) and lo <= p < hi, let D = -p (a fundamental
 * discriminant) and find q(p), the least prime that splits in Q(sqrt(-p)):
 *   q = 2 splits  iff  -p = 1 (mod 8)  iff  p = 7 (mod 8);
 *   odd q != p splits iff (-p | q) = +1 (Legendre symbol).
 * If 4*q(p)^3 < p, Lemma 1 of proof.md shows the class group of Q(sqrt(-p)) does not
 * have exponent dividing 3. Every other p ("survivor") is printed; survivors are
 * settled exactly by exact_classgroups.py.
 *
 * It also counts all primes in [lo, hi) and primes = 1, 3 (mod 4) (to cross-check the sieve
 * against known values of pi(x)), and prints the record values of q(p) and of 4 q(p)^3 / p
 * for p > 10^6 (the hardest cases).
 *
 * Build:  clang -O3 -march=native -o split_sieve split_sieve.c
 * Run:    split_sieve <lo> <hi>          (lo >= 3, hi <= 2^40)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define QMAX 20000           /* odd primes q below this are tabulated */
#define SEG  (1u << 21)      /* odd numbers per segment */

static uint32_t *qs; static int nq;           /* primes < QMAX (including 2) */
static uint8_t **qr;                          /* qr[i][r] = 1 iff r is a nonzero square mod qs[i] */
static uint32_t *sp; static int nsp;          /* sieving primes up to sqrt(hi) */

static void small_primes(uint32_t lim, uint32_t **out, int *n) {
    uint8_t *c = calloc(lim + 1, 1);
    int cnt = 0;
    for (uint32_t i = 2; i <= lim; i++) if (!c[i]) { cnt++; for (uint64_t j = (uint64_t)i * i; j <= lim; j += i) c[j] = 1; }
    *out = malloc(sizeof(uint32_t) * cnt); *n = 0;
    for (uint32_t i = 2; i <= lim; i++) if (!c[i]) (*out)[(*n)++] = i;
    free(c);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s lo hi\n", argv[0]); return 1; }
    uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    if (lo < 3) lo = 3;
    if (lo % 2 == 0) lo++;

    small_primes(QMAX, &qs, &nq);
    qr = malloc(sizeof(uint8_t *) * nq);
    for (int i = 1; i < nq; i++) {            /* i = 0 is q = 2, handled separately */
        uint32_t q = qs[i];
        qr[i] = calloc(q, 1);
        for (uint64_t x = 1; x < q; x++) qr[i][(x * x) % q] = 1;
    }
    uint32_t root = (uint32_t)sqrt((double)hi) + 2;
    small_primes(root, &sp, &nsp);

    uint8_t *seg = malloc(SEG);
    uint64_t nprimes = 0, n1 = 0, n3 = 0, nsurv = 0, nbig = 0;
    uint32_t qrec = 0;                       /* record q(p) */
    double ratio_rec = 0;                    /* record 4 q^3 / p for p > 1e6 */

    for (uint64_t base = lo; base < hi; base += 2ull * SEG) {
        /* seg[k] represents base + 2k */
        uint64_t top = base + 2ull * SEG; if (top > hi) top = hi;
        uint32_t len = (uint32_t)((top - base + 1) / 2);
        memset(seg, 1, len);
        for (int i = 1; i < nsp; i++) {        /* odd sieving primes */
            uint64_t p = sp[i];
            if (p * p >= top) break;
            uint64_t s = p * p;
            if (s < base) { s = ((base + p - 1) / p) * p; if (s % 2 == 0) s += p; }
            for (uint64_t j = (s - base) / 2; j < len; j += p) seg[j] = 0;
        }
        for (uint32_t k = 0; k < len; k++) {
            if (!seg[k]) continue;
            uint64_t p = base + 2ull * k;
            if (p >= hi) break;
            nprimes++;
            if ((p & 3) == 1) { n1++; continue; }
            n3++;
            /* least split prime q(p) */
            uint32_t q = 0;
            if ((p & 7) == 7) q = 2;
            else {
                for (int i = 1; i < nq; i++) {
                    uint32_t qq = qs[i];
                    if (qq == p) continue;
                    uint32_t r = (uint32_t)(p % qq);
                    uint32_t mr = r ? qq - r : 0;        /* -p mod q */
                    if (qr[i][mr]) { q = qq; break; }
                }
            }
            if (q == 0) { printf("NOSPLIT %llu\n", (unsigned long long)p); nbig++; continue; }
            if (q > qrec) { qrec = q; printf("RECORD_Q p=%llu q=%u\n", (unsigned long long)p, q); }
            double qq3 = 4.0 * (double)q * q * q;
            if (p > 1000000ull) {
                double ratio = qq3 / (double)p;
                if (ratio > ratio_rec) { ratio_rec = ratio; printf("RECORD_RATIO p=%llu q=%u 4q^3/p=%.6g\n", (unsigned long long)p, q, ratio); }
            }
            /* survivor iff NOT (4 q^3 < p); exact integer test */
            unsigned __int128 lhs = (unsigned __int128)4 * q * q * q;
            if (!(lhs < p)) { printf("SURVIVOR %llu q=%u\n", (unsigned long long)p, q); nsurv++; }
        }
        fflush(stdout);
    }
    printf("DONE lo=%llu hi=%llu primes=%llu p1mod4=%llu p3mod4=%llu survivors=%llu nosplit=%llu maxq=%u maxratio=%.6g\n",
           (unsigned long long)lo, (unsigned long long)hi, (unsigned long long)nprimes,
           (unsigned long long)n1, (unsigned long long)n3, (unsigned long long)nsurv,
           (unsigned long long)nbig, qrec, ratio_rec);
    return 0;
}
