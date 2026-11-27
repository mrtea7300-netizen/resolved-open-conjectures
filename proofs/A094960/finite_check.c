/* finite_check.c -- direct search for the witnesses of proof.md, Theorem 1, below the threshold.
 *
 * For every n in [LO, HI) and for each of four conditions j = 0, 1, 2, 3 it looks for the SMALLEST
 * prime p > sqrt(n) with  s_p(n) >= p  and
 *      j = 0:  nothing more
 *      j = 1:  p does not divide n+1
 *      j = 2:  p does not divide (n+1)(n+2)
 *      j = 3:  p^2 * n > (n+1)^2        (i.e. (n+1)/p < sqrt(n); Kellner's lambda*_n < sqrt(n))
 * where s_p(n) is the sum of the base-p digits of n, computed by repeated division (the program
 * does not use Lemma 2 of proof.md, nor the fact that n has two digits in base p).
 *
 * Output (stdout, plain text):
 *   - for each j: the list of n with NO such prime at all ("exceptions"; only possible for
 *     n <= PLIM, where every prime up to n is tried), and the number of "unresolved" n > PLIM
 *     (no witness among the primes <= PLIM; must be 0 for the run to count);
 *   - for each j: the running records of the offset  p - floor(sqrt(n))  of the smallest witness
 *     (the hardest cases), and a histogram of the index of the witness among the primes > sqrt(n);
 *   - a checksum (sum over n of the witness prime, mod 2^64) so that two implementations can be
 *     compared exactly.
 *
 * Build:  gcc -O2 -o finite_check finite_check.c
 * Run:    ./finite_check LO HI
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define PLIM 400000u /* primes are sieved up to here */
#define JMAX 4
#define HMAX 40

static uint32_t *primes;
static uint32_t nprimes;

static void sieve(void) {
    unsigned char *c = calloc(PLIM + 1, 1);
    primes = malloc(sizeof(uint32_t) * 40000);
    for (uint32_t i = 2; i <= PLIM; i++) {
        if (!c[i]) {
            primes[nprimes++] = i;
            for (uint64_t k = (uint64_t)i * i; k <= PLIM; k += i) c[k] = 1;
        }
    }
    free(c);
}

static inline uint64_t digit_sum(uint64_t n, uint64_t p) {
    uint64_t s = 0;
    while (n) {
        s += n % p;
        n /= p;
    }
    return s;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s LO HI\n", argv[0]);
        return 2;
    }
    uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    if (lo < 1) lo = 1;
    sieve();

    uint64_t F = 0;
    while ((F + 1) * (F + 1) <= lo) F++; /* F = floor(sqrt(lo)) */
    uint32_t idx = 0;                    /* index of the first prime > F */
    while (idx < nprimes && primes[idx] <= F) idx++;

    uint64_t nexc[JMAX] = {0}, unresolved[JMAX] = {0}, checksum[JMAX] = {0};
    uint64_t rec[JMAX] = {0}, hist[JMAX][HMAX + 1];
    uint64_t lastexc[JMAX] = {0};
    memset(hist, 0, sizeof hist);

    for (uint64_t n = lo; n < hi; n++) {
        if ((F + 1) * (F + 1) <= n) {
            F++;
            while (idx < nprimes && primes[idx] <= F) idx++;
        }
        int found[JMAX] = {0, 0, 0, 0};
        for (uint32_t i = idx; i < nprimes; i++) {
            uint64_t p = primes[i];
            if (p > n) break; /* s_p(n) = n < p for p > n */
            if (digit_sum(n, p) < p) continue;
            int d1 = ((n + 1) % p == 0), d2 = ((n + 2) % p == 0);
            int lam = ((unsigned __int128)p * p * n > (unsigned __int128)(n + 1) * (n + 1));
            int okc[JMAX] = {1, !d1, !d1 && !d2, lam};
            for (int j = 0; j < JMAX; j++) {
                if (found[j] || !okc[j]) continue;
                found[j] = 1;
                checksum[j] += p;
                uint64_t off = p - F, h = i - idx + 1;
                hist[j][h > HMAX ? HMAX : h]++;
                if (off > rec[j]) {
                    rec[j] = off;
                    printf("record j=%d n=%llu F=%llu p=%llu offset=%llu witness_index=%llu\n", j,
                           (unsigned long long)n, (unsigned long long)F, (unsigned long long)p,
                           (unsigned long long)off, (unsigned long long)h);
                }
            }
            if (found[2] && found[3]) break;
        }
        for (int j = 0; j < JMAX; j++) {
            if (found[j]) continue;
            if (n <= PLIM) {
                nexc[j]++;
                lastexc[j] = n;
                printf("exception j=%d n=%llu\n", j, (unsigned long long)n);
            } else {
                unresolved[j]++;
                printf("UNRESOLVED j=%d n=%llu\n", j, (unsigned long long)n);
            }
        }
    }
    for (int j = 0; j < JMAX; j++) {
        printf("summary j=%d range=[%llu,%llu) exceptions=%llu largest_exception=%llu unresolved=%llu "
               "max_offset=%llu checksum=%llu\n",
               j, (unsigned long long)lo, (unsigned long long)hi, (unsigned long long)nexc[j],
               (unsigned long long)lastexc[j], (unsigned long long)unresolved[j],
               (unsigned long long)rec[j], (unsigned long long)checksum[j]);
        printf("hist j=%d", j);
        for (int h = 1; h <= HMAX; h++)
            if (hist[j][h]) printf(" %d:%llu", h, (unsigned long long)hist[j][h]);
        printf("\n");
    }
    return 0;
}
