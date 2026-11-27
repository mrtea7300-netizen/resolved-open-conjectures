/* brute_1094.c -- plain double loop, written separately from dfs_1094.c as a reference.
 *
 * For every pair 2 <= k <= n/2, n <= NMAX (and n <= B*k unless B = 0) compute the least prime
 * factor of C(n,k) by testing the primes 2, 3, 5, ... in turn with Kummer's criterion in the
 * form "p divides C(n,k) iff adding k and n-k in base p produces a carry".
 * (dfs_1094.c uses the digit-domination form; here the carries are counted from the addition.)
 *
 * Prints "n k lpf" for every pair with lpf > max(n/k, 13), then a line
 * "#BRUTE nmax=.. B=.. pairs=.. lpf_gt_13=.. records=..".
 *
 * Build: gcc -O3 -o brute brute_1094.c      Usage: brute NMAX B
 */
#include <stdio.h>
#include <stdlib.h>

static int has_carry(unsigned long long x, unsigned long long y, unsigned p) {
    unsigned c = 0;                       /* add x + y in base p */
    while (x || y) {
        unsigned s = (unsigned)(x % p) + (unsigned)(y % p) + c;
        c = s >= p;
        if (c) return 1;
        x /= p; y /= p;
    }
    return 0;
}

/* Window mode, for spot checks at sizes the double loop cannot reach:
 *     brute window NLO NHI B
 * For every n in [NLO, NHI] run through the k whose binary digits are dominated by those of n
 * (k & ~n == 0; all other k give an even C(n,k)), from the largest one <= n/2 downwards to n/B,
 * and test the primes 2, 3, 5, ... < 1000 with has_carry.  Same output format as the main mode;
 * lpf is printed as 0 if no prime below 1000 divides. */
static int window(unsigned long long nlo, unsigned long long nhi, unsigned long long B) {
    static unsigned primes[200]; int np = 0;
    for (unsigned q = 2; q < 1000; q++) {
        int ok = 1;
        for (unsigned d = 2; d * d <= q; d++) if (q % d == 0) { ok = 0; break; }
        if (ok) primes[np++] = q;
    }
    unsigned long long tested = 0, records = 0;
    for (unsigned long long n = nlo; n <= nhi; n++) {
        if (n < 4) continue;
        unsigned long long top = 1;
        while (top <= n / 2) top <<= 1;              /* highest set bit of n */
        for (unsigned long long k = n ^ top; k >= 2; k = (k - 1) & n) {
            if (B && n > B * k) break;               /* k only decreases from here on */
            if (2 * k > n) continue;
            tested++;
            unsigned lpf = 0;
            /* p = 2 is skipped: k & ~n == 0 means k and n-k have no common binary digit, so the
             * addition has no carry (this alone takes most of the time otherwise) */
            for (int i = 1; i < np; i++)
                if (has_carry(k, n - k, primes[i])) { lpf = primes[i]; break; }
            if (lpf == 0 || (lpf > 13 && (unsigned long long)lpf * k > n)) {
                records++;
                printf("%llu %llu %u\n", n, k, lpf);
            }
        }
    }
    printf("#WINDOW nlo=%llu nhi=%llu B=%llu submasks_tested=%llu records=%llu\n", nlo, nhi, B, tested, records);
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 5 && argv[1][0] == 'w')
        return window(strtoull(argv[2], 0, 10), strtoull(argv[3], 0, 10), strtoull(argv[4], 0, 10));
    if (argc < 3) { fprintf(stderr, "usage: %s NMAX B\n       %s window NLO NHI B\n", argv[0], argv[0]); return 2; }
    unsigned long long nmax = strtoull(argv[1], 0, 10), B = strtoull(argv[2], 0, 10);
    /* all primes up to max(nmax, 100): C(n,k) > 1 always has a prime factor <= n */
    unsigned long long lim = nmax < 100 ? 100 : nmax;
    char *comp = calloc(lim + 1, 1);
    unsigned *primes = malloc((lim + 1) * sizeof(unsigned));
    int np = 0;
    for (unsigned long long q = 2; q <= lim; q++) {
        if (comp[q]) continue;
        primes[np++] = (unsigned)q;
        for (unsigned long long m = q * q; m <= lim; m += q) comp[m] = 1;
    }
    unsigned long long pairs = 0, gt13 = 0, records = 0;
    for (unsigned long long n = 4; n <= nmax; n++) {
        for (unsigned long long k = 2; 2 * k <= n; k++) {
            if (B && n > B * k) continue;
            pairs++;
            unsigned lpf = 0;
            for (int i = 0; i < np; i++)
                if (has_carry(k, n - k, primes[i])) { lpf = primes[i]; break; }
            if (!lpf) { fprintf(stderr, "no prime factor found for %llu %llu\n", n, k); return 3; }
            if (lpf > 13) {
                gt13++;
                if ((unsigned long long)lpf * k > n) { records++; printf("%llu %llu %u\n", n, k, lpf); }
            }
        }
    }
    printf("#BRUTE nmax=%llu B=%llu pairs=%llu lpf_gt_13=%llu records=%llu\n", nmax, B, pairs, gt13, records);
    return 0;
}
