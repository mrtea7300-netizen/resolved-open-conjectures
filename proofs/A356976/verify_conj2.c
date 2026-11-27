/*
 * Finite verification for A356976 Conjecture 2:
 *   For every positive integer n, the least positive integer m such that
 *   f(k) = 2*k^3 + k (k = 1..n) are pairwise distinct modulo m is 2^ceil(log2(n)).
 *
 * This program performs the three finite checks required by proof.md:
 *   (1) Conic Box Lemma for all primes 17 <= p <= P_LIMIT (default 100000):
 *       for every c in {1, ..., p-1}, there exist 1 <= u < v <= (p-1)/2 with
 *       u^2 + u*v + v^2 == c (mod p) and p nmid (2u+v)(u+2v).
 *   (2) Prime-power base cases q in {5^3, 7^3, 11^2, 13^2}:
 *       for every c in {1, ..., q-1} with gcd(c, p) = 1, there exist
 *       1 <= u < v <= (q-1)/2 with u^2 + u*v + v^2 == c (mod q) and p nmid (2u+v)(u+2v).
 *   (3) Remaining 245 smooth moduli m = 2^a * s with 0 <= a <= 6 and
 *       s | (5^2 * 7^2 * 11 * 13), s > 1:
 *       there exist 1 <= x < y <= 2^floor(log2(m)) + 1 with 2x^3+x == 2y^3+y (mod m).
 *
 * Compile: gcc -O3 -march=native -fopenmp verify_conj2.c -o verify_conj2 -lm
 * Run:     ./verify_conj2
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef uint64_t u64;

static int is_prime_u64(u64 n) {
    if (n < 2) return 0;
    if (n % 2 == 0) return n == 2;
    for (u64 d = 3; d * d <= n; d += 2) {
        if (n % d == 0) return 0;
    }
    return 1;
}

static int check_prime_box(int p) {
    int half = (p - 1) / 2;
    uint8_t *seen = calloc(p, 1);
    int covered = 0;
    for (int u = 1; u <= half && covered < p - 1; u++) {
        u64 u2 = (u64)u * u;
        for (int v = u + 1; v <= half; v++) {
            if ((2 * u + v) % p == 0 || (u + 2 * v) % p == 0) continue;
            int r = (int)((u2 + (u64)u * v + (u64)v * v) % (u64)p);
            if (r != 0 && !seen[r]) {
                seen[r] = 1;
                covered++;
                if (covered == p - 1) break;
            }
        }
    }
    free(seen);
    return covered == p - 1;
}

static int check_prime_power_box(int p, int e) {
    int q = 1;
    for (int i = 0; i < e; i++) q *= p;
    int half = (q - 1) / 2;
    uint8_t *seen = calloc(q, 1);
    int need = q - q / p;
    int covered = 0;
    for (int u = 1; u <= half && covered < need; u++) {
        u64 u2 = (u64)u * u;
        for (int v = u + 1; v <= half; v++) {
            if ((2 * u + v) % p == 0 || (u + 2 * v) % p == 0) continue;
            int r = (int)((u2 + (u64)u * v + (u64)v * v) % (u64)q);
            if (r % p != 0 && !seen[r]) {
                seen[r] = 1;
                covered++;
                if (covered == need) break;
            }
        }
    }
    free(seen);
    return covered == need;
}

static int check_small_modulus(u64 m) {
    // Find 2^r < m < 2^(r+1)
    u64 pow2 = 1;
    while (pow2 * 2 <= m) pow2 *= 2;
    u64 limit = pow2 + 1;

    // Hash table or direct array since m <= 64 * 175175 = 11,211,200
    // limit <= 8,388,609; allocate int array of size m? m <= 11.2M -> 44 MB, totally fine!
    // Even smaller: use uint32_t array of size m initialized to 0.
    uint32_t *first = calloc(m, sizeof(uint32_t));
    if (!first) { fprintf(stderr, "OOM for m=%llu\n", (unsigned long long)m); exit(1); }
    int ok = 0;
    for (u64 k = 1; k <= limit; k++) {
        u64 k2 = (k * k) % m;
        u64 k3 = (k2 * k) % m;
        u64 val = (2 * k3 + k) % m;
        if (first[val] != 0) {
            ok = 1;
            break;
        }
        first[val] = (uint32_t)k;
    }
    free(first);
    return ok;
}

int main(int argc, char **argv) {
    int P_LIMIT = 100000;
    if (argc > 1) P_LIMIT = atoi(argv[1]);

    // (1) Conic Box Lemma for all primes 17 <= p <= P_LIMIT
    int *plist = malloc((P_LIMIT / 2 + 10) * sizeof(int));
    int np = 0;
    for (int p = 17; p <= P_LIMIT; p += 2) {
        if (is_prime_u64(p)) plist[np++] = p;
    }
    int fail_primes = 0;
    #pragma omp parallel for schedule(dynamic, 16) reduction(+:fail_primes)
    for (int i = 0; i < np; i++) {
        if (!check_prime_box(plist[i])) {
            #pragma omp critical
            printf("FAIL Conic Box Lemma at p = %d\n", plist[i]);
            fail_primes++;
        }
    }
    printf("[Check 1] Conic Box Lemma for all %d primes in [17, %d]: %s (failures=%d)\n",
           np, P_LIMIT, fail_primes == 0 ? "PASS" : "FAIL", fail_primes);
    free(plist);

    // (2) Prime-power base cases
    int bases[4][2] = {{5, 3}, {7, 3}, {11, 2}, {13, 2}};
    int fail_bases = 0;
    for (int i = 0; i < 4; i++) {
        int ok = check_prime_power_box(bases[i][0], bases[i][1]);
        printf("[Check 2] Base case %d^%d: %s\n", bases[i][0], bases[i][1], ok ? "PASS" : "FAIL");
        if (!ok) fail_bases++;
    }

    // (3) Remaining 245 smooth moduli m = 2^a * 5^c * 7^d * 11^e * 13^f
    // with 0 <= a <= 6, c in {0,1,2}, d in {0,1,2}, e in {0,1}, f in {0,1}, (c,d,e,f) != (0,0,0,0)
    int total_smooth = 0, fail_smooth = 0;
    for (int a = 0; a <= 6; a++) {
        u64 p2 = 1ULL << a;
        for (int c = 0; c <= 2; c++) {
            u64 p5 = (c == 0) ? 1 : (c == 1 ? 5 : 25);
            for (int d = 0; d <= 2; d++) {
                u64 p7 = (d == 0) ? 1 : (d == 1 ? 7 : 49);
                for (int e = 0; e <= 1; e++) {
                    u64 p11 = e ? 11 : 1;
                    for (int f = 0; f <= 1; f++) {
                        u64 p13 = f ? 13 : 1;
                        if (c == 0 && d == 0 && e == 0 && f == 0) continue;
                        u64 m = p2 * p5 * p7 * p11 * p13;
                        total_smooth++;
                        if (!check_small_modulus(m)) {
                            printf("FAIL smooth modulus m = %llu\n", (unsigned long long)m);
                            fail_smooth++;
                        }
                    }
                }
            }
        }
    }
    printf("[Check 3] All %d remaining smooth moduli (a<=6, s|5^2*7^2*11*13): %s (failures=%d)\n",
           total_smooth, fail_smooth == 0 ? "PASS" : "FAIL", fail_smooth);

    return (fail_primes || fail_bases || fail_smooth) ? 1 : 0;
}
