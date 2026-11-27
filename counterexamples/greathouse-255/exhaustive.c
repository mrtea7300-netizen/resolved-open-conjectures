/*
 * exhaustive.c -- ALL odd n in [FROM, TO) that are not of the form p + 2^a + 2^b
 *                 (p prime, a, b >= 1).  No residue-class restriction.  (OEIS A156695)
 *
 *   gcc -O3 -march=native -fopenmp -o exhaustive.exe exhaustive.c
 *   exhaustive.exe FROM TO THREADS [CKPT]          (TO <= 10^15)
 *
 * Method.  Odd numbers are indexed by j (number 2j+1).  A segmented sieve of Eratosthenes gives
 * the bit array P (P[j] = 1 iff 2j+1 is prime).  For every pair 1 <= a <= b <= KB the array
 * P shifted by (2^a + 2^b)/2 positions is OR-ed into a cover array C (pairs with b <= K1 by
 * whole-array shifts, pairs with K1 < b <= KB by single bit look-ups for the n still uncovered),
 * so C[j] = 1 iff n = 2j+1 has a representation with b <= KB.  Every n with C[j] = 0 is then tested directly
 * against all pairs (a, b) with a deterministic 64-bit Miller-Rabin test; if no pair gives a
 * prime it is printed as "HIT n".
 * Work is cut into chunks of CHUNK_BLOCKS blocks of 2^22 odd numbers; a checkpoint (number of
 * finished batches) is written after every batch of chunks.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
#define KB 20
#define BLKBITS 22
#define BLK ((u64)1 << BLKBITS)
#define BW (BLK / 64)
#define CHUNK_BLOCKS 256
#define BATCH 1024
#define MAXB 62

static uint32_t *bp; static int nbp;      /* odd base primes */
#define K1 14
#define TILE 2048
static int nsh, nsh1; static u64 sh[KB * (KB + 1) / 2];
static u64 psum[MAXB * (MAXB + 1) / 2]; static int npair;

static inline u64 mont_inv(u64 n) { u64 x = n; for (int i = 0; i < 5; i++) x *= 2 - n * x; return x; }
static inline u64 mont_mul(u64 a, u64 b, u64 n, u64 ninv) { u128 t = (u128)a * b; u64 m = (u64)t * ninv; u64 hi = (u64)(t >> 64), mh = (u64)(((u128)m * n) >> 64); return hi >= mh ? hi - mh : hi - mh + n; }
static int sprp(u64 n, u64 base) {
    u64 ninv = mont_inv(n), one = (u64)(((u128)1 << 64) % n), r2 = (u64)(((u128)one * one) % n), mone = n - one;
    base %= n; if (base == 0) return 1;
    u64 x = mont_mul(base, r2, n, ninv), d = n - 1; int s = __builtin_ctzll(d); d >>= s; u64 y = one;
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
static int has_rep(u64 n) { for (int i = npair - 1; i >= 0; i--) { if (psum[i] + 2 > n) continue; if (is_prime64(n - psum[i])) return 1; } return 0; }

/* sieve odd indices [j0, j0+BLK) into comp (1 = composite or 1); nxt[] holds offsets */
static int nsmall;                         /* base primes below SUB: sieved per sub-block */
#define SUBBITS 18
#define SUB ((uint32_t)1 << SUBBITS)
/* primes 3..61 are pre-sieved with periodic bit patterns (7 groups), the rest by loops */
#define NPAT 7
#define NPRE 17
static const int patp[NPAT][5] = {{3, 5, 7, 11, 13}, {17, 19, 23, 0, 0}, {29, 31, 0, 0, 0}, {37, 41, 0, 0, 0}, {43, 47, 0, 0, 0}, {53, 59, 0, 0, 0}, {61, 0, 0, 0, 0}};
static u64 *pat[NPAT]; static u64 patL[NPAT], patinv[NPAT];
static void init_patterns(void) {
    for (int g = 0; g < NPAT; g++) { u64 L = 1; for (int k = 0; k < 5 && patp[g][k]; k++) L *= patp[g][k];
        patL[g] = L; pat[g] = calloc(L, 8);
        for (u64 t = 0; t < 64 * L; t++) { u64 v = 2 * (t % L) + 1; for (int k = 0; k < 5 && patp[g][k]; k++) if (v % patp[g][k] == 0) { pat[g][t >> 6] |= (u64)1 << (t & 63); break; } }
        u64 inv = 1; while ((64 * inv) % L != 1) inv++; patinv[g] = inv; }
}
static void sieve_block(u64 *comp, uint32_t *nxt, u64 j0) {
    for (int g = 0; g < NPAT; g++) { u64 L = patL[g], u = (j0 % L) * patinv[g] % L; const u64 *p = pat[g];
        u64 w = 0;
        while (w < BW) { u64 len = L - u < BW - w ? L - u : BW - w;
            if (g == 0) memcpy(comp + w, p + u, len * 8); else for (u64 i = 0; i < len; i++) comp[w + i] |= p[u + i];
            w += len; u = 0; } }
    for (u64 sb = 0; sb < BLK / SUB; sb++) { u64 *c = comp + sb * (SUB / 64);
        for (int i = NPRE; i < nsmall; i++) { uint32_t p = bp[i], o = nxt[i];
            while (o < SUB) { c[o >> 6] |= (u64)1 << (o & 63); o += p; }
            nxt[i] = o - SUB; } }
    for (int i = nsmall; i < nbp; i++) {
        uint32_t p = bp[i], o = nxt[i];
        if (o < BLK) { do { comp[o >> 6] |= (u64)1 << (o & 63); o += p; } while (o < BLK); }
        nxt[i] = o - (uint32_t)BLK;
    }
    if (j0 == 0) { comp[0] |= 1; for (int i = 0; i < NPRE; i++) { u64 j = (bp[i] - 1) / 2; comp[j >> 6] &= ~((u64)1 << (j & 63)); } }
}
static void init_next(uint32_t *nxt, u64 j0) { /* first index >= j0 of an odd multiple of p that is >= p*p */
    u64 lo = 2 * j0 + 1;
    for (int i = 0; i < nbp; i++) { u64 p = bp[i], m = p * p;
        if (m < lo) { m = (lo + p - 1) / p * p; if (!(m & 1)) m += p; }
        u64 o = (m - 1) / 2 - j0; nxt[i] = o > 0xF0000000u ? 0xF0000000u : (uint32_t)o; }
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: exhaustive FROM TO THREADS [CKPT]\n"); return 2; }
    u64 FROM = strtoull(argv[1], 0, 10), TO = strtoull(argv[2], 0, 10); int th = atoi(argv[3]); const char *ckpt = argc > 4 ? argv[4] : NULL;
    if (TO > 1000000000000000ULL) { fprintf(stderr, "TO <= 10^15\n"); return 2; }
    { int k = 0; for (int a = 1; a <= MAXB; a++) for (int b = a; b <= MAXB; b++) psum[k++] = ((u64)1 << a) + ((u64)1 << b); npair = k; }
    nsh = 0; for (int b = 1; b <= KB; b++) { for (int a = 1; a <= b; a++) sh[nsh++] = (((u64)1 << a) + ((u64)1 << b)) / 2; if (b == K1) nsh1 = nsh; }
    { /* base primes up to 31622777 */
        uint32_t lim = 31622777; char *c = calloc(lim / 2 + 1, 1); bp = malloc(sizeof(uint32_t) * 2000000); nbp = 0;
        for (u64 i = 1; 2 * i + 1 <= lim; i++) if (!c[i]) { u64 p = 2 * i + 1; bp[nbp++] = (uint32_t)p; for (u64 m = p * p; m <= lim; m += 2 * p) c[(m - 1) / 2] = 1; }
        free(c); }
    init_patterns();
    nsmall = 0; while (nsmall < nbp && bp[nsmall] < SUB) nsmall++;
    u64 j_from = FROM / 2, j_to = TO / 2;            /* odd n = 2j+1 in [FROM,TO)  <=>  j in [FROM/2, TO/2) */
    u64 CH = (u64)CHUNK_BLOCKS * BLK;
    u64 c0 = j_from / CH, c1 = (j_to + CH - 1) / CH;
    u64 bstart = 0;
    if (ckpt) { FILE *f = fopen(ckpt, "r"); if (f) { unsigned long long v; if (fscanf(f, "%llu", &v) == 1) bstart = v; fclose(f); } }
    fprintf(stderr, "base primes %d, shifts %d, chunks [%llu,%llu), chunk = %llu odd numbers, start batch %llu, threads %d\n", nbp, nsh,
            (unsigned long long)c0, (unsigned long long)c1, (unsigned long long)CH, (unsigned long long)bstart, th);
    omp_set_num_threads(th); double t0 = omp_get_wtime(); u64 hits = 0, surv = 0;
    for (u64 bat = bstart; c0 + bat * BATCH < c1; bat++) {
        u64 ca = c0 + bat * BATCH, cb = ca + BATCH < c1 ? ca + BATCH : c1;
        #pragma omp parallel reduction(+ : hits, surv)
        {
            uint32_t *nxt = malloc(sizeof(uint32_t) * nbp);
            u64 *pr = malloc(2 * BW * 8), *cv = malloc(BW * 8), *comp = malloc(BW * 8);
            #pragma omp for schedule(dynamic, 1)
            for (long long ci = (long long)ca; ci < (long long)cb; ci++) {
                u64 jc = (u64)ci * CH;
                /* previous block (history for the shifts) */
                if (jc >= BLK) { init_next(nxt, jc - BLK); sieve_block(comp, nxt, jc - BLK); for (u64 w = 0; w < BW; w++) pr[w] = ~comp[w]; }
                else { memset(pr, 0, BW * 8); init_next(nxt, jc); }
                for (int blk = 0; blk < CHUNK_BLOCKS; blk++) {
                    u64 j0 = jc + (u64)blk * BLK;
                    if (j0 >= j_to) break;
                    sieve_block(comp, nxt, j0);
                    u64 *cur = pr + BW; for (u64 w = 0; w < BW; w++) cur[w] = ~comp[w];
                    memset(cv, 0, BW * 8);
                    /* stage 1: shifts with b <= K1, tile by tile (everything stays in L1) */
                    for (u64 t = 0; t < BW; t += TILE) {
                        for (int s = 0; s < nsh1; s++) { u64 w = sh[s] >> 6; int r = (int)(sh[s] & 63);
                            const u64 *src = cur - w;
                            if (r == 0) for (u64 i = t; i < t + TILE; i++) cv[i] |= src[i];
                            else for (u64 i = t; i < t + TILE; i++) cv[i] |= (src[i] << r) | (src[i - 1] >> (64 - r)); } }
                    /* stage 2: the remaining shifts, only for n still uncovered; then the exact test */
                    for (u64 w = 0; w < BW; w++) { u64 x = ~cv[w];
                        while (x) { int b = __builtin_ctzll(x); x &= x - 1; u64 q = BLK + w * 64 + b; int cov = 0;
                            for (int s = nsh1; s < nsh; s++) { u64 qq = q - sh[s]; if ((pr[qq >> 6] >> (qq & 63)) & 1) { cov = 1; break; } }
                            if (cov) continue;
                            u64 j = j0 + w * 64 + b;
                            if (j < j_from || j >= j_to) continue;
                            u64 n = 2 * j + 1; surv++;
                            if (!has_rep(n)) { hits++;
                                #pragma omp critical
                                { printf("HIT %llu  mod3=%d mod5=%d mod17=%d mod255=%d\n", (unsigned long long)n, (int)(n % 3), (int)(n % 5), (int)(n % 17), (int)(n % 255)); fflush(stdout); } } } }
                    memcpy(pr, cur, BW * 8);
                }
            }
            free(nxt); free(pr); free(cv); free(comp);
        }
        u64 jl = cb * CH < j_to ? cb * CH : j_to;
        fprintf(stderr, "done n < %llu (%.4e)  survivors of the b<=%d cover %llu  hits %llu  %.0f s\n", (unsigned long long)(2 * jl), (double)(2 * jl), KB, (unsigned long long)surv, (unsigned long long)hits, omp_get_wtime() - t0);
        if (ckpt) { FILE *f = fopen(ckpt, "w"); if (f) { fprintf(f, "%llu\n", (unsigned long long)(bat + 1)); fclose(f); } }
    }
    printf("FINISHED [%llu,%llu): hits %llu\n", (unsigned long long)FROM, (unsigned long long)TO, (unsigned long long)hits);
    return 0;
}
