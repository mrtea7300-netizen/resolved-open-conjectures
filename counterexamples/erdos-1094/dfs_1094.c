/* dfs_1094.c -- box-tree search for binomial coefficients with a large least prime factor.
 *
 * Finds every pair (n, k) with
 *        KMIN <= k,  2k <= n,  NLO <= n <= NHI,  n <= B*k   (B = 0 means no ratio limit)
 * and    lpf(C(n,k)) > max(n/k, 13),
 * where lpf is the least prime factor.
 *
 * Fact used (Kummer / Lucas): a prime p does not divide C(n,k) iff every base-p digit of k
 * is <= the corresponding base-p digit of n ("k is dominated by n in base p").
 *
 * Search: a tree of boxes  n in [n0, n0+2^a),  k in [k0, k0+2^b)  with n0 = 0 mod 2^a and
 * k0 = 0 mod 2^b.  The longer side is halved; a leaf is a single pair.
 *
 * Pruning of a box (all tests are one-sided: a box is dropped only if NO pair in it can qualify):
 *   region : every pair of the box violates one of the region inequalities;
 *   prime p: p is "forced" on the box if p <= 13, or p*k1 <= n0 (k1 = largest k, n0 = smallest n
 *            of the box; then p <= n/k for every pair, so a qualifying pair needs p not dividing
 *            C(n,k)).  For a forced p let j be the least exponent with
 *            floor(n0/p^j) = floor(n1/p^j) and floor(k0/p^j) = floor(k1/p^j)   (n1, k1 = last
 *            elements).  x -> floor(x/p^j) is monotone, so every n in the box has the same digits
 *            at positions >= j as n0, and likewise k.  If one of these fixed digits of k exceeds
 *            the digit of n, p divides C(n,k) for every pair of the box: drop it.
 *            The exponent j only decreases from a box to its sub-boxes, so each node only looks
 *            at the newly fixed digits (state j[] passed down the recursion).
 *
 * Leaf: lpf(C(n,k)) is computed from scratch by exact_lpf() (plain digit loop, shares nothing
 * with the incremental pruning state) and the pair is printed iff lpf >= 17 and lpf*k > n.
 * (Primes are sieved up to SIEVE_LIM = 2*10^6, enough to decide every leaf when B <= 2*10^6.)
 * The leaf also re-checks with the same plain loop that every prime the tree claims to have
 * enforced really does not divide C(n,k); a failure aborts the run.
 *
 * Build:  gcc -O3 -o dfs64  dfs_1094.c          (64-bit;  needs NHI < 2^63)
 *         gcc -O3 -DWIDE -o dfs128 dfs_1094.c   (128-bit; needs NHI < 2^127)
 * No product that could overflow is formed: ratio tests are written with divisions.
 *
 * Usage:  dfs search NLO NHI B [--fixedS] [--pmax P] [--kmin K]
 *         dfs selftest SEED COUNT
 * Output: one line "n k lpf" per pair found, then "#..." statistics lines, last line "#DONE ...".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef WIDE
typedef unsigned __int128 U;
#define WBITS 128
#else
typedef unsigned long long U;
#define WBITS 64
#endif
typedef unsigned long long u64;

#define MAXNPR 256      /* max number of pruning primes */
#define MAXJ 130        /* max number of base-p digits */
#define SIEVE_LIM 2000000

static int nall;                 /* all primes below SIEVE_LIM (for exact lpf) */
static unsigned allp[150000];
static int npr;                  /* pruning primes: allp[0..npr) */
static U ppow[MAXNPR][MAXJ];     /* ppow[i][j] = p_i^j for j < Jtop[i] */
static unsigned char Jtop[MAXNPR]; /* least J with p^J >= 2^A: digits at positions >= J are 0 */
static unsigned char enforce[MAXNPR]; /* test hook: 1 = prime may be used for pruning */

static int A;                    /* root box: n in [0,2^A), k in [0,2^(A-1)) */
static U NLO, NHI, BR, KMIN = 2;
static int fixedS = 0;           /* 1: force only p <= 13 (no ratio-dependent primes) */

static u64 nodes, leaves, records, region_pruned;
static u64 pruned_by[MAXNPR];
static u64 surv_level[2 * WBITS + 2];   /* surviving boxes by a+b */
static FILE *out;

static void fatal(const char *msg) { fprintf(stderr, "FATAL: %s\n", msg); exit(3); }

static U parseU(const char *s) {
    U x = 0;
    if (!*s) fatal("empty number");
    for (; *s; s++) {
        if (*s < '0' || *s > '9') fatal("bad number (plain decimal expected)");
        U y = x * 10 + (U)(*s - '0');
        if (y / 10 != x) fatal("number too large for this build");
        x = y;
    }
    return x;
}
static void printU(FILE *f, U x) {
    char buf[64]; int i = 63; buf[i] = 0;
    if (!x) buf[--i] = '0';
    while (x) { buf[--i] = (char)('0' + (int)(x % 10)); x /= 10; }
    fputs(buf + i, f);
}
static int bitlen(U x) { int b = 0; while (x) { b++; x >>= 1; } return b; }

/* ---------- exact, state-free arithmetic used at leaves and as test oracle ---------- */
static int divides(U n, U k, unsigned p) {      /* does p divide C(n,k)?  (k <= n) */
    while (k) {
        if (k % p > n % p) return 1;
        n /= p; k /= p;
    }
    return 0;
}
static unsigned exact_lpf(U n, U k) {        /* 0 means: no prime below SIEVE_LIM divides C(n,k) */
    for (int i = 0; i < nall; i++) if (divides(n, k, allp[i])) return allp[i];
    return 0;
}

/* ---------- node test ---------- */
/* returns 0 if the box survives, 1 if dropped by the region, 2+i if dropped by prime index i.
 * jin[0..nain) = fixed-digit exponents inherited from the parent (others are Jtop);
 * jout[0..*naout) = exponents for the children. */
static inline int node_test(U n0, int a, U k0, int b, const unsigned char *jin, int nain,
                            unsigned char *jout, int *naout) {
    U n1 = n0 + (((U)1 << a) - 1), k1 = k0 + (((U)1 << b) - 1);
    if (k1 < KMIN) return 1;
    if (n1 < 2 * k0) return 1;                 /* n < 2k for every pair */
    if (n1 < NLO || n0 > NHI) return 1;
    if (BR && n0 && (n0 - 1) / BR >= k1) return 1;   /* n0 > B*k1: n > B k for every pair */
    int m = a > b ? a : b;
    if (enforce[0] && ((k0 >> m) & ~(n0 >> m))) return 2;   /* p = 2 on the fixed top bits */
    U r = fixedS ? 0 : n0 / k1;                /* every pair of the box has n/k >= r */
    int i;
    for (i = 0; i < npr; i++) {
        unsigned p = allp[i];
        if (p > 13 && (U)p > r) break;
        int jj = i < nain ? jin[i] : Jtop[i];
        if (enforce[i]) {
            while (jj > 0) {
                U pw = ppow[i][jj - 1];
                U qn = n0 / pw;
                if (qn != n1 / pw) break;
                U qk = k0 / pw;
                if (qk != k1 / pw) break;
                if (qk % p > qn % p) return 2 + i;
                jj--;
            }
        }
        jout[i] = (unsigned char)jj;
    }
    *naout = i;
    return 0;
}

static void leaf(U n, U k) {
    /* region, exactly */
    if (k < KMIN || n < 2 * k || n < NLO || n > NHI) return;
    if (BR && (n - 1) / BR >= k) return;       /* n > B k   (n >= 4 here) */
    leaves++;
    /* consistency: every prime the tree enforced at this leaf must not divide C(n,k) */
    for (int i = 0; i < npr; i++) {
        unsigned p = allp[i];
        if (!enforce[i]) continue;
        if (p <= 13 || (!fixedS && k <= n / p))            /* p*k <= n */
            if (divides(n, k, p)) fatal("leaf reached although an enforced prime divides C(n,k)");
    }
    unsigned l = exact_lpf(n, k);
    /* l == 0: lpf > SIEVE_LIM.  That decides the question only if n/k < SIEVE_LIM; the pair is
     * then printed with lpf 0 ("above the sieve limit").  It never happened in any run. */
    if (l == 0 && n / k >= SIEVE_LIM) fatal("cannot decide a leaf: n/k above the sieve limit");
    if (l == 0 || (l >= 17 && k > n / l)) {    /* lpf > 13 and lpf*k > n, i.e. lpf > n/k */
        records++;
        printU(out, n); fputc(' ', out); printU(out, k); fprintf(out, " %u\n", l);
    }
}

static void dfs(U n0, int a, U k0, int b, const unsigned char *jin, int nain) {
    unsigned char j[MAXNPR];
    int na;
    nodes++;
    int res = node_test(n0, a, k0, b, jin, nain, j, &na);
    if (res) {
        if (res == 1) region_pruned++; else pruned_by[res - 2]++;
        return;
    }
    surv_level[a + b]++;
    if (a == 0 && b == 0) { leaf(n0, k0); return; }
    if (a >= b) {
        dfs(n0, a - 1, k0, b, j, na);
        dfs(n0 + ((U)1 << (a - 1)), a - 1, k0, b, j, na);
    } else {
        dfs(n0, a, k0, b - 1, j, na);
        dfs(n0, a, k0 + ((U)1 << (b - 1)), b - 1, j, na);
    }
}

/* ---------- setup ---------- */
static void sieve(void) {
    static char comp[SIEVE_LIM];
    for (int i = 2; i < SIEVE_LIM; i++) {
        if (!comp[i]) {
            allp[nall++] = (unsigned)i;
            for (long long q = (long long)i * i; q < SIEVE_LIM; q += i) comp[q] = 1;
        }
    }
}
static void setup(U nhi, U b, unsigned pmax) {
    A = bitlen(nhi);                      /* 2^A > nhi */
    if (A < 2) A = 2;
    (void)b;
    if (A > WBITS - 1) fatal("NHI too large for this build (use -DWIDE)");
    npr = 0;
    while (npr < nall && allp[npr] <= pmax) npr++;
    if (npr > MAXNPR) fatal("too many pruning primes");
    U top = (U)1 << A;
    for (int i = 0; i < npr; i++) {
        U pw = 1; int j = 0;
        while (pw < top) {                /* store p^j while p^j < 2^A */
            if (j >= MAXJ) fatal("MAXJ too small");
            ppow[i][j++] = pw;
            if (pw > (top - 1) / allp[i]) break;   /* next power would be >= 2^A */
            pw *= allp[i];
        }
        Jtop[i] = (unsigned char)j;
        enforce[i] = 1;
    }
}

/* ---------- self test: the tree path of a pair ---------- */
static u64 rs[2];
static u64 rnd(void) {                    /* xorshift128+ */
    u64 x = rs[0], y = rs[1];
    rs[0] = y; x ^= x << 23;
    rs[1] = x ^ y ^ (x >> 17) ^ (y >> 26);
    return rs[1] + y;
}
static U rndU(void) {
#ifdef WIDE
    return ((U)rnd() << 64) | rnd();
#else
    return rnd();
#endif
}
/* walk the root-to-leaf path of (n,k); return 0 if the leaf is reached, else the node_test code */
static int walk(U n, U k) {
    unsigned char ja[MAXNPR], jb[MAXNPR];
    unsigned char *jin = ja, *jout = jb;
    int nain = 0, na;
    U n0 = 0, k0 = 0;
    int a = A, b = A - 1;
    for (;;) {
        int res = node_test(n0, a, k0, b, jin, nain, jout, &na);
        if (res) return res;
        if (a == 0 && b == 0) return 0;
        if (a >= b) { a--; if ((n >> a) & 1) n0 += (U)1 << a; }
        else        { b--; if ((k >> b) & 1) k0 += (U)1 << b; }
        unsigned char *t = jin; jin = jout; jout = t; nain = na;
    }
}
/* k with every base-p digit <= the digit of n, uniformly at random */
static U dominated(U n, unsigned p) {
    U k = 0, pw = 1;
    while (n) {
        unsigned d = (unsigned)(n % p);
        k += pw * (U)(rnd() % (d + 1));
        n /= p;
        if (n) pw *= p;
    }
    return k;
}
static int selftest(u64 seed, u64 count) {
    rs[0] = seed * 0x9E3779B97F4A7C15ULL + 1; rs[1] = seed ^ 0xD1B54A32D192ED03ULL;
    for (int i = 0; i < 20; i++) rnd();
    int maxbits = WBITS - 2;                     /* scales up to 2^62 (2^126 in the wide build) */
    u64 t1 = 0, t1free = 0, t1div = 0, t1inactive = 0, t2 = 0, t3 = 0, skipped = 0;
    /* Test 1: single prime, exact equivalence  "path survives  <=>  p not dividing C(n,k)
     * (or p never forced at the leaf)".  Test 2: random set of primes, pair free of all of them
     * must survive.  Test 3: the same with the ratio limit B = 64 in force. */
    for (u64 it = 0; it < count; it++) {
        int bits = 6 + (int)(rnd() % (unsigned)(maxbits - 5));     /* 6..maxbits */
        U nhi = ((U)1 << bits) - 1;
        int mode = (int)(rnd() % 4);
        BR = (mode == 3) ? 64 : 0; NLO = 0; NHI = nhi; KMIN = 2;
        fixedS = (rnd() % 8 == 0);
        unsigned pmax = 13 + (unsigned)(rnd() % 90);
        setup(nhi, BR ? BR : 1, pmax);
        int pi = (int)(rnd() % (unsigned)npr);
        unsigned p = allp[pi];
        U n = rndU() & nhi;
        if (rnd() % 4 == 0 && bits > 8) {        /* sometimes n close to a power of p */
            U pw = 1; while (pw <= n / p) pw *= p;
            U m = (n / pw) * pw;
            U d = rnd() % 5;
            n = (rnd() & 1) ? m + d : (m > d ? m - 1 - d : m);
            n &= nhi;
        }
        U k;
        int how = (int)(rnd() % 3);
        if (how == 0) k = dominated(n, p);
        else if (how == 1) { int kb = 2 + (int)(rnd() % (unsigned)(bits - 1)); k = rndU() & (((U)1 << kb) - 1); }
        else { int kb = 2 + (int)(rnd() % (unsigned)(bits - 1)); k = dominated(n, p) & (((U)1 << kb) - 1); }
        if (k < 2 || n < 2 * k || (BR && (n - 1) / BR >= k)) { skipped++; continue; }
        if (mode <= 1) {
            for (int i = 0; i < npr; i++) enforce[i] = 0;
            enforce[pi] = 1;
            int res = walk(n, k);
            int d = divides(n, k, p);
            int forced_at_leaf = (p <= 13) || (!fixedS && k <= n / p);
            int expect_survive = !(d && forced_at_leaf);
            if (res == 1) { fprintf(stderr, "selftest: region prune hit an in-region pair\n"); return 1; }
            if ((res == 0) != expect_survive) {
                fprintf(stderr, "selftest FAIL (single prime %u): n=", p); printU(stderr, n);
                fprintf(stderr, " k="); printU(stderr, k);
                fprintf(stderr, " res=%d divides=%d forced=%d fixedS=%d\n", res, d, forced_at_leaf, fixedS);
                return 1;
            }
            t1++;
            if (!d) t1free++; else if (forced_at_leaf) t1div++; else t1inactive++;
        } else {
            /* random subset of primes; keep the pair only if it is free of all of them */
            int ok = 1;
            for (int i = 0; i < npr; i++) {
                enforce[i] = (i == pi) || (rnd() % 6 == 0);
                if (enforce[i] && divides(n, k, allp[i])) ok = 0;
            }
            if (!ok) {   /* fall back to the single prime, which is free when how == 0 or 2 */
                for (int i = 0; i < npr; i++) enforce[i] = (i == pi);
                if (divides(n, k, p)) { skipped++; continue; }
            }
            int res = walk(n, k);
            if (res) {
                fprintf(stderr, "selftest FAIL (free pair pruned, code %d): n=", res); printU(stderr, n);
                fprintf(stderr, " k="); printU(stderr, k); fprintf(stderr, " B=%d\n", (int)BR);
                return 1;
            }
            if (mode == 2) t2++; else t3++;
        }
    }
    printf("selftest OK (%d-bit build, scales 2^6..2^%d): single-prime exact tests %llu "
           "(free %llu, dividing and forced %llu, dividing but not forced %llu); "
           "free pairs with random prime sets %llu; same with B=64 %llu; samples outside region %llu\n",
           WBITS, maxbits, t1, t1free, t1div, t1inactive, t2, t3, skipped);
    return 0;
}

int main(int argc, char **argv) {
    sieve();
    out = stdout;
    if (argc >= 4 && !strcmp(argv[1], "selftest"))
        return selftest(strtoull(argv[2], 0, 10), strtoull(argv[3], 0, 10));
    if (argc < 5 || strcmp(argv[1], "search")) {
        fprintf(stderr, "usage: %s search NLO NHI B [--fixedS] [--pmax P] [--kmin K]\n"
                        "       %s selftest SEED COUNT\n", argv[0], argv[0]);
        return 2;
    }
    NLO = parseU(argv[2]); NHI = parseU(argv[3]); BR = parseU(argv[4]);
    long pmax = -1;
    for (int i = 5; i < argc; i++) {
        if (!strcmp(argv[i], "--fixedS")) fixedS = 1;
        else if (!strcmp(argv[i], "--pmax") && i + 1 < argc) pmax = atol(argv[++i]);
        else if (!strcmp(argv[i], "--kmin") && i + 1 < argc) KMIN = parseU(argv[++i]);
        else fatal("unknown option");
    }
    if (KMIN < 2) KMIN = 2;
    if (pmax < 0) pmax = (BR && BR < 1500) ? (long)BR : 1500;   /* primes above pmax are only tested at leaves */
    if (pmax < 13) pmax = 13;
    if (fixedS) pmax = 13;
    setup(NHI, BR ? BR : 1, (unsigned)pmax);
    clock_t t0 = clock();
    dfs(0, A, 0, A - 1, 0, 0);
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    for (int d = 2 * A; d >= 0; d--)
        if (surv_level[d]) printf("#LEVEL %d %llu\n", d, surv_level[d]);
    printf("#PRUNE region %llu\n", region_pruned);
    for (int i = 0; i < npr; i++) if (pruned_by[i]) printf("#PRUNE %u %llu\n", allp[i], pruned_by[i]);
    printf("#DONE nlo="); printU(stdout, NLO); printf(" nhi="); printU(stdout, NHI);
    printf(" B="); printU(stdout, BR);
    printf(" kmin="); printU(stdout, KMIN);
    printf(" fixedS=%d pmax=%ld bits=%d nodes=%llu leaves=%llu records=%llu secs=%.2f\n",
           fixedS, pmax, WBITS, nodes, leaves, records, secs);
    return 0;
}
