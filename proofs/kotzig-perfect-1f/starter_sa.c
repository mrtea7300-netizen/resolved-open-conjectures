/*
 * starter_sa.c -- Simulated Annealing / Local Search over starters in any finite
 * group G of odd order n (cyclic Z_n, non-cyclic abelian Z_3 x Z_21, or
 * non-abelian Z_7 : Z_9 and F_21 x Z_3) to search for perfect 1-factorizations
 * of K_{n+1}.
 *
 * State: a partition of G \ {0} into H = (n-1)/2 pairs {a_i, b_i}.
 * Moves:
 *   - 2-opt pair swap: {a_i, b_i}, {a_j, b_j} -> {a_i, a_j}, {b_i, b_j}
 *     (or {a_i, b_j}, {b_i, a_j}).
 * Energy:
 *   E = W_DIFF * diff_excess + cycle_excess
 * where:
 *   diff_excess  = number of inverse pairs {d, d^{-1}} in G\{0} with count != 1
 *                  (0 iff S is a valid right-starter with left differences x*y^{-1}).
 *   cycle_excess = sum over representative d of (num_cycles(F_0 U F_d) - 1)
 *                  (0 iff every pair of factors is a single Hamiltonian cycle).
 *   E == 0 iff S is a valid starter inducing a PERFECT 1-factorization of K_{n+1}!
 *
 * Compile: gcc -O3 -march=native -pthread -lm -o starter_sa starter_sa.c
 * Usage:   ./starter_sa <group_spec> <threads> <seed> <max_seconds> <t_start> <t_end> <steps_per_restart>
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>
#include <time.h>

#define MAXN 128

static int N, H;
static uint8_t mul_tab[MAXN][MAXN]; /* right multiplication: a * b */
static uint8_t inv_arr[MAXN];       /* a^{-1} */
static uint8_t diff_id[MAXN][MAXN]; /* canonical diff index 0..H-1 for {a*b^{-1}, b*a^{-1}} */
static uint8_t d_rep[MAXN];         /* canonical representative d for each inverse pair 0..H-1 */

static volatile int found = 0;
static volatile int time_expired = 0;
static double start_wall = 0.0;
static double max_seconds = 60.0;
static double T_start = 3.0, T_end = 0.08;
static long long steps_per_restart = 2000000;
static uint64_t global_seed = 1;
static pthread_mutex_t out_mtx = PTHREAD_MUTEX_INITIALIZER;

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static inline uint64_t xorshift64(uint64_t *st) {
    uint64_t x = *st;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    *st = x;
    return x;
}

static inline double rand_u01(uint64_t *st) {
    return (xorshift64(st) >> 11) * (1.0 / 9007199254740992.0);
}

/* Compute cycle_excess = sum_{j=0..H-1} (num_cycles(F_0 U F_{d_j}) - 1).
   In F_0: mate0[v] = partner of v (with mate0[0] = N, mate0[N] = 0).
   In F_d: partner of v*d is mate0[v]*d (for v != 0), partner of d is N, partner of N is d.
   Wait: to make F_d = S*d U {d, N} fast, precompute mate_d[x] = mul(mate0[mul(x, inv(d))], d),
   OR even faster: walking alternating edges of F_0 and F_d directly! */
static int compute_cycle_excess(const uint8_t *mate0) {
    int excess = 0;
    int V = N + 1;
    uint8_t mate_d[MAXN + 1];
    uint8_t vis[MAXN + 1];

    for (int j = 0; j < H; j++) {
        uint8_t d = d_rep[j];
        const uint8_t *md_row = mul_tab[d]; /* unused: we need right mult x * d */
        (void)md_row;
        for (int v = 1; v < N; v++) {
            uint8_t vd = mul_tab[v][d];
            uint8_t wd = mul_tab[mate0[v]][d];
            mate_d[vd] = wd;
        }
        mate_d[d] = (uint8_t)N;
        mate_d[N] = d;

        memset(vis, 0, (size_t)V);
        int cycles = 0;
        for (int s = 0; s < V; s++) {
            if (vis[s]) continue;
            cycles++;
            int cur = s;
            do {
                vis[cur] = 1;
                cur = mate0[cur];
                vis[cur] = 1;
                cur = mate_d[cur];
            } while (!vis[cur]);
        }
        excess += (cycles - 1);
    }
    return excess;
}

typedef struct {
    int tid;
    uint64_t rng;
    long long total_steps;
    long long restarts;
    int best_valid_cyc; /* minimum cycle_excess seen among valid starters (diff_excess == 0) */
    int best_energy;
} Worker;

static void *worker_main(void *arg) {
    Worker *w = (Worker *)arg;
    w->best_valid_cyc = 1 << 30;
    w->best_energy = 1 << 30;

    uint8_t pa[MAXN / 2], pb[MAXN / 2];
    uint8_t mate0[MAXN + 1];
    int dcnt[MAXN / 2];
    int W_DIFF = 4;

    while (!found && !time_expired) {
        /* Random initial pairing of 1..N-1 */
        uint8_t perm[MAXN];
        for (int i = 0; i < N - 1; i++) perm[i] = (uint8_t)(i + 1);
        for (int i = N - 2; i > 0; i--) {
            int j = (int)(xorshift64(&w->rng) % (uint64_t)(i + 1));
            uint8_t t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        memset(dcnt, 0, (size_t)H * sizeof(int));
        mate0[0] = (uint8_t)N; mate0[N] = 0;
        for (int i = 0; i < H; i++) {
            pa[i] = perm[2 * i];
            pb[i] = perm[2 * i + 1];
            mate0[pa[i]] = pb[i];
            mate0[pb[i]] = pa[i];
            dcnt[diff_id[pa[i]][pb[i]]]++;
        }
        int diff_ex = 0;
        for (int j = 0; j < H; j++) if (dcnt[j] == 0) diff_ex++;
        int cyc_ex = compute_cycle_excess(mate0);
        int cur_E = W_DIFF * diff_ex + cyc_ex;

        double log_ratio = log(T_end / T_start);
        double inv_steps = 1.0 / (double)steps_per_restart;

        for (long long step = 0; step < steps_per_restart && !found && !time_expired; step++) {
            if ((step & 8191LL) == 0 && (now_sec() - start_wall) >= max_seconds) {
                time_expired = 1;
                break;
            }
            /* Pick two distinct pairs i, j */
            int i = (int)(xorshift64(&w->rng) % (uint64_t)H);
            int j = (int)(xorshift64(&w->rng) % (uint64_t)(H - 1));
            if (j >= i) j++;
            int mode = (int)(xorshift64(&w->rng) & 1ULL);

            uint8_t a1 = pa[i], b1 = pb[i], a2 = pa[j], b2 = pb[j];
            uint8_t na1 = a1, nb1 = mode ? a2 : b2;
            uint8_t na2 = b1, nb2 = mode ? b2 : a2;

            int old_d1 = diff_id[a1][b1], old_d2 = diff_id[a2][b2];
            int new_d1 = diff_id[na1][nb1], new_d2 = diff_id[na2][nb2];

            /* Update diff_ex incrementally */
            int delta_diff = 0;
            dcnt[old_d1]--; if (dcnt[old_d1] == 0) delta_diff++;
            dcnt[old_d2]--; if (dcnt[old_d2] == 0) delta_diff++;
            if (dcnt[new_d1] == 0) delta_diff--; dcnt[new_d1]++;
            if (dcnt[new_d2] == 0) delta_diff--; dcnt[new_d2]++;

            int new_diff_ex = diff_ex + delta_diff;

            /* Fast rejection if diff_ex jumps too high when cold */
            double T = T_start * exp(log_ratio * (step * inv_steps));
            int optimistic_E = W_DIFF * new_diff_ex;
            if (optimistic_E - cur_E > 15.0 * T && new_diff_ex > diff_ex + 1) {
                /* Undo dcnt and reject without computing cycles */
                dcnt[new_d1]--; dcnt[new_d2]--;
                dcnt[old_d1]++; dcnt[old_d2]++;
                w->total_steps++;
                continue;
            }

            mate0[na1] = nb1; mate0[nb1] = na1;
            mate0[na2] = nb2; mate0[nb2] = na2;
            int new_cyc_ex = compute_cycle_excess(mate0);
            int new_E = W_DIFF * new_diff_ex + new_cyc_ex;
            int dE = new_E - cur_E;

            if (dE <= 0 || rand_u01(&w->rng) < exp(-(double)dE / T)) {
                pa[i] = na1; pb[i] = nb1;
                pa[j] = na2; pb[j] = nb2;
                diff_ex = new_diff_ex;
                cyc_ex = new_cyc_ex;
                cur_E = new_E;
                if (cur_E < w->best_energy) w->best_energy = cur_E;
                if (diff_ex == 0 && cyc_ex < w->best_valid_cyc) {
                    w->best_valid_cyc = cyc_ex;
                    if (cyc_ex == 0) {
                        pthread_mutex_lock(&out_mtx);
                        if (!found) {
                            found = 1;
                            printf("PERFECT_SA N=%d K_%d tid=%d time=%.3fs steps=%lld restarts=%lld PAIRS:",
                                   N, N + 1, w->tid, now_sec() - start_wall, w->total_steps, w->restarts);
                            for (int p = 0; p < H; p++) printf(" %u-%u", pa[p], pb[p]);
                            printf("\n");
                            fflush(stdout);
                        }
                        pthread_mutex_unlock(&out_mtx);
                    }
                }
            } else {
                /* Undo */
                mate0[a1] = b1; mate0[b1] = a1;
                mate0[a2] = b2; mate0[b2] = a2;
                dcnt[new_d1]--; dcnt[new_d2]--;
                dcnt[old_d1]++; dcnt[old_d2]++;
            }
            w->total_steps++;
        }
        w->restarts++;
    }
    return NULL;
}

static void load_group(const char *path) {
    FILE *fp = fopen(path, "r");
    if (!fp) { perror("fopen group"); exit(2); }
    char buf[512];
    if (!fgets(buf, sizeof(buf), fp)) exit(2);
    printf("Group: %s", buf);
    if (fscanf(fp, "%d", &N) != 1 || N > MAXN || (N & 1) == 0) exit(2);
    H = (N - 1) / 2;
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++) {
            int tmp;
            if (fscanf(fp, "%d", &tmp) != 1) exit(2);
            mul_tab[a][b] = (uint8_t)tmp;
        }
    fclose(fp);

    /* Find inverses (0 is identity!) */
    for (int a = 0; a < N; a++) {
        inv_arr[a] = 255;
        for (int b = 0; b < N; b++) {
            if (mul_tab[a][b] == 0) { inv_arr[a] = (uint8_t)b; break; }
        }
        if (inv_arr[a] == 255) { fprintf(stderr, "No inverse for %d\n", a); exit(2); }
    }

    /* Group non-identity elements into inverse pairs {d, d^{-1}} */
    int pair_of[MAXN];
    for (int a = 0; a < N; a++) pair_of[a] = -1;
    int pid = 0;
    for (int a = 1; a < N; a++) {
        if (pair_of[a] == -1) {
            int ia = inv_arr[a];
            pair_of[a] = pid;
            pair_of[ia] = pid;
            d_rep[pid] = (uint8_t)a;
            pid++;
        }
    }
    if (pid != H) { fprintf(stderr, "Bad inverse pairs %d != %d\n", pid, H); exit(2); }
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++) {
            if (a == b) diff_id[a][b] = 255;
            else diff_id[a][b] = (uint8_t)pair_of[mul_tab[a][inv_arr[b]]];
        }
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "Usage: %s <group_spec> <threads> <seed> <max_sec> <T_start> <T_end> <steps_per_restart>\n", argv[0]);
        return 2;
    }
    load_group(argv[1]);
    int nthreads = atoi(argv[2]);
    if (nthreads < 1) nthreads = 1;
    if (nthreads > 2) nthreads = 2;
    global_seed = strtoull(argv[3], NULL, 10);
    max_seconds = atof(argv[4]);
    T_start = atof(argv[5]);
    T_end = atof(argv[6]);
    steps_per_restart = atoll(argv[7]);

    start_wall = now_sec();
    pthread_t th[2];
    Worker wk[2];
    memset(wk, 0, sizeof(wk));
    for (int t = 0; t < nthreads; t++) {
        wk[t].tid = t;
        wk[t].rng = (global_seed * 0x9E3779B97F4A7C15ULL + 0xBF58476D1CE4E5B9ULL * (uint64_t)(t + 1)) | 1ULL;
        pthread_create(&th[t], NULL, worker_main, &wk[t]);
    }
    long long tot_steps = 0, tot_restarts = 0;
    int best_vc = 1 << 30, best_e = 1 << 30;
    for (int t = 0; t < nthreads; t++) {
        pthread_join(th[t], NULL);
        tot_steps += wk[t].total_steps;
        tot_restarts += wk[t].restarts;
        if (wk[t].best_valid_cyc < best_vc) best_vc = wk[t].best_valid_cyc;
        if (wk[t].best_energy < best_e) best_e = wk[t].best_energy;
    }
    double dt = now_sec() - start_wall;
    printf("DONE_SA N=%d K_%d found=%d best_valid_cyc=%d best_E=%d steps=%lld (%.1f k/s) restarts=%lld time=%.3fs\n",
           N, N + 1, found, best_vc, best_e, tot_steps, dt > 0 ? tot_steps / (1000.0 * dt) : 0.0, tot_restarts, dt);
    return 0;
}
