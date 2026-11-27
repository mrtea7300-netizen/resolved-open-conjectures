/*
 * ring_starter_sa.c -- Simulated Annealing over U-invariant starters in a finite
 * commutative ring R of odd order n with admissible subgroup U <= R*.
 *
 * State: a matching of the 2C U-orbits into C pair-orbits (o1_i, o2_i, m_i),
 * where m_i in 0..M-1 picks which element of o2_i pairs with rep(o1_i).
 * Moves:
 *   (A) Re-phase: pick one pair-orbit i and change m_i -> m_i' in 0..M-1.
 *   (B) 2-opt swap: pick two pair-orbits (a1, b1), (a2, b2) -> (a1, a2), (b1, b2)
 *       (or (a1, b2), (b1, a2)) with random phases m1', m2' in 0..M-1.
 * Energy:
 *   E = W_DIFF * missing_g_orbits + sum_{j=0..C-1} (num_cycles(H_j) - 1).
 *   E == 0 iff the C pair-orbits form a valid U-invariant starter inducing a P1F of K_{n+1}!
 *
 * Compile: gcc -O3 -march=native -pthread -lm -o ring_starter_sa ring_starter_sa.c
 * Usage:   ./ring_starter_sa <spec> <threads> <seed> <max_sec> <T_start> <T_end> <steps_per_restart>
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>
#include <time.h>

#define MAXN 2048
#define MAXC 64

static int N, M, C, NUM_U;
static int *g_reps;
static int *u_orb_rep;
static int *u_orb_elems; /* [NUM_U * M] */
static uint16_t *mul_u;  /* [M * N] */
static uint16_t *shift_tab; /* [C * N] */
static uint8_t  *g_of_pair; /* [NUM_U * NUM_U * M]: G-orbit of rep(o1) - elem(o2, m) */

static volatile int found = 0;
static volatile int time_expired = 0;
static double start_wall = 0.0;
static double max_seconds = 60.0;
static double T_start = 4.0, T_end = 0.05;
static long long steps_per_restart = 1000000;
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

static int compute_cycle_excess(const uint16_t *mate0) {
    int excess = 0;
    int V = N + 1;
    uint16_t mate_d[MAXN + 1];
    uint8_t vis[MAXN + 1];

    for (int j = 0; j < C; j++) {
        const uint16_t *sh = shift_tab + (size_t)j * N;
        uint16_t dj = (uint16_t)g_reps[j];
        for (int v = 1; v < N; v++) {
            mate_d[sh[v]] = sh[mate0[v]];
        }
        mate_d[dj] = (uint16_t)N;
        mate_d[N] = dj;

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

static inline void set_pair_orbit(uint16_t *mate0, int o1, int o2, int mi) {
    int ra = u_orb_rep[o1];
    int rb = u_orb_elems[o2 * M + mi];
    for (int k = 0; k < M; k++) {
        uint16_t ux = mul_u[k * N + ra];
        uint16_t uy = mul_u[k * N + rb];
        mate0[ux] = uy;
        mate0[uy] = ux;
    }
}

typedef struct {
    int tid;
    uint64_t rng;
    long long total_steps;
    long long restarts;
    int best_valid_cyc;
    int best_energy;
} Worker;

static void *worker_main(void *arg) {
    Worker *w = (Worker *)arg;
    w->best_valid_cyc = 1 << 30;
    w->best_energy = 1 << 30;

    int oa[MAXC], ob[MAXC], pm[MAXC], pg[MAXC];
    int gcnt[MAXC];
    uint16_t mate0[MAXN + 1];
    int W_DIFF = 5;

    while (!found && !time_expired) {
        int perm[2 * MAXC];
        for (int i = 0; i < NUM_U; i++) perm[i] = i;
        for (int i = NUM_U - 1; i > 0; i--) {
            int j = (int)(xorshift64(&w->rng) % (uint64_t)(i + 1));
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        memset(gcnt, 0, (size_t)C * sizeof(int));
        mate0[0] = (uint16_t)N; mate0[N] = 0;
        for (int i = 0; i < C; i++) {
            oa[i] = perm[2 * i];
            ob[i] = perm[2 * i + 1];
            pm[i] = (int)(xorshift64(&w->rng) % (uint64_t)M);
            pg[i] = g_of_pair[(oa[i] * NUM_U + ob[i]) * M + pm[i]];
            gcnt[pg[i]]++;
            set_pair_orbit(mate0, oa[i], ob[i], pm[i]);
        }
        int diff_ex = 0;
        for (int j = 0; j < C; j++) if (gcnt[j] == 0) diff_ex++;
        int cyc_ex = compute_cycle_excess(mate0);
        int cur_E = W_DIFF * diff_ex + cyc_ex;

        double log_ratio = log(T_end / T_start);
        double inv_steps = 1.0 / (double)steps_per_restart;

        for (long long step = 0; step < steps_per_restart && !found && !time_expired; step++) {
            if ((step & 4095LL) == 0 && (now_sec() - start_wall) >= max_seconds) {
                time_expired = 1;
                break;
            }
            double T = T_start * exp(log_ratio * (step * inv_steps));
            int move_type = (M > 1 && (xorshift64(&w->rng) % 3ULL == 0ULL)) ? 0 : 1;

            if (move_type == 0) {
                /* Re-phase single pair-orbit i */
                int i = (int)(xorshift64(&w->rng) % (uint64_t)C);
                int old_m = pm[i];
                int new_m = (int)(xorshift64(&w->rng) % (uint64_t)(M - 1));
                if (new_m >= old_m) new_m++;
                int old_g = pg[i];
                int new_g = g_of_pair[(oa[i] * NUM_U + ob[i]) * M + new_m];

                int delta_diff = 0;
                gcnt[old_g]--; if (gcnt[old_g] == 0) delta_diff++;
                if (gcnt[new_g] == 0) delta_diff--; gcnt[new_g]++;
                int new_diff_ex = diff_ex + delta_diff;

                if (W_DIFF * new_diff_ex - cur_E > 15.0 * T && new_diff_ex > diff_ex + 1) {
                    gcnt[new_g]--; gcnt[old_g]++;
                    w->total_steps++;
                    continue;
                }

                set_pair_orbit(mate0, oa[i], ob[i], new_m);
                int new_cyc_ex = compute_cycle_excess(mate0);
                int new_E = W_DIFF * new_diff_ex + new_cyc_ex;
                int dE = new_E - cur_E;
                if (dE <= 0 || rand_u01(&w->rng) < exp(-(double)dE / T)) {
                    pm[i] = new_m; pg[i] = new_g;
                    diff_ex = new_diff_ex; cyc_ex = new_cyc_ex; cur_E = new_E;
                } else {
                    set_pair_orbit(mate0, oa[i], ob[i], old_m);
                    gcnt[new_g]--; gcnt[old_g]++;
                }
            } else {
                /* 2-opt swap of two pair-orbits */
                int i = (int)(xorshift64(&w->rng) % (uint64_t)C);
                int j = (int)(xorshift64(&w->rng) % (uint64_t)(C - 1));
                if (j >= i) j++;
                int mode = (int)(xorshift64(&w->rng) & 1ULL);

                int a1 = oa[i], b1 = ob[i], m1 = pm[i], g1 = pg[i];
                int a2 = oa[j], b2 = ob[j], m2 = pm[j], g2 = pg[j];
                int na1 = a1, nb1 = mode ? a2 : b2;
                int na2 = b1, nb2 = mode ? b2 : a2;
                int nm1 = (int)(xorshift64(&w->rng) % (uint64_t)M);
                int nm2 = (int)(xorshift64(&w->rng) % (uint64_t)M);
                int ng1 = g_of_pair[(na1 * NUM_U + nb1) * M + nm1];
                int ng2 = g_of_pair[(na2 * NUM_U + nb2) * M + nm2];

                int delta_diff = 0;
                gcnt[g1]--; if (gcnt[g1] == 0) delta_diff++;
                gcnt[g2]--; if (gcnt[g2] == 0) delta_diff++;
                if (gcnt[ng1] == 0) delta_diff--; gcnt[ng1]++;
                if (gcnt[ng2] == 0) delta_diff--; gcnt[ng2]++;
                int new_diff_ex = diff_ex + delta_diff;

                if (W_DIFF * new_diff_ex - cur_E > 15.0 * T && new_diff_ex > diff_ex + 1) {
                    gcnt[ng1]--; gcnt[ng2]--; gcnt[g1]++; gcnt[g2]++;
                    w->total_steps++;
                    continue;
                }

                set_pair_orbit(mate0, na1, nb1, nm1);
                set_pair_orbit(mate0, na2, nb2, nm2);
                int new_cyc_ex = compute_cycle_excess(mate0);
                int new_E = W_DIFF * new_diff_ex + new_cyc_ex;
                int dE = new_E - cur_E;
                if (dE <= 0 || rand_u01(&w->rng) < exp(-(double)dE / T)) {
                    oa[i] = na1; ob[i] = nb1; pm[i] = nm1; pg[i] = ng1;
                    oa[j] = na2; ob[j] = nb2; pm[j] = nm2; pg[j] = ng2;
                    diff_ex = new_diff_ex; cyc_ex = new_cyc_ex; cur_E = new_E;
                } else {
                    set_pair_orbit(mate0, a1, b1, m1);
                    set_pair_orbit(mate0, a2, b2, m2);
                    gcnt[ng1]--; gcnt[ng2]--; gcnt[g1]++; gcnt[g2]++;
                }
            }

            if (cur_E < w->best_energy) w->best_energy = cur_E;
            if (diff_ex == 0 && cyc_ex < w->best_valid_cyc) {
                w->best_valid_cyc = cyc_ex;
                if (cyc_ex == 0) {
                    pthread_mutex_lock(&out_mtx);
                    if (!found) {
                        found = 1;
                        printf("PERFECT_RING_SA N=%d K_%d tid=%d time=%.3fs steps=%lld restarts=%lld REPS:",
                               N, N + 1, w->tid, now_sec() - start_wall, w->total_steps, w->restarts);
                        for (int k = 0; k < C; k++) {
                            printf(" %d-%d", u_orb_rep[oa[k]], u_orb_elems[ob[k] * M + pm[k]]);
                        }
                        printf("\n");
                        fflush(stdout);
                    }
                    pthread_mutex_unlock(&out_mtx);
                }
            }
            w->total_steps++;
        }
        w->restarts++;
    }
    return NULL;
}

static void load_spec(const char *path) {
    FILE *fp = fopen(path, "r");
    if (!fp) { perror("fopen spec"); exit(2); }
    char buf[1024];
    if (!fgets(buf, sizeof(buf), fp)) exit(2);
    printf("Spec: %s", buf);
    if (fscanf(fp, "%d %d %d", &N, &M, &C) != 3) exit(2);
    if (N > MAXN || C > MAXC) { fprintf(stderr, "Exceeds MAXN/MAXC\n"); exit(2); }
    NUM_U = 2 * C;
    int *neg_arr = malloc((size_t)N * sizeof(int));
    int *u_orb_id = malloc((size_t)N * sizeof(int));
    int *g_orb_id = malloc((size_t)N * sizeof(int));
    g_reps = malloc((size_t)C * sizeof(int));
    mul_u = malloc((size_t)M * N * sizeof(uint16_t));
    uint16_t *add_tab = malloc((size_t)N * N * sizeof(uint16_t));

    for (int i = 0; i < N; i++) if (fscanf(fp, "%d", &neg_arr[i]) != 1) exit(2);
    for (int i = 0; i < N; i++) if (fscanf(fp, "%d", &u_orb_id[i]) != 1) exit(2);
    for (int i = 0; i < N; i++) if (fscanf(fp, "%d", &g_orb_id[i]) != 1) exit(2);
    for (int i = 0; i < C; i++) if (fscanf(fp, "%d", &g_reps[i]) != 1) exit(2);
    for (int k = 0; k < M; k++)
        for (int a = 0; a < N; a++) {
            int t; if (fscanf(fp, "%d", &t) != 1) exit(2);
            mul_u[k * N + a] = (uint16_t)t;
        }
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++) {
            int t; if (fscanf(fp, "%d", &t) != 1) exit(2);
            add_tab[(size_t)a * N + b] = (uint16_t)t;
        }
    fclose(fp);

    shift_tab = malloc((size_t)C * N * sizeof(uint16_t));
    for (int j = 0; j < C; j++) {
        int dj = g_reps[j];
        for (int x = 0; x < N; x++) shift_tab[(size_t)j * N + x] = add_tab[(size_t)dj * N + x];
    }

    u_orb_rep = malloc((size_t)NUM_U * sizeof(int));
    u_orb_elems = malloc((size_t)NUM_U * M * sizeof(int));
    int *cnt = calloc((size_t)NUM_U, sizeof(int));
    for (int a = 1; a < N; a++) {
        int o = u_orb_id[a];
        if (cnt[o] == 0) u_orb_rep[o] = a;
        u_orb_elems[o * M + cnt[o]++] = a;
    }
    free(cnt);

    g_of_pair = malloc((size_t)NUM_U * NUM_U * M);
    for (int o1 = 0; o1 < NUM_U; o1++) {
        int ra = u_orb_rep[o1];
        for (int o2 = 0; o2 < NUM_U; o2++) {
            for (int mi = 0; mi < M; mi++) {
                int rb = u_orb_elems[o2 * M + mi];
                int diff = add_tab[(size_t)ra * N + neg_arr[rb]];
                g_of_pair[(o1 * NUM_U + o2) * M + mi] = (uint8_t)g_orb_id[diff];
            }
        }
    }
    free(neg_arr); free(u_orb_id); free(g_orb_id); free(add_tab);
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "Usage: %s <spec> <threads> <seed> <max_sec> <T_start> <T_end> <steps_per_restart>\n", argv[0]);
        return 2;
    }
    load_spec(argv[1]);
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
    printf("DONE_RING_SA N=%d K_%d M=%d C=%d found=%d best_valid_cyc=%d best_E=%d steps=%lld (%.1f k/s) restarts=%lld time=%.3fs\n",
           N, N + 1, M, C, found, best_vc, best_e, tot_steps, dt > 0 ? tot_steps / (1000.0 * dt) : 0.0, tot_restarts, dt);
    return 0;
}
