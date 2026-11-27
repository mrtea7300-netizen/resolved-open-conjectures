/*
 * ring_starter_bt_v2.c -- Ultra-fast U-invariant starter exact-cover backtracker.
 * Upgrades over v1:
 *   - Direct O(1) bucket index uug[o1][o2][g] (eliminates scanning dead lists at deep nodes!).
 *   - uint64_t bitmasks for uncovered U-orbits (2C <= 64) and G-orbits (C <= 64),
 *     iterating only set bits via __builtin_ctzll for blazing-fast MRV at depth C-4..C-1.
 *   - L1-cache-resident shift_tab[C][N].
 *   - Single-orbit self-cycle pre-filtering.
 *   - Resumable (seed + periodic progress logging), capped at <= 2 threads.
 *
 * Compile:
 *   gcc -O3 -march=native -pthread -o ring_starter_bt_v2 ring_starter_bt_v2.c
 *
 * Usage:
 *   ./ring_starter_bt_v2 <spec> <threads> <seed> <nodelimit> <max_seconds> [max_sols] [fix_first_u]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <time.h>

#define MAXN 6000
#define MAXC 32
#define MAXU 64

typedef struct {
    uint16_t o1, o2;
    uint16_t g;
    uint16_t ra, rb;
    uint32_t edge_off;
} PairOrbit;

static int N, M, C, NUM_U;
static int *g_reps;
static uint16_t *shift_tab; /* [C * N] */

static PairOrbit *orbits;
static int num_orbits = 0;
static uint16_t *flat_ux;
static uint16_t *flat_uy;

/* Direct bucket index: for ordered pair (o1, o2) with o1 != o2 and G-orbit g:
   bucket_off[idx] .. bucket_off[idx+1] in bucket_val[] gives all PairOrbit indices.
   idx = ((o1 * NUM_U + o2) * C + g). */
static int *bucket_off;
static int *bucket_cnt;
static int *bucket_val;
/* Bitmask of G-orbits that have >= 1 PairOrbit between o1 and o2 */
static uint64_t pair_gmask[MAXU][MAXU];

static volatile int found_sols = 0;
static volatile int time_expired = 0;
static int max_sols = 1;
static int fix_first_u = 0;
static long long nodelimit = 50000;
static double max_seconds = 60.0;
static uint64_t global_seed = 1;
static double start_wall = 0.0;
static double last_log_wall = 0.0;
static pthread_mutex_t out_mtx = PTHREAD_MUTEX_INITIALIZER;

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static inline uint64_t xorshift64(uint64_t *st) {
    uint64_t x = *st;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *st = x;
    return x;
}

static inline int add_edge(uint16_t * restrict e, int u, int v, uint16_t *o1, uint16_t *o2) {
    uint16_t e1 = e[u];
    uint16_t e2 = e[v];
    if (e1 == (uint16_t)v) return 0;
    e[e1] = e2;
    e[e2] = e1;
    *o1 = e1;
    *o2 = e2;
    return 1;
}

static inline void undo_edge(uint16_t * restrict e, uint16_t u, uint16_t v, uint16_t e1, uint16_t e2) {
    e[e1] = u;
    e[e2] = v;
}

typedef struct {
    int tid;
    uint64_t rng;
    long long nodes;
    long long total_nodes;
    long long restarts;
    long long last_cands_tested;
    int max_depth_seen;
    long long depth_hits[MAXC + 1];
    long long pass_h[MAXC + 1]; /* at depth C-1: how many cands passed graphs 0..j-1 */
    int stop_restart;
    uint64_t u_avail; /* bit o set iff U-orbit o is uncovered */
    uint64_t g_avail; /* bit g set iff G-orbit g is uncovered */
    int chosen[MAXC];
    uint16_t *end;
    uint16_t *sv_e1;
    uint16_t *sv_e2;
    uint16_t *sv_u;
    uint16_t *sv_v;
    uint8_t  *sv_j;
} Worker;

static void report_solution(Worker *w) {
    pthread_mutex_lock(&out_mtx);
    found_sols++;
    double dt = now_sec() - start_wall;
    printf("SOLUTION #%d (tid=%d, time=%.3fs, nodes=%lld, restarts=%lld) REPS:",
           found_sols, w->tid, dt, w->total_nodes + w->nodes, w->restarts);
    for (int i = 0; i < C; i++) {
        const PairOrbit *po = &orbits[w->chosen[i]];
        printf(" %u-%u", po->ra, po->rb);
    }
    printf("\n");
    fflush(stdout);
    pthread_mutex_unlock(&out_mtx);
}

static void dfs(Worker *w, int depth) {
    if (w->stop_restart || found_sols >= max_sols || time_expired) return;
    w->depth_hits[depth]++;
    if (depth > w->max_depth_seen) w->max_depth_seen = depth;
    if (depth == C) {
        report_solution(w);
        if (found_sols >= max_sols) w->stop_restart = 1;
        return;
    }
    if (++w->nodes > nodelimit) {
        w->stop_restart = 1;
        return;
    }
    if ((w->nodes & 16383LL) == 0 && (now_sec() - start_wall) >= max_seconds) {
        time_expired = 1;
        w->stop_restart = 1;
        return;
    }

    int V = N + 1;

    /* Fast path for final level: only 2 uncovered U-orbits and 1 uncovered G-orbit! */
    if (depth == C - 1) {
        uint64_t um = w->u_avail;
        int o1 = __builtin_ctzll(um);
        um &= um - 1;
        int o2 = __builtin_ctzll(um);
        int g  = __builtin_ctzll(w->g_avail);
        int bidx = (o1 * NUM_U + o2) * C + g;
        int bs = bucket_off[bidx], be = bucket_off[bidx + 1];
        if (bs == be) return;

        int slice_cap = C * 2 * M;
        int base_off = depth * slice_cap;
        uint16_t *sv_e1 = w->sv_e1 + base_off;
        uint16_t *sv_e2 = w->sv_e2 + base_off;
        uint16_t *sv_u  = w->sv_u  + base_off;
        uint16_t *sv_v  = w->sv_v  + base_off;
        uint8_t  *sv_j  = w->sv_j  + base_off;

        for (int bi = bs; bi < be && found_sols < max_sols; bi++) {
            w->last_cands_tested++;
            int idx = bucket_val[bi];
            const PairOrbit *po = &orbits[idx];
            const uint16_t *ux_arr = flat_ux + po->edge_off;
            const uint16_t *uy_arr = flat_uy + po->edge_off;

            int n_added = 0;
            int ok = 1;
            int passed = 0;
            for (int j = 0; j < C && ok; j++) {
                uint16_t * restrict e = w->end + (size_t)j * V;
                const uint16_t * restrict sh = shift_tab + (size_t)j * N;
                int closed = 0;
                for (int k = 0; k < M; k++) {
                    uint16_t ux = ux_arr[k], uy = uy_arr[k];
                    uint16_t e1, e2;
                    if (!add_edge(e, ux, uy, &e1, &e2)) { ok = 0; break; }
                    sv_j[n_added] = (uint8_t)j; sv_u[n_added] = ux; sv_v[n_added] = uy;
                    sv_e1[n_added] = e1; sv_e2[n_added] = e2; n_added++;

                    uint16_t tx = sh[ux], ty = sh[uy];
                    if (!add_edge(e, tx, ty, &e1, &e2)) {
                        if (k == M - 1 && closed == 0) {
                            closed = 1;
                        } else {
                            ok = 0;
                            break;
                        }
                    } else {
                        sv_j[n_added] = (uint8_t)j; sv_u[n_added] = tx; sv_v[n_added] = ty;
                        sv_e1[n_added] = e1; sv_e2[n_added] = e2; n_added++;
                    }
                }
                if (ok && closed != 1) ok = 0;
                if (ok) passed++;
            }
            for (int p = 0; p <= passed; p++) w->pass_h[p]++;
            if (ok) {
                w->chosen[depth] = idx;
                w->depth_hits[C]++;
                if (C > w->max_depth_seen) w->max_depth_seen = C;
                report_solution(w);
                if (found_sols >= max_sols) w->stop_restart = 1;
            }
            for (int s = n_added - 1; s >= 0; s--) {
                uint16_t * restrict e = w->end + (size_t)sv_j[s] * V;
                undo_edge(e, sv_u[s], sv_v[s], sv_e1[s], sv_e2[s]);
            }
        }
        return;
    }

    /* Exact-cover MRV using bitmasks over uncovered U-orbits and G-orbits */
    int best_is_g = 0;
    int best_item = -1;
    int best_cnt = 1 << 30;
    uint64_t u_avail = w->u_avail;
    uint64_t g_avail = w->g_avail;

    if (depth == 0 && fix_first_u) {
        best_is_g = 0;
        best_item = 0;
        int cnt = 0;
        uint64_t m2 = u_avail & ~(1ULL << 0);
        while (m2) {
            int o2 = __builtin_ctzll(m2); m2 &= m2 - 1;
            uint64_t gm = pair_gmask[0][o2] & g_avail;
            int base = (0 * NUM_U + o2) * C;
            while (gm) {
                int g = __builtin_ctzll(gm); gm &= gm - 1;
                cnt += bucket_cnt[base + g];
            }
        }
        best_cnt = cnt;
    } else {
        uint64_t m1 = u_avail;
        while (m1) {
            int o1 = __builtin_ctzll(m1); m1 &= m1 - 1;
            int cnt = 0;
            uint64_t m2 = u_avail & ~(1ULL << o1);
            while (m2) {
                int o2 = __builtin_ctzll(m2); m2 &= m2 - 1;
                uint64_t gm = pair_gmask[o1][o2] & g_avail;
                int base = (o1 * NUM_U + o2) * C;
                while (gm) {
                    int g = __builtin_ctzll(gm); gm &= gm - 1;
                    cnt += bucket_cnt[base + g];
                }
                if (cnt >= best_cnt) break;
            }
            if (cnt == 0) return;
            if (cnt < best_cnt) {
                best_cnt = cnt;
                best_item = o1;
                best_is_g = 0;
                if (cnt == 1) goto picked;
            }
        }
        uint64_t mg = g_avail;
        while (mg) {
            int g = __builtin_ctzll(mg); mg &= mg - 1;
            int cnt = 0;
            uint64_t m1b = u_avail;
            while (m1b) {
                int o1 = __builtin_ctzll(m1b); m1b &= m1b - 1;
                uint64_t m2b = m1b; /* only o2 > o1 */
                while (m2b) {
                    int o2 = __builtin_ctzll(m2b); m2b &= m2b - 1;
                    cnt += bucket_cnt[(o1 * NUM_U + o2) * C + g];
                }
                if (cnt >= best_cnt) break;
            }
            if (cnt == 0) return;
            if (cnt < best_cnt) {
                best_cnt = cnt;
                best_item = g;
                best_is_g = 1;
                if (cnt == 1) goto picked;
            }
        }
    }
picked:;

    int *cands = (int *)alloca((size_t)best_cnt * sizeof(int));
    int nc = 0;
    if (!best_is_g) {
        int o1 = best_item;
        uint64_t m2 = u_avail & ~(1ULL << o1);
        while (m2) {
            int o2 = __builtin_ctzll(m2); m2 &= m2 - 1;
            uint64_t gm = pair_gmask[o1][o2] & g_avail;
            int base = (o1 * NUM_U + o2) * C;
            while (gm) {
                int g = __builtin_ctzll(gm); gm &= gm - 1;
                int bs = bucket_off[base + g], be = bucket_off[base + g + 1];
                for (int bi = bs; bi < be; bi++) cands[nc++] = bucket_val[bi];
            }
        }
    } else {
        int g = best_item;
        uint64_t m1b = u_avail;
        while (m1b) {
            int o1 = __builtin_ctzll(m1b); m1b &= m1b - 1;
            uint64_t m2b = m1b;
            while (m2b) {
                int o2 = __builtin_ctzll(m2b); m2b &= m2b - 1;
                int bidx = (o1 * NUM_U + o2) * C + g;
                int bs = bucket_off[bidx], be = bucket_off[bidx + 1];
                for (int bi = bs; bi < be; bi++) cands[nc++] = bucket_val[bi];
            }
        }
    }

    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(xorshift64(&w->rng) % (uint64_t)(i + 1));
        int t = cands[i]; cands[i] = cands[j]; cands[j] = t;
    }

    int slice_cap = C * 2 * M;
    int base_off = depth * slice_cap;
    uint16_t *sv_e1 = w->sv_e1 + base_off;
    uint16_t *sv_e2 = w->sv_e2 + base_off;
    uint16_t *sv_u  = w->sv_u  + base_off;
    uint16_t *sv_v  = w->sv_v  + base_off;
    uint8_t  *sv_j  = w->sv_j  + base_off;

    for (int ci = 0; ci < nc && !w->stop_restart && found_sols < max_sols && !time_expired; ci++) {
        int idx = cands[ci];
        const PairOrbit *po = &orbits[idx];
        const uint16_t *ux_arr = flat_ux + po->edge_off;
        const uint16_t *uy_arr = flat_uy + po->edge_off;

        int n_added = 0;
        int ok = 1;
        for (int j = 0; j < C && ok; j++) {
            uint16_t * restrict e = w->end + (size_t)j * V;
            const uint16_t * restrict sh = shift_tab + (size_t)j * N;
            for (int k = 0; k < M; k++) {
                uint16_t ux = ux_arr[k], uy = uy_arr[k];
                uint16_t e1, e2;
                if (!add_edge(e, ux, uy, &e1, &e2)) { ok = 0; break; }
                sv_j[n_added] = (uint8_t)j; sv_u[n_added] = ux; sv_v[n_added] = uy;
                sv_e1[n_added] = e1; sv_e2[n_added] = e2; n_added++;

                uint16_t tx = sh[ux], ty = sh[uy];
                if (!add_edge(e, tx, ty, &e1, &e2)) { ok = 0; break; }
                sv_j[n_added] = (uint8_t)j; sv_u[n_added] = tx; sv_v[n_added] = ty;
                sv_e1[n_added] = e1; sv_e2[n_added] = e2; n_added++;
            }
        }

        if (ok) {
            w->u_avail ^= (1ULL << po->o1) | (1ULL << po->o2);
            w->g_avail ^= (1ULL << po->g);
            w->chosen[depth] = idx;
            dfs(w, depth + 1);
            w->u_avail ^= (1ULL << po->o1) | (1ULL << po->o2);
            w->g_avail ^= (1ULL << po->g);
        }

        for (int s = n_added - 1; s >= 0; s--) {
            uint16_t * restrict e = w->end + (size_t)sv_j[s] * V;
            undo_edge(e, sv_u[s], sv_v[s], sv_e1[s], sv_e2[s]);
        }
    }
}

static void *worker_main(void *arg) {
    Worker *w = (Worker *)arg;
    int V = N + 1;
    int total_undo = C * C * 2 * M;
    w->end   = malloc((size_t)C * V * sizeof(uint16_t));
    w->sv_e1 = malloc((size_t)total_undo * sizeof(uint16_t));
    w->sv_e2 = malloc((size_t)total_undo * sizeof(uint16_t));
    w->sv_u  = malloc((size_t)total_undo * sizeof(uint16_t));
    w->sv_v  = malloc((size_t)total_undo * sizeof(uint16_t));
    w->sv_j  = malloc((size_t)total_undo * sizeof(uint8_t));

    uint64_t full_u = (NUM_U == 64) ? ~0ULL : ((1ULL << NUM_U) - 1ULL);
    uint64_t full_g = (C == 64) ? ~0ULL : ((1ULL << C) - 1ULL);

    while (found_sols < max_sols && !time_expired) {
        w->u_avail = full_u;
        w->g_avail = full_g;
        w->nodes = 0;
        w->stop_restart = 0;
        for (int j = 0; j < C; j++) {
            uint16_t *e = w->end + (size_t)j * V;
            for (int v = 0; v < V; v++) e[v] = (uint16_t)v;
            uint16_t e1, e2;
            add_edge(e, 0, N, &e1, &e2);
            add_edge(e, g_reps[j], N, &e1, &e2);
        }
        dfs(w, 0);
        w->total_nodes += w->nodes;
        w->restarts++;
        xorshift64(&w->rng);
        double now = now_sec();
        if (w->tid == 0 && (now - last_log_wall) >= 60.0) {
            pthread_mutex_lock(&out_mtx);
            if ((now - last_log_wall) >= 60.0) {
                last_log_wall = now;
                printf("PROGRESS t=%.1fs tid0_nodes=%lld tid0_last_cands=%lld tid0_restarts=%lld tid0_pass_h:",
                       now - start_wall, w->total_nodes, w->last_cands_tested, w->restarts);
                for (int p = 0; p <= C; p++) if (w->pass_h[p]) printf(" h%d=%lld", p, w->pass_h[p]);
                printf("\n");
                fflush(stdout);
            }
            pthread_mutex_unlock(&out_mtx);
        }
        if ((now - start_wall) >= max_seconds) {
            time_expired = 1;
            break;
        }
    }

    free(w->end);
    free(w->sv_e1); free(w->sv_e2); free(w->sv_u); free(w->sv_v); free(w->sv_j);
    return NULL;
}

static void load_and_prefilter(const char *path) {
    FILE *fp = fopen(path, "r");
    if (!fp) { perror("fopen spec"); exit(2); }
    char buf[1024];
    if (!fgets(buf, sizeof(buf), fp)) exit(2);
    printf("Spec: %s", buf);
    if (fscanf(fp, "%d %d %d", &N, &M, &C) != 3) exit(2);
    if (N > MAXN || C > MAXC) {
        fprintf(stderr, "Exceeds MAXN=%d or MAXC=%d (N=%d C=%d)\n", MAXN, MAXC, N, C);
        exit(2);
    }
    NUM_U = 2 * C;
    int *neg_arr = malloc((size_t)N * sizeof(int));
    int *u_orb_id = malloc((size_t)N * sizeof(int));
    int *g_orb_id = malloc((size_t)N * sizeof(int));
    g_reps = malloc((size_t)C * sizeof(int));
    int *mul_u = malloc((size_t)M * N * sizeof(int));
    uint16_t *add_tab = malloc((size_t)N * N * sizeof(uint16_t));

    for (int i = 0; i < N; i++) if (fscanf(fp, "%d", &neg_arr[i]) != 1) exit(2);
    for (int i = 0; i < N; i++) if (fscanf(fp, "%d", &u_orb_id[i]) != 1) exit(2);
    for (int i = 0; i < N; i++) if (fscanf(fp, "%d", &g_orb_id[i]) != 1) exit(2);
    for (int i = 0; i < C; i++) if (fscanf(fp, "%d", &g_reps[i]) != 1) exit(2);
    for (int k = 0; k < M; k++)
        for (int a = 0; a < N; a++)
            if (fscanf(fp, "%d", &mul_u[k * N + a]) != 1) exit(2);
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++) {
            int tmp;
            if (fscanf(fp, "%d", &tmp) != 1) exit(2);
            add_tab[(size_t)a * N + b] = (uint16_t)tmp;
        }
    fclose(fp);

    shift_tab = malloc((size_t)C * N * sizeof(uint16_t));
    for (int j = 0; j < C; j++) {
        int dj = g_reps[j];
        for (int x = 0; x < N; x++) shift_tab[(size_t)j * N + x] = add_tab[(size_t)dj * N + x];
    }

    int *u_orb_rep = malloc((size_t)NUM_U * sizeof(int));
    int *u_orb_elems = malloc((size_t)NUM_U * M * sizeof(int));
    int *cnt = calloc((size_t)NUM_U, sizeof(int));
    for (int a = 1; a < N; a++) {
        int o = u_orb_id[a];
        if (cnt[o] == 0) u_orb_rep[o] = a;
        u_orb_elems[o * M + cnt[o]++] = a;
    }
    free(cnt);

    int max_orbits = (NUM_U * (NUM_U - 1) / 2) * M;
    orbits = malloc((size_t)max_orbits * sizeof(PairOrbit));
    flat_ux = malloc((size_t)max_orbits * M * sizeof(uint16_t));
    flat_uy = malloc((size_t)max_orbits * M * sizeof(uint16_t));

    int V = N + 1;
    uint16_t *e = malloc((size_t)V * sizeof(uint16_t));
    int total_raw = 0, kept = 0;

    for (int o1 = 0; o1 < NUM_U; o1++) {
        int ra = u_orb_rep[o1];
        for (int o2 = o1 + 1; o2 < NUM_U; o2++) {
            for (int m_i = 0; m_i < M; m_i++) {
                int y = u_orb_elems[o2 * M + m_i];
                total_raw++;
                int diff = add_tab[(size_t)ra * N + neg_arr[y]];
                int g = g_orb_id[diff];

                int ok = 1;
                for (int j = 0; j < C && ok; j++) {
                    for (int v = 0; v < V; v++) e[v] = (uint16_t)v;
                    uint16_t e1, e2;
                    add_edge(e, 0, N, &e1, &e2);
                    add_edge(e, g_reps[j], N, &e1, &e2);
                    const uint16_t *sh = shift_tab + (size_t)j * N;
                    for (int k = 0; k < M; k++) {
                        int ux = mul_u[k * N + ra];
                        int uy = mul_u[k * N + y];
                        if (!add_edge(e, ux, uy, &e1, &e2)) { ok = 0; break; }
                        if (!add_edge(e, sh[ux], sh[uy], &e1, &e2)) {
                            if (!(C == 1 && k == M - 1)) { ok = 0; break; }
                        }
                    }
                }
                if (ok) {
                    PairOrbit *po = &orbits[kept];
                    po->o1 = (uint16_t)o1;
                    po->o2 = (uint16_t)o2;
                    po->g  = (uint16_t)g;
                    po->ra = (uint16_t)ra;
                    po->rb = (uint16_t)y;
                    po->edge_off = (uint32_t)(kept * M);
                    for (int k = 0; k < M; k++) {
                        flat_ux[po->edge_off + k] = (uint16_t)mul_u[k * N + ra];
                        flat_uy[po->edge_off + k] = (uint16_t)mul_u[k * N + y];
                    }
                    kept++;
                }
            }
        }
    }
    num_orbits = kept;
    printf("Pre-filter: kept %d / %d pair-orbits (%.2f%% survived)\n",
           kept, total_raw, 100.0 * kept / (total_raw ? total_raw : 1));
    fflush(stdout);

    int nbuckets = NUM_U * NUM_U * C;
    bucket_cnt = calloc((size_t)nbuckets, sizeof(int));
    memset(pair_gmask, 0, sizeof(pair_gmask));
    for (int i = 0; i < num_orbits; i++) {
        int o1 = orbits[i].o1, o2 = orbits[i].o2, g = orbits[i].g;
        bucket_cnt[(o1 * NUM_U + o2) * C + g]++;
        bucket_cnt[(o2 * NUM_U + o1) * C + g]++;
        pair_gmask[o1][o2] |= (1ULL << g);
        pair_gmask[o2][o1] |= (1ULL << g);
    }
    bucket_off = malloc((size_t)(nbuckets + 1) * sizeof(int));
    bucket_off[0] = 0;
    for (int b = 0; b < nbuckets; b++) bucket_off[b + 1] = bucket_off[b] + bucket_cnt[b];
    bucket_val = malloc((size_t)bucket_off[nbuckets] * sizeof(int));
    int *cur = calloc((size_t)nbuckets, sizeof(int));
    for (int i = 0; i < num_orbits; i++) {
        int o1 = orbits[i].o1, o2 = orbits[i].o2, g = orbits[i].g;
        int b1 = (o1 * NUM_U + o2) * C + g;
        int b2 = (o2 * NUM_U + o1) * C + g;
        bucket_val[bucket_off[b1] + cur[b1]++] = i;
        bucket_val[bucket_off[b2] + cur[b2]++] = i;
    }

    free(cur); free(e); free(neg_arr); free(u_orb_id); free(g_orb_id);
    free(mul_u); free(add_tab); free(u_orb_rep); free(u_orb_elems);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "Usage: %s <spec> <threads> <seed> <nodelimit> <max_seconds> [max_sols] [fix_first_u]\n", argv[0]);
        return 2;
    }
    load_and_prefilter(argv[1]);
    int nthreads = atoi(argv[2]);
    if (nthreads < 1) nthreads = 1;
    if (nthreads > 2) {
        fprintf(stderr, "Capping threads from %d to 2 (shared-host policy).\n", nthreads);
        nthreads = 2;
    }
    global_seed = strtoull(argv[3], NULL, 10);
    nodelimit = atoll(argv[4]);
    max_seconds = atof(argv[5]);
    if (argc > 6) max_sols = atoi(argv[6]);
    if (argc > 7) fix_first_u = atoi(argv[7]);

    start_wall = now_sec();
    last_log_wall = start_wall;
    pthread_t *th = malloc((size_t)nthreads * sizeof(pthread_t));
    Worker *wk = calloc((size_t)nthreads, sizeof(Worker));

    for (int t = 0; t < nthreads; t++) {
        wk[t].tid = t;
        wk[t].rng = (global_seed * 0x9E3779B97F4A7C15ULL + 0xBF58476D1CE4E5B9ULL * (uint64_t)(t + 1)) | 1ULL;
        pthread_create(&th[t], NULL, worker_main, &wk[t]);
    }

    long long tot_nodes = 0, tot_restarts = 0, tot_last_cands = 0;
    int max_d = 0;
    long long d_hits[MAXC + 1] = {0};
    long long p_hits[MAXC + 1] = {0};
    for (int t = 0; t < nthreads; t++) {
        pthread_join(th[t], NULL);
        tot_nodes += wk[t].total_nodes;
        tot_restarts += wk[t].restarts;
        tot_last_cands += wk[t].last_cands_tested;
        if (wk[t].max_depth_seen > max_d) max_d = wk[t].max_depth_seen;
        for (int d = 0; d <= C; d++) d_hits[d] += wk[t].depth_hits[d];
        for (int p = 0; p <= C; p++) p_hits[p] += wk[t].pass_h[p];
    }

    double dt = now_sec() - start_wall;
    printf("DONE N=%d K_%d M=%d C=%d sols=%d max_depth=%d/%d nodes=%lld (%.1f k/s) last_cands=%lld restarts=%lld time=%.3fs\n",
           N, N + 1, M, C, found_sols, max_d, C, tot_nodes,
           dt > 0 ? tot_nodes / (1000.0 * dt) : 0.0, tot_last_cands, tot_restarts, dt);
    printf("DEPTH_HIST:");
    for (int d = 0; d <= C; d++) if (d_hits[d]) printf(" d%d=%lld", d, d_hits[d]);
    printf("\nPASS_H:");
    for (int p = 0; p <= C; p++) if (p_hits[p]) printf(" h%d=%lld", p, p_hits[p]);
    printf("\n");

    free(th); free(wk);
    return 0;
}
