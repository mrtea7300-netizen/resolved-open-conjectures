/*
 * ring_starter_bt_fast.c -- High-speed generalized U-invariant starter exact-cover
 * backtracker with:
 *   1. Single-orbit self-cycle pre-filtering (eliminates dead pair-orbits upfront).
 *   2. L1-cache-resident shift[C][N] table (no N x N table during search!).
 *   3. Exact-cover MRV over BOTH uncovered U-orbits AND uncovered G-orbits,
 *      scanning only pre-filtered valid pair-orbits.
 *   4. O(1) incremental path-endpoint short-cycle pruning across all C graphs.
 *   5. At most 2 threads (shared-host policy), resumable via seed, time-bounded.
 *
 * Compile:
 *   gcc -O3 -march=native -pthread -o ring_starter_bt_fast ring_starter_bt_fast.c
 *
 * Usage:
 *   ./ring_starter_bt_fast <spec> <threads> <seed> <nodelimit> <max_seconds> [max_sols] [fix_first_u]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <time.h>

#define MAXN 6000
#define MAXC 64

typedef struct {
    uint16_t o1, o2;
    uint16_t g;
    uint16_t ra, rb;
    uint32_t edge_off; /* offset into flat_ux / flat_uy of length M */
} PairOrbit;

static int N, M, C, NUM_U;
static int *g_reps;
static uint16_t *shift_tab; /* [C * N]: shift_tab[j*N + x] = x + g_reps[j] */

static PairOrbit *orbits;
static int num_orbits = 0;
static uint16_t *flat_ux; /* [num_orbits * M] */
static uint16_t *flat_uy; /* [num_orbits * M] */

/* Adjacency lists of pre-filtered PairOrbit indices for fast MRV */
static int *u_list_off;  /* [NUM_U + 1] */
static int *u_list_idx;  /* indices into orbits[] */
static int *g_list_off;  /* [C + 1] */
static int *g_list_idx;  /* indices into orbits[] */

static volatile int found_sols = 0;
static volatile int time_expired = 0;
static int max_sols = 1;
static int fix_first_u = 0;
static long long nodelimit = 50000;
static double max_seconds = 60.0;
static uint64_t global_seed = 1;
static double start_wall = 0.0;
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
    int max_depth_seen;
    long long depth_hits[MAXC + 1];
    int stop_restart;
    uint8_t u_used[2 * MAXC];
    uint8_t g_used[MAXC];
    int chosen[MAXC];
    uint16_t *end;  /* [C * (N+1)] */
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
    if ((w->nodes & 4095LL) == 0 && (now_sec() - start_wall) >= max_seconds) {
        time_expired = 1;
        w->stop_restart = 1;
        return;
    }

    int last = (depth == C - 1);

    /* Exact-cover MRV: choose either an uncovered U-orbit or uncovered G-orbit
       with the minimum number of currently valid PairOrbits */
    int best_is_g = 0;
    int best_item = -1;
    int best_cnt = 1 << 30;

    if (depth == 0 && fix_first_u) {
        best_is_g = 0;
        best_item = 0;
        best_cnt = u_list_off[1] - u_list_off[0];
    } else {
        for (int o = 0; o < NUM_U; o++) {
            if (w->u_used[o]) continue;
            int cnt = 0;
            int s = u_list_off[o], e = u_list_off[o + 1];
            for (int i = s; i < e; i++) {
                const PairOrbit *po = &orbits[u_list_idx[i]];
                if (!w->u_used[po->o1] && !w->u_used[po->o2] && !w->g_used[po->g]) {
                    cnt++;
                    if (cnt >= best_cnt) break;
                }
            }
            if (cnt == 0) return;
            if (cnt < best_cnt) {
                best_cnt = cnt;
                best_item = o;
                best_is_g = 0;
                if (cnt == 1) goto picked;
            }
        }
        for (int g = 0; g < C; g++) {
            if (w->g_used[g]) continue;
            int cnt = 0;
            int s = g_list_off[g], e = g_list_off[g + 1];
            for (int i = s; i < e; i++) {
                const PairOrbit *po = &orbits[g_list_idx[i]];
                if (!w->u_used[po->o1] && !w->u_used[po->o2]) {
                    cnt++;
                    if (cnt >= best_cnt) break;
                }
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
        int s = u_list_off[best_item], e = u_list_off[best_item + 1];
        for (int i = s; i < e; i++) {
            int idx = u_list_idx[i];
            const PairOrbit *po = &orbits[idx];
            if (!w->u_used[po->o1] && !w->u_used[po->o2] && !w->g_used[po->g]) {
                cands[nc++] = idx;
            }
        }
    } else {
        int s = g_list_off[best_item], e = g_list_off[best_item + 1];
        for (int i = s; i < e; i++) {
            int idx = g_list_idx[i];
            const PairOrbit *po = &orbits[idx];
            if (!w->u_used[po->o1] && !w->u_used[po->o2]) {
                cands[nc++] = idx;
            }
        }
    }

    /* Randomize candidate order (Fisher-Yates) */
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

    int V = N + 1;
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
            int closed = 0;
            for (int k = 0; k < M; k++) {
                uint16_t ux = ux_arr[k];
                uint16_t uy = uy_arr[k];
                uint16_t e1, e2;
                if (!add_edge(e, ux, uy, &e1, &e2)) {
                    ok = 0;
                    break;
                }
                sv_j[n_added] = (uint8_t)j; sv_u[n_added] = ux; sv_v[n_added] = uy;
                sv_e1[n_added] = e1; sv_e2[n_added] = e2; n_added++;

                uint16_t tx = sh[ux];
                uint16_t ty = sh[uy];
                if (!add_edge(e, tx, ty, &e1, &e2)) {
                    if (last && k == M - 1 && closed == 0) {
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
            if (ok && last && closed != 1) ok = 0;
        }

        if (ok) {
            w->u_used[po->o1] = 1;
            w->u_used[po->o2] = 1;
            w->g_used[po->g] = 1;
            w->chosen[depth] = idx;
            dfs(w, depth + 1);
            w->u_used[po->o1] = 0;
            w->u_used[po->o2] = 0;
            w->g_used[po->g] = 0;
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

    while (found_sols < max_sols && !time_expired) {
        memset(w->u_used, 0, sizeof(w->u_used));
        memset(w->g_used, 0, sizeof(w->g_used));
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
        if ((now_sec() - start_wall) >= max_seconds) {
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

    /* Build L1-friendly shift_tab[C][N] */
    shift_tab = malloc((size_t)C * N * sizeof(uint16_t));
    for (int j = 0; j < C; j++) {
        int dj = g_reps[j];
        for (int x = 0; x < N; x++) {
            shift_tab[(size_t)j * N + x] = add_tab[(size_t)dj * N + x];
        }
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

    /* Enumerate all unique pair-orbits (o1 < o2, ra = u_orb_rep[o1], y in o2)
       and pre-filter against single-orbit self-cycles across all C graphs! */
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

                /* Check if this single pair-orbit alone closes a short cycle in any H_j */
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
                            /* Only valid if C == 1 and k == M-1 */
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
    printf("Pre-filter: kept %d / %d pair-orbits (%.2f%% survived single-orbit cycle check)\n",
           kept, total_raw, 100.0 * kept / (total_raw ? total_raw : 1));
    fflush(stdout);

    /* Build adjacency lists for U-orbits and G-orbits */
    int *u_cnt = calloc((size_t)NUM_U, sizeof(int));
    int *g_cnt = calloc((size_t)C, sizeof(int));
    for (int i = 0; i < num_orbits; i++) {
        u_cnt[orbits[i].o1]++;
        u_cnt[orbits[i].o2]++;
        g_cnt[orbits[i].g]++;
    }
    u_list_off = malloc((size_t)(NUM_U + 1) * sizeof(int));
    g_list_off = malloc((size_t)(C + 1) * sizeof(int));
    u_list_off[0] = 0;
    for (int o = 0; o < NUM_U; o++) u_list_off[o + 1] = u_list_off[o] + u_cnt[o];
    g_list_off[0] = 0;
    for (int g = 0; g < C; g++) g_list_off[g + 1] = g_list_off[g] + g_cnt[g];
    u_list_idx = malloc((size_t)u_list_off[NUM_U] * sizeof(int));
    g_list_idx = malloc((size_t)g_list_off[C] * sizeof(int));

    int *u_cur = calloc((size_t)NUM_U, sizeof(int));
    int *g_cur = calloc((size_t)C, sizeof(int));
    for (int i = 0; i < num_orbits; i++) {
        int o1 = orbits[i].o1, o2 = orbits[i].o2, g = orbits[i].g;
        u_list_idx[u_list_off[o1] + u_cur[o1]++] = i;
        u_list_idx[u_list_off[o2] + u_cur[o2]++] = i;
        g_list_idx[g_list_off[g] + g_cur[g]++] = i;
    }

    free(u_cnt); free(g_cnt); free(u_cur); free(g_cur);
    free(e); free(neg_arr); free(u_orb_id); free(g_orb_id);
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
    pthread_t *th = malloc((size_t)nthreads * sizeof(pthread_t));
    Worker *wk = calloc((size_t)nthreads, sizeof(Worker));

    for (int t = 0; t < nthreads; t++) {
        wk[t].tid = t;
        wk[t].rng = (global_seed * 0x9E3779B97F4A7C15ULL + 0xBF58476D1CE4E5B9ULL * (uint64_t)(t + 1)) | 1ULL;
        pthread_create(&th[t], NULL, worker_main, &wk[t]);
    }

    long long tot_nodes = 0, tot_restarts = 0;
    int max_d = 0;
    long long d_hits[MAXC + 1] = {0};
    for (int t = 0; t < nthreads; t++) {
        pthread_join(th[t], NULL);
        tot_nodes += wk[t].total_nodes;
        tot_restarts += wk[t].restarts;
        if (wk[t].max_depth_seen > max_d) max_d = wk[t].max_depth_seen;
        for (int d = 0; d <= C; d++) d_hits[d] += wk[t].depth_hits[d];
    }

    double dt = now_sec() - start_wall;
    printf("DONE N=%d K_%d M=%d C=%d sols=%d max_depth=%d/%d nodes=%lld (%.1f k/s) restarts=%lld time=%.3fs\n",
           N, N + 1, M, C, found_sols, max_d, C, tot_nodes,
           dt > 0 ? tot_nodes / (1000.0 * dt) : 0.0, tot_restarts, dt);
    printf("DEPTH_HIST:");
    for (int d = 0; d <= C; d++) if (d_hits[d]) printf(" d%d=%lld", d, d_hits[d]);
    printf("\n");

    free(th); free(wk);
    return 0;
}
