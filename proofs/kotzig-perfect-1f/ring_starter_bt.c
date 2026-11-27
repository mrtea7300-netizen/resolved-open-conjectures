/*
 * ring_starter_bt.c -- Generalized U-invariant starter backtracking search
 * over any finite commutative ring R of odd order n with admissible subgroup U <= R*,
 * using exact-cover MRV branching + incremental O(1) short-cycle pruning across
 * all c = (n-1)/(2|U|) G-orbit Hamiltonicity conditions.
 *
 * Compile (Linux/WSL):
 *   gcc -O3 -march=native -pthread -o ring_starter_bt ring_starter_bt.c
 *
 * Usage:
 *   ./ring_starter_bt <spec_file> <threads> <seed> <nodelimit_per_restart> <max_restarts> [max_sols]
 *
 * Respects thread cap (<= 2 threads on shared 6-core host).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <time.h>

#define MAXN 5000
#define MAXC 64

static int N, M, C, NUM_U;
static int *neg_arr;
static int *u_orb_id;
static int *g_orb_id;
static int *g_reps;
static int *u_orb_rep; /* canonical element of each U-orbit 0..2C-1 */
static int *mul_u;     /* [M * N] */
static int *add_tab;   /* [N * N] */
static int *sub_tab;   /* [N * N], sub_tab[a*N + b] = a - b */

/* Precomputed: for each U-orbit o (0..2C-1) and each element y in R\{0} not in o,
   its difference G-orbit diff_g[o][y] = g_orb_id[r_o - y] */
static int *u_orb_elems; /* [2C * M] elements of each U-orbit */

static volatile int found_sols = 0;
static int max_sols = 1;
static long long nodelimit = 1000000;
static long long max_restarts = 1000;
static uint64_t global_seed = 1;
static pthread_mutex_t out_mtx = PTHREAD_MUTEX_INITIALIZER;
static double start_wall = 0.0;

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

typedef struct {
    int tid;
    uint64_t rng;
    long long nodes;
    long long total_nodes;
    long long restarts;
    int max_depth_seen;
    int stop_restart;
    uint8_t u_used[2 * MAXC];
    uint8_t g_used[MAXC];
    int rep_a[MAXC];
    int rep_b[MAXC];
    int placed;
    /* end[j * (N+1) + v] = other endpoint of path containing v in partial graph H_j */
    uint16_t *end;
    /* Undo stack per depth: at most C * 2 * M * 2 = 4*C*M saved endpoints per depth!
       Actually store per-depth undo buffer dynamically. */
    uint16_t *sv_e1;
    uint16_t *sv_e2;
    uint16_t *sv_u;
    uint16_t *sv_v;
    int *sv_j;
} Worker;

static inline int add_edge(uint16_t *e, int u, int v, uint16_t *o1, uint16_t *o2) {
    uint16_t e1 = e[u];
    uint16_t e2 = e[v];
    if (e1 == (uint16_t)v) return 0; /* closes cycle */
    e[e1] = e2;
    e[e2] = e1;
    *o1 = e1;
    *o2 = e2;
    return 1;
}

static inline void undo_edge(uint16_t *e, uint16_t u, uint16_t v, uint16_t e1, uint16_t e2) {
    e[e1] = u;
    e[e2] = v;
}

static void report_solution(Worker *w) {
    pthread_mutex_lock(&out_mtx);
    found_sols++;
    double dt = now_sec() - start_wall;
    printf("SOLUTION #%d (tid=%d, time=%.3fs, nodes=%lld, restarts=%lld) REPS:",
           found_sols, w->tid, dt, w->total_nodes + w->nodes, w->restarts);
    for (int i = 0; i < C; i++) {
        printf(" %d-%d", w->rep_a[i], w->rep_b[i]);
    }
    printf("\n");
    fflush(stdout);
    pthread_mutex_unlock(&out_mtx);
}

static void dfs(Worker *w, int depth) {
    if (w->stop_restart || found_sols >= max_sols) return;
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

    int last = (depth == C - 1);

    /* MRV over uncovered U-orbits: pick uncovered U-orbit o with fewest valid partners y */
    int best_o = -1;
    int best_cnt = 1 << 30;
    for (int o = 0; o < NUM_U; o++) {
        if (w->u_used[o]) continue;
        int ra = u_orb_rep[o];
        const int *sub_row = sub_tab + ra * N;
        int cnt = 0;
        for (int o2 = 0; o2 < NUM_U; o2++) {
            if (o2 == o || w->u_used[o2]) continue;
            const int *elems = u_orb_elems + o2 * M;
            for (int k = 0; k < M; k++) {
                int y = elems[k];
                int g = g_orb_id[sub_row[y]];
                if (!w->g_used[g]) cnt++;
            }
        }
        if (cnt == 0) return;
        if (cnt < best_cnt) {
            best_cnt = cnt;
            best_o = o;
            if (cnt == 1) break;
        }
    }

    int ra = u_orb_rep[best_o];
    const int *sub_row = sub_tab + ra * N;
    int *cand_y = (int *)alloca((size_t)best_cnt * sizeof(int));
    int nc = 0;
    for (int o2 = 0; o2 < NUM_U; o2++) {
        if (o2 == best_o || w->u_used[o2]) continue;
        const int *elems = u_orb_elems + o2 * M;
        for (int k = 0; k < M; k++) {
            int y = elems[k];
            int g = g_orb_id[sub_row[y]];
            if (!w->g_used[g]) cand_y[nc++] = y;
        }
    }

    /* Fisher-Yates shuffle for randomized Las Vegas ordering */
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(xorshift64(&w->rng) % (uint64_t)(i + 1));
        int tmp = cand_y[i]; cand_y[i] = cand_y[j]; cand_y[j] = tmp;
    }

    /* Per-depth undo slice: up to C * 2 * M edges */
    int slice_cap = C * 2 * M;
    int base_off = depth * slice_cap;
    uint16_t *sv_e1 = w->sv_e1 + base_off;
    uint16_t *sv_e2 = w->sv_e2 + base_off;
    uint16_t *sv_u  = w->sv_u  + base_off;
    uint16_t *sv_v  = w->sv_v  + base_off;
    int *sv_j       = w->sv_j  + base_off;

    int V = N + 1;
    for (int ci = 0; ci < nc && !w->stop_restart && found_sols < max_sols; ci++) {
        int y = cand_y[ci];
        int o2 = u_orb_id[y];
        int g = g_orb_id[sub_row[y]];

        /* Add the U-orbit of pairs {u_k * ra, u_k * y} to all C graphs H_0..H_{C-1} */
        int n_added = 0;
        int ok = 1;
        for (int j = 0; j < C && ok; j++) {
            uint16_t *e = w->end + (size_t)j * V;
            int dj = g_reps[j];
            const int *add_dj = add_tab + dj * N;
            int closed_count = 0;
            for (int k = 0; k < M; k++) {
                int ux = mul_u[k * N + ra];
                int uy = mul_u[k * N + y];
                uint16_t e1, e2;
                /* Edge from F_0 */
                if (!add_edge(e, ux, uy, &e1, &e2)) {
                    ok = 0;
                    break;
                }
                sv_j[n_added] = j; sv_u[n_added] = ux; sv_v[n_added] = uy;
                sv_e1[n_added] = e1; sv_e2[n_added] = e2; n_added++;

                /* Translated edge from F_{dj} */
                int tx = add_dj[ux];
                int ty = add_dj[uy];
                if (!add_edge(e, tx, ty, &e1, &e2)) {
                    if (last && k == M - 1 && closed_count == 0) {
                        /* Very last edge in H_j closes the unique Hamiltonian cycle! */
                        closed_count = 1;
                    } else {
                        ok = 0;
                        break;
                    }
                } else {
                    sv_j[n_added] = j; sv_u[n_added] = tx; sv_v[n_added] = ty;
                    sv_e1[n_added] = e1; sv_e2[n_added] = e2; n_added++;
                }
            }
            if (ok && last && closed_count != 1) {
                /* Should not happen if math is right, defensive check */
                ok = 0;
            }
        }

        if (ok) {
            w->u_used[best_o] = 1;
            w->u_used[o2] = 1;
            w->g_used[g] = 1;
            w->rep_a[depth] = ra;
            w->rep_b[depth] = y;
            dfs(w, depth + 1);
            w->u_used[best_o] = 0;
            w->u_used[o2] = 0;
            w->g_used[g] = 0;
        }

        /* Undo in exact reverse order */
        for (int s = n_added - 1; s >= 0; s--) {
            uint16_t *e = w->end + (size_t)sv_j[s] * V;
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
    w->sv_j  = malloc((size_t)total_undo * sizeof(int));

    for (long long r = 0; r < max_restarts && found_sols < max_sols; r++) {
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
    }

    free(w->end);
    free(w->sv_e1); free(w->sv_e2); free(w->sv_u); free(w->sv_v); free(w->sv_j);
    return NULL;
}

static void load_spec(const char *path) {
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
    neg_arr = malloc((size_t)N * sizeof(int));
    u_orb_id = malloc((size_t)N * sizeof(int));
    g_orb_id = malloc((size_t)N * sizeof(int));
    g_reps = malloc((size_t)C * sizeof(int));
    mul_u = malloc((size_t)M * N * sizeof(int));
    add_tab = malloc((size_t)N * N * sizeof(int));
    sub_tab = malloc((size_t)N * N * sizeof(int));
    u_orb_rep = malloc((size_t)NUM_U * sizeof(int));
    u_orb_elems = malloc((size_t)NUM_U * M * sizeof(int));

    for (int i = 0; i < N; i++) if (fscanf(fp, "%d", &neg_arr[i]) != 1) exit(2);
    for (int i = 0; i < N; i++) if (fscanf(fp, "%d", &u_orb_id[i]) != 1) exit(2);
    for (int i = 0; i < N; i++) if (fscanf(fp, "%d", &g_orb_id[i]) != 1) exit(2);
    for (int i = 0; i < C; i++) if (fscanf(fp, "%d", &g_reps[i]) != 1) exit(2);
    for (int k = 0; k < M; k++)
        for (int a = 0; a < N; a++)
            if (fscanf(fp, "%d", &mul_u[k * N + a]) != 1) exit(2);
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++)
            if (fscanf(fp, "%d", &add_tab[a * N + b]) != 1) exit(2);
    fclose(fp);

    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++)
            sub_tab[a * N + b] = add_tab[a * N + neg_arr[b]];

    int *cnt = calloc((size_t)NUM_U, sizeof(int));
    for (int a = 1; a < N; a++) {
        int o = u_orb_id[a];
        if (cnt[o] == 0) u_orb_rep[o] = a;
        u_orb_elems[o * M + cnt[o]++] = a;
    }
    free(cnt);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "Usage: %s <spec> <threads> <seed> <nodelimit> <max_restarts> [max_sols]\n", argv[0]);
        return 2;
    }
    load_spec(argv[1]);
    int nthreads = atoi(argv[2]);
    if (nthreads < 1) nthreads = 1;
    if (nthreads > 2) {
        fprintf(stderr, "Capping threads from %d to 2 (shared-host policy).\n", nthreads);
        nthreads = 2;
    }
    global_seed = strtoull(argv[3], NULL, 10);
    nodelimit = atoll(argv[4]);
    max_restarts = atoll(argv[5]);
    if (argc > 6) max_sols = atoi(argv[6]);

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
    for (int t = 0; t < nthreads; t++) {
        pthread_join(th[t], NULL);
        tot_nodes += wk[t].total_nodes;
        tot_restarts += wk[t].restarts;
        if (wk[t].max_depth_seen > max_d) max_d = wk[t].max_depth_seen;
    }

    double dt = now_sec() - start_wall;
    printf("DONE N=%d K_%d M=%d C=%d sols=%d max_depth=%d/%d nodes=%lld restarts=%lld time=%.3fs\n",
           N, N + 1, M, C, found_sols, max_d, C, tot_nodes, tot_restarts, dt);

    free(th); free(wk);
    return 0;
}
