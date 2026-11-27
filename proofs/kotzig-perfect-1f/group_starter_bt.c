/*
 * group_starter_bt.c -- Pruned backtracking search for perfect starters in any
 * finite group G of odd order n (cyclic, non-cyclic abelian, or non-abelian),
 * using MRV branching and O(1) incremental path-endpoint short-cycle pruning
 * across all H = (n-1)/2 inverse-pair Hamiltonicity conditions.
 *
 * Compile: gcc -O3 -march=native -pthread -o group_starter_bt group_starter_bt.c
 * Usage:   ./group_starter_bt <group_spec> <threads> <seed> <nodelimit> <max_sec> [max_sols]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <time.h>

#define MAXN 101

static int N, H;
static uint8_t mul_tab[MAXN][MAXN];
static uint8_t inv_arr[MAXN];
static uint8_t diff_id[MAXN][MAXN];
static uint8_t d_rep[MAXN / 2];

static volatile int found_sols = 0;
static volatile int time_expired = 0;
static int max_sols = 1;
static long long nodelimit = 1000000;
static double max_seconds = 30.0;
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
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    *st = x;
    return x;
}

static inline int add_edge(uint8_t * restrict e, int u, int v, uint8_t *sv) {
    uint8_t e1 = e[u], e2 = e[v];
    if (e1 == (uint8_t)v) return 0;
    e[e1] = e2; e[e2] = e1;
    sv[0] = e1; sv[1] = e2;
    return 1;
}

static inline void undo_edge(uint8_t * restrict e, int u, int v, const uint8_t *sv) {
    e[sv[0]] = (uint8_t)u;
    e[sv[1]] = (uint8_t)v;
}

typedef struct {
    int tid;
    uint64_t rng;
    long long nodes;
    long long total_nodes;
    long long restarts;
    int max_depth;
    int stop_restart;
    int8_t mate[MAXN + 1];
    uint8_t dused[MAXN / 2];
    uint8_t end[MAXN / 2][MAXN + 1];
} Worker;

static void report(Worker *w) {
    pthread_mutex_lock(&out_mtx);
    found_sols++;
    printf("PERFECT_GRP N=%d K_%d tid=%d time=%.3fs nodes=%lld restarts=%lld PAIRS:",
           N, N + 1, w->tid, now_sec() - start_wall, w->total_nodes + w->nodes, w->restarts);
    for (int x = 1; x < N; x++) if (w->mate[x] > x) printf(" %d-%d", x, w->mate[x]);
    printf("\n");
    fflush(stdout);
    pthread_mutex_unlock(&out_mtx);
}

static void dfs(Worker *w, int depth) {
    if (w->stop_restart || found_sols >= max_sols || time_expired) return;
    if (depth > w->max_depth) w->max_depth = depth;
    if (depth == H) {
        report(w);
        if (found_sols >= max_sols) w->stop_restart = 1;
        return;
    }
    if (++w->nodes > nodelimit) { w->stop_restart = 1; return; }
    if ((w->nodes & 8191LL) == 0 && (now_sec() - start_wall) >= max_seconds) {
        time_expired = 1; w->stop_restart = 1; return;
    }

    int last = (depth == H - 1);
    int bx = -1, bc = 1 << 30;
    for (int x = 1; x < N; x++) {
        if (w->mate[x] >= 0) continue;
        int c = 0;
        for (int y = 1; y < N; y++) {
            if (y == x || w->mate[y] >= 0) continue;
            if (!w->dused[diff_id[x][y]]) c++;
        }
        if (c == 0) return;
        if (c < bc) { bc = c; bx = x; if (c == 1) break; }
    }

    int cand[MAXN], nc = 0;
    for (int y = 1; y < N; y++) {
        if (y == bx || w->mate[y] >= 0) continue;
        if (!w->dused[diff_id[bx][y]]) cand[nc++] = y;
    }
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(xorshift64(&w->rng) % (uint64_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }

    for (int ci = 0; ci < nc && !w->stop_restart && found_sols < max_sols && !time_expired; ci++) {
        int y = cand[ci];
        int dd = diff_id[bx][y];
        uint8_t sv[MAXN / 2][4];
        int j, ok = 1, half = 0;
        for (j = 0; j < H; j++) {
            uint8_t d = d_rep[j];
            if (!add_edge(w->end[j], bx, y, sv[j])) { ok = 0; half = 0; break; }
            int xd = mul_tab[bx][d], yd = mul_tab[y][d];
            if (!add_edge(w->end[j], xd, yd, sv[j] + 2)) {
                if (last) { sv[j][2] = 255; continue; }
                ok = 0; half = 1; break;
            }
        }
        if (ok) {
            w->mate[bx] = (int8_t)y; w->mate[y] = (int8_t)bx;
            w->dused[dd] = 1;
            dfs(w, depth + 1);
            w->dused[dd] = 0;
            w->mate[bx] = w->mate[y] = -1;
            j = H;
        }
        if (!ok && half) undo_edge(w->end[j], bx, y, sv[j]);
        for (int e = j - 1; e >= 0; e--) {
            uint8_t d = d_rep[e];
            int xd = mul_tab[bx][d], yd = mul_tab[y][d];
            if (sv[e][2] != 255) undo_edge(w->end[e], xd, yd, sv[e] + 2);
            undo_edge(w->end[e], bx, y, sv[e]);
        }
    }
}

static void *worker_main(void *arg) {
    Worker *w = (Worker *)arg;
    int V = N + 1;
    while (found_sols < max_sols && !time_expired) {
        memset(w->dused, 0, sizeof(w->dused));
        for (int v = 0; v < V; v++) w->mate[v] = -1;
        w->mate[0] = (int8_t)N; w->mate[N] = 0;
        for (int j = 0; j < H; j++) {
            for (int v = 0; v < V; v++) w->end[j][v] = (uint8_t)v;
            uint8_t sv[2];
            add_edge(w->end[j], 0, N, sv);
            add_edge(w->end[j], d_rep[j], N, sv);
        }
        w->nodes = 0;
        w->stop_restart = 0;
        dfs(w, 0);
        w->total_nodes += w->nodes;
        w->restarts++;
        xorshift64(&w->rng);
        if ((now_sec() - start_wall) >= max_seconds) { time_expired = 1; break; }
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
            int tmp; if (fscanf(fp, "%d", &tmp) != 1) exit(2);
            mul_tab[a][b] = (uint8_t)tmp;
        }
    fclose(fp);
    for (int a = 0; a < N; a++) {
        for (int b = 0; b < N; b++) if (mul_tab[a][b] == 0) { inv_arr[a] = (uint8_t)b; break; }
    }
    int pair_of[MAXN]; for (int a = 0; a < N; a++) pair_of[a] = -1;
    int pid = 0;
    for (int a = 1; a < N; a++) {
        if (pair_of[a] == -1) {
            pair_of[a] = pair_of[inv_arr[a]] = pid;
            d_rep[pid++] = (uint8_t)a;
        }
    }
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++)
            diff_id[a][b] = (a == b) ? 255 : (uint8_t)pair_of[mul_tab[a][inv_arr[b]]];
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "Usage: %s <group_spec> <threads> <seed> <nodelimit> <max_sec> [max_sols]\n", argv[0]);
        return 2;
    }
    load_group(argv[1]);
    int nthreads = atoi(argv[2]);
    if (nthreads < 1) nthreads = 1;
    if (nthreads > 2) nthreads = 2;
    global_seed = strtoull(argv[3], NULL, 10);
    nodelimit = atoll(argv[4]);
    max_seconds = atof(argv[5]);
    if (argc > 6) max_sols = atoi(argv[6]);

    start_wall = now_sec();
    pthread_t th[2];
    Worker wk[2];
    memset(wk, 0, sizeof(wk));
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
        if (wk[t].max_depth > max_d) max_d = wk[t].max_depth;
    }
    double dt = now_sec() - start_wall;
    printf("DONE_GRP_BT N=%d K_%d sols=%d max_depth=%d/%d nodes=%lld (%.1f k/s) restarts=%lld time=%.3fs\n",
           N, N + 1, found_sols, max_d, H, tot_nodes, dt > 0 ? tot_nodes / (1000.0 * dt) : 0.0, tot_restarts, dt);
    return 0;
}
