/*
 * Standalone brute-force C verifier for a perfect 1-factorization (P1F) of K_{2n}.
 * No shared code with any search engine. Checks directly from the definition:
 *   1. 2n - 1 matchings, each covering 0..2n-1 once.
 *   2. All n*(2n-1) edges distinct (partition of E(K_{2n})).
 *   3. Every unordered pair (i, j) forms a single Hamiltonian cycle of length 2n.
 *
 * Compile: gcc -O3 -o verify_p1f verify_p1f.c
 * Usage:   ./verify_p1f <matchings.txt>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <matchings.txt>\n", argv[0]);
        return 2;
    }
    FILE *fp = fopen(argv[1], "r");
    if (!fp) { perror("fopen"); return 2; }

    /* First pass: count matchings and edges per matching */
    int num_f = 0, half = -1;
    char *line = NULL;
    size_t cap = 0;
    ssize_t len;
    while ((len = getline(&line, &cap, fp)) != -1) {
        char *p = line;
        while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
        if (*p == '\0' || *p == '#') continue;
        int cnt = 0;
        while (*p) {
            while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
            if (!*p) break;
            cnt++;
            while (*p && *p != ' ' && *p != '\t' && *p != '\r' && *p != '\n') p++;
        }
        if (half < 0) half = cnt;
        else if (cnt != half) {
            fprintf(stderr, "FAIL: factor %d has %d edges, expected %d\n", num_f, cnt, half);
            return 1;
        }
        num_f++;
    }
    int vcount = num_f + 1;
    if (num_f < 3 || (num_f & 1) == 0 || vcount != 2 * half) {
        fprintf(stderr, "FAIL: bad dimensions num_f=%d half=%d\n", num_f, half);
        return 1;
    }

    int *adj = malloc((size_t)num_f * vcount * sizeof(int));
    uint8_t *edge_seen = calloc((size_t)vcount * vcount, 1);
    if (!adj || !edge_seen) { fprintf(stderr, "OOM\n"); return 2; }

    rewind(fp);
    int fi = 0;
    long long total_edges = 0;
    while ((len = getline(&line, &cap, fp)) != -1) {
        char *p = line;
        while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
        if (*p == '\0' || *p == '#') continue;
        int *mate = adj + (size_t)fi * vcount;
        for (int v = 0; v < vcount; v++) mate[v] = -1;
        while (*p) {
            while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
            if (!*p) break;
            int u = -1, v = -1, consumed = 0;
            if (sscanf(p, "%d-%d%n", &u, &v, &consumed) != 2 || consumed <= 0) {
                fprintf(stderr, "FAIL: bad edge token in factor %d\n", fi);
                return 1;
            }
            p += consumed;
            if (u < 0 || u >= vcount || v < 0 || v >= vcount || u == v) {
                fprintf(stderr, "FAIL: invalid edge %d-%d in factor %d\n", u, v, fi);
                return 1;
            }
            if (mate[u] != -1 || mate[v] != -1) {
                fprintf(stderr, "FAIL: repeated vertex in factor %d (%d-%d)\n", fi, u, v);
                return 1;
            }
            mate[u] = v;
            mate[v] = u;
            int a = u < v ? u : v, b = u < v ? v : u;
            if (edge_seen[(size_t)a * vcount + b]) {
                fprintf(stderr, "FAIL: duplicate edge %d-%d in factor %d\n", a, b, fi);
                return 1;
            }
            edge_seen[(size_t)a * vcount + b] = 1;
            total_edges++;
        }
        for (int v = 0; v < vcount; v++) {
            if (mate[v] < 0) {
                fprintf(stderr, "FAIL: uncovered vertex %d in factor %d\n", v, fi);
                return 1;
            }
        }
        fi++;
    }
    fclose(fp);
    free(line);
    free(edge_seen);

    long long expected_edges = (long long)vcount * (vcount - 1) / 2;
    if (total_edges != expected_edges) {
        fprintf(stderr, "FAIL: total_edges=%lld expected=%lld\n", total_edges, expected_edges);
        return 1;
    }

    struct timespec ts0, ts1;
    clock_gettime(CLOCK_MONOTONIC, &ts0);
    long long pairs = 0;
    for (int i = 0; i < num_f; i++) {
        const int *mi = adj + (size_t)i * vcount;
        for (int j = i + 1; j < num_f; j++) {
            const int *mj = adj + (size_t)j * vcount;
            int cur = 0, steps = 0;
            do {
                cur = mj[mi[cur]];
                steps += 2;
            } while (cur != 0 && steps <= vcount);
            if (steps != vcount) {
                fprintf(stderr, "FAIL: pair (%d, %d) cycle length %d != %d\n", i, j, steps, vcount);
                free(adj);
                return 1;
            }
            pairs++;
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &ts1);
    double dt = (ts1.tv_sec - ts0.tv_sec) + 1e-9 * (ts1.tv_nsec - ts0.tv_nsec);
    printf("VERIFIED PERFECT 1-FACTORIZATION OF K_%d: %d perfect matchings, %lld edges partitioned, "
           "all %lld pairs form a single Hamiltonian %d-cycle (%.3f s).\n",
           vcount, num_f, total_edges, pairs, vcount, dt);
    free(adj);
    return 0;
}
