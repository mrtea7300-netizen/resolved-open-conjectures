# Upper bounds for ex(n, C4), 45 ≤ n ≤ 56, from a degree-class linear program

Status: **proof (reviewed)** (Gemini 4 Neon review PASS, `reviews/2026-11-27-gemini-4-neon.md`; author Claude Opus 5.5).

Written by Claude Opus 5.5, 2026-11-27. The LP was first proposed by a Gemini agent
(uncommitted `upper_bound_lp.py`). The proofs, code and certificates here are independent of it:
no code is shared.

Throughout, G = (V, E) is a simple graph with n = |V| vertices and m = |E| edges, and it
contains no 4-cycle (it is *C4-free*). N(v) is the neighbourhood of v, N[v] = N(v) ∪ {v}, and
d(v) = |N(v)|. ex(n, C4) is the largest m for which such a graph exists (OEIS A006855, offset 1).

## 1. Facts about C4-free graphs

**Fact 0.** If x ≠ y, then |N(x) ∩ N(y)| ≤ 1.
*Proof.* If u ≠ w both lie in N(x) ∩ N(y), then x, u, y, w are four distinct vertices
(u, w ∉ {x, y} because there are no loops) and x–u–y–w–x is a 4-cycle. ∎

**Lemma 1.** For every v, each vertex u ∈ N(v) has at most one neighbour inside N(v). So the
graph G[N(v)] is a matching plus isolated vertices.
*Proof.* A neighbour of u inside N(v) is a common neighbour of u and v. By Fact 0 (u ≠ v) there is
at most one. ∎

For a vertex v, let t(v) be the number of edges of G[N(v)], and let s(v) be the number of
vertices of N(v) that are isolated in G[N(v)]. By Lemma 1, d(v) = 2 t(v) + s(v). Hence
**s(v) ≡ d(v) (mod 2)**, so **s(v) ≥ d(v) mod 2** and **2 t(v) ≤ d(v) − (d(v) mod 2)**.

**Lemma 2.** For u ∈ N(v): the edge uv lies in a triangle ⇔ u is matched in G[N(v)] ⇔
|N(u) ∩ N(v)| = 1. Otherwise N(u) ∩ N(v) = ∅.
*Proof.* A triangle uvw means w ∈ N(u) ∩ N(v), i.e. u has the neighbour w inside N(v). By
Fact 0, |N(u) ∩ N(v)| ≤ 1. ∎

## 2. The constraints

Let V_d be the set of vertices of degree d, and let n_d = |V_d| for 0 ≤ d ≤ n − 1. For i < j let
e_{i,j} be the number of edges with one end in V_i and the other in V_j, and let e_{d,d} be the
number of edges with both ends in V_d. All of these are nonnegative integers. Write
f(d) = d(d − 1) + (d mod 2) and g(d) = n − 1 + d − (d mod 2).

**(E1)** Σ_d n_d = n.  *(Every vertex has exactly one degree in 0..n − 1.)*

**(E2)** Σ_d d·n_d = 2m.  *(Handshake lemma.)*

**(E3_d)** Σ_{j ≠ d} e_{d,j} + 2 e_{d,d} = d·n_d for each d.
*Proof.* Count pairs (v, edge at v) with v ∈ V_d. Each v ∈ V_d gives d of them, so the total is
d·n_d. An edge between V_d and V_j (j ≠ d) has exactly one end in V_d, so it is counted once. An
edge inside V_d is counted twice. ∎

**(I4)** Σ_d f(d)·n_d ≤ n(n − 1), i.e. Σ_v [C(d(v), 2) + (d(v) mod 2)/2] ≤ C(n, 2).
*Proof.* Split the C(n, 2) unordered pairs {x, y} of distinct vertices by their number of common
neighbours. By Fact 0 this number is 0 or 1. Call the two classes P_0 and P_1.
- |P_1| = Σ_v C(d(v), 2). Map each pair {x, y} ⊆ N(v) with x ≠ y to the pair {x, y}. It lies in
  P_1, because v is a common neighbour. Every pair in P_1 arises from exactly one v, namely its
  unique common neighbour. So this map is a bijection from {(v, {x, y}) : {x, y} ⊆ N(v)} onto P_1.
- Let E_0 ⊆ E be the set of edges in no triangle. An edge uv ∈ E_0 has no common neighbour, so
  E_0 ⊆ P_0. By Lemma 2, for each v the edges of E_0 at v are exactly the edges vu with u
  isolated in G[N(v)], so there are s(v) of them. Counting the pairs (v, edge of E_0 at v) gives
  2|E_0| = Σ_v s(v) ≥ Σ_v (d(v) mod 2).
- P_0 and P_1 are disjoint, so |P_1| + |E_0| ≤ |P_1| + |P_0| = C(n, 2). Substituting the two
  counts and multiplying by 2 gives Σ_v [d(v)(d(v) − 1) + (d(v) mod 2)] ≤ n(n − 1). Group the
  vertices by degree. ∎

(Without the parity term this is the classical counting behind Reiman's bound.)

**(I5_d)** Σ_{j ≠ d} j·e_{d,j} + 2d·e_{d,d} ≤ g(d)·n_d for each d.
*Proof.* Fix v with d(v) = d. For each u ∈ N(v), let A_u = N(u) \ N[v] ⊆ V \ N[v]. Two facts:
- The sets A_u (u ∈ N(v)) are pairwise disjoint. If w ∈ A_u ∩ A_{u'} with u ≠ u', then w ∉ N[v],
  so w ≠ v, and u, u' are two common neighbours of v and w. This contradicts Fact 0.
- |A_u| = d(u) − 1 − |N(u) ∩ N(v)|. Here N(u) ∩ N[v] = {v} ∪ (N(u) ∩ N(v)), a disjoint union,
  because v ∈ N(u) and v ∉ N(v).

So Σ_{u ∈ N(v)} (d(u) − 1 − |N(u) ∩ N(v)|) ≤ |V \ N[v]| = n − 1 − d. By Lemma 2,
Σ_{u ∈ N(v)} |N(u) ∩ N(v)| = (number of matched vertices of G[N(v)]) = 2 t(v) ≤ d − (d mod 2).
Hence

  Σ_{u ∈ N(v)} d(u) ≤ n − 1 − d + d + 2t(v) ≤ n − 1 + d − (d mod 2) = g(d).       (★)

Sum (★) over v ∈ V_d. The left side counts ordered pairs (v, u) with v ∈ V_d and uv ∈ E, each
weighted by d(u). An edge between V_d and V_j (j ≠ d) contributes exactly one such pair, with
weight j. An edge inside V_d contributes two pairs, each with weight d. ∎

**(I6) (induction; used only at n = 45).** If ex(n − 1, C4) ≤ U and G has exactly m edges, then
every vertex has degree ≥ m − U, so n_d = 0 for d < m − U.
*Proof.* G − v is a C4-free graph on n − 1 vertices with m − d(v) edges, so m − d(v) ≤ U. ∎

**Averaging bound.** If ex(n − 1, C4) ≤ U, then ex(n, C4) ≤ ⌊nU/(n − 2)⌋ for n ≥ 3.
*Proof.* Summing (I6) over all v gives nm − 2m ≤ nU. ∎ (This is Alekseyev's formula in OEIS.)

**The LP.** Fix n, m and dmin ≥ 0. Let D = {dmin, …, n − 1}. The variables are n_d (d ∈ D) and
e_{i,j} (i ≤ j in D), all real and ≥ 0. The constraints are (E1), (E2), (E3_d) and (I5_d) for
d ∈ D, and (I4), with all sums restricted to D.

**Proposition 1.** Suppose some C4-free graph on n vertices has exactly m edges and minimum
degree ≥ dmin. Then the LP for (n, m, dmin) has a feasible point.
*Proof.* Every vertex has a degree in D, so the counts n_d, e_{i,j} of the graph involve only
degrees in D. By (E1)–(I5_d) they satisfy every constraint, and they are nonnegative. ∎

**Corollary.** Suppose the LP for (n, m, dmin) is infeasible, and either dmin = 0, or
dmin = m − U with ex(n − 1, C4) ≤ U proved. Then ex(n, C4) ≤ m − 1.
*Proof.* Suppose ex(n, C4) ≥ m. Then some C4-free graph has n vertices and at least m edges.
Deleting edges keeps it C4-free, so some C4-free graph has exactly m edges. By (I6) its minimum
degree is ≥ dmin. Proposition 1 then gives a feasible point, which is a contradiction. ∎

## 3. Farkas certificates

Choose multipliers a, b, c_d (any sign), and z, w_d ≥ 0, for (E1), (E2), (E3_d), (I4) and
(I5_d) respectively. Multiply each constraint by its multiplier and add. Equalities stay
equalities, and inequalities keep their direction because z, w_d ≥ 0. Any feasible point then
satisfies

  Σ_{d∈D} n_d·[a + b d − c_d d + z f(d) − w_d g(d)]
   + Σ_{i<j} e_{i,j}·[c_i + c_j + j w_i + i w_j] + Σ_d e_{d,d}·[2c_d + 2d w_d]
  ≤ a n + 2m b + z n(n − 1).

The coefficient of e_{i,j} (i < j) works out as follows. The variable e_{i,j} appears with
coefficient 1 in (E3_i) and in (E3_j). It appears with coefficient j in (I5_i) and with
coefficient i in (I5_j). The variable e_{d,d} appears with coefficient 2 in (E3_d) and 2d in
(I5_d).

Suppose that

- (C0) z ≥ 0 and w_d ≥ 0;
- (C1) a + b d − c_d d + z f(d) − w_d g(d) ≥ 0 for each d ∈ D;
- (C2) c_i + c_j + j w_i + i w_j ≥ 0 for i < j in D;
- (C3) 2c_d + 2d w_d ≥ 0;
- (C4) a n + 2m b + z n(n − 1) < 0.

Then the left side is ≥ 0 at every nonnegative point and the right side is < 0, so the LP is
infeasible. These are exactly the conditions tested by `check_certificates.py`, in integer
arithmetic. Each file `data/cert_n<n>_m<m>.txt` lists integers a, b, z and (c_d, w_d) for all
d ∈ D.

## 4. Results

**Theorem (draft).** ex(n, C4) ≤ U(n) for

| n | 45 | 46 | 47 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| U(n) | 157 | 163 | 169 | 174 | 180 | 186 | 192 | 197 | 202 | 208 | 214 | 220 |

*Proof.* For each n there is a certificate at m = U(n) + 1 that passes (C0)–(C4). Apply the
Corollary. For n ≠ 45 the certificate has dmin = 0, so these bounds use only (E1)–(I5) and
depend on no other result.

For n = 45 the certificate has dmin = 7 = 158 − 151, so it needs ex(44, C4) ≤ 151. That bound
follows from the averaging bound applied four times, starting at ex(40, C4) = 127:
⌊41·127/39⌋ = 133, ⌊42·133/40⌋ = 139, ⌊43·139/41⌋ = 145, ⌊44·145/42⌋ = 151.
ex(40, C4) = 127 is a computer result of B. McKay, recorded in OEIS A006855 ("a(40) from Brendan
McKay, communicated by Max Alekseyev, Mar 13 2023"). It is the same input that Alekseyev's
OEIS bounds use. We did not re-derive it. The bound at 45 is therefore exactly as reliable as
that computation. ∎

**Short hand-checkable proofs for n = 49, 50, 51.** These certificates have a = 48, b = −13,
z = 1 and all c_d = w_d = 0, so only (I4) is used. In general, let p be even and
φ(d) = (d − p)(d − p − 2) + (d mod 2). Then φ(d) ≥ 0 for every integer d: the product is
negative only at d = p + 1, which is odd, and there φ = −1 + 1 = 0. Summing φ(d(v)) ≥ 0 over v,
and using (I4) in the form Σ d(v)² ≤ n(n − 1) + 2m − #odd, gives

  0 ≤ Σ_v φ(d(v)) = Σ d(v)² − (2p + 2)·2m + p(p + 2) n + #odd ≤ n(n − 1) + p(p + 2) n − (4p + 2) m.

So **m ≤ n(n − 1 + p(p + 2)) / (4p + 2)** for every even p. With p = 6 this is m ≤ n(n + 47)/26:
- n = 49: 49·96/26 = 180.9…, so m ≤ 180.
- n = 50: 50·97/26 = 186.5…, so m ≤ 186.
- n = 51: 51·98/26 = 192.2…, so m ≤ 192.

(The same bound with p = 8 gives 228 at n = 57, which equals Reiman's bound, so n = 57 is not
an improvement.) The parity term is essential here. Without it, the same argument with
φ(d) = (d − p)(d − p − 1), any integer p, gives m ≤ n(n − 1 + p(p + 1))/(4p). At n = 49 the best
choice, p = 7, gives 49·104/28 = 182, which is Reiman's value.

**What is not claimed.** The LP gives U(n) and nothing better: it is feasible at m = U(n), and
an exact rational feasible point was constructed and checked (`python lp_c4.py --run`). For n = 41–44
it gives nothing below the averaging bound (= Alekseyev's bounds). For n = 57 it gives 228, which
equals Reiman's bound.

## 5. Checks performed (2026-11-27)

- `python check_certificates.py`: all 13 certificate files pass (C0)–(C4) in exact integer
  arithmetic. Tampered copies (b changed, m lowered, dmin changed) are rejected.
- `python test_constraints.py --nmax 10 --mckay <dir> --random 3000` (about 50 s) checked
  Fact 0, Lemma 1, the two counts in the proof of (I4), (I4) itself, the disjointness in (I5),
  (★) at every vertex, and Proposition 1 (the graph's own counts satisfy the LP exactly). It ran
  this on
  - every C4-free graph on ≤ 10 vertices up to isomorphism. The counts 1, 2, 4, 8, 18, 44, 117,
    351, 1230, 5069 match OEIS A006786.
  - all 231 graphs in McKay–Afzaly `c4_all.tar.gz` (n = 4..49, including the "maybe" graphs
    for n = 41..49). For n ≤ 40 it also checked (I6) with dmin = a(n) − a(n − 1), and at n = 41 with McKay's lower bound 132 in place of a(41).
  - the polarity graphs ER_2, ER_3, ER_5, ER_7 (n = 7, 13, 31, 57).
  - 3000 random maximal C4-free graphs with n = 10..60.

  No violation was found. (I4) and (★) are tight on some exhaustive and some McKay graphs (slack 0).
- `python lp_c4.py --sanity`: the LP has an exact rational feasible point at m = a(n) for all
  2 ≤ n ≤ 40 (with dmin = 0 and with (I6) from a(n − 1)). It also has one at McKay's lower bounds
  for n = 41..49 (with dmin = 0 and with (I6) from our U(n − 1)). The test above already gives
  integer feasible points from the actual graphs.

GAP: none known in the argument. Its only external input is ex(40, C4) = 127, which is used at
n = 45 only.
