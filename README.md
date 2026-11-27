# Resolved Open Conjectures in Number Theory & Combinatorics

A clean, self-contained archive of **39 resolved open problems** from the literature and the OEIS — each backed by a complete proof, a formal Lean 4 verification, or an independently verified counterexample and certificate.

Every folder contains the verbatim problem statement with primary source citation, the proof or counterexample, and standalone code/certificates to reproduce the verification from scratch.

---

## Highlights

- **Wang & Sun (*The Electronic Journal of Combinatorics* 33(2), 2026, #P2.64) Conjecture 1(1) / OEIS A357130** — Disproved with a 3-line universal counterexample valid in every additive group with $p(G) \ge 4$, plus an infinite odd-$n$ family, formally verified in zero-dependency Lean 4 ([`counterexamples/A357130/`](counterexamples/A357130/)).
- **Erdős–Lacampagne–Selfridge (1993) Conjectures 1 & 2 (`erdos-1094`)** — Counterexamples $\binom{31152939}{1772289}$ (least prime factor $19$, $n/k = 17.58 > 17\frac{1}{8}$) and $\binom{57074}{22050}$ (least prime factor $23$), kernel-checked in Lean 4 ([`counterexamples/erdos-1094/`](counterexamples/erdos-1094/)).
- **Greathouse's 255 Conjecture (OEIS A156695)** — Disproved with the smallest counterexample $n = 275{,}984{,}581{,}255{,}575$ (exhaustively verified below $2.858 \times 10^{14}$, with explicit divisor certificates) ([`counterexamples/greathouse-255/`](counterexamples/greathouse-255/)).
- **Kellner / Alekseyev Bernoulli Polynomial Derivative Conjecture (OEIS A094960)** — Proved unconditionally that `A094960` is finite with largest term $60$, formalized in Lean 4 ([`proofs/A094960/`](proofs/A094960/)).
- **Cheng–Lin (`arXiv:2603.21680v3`) Conjecture 3.30** — Proved for all $d \ge 1$ that the Chow polynomial second-moment inequality is a nonnegative linear combination of flag monotonicity inequalities ([`proofs/cheng-lin-chow-moments/`](proofs/cheng-lin-chow-moments/)).
- **Turán Numbers $\operatorname{ex}(n, C_4)$ (OEIS A006855)** — New upper bounds for $45 \le n \le 56$ with exact LP certificates ([`proofs/turan-c4/`](proofs/turan-c4/)).
- **Kotzig's Perfect 1-Factorization Conjecture** — Explicit perfect 1-factorization constructed and verified for the open order $K_{1682}$ ([`proofs/kotzig-perfect-1f/`](proofs/kotzig-perfect-1f/)).
- **Sun (`arXiv:2302.08315`) Conjectures 4.2–4.4 (OEIS A360278)** — All three recurrent-matrix determinant formulas proved for all $n \ge 1$ and formalized in zero-dependency Lean 4 ([`proofs/A360278/`](proofs/A360278/)).

---

## 1. Counterexamples & Disproofs (20)

| Problem | Conjecture Summary | Counterexample / Result | Verification | Folder |
|---|---|---|---|---|
| **Erdős #1094** | Erdős–Lacampagne–Selfridge (1993) Conj. 1, Conj. 2 & Remark on least prime factor of $\binom{n}{k}$ | $\binom{31152939}{1772289}$ (Conj. 2), $\binom{57074}{22050}$ (Conj. 1), $\binom{23799}{3159}$ (Remark) | **Lean 4** + independent scripts | [`counterexamples/erdos-1094/`](counterexamples/erdos-1094/) |
| **Greathouse 255 (`A156695`)** | Every odd $n > 5$ not of the form $p + 2^a + 2^b$ is divisible by $255$ | Smallest: $n = 275{,}984{,}581{,}255{,}575$ ($n \equiv 15 \pmod{17}$) | Divisor certificates + exhaustive search | [`counterexamples/greathouse-255/`](counterexamples/greathouse-255/) |
| **Wang–Sun 2026 (`A357130`)** | *E-JC* 33(2) (2026) #P2.64 Conj. 1(1): lower bound on adjacent-distinct sumsets $L(A_1,\dots,A_n)$ | $A_1 = A_3 = \{0,g,2g\}$, $A_2 = \{0,2g\}$ ($3 < 4$), plus infinite odd-$n$ family | **Lean 4** (zero-dep) + Python | [`counterexamples/A357130/`](counterexamples/A357130/) |
| **Sun `arXiv:1208.2683` Conj. 2.1** | Generalized Mandl inequality $\frac{1}{n}\sum p_k^\alpha < \frac{p_n^\alpha}{\alpha+1}$ for $n \ge 2\lceil\alpha\rceil^2+\lceil\alpha\rceil+6$ | Fails at $n = 9$ for $\alpha \in (0, 0.00233636\dots]$; proved unconditionally for $n \ge 10, \alpha \in (0,1]$ | Certified interval arithmetic + proof | [`counterexamples/sun-1208.2683-conj2.1/`](counterexamples/sun-1208.2683-conj2.1/) |
| **A349530 (Conj. 3)** | Discriminator $D(n)$ of $k(k^4+1)$ follows $3\cdot 5^a / 5^{a+1}$ law beyond $n = 630$ | Infinite family $n \in \{5^a+1,\dots,5^a+5\}$ for $a = 5k+4$ (smallest: $1{,}953{,}126$) | **Lean 4** (zero-dep) + Python | [`counterexamples/A349530/`](counterexamples/A349530/) |
| **A389880 & A321651 (Conj. 2)** | Permutation $f$ of $\{1,\dots,n\}$ with every $k f(k)$ practical | Fails at $n = 146$ via explicit Hall witness ($\lvert S\rvert = 72 > \lvert N(S)\rvert = 71$) | Independent subset-sum check | [`counterexamples/A389880/`](counterexamples/A389880/) |
| **A224210** | Least prime $p$ with $\sum_{k=0}^n (k+1)^2 x^{n-k}$ irreducible mod $p$ satisfies $a(n) \le p_{4n-3}$ | Fails at $n = 63$: $a(63) = 1627 = p_{258} > p_{249} = 1579$ | `python-flint` + `SymPy` | [`counterexamples/A224210/`](counterexamples/A224210/) |
| **A157218** | Every odd $m > 34$ is $p + 2^x + 7\cdot 2^y$ with $p \equiv 1 \pmod 6$ | $m = 445{,}466{,}268{,}731$ (only one below $10^{13}$) | Independent C + Python | [`counterexamples/A157218/`](counterexamples/A157218/) |
| **A157225** | Same with $p \equiv 5 \pmod 6$ | 4 new counterexamples below $10^{13}$ up to $1{,}572{,}650{,}032{,}347$ | Independent C + Python | [`counterexamples/A157225/`](counterexamples/A157225/) |
| **A303932 (Conj. 1 & 2)** | Every even $2n > 2$ is $p + 2^k + 3^m$ with $(11/p) = +1$ (resp. $-1$) | $2n = 257{,}558{,}146{,}370$ (Conj. 1); $2n = 68{,}211{,}369{,}278$ (Conj. 2) | Independent C + Python | [`counterexamples/A303932/`](counterexamples/A303932/) |
| **A303540 / A303539** | Every $n > 1$ is $a^2 + b^2 + \binom{2c}{c} + \binom{2d}{d}$ | $n = 210{,}107{,}364{,}447$ | Independent C + Python | [`counterexamples/A303540/`](counterexamples/A303540/) |
| **A302984** | Every $n > 5$ is $x^2 + 2y^2 + 2^z + 5\cdot 2^w$ | $n = 4{,}375{,}339{,}279$ ($219$ below $10^{12}$) | Independent C + Python | [`counterexamples/A302984/`](counterexamples/A302984/) |
| **A302982** | Every $n > 3$ is $x^2 + 5y^2 + 2^z + 3\cdot 2^w$ | $n = 558{,}556{,}427$ ($200$ below $4\cdot 10^{10}$) | Independent C + Python | [`counterexamples/A302982/`](counterexamples/A302982/) |
| **A300448 (Conj. 2)** | Every square $n^2$ is $4^k m + x^2 + y^2$ with $m \in \{1, 5, 17\}$ | $n = 239{,}694{,}783$ | Independent C + Python | [`counterexamples/A300448/`](counterexamples/A300448/) |
| **A308644 (Conj. 1 & 2)** | Representations as $(3^a 5^b)^2$ or $(3^a 4^b)^2$ plus polygonal numbers | $n = 108{,}011{,}768$ (Conj. 1) and $n = 7{,}654{,}105$ (Conj. 2) | Independent C + Python | [`counterexamples/A308644/`](counterexamples/A308644/) |
| **A308656 (Conj. 2)** | Every $n > 0$ is $(2^a 9^b)^2 + c(4c+1) + d(3d+1)/2$ | $n = 235{,}644{,}514$ | Independent C + Python | [`counterexamples/A308656/`](counterexamples/A308656/) |
| **A262945** | Uniqueness list for $n - x^4 - 2y^2$ triangular or pentagonal | New $a(n) = 1$ counterexample beyond conjectured list | Independent C + Python | [`counterexamples/A262945/`](counterexamples/A262945/) |
| **A270594** | Uniqueness list for triangular $+$ square $+$ generalized pentagonal | New $a(n) = 1$ counterexample beyond conjectured list | Independent C + Python | [`counterexamples/A270594/`](counterexamples/A270594/) |
| **A270920** | Uniqueness list for triangular $+$ square $+$ fifth power | New $a(n) = 1$ counterexample beyond conjectured list | Independent C + Python | [`counterexamples/A270920/`](counterexamples/A270920/) |
| **A352356** | Representations $12n + 5 = 2x^2 + 5y^2 + 9z^2 + xyz$ | Counterexample beyond conjectured exception list | Independent C + Python | [`counterexamples/A352356/`](counterexamples/A352356/) |

---

## 2. Unconditional Proofs & Constructions (15)

| Problem | Statement Proved | Verification | Folder |
|---|---|---|---|
| **A094960** | Kellner / Alekseyev conjecture: $B'_k(x) \in \mathbb{Z}[x]$ only for $k \in \{1,2,4,6,10,12,28,30,36,60\}$ | **Lean 4** + proof + C check | [`proofs/A094960/`](proofs/A094960/) |
| **Cheng–Lin Conj. 3.30** | `arXiv:2603.21680v3` Conj. 3.30: Chow polynomial second-moment inequality is a nonnegative combination of flag monotonicity inequalities for all $d \ge 1$ | Exact proof + certificates ($d \le 22$) | [`proofs/cheng-lin-chow-moments/`](proofs/cheng-lin-chow-moments/) |
| **Turán $\operatorname{ex}(n, C_4)$ (`A006855`)** | New upper bounds for $\operatorname{ex}(n, C_4)$ across $45 \le n \le 56$ | Exact rational LP certificates | [`proofs/turan-c4/`](proofs/turan-c4/) |
| **Kotzig P1F ($K_{1682}$)** | Existence of a perfect 1-factorization of the open order $K_{1682}$ ($q = 41^2$) | Explicit certificate + verifiers | [`proofs/kotzig-perfect-1f/`](proofs/kotzig-perfect-1f/) |
| **A360278 (Conj. 1–3)** | `arXiv:2302.08315` Conj. 4.2–4.4: exact evaluations of $\det[v(j+k)+\delta_{j,k}]$ for Lucas, Fibonacci, and general $A$ | **Lean 4** (zero-dep) + proof | [`proofs/A360278/`](proofs/A360278/) |
| **A210445** | Least $k$ with $kn$ practical satisfies $a(n) < n$ ($n > 1$) and $a(n) < n/2$ ($n > 47$) | **Lean 4** (zero-dep) + proof | [`proofs/A210445/`](proofs/A210445/) |
| **A392684 ($k = 3$)** | Every $n \ge 6$ is $x+y+z$ with $\operatorname{lcm}(x,y,z) = m(m+1)(m+2)$, and $N(3) = 6$ | **Lean 4** (zero-dep) + proof | [`proofs/A392684/`](proofs/A392684/) |
| **A362743 (Conj. 1, part 1)** | Integers not representable as sums of distinct $4^a + 5^b$ are exactly $\{1,3,4,10,12,18\}$ | **Lean 4** (zero-dep) + Python | [`proofs/A362743/`](proofs/A362743/) |
| **A362861 (Conj. 1(i) & 1(ii) pt 1)** | Exact characterization of even integers as sums of distinct $5^a+5^b$, $3^a+3^b$, and $3^a+7^b$ | **Lean 4** (zero-dep) + Python | [`proofs/A362861/`](proofs/A362861/) |
| **A238165 (part ii)** | Sun `arXiv:1402.6641` Conj. 2.7(i): $\pi(kn)^{1/k}$ is strictly decreasing in $k \ge 1$ for all $n \ge 5$ | Elementary proof + exact checks | [`proofs/A238165/`](proofs/A238165/) |
| **A180364** | Ratio and root-ratio monotonicity of $\sum_{k=0}^n \binom{n}{k}^2 \binom{2k}{k}$ | Complete proof + Python | [`proofs/A180364/`](proofs/A180364/) |
| **A187011** | Evaluation of $\det[\lvert p_i - p_j\rvert]_{1 \le i,j \le n}$ | Complete proof + Python | [`proofs/A187011/`](proofs/A187011/) |
| **A256132** | Representations as a sum of three pentagonal numbers and a second pentagonal number (main statement) | Complete proof + Python | [`proofs/A256132/`](proofs/A256132/) |
| **A271719** | Partitions $n = x + y + z$ with $x \ge y > 0, z > 0, \gcd(x,y,z) = 1$ | Complete proof + Python | [`proofs/A271719/`](proofs/A271719/) |
| **A356976 (Conj. 2)** | Discriminator of $2k^3 + k$ ($k=1\dots n$) is the least power of $2$ not smaller than $n$ | Complete proof + C/Python check | [`proofs/A356976/`](proofs/A356976/) |

---

## 3. Complete Classifications Conditional on RH / Dirichlet GRH (4)

Each result below relies only on the Riemann Hypothesis for $\zeta(s)$ or GRH for Dirichlet $L$-functions, paired with an unconditional finite computation.

| Problem | Result (Conditional on RH / Dirichlet GRH) | Verification | Folder |
|---|---|---|---|
| **Class Group Exponent 3** | Complete list of the 17 imaginary quadratic fundamental discriminants with class group of exponent 3 (given Dirichlet GRH) | Proof + PARI/GP + C sieve | [`rh-conditional/class-group-exponent-3/`](rh-conditional/class-group-exponent-3/) |
| **A353076** | Complete list of all **884** odd integers with $\sigma(k) > (e^\gamma/2)k\log\log k$, largest $c_0/67$ (given RH) | Dual C enumerators + 60-digit verifier | [`rh-conditional/A353076/`](rh-conditional/A353076/) |
| **A350299** | Complete list of all **11** terms (last term $5040$, given RH) | 40-digit Decimal verifier | [`rh-conditional/A350299/`](rh-conditional/A350299/) |
| **Ramanujan's Inequality** | Complete enumeration of all **564,384,969** integer counterexamples (107,146 runs, largest $38{,}358{,}837{,}682$, given RH) | Dual C sieves + Lucy boundary check | [`rh-conditional/ramanujan-inequality/`](rh-conditional/ramanujan-inequality/) |

---

## Reproducing the Verifications

- **Lean 4 proofs:** Zero-dependency files (e.g. `A357130.lean`, `A349530.lean`, `A360278.lean`, `A210445.lean`, `A392684.lean`, `A362743.lean`, `A362861.lean`) verify directly with `lean <file>.lean` (Lean 4.36.0); project folders (`A094960/lean/`, `erdos-1094/lean/`) build with `lake build`.
- **Python / C / PARI-GP scripts:** Each folder's `README.md` lists the exact verification commands.

## License

MIT — see [`LICENSE`](LICENSE).
