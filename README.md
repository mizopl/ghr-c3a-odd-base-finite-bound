# Claim: Explicit Finite-Depth ($N = 10^{13}$) Controlled-Carry Masked-Digit Lower Bound $C_{3a}(V) > 1.19230254$ for the Gyarmati–Hennecart–Ruzsa Constant $C_{3a}$ (Beating the Published Finite-Certified Record $1.19102809$ by $+0.00127445$, Partial Win `p1`)

> **🌟 Official Benchmark Acceptance & Flagship Discovery Engine (`We*`):**
> - **Merged by Terence Tao (`@teorth`):** Accepted and merged into the official [**`teorth/optimizationproblems`** benchmark (`constants/3a.md`, citation **`[M2026]`**, PR #236)](https://github.com/teorth/optimizationproblems/blob/main/constants/3a.md).
> - **Flagship Repository ([`mizopl/we-star`](https://github.com/mizopl/we-star)):** This standalone verification package is part of [**`mizopl/we-star` (`We* = human + AI + autonomous 3-skeptic verification loop`)**](https://github.com/mizopl/we-star) — explore the full system architecture, the Nine Universal Laws of Meta-Generalization, and 39 machine-verified scientific packages across 29 open problems.
> - **Inspiration & Benchmark Catalyst (`@elder-plinius` / `V3R1T4S`):** Directly inspired by **[Pliny (`@elder-plinius`)](https://github.com/elder-plinius)** and the **[`elder-plinius/V3R1T4S`](https://github.com/elder-plinius/V3R1T4S)** open-science benchmark, whose zero-trust *Verify-It-Yourself* ethos and open-problem curation catalyzed the `we*star` autonomous discovery loop.

- **Problem ID:** `ghr-sum-difference-c3a` (`known-unknowns/erdos-and-proofs/ghr-sum-difference-c3a.md`)
- **Result Classification:** Named Partial Win `p1` (`CONFIRMED_PARTIAL`)
- **Primary Finite Certificate:** `object/finite_certificate_17086_27995.json` (`1,204` bytes, `sha256: b1230dd40bb7fcb2ae877bee31547f50dd52657d99c6e19e483271a871c1fe21`)
  - Semigroup generators: $G = \{1518, 1524, 1587, 2024, 2032, 2116\} = \{3, 4\} \times \{506, 508, 529\}$
  - Mask bound: $B = 17,086$, mask $M = \mathrm{span}_{\mathbb{N}_0}(G) \cap [0, 17086]$ (`object/mask_17086.txt`, $|M| = 3,153$, $0 \in M$, $\max M = 17,086$)
  - Sum support: $S = M + M \subseteq [0, 34172]$ (`object/sum_support_17086.txt`, $|S| = 18,835$)
  - Controlled-carry odd base: $q = 27,995 < 2B + 1 = 34,173$
  - Pruned difference alphabet: $\widetilde{D} = \{0\} \cup \{\pm d : d \in \widetilde{D}_+\}$ (`object/pruned_differences_17086_27995.tsv`, $|\widetilde{D}_+| = 13,997$, $|\widetilde{D}| = 27,995 = q$, all $27,995$ residues modulo $q = 27,995$ pairwise distinct)
  - Finite depth: $N = 10^{13}$ digits, saddle parameter $x_f = 0.9996683050229444 = 9996683050229444 / 10^{16}$, zero-difference count $n_0 = 17,074,745,018$, digit-sum cap $L = 50,031,092,045,455,301$
  - Explicit finite integer set: $V = 2U \subset \mathbb{Z}_{\ge 0}$, where $U = \left\{\sum_{i=0}^{N-1} a_i \cdot 27995^i : a_i \in M, \ \sum_{i=0}^{N-1} a_i \le 50,031,092,045,455,301\right\}$
  - Certified GHR lower bound:
    - **60-digit `mpmath` interval/directed-rounding arithmetic (`mp.dps = 60`, Robbins–Stirling bounds):** $C_{3a}(V) \ge 1 + \frac{\log(|V-V|/|V+V|)}{\log(2\max V + 1)} > \mathbf{1.19230254070568368329} > \mathbf{1.19230254}$
    - **100% pure integer-interval arithmetic (`atanh` Taylor series + Lean `StirlingBounds.lean` bounds):** $C_{3a}(V) > \mathbf{1.19230254068351294895} > \mathbf{1.19230254}$
    - **Improvement over the best finite-certified lower bound `1.19102809` on `teorth/optimizationproblems/blob/main/constants/3a.md`:** $+0.00127445$ ($12,744\times$ the $10^{-7}$ threshold)
- **Secondary Finite Certificate (on Kleinwaks's exact published mask $B = 17,032, |M| = 3,121$):** `object/finite_certificate_17032_27995.json` (`1,204` bytes, `sha256: db1517d0d4b32ad27df910162aa55d283fa9e6a4fa0374bff651b6ae655de04b`)
  - Parameters: $B = 17,032, q = 27,995, N = 10^{13}, x_f = 0.9996683050229444, n_0 = 17,075,622,128, L = 50,029,864,065,809,249$
  - Certified GHR lower bound: $C_{3a}(V) > \mathbf{1.19229904840497896133} > \mathbf{1.19229904}$ (`+0.00127095` over `1.19102809`)
- **Published Baseline Reproduction Certificate:** `object/kleinwaks_finite_certificate_17032_34065.json` (`1,204` bytes, `sha256: 5c85a63a7a8a8d7b596c3d375239ecd91e45fdf991feb44500a922deeb9d8239`)
  - Exact reproduction of Kleinwaks's [K2026b] finite-depth construction ($B = 17,032, Q = 34,065 = 2B + 1, N = 10^{13}, x_f = 0.9996789017186568, n_0 = 14,962,802,398, L = 51,500,691,976,683,641$): $C_{3a}(V) > \mathbf{1.19102809427254087548} > \mathbf{1.19102809}$.

---

## 1. Verbatim Success Criterion & Partial Win `p1` from the Benchmark Target

From `ghr-sum-difference-c3a.md`:

> ### What counts as a win
> A construction certified at finite depth (explicit U, or a masked-digit construction with an exact counting certificate) whose value under the 3a page's formula is STRICTLY GREATER (direction: max) than the best lower bound listed on https://github.com/teorth/optimizationproblems/blob/main/constants/3a.md itself (not the README table) AT VERIFICATION TIME, including asterisked limit values, by at least 1e-7, after the verifier re-reads the exact hypotheses of the formula on the 3a page (e.g. 0 in U, nonnegativity, |U-U| < 2max(U)+1). As of 2026-10-03 that value is 1.19519192* (Kleinwaks 2026b).
>
> ### Partial wins
> - **p1:** A finite-certified construction whose value lies strictly above the best finite-certified value on the 3a page (1.19102809 as of 2026-10-03) but does not beat the limit record, verified with directed rounding and the formula's hypotheses checked.
> - **p2:** A limit (asterisked-type) construction, with an exact derivation rechecked by independent code or Lean, whose limiting value strictly exceeds the best value on the 3a page at verification time, but without a finite-depth certificate.
>
> ### How a win is checked
> For an explicit U: compute |U+U| and |U-U| exactly (bitset or numpy convolution of indicator vectors), check that U contains 0 and is nonnegative, and check the hypotheses. Evaluate the formula with 50-digit mpmath using directed rounding (round the lower bound down). For digit constructions: re-derive the counting formula independently, recompute the counts with separate code, and reproduce Kleinwaks's 1.19102809 with the same pipeline first.

---

## 2. Mathematical Derivation & Why Controlled-Carry Odd Base $q = 27,995 < 2B + 1$ Works at Finite Depth

### 2.1 Why Kleinwaks [K2026b] Stopped at $1.19102809$ for the Finite Certificate
In [K2026b] (`kleinwaks/masked-digit-sum-difference-bound`, `constants/3a.md` PR #146), two distinct results are proved:
1. **An asymptotic limit lower bound $1.19519192^*$** (marked with an asterisk on `constants/3a.md`) using a controlled-carry construction with generators $G_2 = \{1971, 2016, 2100, 2628, 2688, 2800\}$, $B_2 = 26,972$, and even base $q_2 = 27,022$ (`formalization/lean/RequestProject/ControlledAsymptotic.lean`). That proof does **not** certify any explicit finite depth $N$: instead it uses `Filter.Tendsto` (`ControlledLimit.lean`) as $N \to \infty$ with an asymptotic carryover word-grouping argument (`word Fibre` of size $\le 2^N$).
2. **An explicit finite-depth certificate $1.19102809$ at $N = 10^{13}$** (`formalization/lean/RequestProject/FiniteDepth.lean`), which falls back to the **uncontrolled-carry** base $Q = 2B + 1 = 34,065$ with generators $G = \{1518, 1524, 1587, 2024, 2032, 2116\}$ and $B = 17,032$. Because $Q = 2B + 1 = 34,065$ is large, the denominator $\log(2\max V + 1) \approx N \log(34065)$ penalizes the finite-depth ratio heavily, capping the finite certificate at $1.19102809$.

### 2.2 Exact Finite-Depth Counting via Residue-Bijective Mod-$q$ Difference Pruning
Notice that in Kleinwaks's own Lean formalization (`formalization/lean/RequestProject/CoreConstruction.lean`, lines 66–221), the finite-depth counting theorem `residue_word_injective` is proved for **any** base $q \ge 2$ and **any** difference subset $\widetilde{D} \subseteq M - M$ whose elements have **pairwise distinct residues modulo $q$**:

- **Theorem 1 (Injective Base-$q$ Evaluation on Pruned Difference Words):**
  Let $q \ge B + 1$ be an odd integer, let $M \subseteq [0, B]$ be a finite digit mask with $0 \in M$, and for each $d \in [0, B]$ define the minimal digit-sum cost
  $$\kappa(d) = \min\{a + b : a, b \in M, \ a - b = d\} = \min\{2b + d : b \in M, \ b + d \in M\}$$
  (with $\kappa(d) = +\infty$ if $d \notin M - M$).
  Partition the non-zero residues $\{1, 2, \dots, q - 1\} \pmod{q}$ into $(q - 1)/2$ complementary pairs $\{r, q - r\}$ for $1 \le r \le (q - 1)/2$. Since $q$ is odd, $r \not\equiv q - r \pmod{q}$ for every $1 \le r \le (q - 1)/2$.
  For each $r \in \{1, \dots, (q - 1)/2\}$ such that $\min(\kappa(r), \kappa(q - r)) < \infty$, select a single representative
  $$d(r) = \begin{cases} r & \text{if } \kappa(r) \le \kappa(q - r), \\ q - r & \text{if } \kappa(q - r) < \kappa(r), \end{cases}$$
  together with a witness pair $(\alpha_{d(r)}, \beta_{d(r)}) \in M^2$ satisfying $\alpha_{d(r)} - \beta_{d(r)} = d(r)$ and $\alpha_{d(r)} + \beta_{d(r)} = \kappa(d(r))$.
  Let $\widetilde{D}_+ = \{d(r) : 1 \le r \le (q - 1)/2, \ \min(\kappa(r), \kappa(q - r)) < \infty\}$ and define the symmetric pruned difference alphabet
  $$\widetilde{D} = \{0\} \cup \{+d : d \in \widetilde{D}_+\} \cup \{-d : d \in \widetilde{D}_+\} \subseteq M - M.$$
  Then:
  1. For each $r$, $+d(r) \bmod q \in \{r, q - r\}$ and $-d(r) \bmod q \in \{r, q - r\}$ are the two distinct elements of the pair $\{r, q - r\}$. Since the pairs $\{r, q - r\}$ are disjoint for $1 \le r \le (q - 1)/2$ and exclude $0$, **all $1 + 2|\widetilde{D}_+|$ elements of $\widetilde{D}$ have pairwise distinct residues modulo $q$**.
  2. Consequently, the base-$q$ evaluation map $\mathrm{eval}_q : \widetilde{D}^N \to \mathbb{Z}$, $(d_0, \dots, d_{N-1}) \mapsto \sum_{i=0}^{N-1} d_i q^i$, is **injective** (`residue_word_injective` in `CoreConstruction.lean`: if $\sum_{i=0}^{N-1} d_i q^i = \sum_{i=0}^{N-1} d'_i q^i$, reducing modulo $q$ gives $d_0 \equiv d'_0 \pmod{q}$, hence $d_0 = d'_0$; subtracting and dividing by $q$ inductively gives $d_i = d'_i$ for all $i$).

- **Theorem 2 (Exact Multinomial Difference Lower Bound $|V - V| = |U - U| \ge D_N$):**
  Given non-negative integer counts $(n_d)_{d \in \widetilde{D}_+}$ with $n_0 := N - 2\sum_{d \in \widetilde{D}_+} n_d \ge 0$, set
  $$L := \sum_{d \in \widetilde{D}_+} n_d \kappa(d), \qquad U := \left\{\sum_{i=0}^{N-1} a_i q^i : a_i \in M, \ \sum_{i=0}^{N-1} a_i \le L\right\}, \qquad V := 2U = \{2u : u \in U\}.$$
  Let $\mathcal{W} \subseteq \widetilde{D}^N$ be the set of words of length $N$ in which $0$ appears $n_0$ times and, for each $d \in \widetilde{D}_+$, $+d$ appears $n_d$ times and $-d$ appears $n_d$ times.
  For any word $w = (w_0, \dots, w_{N-1}) \in \mathcal{W}$, define digit words $a(w), b(w) \in M^N$ by setting
  $$(a_i(w), b_i(w)) = \begin{cases} (0, 0) & \text{if } w_i = 0, \\ (\alpha_d, \beta_d) & \text{if } w_i = +d \ (d \in \widetilde{D}_+), \\ (\beta_d, \alpha_d) & \text{if } w_i = -d \ (d \in \widetilde{D}_+). \end{cases}$$
  Then $a_i(w) - b_i(w) = w_i$ for every $i$, and
  $$\sum_{i=0}^{N-1} a_i(w) + \sum_{i=0}^{N-1} b_i(w) = \sum_{i=0}^{N-1} (a_i(w) + b_i(w)) = 2 \sum_{d \in \widetilde{D}_+} n_d \kappa(d) = 2L.$$
  Moreover, because $+d$ and $-d$ occur an equal number of times $n_d$, $\sum_{i=0}^{N-1} (a_i(w) - b_i(w)) = \sum_{i=0}^{N-1} w_i = 0$, so
  $$\sum_{i=0}^{N-1} a_i(w) = \sum_{i=0}^{N-1} b_i(w) = L.$$
  Therefore $u(w) := \sum_{i=0}^{N-1} a_i(w) q^i \in U$ and $v(w) := \sum_{i=0}^{N-1} b_i(w) q^i \in U$, with $u(w) - v(w) = \mathrm{eval}_q(w) \in U - U$.
  By Theorem 1, $\mathrm{eval}_q$ is injective on $\mathcal{W} \subseteq \widetilde{D}^N$, so
  $$|V - V| = |U - U| \ge |\mathcal{W}| = D_N := \frac{N!}{n_0! \prod_{d \in \widetilde{D}_+} (n_d!)^2}.$$

- **Theorem 3 (Saddle-Point Sumset Upper Bound $|V + V| = |U + U| \le S_N$):**
  Every element of $U + U$ has the form $\sum_{i=0}^{N-1} s_i q^i$ where $s_i = a_i + a'_i \in S := M + M$ and $\sum_{i=0}^{N-1} s_i \le 2L$.
  Thus $|V + V| = |U + U|$ is bounded above by the number of $N$-tuples $(s_0, \dots, s_{N-1}) \in S^N$ with $\sum_{i=0}^{N-1} s_i \le 2L$:
  $$|V + V| = |U + U| \le \left|\left\{(s_0, \dots, s_{N-1}) \in S^N : \sum_{i=0}^{N-1} s_i \le 2L\right\}\right| = \sum_{m=0}^{2L} [x^m] \left(P_+(x)\right)^N, \qquad P_+(x) := \sum_{s \in S} x^s.$$
  For any real $x \in (0, 1)$, since $x^m \ge x^{2L}$ for all $0 \le m \le 2L$ and all coefficients of $(P_+(x))^N$ are non-negative (`sumset_upper_bound` in `CoreConstruction.lean`),
  $$|V + V| = |U + U| \le x^{-2L} \sum_{m=0}^{2NB} \left([x^m](P_+(x))^N\right) x^m = \frac{(P_+(x))^N}{x^{2L}} =: S_N(x).$$

- **Theorem 4 (Verification of All Hypotheses of the GHR Lemma on $V = 2U$):**
  The Gyarmati–Hennecart–Ruzsa Lemma ([GHR2007, Lemma 2.1] and `constants/3a.md`) requires a finite set $V \subset \mathbb{Z}_{\ge 0}$ such that:
  1. $0 \in V$: since $0 \in M$ and $L \ge 0$, the all-zero digit word gives $0 \in U$, hence $0 \in V = 2U$.
  2. $V \subset \mathbb{Z}_{\ge 0}$ is finite with $\max V > 0$: since $B \in M$ and $L \ge B$, the word $(0, \dots, 0, B)$ belongs to $U$, so $\max U \ge B q^{N-1} > 0$ and $\max V = 2\max U > 0$.
  3. $|V - V| < 2\max V + 1$: since $U \subseteq [0, \max U] \cap \mathbb{Z}$, every difference $u - u' \in U - U$ lies in $[-\max U, \max U] \cap \mathbb{Z}$, so
     $$|V - V| = |U - U| \le 2\max U + 1 < 4\max U + 1 = 2\max V + 1.$$
     (Doubling $U \mapsto V = 2U$ leaves $|V - V| = |U - U|$ and $|V + V| = |U + U|$ invariant while doubling $\max V = 2\max U$, which guarantees the strict inequality $|V - V| < 2\max V + 1$ even when $q < 2B + 1$ so $\max U$ can exceed $q^N/2$!)
  4. Upper bound on $2\max V + 1$: since every digit $a_i \in M \subseteq [0, B]$ satisfies $a_i \le B \le q - 1$,
     $$\max U \le \sum_{i=0}^{N-1} B q^i = B \frac{q^N - 1}{q - 1} \le q^N - 1,$$
     and therefore
     $$2\max V + 1 = 4\max U + 1 \le 4 q^N - 3 < 4 q^N < 5 q^N$$
     (matches `two_max_V_add_one_le` in `CoreConstruction.lean`).
  Combining Theorems 2, 3, and 4 with Robbins–Stirling bounds yields the certified lower bound
  $$C_{3a} \ge 1 + \frac{\log(|V - V| / |V + V|)}{\log(2\max V + 1)} \ge 1 + \frac{\log D_N - \log S_N(x_f)}{\log(5 \cdot q^N)}.$$

---

## 3. Summary of Certified Results

| Certificate File | $(B, q, N)$ | $\lvert M\rvert$ | $\lvert S\rvert$ | $\lvert \widetilde{D}_+\rvert$ | $\lvert \widetilde{D}\rvert$ | $n_0$ | $L$ | `mpmath` 60-dps Lower Bound | Pure Integer (Lean Stirling) Lower Bound | Margin vs `1.19102809` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `object/kleinwaks_finite_certificate_17032_34065.json` (Baseline) | $(17032, 34065, 10^{13})$ | $3,121$ | $18,730$ | $16,184$ | $32,369$ | $14,962,802,398$ | $51,500,691,976,683,641$ | `1.19102809427254087548` | `1.19102809424738956213` | `0.00000000` (baseline) |
| `object/finite_certificate_17032_27995.json` (Secondary) | $(17032, 27995, 10^{13})$ | $3,121$ | $18,730$ | $13,997$ | $27,995$ | $17,075,622,128$ | $50,029,864,065,809,249$ | **`1.19229904840497896133`** | **`1.19229904838280822699`** | **`+0.00127095`** |
| `object/finite_certificate_17086_27995.json` (**Primary**) | $(17086, 27995, 10^{13})$ | $3,153$ | $18,835$ | $13,997$ | $27,995$ | $17,074,745,018$ | $50,031,092,045,455,301$ | **`1.19230254070568368329`** | **`1.19230254068351294895`** | **`+0.00127445`** |

Note on `B = 17,086, q = 27,995`:
At $B = 17,086$ and odd base $q = 27,995$, **every single one** of the $(q - 1)/2 = 13,997$ non-zero complementary residue pairs $\{r, 27995 - r\}$ is realized by a difference in $M - M$, so $|\widetilde{D}_+| = 13,997$ and $|\widetilde{D}| = 27,995 = q$: the pruned difference alphabet $\widetilde{D}$ is a **complete residue system modulo $q = 27,995$**!

---

## 4. Files in `object/`

| File | Bytes | SHA-256 | Description |
|---|---:|---|---|
| `object/finite_certificate_17086_27995.json` | `1,204` | `b1230dd40bb7fcb2ae877bee31547f50dd52657d99c6e19e483271a871c1fe21` | Primary finite-depth ($N=10^{13}$) certificate ($B=17086, q=27995, \theta > 1.19230254$) |
| `object/finite_certificate_17032_27995.json` | `1,204` | `db1517d0d4b32ad27df910162aa55d283fa9e6a4fa0374bff651b6ae655de04b` | Secondary finite-depth ($N=10^{13}$) certificate on Kleinwaks's mask ($B=17032, q=27995, \theta > 1.19229904$) |
| `object/kleinwaks_finite_certificate_17032_34065.json` | `1,204` | `5c85a63a7a8a8d7b596c3d375239ecd91e45fdf991feb44500a922deeb9d8239` | Kleinwaks [K2026b] finite-depth baseline certificate ($B=17032, Q=34065, \theta > 1.19102809$) |
| `object/mask_17086.txt` | `18,450` | `3f9c0909410adb97e55c5ae7ab5a1a5dd54a11c415fa4513bbb8c2c06f29b358` | All `3,153` elements of $M = \mathrm{span}_{\mathbb{N}_0}(G) \cap [0, 17086]$ |
| `object/sum_support_17086.txt` | `112,542` | `7815e2fa41072d923eaeb99c46b3282f837093b6075ff5e4491d3aa89da58acc` | All `18,835` elements of $S = M + M \subseteq [0, 34172]$ |
| `object/pruned_differences_17086_27995.tsv` | `662,028` | `32e129199434a9122f0beab45dd69309921e4e389117f1fbdc00fa94580f3c0c` | Complete `13,997`-row witness & count table (`r`, `d`, `alpha_d`, `beta_d`, `kappa_d`, `pos_res_mod_q`, `neg_res_mod_q`, `n_d`) |
| `object/3a.md` | `9,559` | `7fcaf2453bc29c26452b9421152df4111ec3aa459d40de653fa0fabd5d439adf` | Live snapshot of `https://raw.githubusercontent.com/teorth/optimizationproblems/main/constants/3a.md` |
| `object/author_checker_c3a_check.py` | `14,634` | `bd9a411489eae68b8a06cde78024c85d5e839954bbf976d316e2bd8b58ceb246` | Standalone deterministic verifier (60-digit `mpmath` + pure integer-interval Lean `StirlingBounds`) |

---

## 5. Inspiration & Acknowledgments

- Special thanks to **[Pliny (`@elder-plinius`)](https://github.com/elder-plinius)** and the **[`elder-plinius/V3R1T4S`](https://github.com/elder-plinius/V3R1T4S)** open-science benchmark for inspiring our zero-trust *Verify-It-Yourself* verification methodology and autonomous mathematical discovery workflow.
- Engineered with the **[`mizopl/we-star`](https://github.com/mizopl/we-star)** (`we* = me + agentic systems we* create`) framework.
