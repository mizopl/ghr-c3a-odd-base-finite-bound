# Explicit Finite-Depth Carry-Free Lower Bound $C_{3e} > 1.27255802$ for the Unnormalized Single-Set Sum-Difference Constant $C_{3e}$ (`constants/3e.md`, Problem 6.43 of `[GGSWT2025]`)

- **Target Constant:** $C_{3e} = \sup_{|A| \ge 2} \frac{\log |A - A|}{\log |A + A|}$ ([`teorth/optimizationproblems/blob/main/constants/3e.md`](https://github.com/teorth/optimizationproblems/blob/main/constants/3e.md), Problem 6.43 of `[GGSWT2025]`).
- **Previous Published Record (`[HRY1999]`):**
  $$\frac{\log(1 + \sqrt{2})}{\log 2} = 1.27155330316361201881\dots$$
  obtained by Hennecart, Robert, and Yudin (`[HRY1999]`, *Astérisque* **258**, 1999, pp. 173–178; `[GHR2007, §2 Remark]`) from the asymptotic gapless simplex $V(m, m/2) = \{x \in \mathbb{N}_0^m : \sum_{i=1}^m x_i \le m/2\}$ projected to $\mathbb{Z}$.
- **New Finite-Certified Lower Bounds (Carry-Free Base-$Q$ Projection of the Two-Temperature $\langle 4, 5 \rangle$ Budgeted Simplex):**
  1. **Primary Certificate (`c3e_finite_certificate_80_161.json`, $B = 80, Q = 161, N = 10^{13}$):**
     - Pure integer-interval arithmetic (`128`-bit `atanh` + Lean `StirlingBounds.lean`):
       $$C_{3e}(A_N) \ge \frac{\log |A_N - A_N|}{\log |A_N + A_N|} > \mathbf{1.27255796845801701855} > \mathbf{1.27255796}$$
     - 60-digit `mpmath.iv` interval arithmetic:
       $$C_{3e}(A_N) > \mathbf{1.27255796845856979212} > \mathbf{1.27255796}$$
     - Margin over `[HRY1999]`: **`+0.00100466`**
  2. **Secondary Certificate (`c3e_finite_certificate_160_321.json`, $B = 160, Q = 321, N = 10^{15}$):**
     - Pure integer-interval arithmetic (`128`-bit `atanh` + Lean `StirlingBounds.lean`):
       $$C_{3e}(A_N) > \mathbf{1.27255802020996480086} > \mathbf{1.27255802}$$
     - 60-digit `mpmath.iv` interval arithmetic:
       $$C_{3e}(A_N) > \mathbf{1.27255802020997507196} > \mathbf{1.27255802}$$
     - Margin over `[HRY1999]`: **`+0.00100472`**

---

## 1. Provenance & Credit

This construction emerged during a post-mortem / lessons-learned review of our $C_{3a}$ repository prompted by Arhan Canli's (`@arhancanli`, Quantavane) independent from-scratch replay on [`teorth/optimizationproblems#236`](https://github.com/teorth/optimizationproblems/pull/236).

- **Two-Temperature $\langle 4, 5 \rangle \cap [0, 80]$ Alphabet & Tilt Parameters (`[O2026]`):** The truncated numerical semigroup $M = \langle 4, 5 \rangle \cap [0, 80] = \{0, 4, 5, 8, 9, 10\} \cup [12, 80]$ and the separate difference/sum tilts $(x = 8149/10000, y = 42571/50000)$ at depth $N = 10^{13}$ (`n_0 = 1,917,647,564,302`, `2L = 76,435,323,145,630`) were introduced by **Carson Olafson (`@carson-olaf`, `[O2026]`)** in [`teorth/optimizationproblems#148`](https://github.com/teorth/optimizationproblems/pull/148) ([`carson-olaf/c3a-two-temperature-bound`](https://github.com/carson-olaf/c3a-two-temperature-bound)) to prove $C_{3a} > 1.21418 \approx 2 - \sigma/\rho$ via Bertrand-prime cyclic compression.
- **Why $C_{3e}$ Needs Neither Cyclic Compression Nor Bertrand's Postulate:**
  In the two-set GHR problem $C_{3a}$, the finite-set reduction ([GHR2007, Lemma 2.1]) requires $|V - V| < 2\max V + 1$, which places $\log(2\max V + 1)$ in the denominator and forces `[O2026]` to compress $\mathcal{V}_N \subset \mathbb{Z}^N$ modulo a prime $p > |\mathcal{V}_N - \mathcal{V}_N|$.
  By contrast, the unnormalized single-set sum-difference constant $C_{3e}$ (`constants/3e.md`, Problem 6.43 of `[GGSWT2025]`) depends **only** on $\log |A - A| / \log |A + A|$ for a finite nonempty set $A \subset \mathbb{Z}$, with **no** condition on $\max A$.
  Consequently, projecting $\mathcal{V}_N = \{a \in M^N : \sum_{i=0}^{N-1} a_i \le L\}$ to $\mathbb{Z}$ via the elementary **carry-free base $Q = 2B + 1$** ($A_N = \{\sum_{i=0}^{N-1} a_i Q^i : a \in \mathcal{V}_N\}$) is an exact Freiman $2$-isomorphism ($|A_N + A_N| = |\mathcal{V}_N + \mathcal{V}_N|$ and $|A_N - A_N| = |\mathcal{V}_N - \mathcal{V}_N|$) that transfers the reciprocal entropy ratio $\rho/\sigma = (2 - (2 - \sigma/\rho))^{-1}$ directly to $C_{3e}$ at finite depth $N$ using only elementary carry-free digit uniqueness, multinomial counting, and Robbins–Stirling bounds.

---

## 2. Self-Contained Mathematical Proof (Theorems C1–C3)

Let $B \ge 12$ be an integer, let $H = \langle 4, 5 \rangle = \mathbb{N}_0 \setminus \{1, 2, 3, 6, 7, 11\}$, and set
$$M = H \cap [0, B], \qquad S = M + M \subseteq [0, 2B], \qquad D = M - M = [-B, B], \qquad Q = 2B + 1.$$
For each $d \in [1, B]$, define the minimum witness cost
$$\kappa(d) = \min\{a + b : a, b \in M,\ a - b = d\}$$
and fix a witness pair $(\alpha_d, \beta_d) \in M^2$ with $\alpha_d - \beta_d = d$ and $\alpha_d + \beta_d = \kappa(d)$.

### Theorem C1 (Carry-Free Base-$Q$ Freiman $2$-Isomorphism)
For any $N \ge 1$ and $L \ge 0$, define
$$\mathcal{V}_N = \left\{a = (a_0, \dots, a_{N-1}) \in M^N : \sum_{i=0}^{N-1} a_i \le L\right\} \subset \mathbb{Z}^N$$
and its base-$Q$ evaluation image
$$A_N = \mathrm{eval}_Q(\mathcal{V}_N) = \left\{\sum_{i=0}^{N-1} a_i Q^i : a \in \mathcal{V}_N\right\} \subset \mathbb{Z}_{\ge 0}.$$
Then $|A_N + A_N| = |\mathcal{V}_N + \mathcal{V}_N|$ and $|A_N - A_N| = |\mathcal{V}_N - \mathcal{V}_N|$.

**Proof.** By linearity of $\mathrm{eval}_Q$, $A_N \pm A_N = \mathrm{eval}_Q(\mathcal{V}_N \pm \mathcal{V}_N)$, so it suffices to check that $\mathrm{eval}_Q$ is injective on $\mathcal{V}_N + \mathcal{V}_N \subseteq [0, 2B]^N$ and on $\mathcal{V}_N - \mathcal{V}_N \subseteq [-B, B]^N$.
- On $[0, 2B]^N = [0, Q - 1]^N$, $\mathrm{eval}_Q$ is standard base-$Q$ expansion with digits in $[0, Q-1]$, hence injective.
- On $[-B, B]^N$, if $\sum_{i=0}^{N-1} z_i Q^i = \sum_{i=0}^{N-1} z'_i Q^i$ with $z_i, z'_i \in [-B, B]$ and $z \ne z'$, let $i_0$ be the least index with $z_{i_0} \ne z'_{i_0}$. Reducing modulo $Q^{i_0+1}$ and dividing by $Q^{i_0}$ gives $Q \mid (z_{i_0} - z'_{i_0})$, which contradicts $0 < |z_{i_0} - z'_{i_0}| \le 2B = Q - 1 < Q$. $\square$

### Theorem C2 (Multinomial Difference Lower Bound $|A_N - A_N| \ge D_N$)
Given positive integers $(n_d)_{d=1}^B$ with $n_0 := N - 2\sum_{d=1}^B n_d > 0$, define $L := \sum_{d=1}^B n_d \kappa(d)$, and let $\mathcal{W}_N \subset [-B, B]^N$ be the set of words of length $N$ in which $0$ occurs $n_0$ times and each $\pm d$ ($1 \le d \le B$) occurs $n_d$ times.
For each $w \in \mathcal{W}_N$, define $a(w), b(w) \in M^N$ coordinatewise by $(0, 0)$ if $w_i = 0$, $(\alpha_d, \beta_d)$ if $w_i = +d$, and $(\beta_d, \alpha_d)$ if $w_i = -d$.
Then $a(w) - b(w) = w$ and
$$\sum_{i=0}^{N-1} a_i(w) = \sum_{i=0}^{N-1} b_i(w) = \sum_{d=1}^B n_d (\alpha_d + \beta_d) = \sum_{d=1}^B n_d \kappa(d) = L.$$
Hence $a(w), b(w) \in \mathcal{V}_N$ and $\mathcal{W}_N \subseteq \mathcal{V}_N - \mathcal{V}_N$. By Theorem C1,
$$|A_N - A_N| = |\mathcal{V}_N - \mathcal{V}_N| \ge |\mathcal{W}_N| = D_N := \frac{N!}{n_0! \prod_{d=1}^B (n_d!)^2}. \quad \square$$

### Theorem C3 (Saddle-Point Sumset Upper Bound $|A_N + A_N| \le S_N(y)$ and Certified Lower Bound for $C_{3e}$)
Every vector $s = u + v \in \mathcal{V}_N + \mathcal{V}_N$ belongs to $S^N$ and satisfies $\sum_{i=0}^{N-1} s_i \le 2L$. For any real $y \in (0, 1)$, since $y^{\sum s_i} \ge y^{2L}$ whenever $\sum s_i \le 2L$, Theorem C1 gives
$$|A_N + A_N| = |\mathcal{V}_N + \mathcal{V}_N| \le \left|\left\{s \in S^N : \sum_{i=0}^{N-1} s_i \le 2L\right\}\right| \le y^{-2L} \sum_{s \in S^N} y^{\sum_{i=0}^{N-1} s_i} = \frac{P_+(y)^N}{y^{2L}} =: S_N(y),$$
where $P_+(y) = \sum_{s \in S} y^s$. Since $n_1 > 0$ and $L \ge B$, $|A_N + A_N| \ge |A_N| \ge 2$, so $\log |A_N + A_N| > 0$ and
$$C_{3e} \ge \frac{\log |A_N - A_N|}{\log |A_N + A_N|} \ge \frac{\log D_N}{\log S_N(y)}. \quad \square$$

---

## 3. Files & Verification (`< 0.1s`)

| File | Bytes | SHA-256 | Description |
|---|---:|---|---|
| `c3e_finite_certificate_80_161.json` | `1,081` | `21a1203cff2a8cb040794e6149fdbd4a9db6e5b13be8fbfd37d505b551eb1a84` | Primary finite certificate ($B=80, Q=161, N=10^{13}, C_{3e} > 1.27255796$) |
| `c3e_finite_certificate_160_321.json` | `1,100` | `c011cca3555411ee1878371424637857f17b8937d390c143e6f3c04e30addd4e` | Secondary finite certificate ($B=160, Q=321, N=10^{15}, C_{3e} > 1.27255802$) |
| `check_c3e.py` | `11,098` | `b18ae0c0fb87c6702f7fa9be5f9f9bc3ac627675a7b9521674e477b8213e8d0d` | Standalone deterministic verifier (`128`-bit integer-interval `atanh` + `60`-dps `mpmath.iv`) |

Run:
```bash
python3 c3e_finite_certificate/check_c3e.py
```

---

## 4. References

- `[HRY1999]` F. Hennecart, G. Robert, and A. Yudin, *On the number of sums and differences*, Astérisque **258** (1999), 173–178.
- `[GHR2007]` K. Gyarmati, F. Hennecart, and I. Z. Ruzsa, *Sums and differences of finite sets*, Functiones et Approximatio Commentarii Mathematici **37**(1) (2007), 175–186.
- `[GGSWT2025]` B. Georgiev, J. Gómez-Serrano, T. Tao, and A. Z. Wagner, *Mathematical exploration and discovery at scale*, arXiv:2511.02864 (Problem 6.43, §6.25).
- `[K2026b]` L. Kleinwaks, *Masked-digit sum-difference lower bound*, [`teorth/optimizationproblems#146`](https://github.com/teorth/optimizationproblems/pull/146) (2026).
- `[O2026]` C. Olafson, *Two-temperature cyclic compression for the Gyarmati–Hennecart–Ruzsa constant*, [`teorth/optimizationproblems#148`](https://github.com/teorth/optimizationproblems/pull/148) and [`carson-olaf/c3a-two-temperature-bound`](https://github.com/carson-olaf/c3a-two-temperature-bound) (2026).
