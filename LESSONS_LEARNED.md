# Lessons Learned & Post-Mortem (`ghr-sum-difference-c3a` $\to$ `C_{3e}`)

**Date:** 2026-11-06  
**Catalyst:** Independent from-scratch replay by **Arhan Canli (`@arhancanli`, Quantavane)** on [`teorth/optimizationproblems#236`](https://github.com/teorth/optimizationproblems/pull/236#issuecomment-5591952940) (`2026-11-05`, [`arhancanli/quantavane-replays/tree/main/c3a`](https://github.com/arhancanli/quantavane-replays/tree/86099d017e3dc64ff2865a54d0fc55a35093430d/c3a)) and independent verification/review by **Pliny (`@elder-plinius`)** on [`elder-plinius/V3R1T4S#485`](https://github.com/elder-plinius/V3R1T4S/pull/485#issuecomment-5568341920) (`2026-11-03`).

---

## 1. Chronology, Replays & Prior-Art Credit

1. **Prior Independent Discovery of $(B = 17086, q = 27995)$ in a Comment on `PR #134` (`2026-08-12`):**
   On `2026-08-12`, **Carson Olafson (`@carson-olaf`)** posted the same $k = 1$ odd-base parameter tuple $(B = 17,086, q = 27,995, x = 3014/3015) \implies C_{3a} > 1.19230254$ in a comment on closed [`teorth/optimizationproblems#134`](https://github.com/teorth/optimizationproblems/pull/134#issuecomment-5299513691). Twenty-one minutes later, Logan Kleinwaks (`@kleinwaks`) replied that he had formalized a `1.195` limit bound (`PR #146`, `[K2026b]`), so `@carson-olaf` did not open a PR for the `1.19230254` instance and pivoted the following day to cyclic-quotient compression ([`teorth/optimizationproblems#148`](https://github.com/teorth/optimizationproblems/pull/148), `[O2026]`).
2. **Our Independent Re-Derivation and `PR #236` (`2026-10-18/19`, `[M2026]`):**
   On the night of `2026-10-18/19`, our agent inspected `constants/3a.md` and `kleinwaks/masked-digit-sum-difference-bound` (`CoreConstruction.lean`, theorem `residue_word_injective`) without reading the comment thread of closed `PR #134`. Because $(B = 17,086, q = 27,995)$ is the unique global optimum of the 2-parameter scan $(B, q)$ over the 6-generator semigroup $G = \{3, 4\} \times \{506, 508, 529\}$ at block length $k = 1$, our sweep converged on the same $(17086, 27995)$ instance (plus the secondary certificate $(17032, 27995)$ on Kleinwaks's original cutoff $B = 17,032$). We explicitly credit `@carson-olaf`'s August 12 comment in `PR #134` for prior discovery of the $(17086, 27995)$ tuple.
3. **Block-Length $k = 2, 3$ Extension (`2026-10-19`, `[Syl2026]`, `PR #238`):**
   Eleven hours after `PR #236` was opened on `2026-10-19`, `xSyllaa` ([`teorth/optimizationproblems#238`](https://github.com/teorth/optimizationproblems/pull/238), `[Syl2026]`) extended the finite controlled-carry evaluation to block lengths $k = 2$ ($1.19281555^*$) and $k = 3$ ($1.19359680^*$) by dropping the single self-inverse residue $q^k / 2$.
4. **Two Independent From-Scratch Replays (`2026-11-03` and `2026-11-05`):**
   - On `2026-11-03`, `@elder-plinius` (`V3R1T4S#485`) independently re-derived and confirmed `|M| = 3,153`, `|M + M| = 18,835`, all `27,995` residues covered, and $C_{3a} > 1.19230254$ without running our code.
   - On `2026-11-05`, **Arhan Canli (`@arhancanli`, Quantavane)** published a complete, standalone from-scratch replay ([`arhancanli/quantavane-replays/tree/main/c3a`](https://github.com/arhancanli/quantavane-replays/tree/86099d017e3dc64ff2865a54d0fc55a35093430d/c3a)) built solely from Theorems 1–4 of our `README.md`, reproducing all three certificates (`17086_27995`, `17032_27995`, and the `[K2026b]` control `17032_34065`), all `13,997` rows of `pruned_differences_17086_27995.tsv`, and 4 negative (red) controls in 3 seconds.

---

## 2. Internal Decision Trajectory Audit (`2026-10-18/19`)

Reviewing our agent's step-by-step execution logs (`Steps 3064–4148` of the Oct 18–19 session) highlights two structural lessons:

### What Worked: Designing for 3-Second Zero-Dependency Replay
- **Why odd base $q < 2B + 1$ at $k = 1$ with $V = 2U$ was effective:** In an even base $q$, the residue $r = q/2$ is self-inverse ($q - r \equiv r \pmod q$), which in `[K2026b]` required oriented-block machinery (`OrientedBlocks.lean`). Choosing an odd base $q = 27,995$ partitioned $\{1, \dots, q-1\}$ into $13,997$ disjoint pairs $\{r, q-r\}$ with zero self-inverse residue, and doubling $V = 2U$ satisfied $|V - V| \le 2\max U + 1 < 4\max U + 1 = 2\max V + 1$ unconditionally.
- **Why $k = 1$ won the third-party replay race:** Because the $k = 1$ witness table has only `13,997` rows (`662 KB`) and `check_c3a.py` uses 128-bit integer-interval `atanh` + Robbins–Stirling bounds (`0.39s`), external verifiers (`@arhancanli`, `@elder-plinius`) could rebuild and verify the entire calculation in 3 seconds on standard Python, whereas $k = 3$ (`q^3 \approx 1.97 \times 10^{13}` residues, requiring multi-GB C++ hashing) remains in Class `(b)` of `ASTERISK_INDEX.md` without an independent replay.

### What Was Suboptimal: Three Blind Spots
1. **Failed carry-free mask surgery (`Steps 3097–3856`):** The agent spent its first hour trying to improve `[K2026b]` *inside* the carry-free regime $Q = 2B + 1$ by deleting elements from $M$ and scanning 4-parameter glued semigroups $a\langle r, s\rangle + b\mathbb{N}$ in C++. That scan proved $(r=22, s=23, a=23, b=508, B=17032)$ was already the global optimum for $Q = 2B + 1$.
2. **Incomplete PR-comment literature scan:** The agent read `constants/3a.md` and merged `PR #146`, but did not scrape comments on closed `PR #134` or open `PR #148`, missing both `@carson-olaf`'s August 12 comment on $(17086, 27995)$ and his two-temperature cyclic-compression PR (`#148`).
3. **Satisficing at $k = 1$ positional encoding:** Once $(B = 17,086, q = 27,995)$ cleared the `1.19102809` finite bar by `+0.00127445`, the agent stopped to package the `0.39s` certificate rather than either (a) running the $k = 2, 3$ block histograms before publishing `PR #236`, or (b) replacing positional base-$q$ packing ($\log q$ denominator) with linear compression modulo a prime $p > |\mathcal{V}_N - \mathcal{V}_N|$ ($\rho$ denominator) and decoupling the sum/difference temperatures (`[O2026]`, `PR #148`).

---

## 3. New Mathematical Corollary from This Review: Beating the 1999 `[HRY1999]` Record on $C_{3e}$ (`constants/3e.md`)

Prompted by `@arhancanli`'s replay to compare the positional base-$q$ method against `[O2026]`'s two-temperature cyclic compression across all five sum-difference constants (`constants/3a.md`–`3e.md`), we identified an immediate finite-depth consequence for the **unnormalized single-set sum-difference constant $C_{3e}$** ([`constants/3e.md`](https://github.com/teorth/optimizationproblems/blob/main/constants/3e.md), Problem 6.43 of `[GGSWT2025]`):
$$C_{3e} = \sup_{|A| \ge 2} \frac{\log |A - A|}{\log |A + A|}.$$

- On `constants/3e.md`, the best known lower bound has stood since **1999** (`[HRY1999]`, Hennecart–Robert–Yudin 1999):
  $$C_{3e} \ge \frac{\log(1 + \sqrt{2})}{\log 2} = 1.27155330316361201881\dots$$
  from the gapless simplex $V(m, m/2) = \{x \in \mathbb{N}_0^m : \sum x_i \le m/2\}$ (and in `[GGSWT2025]`, AlphaEvolve reached only $\approx 1.21$).
- Unlike $C_{3a}$ (which requires $|V - V| < 2\max V + 1$), $C_{3e}$ imposes **no constraint on $\max A$**.
- Therefore, taking the budgeted simplex $\mathcal{V}_N = \{a \in M^N : \sum_{i=0}^{N-1} a_i \le L\}$ over `[O2026]`'s truncated numerical semigroup $M = \langle 4, 5 \rangle \cap [0, B]$ and projecting to $\mathbb{Z}$ via the **elementary carry-free base $Q = 2B + 1$** ($A_N = \{\sum_{i=0}^{N-1} a_i Q^i : a \in \mathcal{V}_N\}$) is an exact Freiman $2$-isomorphism ($|A_N \pm A_N| = |\mathcal{V}_N \pm \mathcal{V}_N|$) requiring **neither cyclic compression nor Bertrand's postulate**.
- Using our 128-bit pure integer-interval `atanh` + Lean `StirlingBounds.lean` verifier (and 60-digit `mpmath.iv`), we certify in `< 0.1s` (see [`c3e_finite_certificate/`](./c3e_finite_certificate/README.md)):
  - **At $B = 80, Q = 161, N = 10^{13}$ (`x = 8149/10000, y = 42571/50000`):**
    $$C_{3e}(A_N) > \mathbf{1.27255796845801701855} > \mathbf{1.27255796} \quad (\text{+0.00100466 over `[HRY1999]`})$$
  - **At $B = 160, Q = 321, N = 10^{15}$ (`x = 814897/1000000, y = 851418/1000000`):**
    $$C_{3e}(A_N) > \mathbf{1.27255802020996480086} > \mathbf{1.27255802} \quad (\text{+0.00100472 over `[HRY1999]`})$$
