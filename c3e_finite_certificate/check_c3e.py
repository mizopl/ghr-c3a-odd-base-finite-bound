#!/usr/bin/env python3
"""
Standalone deterministic verifier for the unnormalized single-set sum-difference
constant C_{3e} = sup_{|A| >= 2} log|A - A| / log|A + A|
(teorth/optimizationproblems/blob/main/constants/3e.md, Problem 6.43 of [GGSWT2025]):

  1. Primary finite certificate (B = 80, Q = 161, N = 10^13):
       C_{3e}(A_N) > 1.27255796845801701855 > 1.27255796
  2. Secondary finite certificate (B = 160, Q = 321, N = 10^15):
       C_{3e}(A_N) > 1.27255802020996480086 > 1.27255802
  3. Baseline comparison against [HRY1999] (Hennecart-Robert-Yudin 1999):
       log(1 + sqrt(2)) / log(2) = 1.27155330316361201881...
     Margin over [HRY1999]: +0.00100466 (B = 80) and +0.00100472 (B = 160).

Credit: The truncated numerical semigroup M = <4, 5> cap [0, 80] and two-temperature
tilt parameters (x = 8149/10000, y = 42571/50000) at N = 10^13 were introduced by
Carson Olafson (@carson-olaf, [O2026], teorth/optimizationproblems#148) for C_{3a}.
Here we use carry-free base Q = 2B + 1 evaluation (a Freiman 2-isomorphism requiring
neither cyclic compression nor Bertrand's postulate) to certify C_{3e} at finite depth.

Uses both:
  (a) 100% pure integer-interval arithmetic (128-bit fixed-point rational atanh
      Taylor enclosures + Lean StirlingBounds.lean factorial bounds), and
  (b) 60-digit mpmath interval arithmetic (Robbins-Stirling bounds).
"""

import json
import os
import sys
from itertools import product
from mpmath import mp, iv

SH = 128
ONE = 1 << SH
GENS = [4, 5]


def div_floor(num: int, den: int) -> int:
    return num // den


def div_ceil(num: int, den: int) -> int:
    return (num + den - 1) // den


def atanh_fp_iv(p: int, q: int, terms: int = 30):
    p2 = p * p
    q2 = q * q
    pow_lo = div_floor(p << SH, q)
    pow_hi = div_ceil(p << SH, q)
    sum_lo = 0
    sum_hi = 0
    for j in range(terms):
        sum_lo += div_floor(pow_lo, 2 * j + 1)
        sum_hi += div_ceil(pow_hi, 2 * j + 1)
        pow_lo = div_floor(pow_lo * p2, q2)
        pow_hi = div_ceil(pow_hi * p2, q2)
    tail_hi = div_ceil(pow_hi * q2, (2 * terms + 1) * (q2 - p2))
    return sum_lo, sum_hi + tail_hi


LN2_LO_35, LN2_HI_35 = [2 * x for x in atanh_fp_iv(1, 3, 35)]


def log_int_fp_iv(n: int, terms: int = 30):
    e = n.bit_length() - 1
    p = 1 << e
    loz, hiz = atanh_fp_iv(n - p, n + p, terms)
    return e * LN2_LO_35 + 2 * loz, e * LN2_HI_35 + 2 * hiz


def log_rat_fp_iv(num: int, den: int, terms: int = 35):
    nlo, nhi = log_int_fp_iv(num, terms)
    dlo, dhi = log_int_fp_iv(den, terms)
    return nlo - dhi, nhi - dlo


def fp_arr_lo(x_lo: int, sh: int, max_k: int):
    arr = [1 << sh]
    cur = 1 << sh
    for _ in range(max_k):
        cur = (cur * x_lo) >> sh
        arr.append(cur)
    return arr


def fp_arr_hi(x_hi: int, sh: int, max_k: int):
    arr = [1 << sh]
    cur = 1 << sh
    mask = (1 << sh) - 1
    for _ in range(max_k):
        p = cur * x_hi
        cur = (p >> sh) + (1 if (p & mask) != 0 else 0)
        arr.append(cur)
    return arr


def verify_toy_carry_free_bruteforce():
    """
    Brute-force check at N = 3 on M = {0, 4, 5}, B = 5, carry-free base Q = 2B + 1 = 11:
    verifies that carry-free base-Q evaluation is a Freiman 2-isomorphism on V_N
    (|A_N + A_N| == |V_N + V_N| and |A_N - A_N| == |V_N - V_N|) and checks the
    multinomial difference lower bound and saddle-point sumset upper bound.
    """
    M = [0, 4, 5]
    B = 5
    Q = 2 * B + 1  # 11
    N = 3
    # Witness for d = 1 is (5, 4) with cost kappa(1) = 9; take n_1 = 1, n_0 = 1 -> L = 9.
    L = 9
    V_words = [w for w in product(M, repeat=N) if sum(w) <= L]
    A_N = sorted({sum(w[i] * (Q ** i) for i in range(N)) for w in V_words})
    assert len(A_N) == len(V_words)

    V_plus_V = {tuple(u[i] + v[i] for i in range(N)) for u in V_words for v in V_words}
    V_minus_V = {tuple(u[i] - v[i] for i in range(N)) for u in V_words for v in V_words}
    A_plus_A = {a + b for a in A_N for b in A_N}
    A_minus_A = {a - b for a in A_N for b in A_N}

    assert len(A_plus_A) == len(V_plus_V)
    assert len(A_minus_A) == len(V_minus_V)

    # Multinomial word count for n_1 = 1, n_{-1} = 1, n_0 = 1 is 3! / (1! 1! 1!) = 6
    D_N = 6
    S_set = sorted({a + b for a in M for b in M})
    y = 0.85
    P_plus = sum(y ** s for s in S_set)
    S_N_bound = (P_plus ** N) / (y ** (2 * L))
    assert len(A_minus_A) >= D_N
    assert len(A_plus_A) <= S_N_bound


def reconstruct_and_verify_c3e_certificate(cert_path: str):
    with open(cert_path, "r") as f:
        cert = json.load(f)

    assert cert["constant_id"] == "C_3e"
    assert cert["problem_reference"] == "teorth/optimizationproblems/blob/main/constants/3e.md (Problem 6.43 of [GGSWT2025])"
    assert cert["baseline_beaten"] == "log(1+sqrt(2))/log(2) = 1.27155330316361201881 ([HRY1999])"
    assert cert["semigroup_generators"] == GENS
    assert cert["fixed_point_shift_bits"] == SH
    assert cert["cfFloorOK"] is True

    B = int(cert["B"])
    Q = int(cert["carry_free_base_Q"])
    N = int(cert["N"])
    x_num = int(cert["x_num"])
    x_den = int(cert["x_den"])
    y_num = int(cert["y_num"])
    y_den = int(cert["y_den"])
    assert Q == 2 * B + 1

    # Reconstruct M = <4, 5> cap [0, B]
    reach = [False] * (B + 1)
    reach[0] = True
    for n in range(B + 1):
        if reach[n]:
            for g in GENS:
                if n + g <= B:
                    reach[n + g] = True
    M = [n for n in range(B + 1) if reach[n]]
    gaps = [n for n in range(B + 1) if not reach[n]]
    assert gaps == cert["semigroup_gaps"]
    assert len(M) == cert["mask_size"]
    assert M[0] == 0 and M[-1] == B == cert["mask_max"]
    m_set = set(M)

    sums = sorted({a + b for a in M for b in M})
    assert len(sums) == cert["sum_support_size"]
    assert sums[0] == 0 and sums[-1] == 2 * B == cert["sum_support_max"]

    # Reconstruct minimum-cost witnesses kappa(d) = min{a + b : a, b in M, a - b = d}
    kappa = {}
    wit = {}
    for d in range(1, B + 1):
        for b in M:
            if (b + d) in m_set:
                kappa[d] = 2 * b + d
                wit[d] = (b + d, b)
                break
        assert d in kappa, f"Difference d={d} not realized in M - M"
        a_val, b_val = wit[d]
        assert a_val in m_set and b_val in m_set
        assert a_val - b_val == d and a_val + b_val == kappa[d]

    assert len(kappa) == B == cert["positive_differences_count"]
    assert 2 * len(kappa) + 1 == Q == cert["difference_alphabet_size"]

    # Exact 128-bit fixed-point verification of floor counts n_d = floor(N x^{kappa(d)} / Z(x))
    xf_lo = (x_num << SH) // x_den
    xf_hi = ((x_num << SH) + x_den - 1) // x_den
    ax_lo = fp_arr_lo(xf_lo, SH, 2 * B)
    ax_hi = fp_arr_hi(xf_hi, SH, 2 * B)
    W_lo = ax_lo[0] + 2 * sum(ax_lo[kappa[d]] for d in range(1, B + 1))
    W_hi = ax_hi[0] + 2 * sum(ax_hi[kappa[d]] for d in range(1, B + 1))

    counts = []
    for d in range(1, B + 1):
        c_val = kappa[d]
        cnt_lo = (N * ax_lo[c_val]) // W_hi
        cnt_hi = (N * ax_hi[c_val]) // W_lo
        assert cnt_lo == cnt_hi, f"Floor ambiguity at d={d}: {cnt_lo} != {cnt_hi}"
        assert cnt_lo > 0
        counts.append(cnt_lo)

    n0 = N - 2 * sum(counts)
    L = sum(cnt * kappa[d] for cnt, d in zip(counts, range(1, B + 1)))
    assert n0 > 0 and n0 == cert["n_0"]
    assert L >= B and L == cert["L"] and 2 * L == cert["two_L"]

    # 1. Pure integer-interval verification (128-bit atanh + Lean StirlingBounds.lean)
    lN_lo, _ = log_int_fp_iv(N, 35)
    _, ln0_hi = log_int_fp_iv(n0, 30)
    logD_lo = N * lN_lo - (N << SH) + (lN_lo >> 1)
    logD_lo -= (n0 * ln0_hi - (n0 << SH) + div_ceil(ln0_hi, 2) + ONE)
    for cnt in counts:
        _, lcnt_hi = log_int_fp_iv(cnt, 30)
        logD_lo -= 2 * (cnt * lcnt_hi - (cnt << SH) + div_ceil(lcnt_hi, 2) + ONE)

    yf_hi = ((y_num << SH) + y_den - 1) // y_den
    ay_hi = fp_arr_hi(yf_hi, SH, 2 * B)
    P_plus_fp_hi = sum(ay_hi[s] for s in sums)
    _, logP_hi = log_rat_fp_iv(P_plus_fp_hi, ONE, 35)
    logy_lo, _ = log_rat_fp_iv(y_num, y_den, 35)
    logS_hi = N * logP_hi - 2 * L * logy_lo

    dec_scale = 10**20
    c3e_int_scaled = (logD_lo * dec_scale) // logS_hi
    s_int = str(c3e_int_scaled)
    c3e_int_str = s_int[0] + "." + s_int[1:]
    assert c3e_int_str == cert["certified_lower_bound_pure_integer_lean_stirling_floor20dp"]

    # 2. 60-digit mpmath interval verification (Robbins-Stirling bounds)
    iv.dps = 60
    pi_iv = iv.pi

    def stirling_lower_iv(n):
        ni = iv.mpf(n)
        return ni * iv.log(ni) - ni + iv.mpf("0.5") * iv.log(2 * pi_iv * ni) + iv.mpf(1) / (12 * ni + 1)

    def stirling_upper_iv(n):
        ni = iv.mpf(n)
        return ni * iv.log(ni) - ni + iv.mpf("0.5") * iv.log(2 * pi_iv * ni) + iv.mpf(1) / (12 * ni)

    logD_iv = stirling_lower_iv(N) - stirling_upper_iv(n0)
    for cnt in counts:
        logD_iv -= 2 * stirling_upper_iv(cnt)
    y_iv = iv.mpf(y_num) / iv.mpf(y_den)
    P_plus_iv = sum((y_iv ** s for s in sums), iv.mpf(0))
    logS_iv = iv.mpf(N) * iv.log(P_plus_iv) - iv.mpf(2 * L) * iv.log(y_iv)
    c3e_iv = logD_iv / logS_iv

    hry_iv = iv.log(1 + iv.sqrt(2)) / iv.log(2)
    assert c3e_iv.a > hry_iv.b

    mp.dps = 60
    assert mp.nstr(mp.mpf(logD_iv.a), 28) == cert["log_D_N_lower_bound"]
    assert mp.nstr(mp.mpf(logS_iv.b), 28) == cert["log_S_N_upper_bound"]
    c3e_mp_lo = mp.mpf(c3e_iv.a)
    c3e_mp_scaled = int(mp.floor(c3e_mp_lo * (mp.mpf(10) ** 20)))
    s_mp = str(c3e_mp_scaled)
    c3e_mp_str = s_mp[0] + "." + s_mp[1:]
    assert c3e_mp_str == cert["certified_lower_bound_mpmath60_floor20dp"]
    assert c3e_mp_str[:10] == cert["certified_lower_bound_8dp"]
    assert c3e_int_str[:10] == cert["certified_lower_bound_8dp"]

    margin = float(c3e_int_str) - float(mp.nstr(mp.mpf(hry_iv.b), 20))
    return {
        "B": B,
        "Q": Q,
        "N": N,
        "mask_size": len(M),
        "sum_support_size": len(sums),
        "n_0": n0,
        "L": L,
        "c3e_mp60_floor20dp": c3e_mp_str,
        "c3e_int_floor20dp": c3e_int_str,
        "c3e_8dp": cert["certified_lower_bound_8dp"],
        "margin_over_HRY1999": margin,
    }


def main():
    here = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    verify_toy_carry_free_bruteforce()
    print("[PASS] Toy carry-free brute-force check (M={0,4,5}, B=5, Q=11, N=3): Freiman 2-isomorphism & bounds verified.")

    for fname in ["c3e_finite_certificate_80_161.json", "c3e_finite_certificate_160_321.json"]:
        res = reconstruct_and_verify_c3e_certificate(os.path.join(here, fname))
        print(
            f"[PASS] {fname} (B={res['B']}, Q={res['Q']}, N={res['N']}): "
            f"|M|={res['mask_size']}, |S|={res['sum_support_size']}, n_0={res['n_0']}, L={res['L']}, "
            f"C_3e_int >= {res['c3e_int_floor20dp']}, C_3e_mp60 >= {res['c3e_mp60_floor20dp']} "
            f"(margin over [HRY1999] 1.27155330 = +{res['margin_over_HRY1999']:.8f})"
        )
        assert res["margin_over_HRY1999"] > 0.001

    print("ALL C_3e CHECKS PASSED.")


if __name__ == "__main__":
    main()
