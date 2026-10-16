# ============================================================
# UOV / MAYO / QR-UOV (symmetric public forms):
# Independence verification of the quadratic equations of the
# extended intersection attack after eliminating one block
#
# Counterpart of snova_toy_independence.sage, which does the same
# for the non-symmetric (ordered pair) convention of SNOVA.
#
# Setting.  t blocks y_1, ..., y_t in F_q^n; the linear relation
# of the attack,
#       W_t y_t = W_1 y_1 + ... + W_{t-1} y_{t-1},
# is used to eliminate y_t, leaving (t-1)n variables.  The
# relations that are written down are
#       P_k(y_i)        = 0     (1 <= i <= t,     1 <= k <= m)
#       P'_k(y_i, y_j)  = 0     (1 <= i < j <= t, 1 <= k <= m)
# with P'_k(x, y) = x^T (Q_k + Q_k^T) y, hence
#       num_eqns = t(t+1)/2 * m .
# The polar form is symmetric in its two arguments, so only the
# unordered pairs appear; this is the convention of UOV, MAYO and
# QR-UOV.  It differs from SNOVA, where both orderings of a pair
# are distinct relations and the count is t^2 * m_eff.
#
# Measurement.  The rank of the coefficient matrix of the
# substituted relations is the number of independent relations, so
#       deficit = num_eqns - rank
# is the number of redundant ones.  Prediction:
#       deficit = t          (one per block),
# i.e. the reduced system has t(t+1)/2*m - t independent equations,
# and at t = 2 the rank is 3m - 2 (the classical 3o - 2 for UOV).
#
# The script also verifies the derivation of the deficit: with
# W_j = sum_k lam_jk B_k, B_k = Q_k + Q_k^T, and
#       sigma_j = 1 (j < t),  sigma_t = -1,
# the combination
#       sum_{j != i} eps_i sigma_j sum_k lam_jk P'_k(y_i, y_j)
#           - 2 sum_k lam_ik P_k(y_i),      eps_i = -sigma_i,
# vanishes identically for every block i (the second term is
# absent in characteristic two, where 2 = 0).
# ============================================================

from collections import defaultdict


def mat_to_vec(M):
    nr, nc = M.nrows(), M.ncols()
    return vector(M.base_ring(), [M[i, j] for i in range(nr) for j in range(nc)])


def build_uov(v, o, q):
    """UOV-shaped instance: Q_k = T^T F_k T with a vanishing oil-oil block.

    Over GF(2^e) the representation matrices are upper triangular, over an
    odd-characteristic field they are symmetric.  Returns (Fq, Q_list).
    """
    Fq = GF(q)
    n = v + o
    symmetric = (q % 2 == 1)
    F_list = []
    for _ in range(o):
        F = matrix(Fq, n, n)
        for i in range(n):
            for j in range(i, n):
                F[i, j] = Fq.random_element()
        for i in range(v, n):                       # oil-oil block vanishes
            for j in range(i, n):
                F[i, j] = Fq.zero()
        if symmetric:
            for i in range(n):
                for j in range(i):
                    F[i, j] = F[j, i]
        F_list.append(F)
    T = identity_matrix(Fq, n)                      # oil mixing
    for i in range(v):
        for j in range(o):
            T[i, v + j] = Fq.random_element()
    return Fq, [T.transpose() * F * T for F in F_list]


def check_uov(v, o, q, t, seed=None, mode="span", max_attempts=400):
    """Rank / deficit of the t-block system after eliminating y_t."""
    if seed is not None:
        set_random_seed(seed)

    Fq, Q = build_uov(v, o, q)
    n = v + o
    m = len(Q)
    B = [Q[k] + Q[k].transpose() for k in range(m)]  # polar matrices

    V_dim = matrix(Fq, [list(mat_to_vec(M)) for M in B]).rank()

    # ---- W_1, ..., W_t, with their coefficients in B_1, ..., B_m ----
    Ws, lams = [], []
    for _ in range(t):
        W, lam = None, None
        for _ in range(max_attempts):
            if mode == "span":
                coeffs = [Fq.random_element() for _ in range(m)]
                cand = zero_matrix(Fq, n, n)
                for c, Bk in zip(coeffs, B):
                    if c != 0:
                        cand += c * Bk
            else:                                   # arbitrary invertible W
                coeffs = [Fq.zero()] * m
                cand = random_matrix(Fq, n, n)
            if cand.rank() == n:
                W, lam = cand, coeffs
                break
        if W is None:
            return {'v': v, 'o': o, 'q': q, 't': t, 'mode': mode,
                    'status': 'no invertible W (%s)' % mode}
        Ws.append(W)
        lams.append(lam)

    # ---- substitution y_i = Nmaps[i] * z, z of length (t-1)n ----
    free = (t - 1) * n
    Nmaps = []
    for i in range(t - 1):
        Mi = zero_matrix(Fq, n, free)
        for r in range(n):
            Mi[r, i * n + r] = Fq.one()
        Nmaps.append(Mi)
    Mt = zero_matrix(Fq, n, free)
    Wt_inv = Ws[t - 1].inverse()
    for i in range(t - 1):
        Mt[:, i * n:(i + 1) * n] = Wt_inv * Ws[i]
    Nmaps.append(Mt)

    # ---- monomials of z^T X z ----
    mono = {}
    col = 0
    for a in range(free):
        for b in range(a, free):
            mono[(a, b)] = col
            col += 1
    num_monos = col

    def form_row(X):
        row = [Fq.zero()] * num_monos
        for a in range(free):
            c = X[a, a]
            if c != 0:
                row[mono[(a, a)]] += c
            for b in range(a + 1, free):
                c = X[a, b] + X[b, a]
                if c != 0:
                    row[mono[(a, b)]] += c
        return row

    rows, row_info = [], []
    for i in range(t):                              # block relations
        for k in range(m):
            rows.append(form_row(Nmaps[i].transpose() * Q[k] * Nmaps[i]))
            row_info.append(('P', i, k))
    for i in range(t):                              # pair relations, i < j
        for j in range(i + 1, t):
            for k in range(m):
                rows.append(form_row(Nmaps[i].transpose() * B[k] * Nmaps[j]))
                row_info.append(('B', i, j, k))

    coeff_mat = matrix(Fq, rows)
    rank_val = coeff_mat.rank()
    num_eqns = len(rows)
    deficit = num_eqns - rank_val
    kernel_dim = coeff_mat.left_kernel().dimension()

    # ---- the predicted redundant combinations ----
    sig = [Fq.one()] * t
    sig[t - 1] = Fq(-1)
    two = Fq(2)
    preds = []
    for i in range(t):
        eps = -sig[i]
        c = [Fq.zero()] * num_eqns
        for idx, info in enumerate(row_info):
            if info[0] == 'B':
                _, a, b, k = info
                if a == i:
                    j = b
                elif b == i:
                    j = a
                else:
                    continue
                c[idx] = eps * sig[j] * lams[j][k]
            else:
                _, a, k = info
                if a == i:
                    c[idx] = -two * lams[i][k]
        preds.append(c)

    pred_vanish = []
    for c in preds:
        comb = vector(Fq, c) * coeff_mat
        pred_vanish.append(all(x == 0 for x in comb))
    pred_rank = matrix(Fq, preds).rank()

    return {
        'v': v, 'o': o, 'q': q, 't': t, 'mode': mode,
        'n': n, 'm': m, 'free': free, 'num_monos': num_monos,
        'V_dim': V_dim, 'num_eqns': num_eqns, 'rank': rank_val,
        'deficit': deficit, 'kernel_dim': kernel_dim,
        'pred_vanish': all(pred_vanish), 'pred_rank': pred_rank,
        'preds': preds, 'row_info': row_info, 'lams': lams,
        'status': 'ok',
    }


def main():
    print("=" * 100)
    print("  UOV / MAYO / QR-UOV: Quadratic Equation Independence after y_t Elimination")
    print("  Constraint: y_t = W_t^{-1} (W_1 y_1 + ... + W_{t-1} y_{t-1})")
    print("  Equations : P_k(y_i) = 0 and P'_k(y_i,y_j) = 0, total t(t+1)/2 * m")
    print("  Method    : direct term-by-term substitution, exact rank over F_q")
    print("=" * 100)

    all_results = []
    for q in [16, 127]:
        for o in [2, 3]:
            for t in [2, 3, 4]:
                regimes = []
                last = [v for v in range((t - 1) * o + 1, t * o)
                        if v > 1 and v + o <= 20 and (q % 2 == 0 and (v + o) % 2 == 0 or q % 2 == 1)]
                mid = [v for v in range(t * o + 1, (t + 1) * o + 1)
                       if v > 1 and v + o <= 20 and (q % 2 == 0 and (v + o) % 2 == 0 or q % 2 == 1)]
                if last:
                    regimes.append((last[0], 'last block'))
                if mid:
                    regimes.append((mid[0], 'middle'))

                print("\n" + "-" * 100)
                print("  q = %d,  o = %d,  t = %d" % (q, o, t))
                print("-" * 100)
                print("  %-11s %-9s %4s %4s %4s %7s %7s %7s %7s %7s %6s"
                      % ("(v,o)", "regime", "n", "m", "vars", "monos", "eqns",
                         "rank", "deficit", "kernel", "pred"))
                print("  " + "-" * 92)

                for (vv, regime) in regimes:
                    seed = 1000 * t + 100 * vv + 10 * o + (0 if q == 16 else 7)
                    res = check_uov(vv, o, q, t, seed=seed)
                    if res['status'] != 'ok':
                        print("  (v=%2d,o=%2d) %-9s %s" % (vv, o, regime, res['status']))
                        continue
                    all_results.append(res)
                    print("  (%2d,%2d)   %-9s %4d %4d %4d %7d %7d %7d %7d %7d %6s"
                          % (vv, o, regime, res['n'], res['m'], res['free'],
                             res['num_monos'], res['num_eqns'], res['rank'],
                             res['deficit'], res['kernel_dim'],
                             "ok" if res['pred_vanish'] else "NO"))

    # ---- control: W outside the span of the public matrices ----
    print("\n" + "=" * 100)
    print("  CONTROL: W_i drawn arbitrarily (not from span{B_k})")
    print("=" * 100)
    print("  %-11s %4s %4s %7s %7s %7s %8s" % ("(v,o)", "q", "t", "eqns", "rank", "deficit", "kernel"))
    print("  " + "-" * 60)
    control = []
    for (vv, oo2, q2, t2) in [(9, 3, 16, 3), (10, 4, 16, 3), (7, 2, 127, 3)]:
        res = check_uov(vv, oo2, q2, t2, seed=99, mode="arbitrary")
        if res['status'] != 'ok':
            print("  (%2d,%2d)   %4d %4d   %s" % (vv, oo2, q2, t2, res['status']))
            continue
        control.append(res)
        print("  (%2d,%2d)   %4d %4d %7d %7d %7d %8d"
              % (vv, oo2, q2, t2, res['num_eqns'], res['rank'],
                 res['deficit'], res['kernel_dim']))

    # ---- summary ----
    print("\n" + "=" * 100)
    print("  SUMMARY")
    print("=" * 100)
    print("  %4s %4s %3s %11s %7s %7s %8s %8s %6s"
          % ("q", "o", "t", "(v,o)", "eqns", "rank", "deficit", "t", "pred"))
    print("  " + "-" * 76)
    for r in all_results:
        print("  %4d %4d %3d %11s %7d %7d %8d %8d %6s"
              % (r['q'], r['o'], r['t'], "(%d,%d)" % (r['v'], r['o']),
                 r['num_eqns'], r['rank'], r['deficit'], r['t'],
                 "ok" if r['pred_vanish'] else "NO"))
    print("  " + "-" * 76)

    ok1 = all(r['deficit'] == r['t'] for r in all_results)
    ok2 = all(r['kernel_dim'] == r['t'] for r in all_results)
    ok3 = all(r['pred_vanish'] for r in all_results)
    ok4 = all(r['pred_rank'] == r['t'] for r in all_results)
    ok5 = all(r['deficit'] == 0 for r in control)
    print("  deficit  = t            in all cases:  %s" % ("YES" if ok1 else "NO"))
    print("  kernel   = t            in all cases:  %s" % ("YES" if ok2 else "NO"))
    print("  predicted combinations vanish         :  %s" % ("YES" if ok3 else "NO"))
    print("  predicted combinations independent    :  %s" % ("YES" if ok4 else "NO"))
    print("  control (W outside span) has deficit 0:  %s" % ("YES" if ok5 else "NO"))

    stability()

    print("\n" + "=" * 100)
    print("  DONE")
    print("=" * 100)


def stability():
    """Deficit over repeated draws (fresh instances), for a few parameters."""
    print("\n" + "=" * 100)
    print("  Stability of the deficit over repeated draws")
    print("=" * 100)
    print("  %-9s %5s %3s   %s" % ("(v,o)", "q", "t", "deficits over 20 draws"))
    print("  " + "-" * 70)
    worst = None
    for (vv, oo2, q2, t2) in [(9, 3, 16, 3), (8, 4, 16, 3), (7, 2, 127, 3),
                              (12, 4, 16, 4)]:
        seen = {}
        for r in range(20):
            res = check_uov(vv, oo2, q2, t2, seed=1000 + 17 * r + vv)
            if res['status'] != 'ok':
                seen[res['status']] = seen.get(res['status'], 0) + 1
                continue
            key = res['deficit']
            seen[key] = seen.get(key, 0) + 1
            if worst is None or key < worst:
                worst = key
        print("  (%2d,%2d)   %5d %3d   %s" % (vv, oo2, q2, t2, seen))
    print("  " + "-" * 70)
    print("  smallest deficit seen: %s  (prediction: the value of t in each row)"
          % worst)


main()
