# ============================================================
# UOV / MAYO / QR-UOV: end-to-end verification of the attack
# procedure (Algorithm 1 of the paper) on toy instances
#
# Companion of uov_toy_independence.sage: that script counts the
# relations, this one checks that they vanish where they should.
#
# For a UOV-shaped instance (Q_k = T^T F_k T, oil-oil block of F_k
# zero) the script
#   * checks dim O = o, dim O^perp = v, that the P_k vanish on O,
#     that the polar forms vanish on O x O, and that W O is inside
#     O^perp for every W in span{B_k}, B_k = Q_k + Q_k^T;
#   * draws W_1, ..., W_t from span{B_k}, looks for a non-trivial
#     element of W_1 O cap (W_2 O + ... + W_t O) by linear algebra,
#     and measures the number of draws needed and the success rate
#     against the guessing exponent q^(v-to+1);
#   * verifies that the solution returned by that intersection
#     satisfies the linear relation and all relations of the
#     reduced system.
# ============================================================


def mat_to_vec(M):
    nr, nc = M.nrows(), M.ncols()
    return vector(M.base_ring(), [M[i, j] for i in range(nr) for j in range(nc)])


def build_uov(v, o, q):
    """UOV-shaped instance; returns (Fq, Q_list, O_basis)."""
    Fq = GF(q)
    n = v + o
    symmetric = (q % 2 == 1)
    F_list = []
    for _ in range(o):
        F = matrix(Fq, n, n)
        for i in range(n):
            for j in range(i, n):
                F[i, j] = Fq.random_element()
        for i in range(v, n):
            for j in range(i, n):
                F[i, j] = Fq.zero()
        if symmetric:
            for i in range(n):
                for j in range(i):
                    F[i, j] = F[j, i]
        F_list.append(F)
    T = identity_matrix(Fq, n)
    for i in range(v):
        for j in range(o):
            T[i, v + j] = Fq.random_element()
    Q = [T.transpose() * F * T for F in F_list]
    Tinv = T.inverse()
    O_basis = [Tinv.column(v + j) for j in range(o)]      # O = T^{-1}(last o)
    return Fq, Q, O_basis


def random_in_span(Fq, B, n):
    while True:
        coeffs = [Fq.random_element() for _ in range(len(B))]
        W = zero_matrix(Fq, n, n)
        for c, Bk in zip(coeffs, B):
            if c != 0:
                W += c * Bk
        if W.rank() == n:
            return W


def eval_quad(Fq, X, x):
    return (vector(Fq, list(x)) * X * vector(Fq, list(x)))


def eval_bil(Fq, X, x, y):
    return (vector(Fq, list(x)) * X * vector(Fq, list(y)))


def find_intersection(Fq, W, others, Ob, n):
    """Solve x = W a = sum_i W_i b_i with a, b_i in O; returns (x, a, bs)."""
    d = len(Ob)
    cols = [W * Ob[j] for j in range(d)]
    for W2 in others:
        for j in range(d):
            cols.append(-(W2 * Ob[j]))
    K = matrix(Fq, n, len(cols))
    for j, cv in enumerate(cols):
        for i in range(n):
            K[i, j] = cv[i]
    for z in K.right_kernel().basis():
        x = vector(Fq, n)
        for j in range(d):
            if z[j] != 0:
                x += z[j] * cols[j]
        if x.is_zero():
            continue
        a = vector(Fq, n)
        for j in range(d):
            if z[j] != 0:
                a += z[j] * Ob[j]
        bs = []
        for i in range(len(others)):
            b = vector(Fq, n)
            for j in range(d):
                if z[d + i * d + j] != 0:
                    b += z[d + i * d + j] * Ob[j]
            bs.append(b)
        return x, a, bs
    return None


def check_procedure(v, o, q, t, seed=None, trials=2000):
    if seed is not None:
        set_random_seed(seed)
    Fq, Q, Ob = build_uov(v, o, q)
    n = v + o
    m = len(Q)
    B = [Q[k] + Q[k].transpose() for k in range(m)]
    out = {'v': v, 'o': o, 'q': q, 't': t}

    Obm = matrix(Fq, [list(x) for x in Ob])
    out['dim_O'] = Obm.rank()
    out['dim_Operp'] = Obm.right_kernel().dimension()

    # genericity check: the images W O for W in the whole span V should fill
    # O^perp.  A few instances (probability about 1/q) are degenerate here and
    # then the freshness test never fails; the script reports which case it saw.
    probes = []
    for _ in range(20):
        W = random_in_span(Fq, B, n)
        for x in Ob:
            probes.append(W * x)
    out['dim_V_image'] = matrix(Fq, [list(x) for x in probes]).rank()
    if out['dim_V_image'] < out['dim_Operp']:
        out['status'] = ('degenerate instance: the images of V span only %d of '
                         'the %d dimensions of O^perp' % (out['dim_V_image'],
                                                          out['dim_Operp']))
        return out

    ok = True
    for k in range(m):
        for x in Ob:
            if eval_quad(Fq, Q[k], x) != 0:
                ok = False
    for _ in range(20):
        c = [Fq.random_element() for _ in range(o)]
        x = sum(c[j] * Ob[j] for j in range(o))
        for k in range(m):
            if eval_quad(Fq, Q[k], x) != 0:
                ok = False
    out['P_vanish'] = ok

    ok = True
    for k in range(m):
        for x in Ob:
            for y in Ob:
                if eval_bil(Fq, B[k], x, y) != 0:
                    ok = False
    out['Ppolar_vanish'] = ok

    Ws = [random_in_span(Fq, B, n) for _ in range(t)]
    ok = all(eval_bil(Fq, identity_matrix(Fq, n), Ws[i] * x, y) == 0
             for i in range(t) for x in Ob for y in Ob)
    out['WO_in_Operp'] = ok

    others = Ws[1:]
    sum_images = [W * x for W in others for x in Ob]
    out['dim_sum'] = matrix(Fq, [list(x) for x in sum_images]).rank()
    img1 = [Ws[0] * x for x in Ob]
    d1 = matrix(Fq, [list(x) for x in img1]).rank()
    dall = matrix(Fq, [list(x) for x in img1 + sum_images]).rank()
    out['dim_cap'] = d1 + out['dim_sum'] - dall

    # draws until a non-trivial intersection
    pred_draws = q ** max(0, v - t * o + 1)
    got = None
    draws = 0
    while got is None and draws < 40 * pred_draws:
        W = random_in_span(Fq, B, n)
        draws += 1
        got = find_intersection(Fq, W, others, Ob, n)
        if got is not None:
            Ws[0] = W
    out['pred_draws'] = pred_draws
    out['draws'] = draws
    if got is None:
        out['status'] = 'no non-trivial intersection found'
        return out

    x, a, bs = got
    ys = [a] + bs
    rO = Obm.rank()
    out['solutions_in_O'] = all(
        matrix(Fq, [list(y) for y in Ob] + [list(y)]).rank() == rO for y in ys)
    lin = Ws[0] * ys[0] - sum(Ws[i + 1] * ys[i + 1] for i in range(len(bs)))
    out['linear_relation'] = lin.is_zero()
    ok = True
    for i in range(t):
        for k in range(m):
            if eval_quad(Fq, Q[k], ys[i]) != 0:
                ok = False
    out['block_vanish'] = ok
    ok = True
    for i in range(t):
        for j in range(i + 1, t):
            for k in range(m):
                if eval_bil(Fq, B[k], ys[i], ys[j]) != 0:
                    ok = False
    out['pair_vanish'] = ok

    # success rate of the freshness test
    hits = 0
    cnt = 0
    for _ in range(trials):
        W = random_in_span(Fq, B, n)
        cnt += 1
        if find_intersection(Fq, W, others, Ob, n) is not None:
            hits += 1
    out['trials'] = cnt
    out['hits'] = hits
    out['rate'] = float(hits) / cnt
    out['pred_rate'] = 1.0 / q if t * o <= v else 1.0
    out['status'] = 'ok'
    return out


def show(res):
    print("  %-46s %-16s %s" % ("quantity", "prediction", "measured"))
    print("  " + "-" * 84)
    rows = [
        ("dim O", "o = %d" % res['o'], str(res['dim_O'])),
        ("dim O^perp", "v = %d" % res['v'], str(res['dim_Operp'])),
        ("dim(sum_{W in V} W O)  [genericity]", "v = %d" % res['v'],
         str(res['dim_V_image'])),
        ("P_k vanish on O", "yes", "yes" if res['P_vanish'] else "NO"),
        ("P'_k vanish on O x O", "yes", "yes" if res['Ppolar_vanish'] else "NO"),
        ("W O in O^perp for W in span(B_k)", "yes",
         "yes" if res['WO_in_Operp'] else "NO"),
        ("dim(W_2 O + ... + W_t O)", "(t-1)o = %d" % ((res['t'] - 1) * res['o']),
         str(res['dim_sum'])),
        ("dim(W_1 O cap (W_2 O + ... + W_t O))", ">= to-v = %d" % max(0, res['t'] * res['o'] - res['v']),
         str(res['dim_cap'])),
        ("draws until a non-trivial intersection", "q^max(0,v-to+1) = %d" % res['pred_draws'],
         str(res['draws'])),
        ("success rate of the freshness test", "%.4f" % res['pred_rate'],
         "%.4f (%d/%d)" % (res['rate'], res['hits'], res['trials'])),
        ("W_i^{-1} x_i lies in O for the returned vectors", "yes",
         "yes" if res['solutions_in_O'] else "NO"),
        ("linear relation W_1 x_1 = W_2 x_2 + ... holds", "yes",
         "yes" if res['linear_relation'] else "NO"),
        ("block relations vanish at the solution", "yes",
         "yes" if res['block_vanish'] else "NO"),
        ("pair relations vanish at the solution", "yes",
         "yes" if res['pair_vanish'] else "NO"),
    ]
    for (a, b, c) in rows:
        print("  %-46s %-16s %s" % (a, b, c))
    print()


def main():
    print("=" * 88)
    print("  UOV / MAYO / QR-UOV: end-to-end verification of the attack procedure")
    print("=" * 88)
    for (q, v, o, t) in [(16, 9, 3, 3), (256, 8, 4, 3), (16, 12, 4, 4)]:
        print("\n  instance q = %d, (v,o) = (%d,%d), t = %d" % (q, v, o, t))
        print("  " + "-" * 84)
        res = None
        for seed in range(1, 80):
            r = check_procedure(v, o, q, t, seed=seed, trials=2000)
            if r.get('status') == 'ok':
                res = r
                break
        if res is None:
            print("  no non-degenerate instance found")
            continue
        print("  (seed %d)" % seed)
        show(res)
    print("=" * 88)
    print("  DONE")
    print("=" * 88)


main()
