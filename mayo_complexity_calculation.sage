# =====================================================================
#  mayo.sage -- extended intersection attack on MAYO
#
#  sage mayo.sage        (or, in Sage:  load("mayo.sage"))
#  prints one table
#
#  substitution:  (v, o, q, m) <- (n - o, o, q, m)   [symmetric forms]
#
#  Delta_1 = C(t*) - C(2)          improved minus the previous attack
#  Delta_2 = C(t*) - key recovery  improved minus the best attack known
# =====================================================================

from sage.all import *
import time

# best key-recovery figures of Table 5.1 (reconciliation)
KEYREC = {"MAYO_1": 202, "MAYO_2": 203, "MAYO_3": 262, "MAYO_5": 334}

SETS = [
    ("MAYO_1",  88,  80,  8, 10, 16),
    ("MAYO_2",  86,  64, 13,  5, 16),
    ("MAYO_3", 118, 108, 10, 11, 16),
    ("MAYO_5", 154, 142, 12, 12, 16),
]


def F(x):
    return None if x is None else float(x)


def I(x):
    return int(F(x))


_comb = {}


def C(n, k):
    n, k = I(n), I(k)
    if k < 0 or k > n:
        return 0
    k = min(k, n - k)               # same value, far smaller arguments
    if (n, k) not in _comb:
        _comb[(n, k)] = int(binomial(n, k))
    return _comb[(n, k)]


_coeff = {}


def hilbert_coeff(M, n_plus, d):
    """[z^d] (1-z^2)^M (1-z)^{-(n_plus+1)}, exact."""
    M, n_plus, d = I(M), I(n_plus), I(d)
    if (M, n_plus, d) in _coeff:
        return _coeff[(M, n_plus, d)]
    tot = 0
    for i in range(0, min(M, d // 2) + 1):
        b1 = C(M, i)
        if b1:
            k2 = d - 2 * i + n_plus
            b2 = C(k2, n_plus) if n_plus <= k2 else 0
            tot += (-1) ** i * b1 * b2
    _coeff[(M, n_plus, d)] = tot
    return tot


_deg = {}


def degree_of_regularity(N, M, kp, cap=4000):
    """Smallest d with the coefficient <= 0, or None if the series never turns.

    The test M <= A-1 is exact: every term of the alternating sum is then
    positive, so the series never crosses and the FXL estimate does not exist.
    It costs nothing and saves scanning thousands of coefficients in exactly the
    cases (QR-UOV, the lifted SNOVA representation) where the model fails.
    """
    N, M, kp = I(N), I(M), I(kp)
    if (N, M, kp) in _deg:
        return _deg[(N, M, kp)]
    if M <= N - kp:
        _deg[(N, M, kp)] = None
        return None
    out = None
    for d in range(0, min(N - kp + 2, cap)):
        if hilbert_coeff(M, N - kp, d) <= 0:
            out = d
            break
    _deg[(N, M, kp)] = out
    return out


def mq_fxl(N, M, q):
    """(bits, k', D) of the Wiedemann--FXL estimate, minimised over k'."""
    N, M = I(N), I(M)
    lq = float(log(q, 2))
    best = best_kp = best_D = None
    for kp in range(0, N):
        if best is not None and I(kp) * lq >= best:
            break                   # q^{k'} alone already exceeds the best cost
        D = degree_of_regularity(N, M, kp)
        if D is None:
            continue
        try:
            lg = (I(kp) * lq + float(log(3, 2))
                  + float(log(C(N - kp + 2, 2), 2))
                  + 2 * float(log(C(N - kp + D, D), 2))
                  + float(log(2 * lq ** 2 + lq, 2)))
        except OverflowError:
            continue          # beyond float range: this k' cannot win
        if best is None or lg < best:
            best, best_kp, best_D = float(lg), I(kp), I(D)
    return best, best_kp, best_D


def bound_k(v, o):
    v, o = I(v), I(o)
    return v // o + 1 if v % o == 0 else int(ceil(QQ(v) / QQ(o)))


def sizes(k, t, n, o, v, m):
    """(N, M, guess exponent) for a symmetric instance.

    M(t) is one formula for every t: the coefficient matrices are indexed by the
    ordered pairs (i,j), 1 <= i <= j <= t, so there are t(t+1)/2 pairs and each
    carries m matrices, less t because the diagonal blocks are symmetric
    under swapping the two halves.  At t = 2 that is 3*m - 2, not 3*o - 2:
    the count involves the number of public forms, never the number of oil
    variables.

    The middle N(t) = (t-1)*n covers t = 2 as well.  The last row t = k is
    evaluated first so that its own M(k) = k(k+1)/2*m - k and guess 0 win
    when k itself is 2; for k >= 3 the two orders agree everywhere.
    """
    k, t, n, o, v, m = I(k), I(t), I(n), I(o), I(v), I(m)
    if t == k:
        return (k - 1) * n - (k * o - v - 1), k * (k + 1) // 2 * m - k, 0
    return (t - 1) * n, t * (t + 1) // 2 * m - t, max(0, v - t * o + 1)


def curve(n, o, q, m):
    v = n - o
    k = bound_k(v, o)
    lq = float(log(q, 2))
    rows = []
    for t in range(2, k + 1):
        N, M, g = sizes(k, t, n, o, v, m)
        if N <= 0 or M <= 0:
            continue
        f, kp, D = mq_fxl(N, M, q)
        rows.append({"t": I(t), "N": I(N), "M": I(M), "guess": I(g),
                     "fxl": None if f is None else F(f), "kp": kp, "D": D,
                     "total": None if f is None else F(I(g) * lq + f)})
    return k, rows


COLS = [(9, "set", "s"), (16, "(n,m,o,k,q)", "s"), (4, "v", "d"),
        (5, "m", "d"), (3, "k", "d"), (3, "t*", "d"), (7, "N", "d"),
        (8, "M", "d"), (6, "M/N", ".1f"), (6, "guess", "d"), (5, "D", "s"),
        (5, "k'", "s"), (11, "C_FXL", "s"), (11, "total", "s"),
        (10, "Delta1", ".2f"), (10, "Delta2", ".2f")]


def emit(vals, header=False):
    cells = []
    for (w, name, kind), val in zip(COLS, vals):
        txt = None
        if not header:
            if kind == "d":
                try:
                    txt = "%d" % (I(val),)
                except Exception:
                    txt = None
            elif kind in (".1f", ".2f"):
                try:
                    txt = ("%" + kind) % (F(val),)
                except Exception:
                    txt = None
        if txt is None:
            txt = "%s" % (val,)
        cells.append(txt.rjust(w))
    return "".join(cells)


def main():
    t0 = time.time()
    width = sum(w for w, _, _ in COLS)
    print("=" * width)
    print("MAYO -- extended intersection attack (Wiedemann--FXL, bits)")
    print("substitution:  (v, o, q, m) <- (n - o, o, q, m)")
    print("=" * width)
    print(emit([c[1] for c in COLS], header=True))
    print("-" * width)

    for (name, n, m, o, k_w, q) in SETS:
        k_blocks, rows = curve(n, o, q, m)
        good = [r for r in rows if r["total"] is not None]
        if not good:
            print("%-9s %-18s   FXL undefined for every feasible t"
                  % (name, "(%d,%d,%d,%d,%d)" % (n, m, o, k_w, q)))
            continue
        best = min(good, key=lambda r: r["total"])
        ref, kr = rows[0], KEYREC.get(name)
        for r in (rows if len(rows) <= 3 else [ref, best]):
            d1 = None if (r["total"] is None or ref["total"] is None) \
                else r["total"] - ref["total"]
            d2 = None if (r["total"] is None or kr is None) \
                else r["total"] - float(kr)
            print(emit([name, "(%d,%d,%d,%d,%d)" % (n, m, o, k_w, q), n - o, m, k_blocks,
                        r["t"], r["N"], r["M"],
                        float(r["M"]) / float(r["N"]) if r["M"] else 0.0,
                        r["guess"], "n/a" if r["D"] is None else r["D"],
                        "n/a" if r["kp"] is None else r["kp"],
                        "n/a" if r["fxl"] is None else "%.2f" % r["fxl"],
                        "n/a" if r["total"] is None else "%.2f" % r["total"],
                        "n/a" if d1 is None else "%.2f" % d1,
                        "n/a" if d2 is None else "%.2f" % d2])
                  + (" *" if r is best else ""))
        print()
    print("total %.1fs" % (time.time() - t0))


main()
