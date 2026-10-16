# =====================================================================
#  qr-uov.sage -- extended intersection attack on QR-UOV
#
#  sage qr-uov.sage      (or, in Sage:  load("qr-uov.sage"))
#  prints one table (lifted over F_{q^l})
#
#  substitution:  (v, o, q, m) <- (v/l, m/l, q^l, m)          [lifted]
#                 symmetric forms;  o = m/l, so M(t) = t(t+1)/2*m - t
#
#  Delta_1 = C(t*) - Inter    improved minus the previous intersection attack
#  Delta_2 = C(t*) - keyrec   improved minus the best key-recovery attack
# =====================================================================

from sage.all import *
import time

SETS = [
    # SL,   q,   v,   m,  l,  Inter. (Table 11), best key recovery (Table 11)
    # the best key-recovery figure is the smallest of KS, Recon. and RM, which
    # is RM for l = 3 and Recon. for l = 10
    ("I",   127,  156,  54,  3,   460,  158),
    ("I",   127,  540,  60, 10,  3090,  151),
    ("III", 127,  228,  78,  3,   653,  219),
    ("III", 127,  820,  90, 10,  4651,  211),
    ("V",   127,  306, 105,  3,   851,  277),
    ("V",   127, 1040, 110, 10,  5930,  276),
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


def mq_fxl(N, M, log2q):
    """(bits, k', D) of the Wiedemann--FXL estimate, minimised over k'.

    The field size is passed as log2 q, so that q^l for l = 10 never has to be
    materialised.
    """
    N, M = I(N), I(M)
    lq = float(log2q)
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
    variables.  Here o = m/l, so 3*m - 2 is l times the 3*o - 2 it
    replaces.

    The middle N(t) = (t-1)*n covers t = 2 as well.  The last row t = k is
    evaluated first so that its own M(k) = k(k+1)/2*m - k and guess 0 win
    when k itself is 2; for k >= 3 the two orders agree everywhere.
    """
    k, t, n, o, v, m = I(k), I(t), I(n), I(o), I(v), I(m)
    if t == k:
        return (k - 1) * n - (k * o - v - 1), k * (k + 1) // 2 * m - k, 0
    return (t - 1) * n, t * (t + 1) // 2 * m - t, max(0, v - t * o + 1)


def curve(n, o, log2q, m):
    v = n - o
    k = bound_k(v, o)
    rows = []
    for t in range(2, k + 1):
        N, M, g = sizes(k, t, n, o, v, m)
        if N <= 0 or M <= 0:
            continue
        f, kp, D = mq_fxl(N, M, log2q)
        rows.append({"t": I(t), "N": I(N), "M": I(M), "guess": I(g),
                     "fxl": None if f is None else F(f), "kp": kp, "D": D,
                     "total": None if f is None else F(I(g) * float(log2q) + f)})
    return k, rows


COLS = [(4, "SL", "s"), (14, "(q,v,m,l)", "s"), (4, "k", "d"), (3, "t*", "d"),
        (7, "N", "d"), (8, "M", "d"), (6, "M/N", ".1f"), (6, "guess", "d"),
        (5, "D", "s"), (5, "k'", "s"), (11, "C_FXL", "s"),
        (11, "extended", "s"), (8, "Inter", "d"), (7, "keyrec", "d"),
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


def table(title, note, mode):
    width = sum(w for w, _, _ in COLS)
    print("=" * width)
    print(title)
    print(note)
    print("=" * width)
    print(emit([c[1] for c in COLS], header=True))
    print("-" * width)
    out = []
    for (sl, q, v0, m0, l, inter, keyrec) in SETS:
        lab = "(%d,%d,%d,%d)" % (q, v0, m0, l)
        v, o, m = v0 // l, m0 // l, m0
        log2q = float(l) * float(log(q, 2))
        n = v + o
        k, rows = curve(n, o, log2q, m)
        good = [r for r in rows if r["total"] is not None]
        if not good:
            print(emit([sl, lab, k, "n/a", "n/a", "n/a", "n/a", "n/a", "n/a",
                        "n/a", "n/a", "n/a", inter, keyrec, "n/a", "n/a"]))
            out.append({"SL": sl, "repr": mode, "q": I(q), "v": I(v0),
                        "m": I(m0), "l": I(l), "k": I(k), "rows": rows,
                        "t_star": None, "extended": None, "Inter": I(inter),
                        "keyrec": I(keyrec)})
            continue
        r = min(good, key=lambda x: x["total"])
        print(emit([sl, lab, k, r["t"], r["N"], r["M"],
                    float(r["M"]) / float(r["N"]) if r["M"] else 0.0,
                    r["guess"], "n/a" if r["D"] is None else r["D"],
                    "n/a" if r["kp"] is None else r["kp"],
                    "n/a" if r["fxl"] is None else "%.2f" % r["fxl"],
                    "%.2f" % r["total"], inter, keyrec,
                    r["total"] - float(inter), r["total"] - float(keyrec)]))
        out.append({"SL": sl, "repr": mode, "q": I(q), "v": I(v0), "m": I(m0),
                    "l": I(l), "V": I(v0 // l), "M": I(m0 // l), "k": I(k),
                    "t_star": r["t"], "rows": rows, "extended": r,
                    "Inter": I(inter), "keyrec": I(keyrec),
                    "Delta1": F(r["total"] - inter),
                    "Delta2": F(r["total"] - keyrec)})
    print()
    return out


def main():
    t0 = time.time()
    table("QR-UOV, lifted over F_{q^l}",
          "substitution  (v,o,q,m) <- (v/l, m/l, q^l, m);  o = m/l",
          "lift")
    print("total %.1fs" % (time.time() - t0))


main()
