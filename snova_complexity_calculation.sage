# =====================================================================
#  snova.sage -- extended intersection attack on SNOVA
#
#  sage snova.sage       (or, in Sage:  load("snova.sage"))
#  prints two tables (base field, lifted)
#
#  substitutions:  (v, o, q, m) <- (l*v, l*o, q, l^2*m1)   [base field]
#                  (v, o, q, m) <- (v, o, q^l, m1)         [lifted]
#
#  SNOVA forms live in a non-commutative matrix ring and are not symmetric, so
#  the pairs are ordered and the equation count is
#      M(t) = t^2*m - t*l    in the base-field representation, m = l^2*m1,
#      M(t) = t^2*m - t      in the lifted one,            m = m1,
#  (for MAYO and QR-UOV it is the symmetric count t(t+1)/2*m - t).  Here m
#  is the number of coefficient matrices per pair: l^2*m1 in the base-field
#  representation, m1 in the lifted one.
#
#  Delta_1 = C(t*) - CompInt   improved minus the previous intersection attack
#  Delta_2 = C(t*) - CompRec   improved minus the best key-recovery attack
# =====================================================================

from sage.all import *
import time

SETS = [
    # name, v, o, q, l, r, m1, m2, CompInt, CompRec
    ("SNOVA_I_K",    29, 3, 16, 4, 8, 5,  96,  507, 332),
    ("SNOVA_I_B",    27, 4, 16, 4, 6, 5,  96,  436, 300),
    ("SNOVA_I_S",    27, 5, 16, 4, 4, 5,  80,  411, 300),
    ("SNOVA_III_K",  38, 4, 16, 4, 8, 7, 128,  643, 414),
    ("SNOVA_III_B",  38, 5, 16, 4, 6, 7, 120,  615, 414),
    ("SNOVA_III_S",  38, 6, 16, 4, 5, 7, 120,  589, 414),
    ("SNOVA_V_K",    40, 4, 16, 5, 8, 6, 160,  836, 528),
    ("SNOVA_V_B",    40, 5, 16, 5, 6, 6, 150,  802, 528),
    ("SNOVA_V_S",    40, 6, 16, 5, 5, 6, 150,  769, 528),
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

    The field size is passed as log2 q, so that q^l never has to be materialised.
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


def sizes_asym(k, t, n, o, v, m, lsubst):
    """(N, M, guess exponent) for the ordered-pair count  t^2*m - t*lsubst.

    The pairs (i,j), 1 <= i, j <= t, are ordered, because the forms live in a
    non-commutative ring; each pair carries m coefficient matrices, and one
    relation per block group is removed for every ring generator.

    lsubst says how many generators are in play.  That is the only difference
    between the two representations, and each matches ref_calc:

        A, base field F_q:  lsubst = l, m = l^2*m1
            M(2) = 4*l^2*m1 - 2*l      ref_calc: C_FXL(l(v+o), 4*l^2*m1-2*l, q)
        B, lifted F_{q^l}:  lsubst = 1, m = m1
            M(2) = 4*m1 - 2            ref_calc: C_FXL(v+o, 4*m1-2, q^l)

    so A(t) = l*B(t) for every t.  Passing lsubst = l with m = m1, or
    lsubst = 1 with m = l^2*m1, is neither representation.
    """
    k, t, n, o, v, m, lsubst = I(k), I(t), I(n), I(o), I(v), I(m), I(lsubst)
    guess = 0 if t == k else max(0, v - t * o + 1)
    if t == 2:
        N = n
    elif t == k:
        N = (k - 1) * n - (k * o - v - 1)
    else:
        N = (t - 1) * n
    return N, t * t * m - t * lsubst, guess


def curve(n, o, log2q, m, lsubst):
    v = n - o
    k = bound_k(v, o)
    rows = []
    for t in range(2, k + 1):
        N, M, g = sizes_asym(k, t, n, o, v, m, lsubst)
        if N <= 0 or M <= 0:
            continue
        f, kp, D = mq_fxl(N, M, log2q)
        rows.append({"t": I(t), "N": I(N), "M": I(M), "guess": I(g),
                     "fxl": None if f is None else F(f), "kp": kp, "D": D,
                     "total": None if f is None else F(I(g) * float(log2q) + f)})
    return k, rows


COLS = [(13, "set", "s"), (20, "(v,o,q,l,r,m1,m2)", "s"), (4, "k", "d"),
        (3, "t*", "d"), (7, "N", "d"), (8, "M", "d"), (6, "M/N", ".1f"),
        (6, "guess", "d"), (5, "D", "s"), (5, "k'", "s"), (11, "C_FXL", "s"),
        (11, "extended", "s"), (8, "CompInt", "d"), (8, "CompRec", "d"),
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
    for (name, v0, o0, q, l, r, m1, m2, compint, comprec) in SETS:
        lab = "(%d,%d,%d,%d,%d,%d,%d)" % (v0, o0, q, l, r, m1, m2)
        if mode == "base":
            n, o, m, lsubst = l * (v0 + o0), l * o0, l * l * m1, l
            log2q = float(log(q, 2))
        else:
            n, o, m, lsubst = v0 + o0, o0, m1, 1
            log2q = float(l) * float(log(q, 2))
        k, rows = curve(n, o, log2q, m, lsubst)
        good = [x for x in rows if x["total"] is not None]
        if not good:
            print(emit([name, lab, k, "n/a", "n/a", "n/a", "n/a", "n/a", "n/a",
                        "n/a", "n/a", "n/a", compint, comprec, "n/a", "n/a"]))
            out.append({"set": name, "repr": mode, "params": lab, "k": I(k),
                        "rows": rows, "extended": None,
                        "CompInt": I(compint), "CompRec": I(comprec)})
            continue
        best = min(good, key=lambda x: x["total"])
        print(emit([name, lab, k, best["t"], best["N"], best["M"],
                    float(best["M"]) / float(best["N"]), best["guess"],
                    "n/a" if best["D"] is None else best["D"],
                    "n/a" if best["kp"] is None else best["kp"],
                    "n/a" if best["fxl"] is None else "%.2f" % best["fxl"],
                    "%.2f" % best["total"], compint, comprec,
                    best["total"] - float(compint),
                    best["total"] - float(comprec)]))
        out.append({"set": name, "repr": mode, "params": lab, "k": I(k),
                    "t_star": best["t"], "rows": rows, "extended": best,
                    "CompInt": I(compint), "CompRec": I(comprec),
                    "Delta1": F(best["total"] - compint),
                    "Delta2": F(best["total"] - comprec)})
    print()
    return out


def main():
    t0 = time.time()
    table("SNOVA, representation (A): base field F_q",
                 "substitution  (v,o,q,m) <- (l*v, l*o, q, l^2*m1);  "
                 "M(t) = t^2*m - t*l",
                 "base")
    table("SNOVA, representation (B): lifted over F_{q^l}",
                 "substitution  (v,o,q,m) <- (v, o, q^l, m1);  "
                 "M(t) = t^2*m - t",
                 "lift")
    print("total %.1fs" % (time.time() - t0))


main()
