"""Exact numerical checks for milestone Q2 (reversible Gaussian QCA).

Run with python3 (needs sympy).

Conventions (as in the checks of milestone Q1):
  one or n modes per site, cell order positions first: u : Z -> R^{2n}, finitely
  supported, represented as a dict x (int) -> vector (list of length 2n).
  Omega = [[0, I], [-I, 0]] (I the n x n identity).
  (kappa_a u)(x) = u(x - a).
  A rule is a dict m (int) -> (2n x 2n) matrix; (L u)(x) = sum_m l_m u(x - m).
  sigma(u, w) = sum_x u(x)^T Omega w(x).
  L is symplectic iff sum_m l_m^T Omega l_{m+k} = delta_{k0} Omega for every k.
Exact arithmetic only (Python ints / Fractions via sympy.Rational); no floats.
"""
import itertools
import random

import sympy as sp
from sympy import Rational as Rat

random.seed(20260928)
count = 0


def check(cond, label):
    global count
    assert cond, label
    count += 1


# ---------------- exact linear algebra on list matrices/vectors ----------------
def mmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def mvmul(A, v):
    return [sum(A[i][k] * v[k] for k in range(len(v))) for i in range(len(A))]


def mT(A):
    return [list(r) for r in zip(*A)]


def madd(A, B):
    return [[a + b for a, b in zip(r, s)] for r, s in zip(A, B)]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def zero(n, m=None):
    m = n if m is None else m
    return [[0] * m for _ in range(n)]


def vadd(a, b):
    return [x + y for x, y in zip(a, b)]


def vsub(a, b):
    return [x - y for x, y in zip(a, b)]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def bform(B, u, w):  # u^T B w
    return sum(u[i] * B[i][j] * w[j] for i in range(len(B)) for j in range(len(B)))


def omega(n):
    O = zero(2 * n)
    for i in range(n):
        O[i][n + i], O[n + i][i] = 1, -1
    return O


def clean(d, isvec=False):
    out = {}
    for k, v in d.items():
        nz = any(v) if isvec else any(any(r) for r in v)
        if nz:
            out[k] = v
    return out


def apply(L, u, dim2n):
    # (L u)(x) = sum_m l_m u(x - m); loop x = y + m over y in supp(u)
    out = {}
    for m, l in L.items():
        for y, uy in u.items():
            x = y + m
            out[x] = vadd(out.get(x, [0] * dim2n), mvmul(l, uy))
    return clean(out, True)


def translate(u, a):  # (kappa_a u)(x) = u(x - a)
    return {x + a: v for x, v in u.items()}


def sigma(u, w, Om):
    return sum(bform(Om, uy, w[x]) for x, uy in u.items() if x in w)


def supp(d):
    return set(d)


def coef(L, k, Om, n2n):  # sum_m l_m^T Omega l_{m+k}
    S = zero(n2n)
    for m, lm in L.items():
        lmk = L.get(m + k)
        if lmk is not None:
            S = madd(S, mmul(mmul(mT(lm), Om), lmk))
    return S


def is_symplectic(L, Om, n2n):
    ks = {m1 - m2 for m1 in L for m2 in L}
    for k in ks | {0}:
        C = coef(L, k, Om, n2n)
        target = Om if k == 0 else zero(n2n)
        if C != target:
            return False
    return True


def rand_rule(n2n, ms=(-1, 0, 1), lo=-3, hi=3, p=0.8):
    return clean({m: [[random.randint(lo, hi) for _ in range(n2n)] for _ in range(n2n)]
                  for m in ms if random.random() < p})


def rand_vec(n2n, xs=range(-3, 4), lo=-5, hi=5, p=0.6):
    return clean({x: [random.randint(lo, hi) for _ in range(n2n)] for x in xs if random.random() < p},
                  True)


# ================= 1. sigma vanishes on disjoint supports =================
Om1 = omega(1)
for _ in range(8):
    u = {x: [random.randint(-5, 5), random.randint(-5, 5)] for x in range(-4, 0)}
    w = {x: [random.randint(-5, 5), random.randint(-5, 5)] for x in range(1, 5)}
    check(supp(u).isdisjoint(supp(w)), "test supports disjoint")
    check(sigma(u, w, Om1) == 0, "sigma vanishes on disjointly supported vectors")
# overlapping example, nonzero
u = {0: [1, 0], 1: [3, 1]}
w = {0: [0, 1], 1: [1, 2]}
check(not supp(u).isdisjoint(supp(w)), "overlapping supports")
expected = bform(Om1, u[0], w[0]) + bform(Om1, u[1], w[1])
check(sigma(u, w, Om1) == expected, "overlap check arithmetic sanity")
check(sigma(u, w, Om1) != 0, "sigma nonzero on overlapping example")

# ================= 2. supp(Lu) subset supp(u) + N; equality can fail =================
for _ in range(10):
    L = rand_rule(2)
    u = rand_vec(2)
    N = supp(L)
    Lu = apply(L, u, 2)
    check(supp(Lu) <= {x + m for x in supp(u) for m in N}, "supp(Lu) subset supp(u) + N")
# cancellation example: equality fails (strict containment)
Lc = {(-1): [[1, 0], [0, 1]], 0: [[0, 0], [0, 0]], 1: [[-1, 0], [0, -1]]}
uc = {0: [1, 0], 2: [1, 0]}  # (Lu)(1) = l_1 u(0) + l_{-1} u(2) = -[1,0] + [1,0] = 0
Lu_c = apply(Lc, uc, 2)
Nc = supp(Lc)
full = {x + m for x in supp(uc) for m in Nc}
check(1 in full and 1 not in supp(Lu_c), "cancellation: 1 in supp(u)+N but not in supp(Lu)")
check(supp(Lu_c) < full, "strict containment example: equality fails in general")

# ================= 3. L kappa_a = kappa_a L =================
for _ in range(10):
    L = rand_rule(2)
    u = rand_vec(2)
    a = random.randint(-4, 4)
    check(apply(L, translate(u, a), 2) == translate(apply(L, u, 2), a), "L kappa_a = kappa_a L")

# ================= 4. one-cell commutation relations (Lemma 4.2(ii)) =================
def ell_of(L, v, n2n):
    # ell(v)(x) = l_x v, supported on the neighbourhood N of L
    return clean({m: mvmul(l, v) for m, l in L.items()}, True)


def check_one_cell(L, Om, n2n, xs, basis, symplectic_expected, label):
    ok = True
    for x in xs:
        for v in basis:
            for w in basis:
                lv = ell_of(L, v, n2n)
                lw = ell_of(L, w, n2n)
                lhs = sigma(lv, translate(lw, x), Om)
                rhs = bform(Om, v, w) if x == 0 else 0
                if lhs != rhs:
                    ok = False
    if symplectic_expected:
        check(ok, label)
    else:
        check(not ok, label)
    return ok


e1_1, e2_1 = [1, 0], [0, 1]
basis1 = [e1_1, e2_1]
xs_test = range(-3, 4)

# shift z.1: (Lu)(x) = u(x-1), i.e. l_1 = I
shift_rule = {1: eye(2)}
check(is_symplectic(shift_rule, Om1, 2), "shift rule is symplectic (coefficient criterion)")
check_one_cell(shift_rule, Om1, 2, xs_test, basis1, True, "one-cell relations hold for the shift")

for mm in (0, 1, 2, -1):
    Frule = {0: [[0, 1], [-1, -mm]], 1: [[0, 0], [0, 1]], -1: [[0, 0], [0, 1]]}
    Firule = {0: [[-mm, -1], [1, 0]], 1: [[1, 0], [0, 0]], -1: [[1, 0], [0, 0]]}
    check(is_symplectic(Frule, Om1, 2), f"leapfrog F symplectic by coefficient criterion (m2={mm})")
    check(is_symplectic(Firule, Om1, 2), f"leapfrog F^-1 symplectic by coefficient criterion (m2={mm})")
    check_one_cell(Frule, Om1, 2, xs_test, basis1, True, f"one-cell relations hold for F (m2={mm})")
    check_one_cell(Firule, Om1, 2, xs_test, basis1, True, f"one-cell relations hold for F^-1 (m2={mm})")

# non-symplectic control: l_0 = diag(2,1), det != 1, not in Sp(2) = SL(2)
control = {0: [[2, 0], [0, 1]]}
check(not is_symplectic(control, Om1, 2), "control rule fails the coefficient criterion")
check_one_cell(control, Om1, 2, xs_test, basis1, False,
               "one-cell relations FAIL for the non-symplectic control")

# equivalence of the one-cell relations with the coefficient criterion, on random rules
def one_cell_holds(L, Om, n2n, xs, basis):
    for x in xs:
        for v in basis:
            for w in basis:
                lv, lw = ell_of(L, v, n2n), ell_of(L, w, n2n)
                lhs = sigma(lv, translate(lw, x), Om)
                rhs = bform(Om, v, w) if x == 0 else 0
                if lhs != rhs:
                    return False
    return True


for _ in range(15):
    L = rand_rule(2, ms=(-1, 0, 1), lo=-2, hi=2, p=0.9)
    a, b = is_symplectic(L, Om1, 2), one_cell_holds(L, Om1, 2, range(-3, 4), basis1)
    check(a == b, "one-cell relations equivalent to the coefficient criterion (random rule)")

# ================= 5. LinearAQFT leapfrog on Cauchy data =================
def gamma(a, b, m2, xs):  # Gamma(a,b)(x) = (b(x), -a(x)+b(x+1)+b(x-1)-m2 b(x))
    ga = lambda x: b.get(x, 0)
    gb = lambda x: -a.get(x, 0) + b.get(x + 1, 0) + b.get(x - 1, 0) - m2 * b.get(x, 0)
    return {x: [ga(x), gb(x)] for x in xs}


def wronskian(u, w, xs):
    return sum(u.get(x, [0, 0])[0] * w.get(x, [0, 0])[1] - u.get(x, [0, 0])[1] * w.get(x, [0, 0])[0]
               for x in xs)


for mm in (0, 1, 2, -1):
    Frule = {0: [[0, 1], [-1, -mm]], 1: [[0, 0], [0, 1]], -1: [[0, 0], [0, 1]]}
    Firule = {0: [[-mm, -1], [1, 0]], 1: [[1, 0], [0, 0]], -1: [[1, 0], [0, 0]]}
    for _ in range(5):
        rng = range(-5, 6)
        a = {x: random.randint(-4, 4) for x in rng}
        b = {x: random.randint(-4, 4) for x in rng}
        u = {x: [a[x], b[x]] for x in rng}
        # compare on the interior only, where both sides use only in-range data
        interior = range(-3, 4)
        g = gamma(a, b, mm, interior)
        Lu = apply(Frule, u, 2)
        check(all(g[x] == Lu.get(x, [0, 0]) for x in interior),
              f"Gamma matches the rule of F on Cauchy data (m2={mm})")
        # F^-1 F = id and F F^-1 = id, on interior positions (avoid boundary truncation)
        u2 = rand_vec(2, xs=range(-6, 7), lo=-4, hi=4, p=1.0)
        Fu = apply(Frule, u2, 2)
        FiFu = apply(Firule, Fu, 2)
        check(all(FiFu.get(x, [0, 0]) == u2.get(x, [0, 0]) for x in range(-3, 4)),
              f"F^-1 F = id on interior (m2={mm})")
        Fiu = apply(Firule, u2, 2)
        FFiu = apply(Frule, Fiu, 2)
        check(all(FFiu.get(x, [0, 0]) == u2.get(x, [0, 0]) for x in range(-3, 4)),
              f"F F^-1 = id on interior (m2={mm})")
        # Wronskian = sigma, and preserved by F
        u3 = rand_vec(2, xs=rng, lo=-4, hi=4, p=1.0)
        w3 = rand_vec(2, xs=rng, lo=-4, hi=4, p=1.0)
        check(wronskian(u3, w3, rng) == sigma(u3, w3, Om1), "Wronskian equals sigma")
        Fu3, Fw3 = apply(Frule, u3, 2), apply(Frule, w3, 2)
        full_dom = set(Fu3) | set(Fw3) | set(u3) | set(w3)
        check(wronskian(Fu3, Fw3, full_dom) == wronskian(u3, w3, full_dom),
              f"Wronskian preserved by F (m2={mm})")

# ================= 6. time direction on the lattice KG equation =================
# Forward Heisenberg convention (fixed by the proposal, PLAN.md item 6): stepping the
# Cauchy data forward in time, Lambda_{t+1} h = F Lambda_t h, corresponds to running the
# equation of motion forward; the *automorphism* implementing translation by +1 in t on
# solutions is alpha_{F^{-1}} (PLAN.md: "the forward Heisenberg step ... is alpha_{F^{-1}}").
# This script checks the identities only; it does not re-derive the convention.
for mm in (0, 1, 2, -1):
    Frule = {0: [[0, 1], [-1, -mm]], 1: [[0, 0], [0, 1]], -1: [[0, 0], [0, 1]]}
    Firule = {0: [[-mm, -1], [1, 0]], 1: [[1, 0], [0, 0]], -1: [[1, 0], [0, 0]]}
    xs_full = list(range(-30, 31))
    ts_full = list(range(-9, 10))
    h = {}
    # random finitely supported initial slices at t = 0, 1
    for t in (0, 1):
        for x in range(-3, 4):
            h[(t, x)] = random.randint(-4, 4)
        for x in xs_full:
            h.setdefault((t, x), 0)

    def hv(t, x):
        return h.get((t, x), 0)

    # forward recursion: h(t+1,x) = h(t,x+1)+h(t,x-1) - m2 h(t,x) - h(t-1,x)
    for t in range(1, 9):
        for x in xs_full:
            h[(t + 1, x)] = hv(t, x + 1) + hv(t, x - 1) - mm * hv(t, x) - hv(t - 1, x)
    # backward recursion: h(t-1,x) = h(t,x+1)+h(t,x-1) - m2 h(t,x) - h(t+1,x)
    for t in range(0, -9, -1):
        for x in xs_full:
            h[(t - 1, x)] = hv(t, x + 1) + hv(t, x - 1) - mm * hv(t, x) - hv(t + 1, x)

    # sanity: h solves the lattice KG equation everywhere in the interior
    for t in range(-6, 7):
        for x in range(-15, 16):
            check(hv(t + 1, x) + hv(t - 1, x) - hv(t, x + 1) - hv(t, x - 1) + mm * hv(t, x) == 0,
                  f"h solves the lattice KG equation (m2={mm})")

    def cauchy(t, xs):
        return {x: [hv(t, x), hv(t + 1, x)] for x in xs}

    interior = range(-6, 7)
    for t in range(-6, 6):
        # Lambda_{t+1} h = F Lambda_t h
        lam_t = cauchy(t, xs_full)
        lam_t1 = cauchy(t + 1, interior)
        F_lam_t = apply(Frule, lam_t, 2)
        check(all(F_lam_t.get(x, [0, 0]) == lam_t1[x] for x in interior),
              f"Lambda_(t+1) h = F Lambda_t h (m2={mm}, t={t})")
        # time-translated solution (L_(1,0) h)(t,x) = h(t-1,x)
        Lh_t = {x: [hv(t - 1, x), hv(t, x)] for x in xs_full}  # Lambda_t(L h)
        lam_tm1 = cauchy(t - 1, interior)  # Lambda_(t-1) h
        check(all(Lh_t[x] == lam_tm1[x] for x in interior),
              f"Lambda_t(L_(1,0) h) = Lambda_(t-1) h (m2={mm}, t={t})")
        Fi_lam_t = apply(Firule, lam_t, 2)
        check(all(Fi_lam_t.get(x, [0, 0]) == lam_tm1[x] for x in interior),
              f"Lambda_(t-1) h = F^-1 Lambda_t h (m2={mm}, t={t})")

# ================= 7. finding 5: the divisibility argument =================
# If k : Q^2 x Q^2 -> Z is biadditive, represented as k(u,w) = u^T K w with integer K,
# biadditivity gives k(u,w) = n * k(u/n, w) for every nonzero integer n. If k is to take
# integer values on ALL of Q^2 x Q^2, this forces n | k(u,w) for every n, i.e. k(u,w) = 0
# for all u,w, i.e. K = 0. We check the algebraic identity and exhibit, for K != 0, values
# of n for which k(u/n, w) is not an integer (so such k is not Z-valued on Q^2 x Q^2 unless K=0).
u_sym, w_sym = sp.symbols("u1 u2"), sp.symbols("w1 w2")


def k_of(K, u, w):
    return bform(K, list(u), list(w))


for _ in range(6):
    K = [[random.randint(-4, 4), random.randint(-4, 4)],
         [random.randint(-4, 4), random.randint(-4, 4)]]
    u = [Rat(random.randint(-9, 9), random.randint(1, 5)) for _ in range(2)]
    w = [Rat(random.randint(-9, 9), random.randint(1, 5)) for _ in range(2)]
    n = random.randint(2, 9)
    lhs = k_of(K, u, w)
    rhs = n * k_of(K, [x / n for x in u], w)
    check(sp.simplify(lhs - rhs) == 0, "biadditivity: k(u,w) = n k(u/n, w)")

basis_e = [[1, 0], [0, 1]]
for K in ([[1, 0], [0, 0]], [[0, 1], [-1, 0]], [[2, 1], [0, 3]]):
    check(any(any(row) for row in K), "K != 0 test case")
    i, j = next((i, j) for i in range(2) for j in range(2) if K[i][j] != 0)
    ei, ej = basis_e[i], basis_e[j]
    nonint_found = False
    for n in range(2, 50):
        val = Rat(k_of(K, [x / n for x in ei], ej))
        if val.q != 1:
            nonint_found = True
            break
    check(nonint_found, f"K != 0 gives a non-integer k(e_i/n, e_j) for some n (K={K})")

print(f"check_q2: {count} checks passed")
