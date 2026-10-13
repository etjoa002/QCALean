"""Exact numerical checks for milestone Q1 (symbols and form-preserving cellular
automata), items 1-5.

Run with python3 (needs sympy).

Conventions:
  u : iota -> R[G], finitely supported x -> u(x) in R^iota (dict x -> list)
  (kappa_a u)(x) = u(x - a);  z^a acts as kappa_a
  (L u)(x) = sum_m l_m u(x - m),  Lhat(z) = sum_m l_m z^m  (rule = dict m -> matrix)
  star: z -> z^{-1};  Btilde(u, w) = sum_x u(x)^T B w(x)
Exact arithmetic only; P = None means over Z, otherwise entries reduced mod P.
"""
import itertools
import random

import sympy as sp

random.seed(20260927)
count = 0


def check(cond, label):
    global count
    assert cond, label
    count += 1


# ---------- small exact linear algebra on list matrices, optionally mod P ----------
def red(a, P):
    return a % P if P else a


def mmul(A, B, P=None):
    return [[red(sum(A[i][k] * B[k][j] for k in range(len(B))), P) for j in range(len(B[0]))]
            for i in range(len(A))]


def madd(A, B, P=None):
    return [[red(a + b, P) for a, b in zip(r, s)] for r, s in zip(A, B)]


def mT(A):
    return [list(r) for r in zip(*A)]


def mred(A, P):
    return [[red(a, P) for a in r] for r in A]


def zero(n):
    return [[0] * n for _ in range(n)]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def vadd(a, b, P):
    return [red(x + y, P) for x, y in zip(a, b)]


def tadd(a, b, s=1):
    return tuple(x + s * y for x, y in zip(a, b))


# ---------- rules and vectors ----------
def clean(d, P, isvec=False):
    out = {}
    for k, v in d.items():
        v = [red(a, P) for a in v] if isvec else mred(v, P)
        if (any(v) if isvec else any(any(r) for r in v)):
            out[k] = v
    return out


def apply(L, u, P=None):
    n = len(next(iter(L.values()))) if L else 0
    out = {}
    for m, l in L.items():
        for x, ux in u.items():
            y = tadd(x, m)
            out[y] = vadd(out.get(y, [0] * len(ux)), [r[0] for r in mmul(l, [[a] for a in ux], P)], P)
    return clean(out, P, True)


def compose(L2, L1, P=None):  # symbol product L2hat * L1hat (convolution)
    out = {}
    for m2, a in L2.items():
        for m1, b in L1.items():
            m = tadd(m1, m2)
            out[m] = madd(out.get(m, zero(len(a))), mmul(a, b, P), P)
    return clean(out, P)


def star_T(L):  # symbol Lhat(z^{-1})^T
    return {tuple(-c for c in m): mT(l) for m, l in L.items()}


def const(M, dim):
    return {(0,) * dim: M}


def translate(u, a):
    return {tadd(x, a): v for x, v in u.items()}


def form(B, u, w, P=None):
    s = sum(sum(ux[i] * B[i][j] * w[x][j] for i in range(len(B)) for j in range(len(B)))
            for x, ux in u.items() if x in w)
    return red(s, P)


def rand_rule(n, dim, box=1, lo=-3, hi=3, P=None):
    rng = range(-box, box + 1)
    return clean({m: [[random.randint(lo, hi) for _ in range(n)] for _ in range(n)]
                  for m in itertools.product(rng, repeat=dim) if random.random() < 0.7}, P)


def rand_vec(n, dim, box=3, P=None):
    rng = range(-box, box + 1)
    return clean({x: [random.randint(-5, 5) for _ in range(n)]
                  for x in itertools.product(rng, repeat=dim) if random.random() < 0.5}, P, True)


def supp(d):
    return set(d)


# ---------- 1, 2. symbols, convolution, translation invariance, finite range ----------
z1, z2 = sp.symbols("z1 z2")


def sym_poly(L, dim, shift):  # z^shift * Lhat as polynomial matrix
    zs = (z1, z2)[:dim]
    n = len(next(iter(L.values())))
    M = sp.zeros(n)
    for m, l in L.items():
        M += sp.Matrix(l) * sp.Mul(*[zs[i] ** (m[i] + shift) for i in range(dim)])
    return M.expand()


def poly_to_rule(M, dim, shift):
    zs = (z1, z2)[:dim]
    out = {}
    for i in range(M.rows):
        for j in range(M.cols):
            for mon, c in sp.Poly(M[i, j], *zs).terms():
                m = tuple(e - shift for e in mon)
                out.setdefault(m, zero(M.rows))[i][j] = int(c)
    return clean(out, None)


for dim in (1, 2):
    for n in (2, 3):
        for _ in range(3):
            L1, L2 = rand_rule(n, dim), rand_rule(n, dim)
            prod = (sym_poly(L2, dim, 1) * sym_poly(L1, dim, 1)).expand()
            L21 = poly_to_rule(prod, dim, 2)
            check(L21 == compose(L2, L1), f"symbol product = convolution, dim {dim}, n {n}")
            u = rand_vec(n, dim)
            check(apply(L21, u) == apply(L2, apply(L1, u)), f"rule of L2hat L1hat = L2 o L1 ({dim},{n})")
            a = tuple(random.randint(-3, 3) for _ in range(dim))
            check(apply(L1, translate(u, a)) == translate(apply(L1, u), a), "L kappa_a = kappa_a L")
            zs = (z1, z2)[:dim]
            za = {tadd((0,) * dim, a): eye(n)}  # z^a as a rule is kappa_a
            check(apply(za, u) == translate(u, a), "z^a acts as kappa_a")
            N = supp(L1)
            check(supp(apply(L1, u)) <= {tadd(x, m) for x in supp(u) for m in N},
                  "finite range: supp Lu in supp u + N")
    # identity goes to 1
    u = rand_vec(2, dim)
    check(apply(const(eye(2), dim), u) == u, "identity rule acts as identity")

# ---------- 3, 4. twisted criterion and explicit inverse, over Z and ZMod 5 ----------
def omega(k):
    O = zero(2 * k)
    for i in range(k):
        O[i][k + i], O[k + i][i] = 1, -1
    return O


def preserves_symbol(L, B, P):
    lhs = compose(compose(star_T(L), const(B, 1), P), L, P)
    return lhs == clean(const(B, 1), P)


def preserves_form(L, B, P, trials=4):
    for _ in range(trials):
        u, w = rand_vec(len(B), 1, P=P), rand_vec(len(B), 1, P=P)
        if form(B, apply(L, u, P), apply(L, w, P), P) != form(B, u, w, P):
            return False
    return True


def even_laurent(box=2):
    c = {k: random.randint(-3, 3) for k in range(0, box + 1)}
    return {(k,): c[abs(k)] for k in range(-box, box + 1)}


def block_elem(k, p, lower):  # [[1,0],[p,1]] or [[1,p],[0,1]] in blocks of size k
    L = {(0,): eye(2 * k)}
    for m, c in p.items():
        M = L.get(m, zero(2 * k))
        M = [r[:] for r in M]
        for i in range(k):
            if lower:
                M[k + i][i] += c
            else:
                M[i][k + i] += c
        L[m] = M
    return clean(L, None)


def shift(k, n):
    return {(k,): eye(n)}


def perm_sign(n):
    p = list(range(n))
    random.shuffle(p)
    return [[random.choice((1, -1)) if p[i] == j else 0 for j in range(n)] for i in range(n)]


def const_symp(k):  # product of constant elementary symplectic matrices
    A = eye(2 * k)
    for _ in range(3):
        c = random.randint(-2, 2)
        E = eye(2 * k)
        i = random.randrange(k)
        if random.random() < 0.5:
            E[k + i][i] = c
        else:
            E[i][k + i] = c
        A = mmul(A, E)
    return A


for P in (None, 5):
    cases = []
    for k in (1, 2):
        B = mred(omega(k), P)
        Binv = mred([[-a for a in r] for r in omega(k)], P)
        for _ in range(4):
            L = const(const_symp(k), 1)
            for _ in range(2):
                L = compose(L, block_elem(k, even_laurent(), True), P)
                L = compose(block_elem(k, even_laurent(1), False), L, P)
            L = compose(shift(random.randint(-2, 2), 2 * k), L, P)
            cases.append((clean(L, P), B, Binv))
    for n in (2, 3):
        for _ in range(3):
            L = const(perm_sign(n), 1)
            L = compose(shift(random.randint(-2, 2), n), L, P)
            cases.append((clean(L, P), mred(eye(n), P), mred(eye(n), P)))
    for L, B, Binv in cases:
        n = len(B)
        check(preserves_symbol(L, B, P), f"preserving rule: symbol condition (P={P})")
        check(preserves_form(L, B, P), f"preserving rule: form condition (P={P})")
        Linv = compose(compose(const(Binv, 1), star_T(L), P), const(B, 1), P)
        I = clean(const(eye(n), 1), P)
        check(compose(Linv, L, P) == I and compose(L, Linv, P) == I, "B^-1 Lhat*T B two-sided (symbol)")
        u = rand_vec(n, 1, P=P)
        check(apply(Linv, apply(L, u, P), P) == u and apply(L, apply(Linv, u, P), P) == u,
              "explicit inverse on vectors")
        check(len(Linv) > 0 and all(abs(m[0]) < 100 for m in Linv), "inverse has finite range")
        check(preserves_symbol(Linv, B, P), "inverse preserves B")
    # (b) random non-preserving rules: both conditions fail together
    for B in (omega(1), omega(2), eye(2), eye(3)):
        B = mred(B, P)
        for _ in range(5):
            L = rand_rule(len(B), 1, P=P)
            ps = preserves_symbol(L, B, P)
            check(ps == preserves_form(L, B, P, trials=6), f"symbol and form conditions agree (P={P})")

# ---------- 5. alternating vs skew over ZMod 2 ----------
vs2 = list(itertools.product(range(2), repeat=2))
Bs = [[1, 0], [0, 0]]
check(all((Bs[i][j] + Bs[j][i]) % 2 == 0 for i in range(2) for j in range(2) if i != j)
      and mT(Bs) == Bs, "B symmetric = skew mod 2")
check(all((Bs[j][i] + Bs[i][j]) % 2 == 0 for i in range(2) for j in range(2)), "skew: B^T = -B mod 2")
check(any(sum(v[i] * Bs[i][j] * v[j] for i in range(2) for j in range(2)) % 2 for v in vs2),
      "skew but not alternating over ZMod 2")
O2 = mred(omega(1), 2)
check(all(sum(v[i] * O2[i][j] * v[j] for i in range(2) for j in range(2)) % 2 == 0 for v in vs2),
      "Omega alternating over ZMod 2")

# ---------- 6. Prop. 4.4 ----------
Om = sp.Matrix([[0, 1], [-1, 0]])
e = sp.symbols("e1:5")
f = sp.symbols("f1:5")
A, Bm = sp.Matrix(2, 2, e), sp.Matrix(2, 2, f)
check(sp.expand(Om.inv() * A.T * Om - A.adjugate()) == sp.zeros(2), "Omega^-1 M^T Omega = adj M")
check(sp.expand(A.adjugate() * Bm + Bm.adjugate() * A - (A.adjugate() * Bm).trace() * sp.eye(2))
      == sp.zeros(2), "adj(A)B + adj(B)A = tr(adj(A)B) 1")
sol = sp.solve(list(K - K.adjugate() for K in [A])[0][:] + [A.det()], e, dict=True)
check(sol == [{s: 0 for s in e}], "adj K = K with det K = 0 forces K = 0 over Q")

a1, a2, b1, b2, t = sp.symbols("a1 a2 b1 b2 t")
g = sp.symbols("g1:5")
l0 = sp.Matrix(2, 2, g)
av, bv = sp.Matrix([a1, a2]), sp.Matrix([b1, b2])
for v in (sp.Matrix([1, 0]), sp.Matrix([0, 1]), sp.Matrix([1, t])):
    lp, lm = v * av.T, v * bv.T
    # coefficient k of Lhat*T Omega Lhat: sum over m of l_m^T Om l_{m+k}
    coef = {1: lm.T * Om * l0 + l0.T * Om * lp, -1: l0.T * Om * lm + lp.T * Om * l0,
            2: lm.T * Om * lp, -2: lp.T * Om * lm}
    check(coef[2] == sp.zeros(2) or sp.expand(coef[2]) == sp.zeros(2), "k=2 holds for equal ranges")
    check(sp.expand(lm.adjugate() * lp) == sp.zeros(2), "adj(l-) l+ = 0 for equal ranges")
    eqs = [sp.expand(x) for k in (1, -1) for x in coef[k]] + [l0.det() - 1]
    gens = list(g) + [a1, a2, b1, b2] + ([t] if v[1] == t else [])
    y = sp.Symbol("y")
    for target in (a1 - b1, a2 - b2):  # radical membership via Rabinowitsch
        G = sp.groebner(eqs + [1 - y * target], y, *gens, order="lex")
        check(list(G.exprs) == [1], f"a = b forced (v = {list(v)}, {target})")
# k = +-2 conditions give adj(l-) l+ = 0 generically (general l+, l-)
lp, lm = sp.Matrix(2, 2, e), sp.Matrix(2, 2, f)
check(sp.expand(lm.T * Om * lp - (Om * lm.adjugate() * lp)) == sp.zeros(2),
      "k=2 coefficient = Omega adj(l-) l+")
check(sp.expand(lp.T * Om * lm - (Om * lp.adjugate() * lm)) == sp.zeros(2),
      "k=-2 coefficient = Omega adj(l+) l-")
lp_d, lm_d = sp.Matrix([1, 0]) * av.T, sp.Matrix([0, 1]) * bv.T
check(sp.expand(lm_d.adjugate() * lp_d) != sp.zeros(2), "different ranges: adj(l-) l+ != 0 generically")

# ---------- 6b. form (4.12): l+ = l- = e1 a^T, k=+-1 iff a = lambda r ----------
lam = sp.Symbol("lam")
l0 = sp.Matrix(2, 2, g)
r = sp.Matrix([g[2], g[3]])


def nn_conditions(l0, lp, lm):  # coefficients k = -2..2 of Lhat*T Om Lhat minus delta Om
    return {1: lm.T * Om * l0 + l0.T * Om * lp, -1: l0.T * Om * lm + lp.T * Om * l0,
            2: lm.T * Om * lp, -2: lp.T * Om * lm,
            0: lm.T * Om * lm + l0.T * Om * l0 + lp.T * Om * lp - Om}


e1 = sp.Matrix([1, 0])
lp = e1 * av.T
C = nn_conditions(l0, lp, lp)
check(sp.expand(C[1] - (av * r.T - r * av.T)) == sp.zeros(2), "k=1 coefficient = a r^T - r a^T")
check(sp.expand(C[-1] - C[1]) == sp.zeros(2), "k=-1 coefficient = k=1 coefficient")
lp = e1 * (lam * r).T
C = nn_conditions(l0, lp, lp)
check(all(sp.expand(C[k]) == sp.zeros(2) for k in (1, -1, 2, -2)), "(4.11b-e) hold for a = lam r")
check(sp.expand(C[0] - (l0.det() - 1) * Om) == sp.zeros(2), "(4.11a) iff det l0 = 1, all lam")
l0n = sp.Matrix([[2, 1], [1, 1]])
C = nn_conditions(l0n, e1 * sp.Matrix([1, 0]).T, e1 * sp.Matrix([1, 0]).T)
check(sp.expand(C[1]) != sp.zeros(2), "a = (1,0) not proportional to r = (1,1): k=1 fails")
l0F = sp.Matrix([[-sp.Symbol("m2"), -1], [1, 0]])
C = nn_conditions(l0F, e1 * sp.Matrix([1, 0]).T, e1 * sp.Matrix([1, 0]).T)
check(sp.Matrix([l0F[1, 0], l0F[1, 1]]) == sp.Matrix([1, 0])
      and all(sp.expand(C[k]) == sp.zeros(2) for k in C), "Fhat^-1: r = a = (1,0), lambda = 1")

# ---------- 7. leapfrog symbols ----------
z, m2 = sp.symbols("z m2")
F = sp.Matrix([[0, 1], [-1, z + 1 / z - m2]])
Fi = sp.Matrix([[z + 1 / z - m2, -1], [1, 0]])
for M in (F, Fi):
    check(sp.simplify(M.subs(z, 1 / z).T * Om * M - Om) == sp.zeros(2), "leapfrog symplectic")
    check(sp.simplify(M.subs(z, 1 / z) - M) == sp.zeros(2), "leapfrog even")
    lpl = M.applyfunc(lambda x: sp.expand(x).coeff(z, 1))
    lmi = M.applyfunc(lambda x: sp.expand(x * z).coeff(z, 0))
    check(lpl == lmi and lpl.rank() == 1, "l+ = l- rank one")
check(sp.simplify(F * Fi) == sp.eye(2), "Fi is the inverse of F")
l0 = Fi.applyfunc(lambda x: sp.expand(x).coeff(z, 0))
check(l0 == sp.Matrix([[-m2, -1], [1, 0]]), "Fi: l0")
lpm = Fi.applyfunc(lambda x: sp.expand(x).coeff(z, 1))
check(lpm == sp.Matrix([[l0[1, 0], l0[1, 1]], [0, 0]]) == sp.Matrix([[1, 0], [0, 0]]), "(4.12), lambda=1")
for mm in (0, 1, 2):
    Frule = {(0,): [[0, 1], [-1, -mm]], (1,): [[0, 0], [0, 1]], (-1,): [[0, 0], [0, 1]]}
    for _ in range(3):
        u = rand_vec(2, 1, box=4)
        g_ = lambda x, i: u.get(x, [0, 0])[i]
        xs = {(x[0] + s,) for x in u for s in (-1, 0, 1)}
        direct = clean({x: [g_(x, 1), -g_(x, 0) + g_((x[0] + 1,), 1) + g_((x[0] - 1,), 1) - mm * g_(x, 1)]
                        for x in xs}, None, True)
        check(apply(Frule, u) == direct, f"F recursion matches symbol F (m2={mm})")

# 8. The gap in thesis Prop. 4.4: pure shifts. For S in SL2, the nearest-neighbour
#    rule with l- = S, l0 = 0, l+ = 0 (symbol S z^-1) is symplectic, although l0 is not in SL2
#    and l+ != l-. Likewise S z. The corrected statement has two branches (Q1.tex, Proposition 11).
_z = sp.symbols("zz")
_O = sp.Matrix([[0, 1], [-1, 0]])
for S in [sp.Matrix([[1, 0], [0, 1]]), sp.Matrix([[2, 3], [1, 2]]), sp.Matrix([[0, 1], [-1, 0]])]:
    check(S.det() == 1, "S in SL2")
    for k in (1, -1):
        Lh = S * _z**k
        check(sp.simplify(Lh.subs(_z, 1 / _z).T * _O * Lh - _O) == sp.zeros(2),
              "pure shift S z^k is symplectic")
# The branch analysis with l+ = 0: the z^1 coefficient is Omega adj(l-) l0, the z^-1
# coefficient Omega adj(l0) l-, and the z^0 coefficient (det l- + det l0 - 1) Omega.
a_ = sp.Matrix(2, 2, sp.symbols("p0:4"))
b_ = sp.Matrix(2, 2, sp.symbols("q0:4"))
E = sp.expand((a_ * _z + b_).T * _O * (a_ / _z + b_) - _O)
c1 = E.applyfunc(lambda e: sp.expand(e * _z).coeff(_z, 2))
cm1 = E.applyfunc(lambda e: sp.expand(e * _z).coeff(_z, 0))
c0 = E.applyfunc(lambda e: sp.expand(e * _z).coeff(_z, 1))
check(sp.expand(c1 - _O * a_.adjugate() * b_) == sp.zeros(2), "z^1: Omega adj(l-) l0")
check(sp.expand(cm1 - _O * b_.adjugate() * a_) == sp.zeros(2), "z^-1: Omega adj(l0) l-")
check(sp.expand(c0 - (a_.det() + b_.det() - 1) * _O) == sp.zeros(2),
      "z^0: (det l- + det l0 - 1) Omega")

# 9. The hybrid form: evaluating a symbol at z = e^{-ik} gives Krueger's
#    Gamma^(k) = sum_m l_m e^{-ikm} (thesis (4.14)); the leapfrog trace is 2 cos k - m2.
_k, _m2 = sp.symbols("kk mm2", real=True)
Fhat = sp.Matrix([[0, 1], [-1, _z + 1 / _z - _m2]])
Fk = Fhat.subs(_z, sp.exp(-sp.I * _k))
check(sp.simplify(sp.expand_complex(Fk.trace()) - (2 * sp.cos(_k) - _m2)) == 0,
      "leapfrog Fourier symbol trace 2 cos k - m2")
coeffs = {-1: sp.Matrix([[0, 0], [0, 1]]), 0: sp.Matrix([[0, 1], [-1, -_m2]]),
          1: sp.Matrix([[0, 0], [0, 1]])}
series = sum((c * sp.exp(-sp.I * _k * m) for m, c in coeffs.items()), sp.zeros(2))
check(sp.simplify(Fk - series) == sp.zeros(2), "evaluated symbol = sum_m l_m e^{-ikm}")

# 10. Translation examples (Q1.tex Examples 16-20).
# 10a. On-site rule: S^T Omega S = Omega  <=>  S Omega S^T = Omega (BosonicLean's hypothesis),
#      for n = 1 and n = 2 (Omega positions first), on symplectic and non-symplectic samples.
def omega(n):
    return sp.Matrix(sp.BlockMatrix([[sp.zeros(n), sp.eye(n)], [-sp.eye(n), sp.zeros(n)]]))


random.seed(11)
for n in (1, 2):
    On = omega(n)
    samples = []
    for _ in range(6):
        A = sp.Matrix(n, n, [random.randint(-2, 2) for _ in range(n * n)])
        Bs = sp.Matrix(n, n, [random.randint(-2, 2) for _ in range(n * n)])
        Bs = Bs + Bs.T
        lower = sp.Matrix(sp.BlockMatrix([[sp.eye(n), sp.zeros(n)], [Bs, sp.eye(n)]]))
        upper = sp.Matrix(sp.BlockMatrix([[sp.eye(n), Bs], [sp.zeros(n), sp.eye(n)]]))
        samples.append(lower * upper * lower)          # symplectic
        samples.append(sp.Matrix(2 * n, 2 * n, [random.randint(-2, 2) for _ in range(4 * n * n)]))
    for S in samples:
        c1 = S.T * On * S == On
        c2 = S * On * S.T == On
        check(c1 == c2, f"on-site: S^T O S = O iff S O S^T = O (n={n})")
# 10b. Krueger's form (4.10): Gamma^+ = Omega^{-1} Gamma^T Omega; his components
#      sum_x Gamma^+_x Gamma_{u+x} are Omega^{-1} times ours, sum_m l_m^T Omega l_{m+u}.
O1 = omega(1)
rule = {-1: sp.Matrix([[1, 0], [0, 0]]), 0: sp.Matrix([[-3, -1], [1, 0]]),
        1: sp.Matrix([[1, 0], [0, 0]])}                  # F^{-1} at m2 = 3
for u in range(-2, 3):
    ours = sum((rule[m].T * O1 * rule.get(m + u, sp.zeros(2)) for m in rule), sp.zeros(2))
    his = sum((O1.inv() * rule[m].T * O1 * rule.get(m + u, sp.zeros(2)) for m in rule),
              sp.zeros(2))
    check(his == O1.inv() * ours, f"(4.10) = Omega^-1 x ours (u={u})")
    check(his == (sp.eye(2) if u == 0 else sp.zeros(2)), f"(4.10) holds for F^-1 (u={u})")
# 10c. Fourier picture: for a real symplectic symbol, Gamma^(k)^H Omega Gamma^(k) = Omega for all k;
#      a non-even example (a sheared shift) so the conjugate transpose matters.
Lsym = sp.Matrix([[1, 0], [_z + 1 / _z, 1]]) * sp.Matrix([[_z, 0], [0, _z]]) * \
    sp.Matrix([[1, 2], [0, 1]])
check(sp.simplify(Lsym.subs(_z, 1 / _z).T * O1 * Lsym - O1) == sp.zeros(2), "sample symplectic")
Gk = Lsym.subs(_z, sp.exp(-sp.I * _k))
check(sp.simplify((Gk.H * O1 * Gk - O1).applyfunc(sp.expand_complex)) == sp.zeros(2),
      "Gamma^(k)^H Omega Gamma^(k) = Omega")
check(sp.simplify((Gk.T * O1 * Gk - O1).applyfunc(sp.expand_complex)) != sp.zeros(2),
      "plain transpose fails for a non-even symbol")
# 10d. Krueger's example (4.18): Gamma_0 = rotation by phi, Gamma_pm = lambda [[sin, cos],[0,0]].
phi, lam = sp.symbols("phi lam", real=True)
G0 = sp.Matrix([[sp.cos(phi), -sp.sin(phi)], [sp.sin(phi), sp.cos(phi)]])
Gpm = sp.Matrix([[G0[1, 0], G0[1, 1]], [0, 0]])
Ghat_rot = G0 + lam * (_z + 1 / _z) * Gpm
check(sp.simplify(Ghat_rot.det()) == 1, "(4.18): det = 1")
check(sp.simplify(Ghat_rot.subs(_z, 1 / _z).T * O1 * Ghat_rot - O1) == sp.zeros(2),
      "(4.18): symplectic")
Grk = Ghat_rot.subs(_z, sp.exp(-sp.I * _k))
tr = sp.simplify(sp.expand_complex(Grk.trace()))
check(sp.simplify(tr - (2 * sp.cos(phi) + 2 * lam * sp.cos(_k) * sp.sin(phi))) == 0,
      "(4.18): tr = 2cos phi + 2 lam cos k sin phi")
# (4.19): tr = 2 cos alpha, cos alpha = cos phi + f cos k sin phi -- consistent, no factor-2 issue
check(sp.simplify(tr / 2 - (sp.cos(phi) + lam * sp.cos(_k) * sp.sin(phi))) == 0,
      "(4.19): cos alpha = cos phi + f cos k sin phi")
check(sp.simplify((Grk - (G0 + 2 * lam * sp.cos(_k) * Gpm)).applyfunc(sp.expand_complex))
      == sp.zeros(2),
      "(4.15): Gamma^(k) = Gamma_0 + 2 f cos k Gamma_pm")

# 11. The equational route to Proposition 11 used in Lean (2x2 identities, any comm. ring).
A2 = sp.Matrix(2, 2, sp.symbols("e0:4"))
B2 = sp.Matrix(2, 2, sp.symbols("f0:4"))
check(sp.expand(A2.T * O1 * B2 - O1 * A2.adjugate() * B2) == sp.zeros(2), "A^T O B = O adj(A) B")
check(sp.expand((A2 + B2).adjugate() - A2.adjugate() - B2.adjugate()) == sp.zeros(2),
      "adj is additive (2x2)")
check(sp.expand((A2 + B2).det() - A2.det() - B2.det() - (A2.adjugate() * B2).trace()) == 0,
      "det(A+B) = det A + det B + tr(adj(A) B)")
K = sp.Matrix(2, 2, sp.symbols("g0:4"))
sol = sp.solve(list(K.adjugate() - K), list(K), dict=True)
check(len(sol) == 1 and sp.simplify(K.subs(sol[0]) - K[0, 0].subs(sol[0]) * sp.eye(2))
      == sp.zeros(2), "adj K = K iff K = c 1")
# The Proposition 11 derivation on the F^{-1} rule and on a pure shift, symbolically confirmed above;
# here the key step: with (C2) and det l+- = 0, det(l- - l+) = 0.
v = sp.Matrix(sp.symbols("v0:2"))
a_, b_ = sp.Matrix(sp.symbols("a0:2")), sp.Matrix(sp.symbols("b0:2"))
lp_, lm_ = v * a_.T, v * b_.T
check(sp.expand(lm_.adjugate() * lp_) == sp.zeros(2), "equal ranges => adj(l-) l+ = 0")
check(sp.expand((lm_ - lp_).det()) == 0, "det(l- - l+) = 0")

print(f"check_q1: {count} checks passed")
