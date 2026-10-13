"""
Exact checks for milestone Q5: Gaussian channels over (V, sigma), the
lattice results of thesis section 4.3, and the findings F1-F8. Every assertion is an exact
equality or an exact sign test (sympy rationals, Gaussian rationals, and symbolic identities);
no tolerances.

Run with python3 (sympy only).

Conventions:
  Omega = [[0, 1], [-1, 0]] per mode, positions first for n modes (BosonicLean's symplecticForm);
  sigma(u, w) = u^T Omega w (on the lattice: sum_x u(x)^T Omega w(x));
  a channel acts by T(W(u)) = exp(i l(u) - nu(u,u)/4) W(Gamma u), Gamma, nu as matrices;
  dissipation form C = nu + i Omega - i Gamma^T Omega Gamma   (thesis (4.34), sign of (4.35));
  a lattice rule is a dict m -> l_m with (L u)(x) = sum_m l_m u(x - m) (symbol sum_m l_m z^m);
  a translation-invariant form has kernel g: nu(u, w) = sum_{x,y} u(x)^T g(x - y) w(y)
    (QCALean's cellForm), with Laurent symbol g_hat(z) = sum_d g(d) z^d;
  Fourier symbols at z = e^{-ik}; the pull-back of a form by L has symbol L_hat^*T g_hat L_hat.
  Positive semidefiniteness of a Hermitian matrix is tested exactly by all principal minors >= 0.
"""
import itertools
import random

import sympy as sp

I = sp.I
R = sp.Rational
random.seed(20260929)
count = 0


def check(cond, msg):
    global count
    assert cond, msg
    count += 1


def omega(n):
    Z, E = sp.zeros(n), sp.eye(n)
    return sp.BlockMatrix([[Z, E], [-E, Z]]).as_explicit()


def rand_q(lo=-5, hi=5):
    return R(random.randint(lo, hi), random.randint(1, 4))


def rand_mat(r, c):
    return sp.Matrix(r, c, lambda i, j: rand_q())


def rand_sym(n):
    A = rand_mat(n, n)
    return (A + A.T) / 2


def is_zero(M):
    return all(sp.simplify(x) == 0 for x in M)


def is_psd(H):
    """Exact PSD test for a Hermitian matrix: all principal minors are >= 0."""
    H = sp.Matrix(H)
    n = H.shape[0]
    if not is_zero(H - H.H):
        return False
    for k in range(1, n + 1):
        for idx in itertools.combinations(range(n), k):
            m = sp.nsimplify(sp.expand(H.extract(list(idx), list(idx)).det()))
            if sp.im(m) != 0 or sp.re(m) < 0:
                return False
    return True


def transvection(v, t, Sig):
    """x -> x + t sigma(v, x) v, a symplectic map for the form Sig (sigma(u,w) = u^T Sig w)."""
    return sp.eye(len(v)) + t * v * (v.T * Sig)


def rand_symplectic(Sig, k=4):
    n = Sig.shape[0]
    S = sp.eye(n)
    for _ in range(k):
        S = transvection(rand_mat(n, 1), rand_q(), Sig) * S
    return S


# ---------------------------------------------------------------------------------------------
# A. The product formula (4.35) and the action on Gaussian states ((4.33), F1)
# ---------------------------------------------------------------------------------------------
n = 2
OM = omega(n)
for trial in range(12):
    G, nu, ell = rand_mat(2 * n, 2 * n), rand_sym(2 * n), rand_mat(1, 2 * n)
    u, w = rand_mat(2 * n, 1), rand_mat(2 * n, 1)
    sig = lambda a, b: (a.T * OM * b)[0]
    f = lambda a, b: (a.T * nu * b)[0]
    l = lambda a: (ell * a)[0]
    C = lambda a, b: f(a, b) + I * sig(a, b) - I * sig(G * a, G * b)
    # T(W(u) W(w)) = e^{-i sigma(u,w)/2} T(W(u+w)): phase in front of W(Gamma(u+w))
    lhs = -I * sig(u, w) / 2 + I * l(u + w) - f(u + w, u + w) / 4
    # e^{-C(u,w)/2} T(W(u)) T(W(w)), with W(Gu) W(Gw) = e^{-i sigma(Gu,Gw)/2} W(G(u+w))
    rhs = -C(u, w) / 2 + (I * l(u) - f(u, u) / 4) + (I * l(w) - f(w, w) / 4) \
        - I * sig(G * u, G * w) / 2
    check(sp.expand(lhs - rhs) == 0, '(4.35)')
    # the thesis's intermediate line: i sigma(Gu,Gw)/2 - i sigma(u,w)/2 - nu(u,w)/2 (with l = 0)
    check(sp.expand((-I * sig(u, w) / 2 - f(u + w, u + w) / 4)
                    - (I * sig(G * u, G * w) / 2 - I * sig(u, w) / 2 - f(u, w) / 2
                       - f(u, u) / 4 - f(w, w) / 4 - I * sig(G * u, G * w) / 2)) == 0,
          '(4.35), the thesis line on p. 92')
    # F2: C is real-bilinear, so C(t u, w) = t C(u, w); e^{-C/2} = 1 for all t forces C = 0
    t = rand_q()
    check(sp.expand(C(t * u, w) - t * C(u, w)) == 0, 'F2: C is linear in u')
    # States (4.33), corrected (F1): omega(T(W(u))) = exp(i d'(u) - gamma'(u,u)/4)
    gam, d = rand_sym(2 * n), rand_mat(1, 2 * n)
    chi = lambda cov, disp, a: I * (disp * a)[0] - (a.T * cov * a)[0] / 4
    out = I * l(u) - f(u, u) / 4 + chi(gam, d, G * u)
    check(sp.expand(out - chi(G.T * gam * G + nu, d * G + ell, u)) == 0,
          'F1: covariance Gamma^T gamma Gamma + nu, displacement d Gamma + l')
    if f(u, u) != 0:
        check(sp.expand(out - (I * l(u) + f(u, u) / 4 + chi(gam, d, G * u))) != 0,
              'F1: the printed +g/4 in (4.33) disagrees')

# ---------------------------------------------------------------------------------------------
# B. Concatenation (p. 96) and its dissipation form
# ---------------------------------------------------------------------------------------------
for trial in range(8):
    G1, G2 = rand_mat(2 * n, 2 * n), rand_mat(2 * n, 2 * n)
    n1, n2 = rand_sym(2 * n), rand_sym(2 * n)
    l1, l2 = rand_mat(1, 2 * n), rand_mat(1, 2 * n)
    u = rand_mat(2 * n, 1)
    # T2(T1(W(u))) = e^{i l1(u) - n1(u,u)/4} e^{i l2(G1 u) - n2(G1u,G1u)/4} W(G2 G1 u)
    ph = I * (l1 * u)[0] - (u.T * n1 * u)[0] / 4 + I * (l2 * G1 * u)[0] \
        - ((G1 * u).T * n2 * (G1 * u))[0] / 4
    G, nu, ell = G2 * G1, n1 + G1.T * n2 * G1, l1 + l2 * G1
    check(sp.expand(ph - (I * (ell * u)[0] - (u.T * nu * u)[0] / 4)) == 0, 'concatenation data')
    Cm = lambda Gm, num: num + I * OM - I * Gm.T * OM * Gm
    check(is_zero(Cm(G, nu) - (Cm(G1, n1) + G1.T * Cm(G2, n2) * G1)),
          'dissipation form of a concatenation: C1 + G1^T C2 G1')

# ---------------------------------------------------------------------------------------------
# C. Special cases of the condition (4.34)
# ---------------------------------------------------------------------------------------------
for trial in range(6):
    G = rand_mat(2 * n, 2 * n)
    A = OM - G.T * OM * G
    if not is_zero(A):
        Cz = I * A   # nu = 0
        check(sp.simplify(Cz.trace()) == 0 and not is_zero(Cz) and not is_psd(Cz),
              'nu = 0 and Gamma not symplectic: C = i(Omega - G^T Omega G) is not PSD')
    S = rand_symplectic(OM)
    check(is_zero(S.T * OM * S - OM), 'random symplectic matrix')
    nu = rand_sym(2 * n)
    check(is_zero((nu + I * OM - I * S.T * OM * S) - nu), 'symplectic Gamma: C = nu')
check(is_psd(sp.eye(2) + I * omega(1)) and not is_psd(R(1, 2) * sp.eye(2) + I * omega(1)),
      'Gamma = 0: C = nu + i Omega, the state condition (vacuum yes, half-vacuum no)')

# ---------------------------------------------------------------------------------------------
# D. Finite modes: channel matrices (X, Y) in BosonicLean's convention
# ---------------------------------------------------------------------------------------------
for trial in range(8):
    G, nu, gam = rand_mat(2 * n, 2 * n), rand_sym(2 * n), rand_sym(2 * n)
    X, Y, M = OM.T * G.T * OM, OM.T * nu * OM, OM.T * gam * OM
    check(is_zero(OM * OM.T - sp.eye(2 * n)), 'Omega orthogonal')
    check(is_zero(OM.T * (G.T * gam * G + nu) * OM - (X * M * X.T + Y)),
          'output covariance: X M X^T + Y')
    Cf = nu + I * OM - I * G.T * OM * G
    check(is_zero(OM.T * Cf * OM - (Y + I * OM - I * X * OM * X.T)),
          'condition (4.34) in matrix form: Y + i Omega - i X Omega X^T')
    check(is_zero((Y + I * OM - I * X * OM * X.T).conjugate() - (Y - I * OM + I * X * OM * X.T)),
          'complex conjugate: Y - i Omega + i X Omega X^T (same PSD status, real matrices)')
    check(is_zero((X * M * X.T + Y) - I * OM
                  - (X * (M - I * OM) * X.T + (Y - I * OM + I * X * OM * X.T))),
          'admissibility is preserved: sum of two PSD matrices')
one = sp.eye(2)
chan = lambda X, Y: is_psd(Y - I * omega(1) + I * X * omega(1) * X.T)
check(chan(R(3, 5) * one, R(16, 25) * one), 'attenuator eta = 9/25 with vacuum noise')
check(not chan(R(3, 5) * one, R(8, 25) * one), 'attenuator with half the noise is not a channel')
check(chan(R(5, 3) * one, R(16, 9) * one), 'amplifier G = 25/9 with minimal noise')
check(is_psd(one - I * omega(1)), "vacuum admissible in BosonicLean's sign (gamma - i Omega)")
out = R(3, 5) * one * one * R(3, 5) * one + R(16, 25) * one
check(out == one, 'attenuator maps the vacuum to the vacuum')

# ---------------------------------------------------------------------------------------------
# E. Dilation at covariance level (general core of Lemma 4.12, (4.40), F7)
# ---------------------------------------------------------------------------------------------
def dilation_case(ns, na, S):
    Sig = sp.diag(omega(ns), omega(na))
    check(is_zero(S.T * Sig * S - Sig), 'S symplectic for sigma + sigma\'')
    A, Cb = S[:2 * ns, :2 * ns], S[2 * ns:, :2 * ns]
    gp = sp.eye(2 * na) * 2        # thermal ancilla, gamma' + i Omega' >= 0
    check(is_psd(gp + I * omega(na)), 'ancilla state condition')
    nu = Cb.T * gp * Cb
    Cd = nu + I * omega(ns) - I * A.T * omega(ns) * A
    check(is_zero(Cd - Cb.T * (gp + I * omega(na)) * Cb), 'F7: C = C^T (gamma\' + i sigma\') C')
    check(is_psd(Cd), 'F7: the dilation data satisfy (4.34)')
    gam = rand_sym(2 * ns)
    red = (S.T * sp.diag(gam, gp) * S)[:2 * ns, :2 * ns]
    check(is_zero(red - (A.T * gam * A + nu)), '(4.40): reduced covariance')


c5, s5 = R(3, 5), R(4, 5)
BS = sp.Matrix([[c5, 0, s5, 0], [0, c5, 0, s5], [-s5, 0, c5, 0], [0, -s5, 0, c5]])
dilation_case(1, 1, BS)
dilation_case(1, 1, rand_symplectic(sp.diag(omega(1), omega(1))))
dilation_case(1, 2, rand_symplectic(sp.diag(omega(1), omega(2)), k=6))
dilation_case(2, 1, rand_symplectic(sp.diag(omega(2), omega(1)), k=6))

# ---------------------------------------------------------------------------------------------
# F. The lattice: rules, kernels, symbols (n = 1)
# ---------------------------------------------------------------------------------------------
O1 = omega(1)


def apply(L, u):
    out = {}
    for m, lm in L.items():
        for x, v in u.items():
            out[x + m] = out.get(x + m, sp.zeros(2, 1)) + lm * v
    return out


def sigma_l(u, w):
    return sum(((u[x].T * O1 * w[x])[0] for x in u if x in w), sp.Integer(0))


def cellform(g, u, w):
    return sum(((u[x].T * g[x - y] * w[y])[0] for x in u for y in w if x - y in g),
               sp.Integer(0))


def lmul(P, Q):
    out = {}
    for a, A in P.items():
        for b, B in Q.items():
            out[a + b] = out.get(a + b, sp.zeros(A.shape[0], B.shape[1])) + A * B
    return {k: v for k, v in out.items() if not is_zero(v)}


def lstar(P):
    return {-a: A.H for a, A in P.items()}


def const(M):
    return {0: M}


def pullback(L, g):
    """Kernel of g(L., L.): Laurent symbol L^*T g L."""
    return lmul(lmul(lstar(L), g), L)


def supp(P):
    return {k for k, v in P.items() if not is_zero(v)}


def rand_vec_lattice(k=3):
    return {x: rand_mat(2, 1) for x in random.sample(range(-4, 5), k)}


def rand_rule(support):
    return {m: rand_mat(2, 2) for m in support}


def evalz(P, z):
    z = sp.sympify(z)   # a Python int to a negative power would become a float
    return sum((A * z ** a for a, A in P.items()), sp.zeros(*next(iter(P.values())).shape))


for trial in range(6):
    L = rand_rule([-1, 0, 2])
    g = {0: rand_sym(2)}
    B = rand_mat(2, 2)
    g[1], g[-1] = B, B.T
    u, w = rand_vec_lattice(), rand_vec_lattice()
    K = pullback(L, const(O1))
    check(sp.expand(sigma_l(apply(L, u), apply(L, w)) - cellform(K, u, w)) == 0,
          'kernel of sigma(L.,L.) is the Laurent symbol L^*T Omega L')
    H = pullback(L, g)
    check(sp.expand(cellform(g, apply(L, u), apply(L, w)) - cellform(H, u, w)) == 0,
          'kernel of nu(L.,L.) is L^*T g L')
    NmN = {a - b for a in L for b in L}
    check(supp(H) <= {d + e for d in supp(g) for e in NmN}, 'support of the pull-back')
    # thesis (4.36): sum_x Gamma_x^+ Gamma_{D+x}, Gamma^+ = -sigma Gamma^T sigma (p. 79)
    for D in range(-4, 5):
        th = sum((-O1 * L[x].T * O1 * L[D + x] for x in L if D + x in L), sp.zeros(2))
        check(is_zero(th - (-O1) * K.get(D, sp.zeros(2))),
              '(4.36) is Omega^{-1} times the coefficient of L^*T Omega L at z^D')
    # Fourier: symbol at z on the unit circle is Gamma_hat(k)^* Omega Gamma_hat(k)
    for z in (R(3, 5) + R(4, 5) * I, R(5, 13) - R(12, 13) * I, I, -1):
        Lz = evalz(L, z)
        check(is_zero(sp.expand(evalz(K, z) - Lz.H * O1 * Lz)), 'Fourier form of the pull-back')

# ---------------------------------------------------------------------------------------------
# G. F3: the shift satisfies II with M = {0} but not I with N = {0}
# ---------------------------------------------------------------------------------------------
shift = {1: sp.eye(2)}
check(pullback(shift, const(O1)) == {0: O1}, 'F3: shift preserves sigma, C = 0 with nu = 0')
check(supp(shift) == {1} and not supp(shift) <= {0}, 'F3: range {1}, so I fails for N = {0}')

# ---------------------------------------------------------------------------------------------
# H. Lemma 4.11 II, sigma part: symbol support within M
# ---------------------------------------------------------------------------------------------
half = {0: R(1, 2) * sp.eye(2), 1: R(1, 2) * sp.eye(2)}
Kh = pullback(half, const(O1))
check(supp(Kh) == {-1, 0, 1} and is_zero(Kh[1] - R(1, 4) * O1),
      'Gamma = (1 + s)/2: coefficient Omega/4 at z^{+-1}; II fails for M = {0}, holds for {-1,0,1}')

# ---------------------------------------------------------------------------------------------
# I. F5: supports under concatenation are inclusions
# ---------------------------------------------------------------------------------------------
G1 = {0: sp.eye(2), 1: sp.eye(2)}
G2 = {0: sp.eye(2), 1: -sp.eye(2)}
P = lmul(G2, G1)
check(supp(P) == {0, 2} and {a + b for a in G1 for b in G2} == {0, 1, 2},
      'F5: (1 - s)(1 + s) = 1 - s^2, range {0,2} strictly inside N1 + N2 = {0,1,2}')
g1 = {0: sp.eye(2)}
g2 = {0: sp.eye(2)}
Hc = pullback(G1, g2)
nu_c = dict(g1)
for k, v in Hc.items():
    nu_c[k] = nu_c.get(k, sp.zeros(2)) + v
check(supp(nu_c) <= set(g1) | {m + a - b for m in g2 for a in G1 for b in G1},
      'F5: noise support within M1 u (M2 + N1 - N1)')

# ---------------------------------------------------------------------------------------------
# J. F6: the p. 97 counterexample needs noise in the coupled quadrature (4.39)
# ---------------------------------------------------------------------------------------------
phi, lam, a, b, c = sp.symbols('phi lam a b c', real=True)
Rot = sp.Matrix([[sp.cos(phi), -sp.sin(phi)], [sp.sin(phi), sp.cos(phi)]])
e1 = sp.Matrix([1, 0])
r = Rot[1, :]                                     # momentum row (sin phi, cos phi)
lpm = lam * e1 * r                                # QCALean rotationSymbol: l_+- = lam e1 r^T
Lrot = {-1: lpm, 0: Rot, 1: lpm}
g0 = sp.Matrix([[a, c], [c, b]])
Hk = pullback(Lrot, const(g0))
check(is_zero(sp.simplify(Hk[2] - a * lam ** 2 * r.T * r)) and
      is_zero(sp.simplify(Hk[-2] - a * lam ** 2 * r.T * r)), 'F6: K(+-2) = a lam^2 r r^T')
check(sp.simplify(Hk[2].trace() - a * lam ** 2) == 0, 'F6: tr K(2) = a lam^2, so K(2) = 0 iff a lam = 0')
check(all(sp.simplify(x.subs({a: 0, c: 0})) == 0 for d in (1, -1, 2, -2) for x in Hk[d]),
      'F6: momentum-only noise diag(0, b) keeps the composite noise on site')
check(set(Hk) <= {-2, -1, 0, 1, 2}, 'F6: composite noise range within {-2..2}')
# (4.39) in the thesis's orientation: sum_y Gamma^T(y - x) g Gamma(y) equals K(x)
for x in (-2, -1, 1, 2):
    th = sum((Lrot[y - x].T * g0 * Lrot[y] for y in Lrot if y - x in Lrot), sp.zeros(2))
    check(is_zero(sp.simplify(th - Hk[x])), "(4.39): the thesis's sum is K(x)")
# PSD g0 with a = 0 forces c = 0 (2x2 minors), so for PSD noise: (4.39) holds iff lam a = 0
check(sp.Matrix([[0, c], [c, b]]).det() == -c ** 2, 'PSD with a = 0 forces c = 0')
# exact instance: cos phi = 3/5, lam = 1/2, isotropic noise
inst = {sp.cos(phi): R(3, 5), sp.sin(phi): R(4, 5)}
Hn = {k: v.subs(inst).subs({lam: R(1, 2), a: 1, b: 1, c: 0}) for k, v in Hk.items()}
check(not is_zero(Hn[2]) and is_zero(Hn[2] - R(1, 4) * sp.Matrix([[R(16, 25), R(12, 25)],
                                                               [R(12, 25), R(9, 25)]])),
      'F6 instance: K(2) = (1/4) r r^T with r = (4/5, 3/5)')

# ---------------------------------------------------------------------------------------------
# K. F8: the lossy example rule sqrt(eta) L(phi, lam) with vacuum noise (1 - eta) on site
# ---------------------------------------------------------------------------------------------
eta, sq = R(9, 25), R(3, 5)
Lq = {k: v.subs(inst).subs({lam: R(1, 2)}) for k, v in Lrot.items()}
check(pullback(Lq, const(O1)) == {0: O1}, 'the example rule is symplectic (Q1, Example 19)')
Gam = {k: sq * v for k, v in Lq.items()}
Kg = pullback(Gam, const(O1))
check(Kg == {0: eta * O1}, 'F8: symbol form eta Omega, support {0}: II holds with M = {0}')
check(not is_zero(Kg[0] - O1), 'F8: not symplectic')
nu8 = {0: (1 - eta) * sp.eye(2)}
for z in (R(3, 5) + R(4, 5) * I, R(5, 13) + R(12, 13) * I, I, -1, 1):
    Cz = evalz(nu8, z) + I * O1 - I * evalz(Kg, z)
    check(is_zero(sp.expand(Cz - (1 - eta) * (sp.eye(2) + I * O1))) and is_psd(sp.expand(Cz)),
          'F8: Fourier form of (4.34), C(k) = (1 - eta)(1 + i Omega) >= 0')
two = pullback(Gam, nu8)
comp = {k: v for k, v in two.items()}
comp[0] = comp.get(0, sp.zeros(2)) + nu8[0]
check(not is_zero(comp[2]) and is_zero(comp[2] - eta * (1 - eta) * R(1, 4) *
                                       sp.Matrix([[R(16, 25), R(12, 25)], [R(12, 25), R(9, 25)]])),
      'F8: the two-step lossy channel has noise at distance 2, so M = {0} fails')

# ---------------------------------------------------------------------------------------------
# L. Lemma 4.10(v), I does not imply II: data with Gamma = 0 (question 3, explicit data)
# ---------------------------------------------------------------------------------------------
check(is_psd(sp.eye(2) + I * O1), '1 + i Omega >= 0')
for M in ({0}, {-1, 0, 1}, {-2, -1, 0, 1, 2}):
    x0 = max(M) + 1
    g = {0: 2 * sp.eye(2), x0: R(1, 2) * sp.eye(2), -x0: R(1, 2) * sp.eye(2)}
    check(x0 not in M and not is_zero(g[x0]), 'noise outside M')
    for z in (R(3, 5) + R(4, 5) * I, R(5, 13) + R(12, 13) * I, I, -1, 1, -I):
        Cz = sp.expand(evalz(g, z) + I * O1)
        check(is_psd(Cz), 'Fourier form of (4.34) for Gamma = 0')
        gz = sp.expand(evalz(g, z)[0, 0])
        check(sp.im(gz) == 0 and sp.re(gz) >= 1, 'g_hat(k) = 2 + cos(k x0) >= 1')

# ---------------------------------------------------------------------------------------------
# M. Lemma 4.12 on the lattice: Gamma_hat = A_hat, nu_hat = C_hat^* gamma' C_hat, supports
# ---------------------------------------------------------------------------------------------
Sig2 = sp.diag(O1, O1)
BSd = const(BS)
shift_anc = {0: sp.diag(sp.eye(2), sp.zeros(2)), 1: sp.diag(sp.zeros(2), sp.eye(2))}
c13, s13 = R(5, 13), R(12, 13)
BS2 = const(sp.Matrix([[c13, 0, s13, 0], [0, c13, 0, s13], [-s13, 0, c13, 0], [0, -s13, 0, c13]]))
S = lmul(BS2, lmul(shift_anc, BSd))
check(pullback(S, const(Sig2)) == {0: Sig2}, 'S_hat symplectic (Laurent)')
A_ = {k: v[:2, :2] for k, v in S.items() if not is_zero(v[:2, :2])}
C_ = {k: v[2:, :2] for k, v in S.items() if not is_zero(v[2:, :2])}
gp = 2 * sp.eye(2)
nuL = pullback(C_, const(gp))
D = supp(S)
check(supp(A_) <= D and supp(nuL) <= {p - q for p in D for q in D},
      'F7: range of Gamma within D, noise within D - D')
check(supp(nuL) == {-1, 0, 1}, 'the example has correlated noise (range {-1,0,1})')
Cd = {k: v for k, v in nuL.items()}
Cd[0] = Cd.get(0, sp.zeros(2)) + I * O1
for k, v in pullback(A_, const(O1)).items():
    Cd[k] = Cd.get(k, sp.zeros(2)) - I * v
Cd = {k: v for k, v in Cd.items() if not is_zero(v)}
check(Cd == pullback(C_, const(gp + I * O1)), 'F7 on the lattice: C_hat = C^* (gamma\' + i Omega) C')
B = rand_mat(2, 2)
gl = {0: rand_sym(2), 1: B, -1: B.T}
full = pullback(S, {k: sp.diag(v, gp if k == 0 else sp.zeros(2)) for k, v in gl.items()})
red = {k: v[:2, :2] for k, v in full.items() if not is_zero(v[:2, :2])}
rhs = dict(pullback(A_, gl))
for k, v in nuL.items():
    rhs[k] = rhs.get(k, sp.zeros(2)) + v
rhs = {k: v for k, v in rhs.items() if not is_zero(v)}
check(red.keys() == rhs.keys() and all(is_zero(red[k] - rhs[k]) for k in red),
      '(4.40) on the lattice: [S^*T (gamma + gamma\') S]_11 = A^* gamma A + C^* gamma\' C')

# ---------------------------------------------------------------------------------------------
# N. The sketch statements of milestone Q5 as written
# ---------------------------------------------------------------------------------------------
def coeff_support(Ls):
    return {m for m, A in Ls.items() if not is_zero(A)}


def pullback_kernel(Ls, g, d):
    """SketchQ5.pullbackKernel verbatim: sum_{m,m'} (l_m)^T g(d + m - m') l_{m'}."""
    rows = next(iter(Ls.values())).shape[1]
    tot = sp.zeros(rows, rows)
    for m in coeff_support(Ls):
        for mp in coeff_support(Ls):
            if d + m - mp in g:
                tot += Ls[m].T * g[d + m - mp] * Ls[mp]
    return tot


def on_site(g0):
    return {0: g0}


# pullbackKernel = the Laurent pull-back used in sections F-M
for trial in range(4):
    Ls = rand_rule([-1, 0, 1, 3])
    B = rand_mat(2, 2)
    g = {0: rand_sym(2), 2: B, -2: B.T}
    H = pullback(Ls, g)
    for d in range(-8, 9):
        check(is_zero(pullback_kernel(Ls, g, d) - H.get(d, sp.zeros(2))),
              'pullbackKernel (sketch definition) equals the Laurent pull-back')
# rectangular pullbackKernel (dilation_lattice): C maps system (2) to ancilla (2)
Hc = {d: pullback_kernel(C_, {0: gp}, d) for d in range(-4, 5)}
check(all(is_zero(Hc[d] - nuL.get(d, sp.zeros(2))) for d in Hc),
      'rectangular pullbackKernel of S_21 is the lattice dilation noise')
# pullbackKernel_rotation_two, verbatim: (g0 qq * lam^2) . vecMulVec (rotation phi pIdx) (same)
K2 = pullback_kernel(Lrot, on_site(g0), 2)
check(is_zero(sp.simplify(K2 - (a * lam ** 2) * (r.T * r))), 'pullbackKernel_rotation_two')
# rotation_onSite_iff: forward direction on the instance lam = 1/2, a = 1 fails; lam = 0 holds
for lamv, av, holds in ((R(1, 2), 1, False), (0, 1, True), (R(1, 2), 0, True)):
    sub = dict(inst)
    ks = [pullback_kernel({k: v.subs(sub).subs({lam: lamv}) for k, v in Lrot.items()},
                          on_site(g0.subs({a: av, b: 1, c: 0})), x) for x in (-2, -1, 1, 2)]
    check(all(is_zero(k) for k in ks) == holds, 'rotation_onSite_iff instances')
# lossy_example, symbolic in eta (sqrt eta written as t, eta = t^2), phi and lam
t = sp.symbols('t', positive=True)
Lt = {k: t * v for k, v in Lrot.items()}
noise = on_site((1 - t ** 2) * sp.eye(2))
K2l = sp.simplify(pullback_kernel(Lt, noise, 2))
check(is_zero(sp.simplify(K2l - t ** 2 * (1 - t ** 2) * lam ** 2 * (r.T * r))),
      'lossy_example: two-step noise at 2 is eta (1 - eta) lam^2 r r^T')
check(sp.simplify((K2l.trace()) - t ** 2 * (1 - t ** 2) * lam ** 2) == 0,
      'lossy_example: nonzero for 0 < eta < 1 and lam != 0 (trace)')
form = pullback(Lt, const(O1))
check(set(form) == {0} and is_zero(sp.simplify(form[0] - t ** 2 * O1)),
      'lossy_example: symbol form eta Omega, range {0}')
# typeI_II_comp: (N1 - N1) u ((N2 - N2) + N1 - N1) is inside (N1 + N2) - (N1 + N2)
for trial in range(20):
    N1 = set(random.sample(range(-3, 4), random.randint(1, 3)))
    N2 = set(random.sample(range(-3, 4), random.randint(1, 3)))
    diff = lambda X: {x - y for x in X for y in X}
    plus = lambda X, Y: {x + y for x in X for y in Y}
    check(diff(N1) | plus(diff(N2), diff(N1)) <= diff(plus(N1, N2)),
          'typeI_II_comp: support inclusion')
# isChannelMatrix_iff: PSD of nu + i(Omega - G^T Omega G) is PSD of the (X, Y) matrix
for (G, nu) in ((R(3, 5) * sp.eye(2), R(16, 25) * sp.eye(2)),
                (R(3, 5) * sp.eye(2), R(8, 25) * sp.eye(2)),
                (sp.Matrix([[1, R(1, 2)], [0, 1]]), R(1, 3) * sp.eye(2)),
                (sp.Matrix([[2, 0], [0, R(1, 2)]]), sp.zeros(2)),
                (sp.zeros(2), sp.eye(2))):
    X, Y = O1.T * G.T * O1, O1.T * nu * O1
    lhs = is_psd(Y - I * O1 + I * X * O1 * X.T)
    rhs = is_psd(nu + I * (O1 - G.T * O1 * G))
    check(lhs == rhs, 'isChannelMatrix_iff on instances (both truth values occur)')
# exists_isFactorizing_not_isLocalWith: the witness is the shift of section G (checked there)

print(f'check_q5: all {count} exact checks pass.')
