"""
Numerical checks for milestone Q4b: convergence of the
example system's covariance to a stationary one (thesis Prop. 4.7), the limit cells, and the
pointwise convergence of characteristic functions (thesis Thm. 4.9, weak-* part).

Run with python3 (numpy only).

Conventions: those of milestones Q3 and Q4a.
  gamma_hat(k) = sum_x gamma_x e^{-ikx};  Omega = [[0,1],[-1,0]];
  L_hat(k) = Gamma_0 + 2 lam cos k Gamma_pm (real, even in k);
  evolution of cells: gamma'_j = sum_{g,g'} l_g^T gamma_{j+g-g'} l_{g'}, symbol L_hat^T g L_hat;
  theta(k) = arccos(cos phi + lam cos k sin phi);  N(k) = (cos theta 1 - L_hat(k))/sin theta.

Every claim is a floating-point check with tolerance TOL (the claims are about limits and
integrals); algebraic identities are checked at many random points.
"""
import numpy as np

rng = np.random.default_rng(20260928)
TOL = 1e-9
count = 0
OM = np.array([[0.0, 1.0], [-1.0, 0.0]])


def check(cond, msg):
    global count
    assert cond, msg
    count += 1


def Lhat(phi, lam, k):
    c, s = np.cos(phi), np.sin(phi)
    return np.array([[c + 2 * lam * np.cos(k) * s, -s + 2 * lam * np.cos(k) * c], [s, c]])


def theta(phi, lam, k):
    return np.arccos(np.cos(phi) + lam * np.cos(k) * np.sin(phi))


def Nmat(phi, lam, k):
    th = theta(phi, lam, k)
    return (np.cos(th) * np.eye(2) - Lhat(phi, lam, k)) / np.sin(th)


def eps(phi, lam, k):
    return -np.sign(np.sin(phi)) * OM @ Nmat(phi, lam, k)


def regime_point():
    while True:
        phi = rng.uniform(-np.pi, np.pi)
        lam = rng.uniform(-2, 2)
        if abs(np.cos(phi)) + abs(lam * np.sin(phi)) < 0.95 and abs(lam * np.sin(phi)) > 0.05:
            return phi, lam


# 1. Real form of the powers: L^t = cos(t th) 1 - sin(t th) N.
for _ in range(40):
    phi, lam = regime_point()
    k = rng.uniform(-np.pi, np.pi)
    L, N, th = Lhat(phi, lam, k), Nmat(phi, lam, k), theta(phi, lam, k)
    check(np.allclose(N @ N, -np.eye(2), atol=TOL), "N^2 = -1")
    P = np.eye(2)
    for t in range(0, 25):
        check(np.allclose(P, np.cos(t * th) * np.eye(2) - np.sin(t * th) * N, atol=1e-8),
              f"power formula t={t}")
        P = P @ L

# 2. Quadratic split: (L^t)^T A L^t = C + cos(2 t th) Ac + sin(2 t th) As, for any complex A,
#    with C = (A + N^T A N)/2, Ac = (A - N^T A N)/2, As = -(N^T A + A N)/2.
for _ in range(40):
    phi, lam = regime_point()
    k = rng.uniform(-np.pi, np.pi)
    L, N, th = Lhat(phi, lam, k), Nmat(phi, lam, k), theta(phi, lam, k)
    A = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
    C = (A + N.T @ A @ N) / 2
    Ac = (A - N.T @ A @ N) / 2
    As = -(N.T @ A + A @ N) / 2
    for t in range(0, 15):
        Lt = np.linalg.matrix_power(L, t)
        check(np.allclose(Lt.T @ A @ Lt, C + np.cos(2 * t * th) * Ac + np.sin(2 * t * th) * As,
                          atol=1e-8), f"quadratic split t={t}")
    # C is invariant under the step, for every A
    check(np.allclose(L.T @ C @ L, C, atol=1e-9), "C invariant")

# 3. For real symmetric A (reflection-symmetric cells), C = g * eps with g = -(1/2) tr(Om eps Om C),
#    and g >= 1 whenever A + i Om >= 0 (the limit satisfies the state condition).
for _ in range(60):
    phi, lam = regime_point()
    k = rng.uniform(-np.pi, np.pi)
    N, E = Nmat(phi, lam, k), eps(phi, lam, k)
    # random admissible one-mode covariance: S S^T with S symplectic times (nu >= 1)
    a = rng.uniform(-1, 1)
    S = np.array([[np.exp(a), rng.normal()], [0, np.exp(-a)]])
    nu = rng.uniform(1, 3)
    A = nu * S @ S.T
    C = (A + N.T @ A @ N) / 2
    g = -0.5 * np.trace(OM @ E @ OM @ C)
    check(np.allclose(C, g * E, atol=1e-9), "limit symbol is g eps")
    check(g >= 1 - 1e-12, "g >= 1 for admissible A")
    check(np.min(np.linalg.eigvalsh(A + 1j * OM)) > -1e-9, "A + i Om >= 0 (input)")

# 4. Convergence of cells for the vacuum at the thesis's parameters (lam = 0.4, phi = pi/4).
phi, lam = np.pi / 4, 0.4
l0 = np.array([[np.cos(phi), -np.sin(phi)], [np.sin(phi), np.cos(phi)]])
lpm = lam * np.array([[np.sin(phi), np.cos(phi)], [0.0, 0.0]])
coef = {-1: lpm, 0: l0, 1: lpm}
T = 800
R = T + 3
OFF = 2 * R
arr0 = np.zeros((2 * OFF + 1, 2, 2))
arr0[OFF] = np.eye(2)


class Cells:
    def __init__(self, arr):
        self.arr = arr

    def __getitem__(self, x):
        return self.arr[x + OFF]


cells = Cells(arr0)


def step(c):
    a = c.arr
    out = np.zeros_like(a)
    for g, lg in coef.items():
        for g2, lg2 in coef.items():
            d = g - g2
            src = np.roll(a, -d, axis=0)
            out += np.einsum('ji,njk,kl->nil', lg, src, lg2)
    return Cells(out)


def limit_cell(x, M=20000):
    ks = np.linspace(-np.pi, np.pi, M, endpoint=False)
    th = theta(phi, lam, ks)
    L = np.stack([Lhat(phi, lam, k) for k in ks])
    N = (np.cos(th)[:, None, None] * np.eye(2) - L) / np.sin(th)[:, None, None]
    C = (np.eye(2) + np.einsum('nji,njk->nik', N, N)) / 2
    return (np.exp(1j * ks * x)[:, None, None] * C).mean(axis=0).real


cur = cells
errs = {}
for t in range(1, T + 1):
    cur = step(cur)
    if t in (50, 200, 800):
        errs[t] = max(np.abs(cur[x] - limit_cell(x)).max() for x in (0, 1, 2))
check(errs[800] < errs[200] < errs[50], f"cells converge monotonically at samples {errs}")
check(errs[800] < 0.05, f"gamma_800 close to gamma_infty: {errs[800]}")
# decay at least like t^{-1/2} (stationary points at k = 0, pi); observed ratio ~0.27 (about t^{-1})
check(errs[800] / errs[200] < 0.75, f"decay rate: {errs[800] / errs[200]}")
# the limit's symbol is g eps with g >= 1 (Thm 4.8 form)
for k in np.linspace(-np.pi, np.pi, 41):
    N, E = Nmat(phi, lam, k), eps(phi, lam, k)
    C = (np.eye(2) + N.T @ N) / 2
    g = -0.5 * np.trace(OM @ E @ OM @ C)
    check(np.allclose(C, g * E, atol=1e-9) and g >= 1, "vacuum limit is g eps, g >= 1")

# 5. F1: at lam = 0 a squeezed product state does not converge (periodic in t).
phi0 = np.pi / 3
l00 = np.array([[np.cos(phi0), -np.sin(phi0)], [np.sin(phi0), np.cos(phi0)]])
A = np.diag([2.0, 0.5])
vals = []
M = np.eye(2)
for t in range(0, 13):
    vals.append((M.T @ A @ M)[0, 0])
    M = M @ l00
check(abs(vals[3] - vals[0]) < 1e-12 and abs(vals[1] - vals[0]) > 0.1,
      "lam = 0: gamma_t(0) periodic (period 3 in the 2x2 quadratic form), not convergent")

# 6. Riemann-Lebesgue by change of variables on [0, pi]:
#    int_0^pi h(k) e^{2 i t theta(k)} dk = int_{theta(0)}^{theta(pi)} h(k(u)) / theta'(k(u)) e^{2itu} du,
#    and int |h~| du = int |h| dk (the endpoint singularity of 1/theta' is integrable).
phi, lam = np.pi / 4, 0.4
h = lambda k: np.cos(k) ** 2 + 0.3 * np.sin(3 * k) + 1.0
ks = np.linspace(0, np.pi, 400001)
th = theta(phi, lam, ks)
dth = lam * np.sin(phi) * np.sin(ks) / np.sin(th)
check(np.all(np.diff(th) > 0), "theta increasing on [0, pi] for lam sin phi > 0")
check(np.all(dth[1:-1] > 0), "theta' > 0 on (0, pi)")
lhs_abs = np.trapezoid(np.abs(h(ks)), ks)
# in the u variable, |h~| du = |h| / theta' * theta' dk; compare with an integral in u
us = th
ht = np.abs(h(ks[1:-1])) / dth[1:-1]
rhs_abs = np.trapezoid(ht, us[1:-1])
check(abs(lhs_abs - rhs_abs) < 5e-3, f"int |h~| du = int |h| dk: {lhs_abs} vs {rhs_abs}")
prev = None
for t in (100, 1000, 10000):
    val = abs(np.trapezoid(h(ks) * np.exp(2j * t * th), ks))
    check(val < 0.25 * lhs_abs, f"oscillatory integral small at t={t}: {val}")
    if prev is not None:
        check(val < prev, f"oscillatory integral decreasing: t={t}")
    prev = val

# 7. Characteristic functions: chi_t(u) = exp(-1/4 sum u(x)^T gamma_t(x-y) u(y)) converges for a
#    finitely supported u (here supported on {0, 1}).
phi, lam = np.pi / 4, 0.4
u = {0: np.array([0.7, -0.2]), 1: np.array([0.1, 0.5])}


def chi(cells_):
    q = sum(u[x] @ cells_[x - y] @ u[y] for x in u for y in u)
    return np.exp(-q / 4)


cur = cells
chis = {}
lim = {x: limit_cell(x) for x in (-1, 0, 1)}
chi_inf = chi(lim)
for t in range(1, 801):
    cur = step(cur)
    if t in (50, 800):
        chis[t] = abs(chi(cur) - chi_inf)
check(chis[800] < chis[50] and chis[800] < 5e-3, f"chi_t -> chi_infty: {chis}")

# 8. F6: a translation-invariant displacement delta rotates, d_t(e_x) = (L_hat(0)^t)^T delta.
L0 = Lhat(phi, lam, 0.0)
delta = np.array([1.0, 0.0])
ds = [np.linalg.matrix_power(L0, t).T @ delta for t in range(0, 60)]
check(max(abs(d[0] - ds[0][0]) for d in ds[1:]) > 0.5, "displacement does not converge")

# 9. Sketch statements limitSymbol_add_posSemidef, limitCells_real, limitCells_symm, checked on a
#    non-reflection-symmetric admissible input: gamma_0 = 2*1, gamma_{+-1} = +-(1/2) Omega-type
#    antisymmetric cells (symbol 2*1 + i sin k * Omega-ish), plus a symmetric neighbour coupling.
phi, lam = 1.1, 0.3
g1 = np.array([[0.1, -0.5], [0.5, 0.2]])            # gamma_1 (not symmetric)
cellsA = {0: 3.0 * np.eye(2), 1: g1, -1: g1.T}       # gamma_{-x} = gamma_x^T
def ghat(k):
    return sum(cellsA[x] * np.exp(-1j * k * x) for x in cellsA)
ks = np.linspace(-np.pi, np.pi, 4000, endpoint=False)
for k in ks[::97]:
    G = ghat(k)
    check(np.allclose(G, G.conj().T), "input symbol Hermitian")
    check(np.min(np.linalg.eigvalsh(G + 1j * OM)) > -1e-12, "input satisfies Fourier criterion")
    N = Nmat(phi, lam, k)
    C = (G + N.T @ G @ N) / 2
    check(np.min(np.linalg.eigvalsh(C + 1j * OM)) > -1e-9, "limit symbol satisfies the criterion")
def limA(x):
    acc = np.zeros((2, 2), dtype=complex)
    for k in ks:
        N = Nmat(phi, lam, k)
        G = ghat(k)
        acc += np.exp(1j * k * x) * (G + N.T @ G @ N) / 2
    return acc / len(ks)
for x in (0, 1, 2, 3):
    Lx, Lmx = limA(x), limA(-x)
    check(np.abs(Lx.imag).max() < 1e-9, f"limit cell {x} real")
    check(np.allclose(Lmx.real, Lx.real.T, atol=1e-9), f"limit cells symmetric at {x}")

# Notes, Example "The vacuum in the running example": at phi = pi/2 the vacuum's limit symbol is
# eta * epsHat with eta = (1 - lam^2 cos^2 k)^(-1/2), and the limit cells decay exponentially.
for lam in (0.3, 0.6, -0.8):
    for k in np.linspace(-np.pi, np.pi, 13):
        c = np.cos(k)
        L = np.array([[2 * lam * c, -1.0], [1.0, 0.0]])
        s_ = np.sqrt(1 - lam ** 2 * c ** 2)
        N = (lam * c * np.eye(2) - L) / s_
        check(np.allclose(N, np.array([[-lam * c, 1], [-1, lam * c]]) / s_), "vacuum example N")
        C = (np.eye(2) + N.T @ N) / 2
        eps = np.array([[1, -lam * c], [-lam * c, 1]]) / s_
        check(np.allclose(C, eps / s_), "vacuum example C = eta epsHat")
        check(1 / s_ >= 1 - 1e-12, "vacuum example eta >= 1")
    kk = np.linspace(-np.pi, np.pi, 4096, endpoint=False)
    c11 = [abs(np.mean(np.exp(1j * kk * x) / (1 - lam ** 2 * np.cos(kk) ** 2))) for x in (0, 4, 8, 16)]
    check(c11[3] < c11[2] < c11[1] and c11[3] < 1e-2 * c11[0], "vacuum limit cells decay")
print(f"check_q4b: {count} checks passed")
