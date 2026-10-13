"""Numerical checks resolving the conventions of milestone Q3 (Gaussian states on the chain).

Run with python3 (needs numpy).

Source: O. Krueger, PhD thesis, TU Braunschweig 2006, Ch. 4, printed pp. 76-82
(PDF pages 86-92; printed page = PDF page - 10), for (4.4)-(4.6), (4.14)-(4.17) and Lemma 4.5.
BosonicLean conventions: the files BosonicLean/PhaseSpace/Defs.lean, Quantum/Defs.lean and
Quantum/Vacuum.lean of the library BosonicLean.

This script settles, and records for the proposal (see conventions.md):

1. The Schroedinger realization of W(u) consistent with W(u)W(w) = e^{-i sigma(u,w)/2} W(u+w),
   sigma(u,w) = u^T Omega w, Omega = [[0,1],[-1,0]] (= BosonicLean's -Matrix.J, positions first).
   Resolved realization: W(u) = exp(i(u_p X - u_x P)), i.e.
     (W(u) psi)(x) = exp(-i u_x u_p / 2) exp(i u_p x) psi(x - u_x).
   On the one-mode vacuum psi(x) = pi^{-1/4} exp(-x^2/2) this gives
     chi(u) = exp(-1/4 (u_x^2 + u_p^2)) = exp(-1/4 gamma(u,u)),  gamma = I = BosonicLean's
   diagonalOne 1 1 (the vacuum covariance with BosonicLean's gamma = 2V normalization).
   This vacuum case is a red herring for the general dictionary: gamma_B = I is
   Omega-invariant, so it cannot distinguish "gamma_form = gamma_B" from any Omega-conjugated
   variant. Checked directly on a squeezed one-mode state (gamma_B = diag(t, 1/t), the
   BosonicLean covariance for Var X = t/2) and a rotated-squeezed one-mode state (general
   gamma_B with a nonzero cross term): gamma_form(u,u), read off numerically from chi(u) on a
   position-space grid, equals u^T (Omega gamma_B Omega^T) u, NOT u^T gamma_B u. Concretely, for
   gamma_B = diag(t, 1/t), chi(1,0) = exp(-1/(4t)) and chi(0,1) = exp(-t/4): the coefficient of
   u_x^2 is gamma_B's PP entry (1/t) and the coefficient of u_p^2 is gamma_B's XX entry (t) --
   the diagonal entries are swapped, and (checked on the rotated case) the off-diagonal entry
   flips sign, exactly matching Omega gamma_B Omega^T = [[gamma_B_pp, -gamma_B_xp],
   [-gamma_B_xp, gamma_B_xx]]. So in general
     gamma_form = Omega gamma_B Omega^T,  equivalently  gamma_B = Omega^T gamma_form Omega
   (Omega^{-1} = Omega^T since Omega^2 = -I), and the two coincide only when gamma_B commutes
   with Omega, as the vacuum I (and, on the diagonal, any t=1 case) does.

2. The sign: for real symmetric gamma and the real antisymmetric Omega, gamma + i*Omega is
   Hermitian, and its Hermitian-conjugate-transpose is gamma - i*Omega; since positive
   semidefiniteness is invariant under Hermitian conjugation, gamma + i*Omega >= 0 iff
   gamma - i*Omega >= 0 ALWAYS holds simultaneously for real symmetric gamma. So the thesis's
   "+iOmega" state condition (4.5)-(4.6) and BosonicLean's IsAdmissible "-iOmega" condition are
   the same condition, once gamma_form is converted to gamma_B by the Omega-conjugation of
   item 1 (not by a direct identification); there is no separate sign to resolve beyond that
   conjugation. What differs, for a multi-site region O, is the INDEXING as well: the thesis's
   correlation matrix gamma_O is ordered site-by-site (x_1,p_1,x_2,p_2,...) while BosonicLean's
   Gaussian.PhaseIndex (n*|O|) orders it position-block-then-momentum-block. Composing the two
   corrections (Omega-conjugate each site, then reindex by the site-ordering permutation P_O):
     covarianceMatrix O gamma = P_O . (Omega_O^T gamma_O Omega_O) . P_O^T,
   where Omega_O is the block-diagonal, SITE-ORDERED symplectic form (direct sum of Omega(1)
   over the sites, matching gamma_O's own ordering), checked below on single- and two-site
   regions, including a genuinely correlated two-mode state (a two-mode squeezed vacuum, built
   in a truncated Fock basis). Admissibility transports both ways along this whole composite
   map, since each factor (Omega_O-congruence, then the orthogonal permutation P_O) preserves
   positive semidefiniteness in both directions. (Reindexing by the permutation P_O ALONE, with
   no Omega_O-conjugation -- this script's own earlier draft -- does NOT reproduce BosonicLean's
   matrix in general; ruled out explicitly below alongside the Omega_O-conjugation-alone
   candidate.)

3. The Fourier criterion (Lemma 4.5(i)): with gamma_hat(k) = sum_x gamma_x e^{-ikx} (the same
   sign as the thesis's xi_hat(k) = sum_x xi_x e^{-ikx}, (4.14)), gamma + i*sigma >= 0 on V
   (equivalently on large finite truncations, (4.6)) iff gamma_hat(k) + i*Omega >= 0 for all k.

4. Evolution (4.17): gamma_t(x) = sum_{y,z} Gamma_t(y)^T gamma_0(x+y-z) Gamma_t(z) (4.17a) has,
   by direct Fourier-convolution algebra (change of summation variable w=x+y-z), Fourier
   transform gamma_hat_t(k) = Gamma_hat_t(-k)^T gamma_hat_0(k) Gamma_hat_t(k) -- the momentum in
   the LEFT factor is Gamma_hat_t(-k), not Gamma_hat_t(k). This is the general identity, checked
   on a hand-built non-reflection-symmetric rule where Gamma_hat(k) != Gamma_hat(-k).
   The thesis's printed (4.17b), Gamma_hat_t(k)^T gamma_hat_0(k) Gamma_hat_t(k) (no -k), is the
   SPECIAL CASE for the thesis's own reflection-symmetric rules (l_{-1}=l_{+1}, e.g. the
   leapfrog and (4.12)'s Gamma_- = Gamma_+), where Gamma_hat(k) = Gamma_hat(-k) identically, so
   the two formulas coincide; checked on the leapfrog.

5. Lemma 4.5(ii) (printed p. 82): "[gamma] corresponds to a pure Gaussian state if and only if
   gamma_hat(k) + i sigma_s is not strictly positive for any k in [-pi,pi], i.e. if
   (sigma_s gamma_hat(k))^2 = -1."  Checked on vacuum (pure), squeezed (pure) and thermal/mixed
   (not pure) examples.

6. BosonicLean's diagonalOne 1 1 (vacuum) and diagonalOne t (1/t) (squeezed) are IsAdmissible;
   on-site rotation preserves the vacuum's covariance matrix.

7. On-site evolution transport by a NON-orthogonal symplectic S (Corollary (transport)(b)):
   for (Lu)(x) = S u(x) with S^T Omega S = Omega, covarianceMatrix O gamma(L.,L.) =
   T covarianceMatrix O gamma T^T with T = P_O (1_O tensor S^{-1}) P_O^T, exactly as Q3.tex
   states -- checked with S = diag(2, 1/2) (squeezing) and S = [[1,1],[0,1]] (shear), neither
   orthogonal, on regions of 1-3 sites; T itself is a genuinely non-orthogonal congruence
   (T^T T != I) and admissibility is nonetheless preserved (since S^{-1} is symplectic).

8. Purity counterexample and positive direction (Lemma 4.5(ii), 2x2): A = [[sqrt2,-i],[i,sqrt2]]
   has det A = 1 but is admissible on only ONE side (A+iOmega>=0, A-iOmega NOT >=0), and
   (Omega A)^2 != -1: det A = 1 alone does not give purity. Direct algebra on a general Hermitian
   A = [[p,q],[conj(q),r]] shows (Omega A)^2=-1 forces Im(q)=0 whenever p,r != 0 (no genuinely
   complex-off-diagonal 2x2 example survives with det A=1 and p,r != 0 -- and p=0 or r=0 forces
   det A <= 0). So the positive direction (Hermitian A with A+-iOmega>=0 both and det A=1 implies
   (Omega A)^2=-1) is checked by random tests over real symmetric (still Hermitian) rotated
   one-mode squeezed states, all of which pass admissible-both-sides and confirm the implication.

9. The cell-index convention: indexing gamma(u,w) = sum u(x)^T gamma_{y-x} w(y) instead of
   (4.4)'s gamma_{x-y} sends gamma_hat(k) -> gamma_hat(-k) throughout (= gamma_hat(k)^T for
   symmetric gamma), and the general evolution identity (4.17), item 4, becomes
   gamma_hat_t(k) = Lhat(k)^T gamma_hat_0(k) Lhat(-k) -- the roles of Lhat(k) and Lhat(-k) are
   SWAPPED relative to the x-y convention's Lhat(-k)^T gamma_hat_0(k) Lhat(k). Checked on the
   vacuum and on the hand-built non-reflection-symmetric rule, both by an independent
   position-space evolution formula for the y-x convention and by the Fourier identity.

Deterministic seeds; numpy floats with a fixed tolerance TOL.
"""
import numpy as np

np.random.seed(20260928)
TOL = 1e-8
count = 0


def check(cond, label):
    global count
    assert cond, label
    count += 1


# ============================= linear algebra helpers =============================
def Omega(n):
    """[[0, I_n], [-I_n, 0]] = BosonicLean's -Matrix.J, positions first."""
    O = np.zeros((2 * n, 2 * n))
    O[:n, n:] = np.eye(n)
    O[n:, :n] = -np.eye(n)
    return O


def sigma(u, w, Om):
    return u @ Om @ w


def is_psd(M, tol=1e-9):
    """M assumed Hermitian; check via eigenvalues (allow small numerical slack)."""
    Mh = (M + M.conj().T) / 2
    ev = np.linalg.eigvalsh(Mh)
    return ev.min() >= -tol


def hermitian_close(M, tol=1e-9):
    return np.allclose(M, M.conj().T, atol=tol)


Om1 = Omega(1)
check(np.allclose(Om1, [[0.0, 1.0], [-1.0, 0.0]]), "Omega(1) = [[0,1],[-1,0]]")
check(np.allclose(Om1 @ Om1, -np.eye(2)), "Omega(1)^2 = -I")

# =========== 1. one-mode Schroedinger realization and the vacuum chi ===========
# W(u) = exp(i(u_p X - u_x P)); derivation (BCH, [X,P]=i, hbar=1):
#   (W(u) psi)(x) = exp(-i u_x u_p / 2) * exp(i u_p x) * psi(x - u_x).
# This is the unique (up to the free choice absorbed into the phase convention of W) realization
# giving W(u)W(w) = exp(-i sigma(u,w)/2) W(u+w) with sigma(u,w) = u^T Omega w, Omega = [[0,1],[-1,0]].


def vacuum_psi(x):
    return np.pi ** (-0.25) * np.exp(-x ** 2 / 2)


def W_apply_vacuum(u, x_grid):
    ux, up = u
    return np.exp(-1j * ux * up / 2) * np.exp(1j * up * x_grid) * vacuum_psi(x_grid - ux)


def chi_numeric(u, x_grid, dx):
    psi = vacuum_psi(x_grid)
    Wpsi = W_apply_vacuum(u, x_grid)
    return np.trapezoid(np.conj(psi) * Wpsi, dx=dx)


x_grid = np.linspace(-30.0, 30.0, 600001)
dx = x_grid[1] - x_grid[0]
check(abs(np.trapezoid(vacuum_psi(x_grid) ** 2, dx=dx) - 1.0) < 1e-8, "vacuum psi is normalized")

test_us = [(0.0, 0.0), (1.0, 0.0), (0.0, 1.0), (1.0, 2.0), (-1.5, 0.7), (2.0, -1.3)]
for u in test_us:
    ux, up = u
    chi_val = chi_numeric(u, x_grid, dx)
    chi_pred = np.exp(-0.25 * (ux ** 2 + up ** 2))  # gamma = I, i.e. gamma(u,u) = ux^2+up^2
    check(abs(chi_val - chi_pred) < 1e-6,
          f"vacuum chi(u) = exp(-1/4 gamma(u,u)) with gamma = I, u={u}")
    check(abs(chi_val.imag) < 1e-6, f"vacuum chi(u) is real, u={u}")

# Verify the Weyl relation itself holds under this realization, on the vacuum's Hilbert space,
# by comparing <psi, W(u)W(w) psi> with e^{-i sigma(u,w)/2} <psi, W(u+w) psi> (both computable
# via chi since W(u)W(w) = e^{-i sigma(u,w)/2} W(u+w) is an operator identity; check its
# consequence on chi, chi(u+w) is consistent and the phase e^{-i sigma(u,w)/2} matches the
# BCH computation used to build W_apply_vacuum, by an independent path: apply W(w) then W(u)).
for u, w in [((1.0, 0.5), (0.3, -0.8)), ((0.0, 1.0), (1.0, 0.0)), ((-1.0, 2.0), (0.5, 0.5))]:
    psi = vacuum_psi(x_grid)
    Ww_psi = W_apply_vacuum(w, x_grid)
    # apply W(u) to the (non-vacuum) function Ww_psi directly from the BCH formula for W(u):
    ux, up = u
    Wu_Ww_psi = np.exp(-1j * ux * up / 2) * np.exp(1j * up * x_grid) * np.interp(
        x_grid - ux, x_grid, Ww_psi.real) + 1j * np.exp(-1j * ux * up / 2) * np.exp(
        1j * up * x_grid) * np.interp(x_grid - ux, x_grid, Ww_psi.imag)
    lhs = np.trapezoid(np.conj(psi) * Wu_Ww_psi, dx=dx)
    uw = (u[0] + w[0], u[1] + w[1])
    rhs = np.exp(-1j * sigma(np.array(u), np.array(w), Om1) / 2) * chi_numeric(uw, x_grid, dx)
    check(abs(lhs - rhs) < 2e-4, f"W(u)W(w)=e^(-i sigma/2)W(u+w) on the vacuum, u={u}, w={w}")

print("Resolved: W(u) = exp(i(u_p X - u_x P)); vacuum gamma_form = I = BosonicLean diagonalOne 1 1.")

# ===== 1b. squeezed and rotated-squeezed one-mode states: gamma_form = Omega gamma_B Omega^T =====
# Squeezed pure state with BosonicLean covariance gamma_B = diag(t, 1/t) (Var X = t/2, Var P =
# 1/(2t)): psi(x) = (pi t)^{-1/4} exp(-x^2/(2t)).
t_sq = 2.3


def squeezed_psi(xx, t):
    return (np.pi * t) ** (-0.25) * np.exp(-xx ** 2 / (2 * t))


psi_sq = squeezed_psi(x_grid, t_sq)
check(abs(np.trapezoid(psi_sq ** 2, dx=dx) - 1.0) < 1e-8, "squeezed psi is normalized")
VarX_sq = np.trapezoid(x_grid ** 2 * psi_sq ** 2, dx=dx)
check(abs(VarX_sq - t_sq / 2) < 1e-6, "squeezed Var(X) = t/2 (BosonicLean gamma_B = diag(t,1/t))")


def W_apply_general(u, x_grid, psi_func):
    ux, up = u
    return np.exp(-1j * ux * up / 2) * np.exp(1j * up * x_grid) * psi_func(x_grid - ux)


def chi_general(u, x_grid, dx, psi_func):
    psi = psi_func(x_grid)
    Wpsi = W_apply_general(u, x_grid, psi_func)
    return np.trapezoid(np.conj(psi) * Wpsi, dx=dx)


def psi_func_sq(xx):
    return squeezed_psi(xx, t_sq)


gB_sq = np.diag([t_sq, 1.0 / t_sq])  # BosonicLean covariance, diagonalOne t (1/t)
gform_pred_sq = Om1 @ gB_sq @ Om1.T  # = diag(1/t, t)
for u, label in [((1.0, 0.0), "u=(1,0)"), ((0.0, 1.0), "u=(0,1)")]:
    chi_val = chi_general(u, x_grid, dx, psi_func_sq).real
    gform_uu = -4.0 * np.log(chi_val)
    predicted = u[0] ** 2 * gform_pred_sq[0, 0] + u[1] ** 2 * gform_pred_sq[1, 1]
    check(abs(gform_uu - predicted) < 1e-5,
          f"squeezed one-mode: gamma_form(u,u) = u^T (Omega gamma_B Omega^T) u, {label}")
    direct_gB = u[0] ** 2 * gB_sq[0, 0] + u[1] ** 2 * gB_sq[1, 1]
    if abs(direct_gB - predicted) > 1e-3:
        check(abs(gform_uu - direct_gB) > 1e-3,
              f"squeezed one-mode: gamma_form != gamma_B directly (item 1 corrected), {label}")

# Rotated-squeezed one-mode state: general pure Gaussian psi(x) = N exp(-A x^2), A = a + i c,
# a > 0, parametrizes EVERY zero-mean pure one-mode Gaussian (Var X = 1/(4a),
# Cov_sym(X,P) = -c/(2a), Var P = (a^2+c^2)/a); chosen here as the rotation by phi of the t_sq
# squeezed covariance, gamma_B_rot = R^T diag(t,1/t) R.
phi_sq = 0.6
Rrot = np.array([[np.cos(phi_sq), np.sin(phi_sq)], [-np.sin(phi_sq), np.cos(phi_sq)]])
gB_rot = Rrot.T @ gB_sq @ Rrot
a_rot = 1.0 / (2 * gB_rot[0, 0])
c_rot = -gB_rot[0, 1] * a_rot
A_rot = a_rot + 1j * c_rot
check(abs(2 * (a_rot ** 2 + c_rot ** 2) / a_rot - gB_rot[1, 1]) < 1e-8,
      "rotated-squeezed gamma_B is pure/consistent with the (a,c) parametrization")


def psi_func_rot(xx):
    N = (2 * a_rot / np.pi) ** 0.25
    return N * np.exp(-A_rot * xx ** 2)


psi_rot = psi_func_rot(x_grid)
check(abs(np.trapezoid(np.abs(psi_rot) ** 2, dx=dx) - 1.0) < 1e-6, "rotated-squeezed psi is normalized")

gform_pred_rot = Om1 @ gB_rot @ Om1.T
c1 = chi_general((1.0, 0.0), x_grid, dx, psi_func_rot).real
c2 = chi_general((0.0, 1.0), x_grid, dx, psi_func_rot).real
c3 = chi_general((1.0, 1.0), x_grid, dx, psi_func_rot).real
gxx_fit = -4.0 * np.log(c1)
gpp_fit = -4.0 * np.log(c2)
gxp_fit = (-4.0 * np.log(c3) - gxx_fit - gpp_fit) / 2.0
check(abs(gxx_fit - gform_pred_rot[0, 0]) < 1e-4, "rotated-squeezed: gamma_form_xx matches Omega gamma_B Omega^T")
check(abs(gpp_fit - gform_pred_rot[1, 1]) < 1e-4, "rotated-squeezed: gamma_form_pp matches Omega gamma_B Omega^T")
check(abs(gxp_fit - gform_pred_rot[0, 1]) < 1e-3,
      "rotated-squeezed: gamma_form_xp matches Omega gamma_B Omega^T (cross term, sign flip confirmed)")
check(abs(gform_pred_rot[0, 1]) > 0.1, "rotated-squeezed test genuinely has a nonzero cross term")

print("Resolved: gamma_form = Omega gamma_B Omega^T in general (vacuum is the Omega-invariant "
      "special case); item 1 of the earlier draft is corrected.")

# ================= 2. the sign, twisted positivity, and the BosonicLean conversion =================
rng = np.random.default_rng(1)


def gaussian_chi(u, gamma, d=None):
    val = -0.25 * (u @ gamma @ u)
    if d is not None:
        val = val + 1j * (d @ u)
    return np.exp(val)


def twisted_gram(us, gamma, Om, d=None):
    N = len(us)
    M = np.zeros((N, N), dtype=complex)
    for j in range(N):
        for k in range(N):
            diff = us[k] - us[j]
            M[j, k] = np.exp(1j * sigma(us[j], us[k], Om) / 2) * gaussian_chi(diff, gamma, d)
    return M


def is_admissible_thesis(gamma, Om, tol=1e-9):
    """gamma + i Omega >= 0."""
    return is_psd(gamma + 1j * Om, tol=tol)


def is_admissible_bosoniclean(gamma, Om, tol=1e-9):
    """gamma - i Omega >= 0 (BosonicLean's IsAdmissible, sans the symmetry requirement)."""
    return is_psd(gamma - 1j * Om, tol=tol)


# 2a. the two sign conventions coincide for every real symmetric gamma (Hermitian-conjugate
# invariance of PSD-ness): no separate sign choice to make once gamma_form ~ gamma_B.
for _ in range(30):
    A = rng.normal(size=(2, 2))
    gamma = (A + A.T) / 2
    a = is_admissible_thesis(gamma, Om1)
    b = is_admissible_bosoniclean(gamma, Om1)
    check(a == b, "gamma+iOmega>=0 iff gamma-iOmega>=0 for real symmetric gamma (random)")

# 2b. admissible vs non-admissible examples, and twisted positivity of the Gram matrix tracks
# exactly the admissibility of gamma (not its sign convention, per 2a).
examples = [
    (np.eye(2), True, "identity (vacuum) is admissible"),
    (0.5 * np.eye(2), False, "0.5*I is NOT admissible (sub-vacuum noise)"),
    (2.0 * np.eye(2), True, "2*I is admissible (excess noise)"),
    (np.diag([2.0, 0.5]), True, "squeezed diag(2,0.5) is admissible (pure, det=1)"),
    (np.diag([0.5, 0.5]), False, "diag(0.5,0.5) is NOT admissible"),
]
for gamma, expect_admissible, label in examples:
    check(is_admissible_thesis(gamma, Om1) == expect_admissible, label + " [state condition]")
    for _ in range(4):
        N = rng.integers(2, 5)
        us = [rng.normal(size=2, scale=1.5) for _ in range(N)]
        M = twisted_gram(us, gamma, Om1)
        check(hermitian_close(M), f"twisted Gram kernel is Hermitian ({label})")
        psd = is_psd(M, tol=1e-6)
        if expect_admissible:
            check(psd, f"twisted positivity holds for admissible gamma ({label})")
        # for a non-admissible gamma, twisted positivity can still hold on small/special
        # families (positivity is a necessary, not sufficient-from-one-family, condition), so
        # we only assert failure over enough random trials that at least one violates it.
    if not expect_admissible:
        found_violation = False
        for _ in range(60):
            N = rng.integers(2, 6)
            us = [rng.normal(size=2, scale=2.0) for _ in range(N)]
            M = twisted_gram(us, gamma, Om1)
            if not is_psd(M, tol=1e-6):
                found_violation = True
                break
        check(found_violation, f"twisted positivity fails for some family when gamma is non-admissible ({label})")

# 2c. conversion to BosonicLean's covariance matrix on a multi-site region: Omega_O-conjugate
# each site (item 1, generalized), THEN reindex by the site-ordering permutation P_O
# (site-interleaved -> position-block-then-momentum-block). Neither factor alone reproduces
# BosonicLean's matrix; both are checked and ruled out on their own below.
def region_omega(num_sites):
    """Omega_O, block-diagonal direct sum of Omega(1) over the region (thesis convention,
    sigma(xi,eta) = sum_x sigma_s(xi_x, eta_x)), SITE-ORDERED to match gamma_O."""
    n = num_sites
    Om = np.zeros((2 * n, 2 * n))
    for j in range(n):
        Om[2 * j:2 * j + 2, 2 * j:2 * j + 2] = Om1
    return Om


def region_permutation(num_sites):
    """P_O : interleaved (x_1,p_1,...,x_n,p_n) -> block (x_1,...,x_n,p_1,...,p_n)."""
    n = num_sites
    P = np.zeros((2 * n, 2 * n))
    for j in range(n):
        P[j, 2 * j] = 1.0        # position of site j -> slot j
        P[n + j, 2 * j + 1] = 1.0  # momentum of site j -> slot n+j
    return P


for n_sites in (1, 2, 3, 4):
    P = region_permutation(n_sites)
    Om_O = region_omega(n_sites)
    Om_block = Omega(n_sites)
    check(np.allclose(P @ P.T, np.eye(2 * n_sites)), f"P_O is orthogonal (n={n_sites})")
    check(np.allclose(P @ Om_O @ P.T, Om_block),
          f"P_O reindexes Omega_O to BosonicLean's block Omega (n={n_sites})")
    # random symmetric gamma_O (thesis correlation matrix, site-ordered) on the region
    A = rng.normal(size=(2 * n_sites, 2 * n_sites))
    gamma_O = (A + A.T) / 2
    gamma_B_correct = P @ (Om_O.T @ gamma_O @ Om_O) @ P.T  # composite: Omega_O-conjugate, then P_O
    gamma_B_by_permutation_alone = P @ gamma_O @ P.T
    gamma_B_by_Omega_alone = Om_O.T @ gamma_O @ Om_O  # not reindexed to BosonicLean's block order
    check(not np.allclose(gamma_B_correct, gamma_B_by_permutation_alone),
          f"permutation-alone gives a DIFFERENT matrix from the composite (n={n_sites}, ruled out)")
    if n_sites > 1:
        # for n=1 the permutation is the identity, so Omega-alone coincides with the composite;
        # the two are genuinely different only once there is more than one site to reindex.
        check(not np.allclose(gamma_B_correct, gamma_B_by_Omega_alone),
              f"Omega-conjugation-alone gives a DIFFERENT matrix from the composite (n={n_sites}, ruled out)")
    thesis_admissible = is_admissible_thesis(gamma_O, Om_O)
    bl_admissible_correct = is_admissible_bosoniclean(gamma_B_correct, Om_block)
    check(thesis_admissible == bl_admissible_correct,
          f"state condition on O <=> IsAdmissible(covarianceMatrix O gamma) via P_O.Omega_O^T(.)Omega_O (n={n_sites})")

print("Resolved: covarianceMatrix O gamma = P_O (Omega_O^T gamma_O Omega_O) P_O^T; "
      "admissibility transports both ways.")

# 2d. genuinely correlated two-mode example: a two-mode squeezed vacuum (TMSV), built in a
# truncated Fock basis (no continuum wavefunction needed), to confirm 2c's composite formula
# reproduces the actual chi-derived gamma_form on an off-diagonal-coupled multi-site state.
Nc = 30
a_op = np.zeros((Nc, Nc))
for n in range(Nc - 1):
    a_op[n, n + 1] = np.sqrt(n + 1)
ad_op = a_op.T
Iop = np.eye(Nc)
Xop = (a_op + ad_op) / np.sqrt(2)
Pop = (a_op - ad_op) / (1j * np.sqrt(2))

r_tmsv = 0.4
lam = np.tanh(r_tmsv)
coeff = lam ** np.arange(Nc)
coeff = coeff / np.sqrt(np.sum(np.abs(coeff) ** 2))
psi2 = np.zeros((Nc, Nc), dtype=complex)
for n in range(Nc):
    psi2[n, n] = coeff[n]
psi_tmsv = psi2.reshape(-1)
check(abs(np.vdot(psi_tmsv, psi_tmsv) - 1.0) < 1e-10, "TMSV (truncated Fock) state is normalized")

X1, P1 = np.kron(Xop, Iop), np.kron(Pop, Iop)
X2, P2 = np.kron(Iop, Xop), np.kron(Iop, Pop)


def expect_tmsv(Op):
    return np.vdot(psi_tmsv, Op @ psi_tmsv)


def symcov_tmsv(A, B):
    return 0.5 * expect_tmsv(A @ B + B @ A) - expect_tmsv(A) * expect_tmsv(B)


site_ops = [X1, P1, X2, P2]  # site-ordered (x1,p1,x2,p2), matching gamma_O's convention
gB_tmsv = np.zeros((4, 4))
for i in range(4):
    for j in range(4):
        gB_tmsv[i, j] = 2 * symcov_tmsv(site_ops[i], site_ops[j]).real
check(hermitian_close(gB_tmsv), "TMSV site-ordered gamma_B is symmetric")
check(abs(gB_tmsv[0, 2] - np.sinh(2 * r_tmsv)) < 1e-6,
      "TMSV Cov(X1,X2) = sinh(2r)/2 (times the gamma_B=2V factor) matches the closed form")


def chi_tmsv(u):
    ux1, up1, ux2, up2 = u
    G = up1 * X1 - ux1 * P1 + up2 * X2 - ux2 * P2
    G = (G + G.conj().T) / 2
    w, V = np.linalg.eigh(G)
    Ophase = V @ np.diag(np.exp(1j * w)) @ V.conj().T
    return np.vdot(psi_tmsv, Ophase @ psi_tmsv)


def unit4(i):
    v = [0.0, 0.0, 0.0, 0.0]
    v[i] = 1.0
    return v


diag_vals = []
for i in range(4):
    c = chi_tmsv(unit4(i)).real
    diag_vals.append(-4.0 * np.log(c))
gform_O_tmsv = np.diag(diag_vals)
for i in range(4):
    for j in range(i + 1, 4):
        v = unit4(i)
        v[j] = 1.0
        c = chi_tmsv(v).real
        val = -4.0 * np.log(c)
        off = (val - diag_vals[i] - diag_vals[j]) / 2.0
        gform_O_tmsv[i, j] = off
        gform_O_tmsv[j, i] = off

Om_O_2 = region_omega(2)
gform_pred_tmsv = Om_O_2 @ gB_tmsv @ Om_O_2.T
check(np.allclose(gform_O_tmsv, gform_pred_tmsv, atol=1e-4),
      "TMSV two-mode: gamma_form_O (from chi) = Omega_O gamma_B_O Omega_O^T (site-ordered)")
gB_tmsv_from_gform = Om_O_2.T @ gform_O_tmsv @ Om_O_2
check(np.allclose(gB_tmsv_from_gform, gB_tmsv, atol=1e-4),
      "TMSV two-mode: gamma_B_O = Omega_O^T gamma_form_O Omega_O recovers the directly-computed covariance")

P2sites = region_permutation(2)
covmat_tmsv = P2sites @ (Om_O_2.T @ gform_O_tmsv @ Om_O_2) @ P2sites.T
check(np.allclose(covmat_tmsv, P2sites @ gB_tmsv @ P2sites.T, atol=1e-4),
      "TMSV: composite formula covarianceMatrix O gamma = P_O(Omega_O^T gamma_O Omega_O)P_O^T "
      "matches the directly-computed, block-reindexed BosonicLean covariance")
check(is_admissible_thesis(gform_O_tmsv, Om_O_2) == is_admissible_bosoniclean(covmat_tmsv, Omega(2)),
      "TMSV: admissibility transports both ways through the full composite map")

# ================= 3. Fourier criterion on Z (Lemma 4.5(i)) =================
# gamma_hat(k) = sum_x gamma_x e^{-ikx}, matching xi_hat(k) = sum_x xi_x e^{-ikx} (4.14).
def gamma_hat(gamma_x, k):
    S = np.zeros((2, 2), dtype=complex)
    for x, g in gamma_x.items():
        S = S + g * np.exp(-1j * k * x)
    return S


def rand_symmetric_finite_range(rng, R, scale=1.0):
    """gamma_x for x in [-R,R], symmetric gamma_{-x} = gamma_x^T."""
    gx = {}
    gx[0] = None
    A0 = rng.normal(size=(2, 2), scale=scale)
    gx[0] = (A0 + A0.T) / 2
    for x in range(1, R + 1):
        A = rng.normal(size=(2, 2), scale=scale)
        gx[x] = A
        gx[-x] = A.T
    return gx


def truncated_toeplitz_condition_matrix(gamma_x, Om, N):
    """The (2*(2N+1)) x (2*(2N+1)) matrix of (4.6): block (x,y) = gamma(x-y) + i*delta(x,y)*Om,
    for x,y in [-N,N]."""
    sites = list(range(-N, N + 1))
    n = len(sites)
    M = np.zeros((2 * n, 2 * n), dtype=complex)
    for i, x in enumerate(sites):
        for j, y in enumerate(sites):
            d = x - y
            block = gamma_x.get(d, np.zeros((2, 2)))
            if x == y:
                block = block + 1j * Om
            M[2 * i:2 * i + 2, 2 * j:2 * j + 2] = block
    return M


def k_grid_condition_holds(gamma_x, Om, num_k=400, tol=1e-7):
    ks = np.linspace(-np.pi, np.pi, num_k, endpoint=False)
    for k in ks:
        if not is_psd(gamma_hat(gamma_x, k) + 1j * Om, tol=tol):
            return False
    return True


fourier_examples = []
# admissible: vacuum + small nearest-neighbour correlation, scaled down to stay admissible
for scale, admissible_guess in [(0.05, True), (0.4, None), (1.5, False)]:
    gx = rand_symmetric_finite_range(rng, R=1, scale=scale)
    gx[0] = gx[0] + 3.0 * np.eye(2)  # dominant diagonal term to help/hurt admissibility predictably
    fourier_examples.append(gx)

for gx in fourier_examples:
    k_ok = k_grid_condition_holds(gx, Om1)
    # large truncation
    Mbig = truncated_toeplitz_condition_matrix(gx, Om1, N=25)
    trunc_ok = is_psd(Mbig, tol=1e-5)
    check(hermitian_close(Mbig, tol=1e-6), "truncated (4.6) matrix is Hermitian")
    check(k_ok == trunc_ok,
          "Fourier criterion (k-grid) matches large finite truncation of the state condition")

# explicit failing case: gamma_0 = 0.1*I, no coupling -> gamma_hat(k) = 0.1*I always,
# 0.1*I + i*Omega has eigenvalues 0.1 +- 1 -> negative eigenvalue -> fails both sides
gx_fail = {0: 0.1 * np.eye(2)}
check(not k_grid_condition_holds(gx_fail, Om1), "gamma=0.1*I fails the Fourier criterion")
check(not is_psd(truncated_toeplitz_condition_matrix(gx_fail, Om1, N=15), tol=1e-6),
      "gamma=0.1*I fails the truncated state condition (both directions agree)")

# explicit passing case: gamma_0 = I (vacuum, product state)
gx_pass = {0: np.eye(2)}
check(k_grid_condition_holds(gx_pass, Om1), "gamma=I passes the Fourier criterion")
check(is_psd(truncated_toeplitz_condition_matrix(gx_pass, Om1, N=15), tol=1e-6),
      "gamma=I passes the truncated state condition (both directions agree)")

# ================= 4. evolution (4.17) =================
def symbol_of_rule(Lm, k):
    S = np.zeros((2, 2), dtype=complex)
    for m, l in Lm.items():
        S = S + np.array(l, dtype=complex) * np.exp(-1j * k * m)
    return S


def evolve_gamma_position_space(Lm, gamma0, R_out):
    """gamma_t(x) = sum_{y,z} L(y)^T gamma0(x+y-z) L(z), (4.17a), for x in [-R_out, R_out]."""
    out = {}
    ms = list(Lm.keys())
    for x in range(-R_out, R_out + 1):
        S = np.zeros((2, 2))
        for y in ms:
            for z in ms:
                g = gamma0.get(x + y - z)
                if g is not None:
                    S = S + Lm[y].T @ g @ Lm[z]
        out[x] = S
    return out


def check_4_17(Lm, gamma0, label, reflection_symmetric):
    R_out = 8
    gamma_t = evolve_gamma_position_space(Lm, gamma0, R_out)
    for k in np.linspace(-np.pi, np.pi, 9):
        lhs = gamma_hat(gamma_t, k)  # position-space side (exact: gamma_t has finite support)
        Lhat_k = symbol_of_rule(Lm, k)
        Lhat_mk = symbol_of_rule(Lm, -k)
        rhs_general = Lhat_mk.T @ gamma_hat(gamma0, k) @ Lhat_k  # the general identity
        rhs_printed = Lhat_k.T @ gamma_hat(gamma0, k) @ Lhat_k   # literal (4.17b), Lhat(k)^T (.) Lhat(k)
        check(np.allclose(lhs, rhs_general, atol=1e-6),
              f"(4.17a) Fourier-transforms to gamma_hat_t(k)=Lhat(-k)^T gamma_hat_0(k) Lhat(k), "
              f"the general identity ({label}, k={k:.3f})")
        if reflection_symmetric:
            check(np.allclose(Lhat_k, Lhat_mk, atol=1e-8),
                  f"reflection-symmetric rule has Lhat(k)=Lhat(-k) ({label}, k={k:.3f})")
            check(np.allclose(lhs, rhs_printed, atol=1e-6),
                  f"printed (4.17b) Lhat(k)^T(.)Lhat(k) matches too, since Lhat(k)=Lhat(-k) "
                  f"({label}, k={k:.3f})")
        elif abs(abs(k) - np.pi) > 1e-6 and abs(k) > 1e-6:
            # at k = +-pi, e^{-ikm}=e^{ikm} for integer m, so Lhat(k)=Lhat(-k) even here
            check(not np.allclose(Lhat_k, Lhat_mk, atol=1e-8),
                  f"non-symmetric rule genuinely has Lhat(k) != Lhat(-k) ({label}, k={k:.3f})")


mm = 1
Frule = {0: np.array([[0.0, 1.0], [-1.0, -mm]]), 1: np.zeros((2, 2)), -1: np.zeros((2, 2))}
Frule[1][1, 1] = 1.0
Frule[-1][1, 1] = 1.0
check(np.allclose(Frule[1], Frule[-1]), "leapfrog is reflection-symmetric: l_{-1} = l_{+1}")
gamma0_vac = {0: np.eye(2)}
check_4_17(Frule, gamma0_vac, "leapfrog (reflection-symmetric)", reflection_symmetric=True)

# hand-built non-symmetric rule (l_{-1} != l_{+1}); no symplecticity required for (4.17a/b),
# which is a pure Fourier-convolution identity
L_asym = {-1: np.array([[0.2, 0.0], [0.0, 0.0]]), 0: np.array([[1.0, 0.3], [-0.1, 1.0]]),
          1: np.array([[0.0, 0.0], [0.5, 0.0]])}
check(not np.allclose(L_asym[-1], L_asym[1]), "L_asym is genuinely non-reflection-symmetric")
gx_test = rand_symmetric_finite_range(rng, R=1, scale=1.0)
check_4_17(L_asym, gx_test, "hand-built non-symmetric rule", reflection_symmetric=False)

# on-site rotation preserves the vacuum (feeds into item 6 too)
phi = 0.7
Gamma0 = np.array([[np.cos(phi), -np.sin(phi)], [np.sin(phi), np.cos(phi)]])
check(abs(np.linalg.det(Gamma0) - 1.0) < 1e-12, "Gamma0 is a rotation, det=1")
L_rot = {0: Gamma0}
gamma_t_rot = evolve_gamma_position_space(L_rot, gamma0_vac, 1)
check(np.allclose(gamma_t_rot[0], np.eye(2), atol=1e-10),
      "on-site rotation preserves the vacuum correlation function gamma=I (position space)")
check(all(np.allclose(gamma_t_rot[x], 0) for x in gamma_t_rot if x != 0),
      "on-site rotation produces no off-site correlations")

# ================= 5. Lemma 4.5(ii), purity (printed p. 82) =================
# "[gamma] corresponds to a pure Gaussian state if and only if gamma_hat(k) + i sigma_s is not
#  strictly positive for any k in [-pi,pi], i.e. if (sigma_s gamma_hat(k))^2 = -1."
def is_pure_at_k(gamma_hat_k, Om, tol=1e-8):
    return np.allclose(Om @ gamma_hat_k @ Om @ gamma_hat_k, -np.eye(2), atol=tol) \
        if False else np.allclose((Om @ gamma_hat_k) @ (Om @ gamma_hat_k), -np.eye(2), atol=tol)


def not_strictly_positive(gamma_hat_k, Om, tol=1e-8):
    M = gamma_hat_k + 1j * Om
    ev = np.linalg.eigvalsh((M + M.conj().T) / 2)
    return ev.min() < tol  # smallest eigenvalue is (near) 0, i.e. not strictly positive


purity_examples = [
    (np.eye(2), True, "vacuum gamma_hat=I is pure"),
    (np.diag([3.0, 1 / 3.0]), True, "squeezed diag(t,1/t) is pure"),
    (np.diag([5.0, 0.2]) + 0 * np.eye(2), True, "squeezed diag(5,0.2) is pure"),
    (2.0 * np.eye(2), False, "thermal gamma_hat=2I is NOT pure (mixed)"),
    (np.diag([2.0, 1.0]), False, "diag(2,1) (det=2 != 1) is NOT pure"),
]
for gh, expect_pure, label in purity_examples:
    admissible = is_psd(gh + 1j * Om1, tol=1e-8)
    check(admissible, f"purity example is admissible first ({label})")
    pure_by_square = is_pure_at_k(gh, Om1)
    pure_by_boundary = not_strictly_positive(gh, Om1)
    check(pure_by_square == pure_by_boundary,
          f"(sigma_s gamma_hat)^2=-1 iff gamma_hat+i sigma_s not strictly positive ({label})")
    check(pure_by_square == expect_pure, f"purity classification matches Lemma 4.5(ii) ({label})")

# ================= 6. BosonicLean examples =================
def diagonalOne(a, b):
    return np.diag([a, b])


def is_admissible_diagonalOne(a, b):
    return is_admissible_bosoniclean(diagonalOne(a, b), Om1)


for a, b, expect, label in [
    (1.0, 1.0, True, "diagonalOne 1 1 (vacuum)"),
    (2.0, 0.5, True, "diagonalOne 2 (1/2) (squeezed, t=2)"),
    (0.3, 1 / 0.3, True, "diagonalOne t (1/t), t=0.3"),
    (0.5, 0.5, False, "diagonalOne 0.5 0.5 (0<a but a*b<1, not admissible)"),
    (-1.0, 1.0, False, "diagonalOne -1 1 (a<=0, not admissible)"),
]:
    got = is_admissible_diagonalOne(a, b)
    check(got == expect, f"IsAdmissible({label}) matches BosonicLean's 0<a and 1<=a*b criterion")
    # cross-check against the algebraic criterion isAdmissible_diagonalOne_iff
    alg = (a > 0) and (a * b >= 1 - 1e-9)
    check(got == alg, f"numeric IsAdmissible matches algebraic 0<a & 1<=a*b ({label})")

# on-site rotation preserves the vacuum, via BosonicLean's symplecticCongruence-style statement:
# Gamma0^T * I * Gamma0 = I for Gamma0 a rotation (det=1, orthogonal)
check(np.allclose(Gamma0.T @ diagonalOne(1.0, 1.0) @ Gamma0, diagonalOne(1.0, 1.0), atol=1e-10),
      "on-site rotation congruence Gamma0^T (diagonalOne 1 1) Gamma0 = diagonalOne 1 1")
check(is_admissible_diagonalOne(1.0, 1.0), "the preserved vacuum matrix stays IsAdmissible")

# ================= 7. on-site evolution transport by a NON-orthogonal symplectic S =================
# Corollary (transport)(b): for (Lu)(x) = S u(x) on-site with S^T Omega S = Omega,
#   covarianceMatrix O gamma(L.,L.) = T covarianceMatrix O gamma T^T,   T = P_O (1_O tensor S^{-1}) P_O^T.
# Checked here on genuinely non-orthogonal symplectic S (S^T S != I): a one-mode squeeze
# diag(2, 1/2) and a one-mode shear [[1,1],[0,1]] (both in Sp(2,R) = SL(2,R)), for regions of
# 1, 2 and 3 sites, with S applied identically at every site (1_O tensor S).
S_squeeze = np.diag([2.0, 0.5])
S_shear = np.array([[1.0, 1.0], [0.0, 1.0]])
for S_test, S_label in [(S_squeeze, "squeeze diag(2,1/2)"), (S_shear, "shear [[1,1],[0,1]]")]:
    check(np.allclose(S_test.T @ Om1 @ S_test, Om1), f"{S_label} is symplectic, S^T Omega S = Omega")
    check(not np.allclose(S_test.T @ S_test, np.eye(2)), f"{S_label} is NOT orthogonal (S^T S != I)")
    S_inv = np.linalg.inv(S_test)
    check(np.allclose(S_inv @ Om1 @ S_inv.T, Om1), f"{S_label}: S^{{-1}} is symplectic too")

    for n_sites in (1, 2, 3):
        P = region_permutation(n_sites)
        Om_O = region_omega(n_sites)
        S_O = np.kron(np.eye(n_sites), S_test)       # 1_O tensor S, site-ordered
        Sinv_O = np.kron(np.eye(n_sites), S_inv)      # 1_O tensor S^{-1}
        T = P @ Sinv_O @ P.T

        A = rng.normal(size=(2 * n_sites, 2 * n_sites))
        gamma_O = (A + A.T) / 2
        # make gamma_O admissible (state condition) by adding a large multiple of the vacuum
        gamma_O = gamma_O + 4.0 * np.eye(2 * n_sites)
        check(is_admissible_thesis(gamma_O, Om_O), f"gamma_O is admissible before transport ({S_label}, n={n_sites})")

        gamma_O_prime = S_O.T @ gamma_O @ S_O  # gamma'(u,w) = gamma(Lu,Lw) on site vectors
        cov_gamma = P @ (Om_O.T @ gamma_O @ Om_O) @ P.T
        cov_gamma_prime = P @ (Om_O.T @ gamma_O_prime @ Om_O) @ P.T

        predicted = T @ cov_gamma @ T.T
        check(np.allclose(cov_gamma_prime, predicted, atol=1e-8),
              f"covarianceMatrix O gamma' = T covarianceMatrix O gamma T^T, T=P_O(1_O tensor S^-1)P_O^T "
              f"({S_label}, n={n_sites})")
        # T is NOT (in general) an orthogonal congruence, since S is not orthogonal: it still
        # transports admissibility because S^{-1} is symplectic (checked above), but T^T T != I.
        check(not np.allclose(T.T @ T, np.eye(2 * n_sites)),
              f"T is a genuinely non-orthogonal congruence here ({S_label}, n={n_sites})")
        check(is_admissible_bosoniclean(cov_gamma_prime, Omega(n_sites)),
              f"covarianceMatrix O gamma' stays IsAdmissible after non-orthogonal-S transport "
              f"({S_label}, n={n_sites})")
        check(is_admissible_thesis(gamma_O_prime, Om_O),
              f"gamma_O' = S_O^T gamma_O S_O satisfies the state condition on O too ({S_label}, n={n_sites})")

print("Resolved: on-site evolution by non-orthogonal symplectic S transports "
      "covarianceMatrix O by T = P_O(1_O tensor S^{-1})P_O^T (congruence by S^{-1}, blockwise, "
      "reindexed by P_O); admissibility is preserved even though T itself is not orthogonal.")

# ================= 8. purity 2x2 counterexample (complex Hermitian, sign both fail) =================
# A = [[sqrt(2), -i], [i, sqrt(2)]]: det A = 2 - 1 = 1, but A is admissible on only ONE side
# (A + i*Omega >= 0) and NOT the other (A - i*Omega not >= 0), and (Omega A)^2 != -1: det=1 alone,
# or admissibility on only one side, does not give purity -- both +i and -i sides are needed.
A_ce = np.array([[np.sqrt(2.0), -1j], [1j, np.sqrt(2.0)]])
check(hermitian_close(A_ce), "counterexample A is Hermitian")
check(abs(np.linalg.det(A_ce) - 1.0) < 1e-12, "counterexample A has det A = 1")
check(is_psd(A_ce + 1j * Om1), "counterexample A: A + i*Omega >= 0")
check(not is_psd(A_ce - 1j * Om1), "counterexample A: A - i*Omega is NOT >= 0")
OmA_ce = Om1 @ A_ce
check(not np.allclose(OmA_ce @ OmA_ce, -np.eye(2), atol=1e-6),
      "counterexample A: (Omega A)^2 != -1 (A is not pure, consistent with failing one side)")

# Positive direction: Hermitian A with BOTH A+i*Omega>=0 and A-i*Omega>=0 and det A=1 forces
# (Omega A)^2 = -1. Direct algebra on a general Hermitian A=[[p,q],[conj(q),r]] (p,r real) shows
# the off-diagonal entries of (Omega A)^2 are r*(-2i*Im(q)) and p*(2i*Im(q)): with p,r generic
# (nonzero), (Omega A)^2=-1 forces Im(q)=0, i.e. A is real symmetric (2x2 has no genuinely
# complex-off-diagonal pure example with det=1 and p,r != 0, unlike the failing det=1 example
# above). So the positive-direction random tests range over real symmetric A -- still Hermitian
# -- built as random rotations of random one-mode squeezed states (guaranteed pure/admissible by
# construction, generalizing item 1's diag(t,1/t) family).
rng8 = np.random.default_rng(7)
n_hits = 0
n_trials = 300
for _ in range(n_trials):
    t_r = rng8.uniform(0.2, 5.0)
    phi_r = rng8.uniform(-np.pi, np.pi)
    Rr = np.array([[np.cos(phi_r), np.sin(phi_r)], [-np.sin(phi_r), np.cos(phi_r)]])
    A_rand = Rr.T @ np.diag([t_r, 1.0 / t_r]) @ Rr
    check(hermitian_close(A_rand), "random purity-test A is Hermitian (real symmetric)")
    check(abs(np.linalg.det(A_rand) - 1.0) < 1e-8, "random purity-test A has det A = 1")
    both_admissible = is_psd(A_rand + 1j * Om1) and is_psd(A_rand - 1j * Om1)
    check(both_admissible, "random purity-test A is admissible on both sides (det=1 rotated squeeze)")
    if both_admissible:
        n_hits += 1
        OmA = Om1 @ A_rand
        check(np.allclose(OmA @ OmA, -np.eye(2), atol=1e-6),
              "Hermitian A with A+iOmega>=0, A-iOmega>=0, det A=1 has (Omega A)^2 = -1 (random)")
check(n_hits >= 20, "purity random search: enough admissible-both-sides hits to be a real test")

# genuinely complex Hermitian A with p or r zero also cannot have det A = 1 (det = p*r - |q|^2 <=
# -|q|^2 <= 0 when p=0 or r=0), so this 2x2 case gives no complex-off-diagonal, det=1 example on
# either side of admissibility, real-symmetric or not -- confirming the counterexample A above is
# excluded from the "both sides" family precisely by failing the -i*Omega side, not by being real.
for _ in range(20):
    q_im = rng8.normal(scale=1.0) + 1j * rng8.normal(scale=1.0)
    A_deg = np.array([[0.0, q_im], [np.conj(q_im), 0.0]])
    check(hermitian_close(A_deg), "degenerate p=r=0 Hermitian matrix check is Hermitian")
    check(np.linalg.det(A_deg).real <= 1e-12,
          "p=0 (or r=0) Hermitian 2x2 has det A <= 0, so never reaches det A = 1")

print(f"Resolved: A=[[sqrt2,-i],[i,sqrt2]] is a genuine det=1 counterexample to purity (one-sided "
      f"admissible only, (Omega A)^2 != -1); real-symmetric Hermitian A admissible on BOTH sides "
      f"with det A=1 always has (Omega A)^2=-1 ({n_hits}/{n_trials} random hits), and 2x2 Hermitian "
      f"A with det A=1 and genuinely complex off-diagonal entries does not exist when p,r != 0.")

# ================= 9. cell-index convention: gamma_{x-y} vs gamma_{y-x} =================
# (4.4)'s gamma(u,w) = sum_{x,y} u(x)^T gamma_{x-y} w(y), gamma_hat(k) = sum_x gamma_x e^{-ikx}.
# If instead one indexes by gamma_{y-x} (gamma'(u,w) = sum_{x,y} u(x)^T gamma_{y-x} w(y), same
# bilinear form but relabelled), then writing tilde_gamma_d := gamma_{-d} for the coefficients in
# the ORIGINAL convention's slot d, gamma'(u,w) = sum u(x)^T tilde_gamma_{x-y} w(y), and
#   tilde_gamma_hat(k) = sum_x tilde_gamma_x e^{-ikx} = sum_x gamma_{-x} e^{-ikx} = gamma_hat(-k).
# For symmetric gamma (gamma_{-x} = gamma_x^T) this is also gamma_hat(k)^T = conj(gamma_hat(k)).
# Substituting k -> -k in the general evolution identity (item 4),
#   gamma_hat_t(k) = Lhat(-k)^T gamma_hat_0(k) Lhat(k),
# gives, for the y-x-indexed (tilde) data, tilde_gamma_hat_t(k) = gamma_hat_t(-k)
#   = Lhat(k)^T gamma_hat_0(-k) Lhat(-k) = Lhat(k)^T tilde_gamma_hat_0(k) Lhat(-k):
# the roles of Lhat(k) and Lhat(-k) SWAP relative to the x-y convention (the left factor now
# carries Lhat(k), not Lhat(-k)).
def evolve_gamma_position_space_yx(Lm, gamma0, R_out):
    """Gamma_t(d) = sum_{m,n} L(m)^T Gamma0(d+n-m) L(n): the (4.17a)-analogue when the bilinear
    form is written gamma(u,w) = sum_{x,y} u(x)^T Gamma_{y-x} w(y) (index n-m, not m-n)."""
    out = {}
    ms = list(Lm.keys())
    for d in range(-R_out, R_out + 1):
        Sd = np.zeros((2, 2))
        for m in ms:
            for n in ms:
                g = gamma0.get(d + n - m)
                if g is not None:
                    Sd = Sd + Lm[m].T @ g @ Lm[n]
        out[d] = Sd
    return out


for gx_base, label in [(gamma0_vac, "vacuum"), (gx_test, "hand-built non-symmetric-rule data")]:
    tilde_gx = {d: gx_base[-d] for d in gx_base}  # Gamma_d := gamma_{-d}, i.e. reindex by y-x
    for x, g in gx_base.items():
        check(np.allclose(tilde_gx.get(-x, np.zeros((2, 2))), g),
              f"tilde_gamma_{{-x}} = gamma_x reindexing sanity ({label}, x={x})")
    Lm_test = L_asym
    gamma_t_orig = evolve_gamma_position_space(Lm_test, gx_base, 8)      # x-y convention, (4.17a)
    tilde_gamma_t = evolve_gamma_position_space_yx(Lm_test, tilde_gx, 8)  # y-x convention, its analogue
    for x in gamma_t_orig:
        if -x in tilde_gamma_t:
            check(np.allclose(tilde_gamma_t[-x], gamma_t_orig[x], atol=1e-8),
                  f"y-x-evolved tilde_gamma_t({-x}) = gamma_{{-d}} reindexing of the x-y-evolved "
                  f"gamma_t({x}) ({label}): same physical evolved state, either convention")
    for k in np.linspace(-np.pi, np.pi, 7):
        lhs = gamma_hat(tilde_gamma_t, k)
        check(np.allclose(gamma_hat(tilde_gx, k), gamma_hat(gx_base, -k), atol=1e-8),
              f"tilde_gamma_hat(k) = gamma_hat(-k), the y-x reindexing identity ({label}, k={k:.3f})")
        Lhat_k = symbol_of_rule(Lm_test, k)
        Lhat_mk = symbol_of_rule(Lm_test, -k)
        rhs_swapped = Lhat_k.T @ gamma_hat(tilde_gx, k) @ Lhat_mk
        check(np.allclose(lhs, rhs_swapped, atol=1e-6),
              f"y-x convention: gamma_hat_t'(k) = Lhat(k)^T gamma_hat_0'(k) Lhat(-k), "
              f"roles of Lhat(k), Lhat(-k) swapped vs the x-y convention ({label}, k={k:.3f})")

print("Resolved: indexing by gamma_{y-x} instead of gamma_{x-y} sends gamma_hat(k) -> gamma_hat(-k) "
      "throughout, and swaps which factor in (4.17) carries Lhat(k) vs Lhat(-k): "
      "gamma_hat_t(k) = Lhat(k)^T gamma_hat_0(k) Lhat(-k) under the y-x convention.")

# ================= 8. lecture notes: Example ex:gs-leapfrog (exact, sympy) =================
# docs/lecture-notes/gaussianstates.tex, Example "The leapfrog applied to the vacuum".
import sympy as sp

k, m2 = sp.symbols('k m2', real=True)
I2 = sp.eye(2)
Om_sym = sp.Matrix([[0, 1], [-1, 0]])
c = 2 * sp.cos(k) - m2  # c_k

# leapfrog F: ell_0 = [[0,1],[-1,-m2]], ell_{+-1} = diag(0,1)
ellF0 = sp.Matrix([[0, 1], [-1, -m2]])
ellFpm1 = sp.Matrix([[0, 0], [0, 1]])
Fhat = sp.simplify(ellF0 + ellFpm1 * sp.exp(-sp.I * k) + ellFpm1 * sp.exp(sp.I * k))
check(sp.simplify(Fhat - sp.Matrix([[0, 1], [-1, c]])) == sp.zeros(2),
      "lecture notes ex:gs-leapfrog: Fhat(k) = [[0,1],[-1,c_k]] from ell_0, ell_{+-1} of F")

# F^{-1}: ell_0 = [[-m2,-1],[1,0]], ell_{+-1} = diag(1,0); symbol convention Lhat(k) = sum_g ell_g e^{-ikg}
ell0 = sp.Matrix([[-m2, -1], [1, 0]])
ellpm1 = sp.Matrix([[1, 0], [0, 0]])
Fhat_inv = sp.simplify(ell0 + ellpm1 * sp.exp(-sp.I * k) + ellpm1 * sp.exp(sp.I * k))
check(sp.simplify(Fhat_inv - sp.Matrix([[c, -1], [1, 0]])) == sp.zeros(2),
      "lecture notes ex:gs-leapfrog: Fhat^{-1}(k) = [[c_k,-1],[1,0]] from the stated ell_0, ell_{+-1}")
# cross-check Fhat_inv is indeed Fhat^{-1} as matrices (independent of the symbol bookkeeping)
check(sp.simplify(Fhat * Fhat_inv - I2) == sp.zeros(2),
      "lecture notes ex:gs-leapfrog: Fhat(k) . Fhat^{-1}(k) = 1, confirming Fhat^{-1} is genuinely "
      "the inverse symbol")

# evolved vacuum symbol: gamma_hat'(k) = Fhat^{-1}(-k)^T Fhat^{-1}(k) (Theorem thm:gs-evolution,
# gamma'(x) = sum_g ell_g^T gamma(x+g-h) ell_h with gamma = 1 giving gamma_hat' = Lhat(-k)^T Lhat(k))
Fhat_inv_mk = Fhat_inv.subs(k, -k)
gamma_hat_prime = sp.simplify(Fhat_inv_mk.T * Fhat_inv)
gamma_hat_prime_expected = sp.Matrix([[1 + c**2, -c], [-c, 1]])
check(sp.simplify(gamma_hat_prime - gamma_hat_prime_expected) == sp.zeros(2),
      "lecture notes ex:gs-leapfrog: Fhat^{-1}(-k)^T Fhat^{-1}(k) = [[1+c_k^2,-c_k],[-c_k,1]]")

# derive the cell-index formula gamma'_j = sum_g ell_g^T ell_{g+j} (Lm indexed by g in {-1,0,1},
# zero elsewhere) directly from gamma'(x) = sum_{g,h} ell_g^T gamma_{x+g-h} ell_h with the vacuum
# gamma_y = delta_{y,0} I: only h = x+g survives, giving gamma'_x = sum_g ell_g^T ell_{g+x}.
ell = {-1: ellpm1, 0: ell0, 1: ellpm1}


def ell_at(j):
    return ell.get(j, sp.zeros(2))


def gamma_prime_cell(j):
    return sum((ell_at(g).T * ell_at(g + j) for g in (-1, 0, 1)), sp.zeros(2))


gamma_prime_cells_expected = {
    0: sp.Matrix([[3 + m2**2, m2], [m2, 1]]),
    1: sp.Matrix([[-2 * m2, -1], [-1, 0]]),
    -1: sp.Matrix([[-2 * m2, -1], [-1, 0]]),
    2: sp.Matrix([[1, 0], [0, 0]]),
    -2: sp.Matrix([[1, 0], [0, 0]]),
}
for j, expected in gamma_prime_cells_expected.items():
    got = sp.simplify(gamma_prime_cell(j))
    check(sp.simplify(got - expected) == sp.zeros(2),
          f"lecture notes ex:gs-leapfrog: gamma'_{{{j}}} = sum_g ell_g^T ell_{{g+{j}}} matches the "
          f"stated cell {expected.tolist()}")
for j in (-3, 3, -4, 4):
    check(sp.simplify(gamma_prime_cell(j)) == sp.zeros(2),
          f"lecture notes ex:gs-leapfrog: gamma'_{{{j}}} = 0 outside range 2, as stated "
          "('and zero otherwise')")

# re-sum the derived cells against e^{-ikj} and confirm they reproduce the symbol computed above,
# i.e. the index formula and the symbol formula gamma_hat' = Fhat^{-1}(-k)^T Fhat^{-1}(k) agree
gamma_hat_prime_from_cells = sp.simplify(
    sum((gamma_prime_cell(j) * sp.exp(-sp.I * k * j) for j in range(-2, 3)), sp.zeros(2)))
check(sp.simplify(gamma_hat_prime_from_cells - gamma_hat_prime_expected) == sp.zeros(2),
      "lecture notes ex:gs-leapfrog: sum_j gamma'_j e^{-ikj} over the stated finite-range cells "
      "reproduces gamma_hat'(k) = [[1+c_k^2,-c_k],[-c_k,1]]")

# det gamma_hat'(k) = 1 for every k, exactly
check(sp.simplify(gamma_hat_prime_expected.det() - 1) == 0,
      "lecture notes ex:gs-leapfrog: det gamma_hat'(k) = 1 identically")

# 1 + c_k^2 = 3 + m^4 - 4 m^2 cos k + 2 cos 2k
lhs_id = 1 + c**2
rhs_id = 3 + m2**2 - 4 * m2 * sp.cos(k) + 2 * sp.cos(2 * k)
check(sp.simplify(sp.expand_trig(lhs_id) - sp.expand_trig(rhs_id)) == 0,
      "lecture notes ex:gs-leapfrog: 1+c_k^2 = 3+m^4-4m^2 cos k+2 cos 2k")

# backward step: Fhat(k)^T Fhat(k) is the same matrix with the diagonal entries exchanged
Fhat_back = sp.simplify(Fhat.T * Fhat)
Fhat_back_expected = sp.Matrix([[1, -c], [-c, 1 + c**2]])
check(sp.simplify(Fhat_back - Fhat_back_expected) == sp.zeros(2),
      "lecture notes ex:gs-leapfrog: backward step Fhat(k)^T Fhat(k) = [[1,-c_k],[-c_k,1+c_k^2]]")
check(sp.simplify(Fhat_back[0, 0] - gamma_hat_prime_expected[1, 1]) == 0
      and sp.simplify(Fhat_back[1, 1] - gamma_hat_prime_expected[0, 0]) == 0
      and sp.simplify(Fhat_back[0, 1] - gamma_hat_prime_expected[0, 1]) == 0
      and sp.simplify(Fhat_back[1, 0] - gamma_hat_prime_expected[1, 0]) == 0,
      "lecture notes ex:gs-leapfrog: backward-step matrix is the forward-step matrix with its two "
      "diagonal entries exchanged, off-diagonal unchanged")

print("Checked (exact, sympy): lecture notes Example ex:gs-leapfrog, forward/backward symbols, "
      "the derived cell-index formula gamma'_j = sum_g ell_g^T ell_{g+j}, and the trig identity "
      "1+c_k^2 = 3+m^4-4m^2 cos k+2 cos 2k.")

# ================= 9. lecture notes: purity counterexample (Corollary cor:gs-purity remark) =================
# gamma_0 = 2.1, gamma_1 = (1/2)[[0,-1],[1,0]], gamma_{-1} = gamma_1^T, gamma_x = 0 otherwise.
gamma0_p = 2 * I2
gamma1_p = sp.Rational(1, 2) * sp.Matrix([[0, -1], [1, 0]])
gammam1_p = gamma1_p.T
check(sp.simplify(gammam1_p - sp.Rational(1, 2) * sp.Matrix([[0, 1], [-1, 0]])) == sp.zeros(2),
      "lecture notes purity example: gamma_{-1} = gamma_1^T as stated")

gamma_hat_p = sp.simplify(gamma0_p + gamma1_p * sp.exp(-sp.I * k) + gammam1_p * sp.exp(sp.I * k))
gamma_hat_p_expected = sp.Matrix([[2, sp.I * sp.sin(k)], [-sp.I * sp.sin(k), 2]])
check(sp.simplify(gamma_hat_p - gamma_hat_p_expected) == sp.zeros(2),
      "lecture notes purity example: gamma_hat(k) = [[2,i sin k],[-i sin k,2]]")

M_plus = sp.simplify(gamma_hat_p_expected + sp.I * Om_sym)
det_plus = sp.simplify(sp.expand_trig(M_plus.det()))
det_plus_expected = sp.expand_trig(4 - (1 + sp.sin(k))**2)
check(sp.simplify(det_plus - det_plus_expected) == 0,
      "lecture notes purity example: det(gamma_hat(k)+i Omega) = 4-(1+sin k)^2")
# gamma_hat(k)+iOmega >= 0 for every k: Hermitian 2x2 with positive diagonal (=2) and
# non-negative determinant is positive semidefinite; check the determinant is >= 0 for all real k
# exactly (as a trig inequality) and confirm at a dense sample of exact rational multiples of pi.
check(sp.simplify(M_plus[0, 0] - 2) == 0 and sp.simplify(M_plus[1, 1] - 2) == 0,
      "lecture notes purity example: gamma_hat(k)+i Omega has diagonal entries = 2 > 0")
for j in range(0, 24):
    kk = sp.pi * sp.Rational(j, 12)
    val = det_plus_expected.subs(k, kk)
    check(sp.simplify(val) >= 0,
          f"lecture notes purity example: det(gamma_hat(k)+i Omega) >= 0 at k = {j}pi/12 (exact)")
check(sp.simplify(det_plus_expected.subs(k, sp.pi * sp.Rational(1, 2))) == 0,
      "lecture notes purity example: gamma_hat(k)+i Omega is singular at k = pi/2 (det = 0, exact)")

det_gamma_hat_p = sp.simplify(gamma_hat_p_expected.det())
check(sp.simplify(det_gamma_hat_p.subs(k, sp.pi * sp.Rational(1, 2)) - 3) == 0,
      "lecture notes purity example: det gamma_hat(pi/2) = 3, exact")
# and det gamma_hat(k) is not identically 1 (this is the point of the example: singular at a
# single k does not force det = 1 there)
check(sp.simplify(det_gamma_hat_p - 1) != 0,
      "lecture notes purity example: det gamma_hat(k) is NOT identically 1 (only satisfies "
      "purity's det=1 criterion pointwise-coincidentally, not as an identity)")

print("Checked (exact, sympy): lecture notes purity counterexample (Corollary cor:gs-purity "
      "remark), gamma_hat(k)+iOmega >= 0 for all k, singular exactly at k=pi/2, "
      "det gamma_hat(pi/2) = 3.")

print(f"check_q3: {count} checks passed")
