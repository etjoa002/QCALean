"""
Numerical/symbolic checks resolving the conventions and testing the claims of
milestone Q4a: the example system (thesis (4.18)-(4.20)), Lemma 4.6,
Thm. 4.8 (stationary states, including the completeness half F3), and finding 2.

Run with python3 (needs sympy, numpy).

Source: O. Krueger, PhD thesis, TU Braunschweig 2006, Ch. 4, printed pp. 82-90
(PDF pages 92-100; printed page = PDF page - 10; pdftotext -layout), covering (4.18)-(4.29),
Lemma 4.5(ii), Lemma 4.6, Prop. 4.7 (statement only, its proof is Q4b), Thm. 4.8, and the
irreversible-QCA introduction (out of scope for Q4a).

Conventions, fixed in milestone Q3 and matched against the Lean definitions of
QCALean/Bosonic/NearestNeighbour.lean (`rotation_example`, `nnSymbol`) and Fourier.lean
(`rotation`, `rotationSymbol`, `fourierSymbol`):
  - gamma_hat(k) = sum_x gamma_x e^{-ikx}  (same sign as the thesis's (4.14)).
  - Evolution: gamma_hat' = L_hat(-k)^T gamma_hat L_hat(k) (Q3 item 4; the thesis's printed
    (4.17b), Gamma_hat_t(k)^T gamma_hat_0(k) Gamma_hat_t(k) with no -k, is the special case for
    reflection-symmetric rules, Gamma_hat(-k)=Gamma_hat(k), which holds here by (4.18)).
  - Omega = [[0,1],[-1,0]] (thesis's sigma_s, same matrix).
  - lam (Lean `rotationSymbol phi lam`) = the thesis's coupling f.

Krueger's Gamma_0 = rotation(phi) = [[cos phi, -sin phi],[sin phi, cos phi]] and
Gamma_pm = [[(Gamma_0)_{21}, (Gamma_0)_{22}], [0,0]] = [[sin phi, cos phi], [0,0]] (4.18).
Lean's `rotation phi` is exactly Gamma_0; `rotationSymbol phi lam` has l0 = rotation phi and
l+ = l- = vecMulVec e1 (lam * rotation phi pIdx), which is lam * (row Sum.inr of rotation phi)
placed in row Sum.inl -- i.e. lam * Gamma_pm above, since the momentum row (`pIdx = Sum.inr`) of
rotation phi is (sin phi, cos phi) = (Gamma_0)_{2,*}. So the Fourier symbol
  Gamma_hat(k) = fourierSymbol k (rotationSymbol phi lam)
              = e^{ik} lam Gamma_pm + Gamma_0 + e^{-ik} lam Gamma_pm
              = Gamma_0 + 2 lam cos(k) Gamma_pm,
matching (4.18) exactly with f = lam, checked below at item 1.

Corrections F1-F6 tested where the plan asks for a test (F4 is deferred, no check needed):
  F1. Prop. 4.7 needs lam*sin(phi) != 0; the thesis omits this. Tested at lam=0: gamma_t(0)
      for an onsite (neighbourhood {0}) rule with a squeezed (non-identity) gamma_0(0) is exactly
      periodic in t, not convergent -- item 8 below.
  F2. The stationary-phase heuristic in Prop. 4.7's proof is unnecessary; alpha is monotone
      away from the (finitely many) extrema. Tested via alpha' at item 3.
  F3. Thm. 4.8's "all stationary states" needs the completeness half: the invariant symmetric
      forms of an elliptic Gamma_hat(k) form a 1-dimensional space, spanned by eps_hat(k), and
      the state-condition threshold is g >= 1 exactly. Tested at item 6.
  F4. eps_hat continuous does not give gamma_infty absolutely summable (a different argument,
      real-analyticity + Wiener algebra, is needed). Deferred to Q4b; no check here.
  F5. Thm. 4.8 uses the Fourier-side state condition gamma_hat(k) +- i*Omega >= 0 (user decision
      3); consistent with Lemma 4.5(i) used throughout.
  F6. First moments do not converge unless d=0; kept as a hypothesis, not checked (Q4a scope
      does not include the amplitude part).

Deterministic; sympy exact asserts where the quantities are algebraic identities
in phi, lam, k or rational multiples of pi; numpy/mpmath floating checks with a stated
tolerance TOL where the claim is inherently about limits, eigenvalues, or a scan over k.
"""
import sympy as sp
import numpy as np

count = 0


def check(cond, label):
    global count
    assert cond, label
    count += 1


TOL = 1e-9

phi, lam, k, m2, t = sp.symbols('phi lam k m2 t', real=True)
Omega = sp.Matrix([[0, 1], [-1, 0]])


def rotation(ph):
    """Krueger's Gamma_0 = Lean's `rotation phi`."""
    return sp.Matrix([[sp.cos(ph), -sp.sin(ph)], [sp.sin(ph), sp.cos(ph)]])


def Gamma_pm(ph):
    """Krueger's Gamma_pm = [[(Gamma_0)_{21}, (Gamma_0)_{22}], [0,0]] (4.18)."""
    G0 = rotation(ph)
    return sp.Matrix([[G0[1, 0], G0[1, 1]], [0, 0]])


def GammaHat(ph, la, kk):
    """Gamma_hat(k) = Gamma_0 + 2 lam cos(k) Gamma_pm (4.18)."""
    return rotation(ph) + 2 * la * sp.cos(kk) * Gamma_pm(ph)


# ============================= 1. The example symbol (4.18) =============================
G0 = rotation(phi)
Gpm = Gamma_pm(phi)
check(sp.simplify(Gpm - sp.Matrix([[sp.sin(phi), sp.cos(phi)], [0, 0]])) == sp.zeros(2, 2),
      "Gamma_pm = [[sin phi, cos phi],[0,0]] = lam^{-1} times Lean's l+ = l- restricted to the "
      "rotation row (matches Lean's rotationSymbol; (4.18))")

Ghat = GammaHat(phi, lam, k)
check(sp.simplify(Ghat.det() - 1) == 0, "det Gamma_hat(k) = 1 exactly, for all phi, lam, k")
check(sp.simplify(Ghat.subs(k, -k) - Ghat) == sp.zeros(2, 2),
      "Gamma_hat(-k) = Gamma_hat(k) exactly (reflection symmetry, used throughout Thm. 4.8)")
tr_expected = 2 * sp.cos(phi) + 2 * lam * sp.cos(k) * sp.sin(phi)
check(sp.simplify(Ghat.trace() - tr_expected) == 0,
      "tr Gamma_hat(k) = 2 cos phi + 2 lam cos k sin phi (4.19; matches Lean's "
      "rotation_example trace formula, 2*cos phi + 2*lam*cos k*sin phi, exactly)")
check(sp.simplify((Ghat.T * Omega * Ghat - Omega)) == sp.zeros(2, 2),
      "Gamma_hat(k) is symplectic, Gamma_hat^T Omega Gamma_hat = Omega, for all phi, lam, k "
      "(consequence of det = 1 for a 2x2 matrix, thesis p. 83)")

# ============================= 2. The regime (4.20) =============================
# max_k |cos phi + lam cos k sin phi| = |cos phi| + |lam sin phi|, since the k-dependence is
# through cos k in [-1, 1] and the coefficient lam sin phi multiplies it linearly.
for ph_val in np.linspace(-3.0, 3.0, 13):
    for la_val in np.linspace(-2.0, 2.0, 9):
        ks = np.linspace(-np.pi, np.pi, 2001)
        vals = np.cos(ph_val) + la_val * np.cos(ks) * np.sin(ph_val)
        numeric_max = np.max(np.abs(vals))
        predicted = abs(np.cos(ph_val)) + abs(la_val * np.sin(ph_val))
        check(abs(numeric_max - predicted) < 1e-8,
              f"max_k |cos phi + lam cos k sin phi| = |cos phi| + |lam sin phi|, "
              f"phi={ph_val:.3f}, lam={la_val:.3f}")

# So the nonsqueezing regime "|tr Gamma_hat(k)| <= 2 for all k" is exactly
# |cos phi| + |lam sin phi| <= 1, and the plan's strict regime |cos phi| + |lam sin phi| < 1
# (with lam sin phi != 0, F1) is the nondegenerate case Lemma 4.6 needs.

# f_crit = (1 - |cos phi|)/|sin phi| form (4.20), for sin phi != 0:
for ph_val, la_val in [(0.7, 0.3), (2.1, -0.5), (-1.2, 0.8), (1.0, 1.5)]:
    if abs(np.sin(ph_val)) < 1e-6:
        continue
    fcrit = (1 - abs(np.cos(ph_val))) / abs(np.sin(ph_val))
    in_regime_direct = abs(np.cos(ph_val)) + abs(la_val * np.sin(ph_val)) < 1
    in_regime_fcrit = abs(la_val) < fcrit
    check(in_regime_direct == in_regime_fcrit,
          f"|cos phi|+|lam sin phi|<1  <=>  |lam| < f_crit = (1-|cos phi|)/|sin phi|, "
          f"phi={ph_val}, lam={la_val}")

# The tan(phi/2)/cot(phi/2) form of f_crit = (1-|cos phi|)/|sin phi|, exact (4.20):
for ph_val in [sp.pi / 6, sp.pi / 3, sp.pi * sp.Rational(2, 5)]:  # 0 < phi <= pi/2
    lhs = (1 - sp.Abs(sp.cos(ph_val))) / sp.Abs(sp.sin(ph_val))
    rhs = sp.tan(ph_val / 2)
    check(sp.simplify(lhs - rhs) == 0,
          f"f_crit = tan(phi/2) for phi={ph_val} (0 < phi <= pi/2), exact (4.20)")
for ph_val in [sp.pi * sp.Rational(2, 3), sp.pi * sp.Rational(5, 6)]:  # pi/2 < phi < pi
    lhs = (1 - sp.Abs(sp.cos(ph_val))) / sp.Abs(sp.sin(ph_val))
    rhs = 1 / sp.tan(ph_val / 2)
    check(sp.simplify(lhs - rhs) == 0,
          f"f_crit = cot(phi/2) for phi={ph_val} (pi/2 < phi < pi), exact (4.20)")

# ============================= 3. alpha(k) and alpha'(k) (4.19), F2 =============================
alpha_expr = sp.acos(sp.cos(phi) + lam * sp.cos(k) * sp.sin(phi))
alpha_prime = sp.diff(alpha_expr, k)
predicted_alpha_prime_sqrt = (lam * sp.sin(phi) * sp.sin(k)
                               / sp.sqrt(1 - (sp.cos(phi) + lam * sp.cos(k) * sp.sin(phi)) ** 2))
check(sp.simplify(alpha_prime - predicted_alpha_prime_sqrt) == 0,
      "alpha'(k) = lam sin phi sin k / sqrt(1 - cos^2 alpha(k)) exactly (chain rule on arccos)")
# In the regime sin alpha(k) > 0, so sqrt(1-cos^2 alpha) = sin alpha(k); check this numerically
# on a regime sample and confirm the plan's form alpha'(k) = lam sin phi sin k / sin alpha(k),
# together with monotonicity: sign(alpha'(k)) = sign(lam sin phi sin k) on (0, pi).
rng = np.random.default_rng(20260928)
regime_samples = 0
for _ in range(400):
    ph_val = rng.uniform(-np.pi + 0.05, np.pi - 0.05)
    if abs(np.sin(ph_val)) < 0.05:
        continue
    fcrit = (1 - abs(np.cos(ph_val))) / abs(np.sin(ph_val))
    la_val = rng.uniform(-0.98, 0.98) * fcrit
    if abs(la_val * np.sin(ph_val)) < 1e-3:
        continue  # F1: exclude lam sin phi = 0
    regime_samples += 1
    k_val = rng.uniform(0.01, np.pi - 0.01)
    cos_a = np.cos(ph_val) + la_val * np.cos(k_val) * np.sin(ph_val)
    sin_a = np.sqrt(max(1 - cos_a ** 2, 0.0))
    check(sin_a > 1e-6, "sin alpha(k) > 0 in the strict regime (nondegenerate case, Lemma 4.6)")
    alpha_prime_num = la_val * np.sin(ph_val) * np.sin(k_val) / sin_a
    h = 1e-6
    cos_a_p = np.cos(ph_val) + la_val * np.cos(k_val + h) * np.sin(ph_val)
    cos_a_m = np.cos(ph_val) + la_val * np.cos(k_val - h) * np.sin(ph_val)
    fd = (np.arccos(np.clip(cos_a_p, -1, 1)) - np.arccos(np.clip(cos_a_m, -1, 1))) / (2 * h)
    check(abs(fd - alpha_prime_num) < 1e-4,
          "alpha'(k) = lam sin phi sin k / sin alpha(k) matches a finite-difference derivative "
          "of arccos(cos phi + lam cos k sin phi) in the regime")
    check(np.sign(alpha_prime_num) == np.sign(la_val * np.sin(ph_val) * np.sin(k_val)) or
          abs(alpha_prime_num) < 1e-9,
          "sign(alpha'(k)) = sign(lam sin phi sin k): alpha is strictly monotone on (0, pi), "
          "with no interior critical point other than the excluded lam sin phi = 0 case (F2)")
check(regime_samples > 50, "the regime/monotonicity random scan produced enough samples")

# ============================= 4. The power formula (Lemma 4.6, Chebyshev form) =====
# Gamma_hat(k)^t = (sin(t alpha)/sin alpha) Gamma_hat(k) - (sin((t-1) alpha)/sin alpha) * 1,
# from Cayley-Hamilton with det Gamma_hat = 1, tr Gamma_hat = 2 cos alpha.
test_points = [
    (np.pi / 3, 0.25, np.pi / 5),
    (np.pi / 4, -0.35, np.pi / 7),
    (-np.pi / 5, 0.2, 2.1),
    (2.4, -0.2, -1.3),
]
for ph_val, la_val, k_val in test_points:
    fcrit = (1 - abs(np.cos(ph_val))) / abs(np.sin(ph_val))
    assert abs(la_val) < fcrit and abs(la_val * np.sin(ph_val)) > 1e-3
    M = np.array([[np.cos(ph_val) + 2 * la_val * np.cos(k_val) * np.sin(ph_val),
                   -np.sin(ph_val) + 2 * la_val * np.cos(k_val) * np.cos(ph_val)],
                  [np.sin(ph_val), np.cos(ph_val)]])
    tr = np.trace(M)
    check(abs(np.linalg.det(M) - 1) < TOL, "sample Gamma_hat(k) has det = 1 (setup check)")
    alpha_val = np.arccos(np.clip(tr / 2, -1, 1))
    Mt = np.eye(2)
    for tt in range(1, 11):
        Mt = Mt @ M
        formula = ((np.sin(tt * alpha_val) / np.sin(alpha_val)) * M
                   - (np.sin((tt - 1) * alpha_val) / np.sin(alpha_val)) * np.eye(2))
        check(np.allclose(Mt, formula, atol=1e-8),
              f"Gamma_hat(k)^t = (sin t alpha/sin alpha) Gamma_hat - (sin(t-1)alpha/sin alpha)*1, "
              f"t={tt}, sample phi={ph_val:.3f}, lam={la_val:.3f}, k={k_val:.3f}")

# ============================= 5. Lemma 4.6: the projectors P_k, P_k-bar =============================
for ph_val, la_val, k_val in test_points:
    M = np.array([[np.cos(ph_val) + 2 * la_val * np.cos(k_val) * np.sin(ph_val),
                   -np.sin(ph_val) + 2 * la_val * np.cos(k_val) * np.cos(ph_val)],
                  [np.sin(ph_val), np.cos(ph_val)]], dtype=complex)
    tr = np.trace(M).real
    alpha_val = np.arccos(np.clip(tr / 2, -1, 1))
    sin_a = np.sin(alpha_val)
    P = 0.5 * (np.eye(2) + 1j * (np.cos(alpha_val) * np.eye(2) - M) / sin_a)
    Pbar = np.eye(2) - P
    check(np.allclose(P @ P, P, atol=1e-8), "P_k is idempotent, P_k^2 = P_k (Lemma 4.6)")
    check(np.allclose(Pbar, P.conj(), atol=1e-8), "P_k-bar = complex conjugate of P_k (Lemma 4.6)")
    check(np.allclose(P @ Pbar, 0, atol=1e-8), "P_k P_k-bar = 0 (disjoint eigenspaces)")
    check(np.allclose(P + Pbar, np.eye(2), atol=1e-8), "P_k + P_k-bar = 1")
    recon = (np.exp(1j * alpha_val) * P + np.exp(-1j * alpha_val) * Pbar)
    check(np.allclose(recon, M, atol=1e-8),
          "Gamma_hat(k) = e^{i alpha} P_k + e^{-i alpha} P_k-bar (4.21)")

# ============================= 6. eps_hat(k) (4.28) and Thm. 4.8, F3 =============================
def eps_hat(ph_val, la_val, k_val):
    M = np.array([[np.cos(ph_val) + 2 * la_val * np.cos(k_val) * np.sin(ph_val),
                   -np.sin(ph_val) + 2 * la_val * np.cos(k_val) * np.cos(ph_val)],
                  [np.sin(ph_val), np.cos(ph_val)]])
    tr = np.trace(M)
    alpha_val = np.arccos(np.clip(tr / 2, -1, 1))
    sin_a = np.sin(alpha_val)
    Om = np.array([[0.0, 1.0], [-1.0, 0.0]])
    return -Om @ (np.cos(alpha_val) * np.eye(2) - M) / sin_a, M, alpha_val


for ph_val, la_val, k_val in test_points:
    eps, M, alpha_val = eps_hat(ph_val, la_val, k_val)
    check(np.allclose(eps, eps.T, atol=1e-8), "eps_hat(k) is real symmetric (4.28)")
    check(np.allclose(M.T @ eps @ M, eps, atol=1e-8),
          "Gamma_hat(k)^T eps_hat(k) Gamma_hat(k) = eps_hat(k), invariance under the dynamics")
    eps_mk, M_mk, _ = eps_hat(ph_val, la_val, -k_val)
    check(np.allclose(eps_mk, eps, atol=1e-8), "eps_hat(-k) = eps_hat(k)")
    Om = np.array([[0.0, 1.0], [-1.0, 0.0]])
    check(np.allclose((Om @ eps) @ (Om @ eps), -np.eye(2), atol=1e-8),
          "(Omega eps_hat(k))^2 = -1, i.e. eps_hat(k) corresponds to a pure state, det = 1 "
          "purity criterion (Lemma 4.5(ii))")
    ev_plus = np.linalg.eigvalsh(eps + 1j * Om)
    ev_minus = np.linalg.eigvalsh(eps - 1j * Om)
    # Discrepancy noted for conventions-q4a.md: for real symmetric eps_hat, eps_hat + i Omega
    # >= 0 iff eps_hat - i Omega >= 0 ALWAYS (Q3 conventions.md item 2: complex conjugation
    # preserves the real eigenvalues of a Hermitian matrix), checked here on both signs of phi;
    # they are not an independent choice, unlike a literal reading of the thesis's two-branch
    # display for eps_hat(k) might suggest. So (4.28)'s single eps_hat formula (used throughout,
    # with no phi-branch) satisfies the state condition (BOTH signs at once) for 0 < phi < pi,
    # and -(4.28)'s eps_hat does so for -pi < phi < 0.
    check(np.allclose(ev_plus, ev_minus, atol=1e-6),
          "eps_hat(k) + i Omega and eps_hat(k) - i Omega have the SAME eigenvalues (Q3 item 2's "
          "general fact for real symmetric eps_hat), so the state condition's sign is not an "
          "independent choice for the two terms")
    if 0 < ph_val < np.pi:
        check(ev_plus.min() > -1e-8 and ev_minus.min() > -1e-8,
              "eps_hat(k) +- i Omega >= 0 (both, simultaneously) for 0 < phi < pi (Thm. 4.8, "
              "using (4.28)'s formula directly with no phi-branch)")
    elif -np.pi < ph_val < 0:
        check(ev_plus.min() < -1e-8 and ev_minus.min() < -1e-8,
              "eps_hat(k) +- i Omega is NOT >= 0 (either sign) for -pi < phi < 0 with (4.28)'s "
              "formula as printed; -eps_hat(k) is the one satisfying the state condition there "
              "(the thesis's phi-branch on eps_hat itself, not on the +-i Omega choice)")

    # thesis p. 88: tr[i sigma_s P_k] = (sin phi - lam cos k cos phi)/sin alpha(k)
    sin_a = np.sin(alpha_val)
    P = 0.5 * (np.eye(2) + 1j * (np.cos(alpha_val) * np.eye(2) - M) / sin_a)
    tr_iOmegaP = np.trace(1j * Om @ P)
    predicted_tr = (np.sin(ph_val) - la_val * np.cos(k_val) * np.cos(ph_val)) / sin_a
    check(abs(tr_iOmegaP.real - predicted_tr) < 1e-7 and abs(tr_iOmegaP.imag) < 1e-7,
          "tr[i sigma_s P_k] = (sin phi - lam cos k cos phi)/sin alpha(k), exactly the thesis's "
          "p. 88 formula, and real")
    check((predicted_tr > 0) == (0 < ph_val < np.pi),
          "the nonzero eigenvalue of i sigma_s P_k is positive for 0<phi<pi and negative for "
          "-pi<phi<0, matching the state-condition sign of Thm. 4.8's proof")

# ---- F3: completeness. The invariant symmetric forms of an elliptic Gamma_hat(k) are a
# 1-dimensional space, spanned by eps_hat(k). Set up the linear map S |-> Gamma_hat^T S Gamma_hat
# - S on the 3-dimensional space of real symmetric 2x2 matrices, and check its kernel is exactly
# 1-dimensional and contains eps_hat(k).
basis = [np.array([[1.0, 0.0], [0.0, 0.0]]),
         np.array([[0.0, 1.0], [1.0, 0.0]]),
         np.array([[0.0, 0.0], [0.0, 1.0]])]
for ph_val, la_val, k_val in test_points:
    eps, M, _ = eps_hat(ph_val, la_val, k_val)
    A = np.zeros((3, 3))
    for j, B in enumerate(basis):
        img = M.T @ B @ M - B
        A[:, j] = [img[0, 0], img[0, 1], img[1, 1]]
    rank = np.linalg.matrix_rank(A, tol=1e-8)
    check(rank == 2,
          "the invariance map S -> Gamma_hat^T S Gamma_hat - S on symmetric 2x2 matrices has "
          "rank 2 (F3: a 1-dimensional kernel), for an elliptic Gamma_hat(k) in the regime")
    # the kernel (from SVD) is spanned by a single vector; check it is parallel to eps_hat(k)
    _, _, Vt = np.linalg.svd(A)
    kernel_vec = Vt[-1]
    eps_vec = np.array([eps[0, 0], eps[0, 1], eps[1, 1]])
    check(np.allclose(kernel_vec / np.linalg.norm(kernel_vec),
                       eps_vec / np.linalg.norm(eps_vec), atol=1e-6) or
          np.allclose(kernel_vec / np.linalg.norm(kernel_vec),
                       -eps_vec / np.linalg.norm(eps_vec), atol=1e-6),
          "the 1-dimensional kernel of the invariance map is spanned by eps_hat(k) (F3, "
          "completeness: every invariant symmetric form is a multiple g(k) eps_hat(k))")

# ---- F3/Thm. 4.8: the state-condition threshold is g >= 1 exactly.
# g eps_hat(k) + i Omega (for 0<phi<pi; the mirror case uses -i Omega) is PSD iff g >= 1,
# since eps_hat + i Omega is rank-one PSD (2 i Omega P_k) and g eps_hat + i Omega =
# (g-1) eps_hat + (eps_hat + i Omega); scan g on both sides of 1 and check the PSD threshold.
for ph_val, la_val, k_val in test_points:
    if not (0 < ph_val < np.pi):
        continue
    eps, M, _ = eps_hat(ph_val, la_val, k_val)
    Om = np.array([[0.0, 1.0], [-1.0, 0.0]])
    for g_val in [0.5, 0.9, 0.999]:
        ev = np.linalg.eigvalsh(g_val * eps + 1j * Om)
        check(ev.min() < -1e-8, f"g eps_hat(k) + i Omega is NOT PSD for g={g_val} < 1 (F3: "
              "the state-condition threshold g >= 1 is sharp)")
    for g_val in [1.0, 1.001, 1.5, 3.0]:
        ev = np.linalg.eigvalsh(g_val * eps + 1j * Om)
        check(ev.min() > -1e-7, f"g eps_hat(k) + i Omega IS PSD for g={g_val} >= 1 "
              "(Thm. 4.8's stationary states, g(k) >= 1)")

# ============================= 7. F1: lam sin phi = 0 gives no decay =============================
# Onsite rule (neighbourhood {0} exactly at lam = 0): gamma_t(x) = Gamma_0^t)^T gamma_0(x)
# Gamma_0^t, exactly (no k-integral needed since the rule has no nearest-neighbour part).
# Take gamma_0(0) = diag(s, 1/s), s != 1 (a squeezed, non-vacuum product state), and
# phi = pi/3 so Gamma_0^6 = rotation(2 pi) = 1 exactly: gamma_t(0) is then exactly periodic
# in t with period 6, and NOT constant over one period, so it does not converge as t -> oo.
s_val = sp.Rational(2)
gamma0_00 = sp.diag(s_val, 1 / s_val)
G0_pi3 = rotation(sp.pi / 3)


def gamma_t0(tt):
    Gt = G0_pi3 ** tt
    return sp.simplify(Gt.T * gamma0_00 * Gt)


gamma_t0_vals = [gamma_t0(tt) for tt in range(7)]
# rotation(pi/3)^3 = rotation(pi) = -1, and conjugation by -1 is trivial, so the period of
# gamma_t(0) = rotation(t pi/3)^T gamma_0(0) rotation(t pi/3) is 3, not 6.
check(gamma_t0_vals[0] == gamma_t0_vals[3],
      "F1 (lam sin phi = 0): gamma_t(0) is exactly periodic in t (period 3 at phi=pi/3, an "
      "onsite rotation, since rotation(pi/3)^3 = -1 and conjugation by -1 is trivial), "
      "gamma_0(0) = gamma_3(0), exact")
check(gamma_t0_vals[0] == gamma_t0_vals[6],
      "F1: gamma_0(0) = gamma_6(0) too (period 3 divides 6), exact")
for tt in [1, 2]:
    check(gamma_t0_vals[tt] != gamma_t0_vals[0],
          f"F1: gamma_t(0) at t={tt} differs from t=0 within the period -- genuine oscillation, "
          "not convergence to a fixed limit (no decay when lam sin phi = 0)")

# ============================= 8. Finding 2 =============================
# 8(a): the leapfrog symbol trace is 2 cos k - m^2 (both F and F^{-1}, QCALean's leapfrog_trace);
# for every real m^2 some k has |tr| >= 2.
tr_at_pi = -2 - m2
tr_at_0 = 2 - m2
for m2_val in [sp.Integer(0), sp.Integer(1), sp.Rational(3, 2), sp.Integer(5)]:
    val = tr_at_pi.subs(m2, m2_val)
    check(sp.simplify(sp.Abs(val) - 2) >= 0,
          f"finding 2: |tr Gamma_hat(pi)| = |-2-m2| >= 2 at m2={m2_val} >= 0 (witness k=pi)")
for m2_val in [sp.Integer(0), sp.Integer(-1), sp.Rational(-3, 2), sp.Integer(-5)]:
    val = tr_at_0.subs(m2, m2_val)
    check(sp.simplify(sp.Abs(val) - 2) >= 0,
          f"finding 2: |tr Gamma_hat(0)| = |2-m2| >= 2 at m2={m2_val} <= 0 (witness k=0)")
# and generically, exactly: 2+m2 >= 2 for m2 >= 0, and 2-m2 = 2+|m2| >= 2 for m2 <= 0.
m2s = sp.Symbol('m2s', nonnegative=True)
check(sp.simplify((2 + m2s) - 2) >= 0, "2 + m2 >= 2 for m2 >= 0 (symbolic, nonnegative m2)")
m2n = sp.Symbol('m2n', nonpositive=True)
check(sp.simplify((2 - m2n) - 2) >= 0, "2 - m2 >= 2 for m2 <= 0 (symbolic, nonpositive m2)")

# 8(b): leapfrogInvSymbol 0 = rotationSymbol(pi/2, 1) exactly (the massless inverse leapfrog is
# the example system on the boundary lam = f_crit).
leapfrogInvShift = sp.Matrix([[1, 0], [0, 0]])
leapfrogInvCentre_0 = sp.Matrix([[0, -1], [1, 0]])  # m2 = 0 in [[-m2,-1],[1,0]]
rot_pi2 = rotation(sp.pi / 2)
check(sp.simplify(rot_pi2 - leapfrogInvCentre_0) == sp.zeros(2, 2),
      "finding 2(b): rotation(pi/2) = leapfrogInvCentre(0) = [[0,-1],[1,0]] exactly, matching "
      "Lean's leapfrogInvSymbol at m2=0 against rotationSymbol(pi/2, 1)'s l0 coefficient")
r_pi2 = sp.Matrix([[sp.sin(sp.pi / 2), sp.cos(sp.pi / 2)]])  # momentum row of rotation(pi/2)
e1 = sp.Matrix([[1], [0]])
lp_pi2_lam1 = e1 * (1 * r_pi2)
check(sp.simplify(lp_pi2_lam1 - leapfrogInvShift) == sp.zeros(2, 2),
      "finding 2(b): lam * e1 * r^T at phi=pi/2, lam=1 = [[1,0],[0,0]] = leapfrogInvShift "
      "exactly, matching Lean's leapfrogInvSymbol at m2=0 against rotationSymbol(pi/2, 1)'s "
      "l+ = l- coefficient. So leapfrogInvSymbol 0 = rotationSymbol (pi/2) 1 exactly (Lean "
      "statement, item 8(b) of the plan): the massless inverse leapfrog sits exactly on the "
      "boundary phi=pi/2, lam=f_crit(pi/2)=1 of the nonsqueezing regime.")
fcrit_pi2 = (1 - sp.cos(sp.pi / 2)) / sp.sin(sp.pi / 2)
check(sp.simplify(fcrit_pi2 - 1) == 0,
      "finding 2(b): f_crit(pi/2) = 1 = lam exactly, so phi=pi/2, lam=1 sits ON the regime "
      "boundary (degenerate case of finding 2, not in the strict open regime)")

# ======= 9. ExampleRegime => |lam cos phi| < |sin phi| (needed for sign_sin_sub_eq) =======
# SketchQ4a.lean's `sign_sin_sub_eq` states, under `ExampleRegime phi lam`
# (|cos phi| + |lam * sin phi| < 1, lam * sin phi != 0), that
#   sign(sin phi - lam cos k cos phi) = sign(sin phi)   for all k.
# Since |cos k| <= 1, this holds for every k as soon as |lam cos phi| < |sin phi| (so that
# lam cos k cos phi stays strictly inside (-|sin phi|, |sin phi|) and cannot flip or kill the
# sign of sin phi - lam cos k cos phi). This item checks that ExampleRegime implies exactly
# this sufficient condition |lam cos phi| < |sin phi|.
#
# Exact proof (sympy-checked algebraic identity below): write c = |cos phi|, s = |sin phi|,
# so c^2 + s^2 = 1. ExampleRegime gives c + |lam| s < 1.
#   - s = 0 is impossible in the regime: s = 0 forces c = 1, and then c + |lam| s = 1 < 1 is
#     false. So s > 0 throughout the regime, and c < 1 (else c + |lam| s >= 1).
#   - From c + |lam| s < 1: |lam| < (1 - c) / s.
#   - Multiply by c >= 0: |lam| c < (1 - c) c / s = c(1-c)/s.
#   - c(1-c) < (1-c)(1+c) = 1 - c^2 = s^2 exactly (dividing by 1-c > 0, this is c < 1 + c,
#     immediate). So c(1-c)/s < s^2 / s = s.
#   - Hence |lam| c < s, i.e. |lam cos phi| < |sin phi|.
c_sym = sp.Symbol('c_sym', nonnegative=True)
identity_lhs = (1 - c_sym) * (1 + c_sym) - c_sym * (1 - c_sym)
check(sp.simplify(identity_lhs - (1 - c_sym)) == 0,
      "algebraic step: (1-c)(1+c) - c(1-c) = 1-c exactly (c = |cos phi|), the identity "
      "used to prove |lam cos phi| < |sin phi| from the ExampleRegime bound c + |lam| s < 1")

# 9(a) exact endpoints/witnesses (sympy).
# cos phi = 0 case: c = 0, s = |sin phi| = 1 (only possibility), so the regime is |lam| < 1,
# and the conclusion |lam * 0| < 1 holds for every lam whatsoever (trivial but must be checked,
# since c = 0 makes the general division-by-c argument above vacuous).
for phi_val in [sp.pi / 2, -sp.pi / 2]:
    c_val = sp.Abs(sp.cos(phi_val))
    s_val = sp.Abs(sp.sin(phi_val))
    check(sp.simplify(c_val) == 0 and sp.simplify(s_val) == 1,
          f"cos phi = 0 case, phi={phi_val}: |cos phi| = 0, |sin phi| = 1 exactly")
    for lam_val in [sp.Rational(0), sp.Rational(1, 2), sp.Rational(99, 100), sp.Integer(-5),
                    sp.Integer(1000000)]:
        in_regime = bool(c_val + sp.Abs(lam_val * sp.sin(phi_val)) < 1)
        concl = bool(sp.Abs(lam_val * sp.cos(phi_val)) < sp.Abs(sp.sin(phi_val)))
        # regime only holds for |lam| < 1 here, but the conclusion (0 < 1) holds regardless
        check(concl, f"cos phi=0, phi={phi_val}, lam={lam_val}: |lam cos phi| = 0 < 1 = "
              "|sin phi| always, exact (cos phi = 0 case of the implication)")
        if in_regime:
            check(concl, f"cos phi=0, phi={phi_val}, lam={lam_val}: in ExampleRegime and "
                  "conclusion holds, exact")

# Rational witness away from cos phi = 0: use a Pythagorean angle with cos phi = 3/5,
# sin phi = 4/5 (exact rationals, avoiding pi/3-type irrational sin/cos).
c35, s35 = sp.Rational(3, 5), sp.Rational(4, 5)
for lam_val in [sp.Rational(0), sp.Rational(1, 10), sp.Rational(2, 3),
                sp.Rational(4, 3) - sp.Rational(1, 1000)]:
    in_regime = bool(c35 + sp.Abs(lam_val * s35) < 1)
    concl = bool(sp.Abs(lam_val * c35) < s35)
    if in_regime:
        check(concl, f"Pythagorean witness cos phi=3/5, sin phi=4/5, lam={lam_val}: "
              "ExampleRegime holds and |lam cos phi| < |sin phi| holds, exact rational check")

# 9(b) dense deterministic numeric scan over phi in (-pi, pi), lam over a wide range covering
# and exceeding the regime, including phi with cos phi = 0 (phi = +-pi/2, included exactly on
# the grid below since N_PHI is chosen so pi/2 lands on a grid point) and near-boundary points
# (lam chosen just inside f_crit(phi) for each phi).
N_PHI = 2001  # odd, and pi/2 is exactly representable: phi_i = -pi + i * (2pi/2000)
phis = np.linspace(-np.pi, np.pi, N_PHI, endpoint=True)
assert np.any(np.isclose(phis, np.pi / 2, atol=1e-12))
assert np.any(np.isclose(phis, 0.0, atol=1e-12))
lam_grid = np.linspace(-50.0, 50.0, 401)  # wide deterministic grid, well beyond any f_crit

n_regime_checked = 0
n_boundary_checked = 0
for ph_val in phis:
    c_val = abs(np.cos(ph_val))
    s_val = abs(np.sin(ph_val))
    for la_val in lam_grid:
        lhs = c_val + abs(la_val * s_val)
        if lhs < 1.0 - 1e-12:  # strictly inside ExampleRegime's inequality (numeric margin)
            rhs_ok = abs(la_val * c_val) < s_val + 1e-12  # tiny fp slack, still must hold
            assert rhs_ok, (f"COUNTEREXAMPLE to |cos phi|+|lam sin phi|<1 => |lam cos phi|<"
                             f"|sin phi| at phi={ph_val}, lam={la_val}")
            n_regime_checked += 1
    # near-boundary points: lam = f_crit(phi) * (1 - eps), eps small, deterministic.
    if s_val > 1e-9:
        fcrit = (1.0 - c_val) / s_val
        for eps in [1e-3, 1e-6, 1e-9]:
            la_in = fcrit * (1.0 - eps)
            lhs_in = c_val + abs(la_in * s_val)
            if lhs_in < 1.0:
                assert abs(la_in * c_val) < s_val + 1e-9, (
                    f"COUNTEREXAMPLE near boundary (inside), phi={ph_val}, lam={la_in}")
                n_boundary_checked += 1
check(n_regime_checked > 5000,
      f"dense numeric scan: {n_regime_checked} (phi, lam) grid points strictly inside "
      "ExampleRegime's |cos phi| + |lam sin phi| < 1 (including phi = +-pi/2, i.e. cos phi = 0, "
      "and phi = 0, +-pi) all satisfy |lam cos phi| < |sin phi|, no counterexample found "
      "(a genuine counterexample would fire the assert above, not just fail a soft check)")
check(n_boundary_checked > 0,
      f"near-boundary scan: {n_boundary_checked} points just inside the regime "
      "(lam = f_crit(phi)*(1-eps), eps in {1e-3,1e-6,1e-9}) also satisfy |lam cos phi| < "
      "|sin phi|, consistent with the exact proof above")

# 9(c) does the implication FAIL just outside ExampleRegime? Record the answer either way.
# At phi with a small |sin phi|, a large lam makes |cos phi| + |lam sin phi| >= 1 (well outside
# the regime) while |lam cos phi| >> |sin phi|, so the conclusion |lam cos phi| < |sin phi|
# DOES fail outside the regime, at least for some (phi, lam) -- the regime hypothesis is doing
# real work, not slack.
phi_small = 0.01
lam_big = 1000.0
c_small, s_small = np.cos(phi_small), np.sin(phi_small)
lhs_outside = abs(c_small) + abs(lam_big * s_small)
concl_outside = abs(lam_big * c_small) < abs(s_small)
check(lhs_outside >= 1.0, "witness for 9(c): phi=0.01, lam=1000 lies OUTSIDE ExampleRegime's "
      f"inequality ({lhs_outside:.4f} >= 1)")
check(not concl_outside, "witness for 9(c): at this outside point |lam cos phi| < |sin phi| "
      "FAILS (|lam cos phi| approx 999.95 >= |sin phi| approx 0.01) -- so the implication "
      "|cos phi|+|lam sin phi|<1 => |lam cos phi|<|sin phi| genuinely needs the ExampleRegime "
      "hypothesis and is not true unconditionally just outside it. Recorded: the implication "
      "FAILS outside the regime (at least at this witness); see conventions-q4a.md.")
# but also record: failure is not universal just outside -- e.g. at phi=pi/2 (cos phi=0) the
# conclusion 0 < |sin phi| holds for EVERY lam, regime or not, so "just outside" does not
# uniformly break the conclusion; it is the c + |lam| s >= 1 boundary together with c > 0 that
# produces counterexamples (as in the phi=0.01 witness), not proximity to the boundary alone.
lam_just_outside_pi2 = 1.5  # phi=pi/2: regime is |lam| < 1, so lam=1.5 is just outside
concl_pi2_outside = abs(lam_just_outside_pi2 * np.cos(np.pi / 2)) < abs(np.sin(np.pi / 2))
check(concl_pi2_outside, "at phi=pi/2 (cos phi=0), the conclusion 0 < |sin phi| = 1 still "
      "holds even just outside the regime (lam=1.5 > f_crit(pi/2)=1) -- the implication's "
      "converse is not simply 'outside the regime it fails': failure needs cos phi != 0 too "
      "(see the phi=0.01 witness above), recorded in conventions-q4a.md")

# ================== 10. Eq. (2) (\eqref{eq:twobytwo}) of Q4a.tex, general 2x2 A ==================
# A^T Omega A = (det A) Omega  and  Omega A + A^T Omega = (tr A) Omega, for every real or
# complex 2x2 A = [[a,b],[c,d]] (symbolic, exact).
a_s, b_s, c_s, d_s = sp.symbols('a_s b_s c_s d_s')
A_sym = sp.Matrix([[a_s, b_s], [c_s, d_s]])
check(sp.simplify(A_sym.T * Omega * A_sym - A_sym.det() * Omega) == sp.zeros(2, 2),
      "Q4a.tex eq. (2): A^T Omega A = (det A) Omega, exact, for a general symbolic 2x2 A")
check(sp.simplify(Omega * A_sym + A_sym.T * Omega - A_sym.trace() * Omega) == sp.zeros(2, 2),
      "Q4a.tex eq. (2): Omega A + A^T Omega = (tr A) Omega, exact, for a general symbolic 2x2 A")

# ============ 11. Example (running example, Sec. 3, ex:running): phi = pi/2 ============
# Gamma_hat(k) = [[2 lam cos k, -1], [1, 0]] exactly at phi = pi/2 (c=0, s=1).
Ghat_pi2 = GammaHat(sp.pi / 2, lam, k)
check(sp.simplify(Ghat_pi2 - sp.Matrix([[2 * lam * sp.cos(k), -1], [1, 0]])) == sp.zeros(2, 2),
      "Q4a.tex Example (ex:running), phi=pi/2: Gamma_hat(k) = [[2 lam cos k, -1],[1,0]] exactly")

# ============ 12. Example (running example, ex:running-stat): explicit eps_hat(k) at phi=pi/2 ==
# eps_hat(k) = -Omega (cos alpha - Gamma_hat(k)) / sin alpha, evaluated symbolically at
# phi = pi/2 (cos phi = 0, sin phi = 1): tr Gamma_hat = 2 lam cos k, so
# cos alpha = lam cos k, sin alpha = sqrt(1 - lam^2 cos^2 k) (regime: |lam cos k| < 1 there).
sin_alpha_pi2 = sp.sqrt(1 - lam ** 2 * sp.cos(k) ** 2)
eps_pi2_formula = -Omega * (lam * sp.cos(k) * sp.eye(2) - Ghat_pi2) / sin_alpha_pi2
eps_pi2_thesis = (sp.Matrix([[1, -lam * sp.cos(k)], [-lam * sp.cos(k), 1]])
                   / sp.sqrt(1 - lam ** 2 * sp.cos(k) ** 2))
check(sp.simplify(eps_pi2_formula - eps_pi2_thesis) == sp.zeros(2, 2),
      "Q4a.tex Example (ex:running-stat) and Sec. 6 (\"In the running example\"): "
      "eps_hat(k) at phi=pi/2 equals (1-lam^2 cos^2 k)^{-1/2} [[1,-lam cos k],[-lam cos k,1]] "
      "exactly, matching (4.28) evaluated at phi=pi/2")
check(sp.simplify(eps_pi2_thesis.det() - 1) == 0,
      "Q4a.tex Sec. 6: det eps_hat(k) = 1 exactly at phi=pi/2 (\"whose determinant is visibly 1\")")

# f_crit(pi/2) = 1 exactly (already checked at item 8(b) as fcrit_pi2; restated here against the
# running example's own regime statement 0 < |lam| < 1, ex:running-stat).
check(sp.simplify((1 - sp.cos(sp.pi / 2)) / sp.sin(sp.pi / 2) - 1) == 0,
      "Q4a.tex ex:running-stat: f_crit(pi/2) = 1, so \"0 < |lam| < 1\" is exactly the strict "
      "regime at phi=pi/2 (matches Prop. finding2(c)'s fcrit(pi/2)=1)")

# ==================== 13. Threshold proposition (prop:threshold), general symmetric E ====================
# det(g E + i Omega) = g^2 det E - 1, for a general real symmetric E = [[e1,e2],[e2,e3]] and g in R.
e1_s, e2_s, e3_s, g_s = sp.symbols('e1_s e2_s e3_s g_s', real=True)
E_sym = sp.Matrix([[e1_s, e2_s], [e2_s, e3_s]])
gE_iOmega = g_s * E_sym + sp.I * Omega
check(sp.simplify(gE_iOmega.det() - (g_s ** 2 * E_sym.det() - 1)) == 0,
      "Q4a.tex Proposition (prop:threshold): det(g E + i Omega) = g^2 det E - 1, exact, for a "
      "general symbolic real symmetric 2x2 E")
# The case det E = 1 (E = eps_hat(k)), as stated in the proposition: det(g E + i Omega) = g^2 - 1.
det_E1_case = (g_s ** 2 * 1 - 1)
check(sp.simplify(det_E1_case - (g_s ** 2 - 1)) == 0,
      "Q4a.tex prop:threshold, det E = 1: g^2 det E - 1 = g^2 - 1 exactly")

# =============== 14. Corollary 26 identification (Q3 purity criterion), g=1 pure state ===============
# The text after Theorem (thm:stationary) identifies g == 1 (eps_hat itself) as the pure
# stationary state, det Gamma_hat(k) = 1, via Q3's Corollary 26 purity criterion; every other
# stationary state g eps_hat(k) has det = g^2 > 1 for g > 1. Check det(g * eps_hat(k)) = g^2 * 1
# = g^2 exactly, symbolically, using eps_hat's det = 1 (item 12 above and item 6's numeric check).
g_eps_pi2 = g_s * eps_pi2_thesis
check(sp.simplify(g_eps_pi2.det() - g_s ** 2) == 0,
      "Q4a.tex, text after thm:stationary (Corollary 26 identification): det(g eps_hat(k)) = "
      "g^2 exactly (det eps_hat(k) = 1), so g=1 is the pure stationary state (det = 1, Q3's "
      "Corollary 26 purity criterion) and every g > 1 has det = g^2 > 1")
for g_val in [sp.Rational(3, 2), sp.Integer(2), sp.Rational(5, 4)]:
    check(sp.simplify(g_val ** 2 - 1) > 0,
          f"Q4a.tex: for g={g_val} > 1, det(g eps_hat(k)) = g^2 = {g_val**2} > 1 exactly")
check(sp.simplify(sp.Integer(1) ** 2 - 1) == 0,
      "Q4a.tex: for g=1, det(g eps_hat(k)) = 1 exactly (the pure state)")

print(f"check_q4a: {count} checks passed")
