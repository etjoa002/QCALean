/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.CellForm
import QCALean.Bosonic.Examples
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Basic.Real.Sign

/-!
# The example system

Milestone Q4a. Krüger's example system (thesis §4.2.4): the nearest-neighbour rule with on-site
rotation `Γ₀` by `φ` and coupling `λ Γ±`, `Γ± = [[sin φ, cos φ], [0, 0]]`. Its Fourier symbol is
the real matrix `Γ̂(k) = Γ₀ + 2λ cos k Γ±` (4.18), of determinant one and trace
`2(cos φ + λ cos k sin φ)`. In the regime `|cos φ| + |λ sin φ| < 1`, `λ sin φ ≠ 0`, every mode is
a rotation by
the angle `α(k) = arccos(cos φ + λ cos k sin φ)` (4.19)–(4.20); the powers of `Γ̂(k)` have a
closed form, and the spectral projectors of Lemma 4.6 decompose them (4.21)–(4.24). The massless
inverse leapfrog is the example system on the boundary of the regime.

## Main definitions and results

* `QCALean.Bosonic.exampleSymbol`, `QCALean.Bosonic.fourierSymbol_rotationSymbol`: (4.18).
* `QCALean.Bosonic.ExampleRegime`, `QCALean.Bosonic.lt_one_iff_forall_abs_trace_lt`,
  `QCALean.Bosonic.lt_one_iff_abs_lt_fcrit`: the regime and (4.20).
* `QCALean.Bosonic.alpha`, `QCALean.Bosonic.hasDerivAt_alpha`: the rotation angle (4.19).
* `QCALean.Bosonic.pow_eq_chebyshev`, `QCALean.Bosonic.exampleSymbol_pow`: powers.
* `QCALean.Bosonic.projP`, `QCALean.Bosonic.exampleSymbol_eq_projP`: Lemma 4.6 and (4.24).
* `QCALean.Bosonic.leapfrogInvSymbol_zero_eq`: the massless inverse leapfrog.
-/

open LinearAQFT QCALean.Core Matrix Gaussian
open scoped ComplexConjugate

namespace QCALean.Bosonic

/-! ### The symbol (4.18) -/

section Symbol

/-- The Fourier symbol of a reflection-symmetric nearest-neighbour rule,
`ℓ e^{ik} + ℓ₀ + ℓ e^{−ik} = ℓ₀ + 2 cos k ℓ`. -/
theorem fourierSymbol_nnSymbol_symm (l0 l : Matrix Cell Cell ℝ) (k : ℝ) :
    fourierSymbol k (nnSymbol l l0 l) = (l0 + (2 * Real.cos k) • l).map Complex.ofReal := by
  ext i j
  simp only [nnSymbol, fourierSymbol_add, fourierSymbol_mono, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Int.cast_neg, Int.cast_one, Int.cast_zero,
    mul_zero, zero_mul, Complex.exp_zero, one_mul, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_cos, Complex.cos, Complex.ofReal_ofNat]
  ring_nf

/-- The coupling matrix `Γ± = e₁ rᵀ = [[sin φ, cos φ], [0, 0]]` of (4.18), `r` the momentum row
of the rotation. (notes: `def:es-example`) -/
noncomputable def gammaPm (φ : ℝ) : Matrix Cell Cell ℝ := vecMulVec e1 (rotation φ pIdx)

/-- Milestone Q4a, Definition 6: the real Fourier symbol `Γ̂(k) = Γ₀ + 2λ cos k Γ±` (4.18).
(notes: `def:es-example`) -/
noncomputable def exampleSymbol (φ lam k : ℝ) : Matrix Cell Cell ℝ :=
  rotation φ + (2 * lam * Real.cos k) • gammaPm φ

/-- Milestone Q4a, Proposition 7(a): the Fourier symbol of the example rule is `Γ̂(k)`.
(notes: `prop:es-symbol`) -/
theorem fourierSymbol_rotationSymbol (φ lam k : ℝ) :
    fourierSymbol k (rotationSymbol φ lam) = (exampleSymbol φ lam k).map Complex.ofReal := by
  rw [rotationSymbol, fourierSymbol_nnSymbol_symm, exampleSymbol, gammaPm, vecMulVec_smul,
    smul_smul, mul_right_comm]

/-- Milestone Q4a, Definition 6: the entries of `Γ̂(k)`. -/
theorem exampleSymbol_apply (φ lam k : ℝ) :
    exampleSymbol φ lam k = Matrix.of fun i j => match i, j with
      | Sum.inl _, Sum.inl _ => Real.cos φ + 2 * lam * Real.cos k * Real.sin φ
      | Sum.inl _, Sum.inr _ => -Real.sin φ + 2 * lam * Real.cos k * Real.cos φ
      | Sum.inr _, Sum.inl _ => Real.sin φ
      | Sum.inr _, Sum.inr _ => Real.cos φ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [exampleSymbol, gammaPm, rotation, vecMulVec_apply, e1]

@[simp] theorem exampleSymbol_qq (φ lam k : ℝ) :
    exampleSymbol φ lam k qIdx qIdx = Real.cos φ + 2 * lam * Real.cos k * Real.sin φ := by
  rw [exampleSymbol_apply]; rfl
@[simp] theorem exampleSymbol_qp (φ lam k : ℝ) :
    exampleSymbol φ lam k qIdx pIdx = -Real.sin φ + 2 * lam * Real.cos k * Real.cos φ := by
  rw [exampleSymbol_apply]; rfl
@[simp] theorem exampleSymbol_pq (φ lam k : ℝ) : exampleSymbol φ lam k pIdx qIdx = Real.sin φ := by
  rw [exampleSymbol_apply]; rfl
@[simp] theorem exampleSymbol_pp (φ lam k : ℝ) : exampleSymbol φ lam k pIdx pIdx = Real.cos φ := by
  rw [exampleSymbol_apply]; rfl

/-- Milestone Q4a, Proposition 7(b): `Γ̂(−k) = Γ̂(k)`. (notes: `prop:es-symbol`) -/
theorem exampleSymbol_neg (φ lam k : ℝ) : exampleSymbol φ lam (-k) = exampleSymbol φ lam k := by
  rw [exampleSymbol, exampleSymbol, Real.cos_neg]

/-- Milestone Q4a, Proposition 7(c): `det Γ̂(k) = 1`. (notes: `prop:es-symbol`) -/
theorem det2_exampleSymbol (φ lam k : ℝ) : det2 (exampleSymbol φ lam k) = 1 := by
  simp only [det2, exampleSymbol_qq, exampleSymbol_qp, exampleSymbol_pq, exampleSymbol_pp]
  linear_combination Real.sin_sq_add_cos_sq φ

/-- Milestone Q4a, Proposition 7(c): `tr Γ̂(k) = 2(cos φ + λ cos k sin φ)`.
(notes: `prop:es-symbol`) -/
theorem trace_exampleSymbol (φ lam k : ℝ) :
    (exampleSymbol φ lam k).trace = 2 * (Real.cos φ + lam * Real.cos k * Real.sin φ) := by
  rw [trace_cell, exampleSymbol_qq, exampleSymbol_pp]
  ring

/-- Milestone Q4a, Proposition 7(c): `Γ̂(k)ᵀ Ω Γ̂(k) = Ω`. (notes: `prop:es-symbol`) -/
theorem exampleSymbol_symplectic (φ lam k : ℝ) :
    (exampleSymbol φ lam k)ᵀ * omega * exampleSymbol φ lam k = omega := by
  rw [transpose_mul_omega_mul_self, det2_exampleSymbol, one_smul]

/-- Milestone Q4a, Proposition 7(b): the example rule is reflection symmetric, `ℓ_{−m} = ℓ_m`.
(notes: `prop:es-symbol`) -/
theorem coeffMat_rotationSymbol_neg (φ lam : ℝ) (m : ℤ) :
    coeffMat (-m) (rotationSymbol φ lam) = coeffMat m (rotationSymbol φ lam) := by
  simp only [rotationSymbol, nnSymbol, map_add, coeffMat_mono]
  by_cases h1 : m = 1
  · subst h1; simp
  · by_cases h2 : m = -1
    · subst h2; simp
    · by_cases h0 : m = 0
      · subst h0; simp
      · simp [show (-1 : ℤ) ≠ m by omega, show (0 : ℤ) ≠ m by omega, show (1 : ℤ) ≠ m by omega,
          show (-1 : ℤ) ≠ -m by omega, show (0 : ℤ) ≠ -m by omega,
          show (1 : ℤ) ≠ -m by omega]

/-- Milestone Q4a, Proposition 7(d): the example rule is symplectic. (notes: `prop:es-symbol`) -/
theorem isSymplectic_rotationSymbol (φ lam : ℝ) : IsSymplectic (rotationSymbol φ lam) :=
  isSymplectic_of_mono (rotation_example φ lam 0).1

/-- Milestone Q4a, Proposition 7(e): the evolved cells of the example system have the symbol
`Γ̂(k)ᵀ γ̂(k) Γ̂(k)` (4.17b). (notes: `prop:es-symbol`) -/
theorem gammaHat_evolve_example (φ lam : ℝ) {γc : ℤ → Matrix Cell Cell ℝ} (h : CellData γc)
    (k : ℝ) :
    gammaHat (evolveCells (rotationSymbol φ lam) γc) k =
      (exampleSymbol φ lam k)ᵀ.map Complex.ofReal * gammaHat γc k *
        (exampleSymbol φ lam k).map Complex.ofReal := by
  rw [gammaHat_evolve_of_symm _ h.summable (coeffMat_rotationSymbol_neg φ lam),
    fourierSymbol_rotationSymbol, Matrix.transpose_map]

end Symbol

/-! ### The regime (4.19)–(4.20) -/

section Regime

/-- Milestone Q4a, Definition 10: the regime `|cos φ| + |λ sin φ| < 1`, `λ sin φ ≠ 0`, in which
every mode is a rotation. (notes: `def:es-regime`) -/
structure ExampleRegime (φ lam : ℝ) : Prop where
  lt_one : |Real.cos φ| + |lam * Real.sin φ| < 1
  ne_zero : lam * Real.sin φ ≠ 0

/-- Milestone Q4a, Lemma 9: `|cos φ + λ cos k sin φ| ≤ |cos φ| + |λ sin φ|`.
(notes: `lem:es-max`) -/
theorem abs_trace_le (φ lam k : ℝ) :
    |Real.cos φ + lam * Real.cos k * Real.sin φ| ≤ |Real.cos φ| + |lam * Real.sin φ| := by
  refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
  rw [show lam * Real.cos k * Real.sin φ = lam * Real.sin φ * Real.cos k by ring, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one k)

/-- Milestone Q4a, Lemma 9: the bound is attained, at `k = 0` or `k = π`. (notes: `lem:es-max`) -/
theorem exists_abs_trace_eq (φ lam : ℝ) :
    ∃ k, |Real.cos φ + lam * Real.cos k * Real.sin φ| = |Real.cos φ| + |lam * Real.sin φ| := by
  by_cases h : 0 ≤ Real.cos φ * (lam * Real.sin φ)
  · refine ⟨0, ?_⟩
    rw [Real.cos_zero, mul_one, abs_add_eq_add_abs_iff]
    rcases mul_nonneg_iff.1 h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · refine ⟨Real.pi, ?_⟩
    have h' : 0 ≤ Real.cos φ * -(lam * Real.sin φ) := by rw [mul_neg]; linarith
    rw [Real.cos_pi, show lam * -1 * Real.sin φ = -(lam * Real.sin φ) by ring,
      ← abs_neg (lam * Real.sin φ), abs_add_eq_add_abs_iff]
    rcases mul_nonneg_iff.1 h' with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- Milestone Q4a, Proposition 11(a): the regime inequality holds exactly when every mode is
elliptic, `|tr Γ̂(k)| < 2` for all `k`. (notes: `prop:es-regime`) -/
theorem lt_one_iff_forall_abs_trace_lt (φ lam : ℝ) :
    |Real.cos φ| + |lam * Real.sin φ| < 1 ↔ ∀ k, |(exampleSymbol φ lam k).trace| < 2 := by
  have e : ∀ k, |(exampleSymbol φ lam k).trace| =
      2 * |Real.cos φ + lam * Real.cos k * Real.sin φ| := fun k => by
    rw [trace_exampleSymbol, abs_mul, abs_two]
  simp_rw [e]
  constructor
  · intro h k
    linarith [abs_trace_le φ lam k]
  · intro h
    obtain ⟨k, hk⟩ := exists_abs_trace_eq φ lam
    linarith [h k]

/-- Milestone Q4a, Proposition 11(b): outside the regime some mode is not elliptic.
(notes: `prop:es-regime`) -/
theorem exists_two_le_abs_trace {φ lam : ℝ} (h : 1 ≤ |Real.cos φ| + |lam * Real.sin φ|) :
    ∃ k, 2 ≤ |(exampleSymbol φ lam k).trace| := by
  obtain ⟨k, hk⟩ := exists_abs_trace_eq φ lam
  refine ⟨k, ?_⟩
  rw [trace_exampleSymbol, abs_mul, abs_two, hk]
  linarith

/-- Milestone Q4a, Proposition 11(c): for `sin φ ≠ 0` the regime inequality is
`|λ| < f_crit = (1 − |cos φ|)/|sin φ|` (4.20). (notes: `prop:es-regime`) -/
theorem lt_one_iff_abs_lt_fcrit {φ : ℝ} (hs : Real.sin φ ≠ 0) (lam : ℝ) :
    |Real.cos φ| + |lam * Real.sin φ| < 1 ↔ |lam| < (1 - |Real.cos φ|) / |Real.sin φ| := by
  rw [lt_div_iff₀ (abs_pos.2 hs), abs_mul]
  constructor <;> intro h <;> linarith

/-- Milestone Q4a, Proposition 11(d): `f_crit = tan(φ/2)` for `0 < φ ≤ π/2`.
(notes: `prop:es-regime`) -/
theorem fcrit_eq_tan {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ Real.pi / 2) :
    (1 - |Real.cos φ|) / |Real.sin φ| = Real.tan (φ / 2) := by
  have hc : 0 ≤ Real.cos φ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  set x := φ / 2 with hx
  have hφ : φ = 2 * x := by rw [hx]; ring
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcx : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [abs_of_nonneg hc, abs_of_pos hs, Real.tan_eq_sin_div_cos, div_eq_div_iff hs.ne' hcx.ne',
    hφ, Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (-2 * Real.cos x) * Real.sin_sq_add_cos_sq x

/-- Milestone Q4a, Proposition 11(d): `f_crit = cot(φ/2)` for `π/2 < φ < π`.
(notes: `prop:es-regime`) -/
theorem fcrit_eq_cot {φ : ℝ} (h0 : Real.pi / 2 < φ) (h1 : φ < Real.pi) :
    (1 - |Real.cos φ|) / |Real.sin φ| = (Real.tan (φ / 2))⁻¹ := by
  have hc : Real.cos φ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h0 (by linarith)
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) h1
  set x := φ / 2 with hx
  have hφ : φ = 2 * x := by rw [hx]; ring
  have hsx : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith)
  have hcx : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [abs_of_neg hc, abs_of_pos hs, Real.tan_eq_sin_div_cos, inv_div,
    div_eq_div_iff hs.ne' hsx.ne', hφ, Real.cos_two_mul, Real.sin_two_mul]
  ring

/-- Milestone Q4a, Lemma 12: in the regime, `|λ cos φ| < |sin φ|`. (notes: `lem:es-sign`) -/
theorem abs_mul_cos_lt_abs_sin {φ lam : ℝ} (h : |Real.cos φ| + |lam * Real.sin φ| < 1) :
    |lam * Real.cos φ| < |Real.sin φ| := by
  set c := |Real.cos φ|
  set s := |Real.sin φ|
  have hc0 : 0 ≤ c := abs_nonneg _
  have hls : |lam| * s < 1 - c := by rw [← abs_mul]; linarith
  have hc1 : c < 1 := by linarith [abs_nonneg (lam * Real.sin φ)]
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    simp only [c, s, sq_abs]; exact Real.cos_sq_add_sin_sq φ
  have hs0 : 0 < s := by nlinarith [hcs, hc1, hc0, abs_nonneg (Real.sin φ)]
  have key : |lam| * c * s < s * s := by
    have e1 : |lam| * s * c ≤ (1 - c) * c := mul_le_mul_of_nonneg_right hls.le hc0
    have e2 : (1 - c) * c < s * s := by nlinarith [hcs, hc1]
    linarith [show |lam| * c * s = |lam| * s * c by ring]
  rw [abs_mul]
  exact lt_of_mul_lt_mul_right key hs0.le

/-- Milestone Q4a, Lemma 12: in the regime, `sin φ − λ cos k cos φ` has the sign of `sin φ`.
(notes: `lem:es-sign`) -/
theorem sign_sin_sub_eq {φ lam : ℝ} (h : |Real.cos φ| + |lam * Real.sin φ| < 1) (k : ℝ) :
    Real.sign (Real.sin φ - lam * Real.cos k * Real.cos φ) = Real.sign (Real.sin φ) := by
  have hb := abs_mul_cos_lt_abs_sin h
  have hx : |lam * Real.cos k * Real.cos φ| < |Real.sin φ| := by
    rw [show lam * Real.cos k * Real.cos φ = lam * Real.cos φ * Real.cos k by ring, abs_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one k)) hb
  set y := lam * Real.cos k * Real.cos φ
  have h1 := neg_abs_le y
  have h2 := le_abs_self y
  rcases lt_trichotomy (Real.sin φ) 0 with hs | hs | hs
  · rw [abs_of_neg hs] at hx
    have hneg : Real.sin φ - y < 0 := by linarith
    rw [Real.sign_of_neg hs, Real.sign_of_neg hneg]
  · rw [hs, abs_zero] at hx
    exact absurd hx (not_lt.2 (abs_nonneg _))
  · rw [abs_of_pos hs] at hx
    have hpos : 0 < Real.sin φ - y := by linarith
    rw [Real.sign_of_pos hs, Real.sign_of_pos hpos]

/-- Milestone Q4a, Lemma 12: in the regime `sin φ ≠ 0`. (notes: `lem:es-sign`) -/
theorem sin_ne_zero_of_lt_one {φ lam : ℝ} (h : |Real.cos φ| + |lam * Real.sin φ| < 1) :
    Real.sin φ ≠ 0 := by
  intro hs
  have := Real.cos_sq_add_sin_sq φ
  rw [hs] at this h
  have hc : |Real.cos φ| < 1 := by simpa using h
  nlinarith [abs_lt.1 hc, sq_abs (Real.cos φ)]

/-- Milestone Q4a, Definition 10: the regime is not empty; it contains `(π/2, 1/2)`.
(notes: `def:es-regime`) -/
theorem exampleRegime_pi_div_two_half : ExampleRegime (Real.pi / 2) (1 / 2) where
  lt_one := by norm_num
  ne_zero := by norm_num

end Regime

/-! ### The rotation angle (4.19) -/

section Alpha

/-- Milestone Q4a, Definition 13: the rotation angle `α(k) = arccos(cos φ + λ cos k sin φ)`
(4.19). (notes: `def:es-alpha`) -/
noncomputable def alpha (φ lam k : ℝ) : ℝ :=
  Real.arccos (Real.cos φ + lam * Real.cos k * Real.sin φ)

variable {φ lam : ℝ}

/-- Milestone Q4a, Proposition 14(a). (notes: `prop:es-alpha`) -/
theorem abs_cos_add_lt_one (hr : ExampleRegime φ lam) (k : ℝ) :
    |Real.cos φ + lam * Real.cos k * Real.sin φ| < 1 :=
  (abs_trace_le φ lam k).trans_lt hr.lt_one

/-- Milestone Q4a, Proposition 14(a): `cos α(k) = cos φ + λ cos k sin φ`.
(notes: `prop:es-alpha`) -/
theorem cos_alpha (hr : ExampleRegime φ lam) (k : ℝ) :
    Real.cos (alpha φ lam k) = Real.cos φ + lam * Real.cos k * Real.sin φ :=
  Real.cos_arccos (abs_lt.1 (abs_cos_add_lt_one hr k)).1.le
    (abs_lt.1 (abs_cos_add_lt_one hr k)).2.le

/-- Milestone Q4a, Proposition 14(a): `tr Γ̂(k) = 2 cos α(k)`. (notes: `prop:es-alpha`) -/
theorem trace_eq_two_cos_alpha (hr : ExampleRegime φ lam) (k : ℝ) :
    (exampleSymbol φ lam k).trace = 2 * Real.cos (alpha φ lam k) := by
  rw [trace_exampleSymbol, cos_alpha hr]

/-- Milestone Q4a, Proposition 14(a): `α(k) ∈ (0, π)`. (notes: `prop:es-alpha`) -/
theorem alpha_mem_Ioo (hr : ExampleRegime φ lam) (k : ℝ) :
    alpha φ lam k ∈ Set.Ioo 0 Real.pi :=
  ⟨Real.arccos_pos.2 (abs_lt.1 (abs_cos_add_lt_one hr k)).2,
    Real.arccos_lt_pi.2 (abs_lt.1 (abs_cos_add_lt_one hr k)).1⟩

/-- Milestone Q4a, Proposition 14(a): `sin α(k) > 0`. (notes: `prop:es-alpha`) -/
theorem sin_alpha_pos (hr : ExampleRegime φ lam) (k : ℝ) : 0 < Real.sin (alpha φ lam k) :=
  Real.sin_pos_of_pos_of_lt_pi (alpha_mem_Ioo hr k).1 (alpha_mem_Ioo hr k).2

variable (φ lam) in
/-- Milestone Q4a, Proposition 14(b): `α(−k) = α(k)`. (notes: `prop:es-alpha`) -/
theorem alpha_neg (k : ℝ) : alpha φ lam (-k) = alpha φ lam k := by
  rw [alpha, alpha, Real.cos_neg]

variable (φ lam) in
/-- Milestone Q4a, Proposition 14(b): `α` is continuous. (notes: `prop:es-alpha`) -/
theorem continuous_alpha : Continuous (alpha φ lam) :=
  Real.continuous_arccos.comp (by fun_prop)

/-- Milestone Q4a, Proposition 14(c): `α′(k) = λ sin φ sin k / sin α(k)`.
(notes: `prop:es-alpha`) -/
theorem hasDerivAt_alpha (hr : ExampleRegime φ lam) (k : ℝ) :
    HasDerivAt (alpha φ lam)
      (lam * Real.sin φ * Real.sin k / Real.sin (alpha φ lam k)) k := by
  have hb := abs_lt.1 (abs_cos_add_lt_one hr k)
  have hτ : HasDerivAt (fun k => Real.cos φ + lam * Real.cos k * Real.sin φ)
      (lam * -Real.sin k * Real.sin φ) k :=
    (((Real.hasDerivAt_cos k).const_mul lam).mul_const _).const_add _
  have ha := (Real.hasDerivAt_arccos hb.1.ne' hb.2.ne).comp k hτ
  have hsq : 0 < √(1 - (Real.cos φ + lam * Real.cos k * Real.sin φ) ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [hb.1, hb.2])
  refine ha.congr_deriv ?_
  simp only [alpha, Real.sin_arccos]
  field_simp

/-- Milestone Q4a, Proposition 14(d): `α` is strictly increasing on `[0, π]` when `λ sin φ > 0`.
(notes: `prop:es-alpha`) -/
theorem strictMonoOn_alpha (hr : ExampleRegime φ lam) (hpos : 0 < lam * Real.sin φ) :
    StrictMonoOn (alpha φ lam) (Set.Icc 0 Real.pi) := by
  intro a ha b hb hab
  have hcos := Real.strictAntiOn_cos ha hb hab
  have ht : Real.cos φ + lam * Real.cos b * Real.sin φ <
      Real.cos φ + lam * Real.cos a * Real.sin φ := by
    have := mul_lt_mul_of_pos_left hcos hpos
    linarith [show lam * Real.sin φ * Real.cos b = lam * Real.cos b * Real.sin φ by ring,
      show lam * Real.sin φ * Real.cos a = lam * Real.cos a * Real.sin φ by ring]
  have hma := abs_lt.1 (abs_cos_add_lt_one hr a)
  have hmb := abs_lt.1 (abs_cos_add_lt_one hr b)
  exact Real.strictAntiOn_arccos ⟨hmb.1.le, hmb.2.le⟩ ⟨hma.1.le, hma.2.le⟩ ht

/-- Milestone Q4a, Proposition 14(d): `α` is strictly decreasing on `[0, π]` when `λ sin φ < 0`.
(notes: `prop:es-alpha`) -/
theorem strictAntiOn_alpha (hr : ExampleRegime φ lam) (hneg : lam * Real.sin φ < 0) :
    StrictAntiOn (alpha φ lam) (Set.Icc 0 Real.pi) := by
  intro a ha b hb hab
  have hcos := Real.strictAntiOn_cos ha hb hab
  have ht : Real.cos φ + lam * Real.cos a * Real.sin φ <
      Real.cos φ + lam * Real.cos b * Real.sin φ := by
    have := mul_lt_mul_of_neg_left hcos hneg
    linarith [show lam * Real.sin φ * Real.cos b = lam * Real.cos b * Real.sin φ by ring,
      show lam * Real.sin φ * Real.cos a = lam * Real.cos a * Real.sin φ by ring]
  have hma := abs_lt.1 (abs_cos_add_lt_one hr a)
  have hmb := abs_lt.1 (abs_cos_add_lt_one hr b)
  exact Real.strictAntiOn_arccos ⟨hma.1.le, hma.2.le⟩ ⟨hmb.1.le, hmb.2.le⟩ ht

end Alpha

/-! ### Powers and Lemma 4.6 (4.21)–(4.24) -/

section Powers

/-- Milestone Q4a, Lemma 15: the powers of a `2 × 2` matrix of determinant one with trace
`2 cos a`, `sin a ≠ 0`, are `A^t = (sin ta / sin a) A − (sin (t−1)a / sin a) 1`.
(notes: `lem:es-chebyshev`) -/
theorem pow_eq_chebyshev {A : Matrix Cell Cell ℝ} {a : ℝ} (hd : det2 A = 1)
    (ht : A.trace = 2 * Real.cos a) (hs : Real.sin a ≠ 0) (t : ℕ) :
    A ^ t = (Real.sin (t * a) / Real.sin a) • A -
      (Real.sin (((t : ℝ) - 1) * a) / Real.sin a) • 1 := by
  induction t with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, Real.sin_zero, zero_div, zero_smul, zero_sub,
      neg_mul, one_mul, Real.sin_neg, neg_div, div_self hs, neg_smul, one_smul, neg_neg]
  | succ t ih =>
    have hA2 := sq_eq_trace_smul_sub A
    rw [ht, hd] at hA2
    have hsum : Real.sin (((t + 1 : ℕ) : ℝ) * a) =
        2 * Real.cos a * Real.sin (t * a) - Real.sin (((t : ℝ) - 1) * a) := by
      rw [show (((t + 1 : ℕ) : ℝ) * a) = t * a + a by push_cast; ring,
        show ((t : ℝ) - 1) * a = t * a - a by ring, Real.sin_add, Real.sin_sub]
      ring
    have key : Real.sin (((t + 1 : ℕ) : ℝ) * a) / Real.sin a =
        2 * Real.cos a * (Real.sin (t * a) / Real.sin a) -
          Real.sin (((t : ℝ) - 1) * a) / Real.sin a := by
      rw [hsum]; ring
    have key' : (((t + 1 : ℕ) : ℝ) - 1) * a = t * a := by push_cast; ring
    rw [pow_succ, ih, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hA2, Matrix.one_mul,
      key, key']
    module

variable {φ lam : ℝ}

/-- Milestone Q4a, Corollary 16: the powers of `Γ̂(k)` in the regime. (notes: `lem:es-chebyshev`) -/
theorem exampleSymbol_pow (hr : ExampleRegime φ lam) (k : ℝ) (t : ℕ) :
    exampleSymbol φ lam k ^ t =
      (Real.sin (t * alpha φ lam k) / Real.sin (alpha φ lam k)) • exampleSymbol φ lam k -
        (Real.sin (((t : ℝ) - 1) * alpha φ lam k) / Real.sin (alpha φ lam k)) • 1 :=
  pow_eq_chebyshev (det2_exampleSymbol φ lam k) (trace_eq_two_cos_alpha hr k)
    (sin_alpha_pos hr k).ne' t

variable (φ lam) in
/-- Milestone Q4a, Proposition 17: the real matrix `N(k) = (cos α(k) 1 − Γ̂(k)) / sin α(k)`,
with `N(k)² = −1` in the regime. (notes: `prop:es-projectors`) -/
noncomputable def nMat (k : ℝ) : Matrix Cell Cell ℝ :=
  (Real.sin (alpha φ lam k))⁻¹ • (Real.cos (alpha φ lam k) • 1 - exampleSymbol φ lam k)

/-- Milestone Q4a, Proposition 17: `N(k)² = −1` in the regime. (notes: `prop:es-projectors`) -/
theorem nMat_mul_self (hr : ExampleRegime φ lam) (k : ℝ) : nMat φ lam k * nMat φ lam k = -1 := by
  have hA2 := sq_eq_trace_smul_sub (exampleSymbol φ lam k)
  rw [trace_eq_two_cos_alpha hr, det2_exampleSymbol] at hA2
  have hs := (sin_alpha_pos hr k).ne'
  have hcs := Real.sin_sq_add_cos_sq (alpha φ lam k)
  set Γ := exampleSymbol φ lam k
  set c := Real.cos (alpha φ lam k)
  set s := Real.sin (alpha φ lam k)
  have hX : (c • 1 - Γ) * (c • 1 - Γ) = (-(s ^ 2)) • (1 : Matrix Cell Cell ℝ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hA2]
    match_scalars <;> first | linear_combination hcs | ring
  rw [nMat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX, smul_smul]
  have e : s⁻¹ * s⁻¹ * -(s ^ 2) = -1 := by field_simp
  rw [e, neg_one_smul]

/-- Milestone Q4a, Proposition 17: `Γ̂(k) = cos α(k) 1 − sin α(k) N(k)`. -/
theorem exampleSymbol_eq_nMat (hr : ExampleRegime φ lam) (k : ℝ) :
    exampleSymbol φ lam k =
      Real.cos (alpha φ lam k) • 1 - Real.sin (alpha φ lam k) • nMat φ lam k := by
  rw [nMat, smul_smul, mul_inv_cancel₀ (sin_alpha_pos hr k).ne', one_smul, sub_sub_cancel]

variable (φ lam) in
/-- Milestone Q4a, Proposition 17: the spectral projector
`P_k = ½(1 + i(cos α(k) 1 − Γ̂(k))/sin α(k))` of Lemma 4.6. (notes: `prop:es-projectors`) -/
noncomputable def projP (k : ℝ) : Matrix Cell Cell ℂ :=
  (1 / 2 : ℂ) • (1 + (Complex.I / Real.sin (alpha φ lam k)) •
    (Real.cos (alpha φ lam k) • 1 - exampleSymbol φ lam k).map Complex.ofReal)

/-- Milestone Q4a, Proposition 17: `P_k = ½(1 + i N(k))`. -/
theorem projP_eq (φ lam k : ℝ) :
    projP φ lam k = (1 / 2 : ℂ) • (1 + Complex.I • (nMat φ lam k).map Complex.ofReal) := by
  rw [projP, nMat]
  congr 2
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_inv]
  ring

/-- Milestone Q4a, Proposition 17: `P̄_k = ½(1 − i N(k))`. -/
theorem conj_projP_eq (φ lam k : ℝ) :
    (projP φ lam k).map (starRingEnd ℂ) =
      (1 / 2 : ℂ) • (1 - Complex.I • (nMat φ lam k).map Complex.ofReal) := by
  rw [projP_eq]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Complex.conj_ofReal, sub_eq_add_neg, map_ofNat]
    ring
  · simp [hij, Complex.conj_ofReal, sub_eq_add_neg, map_ofNat]

/-- Milestone Q4a, Proposition 17: `N(k)² = −1` over `ℂ`. -/
theorem nMat_map_mul_self (hr : ExampleRegime φ lam) (k : ℝ) :
    (nMat φ lam k).map Complex.ofReal * (nMat φ lam k).map Complex.ofReal = -1 := by
  rw [← map_ofReal_mul, nMat_mul_self hr, Matrix.map_neg _ Complex.ofReal_neg, Matrix.map_one _
    Complex.ofReal_zero Complex.ofReal_one]

variable (φ lam) in
/-- Milestone Q4a, Proposition 17(a): `P_k + P̄_k = 1`, for all parameters.
(notes: `prop:es-projectors`) -/
theorem projP_add_conj (k : ℝ) :
    projP φ lam k + (projP φ lam k).map (starRingEnd ℂ) = 1 := by
  rw [conj_projP_eq, projP_eq]
  module

/-- Milestone Q4a, Proposition 17(a): `P_k² = P_k`. (notes: `prop:es-projectors`) -/
theorem projP_mul_self (hr : ExampleRegime φ lam) (k : ℝ) :
    projP φ lam k * projP φ lam k = projP φ lam k := by
  rw [projP_eq]
  set N := (nMat φ lam k).map Complex.ofReal
  have hN : N * N = -1 := nMat_map_mul_self hr k
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hN, smul_smul, smul_add]
  match_scalars
  · ring_nf
    simp [Complex.I_sq]
    ring
  · ring

/-- Milestone Q4a, Proposition 17(a): `P_k P̄_k = 0`. (notes: `prop:es-projectors`) -/
theorem projP_mul_conj (hr : ExampleRegime φ lam) (k : ℝ) :
    projP φ lam k * (projP φ lam k).map (starRingEnd ℂ) = 0 := by
  rw [conj_projP_eq, projP_eq]
  set N := (nMat φ lam k).map Complex.ofReal
  have hN : N * N = -1 := nMat_map_mul_self hr k
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, hN, smul_smul, smul_add, smul_sub]
  match_scalars
  · ring_nf
    simp [Complex.I_sq]
  · ring

/-- Milestone Q4a, Proposition 17(a): `P̄_k P_k = 0`. (notes: `prop:es-projectors`) -/
theorem conj_mul_projP (hr : ExampleRegime φ lam) (k : ℝ) :
    (projP φ lam k).map (starRingEnd ℂ) * projP φ lam k = 0 := by
  rw [conj_projP_eq, projP_eq]
  set N := (nMat φ lam k).map Complex.ofReal
  have hN : N * N = -1 := nMat_map_mul_self hr k
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_one, hN, smul_smul, smul_add, smul_sub]
  match_scalars
  · ring_nf
    simp [Complex.I_sq]
  · ring

/-- Milestone Q4a, Proposition 17: `Γ̂(k) = cos α 1 − sin α N(k)` over `ℂ`. -/
theorem exampleSymbol_map_eq_nMat (hr : ExampleRegime φ lam) (k : ℝ) :
    (exampleSymbol φ lam k).map Complex.ofReal =
      (Real.cos (alpha φ lam k) : ℂ) • 1 -
        (Real.sin (alpha φ lam k) : ℂ) • (nMat φ lam k).map Complex.ofReal := by
  conv_lhs => rw [exampleSymbol_eq_nMat hr]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- Milestone Q4a, Proposition 17(b): `Γ̂(k) = e^{iα} P_k + e^{−iα} P̄_k` (4.21).
(notes: `prop:es-projectors`) -/
theorem exampleSymbol_eq_projP (hr : ExampleRegime φ lam) (k : ℝ) :
    (exampleSymbol φ lam k).map Complex.ofReal =
      Complex.exp (alpha φ lam k * Complex.I) • projP φ lam k +
        Complex.exp (-(alpha φ lam k * Complex.I)) • (projP φ lam k).map (starRingEnd ℂ) := by
  rw [exampleSymbol_map_eq_nMat hr, conj_projP_eq, projP_eq]
  set a := alpha φ lam k
  have hc : (Real.cos a : ℂ) = (Complex.exp (a * Complex.I) + Complex.exp (-(a * Complex.I))) / 2 :=
    by rw [Complex.ofReal_cos, Complex.cos, neg_mul]
  have hs : (Real.sin a : ℂ) =
      (Complex.exp (-(a * Complex.I)) - Complex.exp (a * Complex.I)) * Complex.I / 2 := by
    rw [Complex.ofReal_sin, Complex.sin, neg_mul]
  rw [hc, hs]
  match_scalars <;> ring_nf

/-- Milestone Q4a, Proposition 17(b): `Γ̂(k) P_k = e^{iα} P_k`. (notes: `prop:es-projectors`) -/
theorem exampleSymbol_mul_projP (hr : ExampleRegime φ lam) (k : ℝ) :
    (exampleSymbol φ lam k).map Complex.ofReal * projP φ lam k =
      Complex.exp (alpha φ lam k * Complex.I) • projP φ lam k := by
  rw [exampleSymbol_eq_projP hr, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    projP_mul_self hr, conj_mul_projP hr, smul_zero, add_zero]

/-- Milestone Q4a, Proposition 17(c): `Γ̂(k)^t = e^{itα} P_k + e^{−itα} P̄_k` (4.24).
(notes: `prop:es-projectors`) -/
theorem exampleSymbol_pow_eq_projP (hr : ExampleRegime φ lam) (k : ℝ) (t : ℕ) :
    (exampleSymbol φ lam k ^ t).map Complex.ofReal =
      Complex.exp (t * alpha φ lam k * Complex.I) • projP φ lam k +
        Complex.exp (-(t * alpha φ lam k * Complex.I)) •
          (projP φ lam k).map (starRingEnd ℂ) := by
  induction t with
  | zero =>
    simp only [pow_zero, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one, Nat.cast_zero,
      zero_mul, neg_zero, Complex.exp_zero, one_smul]
    exact (projP_add_conj φ lam k).symm
  | succ t ih =>
    rw [pow_succ, map_ofReal_mul, ih, exampleSymbol_eq_projP hr]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      projP_mul_self hr, projP_mul_conj hr, conj_mul_projP hr, smul_zero, add_zero, zero_add,
      smul_smul]
    have hsq : (projP φ lam k).map (starRingEnd ℂ) * (projP φ lam k).map (starRingEnd ℂ) =
        (projP φ lam k).map (starRingEnd ℂ) := by
      rw [← Matrix.map_mul (f := starRingEnd ℂ), projP_mul_self hr]
    rw [hsq, ← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf

end Powers

/-! ### The massless inverse leapfrog -/

section Finding2

/-- The trace of the inverse leapfrog symbol is `2 cos k − m²`. (notes: `prop:es-finding2`) -/
theorem leapfrogInv_trace (m2 k : ℝ) :
    (fourierSymbol k (leapfrogInvSymbol m2)).trace = 2 * Real.cos k - m2 := by
  rw [leapfrogInvSymbol, fourierSymbol_nnSymbol_symm, trace_cell]
  simp [leapfrogInvShift, leapfrogInvCentre]
  ring

/-- Milestone Q4a, Proposition 26(a): the leapfrog and its inverse have the same trace.
(notes: `prop:es-finding2`) -/
theorem leapfrog_trace_eq_inv (m2 k : ℝ) :
    (fourierSymbol k (leapfrogSymbol m2)).trace =
      (fourierSymbol k (leapfrogInvSymbol m2)).trace := by
  rw [leapfrog_trace, leapfrogInv_trace]

/-- Milestone Q4a, Proposition 26(a): the mode `k = π` for `m² ≥ 0`, and `k = 0` for `m² < 0`, of
the leapfrog is not elliptic. (notes: `prop:es-finding2`) -/
theorem two_le_norm_trace_leapfrog (m2 : ℝ) :
    2 ≤ ‖(fourierSymbol (if 0 ≤ m2 then Real.pi else 0) (leapfrogSymbol m2)).trace‖ := by
  split_ifs with h
  · rw [leapfrog_trace, Real.cos_pi,
      show (2 * (-1 : ℝ) - m2 : ℂ) = ((-(2 + m2) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by linarith)]
    linarith
  · rw [leapfrog_trace, Real.cos_zero,
      show (2 * (1 : ℝ) - m2 : ℂ) = ((2 - m2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith

/-- Milestone Q4a, Proposition 26(a): for every real `m²` some leapfrog mode is not elliptic. -/
theorem leapfrog_exists_two_le_trace (m2 : ℝ) :
    ∃ k, 2 ≤ ‖(fourierSymbol k (leapfrogSymbol m2)).trace‖ :=
  ⟨_, two_le_norm_trace_leapfrog m2⟩

/-- Milestone Q4a, Proposition 26(a): the same for the inverse leapfrog. -/
theorem leapfrogInv_exists_two_le_trace (m2 : ℝ) :
    ∃ k, 2 ≤ ‖(fourierSymbol k (leapfrogInvSymbol m2)).trace‖ :=
  ⟨_, (leapfrog_trace_eq_inv m2 _) ▸ two_le_norm_trace_leapfrog m2⟩

/-- Milestone Q4a, Proposition 26(b): the massless inverse leapfrog is the example rule at
`φ = π/2`, `λ = 1`. (notes: `prop:es-finding2`) -/
theorem leapfrogInvSymbol_zero_eq : leapfrogInvSymbol 0 = rotationSymbol (Real.pi / 2) 1 := by
  rw [leapfrogInvSymbol, rotationSymbol]
  have hs : vecMulVec e1 ((1 : ℝ) • rotation (Real.pi / 2) pIdx) = leapfrogInvShift := by
    apply cell_ext <;> simp [vecMulVec_apply, e1, rotation, leapfrogInvShift]
  have hc : rotation (Real.pi / 2) = leapfrogInvCentre 0 := by
    apply cell_ext <;> simp [rotation, leapfrogInvCentre]
  rw [hs, hc]

/-- Milestone Q4a, Proposition 26(c): the pair `(π/2, 1)` lies on the boundary of the regime,
`λ = 1 = f_crit(π/2)`. (notes: `prop:es-finding2`) -/
theorem not_exampleRegime_pi_div_two :
    ¬ ExampleRegime (Real.pi / 2) 1 ∧
      |Real.cos (Real.pi / 2)| + |1 * Real.sin (Real.pi / 2)| = 1 ∧
      (1 - |Real.cos (Real.pi / 2)|) / |Real.sin (Real.pi / 2)| = 1 := by
  have e : |Real.cos (Real.pi / 2)| + |1 * Real.sin (Real.pi / 2)| = 1 := by simp
  exact ⟨fun hr => (lt_irrefl _ (e ▸ hr.lt_one)), e, by simp⟩

end Finding2

end QCALean.Bosonic
