/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.ExampleSystem

/-!
# The stationary states of the example system

Milestone Q4a. In the regime every Fourier mode `Γ̂(k)` of Krüger's example system preserves the
pure form `ε̂(k) = −sgn(sin φ) Ω (cos α(k) 1 − Γ̂(k)) / sin α(k)` (4.28), and the invariant real
symmetric forms of `Γ̂(k)` are its real multiples. Hence (thesis Theorem 4.8, both directions) the
stationary, reflection-symmetric admissible cells satisfying the Fourier state condition are
exactly those with `γ̂(k) = g(k) ε̂(k)`, `g` continuous and even with `g ≥ 1`.

## Main definitions and results

* `QCALean.Bosonic.epsHat`: the invariant form (4.28), with the sign of `sin φ`.
* `QCALean.Bosonic.smul_epsHat_add_posSemidef_iff`: the state-condition threshold `g ≥ 1`.
* `QCALean.Bosonic.eq_smul_of_invariant_sl2`: invariant symmetric forms of an elliptic
  element of `SL₂(ℝ)` are one-dimensional.
* `QCALean.Bosonic.stationary_iff`: Theorem 4.8.
-/

open LinearAQFT QCALean.Core Matrix Gaussian
open scoped ComplexOrder ComplexConjugate

namespace QCALean.Bosonic

/-- `Ω` as a complex matrix (the complexified `Gaussian.symplecticForm 1`). -/
local notation "Ωc" => Matrix.map (Gaussian.symplecticForm 1) Complex.ofReal

/-! ### Two-by-two matrix facts -/

section TwoByTwo

/-- The sign of a nonzero real squares to one. -/
theorem sign_mul_self_of_ne_zero {r : ℝ} (h : r ≠ 0) : Real.sign r * Real.sign r = 1 := by
  rcases Real.sign_apply_eq_of_ne_zero r h with e | e <;> rw [e] <;> norm_num

/-- `sgn(r) r = |r|`. -/
theorem sign_mul_self_eq_abs (r : ℝ) : Real.sign r * r = |r| := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · rw [h, Real.sign_zero, abs_zero, mul_zero]
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

/-- Milestone Q4a, Proposition 22: the invariant real symmetric forms of an elliptic element of
`SL₂(ℝ)` are one-dimensional: each is a unique multiple of a nonzero one.
(notes: `prop:es-invariant`) -/
theorem eq_smul_of_invariant_sl2 {A S E : Matrix Cell Cell ℝ} (hd : det2 A = 1)
    (he : |A.trace| < 2) (hE : Eᵀ = E) (hEA : Aᵀ * E * A = E) (hE0 : E ≠ 0)
    (hS : Sᵀ = S) (hSA : Aᵀ * S * A = S) : ∃! g : ℝ, S = g • E := by
  have hA : ∀ c : ℝ, A ≠ c • 1 := by
    intro c hc
    rw [hc, det2_smul, det2_one, mul_one] at hd
    rw [hc, trace_cell] at he
    simp only [Matrix.smul_apply, one_qq, one_pp, smul_eq_mul, mul_one] at he
    have : |c| = 1 := by
      have := sq_abs c
      nlinarith [abs_nonneg c, sq_nonneg (|c| - 1), sq_nonneg (|c| + 1)]
    rw [show c + c = 2 * c by ring, abs_mul, abs_two, this] at he
    linarith
  obtain ⟨qS, hqS⟩ := eq_smul_of_invariant_sym hd hA hS hSA
  obtain ⟨qE, hqE⟩ := eq_smul_of_invariant_sym hd hA hE hEA
  have hqE0 : qE ≠ 0 := by rintro rfl; rw [zero_smul] at hqE; exact hE0 hqE
  refine ⟨qS / qE, ?_, fun g' hg' => ?_⟩
  · change S = (qS / qE) • E
    rw [hqS, hqE, smul_smul, div_mul_cancel₀ _ hqE0]
  · have hg'' : S = g' • E := hg'
    have e : g' • E = (qS / qE) • E := by
      rw [← hg'', hqS, hqE, smul_smul, div_mul_cancel₀ _ hqE0]
    exact smul_left_injective ℝ hE0 e

end TwoByTwo

/-! ### The invariant form (4.28) -/

section Eps

/-- Milestone Q4a, Definition 18: the invariant pure form
`ε̂(k) = −sgn(sin φ) Ω (cos α(k) 1 − Γ̂(k)) / sin α(k)` (4.28). (notes: `def:es-eps`) -/
noncomputable def epsHat (φ lam k : ℝ) : Matrix Cell Cell ℝ :=
  (-(Real.sign (Real.sin φ)) / Real.sin (alpha φ lam k)) •
    (omega * (Real.cos (alpha φ lam k) • 1 - exampleSymbol φ lam k))

variable {φ lam : ℝ}

/-- `ε̂(k) = −sgn(sin φ) Ω N(k)`. (notes: `def:es-eps`) -/
theorem epsHat_eq_nMat (φ lam k : ℝ) :
    epsHat φ lam k = (-(Real.sign (Real.sin φ))) • (omega * nMat φ lam k) := by
  rw [epsHat, nMat, Matrix.mul_smul, smul_smul, div_eq_mul_inv]

/-- Milestone Q4a, Definition 18: the `(1,1)` entry of `ε̂(k)` in the regime. -/
theorem epsHat_qq (hr : ExampleRegime φ lam) (k : ℝ) :
    epsHat φ lam k qIdx qIdx = Real.sign (Real.sin φ) * Real.sin φ / Real.sin (alpha φ lam k) := by
  simp [epsHat, cos_alpha hr]; ring

/-- Milestone Q4a, Definition 18: the `(1,2)` entry of `ε̂(k)` in the regime. -/
theorem epsHat_qp (hr : ExampleRegime φ lam) (k : ℝ) :
    epsHat φ lam k qIdx pIdx = -(Real.sign (Real.sin φ)) * (lam * Real.cos k * Real.sin φ) /
      Real.sin (alpha φ lam k) := by
  simp [epsHat, cos_alpha hr]; ring

/-- Milestone Q4a, Definition 18: the `(2,1)` entry of `ε̂(k)` in the regime. -/
theorem epsHat_pq (hr : ExampleRegime φ lam) (k : ℝ) :
    epsHat φ lam k pIdx qIdx = -(Real.sign (Real.sin φ)) * (lam * Real.cos k * Real.sin φ) /
      Real.sin (alpha φ lam k) := by
  simp [epsHat, cos_alpha hr]; ring

/-- Milestone Q4a, Definition 18: the `(2,2)` entry of `ε̂(k)` in the regime. -/
theorem epsHat_pp (hr : ExampleRegime φ lam) (k : ℝ) :
    epsHat φ lam k pIdx pIdx = Real.sign (Real.sin φ) *
      (Real.sin φ - 2 * lam * Real.cos k * Real.cos φ) / Real.sin (alpha φ lam k) := by
  simp [epsHat, cos_alpha hr]; ring

/-- Milestone Q4a, Proposition 19(a): `ε̂(k)` is symmetric. (notes: `prop:es-eps`) -/
theorem epsHat_transpose (hr : ExampleRegime φ lam) (k : ℝ) :
    (epsHat φ lam k)ᵀ = epsHat φ lam k := by
  apply cell_ext <;> simp only [Matrix.transpose_apply, epsHat_pq hr, epsHat_qp hr]

variable (φ lam) in
/-- Milestone Q4a, Proposition 19(b): `Γ̂(k)ᵀ ε̂(k) Γ̂(k) = ε̂(k)`, for all parameters.
(notes: `prop:es-eps`) -/
theorem epsHat_invariant (k : ℝ) :
    (exampleSymbol φ lam k)ᵀ * epsHat φ lam k * exampleSymbol φ lam k = epsHat φ lam k := by
  rw [epsHat, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  set Γ := exampleSymbol φ lam k
  set a := Real.cos (alpha φ lam k)
  have hS := exampleSymbol_symplectic φ lam k
  calc Γᵀ * (omega * (a • 1 - Γ)) * Γ = a • (Γᵀ * omega * Γ) - Γᵀ * omega * Γ * Γ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.mul_assoc]
    _ = omega * (a • 1 - Γ) := by
        rw [hS, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]

variable (φ lam) in
/-- Milestone Q4a, Proposition 19(a): `ε̂(−k) = ε̂(k)`, for all parameters.
(notes: `prop:es-eps`) -/
theorem epsHat_neg (k : ℝ) : epsHat φ lam (-k) = epsHat φ lam k := by
  rw [epsHat, epsHat, alpha_neg, exampleSymbol_neg]

variable (φ lam) in
/-- Milestone Q4a, Proposition 19(a): `Γ̂` is continuous in `k`. -/
theorem continuous_exampleSymbol : Continuous (exampleSymbol φ lam) :=
  continuous_const.add ((by fun_prop : Continuous fun k => 2 * lam * Real.cos k).smul
    continuous_const)

/-- Milestone Q4a, Proposition 19(a): `ε̂` is continuous. (notes: `prop:es-eps`) -/
theorem continuous_epsHat (hr : ExampleRegime φ lam) : Continuous (epsHat φ lam) := by
  have hα := continuous_alpha φ lam
  refine Continuous.smul (continuous_const.div (Real.continuous_sin.comp hα)
    fun k => (sin_alpha_pos hr k).ne') (continuous_const.matrix_mul ?_)
  exact ((Real.continuous_cos.comp hα).smul continuous_const).sub
    (continuous_exampleSymbol φ lam)

/-- Milestone Q4a, Proposition 19(c): `det ε̂(k) = 1`. (notes: `prop:es-eps`) -/
theorem det2_epsHat (hr : ExampleRegime φ lam) (k : ℝ) : det2 (epsHat φ lam k) = 1 := by
  have hs := sin_ne_zero_of_lt_one hr.lt_one
  have hsg := sign_mul_self_of_ne_zero hs
  have hsa := (sin_alpha_pos hr k).ne'
  have hsq : Real.sin (alpha φ lam k) ^ 2 =
      1 - (Real.cos φ + lam * Real.cos k * Real.sin φ) ^ 2 := by
    rw [← cos_alpha hr]; linarith [Real.sin_sq_add_cos_sq (alpha φ lam k)]
  rw [det2, epsHat_qq hr, epsHat_qp hr, epsHat_pq hr, epsHat_pp hr]
  field_simp
  linear_combination (Real.sin φ ^ 2 - 2 * lam * Real.cos k * Real.cos φ * Real.sin φ -
    lam ^ 2 * Real.cos k ^ 2 * Real.sin φ ^ 2) * hsg - hsq + Real.sin_sq_add_cos_sq φ

/-- Milestone Q4a, Proposition 19(c): purity, `(Ω ε̂(k))² = −1`. (notes: `prop:es-eps`) -/
theorem omega_mul_epsHat_sq (hr : ExampleRegime φ lam) (k : ℝ) :
    (omega * epsHat φ lam k) ^ 2 = -1 := by
  have hsg := sign_mul_self_of_ne_zero (sin_ne_zero_of_lt_one hr.lt_one)
  have e : omega * epsHat φ lam k = Real.sign (Real.sin φ) • nMat φ lam k := by
    rw [epsHat_eq_nMat, Matrix.mul_smul, ← Matrix.mul_assoc, omega_mul_omega, Matrix.neg_mul,
      Matrix.one_mul, smul_neg, neg_smul, neg_neg]
  rw [sq, e, Matrix.smul_mul, Matrix.mul_smul, smul_smul, nMat_mul_self hr, hsg, one_smul]

/-- Milestone Q4a, Proposition 19(d): `ε̂(k)` is positive definite. (notes: `prop:es-eps`) -/
theorem epsHat_posDef (hr : ExampleRegime φ lam) (k : ℝ) : (epsHat φ lam k).PosDef := by
  have hs := sin_ne_zero_of_lt_one hr.lt_one
  refine posDef_of_cell (epsHat_transpose hr k) ?_ (by rw [det2_epsHat hr]; exact one_pos)
  rw [epsHat_qq hr, sign_mul_self_eq_abs]
  exact div_pos (abs_pos.2 hs) (sin_alpha_pos hr k)

/-- Milestone Q4a, Proposition 19(d): `ε̂(k)₁₁ = |sin φ| / sin α(k)`. (notes: `prop:es-eps`) -/
theorem epsHat_qq_eq_abs (hr : ExampleRegime φ lam) (k : ℝ) :
    epsHat φ lam k qIdx qIdx = |Real.sin φ| / Real.sin (alpha φ lam k) := by
  rw [epsHat_qq hr, sign_mul_self_eq_abs]

/-- Milestone Q4a, Proposition 19(e): the trace `tr(iΩ P_k) = (sin φ − λ cos k cos φ)/sin α(k)`
of the thesis (p. 88); its sign is that of `sin φ` by `sign_sin_sub_eq`. (notes: `prop:es-eps`) -/
theorem trace_I_omega_projP (hr : ExampleRegime φ lam) (k : ℝ) :
    (Complex.I • (omega : Matrix Cell Cell ℂ) * projP φ lam k).trace =
      ((Real.sin φ - lam * Real.cos k * Real.cos φ) / Real.sin (alpha φ lam k) : ℝ) := by
  rw [projP, trace_cell]
  simp [cos_alpha hr, Matrix.sub_apply]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Milestone Q4a, Proposition 19(f): `ε̂(k) = sgn(sin φ) iΩ(P_k − P̄_k)`. (notes: `prop:es-eps`) -/
theorem epsHat_eq_projP (φ lam k : ℝ) :
    (epsHat φ lam k).map Complex.ofReal = (Real.sign (Real.sin φ) : ℂ) •
      (Complex.I • (omega : Matrix Cell Cell ℂ) *
        (projP φ lam k - (projP φ lam k).map (starRingEnd ℂ))) := by
  rw [conj_projP_eq, projP_eq, epsHat_eq_nMat]
  ext i j
  rcases i with ⟨i⟩ | ⟨i⟩ <;> rcases j with ⟨j⟩ | ⟨j⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, omega, Matrix.J, Matrix.one_apply] <;>
    ring_nf <;> simp [Complex.I_sq]

/-- Milestone Q4a, Proposition 19(f): for `sin φ > 0`, `ε̂(k) + iΩ = 2iΩ P_k`.
(notes: `prop:es-eps`) -/
theorem epsHat_add_eq_projP (hs : 0 < Real.sin φ) (k : ℝ) :
    (epsHat φ lam k).map Complex.ofReal + Complex.I • (omega : Matrix Cell Cell ℂ) =
      (2 : ℂ) • (Complex.I • (omega : Matrix Cell Cell ℂ) * projP φ lam k) := by
  rw [epsHat_eq_projP, Real.sign_of_pos hs, Complex.ofReal_one, one_smul]
  have hc : (projP φ lam k).map (starRingEnd ℂ) = 1 - projP φ lam k := by
    rw [← projP_add_conj φ lam k, add_sub_cancel_left]
  rw [hc, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one]
  module

/-- The rank-one factorizations `E ± iΩ = w w*`, `w = (√e₁, (e₂ ∓ i)/√e₁)`, of a real symmetric
one-mode matrix `E` with `e₁ = E₁₁ > 0` and `det E = 1`. -/
theorem add_I_omega_eq_vecMulVec {E : Matrix Cell Cell ℝ} (hs : Eᵀ = E)
    (he1 : 0 < E qIdx qIdx) (hd : det2 E = 1) (s : ℝ) (hs1 : s = 1 ∨ s = -1) :
    E.map Complex.ofReal + ((s : ℂ) * Complex.I) • (omega : Matrix Cell Cell ℂ) =
      vecMulVec (Sum.elim (fun _ => (√(E qIdx qIdx) : ℂ))
          (fun _ => ((E qIdx pIdx : ℂ) - s * Complex.I) / √(E qIdx qIdx)))
        (star (Sum.elim (fun _ => (√(E qIdx qIdx) : ℂ))
          (fun _ => ((E qIdx pIdx : ℂ) - s * Complex.I) / √(E qIdx qIdx)))) := by
  have hsym : E pIdx qIdx = E qIdx pIdx := by
    have := congrFun (congrFun hs qIdx) pIdx
    rwa [Matrix.transpose_apply] at this
  have hdet : E qIdx qIdx * E pIdx pIdx - E qIdx pIdx * E qIdx pIdx = 1 := by
    unfold det2 at hd
    linear_combination hd + E qIdx pIdx * hsym
  have hsq : (√(E qIdx qIdx)) ^ 2 = E qIdx qIdx := Real.sq_sqrt he1.le
  have hr0 : (√(E qIdx qIdx) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 he1).ne'
  have hs2 : s ^ 2 = 1 := by rcases hs1 with rfl | rfl <;> norm_num
  apply cell_ext <;>
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, vecMulVec_apply,
      Pi.star_apply, Sum.elim_inl, Sum.elim_inr, omega_qq, omega_qp, omega_pq, omega_pp,
      smul_eq_mul, mul_zero, add_zero, mul_one, mul_neg, Complex.star_def, map_div₀,
      map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, hsym]
  · rw [← Complex.ofReal_mul, ← sq, hsq]
  · field_simp; ring
  · field_simp; ring
  · field_simp
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sq] <;>
      nlinarith [hdet, hsq, hs2]

/-- Milestone Q4a, Proposition 20: for a real symmetric positive definite one-mode matrix `E`
with `det E = 1`, `g E + iΩ ≥ 0` holds exactly when `g ≥ 1`. (notes: `prop:es-threshold`) -/
theorem smul_add_posSemidef_iff {E : Matrix Cell Cell ℝ} (hs : Eᵀ = E) (hpd : E.PosDef)
    (hd : det2 E = 1) (g : ℝ) :
    ((g • E).map Complex.ofReal + Complex.I • Ωc).PosSemidef ↔ 1 ≤ g := by
  rw [map_symplecticForm_one]
  have hA : ((g • E).map Complex.ofReal).IsHermitian :=
    isHermitian_map_ofReal (by rw [Matrix.transpose_smul, hs])
  have he1 : 0 < E qIdx qIdx := hpd.diag_pos
  constructor
  · intro hp
    have hdiag := hp.diag_nonneg (i := qIdx)
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, omega_qq, smul_eq_mul,
      mul_zero, add_zero, Complex.ofReal_mul] at hdiag
    have hg0 : 0 ≤ g := by
      have : (0 : ℝ) ≤ g * E qIdx qIdx := by exact_mod_cast hdiag
      exact nonneg_of_mul_nonneg_left this he1
    have hdet := hp.det_nonneg
    have ed := det_add_I_omega hA 1
    rw [Complex.ofReal_one, one_mul] at ed
    rw [ed, ← det2_eq_det] at hdet
    have hdg : det2 ((g • E).map Complex.ofReal) = ((g ^ 2 : ℝ) : ℂ) := by
      simp only [det2, Matrix.map_apply]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
      congr 1
      have := det2_smul g E
      rw [hd, mul_one] at this
      exact this
    rw [hdg] at hdet
    simp only [Matrix.map_apply, Complex.ofReal_im, one_pow] at hdet
    rw [show ((g ^ 2 : ℝ) : ℂ) - 1 = ((g ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring] at hdet
    simp only [Complex.ofReal_zero, mul_zero, sub_zero] at hdet
    have h2 := Complex.zero_le_real.1 hdet
    by_contra hlt
    rw [not_le] at hlt
    nlinarith [hg0, h2, hlt]
  · intro hg
    have hA1 := add_I_omega_eq_vecMulVec hs he1 hd 1 (Or.inl rfl)
    have hA2 := add_I_omega_eq_vecMulVec hs he1 hd (-1) (Or.inr rfl)
    have split : (g • E).map Complex.ofReal + Complex.I • (omega : Matrix Cell Cell ℂ) =
        (((g + 1) / 2 : ℝ) : ℂ) • (E.map Complex.ofReal +
            (((1 : ℝ) : ℂ) * Complex.I) • (omega : Matrix Cell Cell ℂ)) +
          (((g - 1) / 2 : ℝ) : ℂ) • (E.map Complex.ofReal +
            (((-1 : ℝ) : ℂ) * Complex.I) • (omega : Matrix Cell Cell ℂ)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_ofNat]
      ring
    rw [split, hA1, hA2]
    refine Matrix.PosSemidef.add ?_ ?_
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by
        exact_mod_cast (show (0 : ℝ) ≤ (g + 1) / 2 by linarith))
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by
        exact_mod_cast (show (0 : ℝ) ≤ (g - 1) / 2 by linarith))

/-- Milestone Q4a, Proposition 20, for `E = ε̂(k)`: the state condition `g ε̂(k) + iΩ ≥ 0` holds
exactly when `g ≥ 1`. (notes: `prop:es-threshold`) -/
theorem smul_epsHat_add_posSemidef_iff (hr : ExampleRegime φ lam) (k g : ℝ) :
    ((g • epsHat φ lam k).map Complex.ofReal + Complex.I • Ωc).PosSemidef ↔ 1 ≤ g :=
  smul_add_posSemidef_iff (epsHat_transpose hr k) (epsHat_posDef hr k) (det2_epsHat hr k) g

/-- `ε̂(k) ≠ 0` in the regime. -/
theorem epsHat_ne_zero (hr : ExampleRegime φ lam) (k : ℝ) : epsHat φ lam k ≠ 0 := by
  intro h
  have := det2_epsHat hr k
  rw [h] at this
  simp [det2] at this

variable (φ lam) in
/-- Milestone Q4a, Corollary 23: the coefficient `g_k(S) = −½ tr(Ω ε̂(k) Ω S)`.
(notes: `cor:es-coeff`) -/
noncomputable def epsCoeff (k : ℝ) (S : Matrix Cell Cell ℝ) : ℝ :=
  -(1 / 2) * (omega * epsHat φ lam k * omega * S).trace

/-- Milestone Q4a, Corollary 23: `g_k(g ε̂(k)) = g`. (notes: `cor:es-coeff`) -/
theorem epsCoeff_smul (hr : ExampleRegime φ lam) (k g : ℝ) :
    epsCoeff φ lam k (g • epsHat φ lam k) = g := by
  rw [epsCoeff, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_assoc (omega * epsHat φ lam k),
    ← sq, omega_mul_epsHat_sq hr, Matrix.trace_neg, Matrix.trace_one]
  simp
  ring

/-- Milestone Q4a, Corollary 23: every invariant real symmetric form of `Γ̂(k)` is
`g_k(S) ε̂(k)`. (notes: `cor:es-coeff`) -/
theorem eq_epsCoeff_smul_of_invariant (hr : ExampleRegime φ lam) (k : ℝ)
    {S : Matrix Cell Cell ℝ} (hS : Sᵀ = S)
    (hSA : (exampleSymbol φ lam k)ᵀ * S * exampleSymbol φ lam k = S) :
    S = epsCoeff φ lam k S • epsHat φ lam k := by
  have he : |(exampleSymbol φ lam k).trace| < 2 :=
    (lt_one_iff_forall_abs_trace_lt φ lam).1 hr.lt_one k
  obtain ⟨g, hg, -⟩ := eq_smul_of_invariant_sl2 (det2_exampleSymbol φ lam k) he
    (epsHat_transpose hr k) (epsHat_invariant φ lam k) (epsHat_ne_zero hr k) hS hSA
  rw [hg, epsCoeff_smul hr]

end Eps

/-! ### Theorem 4.8 -/

section Stationary

variable {φ lam : ℝ}

/-- Complexification of real one-mode matrices is injective. -/
theorem map_ofReal_injective {A B : Matrix Cell Cell ℝ}
    (h : A.map Complex.ofReal = B.map Complex.ofReal) : A = B := by
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

/-- Milestone Q4a, Theorem 24, (ii) ⇒ (i): cells with `γ̂(k) = g(k) ε̂(k)`, `g ≥ 1`, are stationary
and satisfy the Fourier state condition. (notes: `thm:es-stationary`) -/
theorem stationary_of_eq_smul_epsHat (hr : ExampleRegime φ lam) {γc : ℤ → Matrix Cell Cell ℝ}
    (h : CellData γc) {g : ℝ → ℝ} (hg1 : ∀ k, 1 ≤ g k)
    (hγ : ∀ k, gammaHat γc k = (g k • epsHat φ lam k).map Complex.ofReal) :
    evolveCells (rotationSymbol φ lam) γc = γc ∧
      ∀ k, (gammaHat γc k + Complex.I • Ωc).PosSemidef := by
  refine ⟨gammaHat_injective (evolveCells_cellData _ h) h fun k => ?_, fun k => ?_⟩
  · rw [gammaHat_evolve_example φ lam h, hγ, ← map_ofReal_mul, ← map_ofReal_mul,
      Matrix.mul_smul, Matrix.smul_mul, epsHat_invariant]
  · rw [hγ]
    exact (smul_epsHat_add_posSemidef_iff hr k (g k)).2 (hg1 k)

/-- Milestone Q4a, Theorem 24, (i) ⇒ (ii): every stationary reflection-symmetric admissible cell
family satisfying the Fourier state condition has `γ̂(k) = g(k) ε̂(k)` with `g` continuous, even
and `g ≥ 1`. (notes: `thm:es-stationary`) -/
theorem eq_smul_epsHat_of_stationary (hr : ExampleRegime φ lam) {γc : ℤ → Matrix Cell Cell ℝ}
    (h : CellData γc) (hrefl : ∀ x, γc (-x) = γc x)
    (hst : evolveCells (rotationSymbol φ lam) γc = γc)
    (hsc : ∀ k, (gammaHat γc k + Complex.I • Ωc).PosSemidef) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ k, g (-k) = g k) ∧ (∀ k, 1 ≤ g k) ∧
      ∀ k, gammaHat γc k = (g k • epsHat φ lam k).map Complex.ofReal := by
  set S : ℝ → Matrix Cell Cell ℝ := fun k => (gammaHat γc k).map Complex.re
  have hSre : ∀ k, gammaHat γc k = (S k).map Complex.ofReal := fun k =>
    (gammaHat_real h hrefl k).1
  have hSsym : ∀ k, (S k)ᵀ = S k := fun k => (gammaHat_real h hrefl k).2
  have hSinv : ∀ k, (exampleSymbol φ lam k)ᵀ * S k * exampleSymbol φ lam k = S k := fun k => by
    have e := gammaHat_evolve_example φ lam h k
    rw [hst, hSre k, ← map_ofReal_mul, ← map_ofReal_mul] at e
    exact (map_ofReal_injective e).symm
  have hSg : ∀ k, S k = epsCoeff φ lam k (S k) • epsHat φ lam k := fun k =>
    eq_epsCoeff_smul_of_invariant hr k (hSsym k) (hSinv k)
  have hγ : ∀ k, gammaHat γc k = (epsCoeff φ lam k (S k) • epsHat φ lam k).map Complex.ofReal :=
    fun k => by rw [hSre k, ← hSg k]
  refine ⟨fun k => epsCoeff φ lam k (S k), ?_, fun k => ?_, fun k => ?_, hγ⟩
  · have hScont : Continuous S :=
      (continuous_gammaHat h.summable).matrix_map Complex.continuous_re
    exact continuous_const.mul ((((continuous_const.matrix_mul (continuous_epsHat hr)).matrix_mul
      continuous_const).matrix_mul hScont).matrix_trace)
  · simp only [epsCoeff, S, epsHat_neg, gammaHat_neg_of_refl hrefl]
  · have := hsc k
    rw [hγ k] at this
    exact (smul_epsHat_add_posSemidef_iff hr k _).1 this

/-- Milestone Q4a, Theorem 24 (thesis Theorem 4.8, with the completeness half): in the regime,
reflection-symmetric admissible cells are stationary and satisfy the Fourier state condition
exactly when `γ̂(k) = g(k) ε̂(k)` with `g` continuous, even and `g ≥ 1`.
(notes: `thm:es-stationary`) -/
theorem stationary_iff (hr : ExampleRegime φ lam) {γc : ℤ → Matrix Cell Cell ℝ}
    (h : CellData γc) (hrefl : ∀ x, γc (-x) = γc x) :
    (evolveCells (rotationSymbol φ lam) γc = γc ∧
        ∀ k, (gammaHat γc k + Complex.I • Ωc).PosSemidef) ↔
      ∃ g : ℝ → ℝ, Continuous g ∧ (∀ k, g (-k) = g k) ∧ (∀ k, 1 ≤ g k) ∧
        ∀ k, gammaHat γc k = (g k • epsHat φ lam k).map Complex.ofReal := by
  constructor
  · rintro ⟨hst, hsc⟩
    exact eq_smul_epsHat_of_stationary hr h hrefl hst hsc
  · rintro ⟨g, -, -, hg1, hγ⟩
    exact stationary_of_eq_smul_epsHat hr h hg1 hγ

/-- Milestone Q4a, remark after Theorem 24: a symbol `γ̂(k) = g(k) ε̂(k)` has
`det γ̂(k) = g(k)²`. (notes: `thm:es-stationary`) -/
theorem det_gammaHat_of_eq_smul_epsHat (hr : ExampleRegime φ lam)
    {γc : ℤ → Matrix Cell Cell ℝ} {g : ℝ → ℝ}
    (hγ : ∀ k, gammaHat γc k = (g k • epsHat φ lam k).map Complex.ofReal) (k : ℝ) :
    (gammaHat γc k).det = ((g k ^ 2 : ℝ) : ℂ) := by
  rw [hγ, ← det2_eq_det]
  simp only [det2, Matrix.map_apply]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  congr 1
  have := det2_smul (g k) (epsHat φ lam k)
  rw [det2_epsHat hr, mul_one] at this
  exact this

/-- Milestone Q4a, remark after Theorem 24: the stationary state with `g ≡ 1` has
`det γ̂(k) = 1`, the pure one. -/
theorem det_gammaHat_of_eq_epsHat (hr : ExampleRegime φ lam) {γc : ℤ → Matrix Cell Cell ℝ}
    (hγ : ∀ k, gammaHat γc k = (epsHat φ lam k).map Complex.ofReal) (k : ℝ) :
    (gammaHat γc k).det = 1 := by
  have := det_gammaHat_of_eq_smul_epsHat hr (g := fun _ => 1)
    (fun k => by rw [hγ, one_smul]) k
  rw [this, one_pow, Complex.ofReal_one]

end Stationary

end QCALean.Bosonic
