/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.NearestNeighbour
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Fourier symbol on the unit circle

Evaluating a symbol at `z = e^{-ik}` gives Krüger's Fourier symbol `Γ̂(k) = Σ_m ℓ_m e^{-ikm}`
(thesis (4.14)–(4.15)). The involution `z ↦ z⁻¹` becomes complex conjugation on the circle, so a
symplectic rule is symplectic on every Fourier mode (thesis p. 82). Milestone Q1, Lemma 15 and
Examples 18–19.

## Main definitions and results

* `QCALean.Bosonic.evalCircle k`: evaluation at `e^{-ik}`, a ring homomorphism `ℝ[ℤ] → ℂ`.
* `QCALean.Bosonic.evalCircle_apply`: `p(e^{-ik}) = Σ_m p_m e^{-ikm}`.
* `QCALean.Bosonic.fourierSymbol_symplectic`: `Γ̂(k)ᴴ Ω Γ̂(k) = Ω`.
* `QCALean.Bosonic.leapfrog_trace`, `QCALean.Bosonic.rotation_example`.
-/

open Matrix LaurentPolynomial QCALean.Core ComplexConjugate Gaussian

namespace QCALean.Bosonic

/-- The unit `e^{-ik}` of `ℂ`. -/
noncomputable def circleUnit (k : ℝ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(k : ℂ) * Complex.I)) (Complex.exp_ne_zero _)

/-- Evaluation of a Laurent polynomial at `z = e^{-ik}` (thesis (4.14)).
(notes: `lem:qca-circle`) -/
noncomputable def evalCircle (k : ℝ) : L →+* ℂ :=
  LaurentPolynomial.eval₂ (algebraMap ℝ ℂ) (circleUnit k)

theorem evalCircle_single (k : ℝ) (m : ℤ) (c : ℝ) :
    evalCircle k (AddMonoidAlgebra.single m c) = c * Complex.exp (-(k : ℂ) * m * Complex.I) := by
  rw [single_eq_C_mul_T, evalCircle, eval₂_C_mul_T, Units.val_zpow_eq_zpow_val, circleUnit,
    Units.val_mk0, ← Complex.exp_int_mul]
  simp only [Complex.coe_algebraMap]
  ring_nf

/-- Milestone Q1, Lemma 15: `p(e^{-ik}) = Σ_m p_m e^{-ikm}`. (notes: `lem:qca-circle`) -/
theorem evalCircle_apply (k : ℝ) (p : L) :
    evalCircle k p = (AddMonoidAlgebra.coeff p).sum
      fun m c => (c : ℂ) * Complex.exp (-(k : ℂ) * m * Complex.I) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  rw [map_finsuppSum]
  simp only [evalCircle_single]

/-- On the circle the involution `z ↦ z⁻¹` is complex conjugation. (notes: `lem:qca-circle`) -/
theorem evalCircle_involution (k : ℝ) (p : L) :
    evalCircle k (involution ℝ ℤ p) = conj (evalCircle k p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T n a =>
    rw [← single_eq_C_mul_T, involution_single, evalCircle_single, evalCircle_single, map_mul,
      Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal, Complex.conj_I]

/-- The Fourier symbol of a rule: its symbol evaluated entrywise on the unit circle.
(notes: `ex:qca-modes`) -/
noncomputable def fourierSymbol {ι : Type*} (k : ℝ) (M : Matrix ι ι L) : Matrix ι ι ℂ :=
  M.map (evalCircle k)

theorem circleUnit_add_two_pi (k : ℝ) : circleUnit (k + 2 * Real.pi) = circleUnit k := by
  ext
  simp only [circleUnit, Units.val_mk0]
  have : -((k + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
      -(k : ℂ) * Complex.I + ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Milestone Q4a, Proposition 1(a): the Fourier symbol of a rule is `2π`-periodic.
(notes: `prop:es-iterate`) -/
theorem fourierSymbol_add_two_pi {ι : Type*} (M : Matrix ι ι L) (k : ℝ) :
    fourierSymbol (k + 2 * Real.pi) M = fourierSymbol k M := by
  simp only [fourierSymbol, evalCircle, circleUnit_add_two_pi]

/-- Milestone Q4a, Proposition 1(b): the Fourier symbol of a power is the power of the Fourier
symbol. (notes: `prop:es-iterate`) -/
theorem fourierSymbol_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι L) (k : ℝ)
    (t : ℕ) : fourierSymbol k (M ^ t) = fourierSymbol k M ^ t :=
  map_pow (evalCircle k).mapMatrix M t

section Fourier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem fourierSymbol_mul (k : ℝ) (M N : Matrix ι ι L) :
    fourierSymbol k (M * N) = fourierSymbol k M * fourierSymbol k N :=
  Matrix.map_mul

omit [Fintype ι] [DecidableEq ι] in
theorem fourierSymbol_add (k : ℝ) (M N : Matrix ι ι L) :
    fourierSymbol k (M + N) = fourierSymbol k M + fourierSymbol k N :=
  Matrix.map_add _ (map_add _) M N

omit [Fintype ι] [DecidableEq ι] in
theorem fourierSymbol_starTranspose (k : ℝ) (M : Matrix ι ι L) :
    fourierSymbol k (starTranspose M) = (fourierSymbol k M)ᴴ := by
  ext i j
  simp [fourierSymbol, starTranspose, evalCircle_involution]

omit [Fintype ι] [DecidableEq ι] in
theorem fourierSymbol_const (k : ℝ) (B : Matrix ι ι ℝ) :
    fourierSymbol k (const ℤ B) = B.map Complex.ofReal := by
  ext i j
  simp [fourierSymbol, const, evalCircle, Complex.coe_algebraMap]

omit [Fintype ι] [DecidableEq ι] in
theorem fourierSymbol_mono (k : ℝ) (m : ℤ) (A : Matrix ι ι ℝ) :
    fourierSymbol k (mono m A) = Complex.exp (-(k : ℂ) * m * Complex.I) • A.map Complex.ofReal := by
  ext i j
  simp only [fourierSymbol, Matrix.map_apply, mono_apply, evalCircle_single, Matrix.smul_apply,
    smul_eq_mul, mul_comm]

/-- Milestone Q1, Example 18: a symplectic rule is symplectic on every Fourier mode,
`Γ̂(k)ᴴ Ω Γ̂(k) = Ω` (thesis p. 82). (notes: `ex:qca-modes`) -/
theorem fourierSymbol_symplectic {n : ℕ}
    {M : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) L}
    (h : starTranspose M * const ℤ (Gaussian.symplecticForm n) * M =
      const ℤ (Gaussian.symplecticForm n)) (k : ℝ) :
    (fourierSymbol k M)ᴴ * (Gaussian.symplecticForm n).map Complex.ofReal * fourierSymbol k M =
      (Gaussian.symplecticForm n).map Complex.ofReal := by
  have := congrArg (fourierSymbol k) h
  rwa [fourierSymbol_mul, fourierSymbol_mul, fourierSymbol_starTranspose,
    fourierSymbol_const] at this

end Fourier

/-- Milestone Q1, Lemma 15: the trace of the leapfrog Fourier symbol is `2 cos k - m²`.
(notes: `ex:qca-modes`) -/
theorem leapfrog_trace (m2 k : ℝ) :
    (fourierSymbol k (leapfrogSymbol m2)).trace = 2 * Real.cos k - m2 := by
  simp only [leapfrogSymbol, nnSymbol, fourierSymbol_add, fourierSymbol_mono]
  simp only [trace, Int.reduceNeg, Int.cast_neg, Int.cast_one, mul_neg, mul_one, neg_neg,
    leapfrogShift, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, leapfrogCentre, one_smul,
    neg_mul, diag_apply, Matrix.add_apply, Matrix.smul_apply, map_apply, of_apply, smul_eq_mul,
    Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Complex.ofReal_zero,
    add_zero, Finset.sum_const_zero, Complex.ofReal_one, Complex.ofReal_neg, Finset.sum_const,
    Finset.card_singleton, smul_add, smul_neg, zero_add, Complex.ofReal_cos]
  rw [Complex.cos]
  ring_nf

/-- The rotation by `φ`, the `z⁰` coefficient of Krüger's example system (4.18). -/
noncomputable def rotation (φ : ℝ) : Matrix Cell Cell ℝ :=
  Matrix.of fun i j => match i, j with
    | Sum.inl _, Sum.inl _ => Real.cos φ
    | Sum.inl _, Sum.inr _ => -Real.sin φ
    | Sum.inr _, Sum.inl _ => Real.sin φ
    | Sum.inr _, Sum.inr _ => Real.cos φ

/-- Krüger's example system (4.18): `ℓ₀` the rotation by `φ` and
`ℓ± = λ [[sin φ, cos φ], [0, 0]] = λ e₁ rᵀ`, `r` the momentum row of the rotation.
(notes: `ex:qca-rotation`) -/
noncomputable def rotationSymbol (φ lam : ℝ) : Matrix Cell Cell L :=
  nnSymbol (vecMulVec e1 (lam • rotation φ pIdx)) (rotation φ)
    (vecMulVec e1 (lam • rotation φ pIdx))

/-- Milestone Q1, Example 19: Krüger's example system is symplectic for every `φ, λ`, and the
trace of its Fourier symbol is `2 cos φ + 2 λ cos k sin φ`, that is
`cos α(k) = cos φ + λ cos k sin φ` (thesis (4.19)). (notes: `ex:qca-rotation`) -/
theorem rotation_example (φ lam k : ℝ) :
    starTranspose (rotationSymbol φ lam) * mono 0 omega * rotationSymbol φ lam = mono 0 omega ∧
    (fourierSymbol k (rotationSymbol φ lam)).trace =
      2 * Real.cos φ + 2 * lam * Real.cos k * Real.sin φ := by
  constructor
  · apply nn_form_symplectic
    rw [transpose_mul_omega_mul_self_eq_iff]
    simp [det2, rotation]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  · simp only [rotationSymbol, nnSymbol, fourierSymbol_add, fourierSymbol_mono]
    simp only [trace, Int.reduceNeg, Int.cast_neg, Int.cast_one, mul_neg, mul_one, neg_neg, e1,
      rotation, vecMulVec_smul, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_smul,
      neg_mul, diag_apply, Matrix.add_apply, Matrix.smul_apply, map_apply, vecMulVec_apply,
      of_apply, smul_eq_mul, Complex.ofReal_mul, Fintype.sum_sum_type, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, Complex.ofReal_sin, Complex.ofReal_cos,
      Finset.sum_singleton, Pi.single_eq_same, Complex.ofReal_one, one_mul, ne_eq, reduceCtorEq,
      not_false_eq_true, Pi.single_eq_of_ne, Complex.ofReal_zero, zero_add, add_zero,
      Finset.sum_const, Finset.card_singleton]
    have hc : 2 * Complex.cos k = Complex.exp (k * Complex.I) + Complex.exp (-(k * Complex.I)) := by
      rw [Complex.cos]; ring_nf
    linear_combination (-(lam * Complex.sin φ)) * hc

end QCALean.Bosonic
