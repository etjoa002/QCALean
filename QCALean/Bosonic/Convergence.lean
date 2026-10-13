/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.Stationary
import QCALean.Core.RiemannLebesgue
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# Convergence to the stationary states

Milestone Q4b. In the regime, the covariance of Krüger's example system converges on every finite
region (thesis Proposition 4.7): the cells of the evolved covariance tend to the Fourier
coefficients of the limit symbol `C(k) = ½(γ̂(k) + N(k)ᵀ γ̂(k) N(k))`, because the oscillating
parts, with phases `e^{±2itθ(k)}`, vanish by the Riemann–Lebesgue lemma along the monotone phase
`θ`. The limit symbol is invariant and inherits the state condition. For a Gaussian initial state
with zero displacement, the characteristic functions converge pointwise and the evolved states
converge on every observable to a Gaussian state (the weak-* part of thesis Theorem 4.9).

## Main definitions and results

* `QCALean.Bosonic.limitSymbol`, `QCALean.Bosonic.limitCells`
* `QCALean.Bosonic.tendsto_iterate_evolveCells`: thesis Proposition 4.7.
* `QCALean.Bosonic.limitSymbol_eq_smul_epsHat`: the limit has the form of thesis Theorem 4.8.
* `QCALean.Bosonic.exists_limit_state`: thesis Theorem 4.9, weak-* part.
-/

open LinearAQFT QCALean.Core Matrix Filter Topology Gaussian
open scoped ComplexOrder ComplexConjugate

namespace QCALean.Bosonic

variable {φ lam : ℝ}

/-! ### Oscillatory integrals of the example -/

section Oscillatory

/-- `θ'(k) ≠ 0` away from `k ∈ πℤ`, in the regime. -/
theorem alpha_deriv_ne_zero (hr : ExampleRegime φ lam) {k : ℝ} (hk : Real.sin k ≠ 0) :
    lam * Real.sin φ * Real.sin k / Real.sin (alpha φ lam k) ≠ 0 :=
  div_ne_zero (mul_ne_zero hr.ne_zero hk) (sin_alpha_pos hr k).ne'

/-- `θ` is injective on `(0, π)` in the regime. -/
theorem injOn_alpha_Ioo (hr : ExampleRegime φ lam) :
    Set.InjOn (alpha φ lam) (Set.Ioo 0 Real.pi) := by
  rcases lt_or_gt_of_ne hr.ne_zero with hneg | hpos
  · exact (strictAntiOn_alpha hr hneg).injOn.mono Set.Ioo_subset_Icc_self
  · exact (strictMonoOn_alpha hr hpos).injOn.mono Set.Ioo_subset_Icc_self

/-- `θ` is injective on `(−π, 0)` in the regime, by evenness. -/
theorem injOn_alpha_Ioo_neg (hr : ExampleRegime φ lam) :
    Set.InjOn (alpha φ lam) (Set.Ioo (-Real.pi) 0) := by
  intro x hx y hy hxy
  have hx' : -x ∈ Set.Ioo 0 Real.pi := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hy' : -y ∈ Set.Ioo 0 Real.pi := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have := injOn_alpha_Ioo hr hx' hy' (by rw [alpha_neg, alpha_neg]; exact hxy)
  linarith

/-- Milestone Q4b, Corollary 2 (one half): the oscillatory integral over one half of the circle,
with phase `σθ`, `σ ≠ 0`. -/
theorem tendsto_half (hr : ExampleRegime φ lam) (h : ℝ → ℂ) {σ : ℝ} (hσ : σ ≠ 0)
    {s : Set ℝ} (hsI : s = Set.Ioo 0 Real.pi ∨ s = Set.Ioo (-Real.pi) 0) :
    Tendsto (fun r : ℝ => ∫ k in s, h k *
      Complex.exp (r * ((σ * alpha φ lam k : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hs : MeasurableSet s := by rcases hsI with rfl | rfl <;> exact measurableSet_Ioo
  have hsin : ∀ k ∈ s, Real.sin k ≠ 0 := by
    rcases hsI with rfl | rfl
    · exact fun k hk => (Real.sin_pos_of_pos_of_lt_pi hk.1 hk.2).ne'
    · exact fun k hk => (Real.sin_neg_of_neg_of_neg_pi_lt hk.2 hk.1).ne
  have hinj : Set.InjOn (alpha φ lam) s := by
    rcases hsI with rfl | rfl
    · exact injOn_alpha_Ioo hr
    · exact injOn_alpha_Ioo_neg hr
  refine tendsto_setIntegral_mul_exp_of_injOn hs h (θ := fun k => σ * alpha φ lam k)
    (θ' := fun k => σ * (lam * Real.sin φ * Real.sin k / Real.sin (alpha φ lam k)))
    (fun x _ => ((hasDerivAt_alpha hr x).const_mul σ).hasDerivWithinAt)
    (fun x hx y hy hxy => hinj hx hy (mul_left_cancel₀ hσ hxy))
    (fun x hx => mul_ne_zero hσ (alpha_deriv_ne_zero hr (hsin x hx)))

/-- Milestone Q4b, Corollary 2: in the regime, for continuous `h` and `σ = ±1`, the oscillatory
integrals `∫_{−π}^{π} h(k) e^{iσ 2t θ(k)} dk` tend to zero along `t ∈ ℕ`.
(notes: `cor:cv-rl`) -/
theorem tendsto_integral_mul_exp_alpha (hr : ExampleRegime φ lam) {h : ℝ → ℂ}
    (hh : Continuous h) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun t : ℕ => ∫ k in (-Real.pi)..Real.pi,
      h k * Complex.exp (((σ * (2 * t) * alpha φ lam k : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hpi := Real.pi_pos
  set F : ℕ → ℝ → ℂ := fun t k =>
    h k * Complex.exp ((((2 * t : ℕ) : ℝ) : ℂ) * ((σ * alpha φ lam k : ℝ) : ℂ) * Complex.I)
  have hfun : ∀ t : ℕ, (fun k => h k *
      Complex.exp (((σ * (2 * t) * alpha φ lam k : ℝ) : ℂ) * Complex.I)) = F t := by
    intro t
    funext k
    simp only [F]
    congr 2
    push_cast
    ring
  have hint : ∀ t : ℕ, ∀ a b : ℝ, IntervalIntegrable (F t) MeasureTheory.volume a b := by
    intro t a b
    rw [← hfun t]
    exact (hh.mul (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_alpha φ lam))).mul continuous_const))).intervalIntegrable
        a b
  have hsplit : ∀ t : ℕ, ∫ k in (-Real.pi)..Real.pi, F t k =
      (∫ k in Set.Ioo (-Real.pi) 0, F t k) + ∫ k in Set.Ioo 0 Real.pi, F t k := by
    intro t
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint t (-Real.pi) 0)
      (hint t 0 Real.pi), intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_of_le hpi.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have h2t : Tendsto (fun t : ℕ => (((2 * t : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  have e : (fun t : ℕ => ∫ k in (-Real.pi)..Real.pi,
      h k * Complex.exp (((σ * (2 * t) * alpha φ lam k : ℝ) : ℂ) * Complex.I)) =
      fun t => (∫ k in Set.Ioo (-Real.pi) 0, F t k) + ∫ k in Set.Ioo 0 Real.pi, F t k := by
    funext t
    rw [hfun t, hsplit t]
  rw [e, ← add_zero (0 : ℂ)]
  exact ((tendsto_half hr h hσ0 (Or.inr rfl)).comp h2t).add
    ((tendsto_half hr h hσ0 (Or.inl rfl)).comp h2t)

end Oscillatory

/-! ### The evolved symbol -/

section Symbol

/-- The real form of the powers, `Γ̂(k)^t = cos(tθ) 1 − sin(tθ) N(k)`. -/
theorem exampleSymbol_pow_eq_cos_sub_sin (hr : ExampleRegime φ lam) (k : ℝ) (t : ℕ) :
    exampleSymbol φ lam k ^ t = Real.cos (t * alpha φ lam k) • (1 : Matrix Cell Cell ℝ) -
      Real.sin (t * alpha φ lam k) • nMat φ lam k := by
  have hs := (sin_alpha_pos hr k).ne'
  rw [exampleSymbol_pow hr]
  conv_lhs => rw [exampleSymbol_eq_nMat hr k]
  have e : Real.sin (((t : ℝ) - 1) * alpha φ lam k) = Real.sin (t * alpha φ lam k) *
      Real.cos (alpha φ lam k) - Real.cos (t * alpha φ lam k) * Real.sin (alpha φ lam k) := by
    rw [show ((t : ℝ) - 1) * alpha φ lam k = t * alpha φ lam k - alpha φ lam k by ring,
      Real.sin_sub]
  rw [e]
  match_scalars
  · field_simp
    ring
  · field_simp

/-- Milestone Q4b, Lemma 3: the quadratic split
`(Γ̂^t)ᵀ A Γ̂^t = C + cos(2tθ) A_c + sin(2tθ) A_s`. (notes: `lem:cv-split`) -/
theorem pow_transpose_mul_mul_pow (hr : ExampleRegime φ lam) (k : ℝ) (A : Matrix Cell Cell ℂ)
    (t : ℕ) :
    ((exampleSymbol φ lam k ^ t)ᵀ).map Complex.ofReal * A *
        (exampleSymbol φ lam k ^ t).map Complex.ofReal =
      (1 / 2 : ℂ) • (A + ((nMat φ lam k)ᵀ).map Complex.ofReal * A *
          (nMat φ lam k).map Complex.ofReal) +
        (Real.cos (2 * t * alpha φ lam k) : ℂ) • ((1 / 2 : ℂ) • (A -
          ((nMat φ lam k)ᵀ).map Complex.ofReal * A * (nMat φ lam k).map Complex.ofReal)) +
        (Real.sin (2 * t * alpha φ lam k) : ℂ) • (-(1 / 2 : ℂ) •
          (((nMat φ lam k)ᵀ).map Complex.ofReal * A + A * (nMat φ lam k).map Complex.ofReal)) := by
  set x := (t : ℝ) * alpha φ lam k
  have hcs : (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq x
  rw [show 2 * (t : ℝ) * alpha φ lam k = 2 * x by ring, Real.cos_two_mul, Real.sin_two_mul,
    exampleSymbol_pow_eq_cos_sub_sin hr]
  set N := nMat φ lam k
  have hT : ((Real.cos x • (1 : Matrix Cell Cell ℝ) - Real.sin x • N)ᵀ).map Complex.ofReal =
      (Real.cos x : ℂ) • 1 - (Real.sin x : ℂ) • (Nᵀ).map Complex.ofReal := by
    ext i j; by_cases hij : i = j <;> simp [hij, Matrix.transpose_apply]
  have hM : (Real.cos x • (1 : Matrix Cell Cell ℝ) - Real.sin x • N).map Complex.ofReal =
      (Real.cos x : ℂ) • 1 - (Real.sin x : ℂ) • N.map Complex.ofReal := by
    ext i j; by_cases hij : i = j <;> simp [hij]
  rw [hT, hM]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_sub, smul_add, smul_smul, Matrix.mul_assoc]
  push_cast at hcs ⊢
  match_scalars <;> first | linear_combination hcs | linear_combination (1 / 2 : ℂ) * hcs |
    linear_combination (-(1 / 2) : ℂ) * hcs | ring

/-- The Fourier symbol of `L^t` is `Γ̂(k)^t`, as a complex matrix. -/
theorem fourierSymbol_rotationSymbol_pow (k : ℝ) (t : ℕ) :
    fourierSymbol k (rotationSymbol φ lam ^ t) =
      (exampleSymbol φ lam k ^ t).map Complex.ofReal := by
  rw [fourierSymbol_pow, fourierSymbol_rotationSymbol]
  exact (map_pow (Complex.ofRealHom.mapMatrix) (exampleSymbol φ lam k) t).symm

/-- Milestone Q4b, Lemma 4: the symbol of the iterates, `γ̂_t(k) = (Γ̂(k)^t)ᵀ γ̂(k) Γ̂(k)^t`.
(notes: `lem:cv-split`) -/
theorem gammaHat_iterate_example {γc : ℤ → Matrix Cell Cell ℝ} (h : CellData γc) (t : ℕ)
    (k : ℝ) :
    gammaHat ((evolveCells (rotationSymbol φ lam))^[t] γc) k =
      ((exampleSymbol φ lam k ^ t)ᵀ).map Complex.ofReal * gammaHat γc k *
        (exampleSymbol φ lam k ^ t).map Complex.ofReal := by
  rw [evolveCells_iterate, gammaHat_evolve _ h.summable, fourierSymbol_rotationSymbol_pow,
    fourierSymbol_rotationSymbol_pow, exampleSymbol_neg, Matrix.transpose_map]

end Symbol

/-! ### The limit covariance -/

section Limit

variable (φ lam) in
/-- `N(−k) = N(k)`, for all parameters. -/
theorem nMat_neg (k : ℝ) : nMat φ lam (-k) = nMat φ lam k := by
  rw [nMat, nMat, alpha_neg, exampleSymbol_neg]

/-- `N` is continuous in the regime. -/
theorem continuous_nMat (hr : ExampleRegime φ lam) : Continuous (nMat φ lam) := by
  have hα := continuous_alpha φ lam
  refine Continuous.smul ((Real.continuous_sin.comp hα).inv₀ fun k => (sin_alpha_pos hr k).ne') ?_
  exact ((Real.continuous_cos.comp hα).smul continuous_const).sub (continuous_exampleSymbol φ lam)

variable (φ lam) in
/-- Milestone Q4b, Definition 5: the limit symbol `C(k) = ½(γ̂(k) + N(k)ᵀ γ̂(k) N(k))`.
(notes: `def:cv-limit`) -/
noncomputable def limitSymbol (γc : ℤ → Matrix Cell Cell ℝ) (k : ℝ) : Matrix Cell Cell ℂ :=
  (1 / 2 : ℂ) • (gammaHat γc k + ((nMat φ lam k)ᵀ).map Complex.ofReal * gammaHat γc k *
    (nMat φ lam k).map Complex.ofReal)

variable (φ lam) in
/-- Milestone Q4b, Definition 5: the limit cells `γ∞,x = (2π)⁻¹ ∫_{−π}^{π} e^{ikx} C(k) dk`, taken
entrywise as the real part of the integral, which is real (`limitCells_real`).
(notes: `def:cv-limit`) -/
noncomputable def limitCells (γc : ℤ → Matrix Cell Cell ℝ) (x : ℤ) : Matrix Cell Cell ℝ :=
  Matrix.of fun a b => (((2 * Real.pi)⁻¹ : ℂ) *
    ∫ k in (-Real.pi)..Real.pi, Complex.exp ((k : ℂ) * x * Complex.I) *
      limitSymbol φ lam γc k a b).re

/-- `C(−k) = conj C(k)`, for all parameters. -/
theorem limitSymbol_neg {γc : ℤ → Matrix Cell Cell ℝ} (h : CellData γc) (k : ℝ) :
    limitSymbol φ lam γc (-k) = (limitSymbol φ lam γc k).map (starRingEnd ℂ) := by
  have h2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
  have hc : ∀ M : Matrix Cell Cell ℝ,
      (M.map Complex.ofReal).map (starRingEnd ℂ) = M.map Complex.ofReal := fun M => by
    ext; simp
  have key : (((nMat φ lam k)ᵀ).map Complex.ofReal * gammaHat γc k *
      (nMat φ lam k).map Complex.ofReal).map (starRingEnd ℂ) =
      ((nMat φ lam k)ᵀ).map Complex.ofReal * (gammaHat γc k).map (starRingEnd ℂ) *
        (nMat φ lam k).map Complex.ofReal := by
    rw [Matrix.map_mul, Matrix.map_mul, hc, hc]
  rw [limitSymbol, limitSymbol, nMat_neg, gammaHat_neg h.summable, ← key]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply, smul_eq_mul]
  rw [map_mul, map_add, h2]

/-- `C(k)` is Hermitian. -/
theorem limitSymbol_conj {γc : ℤ → Matrix Cell Cell ℝ} (h : CellData γc) (k : ℝ) (a b : Cell) :
    limitSymbol φ lam γc k b a = starRingEnd ℂ (limitSymbol φ lam γc k a b) := by
  have h2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
  have hNH : ((nMat φ lam k).map Complex.ofReal)ᴴ = ((nMat φ lam k)ᵀ).map Complex.ofReal := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hX : (gammaHat γc k + ((nMat φ lam k)ᵀ).map Complex.ofReal * gammaHat γc k *
      (nMat φ lam k).map Complex.ofReal).IsHermitian := by
    refine (gammaHat_isHermitian h k).add ?_
    rw [← hNH]
    exact Matrix.isHermitian_conjTranspose_mul_mul _ (gammaHat_isHermitian h k)
  simp only [limitSymbol, Matrix.smul_apply, smul_eq_mul]
  rw [map_mul, h2, ← hX.apply a b, Complex.star_def, Complex.conj_conj]

/-- Milestone Q4b, Lemma 6: the defining integral of the limit cells is real.
(notes: `lem:cv-limit`) -/
theorem limitCells_real {γc : ℤ → Matrix Cell Cell ℝ} (h : CellData γc) (x : ℤ) (a b : Cell) :
    ((2 * Real.pi)⁻¹ : ℂ) * ∫ k in (-Real.pi)..Real.pi,
        Complex.exp ((k : ℂ) * x * Complex.I) * limitSymbol φ lam γc k a b =
      (limitCells φ lam γc x a b : ℂ) := by
  set I := ∫ k in (-Real.pi)..Real.pi,
    Complex.exp ((k : ℂ) * x * Complex.I) * limitSymbol φ lam γc k a b
  have hI : starRingEnd ℂ I = I := by
    rw [conj_integral_pi]
    have e : ∀ k : ℝ, starRingEnd ℂ (Complex.exp ((k : ℂ) * x * Complex.I) *
        limitSymbol φ lam γc k a b) = (fun k : ℝ => Complex.exp ((k : ℂ) * x * Complex.I) *
          limitSymbol φ lam γc k a b) (-k) := by
      intro k
      simp only [map_mul, ← Complex.exp_conj, limitSymbol_neg h, Matrix.map_apply]
      congr 2
      simp only [Complex.conj_ofReal, Complex.conj_I, map_intCast]
      push_cast
      ring
    have hn := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi)
      (fun k : ℝ => Complex.exp ((k : ℂ) * x * Complex.I) * limitSymbol φ lam γc k a b)
    simp only [neg_neg] at hn
    rw [intervalIntegral.integral_congr (fun k _ => e k)]
    exact hn
  have hw : starRingEnd ℂ (((2 * Real.pi)⁻¹ : ℂ) * I) = ((2 * Real.pi)⁻¹ : ℂ) * I := by
    rw [map_mul, hI, map_inv₀, map_mul, map_ofNat, Complex.conj_ofReal]
  simp only [limitCells, Matrix.of_apply]
  exact (Complex.conj_eq_iff_re.1 hw).symm

/-- Milestone Q4b, Lemma 6: the limit cells are symmetric, `γ∞,−x = γ∞,xᵀ`.
(notes: `lem:cv-limit`) -/
theorem limitCells_symm {γc : ℤ → Matrix Cell Cell ℝ} (h : CellData γc) (x : ℤ) :
    limitCells φ lam γc (-x) = (limitCells φ lam γc x)ᵀ := by
  ext a b
  rw [Matrix.transpose_apply]
  apply Complex.ofReal_injective
  rw [← limitCells_real h, ← limitCells_real h]
  have e : ∫ k in (-Real.pi)..Real.pi, Complex.exp ((k : ℂ) * x * Complex.I) *
      limitSymbol φ lam γc k b a = starRingEnd ℂ (∫ k in (-Real.pi)..Real.pi,
        Complex.exp ((k : ℂ) * ((-x : ℤ) : ℂ) * Complex.I) * limitSymbol φ lam γc k a b) := by
    rw [conj_integral_pi]
    refine intervalIntegral.integral_congr fun k _ => ?_
    rw [map_mul, ← limitSymbol_conj h k a b, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast]
    push_cast
    ring
  rw [e]
  have hr' := limitCells_real (φ := φ) (lam := lam) h (-x) a b
  rw [hr', ← Complex.conj_ofReal, ← hr', map_mul, map_inv₀, map_mul, map_ofNat,
    Complex.conj_ofReal]

/-- The complexified `N` and `Nᵀ` are continuous in the regime. -/
theorem continuous_nMat_map (hr : ExampleRegime φ lam) :
    Continuous fun k => (nMat φ lam k).map Complex.ofReal :=
  (continuous_nMat hr).matrix_map Complex.continuous_ofReal

/-- The complexified `Nᵀ` is continuous in the regime. -/
theorem continuous_nMat_transpose_map (hr : ExampleRegime φ lam) :
    Continuous fun k => ((nMat φ lam k)ᵀ).map Complex.ofReal :=
  (continuous_nMat hr).matrix_transpose.matrix_map Complex.continuous_ofReal

/-- `C` is continuous in the regime. -/
theorem continuous_limitSymbol (hr : ExampleRegime φ lam) {γc : ℤ → Matrix Cell Cell ℝ}
    (h : CellData γc) : Continuous (limitSymbol φ lam γc) := by
  have hg := continuous_gammaHat h.summable
  exact (hg.add (((continuous_nMat_transpose_map hr).matrix_mul
    hg).matrix_mul (continuous_nMat_map hr))).const_smul (1 / 2 : ℂ)

/-- `cos y = (e^{iy} + e^{−iy})/2` in the form used by the oscillatory integrals. -/
private theorem ofReal_cos_eq (t : ℕ) (a : ℝ) :
    (Real.cos (2 * t * a) : ℂ) = (Complex.exp (((1 * (2 * t) * a : ℝ) : ℂ) * Complex.I) +
      Complex.exp ((((-1) * (2 * t) * a : ℝ) : ℂ) * Complex.I)) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  congr 2 <;> congr 1 <;> push_cast <;> ring

/-- `sin y = (e^{−iy} − e^{iy}) i / 2` in the same form. -/
private theorem ofReal_sin_eq (t : ℕ) (a : ℝ) :
    (Real.sin (2 * t * a) : ℂ) = (Complex.exp ((((-1) * (2 * t) * a : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((1 * (2 * t) * a : ℝ) : ℂ) * Complex.I)) * Complex.I / 2 := by
  rw [Complex.ofReal_sin, Complex.sin]
  congr 3 <;> congr 1 <;> push_cast <;> ring

/-- Milestone Q4b, Theorem 7 (thesis Proposition 4.7): in the regime, the cells of the evolved
covariance converge entrywise to the limit cells. (notes: `thm:cv-converge`) -/
theorem tendsto_iterate_evolveCells (hr : ExampleRegime φ lam) {γc : ℤ → Matrix Cell Cell ℝ}
    (h : CellData γc) (x : ℤ) (a b : Cell) :
    Tendsto (fun t : ℕ => (evolveCells (rotationSymbol φ lam))^[t] γc x a b) atTop
      (𝓝 (limitCells φ lam γc x a b)) := by
  set e : ℝ → ℂ := fun k => Complex.exp ((k : ℂ) * x * Complex.I)
  set N := fun k => (nMat φ lam k).map Complex.ofReal
  set NT := fun k => ((nMat φ lam k)ᵀ).map Complex.ofReal
  set g : ℝ → Matrix Cell Cell ℂ := gammaHat γc
  set g0 : ℝ → ℂ := fun k => e k * limitSymbol φ lam γc k a b
  set g1 : ℝ → ℂ := fun k => e k * ((1 / 2 : ℂ) • (g k - NT k * g k * N k)) a b
  set g2 : ℝ → ℂ := fun k => e k * (-(1 / 2 : ℂ) • (NT k * g k + g k * N k)) a b
  set E : ℝ → ℕ → ℝ → ℂ := fun σ t k =>
    Complex.exp (((σ * (2 * t) * alpha φ lam k : ℝ) : ℂ) * Complex.I)
  have he : Continuous e := by fun_prop
  have hg : Continuous g := continuous_gammaHat h.summable
  have hN := continuous_nMat_map hr
  have hNT := continuous_nMat_transpose_map hr
  have hg0 : Continuous g0 := he.mul ((continuous_limitSymbol hr h).matrix_elem a b)
  have hg1 : Continuous g1 := he.mul (((hg.sub ((hNT.matrix_mul hg).matrix_mul
    hN)).const_smul (1 / 2 : ℂ)).matrix_elem a b)
  have hg2 : Continuous g2 := he.mul ((((hNT.matrix_mul hg).add
    (hg.matrix_mul hN)).const_smul (-(1 / 2 : ℂ))).matrix_elem a b)
  have hE : ∀ σ t, Continuous (E σ t) := fun σ t => by
    have := continuous_alpha φ lam
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul this)).mul continuous_const)
  have hint : ∀ f : ℝ → ℂ, Continuous f → IntervalIntegrable f MeasureTheory.volume
      (-Real.pi) Real.pi := fun f hf => hf.intervalIntegrable _ _
  have hpt : ∀ t : ℕ, ∀ k : ℝ,
      e k * gammaHat ((evolveCells (rotationSymbol φ lam))^[t] γc) k a b =
      g0 k + (1 / 2 : ℂ) * (g1 k * E 1 t k) + (1 / 2 : ℂ) * (g1 k * E (-1) t k) +
        (Complex.I / 2) * (g2 k * E (-1) t k) - (Complex.I / 2) * (g2 k * E 1 t k) := by
    intro t k
    rw [gammaHat_iterate_example h, pow_transpose_mul_mul_pow hr]
    simp only [g0, g1, g2, E, g, N, NT, limitSymbol, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, ofReal_cos_eq, ofReal_sin_eq]
    ring
  have hlim : Tendsto (fun t : ℕ => ∫ k in (-Real.pi)..Real.pi,
      e k * gammaHat ((evolveCells (rotationSymbol φ lam))^[t] γc) k a b) atTop
      (𝓝 (∫ k in (-Real.pi)..Real.pi, g0 k)) := by
    have hosc : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) → ∀ f : ℝ → ℂ, Continuous f →
        Tendsto (fun t : ℕ => ∫ k in (-Real.pi)..Real.pi, f k * E σ t k) atTop (𝓝 0) :=
      fun σ hσ f hf => tendsto_integral_mul_exp_alpha hr hf σ hσ
    have e2 : ∀ t : ℕ, ∫ k in (-Real.pi)..Real.pi,
        e k * gammaHat ((evolveCells (rotationSymbol φ lam))^[t] γc) k a b =
        (∫ k in (-Real.pi)..Real.pi, g0 k) +
          (1 / 2 : ℂ) * (∫ k in (-Real.pi)..Real.pi, g1 k * E 1 t k) +
          (1 / 2 : ℂ) * (∫ k in (-Real.pi)..Real.pi, g1 k * E (-1) t k) +
          (Complex.I / 2) * (∫ k in (-Real.pi)..Real.pi, g2 k * E (-1) t k) -
          (Complex.I / 2) * (∫ k in (-Real.pi)..Real.pi, g2 k * E 1 t k) := by
      intro t
      simp_rw [hpt t]
      have i0 : IntervalIntegrable g0 MeasureTheory.volume (-Real.pi) Real.pi := hint _ hg0
      have i1 : IntervalIntegrable (fun k => (1 / 2 : ℂ) * (g1 k * E 1 t k))
          MeasureTheory.volume (-Real.pi) Real.pi :=
        (hint _ (hg1.mul (hE 1 t))).const_mul (1 / 2 : ℂ)
      have i2 : IntervalIntegrable (fun k => (1 / 2 : ℂ) * (g1 k * E (-1) t k))
          MeasureTheory.volume (-Real.pi) Real.pi :=
        (hint _ (hg1.mul (hE (-1) t))).const_mul (1 / 2 : ℂ)
      have i3 : IntervalIntegrable (fun k => (Complex.I / 2) * (g2 k * E (-1) t k))
          MeasureTheory.volume (-Real.pi) Real.pi :=
        (hint _ (hg2.mul (hE (-1) t))).const_mul (Complex.I / 2)
      have i4 : IntervalIntegrable (fun k => (Complex.I / 2) * (g2 k * E 1 t k))
          MeasureTheory.volume (-Real.pi) Real.pi :=
        (hint _ (hg2.mul (hE 1 t))).const_mul (Complex.I / 2)
      rw [intervalIntegral.integral_sub (((i0.add i1).add i2).add i3) i4,
        intervalIntegral.integral_add ((i0.add i1).add i2) i3,
        intervalIntegral.integral_add (i0.add i1) i2, intervalIntegral.integral_add i0 i1,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    simp_rw [e2]
    have := (((tendsto_const_nhds (x := ∫ k in (-Real.pi)..Real.pi, g0 k)).add
      ((hosc 1 (Or.inl rfl) g1 hg1).const_mul (1 / 2 : ℂ))).add
      ((hosc (-1) (Or.inr rfl) g1 hg1).const_mul (1 / 2 : ℂ))).add
      ((hosc (-1) (Or.inr rfl) g2 hg2).const_mul (Complex.I / 2)) |>.sub
      ((hosc 1 (Or.inl rfl) g2 hg2).const_mul (Complex.I / 2))
    simpa using this
  have hC : ∀ t : ℕ, ((evolveCells (rotationSymbol φ lam))^[t] γc x a b : ℂ) =
      ((2 * Real.pi)⁻¹ : ℂ) * ∫ k in (-Real.pi)..Real.pi,
        e k * gammaHat ((evolveCells (rotationSymbol φ lam))^[t] γc) k a b := fun t =>
    (integral_gammaHat (cellData_iterate _ h t) x a b).symm
  have hcx : Tendsto (fun t : ℕ => ((evolveCells (rotationSymbol φ lam))^[t] γc x a b : ℂ))
      atTop (𝓝 (limitCells φ lam γc x a b : ℂ)) := by
    rw [← limitCells_real h]
    simp_rw [hC]
    exact hlim.const_mul _
  have := (Complex.continuous_re.tendsto _).comp hcx
  simpa [Function.comp_def] using this

/-! ### The limit is stationary -/

/-- `det N(k) = 1` in the regime. -/
theorem det2_nMat (hr : ExampleRegime φ lam) (k : ℝ) : det2 (nMat φ lam k) = 1 := by
  have hs := (sin_alpha_pos hr k).ne'
  have htr := trace_eq_two_cos_alpha hr k
  rw [trace_cell] at htr
  have hd := det2_exampleSymbol φ lam k
  have hcs := Real.sin_sq_add_cos_sq (alpha φ lam k)
  rw [nMat, det2_smul]
  simp only [det2, Matrix.sub_apply, Matrix.smul_apply, one_qq, one_pp, one_qp, one_pq,
    smul_eq_mul] at hd ⊢
  field_simp
  linear_combination hd - Real.cos (alpha φ lam k) * htr - hcs

/-- `(Nᵀ)² = −1` in the regime, for the complexified `Nᵀ`. -/
theorem nMat_transpose_map_mul_self (hr : ExampleRegime φ lam) (k : ℝ) :
    ((nMat φ lam k)ᵀ).map Complex.ofReal * ((nMat φ lam k)ᵀ).map Complex.ofReal = -1 := by
  have := congrArg Matrix.transpose (nMat_map_mul_self hr k)
  rw [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.transpose_one] at this
  simpa [Matrix.transpose_map] using this

/-- Milestone Q4b, Proposition 9(a): the limit symbol is invariant, `Γ̂ᵀ C Γ̂ = C`.
(notes: `prop:cv-stationary`) -/
theorem limitSymbol_invariant (hr : ExampleRegime φ lam) (γc : ℤ → Matrix Cell Cell ℝ) (k : ℝ) :
    ((exampleSymbol φ lam k)ᵀ).map Complex.ofReal * limitSymbol φ lam γc k *
        (exampleSymbol φ lam k).map Complex.ofReal = limitSymbol φ lam γc k := by
  set c : ℂ := (Real.cos (alpha φ lam k) : ℂ)
  set s : ℂ := (Real.sin (alpha φ lam k) : ℂ)
  set N := (nMat φ lam k).map Complex.ofReal
  set NT := ((nMat φ lam k)ᵀ).map Complex.ofReal
  set A := gammaHat γc k
  have hcs : s ^ 2 + c ^ 2 = 1 := by
    simp only [s, c]; exact_mod_cast Real.sin_sq_add_cos_sq (alpha φ lam k)
  have hL : (exampleSymbol φ lam k).map Complex.ofReal = c • 1 - s • N :=
    exampleSymbol_map_eq_nMat hr k
  have hLT : ((exampleSymbol φ lam k)ᵀ).map Complex.ofReal = c • 1 - s • NT := by
    rw [Matrix.transpose_map, hL, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.transpose_one, ← Matrix.transpose_map]
  have h1 := sandwich_add_sandwich_of_sq_eq_neg_one A N NT (nMat_map_mul_self hr k)
    (nMat_transpose_map_mul_self hr k)
  have h2 := mul_add_add_mul_eq_zero_of_sq_eq_neg_one A N NT (nMat_map_mul_self hr k)
    (nMat_transpose_map_mul_self hr k)
  have hC : limitSymbol φ lam γc k = (1 / 2 : ℂ) • (A + NT * A * N) := rfl
  rw [hC, hLT, hL]
  have e : (c • (1 : Matrix Cell Cell ℂ) - s • NT) * ((1 / 2 : ℂ) • (A + NT * A * N)) *
      (c • 1 - s • N) = (1 / 2 : ℂ) • ((c * c) • (A + NT * A * N) -
        (c * s) • (NT * (A + NT * A * N) + (A + NT * A * N) * N) +
        (s * s) • (NT * (A + NT * A * N) * N)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.add_mul, Matrix.mul_add, smul_add, smul_sub, smul_smul,
      Matrix.mul_assoc]
    module
  rw [e, h1, h2]
  match_scalars <;> linear_combination (1 / 2 : ℂ) * hcs

/-- Milestone Q4b, Proposition 9(b): the limit symbol satisfies the Fourier state condition at
every wave number where `γ̂` does. (notes: `prop:cv-stationary`) -/
theorem limitSymbol_add_posSemidef (hr : ExampleRegime φ lam) (γc : ℤ → Matrix Cell Cell ℝ)
    (k : ℝ) (hk : (gammaHat γc k +
      Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef) :
    (limitSymbol φ lam γc k +
      Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef := by
  rw [map_symplecticForm_one] at hk ⊢
  set N := (nMat φ lam k).map Complex.ofReal
  set NT := ((nMat φ lam k)ᵀ).map Complex.ofReal
  set P := gammaHat γc k + Complex.I • (omega : Matrix Cell Cell ℂ)
  have hNH : Nᴴ = NT := by
    ext i j; simp [N, NT, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hΩ : NT * omega * N = omega := by
    have := transpose_mul_omega_mul_self (R := ℂ) N
    rw [show Nᵀ = NT by simp [N, NT, Matrix.transpose_map]] at this
    rw [this]
    have hd : det2 N = 1 := by
      have := det2_nMat hr k
      simp only [det2, N, Matrix.map_apply] at this ⊢
      exact_mod_cast this
    rw [hd, one_smul]
  have e : limitSymbol φ lam γc k + Complex.I • (omega : Matrix Cell Cell ℂ) =
      ((1 / 2 : ℝ) : ℂ) • P + ((1 / 2 : ℝ) : ℂ) • (Nᴴ * P * N) := by
    rw [hNH]
    simp only [limitSymbol, P, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, hΩ, N, NT]
    push_cast
    module
  rw [e]
  have h12 : (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ) := by exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact (hk.smul h12).add ((hk.conjTranspose_mul_mul_same N).smul h12)

/-- Milestone Q4b, Proposition 9(c): for reflection-symmetric cells with the Fourier state
condition, the limit symbol is `η ε̂(k)` with `η ≥ 1`, the form of thesis Theorem 4.8.
(notes: `prop:cv-stationary`) -/
theorem limitSymbol_eq_smul_epsHat (hr : ExampleRegime φ lam) {γc : ℤ → Matrix Cell Cell ℝ}
    (h : CellData γc) (hrefl : ∀ x, γc (-x) = γc x)
    (k : ℝ) (hsc : (gammaHat γc k +
      Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef) :
    ∃ g : ℝ, 1 ≤ g ∧ limitSymbol φ lam γc k = (g • epsHat φ lam k).map Complex.ofReal := by
  obtain ⟨hre, hsym⟩ := gammaHat_real h hrefl k
  set S := (gammaHat γc k).map Complex.re
  set Nr := nMat φ lam k
  set Cr : Matrix Cell Cell ℝ := (1 / 2 : ℝ) • (S + Nrᵀ * S * Nr)
  have hCr : limitSymbol φ lam γc k = Cr.map Complex.ofReal := by
    rw [limitSymbol, hre]
    ext i j
    simp only [Cr, Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.transpose_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_sum]
    push_cast
    ring
  have hCsym : Crᵀ = Cr := by
    simp only [Cr, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, hsym, Matrix.mul_assoc]
  have hCinv : (exampleSymbol φ lam k)ᵀ * Cr * exampleSymbol φ lam k = Cr := by
    apply map_ofReal_injective
    have := limitSymbol_invariant hr γc k
    rw [hCr] at this
    rw [map_ofReal_mul, map_ofReal_mul]
    exact this
  refine ⟨epsCoeff φ lam k Cr, ?_, ?_⟩
  · have hpsd := limitSymbol_add_posSemidef hr γc k hsc
    rw [hCr, eq_epsCoeff_smul_of_invariant hr k hCsym hCinv] at hpsd
    exact (smul_epsHat_add_posSemidef_iff hr k _).1 hpsd
  · rw [hCr, ← eq_epsCoeff_smul_of_invariant hr k hCsym hCinv]

end Limit

/-! ### Without the dispersive term the cells need not converge -/

section NoDispersion

/-- The product cells `diag(2, 1/2)` at the origin, the witness of `not_tendsto_lam_zero`.
(notes: `prop:cv-nocoupling`) -/
noncomputable def productCells : ℤ → Matrix Cell Cell ℝ := fun x =>
  if x = 0 then Matrix.diagonal fun i => if i = qIdx then (2 : ℝ) else 1 / 2 else 0

/-- The product cells are admissible. -/
theorem cellData_productCells : CellData productCells where
  summable i j := summable_of_ne_finset_zero (s := {0}) fun x hx => by
    rw [Finset.mem_singleton] at hx
    simp [productCells, hx]
  symm x := by
    by_cases hx : x = 0
    · subst hx; simp [productCells]
    · have hx' : -x ≠ 0 := neg_ne_zero.2 hx
      simp [productCells, hx, hx']

/-- The symbol of the product cells is the constant `diag(2, 1/2)`. -/
theorem gammaHat_productCells (k : ℝ) :
    gammaHat productCells k =
      (Matrix.diagonal fun i => if i = qIdx then (2 : ℝ) else 1 / 2).map Complex.ofReal := by
  rw [gammaHat, tsum_eq_single 0 fun x hx => by simp [productCells, hx]]
  simp [productCells]

/-- At `λ = 0` the symbol does not depend on the wave number. -/
theorem exampleSymbol_pi_div_two_zero (k : ℝ) :
    exampleSymbol (Real.pi / 2) 0 k = exampleSymbol (Real.pi / 2) 0 0 := by
  simp [exampleSymbol]

/-- At `φ = π/2`, `λ = 0` the symbol squares to `−1`. -/
theorem exampleSymbol_pi_div_two_sq :
    exampleSymbol (Real.pi / 2) 0 0 * exampleSymbol (Real.pi / 2) 0 0 = -1 := by
  apply cell_ext <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- The position-position entry of the evolved product cells at the origin. -/
theorem productCells_iterate_zero (t : ℕ) :
    (evolveCells (rotationSymbol (Real.pi / 2) 0))^[t] productCells 0 qIdx qIdx =
      ((exampleSymbol (Real.pi / 2) 0 0 ^ t)ᵀ *
        Matrix.diagonal (fun i => if i = qIdx then (2 : ℝ) else 1 / 2) *
          exampleSymbol (Real.pi / 2) 0 0 ^ t) qIdx qIdx := by
  apply Complex.ofReal_injective
  rw [← integral_gammaHat (cellData_iterate _ cellData_productCells t)]
  have hk : ∀ k : ℝ, Complex.exp ((k : ℂ) * ((0 : ℤ) : ℂ) * Complex.I) *
      gammaHat ((evolveCells (rotationSymbol (Real.pi / 2) 0))^[t] productCells) k qIdx qIdx =
      (((exampleSymbol (Real.pi / 2) 0 0 ^ t)ᵀ *
        Matrix.diagonal (fun i => if i = qIdx then (2 : ℝ) else 1 / 2) *
          exampleSymbol (Real.pi / 2) 0 0 ^ t) qIdx qIdx : ℂ) := by
    intro k
    rw [gammaHat_iterate_example cellData_productCells, gammaHat_productCells,
      exampleSymbol_pi_div_two_zero, ← map_ofReal_mul, ← map_ofReal_mul, Matrix.map_apply]
    simp
  simp_rw [hk]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- The entry has period two in time. -/
theorem productCells_iterate_add_two (t : ℕ) :
    (evolveCells (rotationSymbol (Real.pi / 2) 0))^[t + 2] productCells 0 qIdx qIdx =
      (evolveCells (rotationSymbol (Real.pi / 2) 0))^[t] productCells 0 qIdx qIdx := by
  rw [productCells_iterate_zero, productCells_iterate_zero, pow_add, sq,
    exampleSymbol_pi_div_two_sq]
  simp [Matrix.transpose_neg]

/-- Milestone Q4b, Proposition 10: at `φ = π/2`, `λ = 0` the position-position entry of the evolved
product cells at the origin is `2` at even times. (notes: `prop:cv-nocoupling`) -/
theorem productCells_iterate_even (s : ℕ) :
    (evolveCells (rotationSymbol (Real.pi / 2) 0))^[2 * s] productCells 0 qIdx qIdx = 2 := by
  induction s with
  | zero => rw [productCells_iterate_zero]; simp
  | succ s ih => rw [show 2 * (s + 1) = 2 * s + 2 by ring, productCells_iterate_add_two, ih]

/-- Milestone Q4b, Proposition 10: the same entry is `1/2` at odd times.
(notes: `prop:cv-nocoupling`) -/
theorem productCells_iterate_odd (s : ℕ) :
    (evolveCells (rotationSymbol (Real.pi / 2) 0))^[2 * s + 1] productCells 0 qIdx qIdx =
      1 / 2 := by
  induction s with
  | zero =>
    rw [productCells_iterate_zero]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Real.cos_pi_div_two, Real.sin_pi_div_two]
  | succ s ih =>
    rw [show 2 * (s + 1) + 1 = (2 * s + 1) + 2 by ring, productCells_iterate_add_two, ih]

/-- Milestone Q4b, Proposition 10: at `φ = π/2`, `λ = 0` the entry does not converge.
(notes: `prop:cv-nocoupling`) -/
theorem not_tendsto_productCells : ¬ ∃ c : ℝ,
    Tendsto (fun t : ℕ =>
      (evolveCells (rotationSymbol (Real.pi / 2) 0))^[t] productCells 0 qIdx qIdx) atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  have h2 : Tendsto (fun s : ℕ => 2 * s) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have h2' : Tendsto (fun s : ℕ => 2 * s + 1) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have he : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 c) := by
    simpa [Function.comp_def, productCells_iterate_even] using hc.comp h2
  have ho : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 c) := by
    simpa [Function.comp_def, productCells_iterate_odd] using hc.comp h2'
  have e1 := tendsto_nhds_unique tendsto_const_nhds he
  have e2 := tendsto_nhds_unique tendsto_const_nhds ho
  linarith

/-- Milestone Q4b, Proposition 10: at `λ = 0` the rule rotates every mode, and the evolved
product cells oscillate at `φ = π/2` without converging. (notes: `prop:cv-nocoupling`) -/
theorem not_tendsto_lam_zero :
    ∃ (φ : ℝ) (γc : ℤ → Matrix Cell Cell ℝ), CellData γc ∧ ¬ ∃ c : ℝ,
      Tendsto (fun t : ℕ => (evolveCells (rotationSymbol φ 0))^[t] γc 0 qIdx qIdx) atTop
        (𝓝 c) :=
  ⟨Real.pi / 2, productCells, cellData_productCells, not_tendsto_productCells⟩

end NoDispersion

/-! ### Convergence of the states -/

section LimitState

open BosonicLean.Weyl

/-- Entrywise convergence of cells gives convergence of the covariance forms. -/
theorem tendsto_cellForm {γ : ℕ → ℤ → Matrix Cell Cell ℝ} {γ' : ℤ → Matrix Cell Cell ℝ}
    (h : ∀ x a b, Tendsto (fun t => γ t x a b) atTop (𝓝 (γ' x a b))) (u w : PhaseVec ℤ 1) :
    Tendsto (fun t => cellForm (γ t) u w) atTop (𝓝 (cellForm γ' u w)) := by
  simp only [cellForm, LinearMap.mk₂_apply, cellPair, Finsupp.sum]
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ =>
      (tendsto_const_nhds.mul (h _ _ _)).mul tendsto_const_nhds

/-- Milestone Q4b, Theorem 12(a): the characteristic functions of the evolved Gaussian state
converge to the Gaussian characteristic function of the limit cells. (notes: `thm:cv-weak`) -/
theorem tendsto_charFun_evolve (hr : ExampleRegime φ lam) {γc : ℤ → Matrix Cell Cell ℝ}
    (h : CellData γc) (ω : GaussianState (sigma ℤ 1)) (hcov : ω.cov = cellForm γc)
    (hdisp : ω.disp = 0) (u : PhaseVec ℤ 1) :
    Tendsto (fun t : ℕ =>
        (ω.evolve (isSymplectic_pow (isSymplectic_rotationSymbol φ lam) t)).charFun u)
      atTop (𝓝 (Complex.exp (-(cellForm (limitCells φ lam γc) u u : ℂ) / 4))) := by
  have e : ∀ t : ℕ,
      (ω.evolve (isSymplectic_pow (isSymplectic_rotationSymbol φ lam) t)).charFun u =
      Complex.exp (-(cellForm ((evolveCells (rotationSymbol φ lam))^[t] γc) u u : ℂ) / 4) := by
    intro t
    rw [(ω.evolve _).charFun_eq, GaussianState.evolve_cov, GaussianState.evolve_disp, hcov, hdisp,
      cellForm_evolve, evolveCells_iterate]
    simp only [LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, zero_sub, neg_div]
  have hc := tendsto_cellForm (fun x a b => tendsto_iterate_evolveCells hr h x a b) u u
  exact (((Complex.continuous_ofReal.tendsto _).comp hc).neg.div_const 4).cexp.congr
    fun t => (e t).symm

/-- Milestone Q4b, Theorem 12(b) (thesis Theorem 4.9): the evolved states converge on every
observable to a Gaussian state with the limit covariance and zero displacement.
(notes: `thm:cv-weak`) -/
theorem exists_limit_state (hr : ExampleRegime φ lam) {γc : ℤ → Matrix Cell Cell ℝ}
    (h : CellData γc) (ω : GaussianState (sigma ℤ 1)) (hcov : ω.cov = cellForm γc)
    (hdisp : ω.disp = 0) :
    ∃ ωinf : GaussianState (sigma ℤ 1), ωinf.cov = cellForm (limitCells φ lam γc) ∧ ωinf.disp = 0 ∧
      ∀ a, Tendsto (fun t : ℕ =>
        (ω.evolve (isSymplectic_pow (isSymplectic_rotationSymbol φ lam) t)).toCLM a) atTop
        (𝓝 (ωinf.toCLM a)) := by
  let F : ℕ → CCR (sigma ℤ 1) →L[ℂ] ℂ := fun t =>
    (ω.evolve (isSymplectic_pow (isSymplectic_rotationSymbol φ lam) t)).toCLM
  have hσ := sigma_isAlt ℤ 1
  have hF : ∀ t a, ‖F t a‖ ≤ ‖a‖ := fun t a => State.norm_apply_le _ a
  -- convergence on the linear span of the Weyl operators
  have hspan : ∀ y ∈ Submodule.span ℂ (Set.range (CCR.weylSystem (sigma ℤ 1) hσ).W),
      ∃ l, Tendsto (fun t => F t y) atTop (𝓝 l) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, rfl⟩ := hy
      exact ⟨_, tendsto_charFun_evolve hr h ω hcov hdisp u⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨l, hl⟩ := hx
      obtain ⟨l', hl'⟩ := hy
      exact ⟨l + l', by simpa using hl.add hl'⟩
    | smul c x _ hx =>
      obtain ⟨l, hl⟩ := hx
      exact ⟨c * l, by simpa using hl.const_mul c⟩
  -- the sequence is Cauchy at every observable
  have hcauchy : ∀ a, CauchySeq fun t => F t a := by
    intro a
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨y, hy, hay⟩ := Metric.mem_closure_iff.1
      (weyl_mem_closure_span (CCR.weylSystem (sigma ℤ 1) hσ) hσ a) (ε / 4) (by positivity)
    obtain ⟨l, hl⟩ := hspan y hy
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hl.cauchySeq (ε / 4) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hd : ∀ t, dist (F t a) (F t y) < ε / 4 := fun t => by
      rw [dist_eq_norm, ← map_sub]
      exact (hF t _).trans_lt (by rwa [← dist_eq_norm])
    calc dist (F n a) (F N a) ≤ dist (F n a) (F n y) + dist (F n y) (F N y) +
          dist (F N y) (F N a) := dist_triangle4 _ _ _ _
      _ < ε / 4 + ε / 4 + ε / 4 := by
          gcongr
          · exact hd n
          · exact hN n hn
          · rw [dist_comm]; exact hd N
      _ < ε := by linarith
  choose L hL using fun a => cauchySeq_tendsto_of_complete (hcauchy a)
  -- the limit functional
  let Llin : CCR (sigma ℤ 1) →ₗ[ℂ] ℂ :=
    { toFun := L
      map_add' := fun a b => tendsto_nhds_unique (hL (a + b)) (by
        simpa using (hL a).add (hL b))
      map_smul' := fun c a => tendsto_nhds_unique (hL (c • a)) (by
        simpa using (hL a).const_mul c) }
  have hLb : ∀ a, ‖Llin a‖ ≤ 1 * ‖a‖ := fun a => by
    rw [one_mul]
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp (hL a)) fun t => hF t a
  let S : State (sigma ℤ 1) :=
    { toCLM := Llin.mkContinuous 1 hLb
      map_one := tendsto_nhds_unique (hL 1) (by
        simp only [F, (State.map_one _)]
        exact tendsto_const_nhds)
      nonneg := fun a => ge_of_tendsto' (hL (star a * a)) fun t => State.nonneg _ a }
  have hS : ∀ a, S.toCLM a = L a := fun _ => rfl
  refine ⟨{ toState := S
            cov := cellForm (limitCells φ lam γc)
            isSymm := cellForm_isSymm (limitCells_symm h)
            disp := 0
            charFun_eq := fun u => ?_ }, rfl, rfl, fun a => ?_⟩
  · change L (wCCR (sigma ℤ 1) u) = _
    rw [tendsto_nhds_unique (hL _) (tendsto_charFun_evolve hr h ω hcov hdisp u)]
    simp only [LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, zero_sub, neg_div]
  · exact hL a

end LimitState

end QCALean.Bosonic
