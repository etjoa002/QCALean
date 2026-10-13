/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Riemann–Lebesgue lemma along a monotone phase

Milestone Q4b. If `θ` is injective and differentiable with nonvanishing derivative on a measurable
set `s ⊆ ℝ`, then `∫_s h(k) e^{i r θ(k)} dk → 0` as `r → ∞`, for every `h : ℝ → ℂ`. The change of
variables `u = θ(k)` turns the integral into the Fourier transform of `u ↦ h(θ⁻¹ u)/|θ'(θ⁻¹ u)|`
on `θ(s)`, to which Mathlib's Riemann–Lebesgue lemma applies; no integrability hypothesis is
needed, since a non-integrable function has integral zero on both sides of the change of
variables. The interval forms for strictly monotone phases follow.

## Main results

* `QCALean.Core.tendsto_setIntegral_mul_exp_of_injOn`
* `QCALean.Core.tendsto_integral_mul_exp_of_strictMonoOn`,
  `QCALean.Core.tendsto_integral_mul_exp_of_strictAntiOn`
-/

open MeasureTheory Filter Topology Set

namespace QCALean.Core

/-- Milestone Q4b, Lemma 1 (step): the frequencies `−r/(2π)` leave every compact set as
`r → ∞`. -/
theorem tendsto_neg_div_two_pi_cocompact :
    Tendsto (fun r : ℝ => -r / (2 * Real.pi)) atTop (cocompact ℝ) := by
  rw [cocompact_eq_atBot_atTop]
  exact (tendsto_neg_atTop_atBot.atBot_div_const Real.two_pi_pos).mono_right le_sup_left

/-- Milestone Q4b, Lemma 1 (general form): the Riemann–Lebesgue lemma along a phase that is
injective and differentiable with nonvanishing derivative on a measurable set.
(notes: `lem:cv-rl`) -/
theorem tendsto_setIntegral_mul_exp_of_injOn {s : Set ℝ} (hs : MeasurableSet s)
    {θ θ' : ℝ → ℝ} (h : ℝ → ℂ) (hd : ∀ x ∈ s, HasDerivWithinAt θ (θ' x) s x)
    (hinj : InjOn θ s) (hd0 : ∀ x ∈ s, θ' x ≠ 0) :
    Tendsto (fun r : ℝ => ∫ k in s, h k * Complex.exp (r * θ k * Complex.I)) atTop (𝓝 0) := by
  classical
  set κ := Function.invFunOn θ s
  set H : ℝ → ℂ := fun u => ((|θ' (κ u)| : ℝ) : ℂ)⁻¹ * h (κ u)
  have hcont : ContinuousOn θ s := fun x hx => (hd x hx).continuousWithinAt
  have hI : MeasurableSet (θ '' s) := hs.image_of_continuousOn_injOn hcont hinj
  have key : ∀ r : ℝ, ∫ k in s, h k * Complex.exp (r * θ k * Complex.I) =
      ∫ u, (Real.fourierChar (-(u * (-r / (2 * Real.pi)))) : ℂ) * (θ '' s).indicator H u := by
    intro r
    have hG := integral_image_eq_integral_abs_deriv_smul hs hd hinj
      (fun u => Complex.exp (r * u * Complex.I) * H u)
    have e1 : ∫ x in s, |θ' x| • (Complex.exp (r * θ x * Complex.I) * H (θ x)) =
        ∫ k in s, h k * Complex.exp (r * θ k * Complex.I) := by
      refine setIntegral_congr_fun hs fun x hx => ?_
      have hk : κ (θ x) = x := hinj.leftInvOn_invFunOn hx
      have hne : ((|θ' x| : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast abs_ne_zero.2 (hd0 x hx)
      simp only [H, hk, Complex.real_smul]
      field_simp
    rw [← e1, ← hG, ← integral_indicator hI]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ θ '' s
    · simp only [indicator_of_mem hu, Real.fourierChar_apply]
      congr 2
      push_cast
      field_simp
    · simp [indicator_of_notMem hu]
  have hlim := (Real.tendsto_integral_exp_smul_cocompact ((θ '' s).indicator H)).comp
    tendsto_neg_div_two_pi_cocompact
  refine hlim.congr fun r => ?_
  simp only [Function.comp_apply, Circle.smul_def, smul_eq_mul]
  exact (key r).symm

/-- Milestone Q4b, Lemma 1: the Riemann–Lebesgue lemma along a strictly increasing phase.
(notes: `lem:cv-rl`) -/
theorem tendsto_integral_mul_exp_of_strictMonoOn {a b : ℝ} (hab : a ≤ b) {θ θ' : ℝ → ℝ}
    (h : ℝ → ℂ) (hmono : StrictMonoOn θ (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt θ (θ' x) x) (hd0 : ∀ x ∈ Ioo a b, θ' x ≠ 0) :
    Tendsto (fun r : ℝ => ∫ k in a..b, h k * Complex.exp (r * θ k * Complex.I)) atTop (𝓝 0) := by
  refine (tendsto_setIntegral_mul_exp_of_injOn measurableSet_Ioo h
    (fun x hx => (hd x hx).hasDerivWithinAt) (hmono.injOn.mono Ioo_subset_Icc_self) hd0).congr
    fun r => ?_
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- Milestone Q4b, Lemma 1: the Riemann–Lebesgue lemma along a strictly decreasing phase.
(notes: `lem:cv-rl`) -/
theorem tendsto_integral_mul_exp_of_strictAntiOn {a b : ℝ} (hab : a ≤ b) {θ θ' : ℝ → ℝ}
    (h : ℝ → ℂ) (hanti : StrictAntiOn θ (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt θ (θ' x) x) (hd0 : ∀ x ∈ Ioo a b, θ' x ≠ 0) :
    Tendsto (fun r : ℝ => ∫ k in a..b, h k * Complex.exp (r * θ k * Complex.I)) atTop (𝓝 0) := by
  refine (tendsto_setIntegral_mul_exp_of_injOn measurableSet_Ioo h
    (fun x hx => (hd x hx).hasDerivWithinAt) (hanti.injOn.mono Ioo_subset_Icc_self) hd0).congr
    fun r => ?_
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

end QCALean.Core
