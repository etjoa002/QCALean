/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.Covariance
import QCALean.Core.FourierSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Fourier criterion for translation-invariant covariance forms

Milestone Q3, Section 5 and Example 31. For admissible cell data `(γ_x)` on `ℤ`, the covariance
form `γ(u,w) = Σ_{x,y} u(x)ᵀ γ_{x−y} w(y)` satisfies the state condition when its symbol
`γ̂(k) + iΩ` is positive semidefinite for every `k` (Parseval), and conversely for cells of
finite range (Fejér vectors).

## Main results

* `QCALean.Bosonic.fourier_of_stateCondition` (finite range)
-/

open LinearAQFT BosonicLean.Weyl QCALean.Core Matrix Gaussian
open scoped ComplexOrder ComplexConjugate

namespace QCALean.Bosonic

variable {n : ℕ}

/-- The coefficient `a_m = γ_m + i δ_{m0} Ω` of the thesis form (4.6). (notes: `lem:gs-parseval`) -/
noncomputable def cellCoeff (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (m : ℤ) : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℂ :=
  (γc m).map Complex.ofReal +
    if m = 0 then Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal else 0

/-- The matrix of `γ + iσ` on the site vectors of a finite region. -/
noncomputable def regionStateMatrix
    (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) (T : Finset ℤ) :
    Matrix (Gaussian.PhaseIndex (n * T.card)) (Gaussian.PhaseIndex (n * T.card)) ℂ :=
  Matrix.of fun a b => (cellForm γc (regionVec T a) (regionVec T b) : ℂ) +
    Complex.I * (sigma ℤ n (regionVec T a) (regionVec T b) : ℂ)

theorem sigma_siteVec (x y : ℤ) (i j : Gaussian.PhaseIndex n) :
    sigma ℤ n (siteVec x i) (siteVec y j) =
      if x = y then Gaussian.symplecticForm n i j else 0 :=
  liftForm_siteVec _ x y i j

/-- The quadratic form of `γ + iσ` on a region, `Σ_{x,y ∈ T} ν(x)* a_{x−y} ν(y)`. -/
theorem quad_regionStateMatrix
    (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) (T : Finset ℤ)
    (c : Gaussian.PhaseIndex (n * T.card) → ℂ) :
    star c ⬝ᵥ (regionStateMatrix γc T *ᵥ c) =
      ∑ x : T, ∑ y : T, ∑ i, ∑ j, conj (c (regionEquiv T (x, i))) *
        c (regionEquiv T (y, j)) * cellCoeff γc ((x : ℤ) - y) i j := by
  rw [star_dotProduct_mulVec_eq, ← (regionEquiv T).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset T))
    (t := (Finset.univ : Finset (Gaussian.PhaseIndex n)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (regionEquiv T).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [regionStateMatrix, Matrix.of_apply, regionVec, Equiv.symm_apply_apply,
    cellForm_siteVec, sigma_siteVec, cellCoeff, Matrix.add_apply, Matrix.map_apply,
    sub_eq_zero, Subtype.coe_inj]
  split_ifs <;> simp

theorem iOmega_isHermitian :
    (Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal).IsHermitian := by
  ext i j
  have := congrFun (congrFun (Gaussian.transpose_symplecticForm n) i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
  simp [Matrix.conjTranspose_apply, this]

/-- For cells of range `R`, `γ̂(k) + iΩ = Σ_{|m| ≤ R} e^{−ikm} a_m`. -/
theorem gammaHat_add_eq_sum
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (R : ℕ)
    (hR : ∀ m, (R : ℤ) < |m| → γc m = 0) (k : ℝ) :
    gammaHat γc k + Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal =
      ∑ m ∈ Finset.Icc (-(R : ℤ)) R,
        Complex.exp (-(k : ℂ) * m * Complex.I) • cellCoeff γc m := by
  have hout : ∀ m ∉ Finset.Icc (-(R : ℤ)) R, (R : ℤ) < |m| := fun m hm => by
    rw [Finset.mem_Icc, not_and_or] at hm; rw [lt_abs]; omega
  rw [gammaHat, tsum_eq_sum (s := Finset.Icc (-(R : ℤ)) R) fun m hm => by
    rw [hR m (hout m hm)]; simp]
  simp only [cellCoeff, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_Icc]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  simp

/-- Milestone Q3, Theorem 23(b): for cells of finite range, the state condition implies that
`γ̂(k) + iΩ` is positive semidefinite for every `k` (Fejér vectors); an instance of the Fejér
argument for matrix sequences, `QCALean.Core.posSemidef_of_fejer`. -/
theorem fourier_of_stateConditionPair
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (R : ℕ) (hR : ∀ m, (R : ℤ) < |m| → γc m = 0)
    (hs : IsStateConditionPair (cellForm γc) (sigma ℤ n)) (k : ℝ) :
    (gammaHat γc k + Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal).PosSemidef := by
  have herm := (gammaHat_isHermitian h k).add iOmega_isHermitian
  rw [gammaHat_add_eq_sum R hR] at herm ⊢
  refine posSemidef_of_fejer R (fun m hm => ?_) k herm fun N ν => ?_
  · have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
    simp [cellCoeff, hR m hm, hm0]
  · set T := Finset.Ico (0 : ℤ) N
    have hpsd := (posSemidef_region_iff T (cellForm_isSymm h.symm) (sigma_isAlt ℤ n)).2
      fun u _ w _ => hs u w
    set c : Gaussian.PhaseIndex (n * T.card) → ℂ := fun a =>
      ν ((regionEquiv T).symm a).1 ((regionEquiv T).symm a).2 with hc
    have hq := hpsd.dotProduct_mulVec_nonneg c
    change 0 ≤ star c ⬝ᵥ (regionStateMatrix γc T *ᵥ c) at hq
    rw [quad_regionStateMatrix] at hq
    simp only [c, Equiv.symm_apply_apply] at hq
    have hsum : (∑ x ∈ T, ∑ y ∈ T, ∑ i, ∑ j, conj (ν x i) * ν y j * cellCoeff γc (x - y) i j) =
        ∑ x : T, ∑ y : T, ∑ i, ∑ j,
          conj (ν x i) * ν y j * cellCoeff γc ((x : ℤ) - y) i j := by
      rw [← Finset.sum_coe_sort T]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_coe_sort T]
    rw [hsum]
    exact (Complex.nonneg_iff.1 hq).1

/-- Milestone Q3, Theorem 23(b), from the state condition `γ + iσ ≥ 0`. (notes: `thm:gs-fourier`) -/
theorem fourier_of_stateCondition
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (R : ℕ) (hR : ∀ m, (R : ℤ) < |m| → γc m = 0)
    (hs : IsStateConditionC (cellForm γc) (sigma ℤ n)) (k : ℝ) :
    (gammaHat γc k + Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal).PosSemidef :=
  fourier_of_stateConditionPair h R hR
    ((isStateConditionC_iff_pair (cellForm_isSymm h.symm) (sigma_isAlt ℤ n)).1 hs) k

theorem summable_cellCoeff
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (i j : Gaussian.PhaseIndex n) :
    Summable fun m => ‖cellCoeff γc m i j‖ := by
  have h2 : Summable fun m : ℤ =>
      ‖(if m = 0 then Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal else 0) i j‖ :=
    summable_of_ne_finset_zero (s := {0}) fun m hm => by
      rw [Finset.mem_singleton] at hm; simp [hm]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) ((h i j).add h2)
  simp only [cellCoeff, Matrix.add_apply, Matrix.map_apply]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- The entries of `γ̂(k) + iΩ` as Fourier series of the coefficients `a_m`. -/
theorem gammaHat_add_apply
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (k : ℝ) (i j : Gaussian.PhaseIndex n) :
    (gammaHat γc k + Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal) i j =
      ∑' m : ℤ, cellCoeff γc m i j * Complex.exp (-(k : ℂ) * m * Complex.I) := by
  have h1 := summable_phase_mul h k i j
  have h2 : Summable fun m : ℤ => (if m = 0 then Complex.I •
      (Gaussian.symplecticForm n).map Complex.ofReal else 0) i j *
        Complex.exp (-(k : ℂ) * m * Complex.I) :=
    summable_of_ne_finset_zero (s := {0}) fun m hm => by
      rw [Finset.mem_singleton] at hm; simp [hm]
  simp only [cellCoeff, Matrix.add_apply, add_mul]
  have h3 : ∑' m : ℤ, (if m = 0 then Complex.I •
      (Gaussian.symplecticForm n).map Complex.ofReal else 0) i j *
        Complex.exp (-(k : ℂ) * m * Complex.I) =
      Complex.I * (Gaussian.symplecticForm n i j : ℂ) := by
    rw [tsum_eq_single 0 fun m hm => by simp [hm]]
    simp
  rw [Summable.tsum_add (by simpa [mul_comm] using h1) h2, gammaHat_apply h, h3]
  simp [mul_comm]

/-- Milestone Q3, Lemma 22 (Parseval, thesis (4.16)): on a finite region,
`∫_{−π}^{π} μ̂(k)* (γ̂(k) + iΩ) μ̂(k) dk = 2π Σ_{x,y} μ(x)* a_{x−y} μ(y)`; an instance of Parseval
for matrix sequences, `QCALean.Core.parseval_matrix`. (notes: `lem:gs-parseval`) -/
theorem parseval_region
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (T : Finset ℤ)
    (ν : T × Gaussian.PhaseIndex n → ℂ) :
    ∫ k in (-Real.pi)..Real.pi,
      star (fun i => ∑ x : T, ν (x, i) * Complex.exp (-(k : ℂ) * (x : ℤ) * Complex.I)) ⬝ᵥ
        ((gammaHat γc k + Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal) *ᵥ
          fun i => ∑ x : T, ν (x, i) * Complex.exp (-(k : ℂ) * (x : ℤ) * Complex.I)) =
      2 * Real.pi * ∑ x : T, ∑ y : T, ∑ i, ∑ j,
        conj (ν (x, i)) * ν (y, j) * cellCoeff γc ((x : ℤ) - y) i j :=
  parseval_matrix (summable_cellCoeff h) (gammaHat_add_apply h) (fun x : T => (x : ℤ))
    fun x i => ν (x, i)

/-- The real part of the Hermitian form of `γ + iσ` on a family, with no symmetry of `γ`:
`Re Σ_{j,k} c̄_j c_k (γ + iσ)(u_j, u_k) = γ(a,a) + γ(b,b) − σ(a,b) + σ(b,a)`
for `a = Σ_k Re c_k u_k` and `b = Σ_k Im c_k u_k`. -/
theorem re_sum_conj_mul_stateMatrix {V : Type*} [AddCommGroup V] [Module ℝ V]
    (γ σ : LinearMap.BilinForm ℝ V) {ι : Type*} [Fintype ι] (u : ι → V) (c : ι → ℂ) :
    (∑ j, ∑ k, conj (c j) * c k * ((γ (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ))).re =
      γ (∑ k, (c k).re • u k) (∑ k, (c k).re • u k) +
        γ (∑ k, (c k).im • u k) (∑ k, (c k).im • u k) -
        σ (∑ k, (c k).re • u k) (∑ k, (c k).im • u k) +
        σ (∑ k, (c k).im • u k) (∑ k, (c k).re • u k) := by
  simp only [bilin_sum_sum, Complex.re_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Milestone Q6: positivity of the matrix of `γ + iσ` on the site vectors of a region gives
`2σ(u,w) ≤ γ(u,u) + γ(w,w)` for vectors supported in the region. Unlike `posSemidef_region_iff`,
no symmetry of `γ` is assumed: only the real part of the quadratic form is used. -/
theorem pair_le_of_posSemidef_region (O : Finset ℤ)
    {γ σ' : LinearMap.BilinForm ℝ (PhaseVec ℤ n)} (hσ : σ'.IsAlt)
    (h : (Matrix.of fun a b => (γ (regionVec O a) (regionVec O b) : ℂ) +
      Complex.I * (σ' (regionVec O a) (regionVec O b) : ℂ)).PosSemidef)
    {u w : PhaseVec ℤ n} (hu : u ∈ loc ℤ n (O : Set ℤ)) (hw : w ∈ loc ℤ n (O : Set ℤ)) :
    2 * σ' u w ≤ γ u u + γ w w := by
  have h2 := h.dotProduct_mulVec_nonneg
    (fun a => (regionCoords O u a : ℂ) + Complex.I * (regionCoords O w a : ℂ))
  rw [star_dotProduct_mulVec_eq] at h2
  simp only [Matrix.of_apply] at h2
  have hre := (Complex.nonneg_iff.1 h2).1
  rw [re_sum_conj_mul_stateMatrix] at hre
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, zero_mul, mul_zero, sub_zero,
    add_zero, one_mul, zero_add, sum_regionCoords O hu, sum_regionCoords O hw] at hre
  have hs := isAlt_swap hσ w u
  linarith

/-- Milestone Q6: for cells `g` and an alternating form `B` on the chain, positivity of the
matrices of `γ + iB` on the site vectors of every finite region gives the state condition in pair
form. The region step of the Fourier criteria of Q3 and Q5b; no symmetry of the cell form is
assumed. -/
theorem isStateConditionPair_of_region
    {g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    {B : LinearMap.BilinForm ℝ (PhaseVec ℤ n)} (hB : B.IsAlt)
    (h : ∀ T : Finset ℤ, (Matrix.of fun a b => (cellForm g (regionVec T a) (regionVec T b) : ℂ) +
      Complex.I * (B (regionVec T a) (regionVec T b) : ℂ)).PosSemidef) :
    IsStateConditionPair (cellForm g) B := by
  classical
  intro a b
  set T := Finset.univ.biUnion (fun i => (a i).coeff.support) ∪
    Finset.univ.biUnion (fun i => (b i).coeff.support)
  have hloc : ∀ u : PhaseVec ℤ n, (∀ i, (u i).coeff.support ⊆ T) →
      u ∈ loc ℤ n (T : Set ℤ) := by
    intro u hu z hz
    funext i
    simp only [LatticeSpace.valueAt_apply, Pi.zero_apply]
    by_contra hne
    exact hz (hu i (Finsupp.mem_support_iff.2 hne))
  have ha : ∀ i, (a i).coeff.support ⊆ T := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => (a i).coeff.support) (Finset.mem_univ i)).trans
      Finset.subset_union_left
  have hb : ∀ i, (b i).coeff.support ⊆ T := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => (b i).coeff.support) (Finset.mem_univ i)).trans
      Finset.subset_union_right
  exact pair_le_of_posSemidef_region T hB (h T) (hloc a ha) (hloc b hb)

/-- Milestone Q3, Theorem 23(a): if `γ̂(k) + iΩ ≥ 0` for every `k`, the covariance form of
admissible cells satisfies the state condition, in pair form. -/
theorem stateConditionPair_of_fourier
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (hk : ∀ k, (gammaHat γc k +
      Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal).PosSemidef) :
    IsStateConditionPair (cellForm γc) (sigma ℤ n) := by
  refine isStateConditionPair_of_region (sigma_isAlt ℤ n) fun T => ?_
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_stateMatrix (cellForm_isSymm h.symm) (sigma_isAlt ℤ n) _) fun c => ?_
  change 0 ≤ star c ⬝ᵥ (regionStateMatrix γc T *ᵥ c)
  rw [quad_regionStateMatrix]
  exact nonneg_of_integral_eq (fun k => (hk k).dotProduct_mulVec_nonneg _)
    (parseval_region h.summable T fun p => c (regionEquiv T p))

/-- Milestone Q3, Theorem 23(a): if `γ̂(k) + iΩ ≥ 0` for every `k`, then `(γ, σ)` satisfies the
state condition `γ + iσ ≥ 0`. (notes: `thm:gs-fourier`) -/
theorem stateCondition_of_fourier
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (hk : ∀ k, (gammaHat γc k +
      Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal).PosSemidef) :
    IsStateConditionC (cellForm γc) (sigma ℤ n) :=
  (isStateConditionC_iff_pair (cellForm_isSymm h.symm) (sigma_isAlt ℤ n)).2
    (stateConditionPair_of_fourier h hk)

/-- Milestone Q3, Theorem 23: for admissible cells of finite range, the state condition holds
exactly when `γ̂(k) + iΩ ≥ 0` for every `k`. (notes: `thm:gs-fourier`) -/
theorem stateCondition_iff_fourier
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (R : ℕ) (hR : ∀ m, (R : ℤ) < |m| → γc m = 0) :
    IsStateConditionC (cellForm γc) (sigma ℤ n) ↔
      ∀ k, (gammaHat γc k +
        Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal).PosSemidef :=
  ⟨fun hs k => fourier_of_stateCondition h R hR hs k, stateCondition_of_fourier h⟩

/-- Milestone Q4a, Proposition 4(a): Fourier inversion for cells. (notes: `prop:es-inversion`) -/
theorem integral_gammaHat
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (x : ℤ) (a b : Gaussian.PhaseIndex n) :
    ((2 * Real.pi)⁻¹ : ℂ) *
        ∫ k in (-Real.pi)..Real.pi, Complex.exp ((k : ℂ) * x * Complex.I) * gammaHat γc k a b =
      γc x a b := by
  simp_rw [gammaHat_apply' h.summable]
  have hs : Summable fun m => ‖(γc m a b : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h.summable a b
  rw [integral_fourier_series _ hs x]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

/-- Milestone Q4a, Proposition 4(b): admissible cell data are determined by their symbol.
(notes: `prop:es-inversion`) -/
theorem gammaHat_injective
    {γc γc' : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : CellData γc) (h' : CellData γc') (e : ∀ k, gammaHat γc k = gammaHat γc' k) :
    γc = γc' := by
  funext x
  ext a b
  apply Complex.ofReal_injective
  rw [← integral_gammaHat h, ← integral_gammaHat h']
  simp only [e]

/-! ### The leapfrog -/

/-- Milestone Q3, Example 18: the vacuum cells, `γ_0 = 1` and `γ_x = 0` otherwise.
(notes: `ex:gs-leapfrog`) -/
noncomputable def vacuumCells : ℤ → Matrix Cell Cell ℝ := onSiteKernel 1

theorem vacuumCells_summable (i j : Cell) : Summable fun x => |vacuumCells x i j| :=
  summable_of_ne_finset_zero (s := {0}) fun m hm => by
    rw [Finset.mem_singleton] at hm; simp [vacuumCells, onSiteKernel, hm]

theorem gammaHat_vacuumCells (k : ℝ) : gammaHat vacuumCells k = 1 := by
  rw [gammaHat, tsum_eq_single 0 fun m hm => by simp [vacuumCells, onSiteKernel, hm]]
  simp [vacuumCells, onSiteKernel]

theorem coeffMat_leapfrogSymbol_neg (m2 : ℝ) (m : ℤ) :
    coeffMat (-m) (leapfrogSymbol m2) = coeffMat m (leapfrogSymbol m2) := by
  simp only [leapfrogSymbol, nnSymbol, map_add, coeffMat_mono]
  by_cases h1 : m = 1
  · subst h1; simp
  · by_cases h2 : m = -1
    · subst h2; simp
    · by_cases h0 : m = 0
      · subst h0; simp
      · simp [show (-1 : ℤ) ≠ m by omega, show (0 : ℤ) ≠ m by omega, show (1 : ℤ) ≠ m by omega,
          show (-1 : ℤ) ≠ -m by omega, show (0 : ℤ) ≠ -m by omega,
          show (1 : ℤ) ≠ -m by omega]

/-- The Fourier symbol of the leapfrog, `F̂(k) = [[0, 1], [−1, c_k]]` with `c_k = 2 cos k − m²`. -/
theorem fourierSymbol_leapfrog (m2 k : ℝ) :
    fourierSymbol k (leapfrogSymbol m2) qIdx qIdx = 0 ∧
      fourierSymbol k (leapfrogSymbol m2) qIdx pIdx = 1 ∧
      fourierSymbol k (leapfrogSymbol m2) pIdx qIdx = -1 ∧
      fourierSymbol k (leapfrogSymbol m2) pIdx pIdx = 2 * Complex.cos k - m2 := by
  simp only [leapfrogSymbol, nnSymbol, fourierSymbol_add, fourierSymbol_mono, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, leapfrogShift, leapfrogCentre, Matrix.of_apply,
    smul_eq_mul, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero]
  refine ⟨by simp, by simp, by simp, ?_⟩
  rw [Complex.cos]
  push_cast
  ring_nf

theorem gammaHat_leapfrog_vacuum_eq (m2 k : ℝ) :
    gammaHat (evolveCells (leapfrogSymbol m2) vacuumCells) k =
      (fourierSymbol k (leapfrogSymbol m2))ᵀ * fourierSymbol k (leapfrogSymbol m2) := by
  rw [gammaHat_evolve_of_symm _ vacuumCells_summable (coeffMat_leapfrogSymbol_neg m2),
    gammaHat_vacuumCells, Matrix.mul_one]

theorem transpose_mul_self_cell {F : Matrix Cell Cell ℂ} {c : ℂ}
    (h : F qIdx qIdx = 0 ∧ F qIdx pIdx = 1 ∧ F pIdx qIdx = -1 ∧ F pIdx pIdx = c) :
    (Fᵀ * F) qIdx qIdx = 1 ∧ (Fᵀ * F) qIdx pIdx = -c ∧ (Fᵀ * F) pIdx qIdx = -c ∧
      (Fᵀ * F) pIdx pIdx = 1 + c ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [mul_qq, mul_qp, mul_pq, mul_pp, Matrix.transpose_apply, h1, h2, h3, h4]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- Milestone Q3, Example 31: one step of the leapfrog takes the vacuum symbol `γ̂ = 1` to
`γ̂'(k) = F̂(k)ᵀ F̂(k) = [[1, −c_k], [−c_k, 1 + c_k²]]`, `c_k = 2 cos k − m²`.
(notes: `ex:gs-leapfrog`) -/
theorem gammaHat_leapfrog_vacuum (m2 k : ℝ) :
    gammaHat (evolveCells (leapfrogSymbol m2) vacuumCells) k =
      (fourierSymbol k (leapfrogSymbol m2))ᵀ * fourierSymbol k (leapfrogSymbol m2) ∧
    gammaHat (evolveCells (leapfrogSymbol m2) vacuumCells) k qIdx qIdx = 1 ∧
    gammaHat (evolveCells (leapfrogSymbol m2) vacuumCells) k qIdx pIdx =
      -(2 * Complex.cos k - m2) ∧
    gammaHat (evolveCells (leapfrogSymbol m2) vacuumCells) k pIdx qIdx =
      -(2 * Complex.cos k - m2) ∧
    gammaHat (evolveCells (leapfrogSymbol m2) vacuumCells) k pIdx pIdx =
      1 + (2 * Complex.cos k - m2) ^ 2 := by
  rw [gammaHat_leapfrog_vacuum_eq]
  exact ⟨rfl, transpose_mul_self_cell (fourierSymbol_leapfrog m2 k)⟩

end QCALean.Bosonic
