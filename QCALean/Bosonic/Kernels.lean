/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.CellForm
import QCALean.Bosonic.Examples
import QCALean.Bosonic.Fourier

/-!
# Pull-back cells of translation-invariant forms

Milestone Q5b. For a Laurent matrix `L̂` (possibly rectangular) and cells `ν_•`, the pull-back cells
`(L*ν)_d = Σ_{m,m'} ℓ_mᵀ ν_{d+m−m'} ℓ_{m'}` represent the form `ν(L·, L·)`. For a square symbol they
are the evolved cells of milestone Q3, so that for summable cells their Fourier symbol is
`L̂(k)* ν̂(k) L̂(k)`; for on-site cells `g₀` the same formula `Ĉ(k)* g₀ Ĉ(k)` holds for a
rectangular symbol `Ĉ`. This file proves the support statements used for concatenation on the
chain (thesis p. 96), the corrected counterexample of p. 97, the Fourier form of the condition
(4.34) for finite-range noise, and the covariance-level core of thesis Lemma 4.12 on the chain.

## Main definitions and results

* `QCALean.Bosonic.symbolLin`, `QCALean.Bosonic.pullbackKernel`, `QCALean.Bosonic.onSiteKernel`
* `QCALean.Bosonic.cellForm_pullbackKernel`: the pull-back cells represent `ν(L·, L·)`.
* `QCALean.Bosonic.pullbackKernel_eq_evolveCells`, `QCALean.Bosonic.gammaHat_pullbackKernel`:
  comparison with the evolved cells of Q3 and their Fourier symbol.
* `QCALean.Bosonic.rotation_onSite_iff`: the corrected p. 97 claim.
* `QCALean.Bosonic.isStateConditionC_channel_iff_fourier`: the Fourier form of (4.34).
* `QCALean.Bosonic.dilation_lattice`: thesis Lemma 4.12 on the chain, at covariance level.
-/

open LinearAQFT BosonicLean.Weyl QCALean.Core Matrix Gaussian
open scoped ComplexOrder ComplexConjugate Pointwise

namespace QCALean.Bosonic

variable {n : ℕ}

local notation "Om" => Gaussian.symplecticForm

/-- The real-linear map of a symbol, on the lattice `G` (on the chain, `G = ℤ`).
(notes: `def:lc-pullback`) -/
noncomputable def symbolLin {G : Type*} [AddCommGroup G] (Ls : Sym G n) :
    PhaseVec G n →ₗ[ℝ] PhaseVec G n :=
  (Matrix.toLin' Ls).restrictScalars ℝ

/-- The rule of a symbol applied to a vector. -/
@[simp]
theorem symbolLin_apply {G : Type*} [AddCommGroup G] (Ls : Sym G n) (u : PhaseVec G n) :
    symbolLin Ls u = Matrix.toLin' Ls u :=
  rfl

/-! ### Comparison with the evolved cells of Q3 -/

/-- For a square symbol, the pull-back cells are the evolved cells of Q3.
(notes: `def:lc-pullback`) -/
theorem pullbackKernel_eq_evolveCells (Ls : Sym ℤ n)
    (g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    pullbackKernel Ls g = evolveCells Ls g :=
  rfl

/-- For a square symbol and summable cells, the Fourier symbol of the pull-back cells is
`L̂(k)* ν̂(k) L̂(k)` (Q3). (notes: `lem:lc-pullback`) -/
theorem gammaHat_pullbackKernel (Ls : Sym ℤ n)
    {g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hg : ∀ i j, Summable fun x => |g x i j|) (k : ℝ) :
    gammaHat (pullbackKernel Ls g) k =
      (fourierSymbol k Ls)ᴴ * gammaHat g k * fourierSymbol k Ls :=
  gammaHat_evolve_conjTranspose Ls hg k

/-! ### Helpers -/

/-- The coefficient matrices vanish outside the exponent set. -/
theorem laurentCoeff_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ] (Ls : Matrix κ ι L) {m : ℤ}
    (hm : m ∉ laurentSupport Ls) : laurentCoeff Ls m = 0 := by
  ext k i
  simp only [laurentCoeff, Matrix.of_apply, Matrix.zero_apply]
  by_contra h
  exact hm (support_coeff_subset_laurentSupport Ls k i (Finsupp.mem_support_iff.2 h))

/-- The pull-back cells as a sum over any superset of the exponent set. -/
theorem pullbackKernel_eq_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (Ls : Matrix κ ι L)
    (g : ℤ → Matrix κ κ ℝ) {S : Finset ℤ} (hS : laurentSupport Ls ⊆ S) (d : ℤ) :
    pullbackKernel Ls g d = ∑ m ∈ S, ∑ m' ∈ S,
      (laurentCoeff Ls m)ᵀ * g (d + m - m') * laurentCoeff Ls m' := by
  rw [pullbackKernel]
  refine (Finset.sum_subset hS fun m _ hm => ?_).trans
    (Finset.sum_congr rfl fun m _ => Finset.sum_subset hS fun m' _ hm' => ?_)
  · refine Finset.sum_eq_zero fun m' _ => ?_
    rw [laurentCoeff_eq_zero Ls hm, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
  · rw [laurentCoeff_eq_zero Ls hm', Matrix.mul_zero]

/-- Milestone Q5b, Lemma 20: the pull-back cells represent the pulled-back form.
(notes: `lem:lc-pullback`) -/
theorem cellForm_pullbackKernel (Ls : Sym ℤ n)
    (g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    cellForm (pullbackKernel Ls g) = (cellForm g).comp (symbolLin Ls) (symbolLin Ls) :=
  cellForm_pullbackKernel_rect Ls g

/-- Milestone Q5b, Lemma 20: pull-back cells of cell data are cell data.
(notes: `lem:lc-pullback`) -/
theorem cellData_pullbackKernel (Ls : Sym ℤ n)
    {g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (hg : CellData g) :
    CellData (pullbackKernel Ls g) := by
  rw [pullbackKernel_eq_evolveCells]
  exact evolveCells_cellData Ls hg

/-- The form of on-site cells is the lifted form. -/
theorem cellForm_onSiteKernel (B : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    cellForm (onSiteKernel B) = (liftForm B : LinearMap.BilinForm ℝ (PhaseVec ℤ n)) :=
  bilinForm_ext_siteVec fun x i y j => by
    rw [cellForm_siteVec, liftForm_siteVec, onSiteKernel]
    by_cases h : x = y
    · simp [h]
    · simp [h, sub_eq_zero]

/-- On-site cells of a symmetric matrix are cell data. -/
theorem cellData_onSiteKernel {g0 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hg0 : g0ᵀ = g0) : CellData (onSiteKernel g0) where
  summable i j := summable_of_ne_finset_zero (s := {0}) fun m hm => by
    rw [Finset.mem_singleton] at hm
    simp [onSiteKernel, hm]
  symm x := by
    by_cases hx : x = 0
    · subst hx; simp [onSiteKernel, hg0]
    · simp [onSiteKernel, hx]

/-- The Fourier symbol of on-site cells is constant. -/
theorem gammaHat_onSiteKernel (g0 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (k : ℝ) : gammaHat (onSiteKernel g0) k = g0.map Complex.ofReal := by
  rw [gammaHat, tsum_eq_single 0 fun m hm => by simp [onSiteKernel, hm]]
  simp [onSiteKernel]

/-- The exponents of a non-zero multiple of a Laurent matrix are those of the matrix. -/
theorem laurentSupport_smul {ι κ : Type*} [Fintype ι] [Fintype κ] {r : ℝ} (hr : r ≠ 0)
    (Ls : Matrix κ ι L) : laurentSupport (r • Ls) = laurentSupport Ls := by
  simp only [laurentSupport, Matrix.smul_apply, AddMonoidAlgebra.coeff_smul,
    Finsupp.support_smul_eq hr]

/-- The coefficient matrices of a multiple of a Laurent matrix. -/
theorem laurentCoeff_smul {ι κ : Type*} (r : ℝ) (Ls : Matrix κ ι L) (m : ℤ) :
    laurentCoeff (r • Ls) m = r • laurentCoeff Ls m := by
  ext i j
  simp [laurentCoeff]

/-- Pull-back cells of a non-zero multiple of a symbol scale quadratically. -/
theorem pullbackKernel_smul {ι κ : Type*} [Fintype ι] [Fintype κ] {r : ℝ} (hr : r ≠ 0)
    (Ls : Matrix κ ι L) (g : ℤ → Matrix κ κ ℝ) (d : ℤ) :
    pullbackKernel (r • Ls) g d = (r * r) • pullbackKernel Ls g d := by
  simp only [pullbackKernel, laurentSupport_smul hr, laurentCoeff_smul, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.smul_sum]

/-- Milestone Q5b: the symplectic form pulled back by a symbol is the form of the cells `K`, the
coefficients of `L̂⋆ᵀ Ω L̂`. (notes: `lem:lc-pullback`) -/
theorem sigma_comp_symbolLin (Ls : Sym ℤ n) :
    (sigma ℤ n).comp (symbolLin Ls) (symbolLin Ls) =
      cellForm (pullbackKernel Ls (onSiteKernel (Om n))) := by
  rw [cellForm_pullbackKernel, cellForm_onSiteKernel]
  rfl

/-- The pairing of two site vectors reads off a coefficient. -/
theorem pairing_siteVec (P : Sym ℤ n) (x y : ℤ) (i j : Gaussian.PhaseIndex n) :
    pairing P (siteVec x i) (siteVec y j) = (P i j).coeff (x - y) := by
  have hs : starVec (siteVec x i : PhaseVec ℤ n) = siteVec (-x) i := by
    funext k
    by_cases h : k = i
    · subst h; simp [starVec, siteVec, involution_T]
    · simp [starVec, siteVec, h]
  rw [pairing_apply, hs, siteVec, single_dotProduct, siteVec, mulVec_single]
  simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    AddMonoidAlgebra.coeff_single_mul_apply, AddMonoidAlgebra.coeff_mul_single_apply, one_mul,
    mul_one]
  congr 1
  ring

/-- The cells `K` are the coefficient matrices of `L̂⋆ᵀ Ω L̂`: `K_d` is the coefficient of `z^d`.
(notes: `lem:lc-pullback`) -/
theorem pullbackKernel_onSite_eq_coeffMat (Ls : Sym ℤ n) (d : ℤ) :
    pullbackKernel Ls (onSiteKernel (Om n)) d =
      coeffMat d (starTranspose Ls * const ℤ (Om n) * Ls) := by
  ext i j
  have h := congrArg (fun B : LinearMap.BilinForm ℝ (PhaseVec ℤ n) => B (siteVec d i) (siteVec 0 j))
    (sigma_comp_symbolLin Ls)
  simp only [LinearMap.BilinForm.comp_apply, cellForm_siteVec, sub_zero] at h
  rw [← h, symbolLin, LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, sigma,
    liftForm, pairing_toLin', pairing_siteVec, sub_zero]
  rfl

/-- Milestone Q5b, Proposition 26(a): ranges under concatenation are inclusions (F5). The inclusion
can be strict, since coefficients of the product can cancel, so there is no equality version.
(notes: `prop:lc-supports`) -/
theorem symbolRange_mul_subset' (L₁ L₂ : Sym ℤ n) :
    symbolRange (L₂ * L₁) ⊆ symbolRange L₁ + symbolRange L₂ := by
  intro d hd
  simp only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and] at hd
  obtain ⟨i, j, hd⟩ := hd
  rw [Matrix.mul_apply, AddMonoidAlgebra.coeff_sum] at hd
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hd)
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ hk)
  rw [show a + b = b + a from add_comm a b]
  exact Finset.add_mem_add (support_coeff_subset_symbolRange L₁ k j hb)
    (support_coeff_subset_symbolRange L₂ i k ha)

/-- Proposition 26(b) for a rectangular symbol and any superset of its exponent set. -/
theorem pullbackKernel_eq_zero_of_subset {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ls : Matrix κ ι L) (g : ℤ → Matrix κ κ ℝ) (Mg R : Finset ℤ) (hR : laurentSupport Ls ⊆ R)
    (hg : ∀ x ∉ Mg, g x = 0) (d : ℤ) (hd : d ∉ Mg + (R - R)) :
    pullbackKernel Ls g d = 0 := by
  refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun m' hm' => ?_
  rw [hg (d + m - m'), Matrix.mul_zero, Matrix.zero_mul]
  intro hmem
  apply hd
  have := Finset.add_mem_add hmem (Finset.sub_mem_sub (hR hm') (hR hm))
  rwa [show d + m - m' + (m' - m) = d by ring] at this

/-- Milestone Q5b, Proposition 26(b): noise supports under concatenation (F5).
(notes: `prop:lc-supports`) -/
theorem pullbackKernel_eq_zero (Ls : Sym ℤ n)
    (g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) (Mg : Finset ℤ)
    (hg : ∀ x ∉ Mg, g x = 0) (d : ℤ) (hd : d ∉ Mg + (symbolRange Ls - symbolRange Ls)) :
    pullbackKernel Ls g d = 0 :=
  pullbackKernel_eq_zero_of_subset Ls g Mg _ subset_rfl hg d hd

/-- On-site cells vanish off the origin. -/
theorem onSiteKernel_eq_zero {ι : Type*} (g0 : Matrix ι ι ℝ) :
    ∀ x ∉ ({0} : Finset ℤ), onSiteKernel g0 x = 0 :=
  fun x hx => ite_eq_right (by simpa using hx)

/-- Adding the singleton `{0}` does not change a finite set. -/
private theorem mem_singleton_zero_add {s : Finset ℤ} {d : ℤ} :
    d ∈ ({0} : Finset ℤ) + s ↔ d ∈ s := by
  simp [Finset.mem_add]

/-- Milestone Q5b, Proposition 26(c): the symbol of `σ(L·, L·)` lives on `R − R`.
(notes: `prop:lc-supports`) -/
theorem symbolRange_form_subset (Ls : Sym ℤ n) :
    symbolRange (starTranspose Ls * const ℤ (Om n) * Ls) ⊆ symbolRange Ls - symbolRange Ls := by
  intro d hd
  by_contra hnot
  simp only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finsupp.mem_support_iff] at hd
  obtain ⟨i, j, hij⟩ := hd
  apply hij
  have h0 := pullbackKernel_eq_zero Ls (onSiteKernel (Om n)) {0} (onSiteKernel_eq_zero _) d
    (fun h => hnot (mem_singleton_zero_add.1 h))
  have := congrFun (congrFun h0 i) j
  rw [pullbackKernel_onSite_eq_coeffMat] at this
  simpa [coeffMat] using this

/-- Milestone Q5b, Proposition 26(d): type I+II with `Mᵢ = Nᵢ − Nᵢ` is closed under
concatenation (p. 96). The hypothesis that `N₂` is non-empty is needed, since for `N₂ = ∅` the
statement fails. (notes: `prop:lc-supports`) -/
theorem typeI_II_comp {L₁ L₂ : Sym ℤ n}
    {g₁ g₂ : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (N₁ N₂ : Finset ℤ)
    (hr₁ : symbolRange L₁ ⊆ N₁) (hg₁ : ∀ x ∉ N₁ - N₁, g₁ x = 0) (hr₂ : symbolRange L₂ ⊆ N₂)
    (hg₂ : ∀ x ∉ N₂ - N₂, g₂ x = 0) (hN₂ : N₂.Nonempty) :
    symbolRange (L₂ * L₁) ⊆ N₁ + N₂ ∧
      ∀ x ∉ (N₁ + N₂) - (N₁ + N₂), (g₁ + pullbackKernel L₁ g₂) x = 0 := by
  refine ⟨(symbolRange_mul_subset' L₁ L₂).trans (Finset.add_subset_add hr₁ hr₂), fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hN₂
  have h1 : g₁ x = 0 := by
    refine hg₁ x fun hmem => hx ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.1 hmem
    exact Finset.mem_sub.2
      ⟨a + c, Finset.add_mem_add ha hc, b + c, Finset.add_mem_add hb hc, by abel⟩
  have h2 : pullbackKernel L₁ g₂ x = 0 := by
    refine pullbackKernel_eq_zero L₁ g₂ (N₂ - N₂) hg₂ x fun hmem => hx ?_
    obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.1 hmem
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.1 hy
    obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_sub.1 hz
    exact Finset.mem_sub.2 ⟨p + a, Finset.add_mem_add (hr₁ hp) ha, q + b,
      Finset.add_mem_add (hr₁ hq) hb, by abel⟩
  simp [Pi.add_apply, h1, h2]

/-- Milestone Q5b, Proposition 26(e): (4.39), for on-site noises the concatenation has on-site
noise iff the pulled-back second noise is on site. (notes: `prop:lc-supports`) -/
theorem onSite_comp_iff (L₁ : Sym ℤ n)
    (g01 g02 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    (∀ x ≠ 0, (onSiteKernel g01 + pullbackKernel L₁ (onSiteKernel g02)) x = 0) ↔
      ∀ x ≠ 0, pullbackKernel L₁ (onSiteKernel g02) x = 0 := by
  refine forall₂_congr fun x hx => ?_
  rw [Pi.add_apply, onSiteKernel, ite_eq_right hx, zero_add]

/-- The coefficient matrices of a nearest-neighbour symbol. -/
theorem laurentCoeff_nnSymbol (lm l0 lp : Matrix Cell Cell ℝ) (m : ℤ) :
    laurentCoeff (nnSymbol lm l0 lp) m =
      (if -1 = m then lm else 0) + (if 0 = m then l0 else 0) + (if 1 = m then lp else 0) := by
  change coeffMat m (nnSymbol lm l0 lp) = _
  simp only [nnSymbol, map_add, coeffMat_mono]

/-- A nearest-neighbour symbol has exponents in `{-1, 0, 1}`. -/
theorem laurentSupport_nnSymbol_subset (lm l0 lp : Matrix Cell Cell ℝ) :
    laurentSupport (nnSymbol lm l0 lp) ⊆ {-1, 0, 1} := by
  intro m hm
  simp only [laurentSupport, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finsupp.mem_support_iff] at hm
  obtain ⟨i, j, h⟩ := hm
  by_contra hm'
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm'
  obtain ⟨h1, h2, h3⟩ := hm'
  apply h
  have := congrFun (congrFun (laurentCoeff_nnSymbol lm l0 lp m) i) j
  simp only [laurentCoeff, Matrix.of_apply] at this
  rw [this]
  simp [show (-1 : ℤ) ≠ m from fun e => h1 e.symm, show (0 : ℤ) ≠ m from fun e => h2 e.symm,
    show (1 : ℤ) ≠ m from fun e => h3 e.symm]

/-- Milestone Q5b, Theorem 27: the pulled-back on-site noise at distance 2 for the example rule
is `(g₀)_qq λ² r rᵀ`, `r` the momentum row of the rotation (F6). (notes: `thm:lc-twosteps`) -/
theorem pullbackKernel_rotation_two (φ lam : ℝ) (g0 : Matrix Cell Cell ℝ) :
    pullbackKernel (rotationSymbol φ lam) (onSiteKernel g0) 2 =
      (g0 qIdx qIdx * lam ^ 2) • vecMulVec (rotation φ pIdx) (rotation φ pIdx) := by
  unfold rotationSymbol
  rw [pullbackKernel_eq_sum _ _ (laurentSupport_nnSymbol_subset _ _ _)]
  simp only [laurentCoeff_nnSymbol]
  norm_num [Finset.sum_insert, onSiteKernel]
  ext a b
  simp only [e1, Matrix.smul_apply, Matrix.mul_apply, vecMulVec_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, reduceIte, one_mul,
    smul_eq_mul]
  ring

/-- Milestone Q5b, Theorem 27, the corrected p. 97 claim (F6): for positive semidefinite on-site
noise, two steps of the example rule keep the noise on site iff `λ = 0` or `(g₀)_qq = 0`.
(notes: `thm:lc-twosteps`) -/
theorem rotation_onSite_iff (φ lam : ℝ) {g0 : Matrix Cell Cell ℝ} (hg : g0.PosSemidef) :
    (∀ x ≠ 0, pullbackKernel (rotationSymbol φ lam) (onSiteKernel g0) x = 0) ↔
      lam = 0 ∨ g0 qIdx qIdx = 0 := by
  constructor
  · intro h
    have h2 := h 2 (by norm_num)
    rw [pullbackKernel_rotation_two] at h2
    have hq := congrFun (congrFun h2 qIdx) qIdx
    have hp := congrFun (congrFun h2 pIdx) pIdx
    simp only [Matrix.smul_apply, vecMulVec_apply, rotation, Matrix.of_apply, smul_eq_mul,
      Matrix.zero_apply] at hq hp
    have h0 : g0 qIdx qIdx * lam ^ 2 = 0 := by
      have := Real.sin_sq_add_cos_sq φ
      linear_combination hq + hp - (g0 qIdx qIdx * lam ^ 2) * this
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (pow_eq_zero_iff two_ne_zero |>.1 h0)
  · intro h x hx
    have hv : g0 * vecMulVec e1 (lam • rotation φ pIdx) = 0 ∧
        (vecMulVec e1 (lam • rotation φ pIdx))ᵀ * g0 = 0 := by
      rcases h with h | h
      · simp [h]
      · have hcol : g0 *ᵥ e1 = 0 := (hg.dotProduct_mulVec_zero_iff (x := e1)).1 (by simp [e1, h])
        have hsym : g0ᵀ = g0 := by
          rw [← conjTranspose_eq_transpose_of_trivial]; exact hg.1
        constructor
        · rw [mul_vecMulVec, hcol, zero_vecMulVec]
        · rw [transpose_vecMulVec, vecMulVec_mul, ← mulVec_transpose, hsym, hcol, vecMulVec_zero]
    have hl : ∀ m ≠ 0, g0 * laurentCoeff (rotationSymbol φ lam) m = 0 ∧
        (laurentCoeff (rotationSymbol φ lam) m)ᵀ * g0 = 0 := by
      intro m hm
      unfold rotationSymbol
      have h0m : ¬((0 : ℤ) = m) := fun e => hm e.symm
      simp only [laurentCoeff_nnSymbol, h0m, reduceIte, add_zero]
      split_ifs <;> simp only [Matrix.mul_add, Matrix.transpose_add, Matrix.add_mul,
        Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hv.1, hv.2,
        and_self]
    refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun m' _ => ?_
    by_cases hd : x + m - m' = 0
    · rw [onSiteKernel, ite_eq_left hd]
      by_cases hm' : m' = 0
      · have hm : m ≠ 0 := by omega
        rw [(hl m hm).2, Matrix.zero_mul]
      · rw [Matrix.mul_assoc, (hl m' hm').1, Matrix.mul_zero]
    · rw [onSiteKernel, ite_eq_right hd, Matrix.mul_zero, Matrix.zero_mul]

/-! ### Dilations on the chain -/

/-- A real matrix mapped to `ℂ` has conjugate transpose the mapped transpose. -/
private theorem conjTranspose_map_ofReal {ι κ : Type*} (M : Matrix κ ι ℝ) :
    (M.map Complex.ofReal)ᴴ = Mᵀ.map Complex.ofReal := by
  ext i j
  simp [Matrix.conjTranspose_apply]

/-- The Fourier symbol of a rectangular symbol as a finite sum. -/
theorem map_evalCircle_eq_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (C : Matrix κ ι L) (k : ℝ) :
    C.map (evalCircle k) = ∑ x ∈ laurentSupport C,
      Complex.exp (-(k : ℂ) * x * Complex.I) • (laurentCoeff C x).map Complex.ofReal := by
  ext a b
  rw [Matrix.map_apply, evalCircle_apply, Matrix.sum_apply,
    Finsupp.sum_of_support_subset _ (support_coeff_subset_laurentSupport C a b) _
      (fun _ _ => by simp)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [laurentCoeff, mul_comm]

/-- Lemma 20 on the circle, for on-site cells and a rectangular symbol:
`(C*g₀)^(k) = Ĉ(k)* g₀ Ĉ(k)`. -/
theorem gammaHat_pullbackKernel_onSite {m : ℕ}
    (C : Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex n) L)
    (g0 : Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex m) ℝ) (k : ℝ) :
    gammaHat (pullbackKernel C (onSiteKernel g0)) k =
      (C.map (evalCircle k))ᴴ * g0.map Complex.ofReal * C.map (evalCircle k) := by
  set S := laurentSupport C
  set e : ℤ → ℂ := fun x => Complex.exp (-(k : ℂ) * x * Complex.I) with he
  set A : ℤ → Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex n) ℂ :=
    fun x => (laurentCoeff C x).map Complex.ofReal with hA
  set P : ℤ → ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℂ :=
    fun x y => (A x)ᵀ * g0.map Complex.ofReal * A y with hP
  have hterm : ∀ d : ℤ, e d • (pullbackKernel C (onSiteKernel g0) d).map Complex.ofReal =
      ∑ x ∈ S, ∑ y ∈ S, if d = y - x then e (y - x) • P x y else 0 := by
    intro d
    rw [pullbackKernel, map_ofReal_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_ofReal_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : d = y - x
    · subst h
      rw [ite_eq_left rfl, onSiteKernel, ite_eq_left (by ring)]
      simp only [hP, hA, ← Matrix.transpose_map]
      congr 1
      exact (Matrix.map_mul (f := Complex.ofRealHom)).trans
        (congrArg (· * _) (Matrix.map_mul (f := Complex.ofRealHom)))
    · rw [ite_eq_right h, onSiteKernel, ite_eq_right (by omega)]
      simp
  have hsum : ∀ x y, Summable fun d : ℤ => if d = y - x then e (y - x) • P x y else 0 :=
    fun x y => summable_of_ne_finset_zero (s := {y - x}) fun d hd => by
      rw [Finset.mem_singleton] at hd
      simp [hd]
  rw [gammaHat, tsum_congr hterm,
    Summable.tsum_finsetSum fun x _ => summable_sum fun y _ => hsum x y]
  simp_rw [Summable.tsum_finsetSum fun y _ => hsum _ y, tsum_ite_eq]
  rw [map_evalCircle_eq_sum, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP, hA,
    conjTranspose_map_ofReal, Matrix.transpose_map]
  congr 1
  simp only [he, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, map_intCast, Complex.conj_I]
  push_cast
  ring

/-- The rule of a block symbol on a system vector: `S(u, 0) = (S₁₁ u, S₂₁ u)`. -/
theorem toLin'_sumElim_zero {m : ℕ}
    (S : Matrix (Gaussian.PhaseIndex n ⊕ Gaussian.PhaseIndex m)
      (Gaussian.PhaseIndex n ⊕ Gaussian.PhaseIndex m) L) (u : PhaseVec ℤ n) :
    Matrix.toLin' S (Sum.elim u 0) =
      Sum.elim (Matrix.toLin' S.toBlocks₁₁ u) (Matrix.toLin' S.toBlocks₂₁ u) := by
  funext a
  rcases a with a | a <;>
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

/-- The lifted form of a block-diagonal matrix splits over system and ancilla. -/
theorem liftForm_fromBlocks_sumElim {m : ℕ}
    (B : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (B' : Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex m) ℝ)
    (a a' : PhaseVec ℤ n) (c c' : PhaseVec ℤ m) :
    liftForm (G := ℤ) (Matrix.fromBlocks B 0 0 B') (Sum.elim a c) (Sum.elim a' c') =
      liftForm B a a' + liftForm B' c c' := by
  simp [liftForm_apply, Fintype.sum_sum_type]

/-- A cell `γ₀` with `γ₀ + iΩ ≥ 0` satisfies the real pair form of the state condition. -/
theorem pair_of_posSemidef {m : ℕ} {γ0 : Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex m) ℝ}
    (hγ0 : (γ0.map Complex.ofReal + Complex.I • (Om m).map Complex.ofReal).PosSemidef)
    (a b : Gaussian.PhaseIndex m → ℝ) :
    2 * ∑ i, ∑ j, a i * Om m i j * b j ≤
      ∑ i, ∑ j, a i * γ0 i j * a j + ∑ i, ∑ j, b i * γ0 i j * b j := by
  have h := hγ0.dotProduct_mulVec_nonneg (fun i => (a i : ℂ) + Complex.I * b i)
  rw [star_dotProduct_mulVec_eq] at h
  have hre := (Complex.nonneg_iff.1 h).1
  have hΩ : ∀ i j, Om m j i = -Om m i j := fun i j => by
    have := congrFun (congrFun (Gaussian.transpose_symplecticForm m) i) j
    simpa using this
  have hswap : ∑ i, ∑ j, b i * Om m i j * a j = -∑ i, ∑ j, a i * Om m i j * b j := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΩ]
    ring
  have e : ∀ i j, (conj ((a i : ℂ) + Complex.I * b i) * ((a j : ℂ) + Complex.I * b j) *
      (γ0.map Complex.ofReal + Complex.I • (Om m).map Complex.ofReal) i j).re =
      a i * γ0 i j * a j + b i * γ0 i j * b j - a i * Om m i j * b j +
        b i * Om m i j * a j := by
    intro i j
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re, Complex.add_re,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im]
    ring
  simp only [Complex.re_sum, e, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hre
  linarith [hswap]

/-- Milestone Q5b, Theorem 31, thesis Lemma 4.12 on the chain at covariance level: a
translation-invariant symplectic `S` on system (`n` modes) and ancilla (`m` modes) with an on-site
ancilla state `γ₀` gives channel data `A = S₁₁`, `ν = C*γ₀` (`C = S₂₁`) satisfying (4.34), with
`ν̂(k) = Ĉ(k)* γ₀ Ĉ(k)` and noise supported in `D − D`, `D` the range of `S` (F7).
(notes: `thm:lc-dilation`) -/
theorem dilation_lattice {m : ℕ}
    (S : Matrix (Gaussian.PhaseIndex n ⊕ Gaussian.PhaseIndex m)
      (Gaussian.PhaseIndex n ⊕ Gaussian.PhaseIndex m) L)
    (hS : starTranspose S * const ℤ (Matrix.fromBlocks (Om n) 0 0 (Om m)) * S =
      const ℤ (Matrix.fromBlocks (Om n) 0 0 (Om m)))
    {γ0 : Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex m) ℝ}
    (hγ0 : (γ0.map Complex.ofReal + Complex.I • (Om m).map Complex.ofReal).PosSemidef) :
    IsStateConditionC (cellForm (pullbackKernel S.toBlocks₂₁ (onSiteKernel γ0)))
        ((phaseSpace ℤ n).sigma - ((phaseSpace ℤ n).sigma).comp (symbolLin S.toBlocks₁₁)
          (symbolLin S.toBlocks₁₁)) ∧
      (∀ k, gammaHat (pullbackKernel S.toBlocks₂₁ (onSiteKernel γ0)) k =
        (S.toBlocks₂₁.map (evalCircle k))ᴴ * γ0.map Complex.ofReal *
          S.toBlocks₂₁.map (evalCircle k)) ∧
      symbolRange S.toBlocks₁₁ ⊆ symbolRange S ∧
      ∀ d ∉ symbolRange S - symbolRange S,
        pullbackKernel S.toBlocks₂₁ (onSiteKernel γ0) d = 0 := by
  set Cl : PhaseVec ℤ n →ₗ[ℝ] PhaseVec ℤ m :=
    (Matrix.toLin' S.toBlocks₂₁).restrictScalars ℝ with hCl
  have hpres : ∀ u w, sigma ℤ n (symbolLin S.toBlocks₁₁ u) (symbolLin S.toBlocks₁₁ w) +
      sigma ℤ m (Cl u) (Cl w) = sigma ℤ n u w := by
    intro u w
    have h := (preserves_iff _ S).2 hS (Sum.elim u 0) (Sum.elim w 0)
    rw [toLin'_sumElim_zero, toLin'_sumElim_zero, liftForm_fromBlocks_sumElim,
      liftForm_fromBlocks_sumElim] at h
    simpa [sigma, symbolLin, hCl] using h
  have hγsymm : γ0ᵀ = γ0 := by
    ext i j
    have := congrArg Complex.re (congrFun (congrFun hγ0.1 j) i)
    have hΩ := congrFun (congrFun (Gaussian.transpose_symplecticForm m) i) j
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hΩ
    simp [Matrix.conjTranspose_apply, hΩ] at this
    rw [Matrix.transpose_apply]
    exact this.symm
  have hsymm : (liftForm (G := ℤ) γ0).IsSymm := by
    rw [← cellForm_onSiteKernel]
    refine cellForm_isSymm fun x => ?_
    by_cases hx : x = 0
    · simp [onSiteKernel, hx, hγsymm]
    · simp [onSiteKernel, hx]
  have hst : IsStateConditionC (liftForm (G := ℤ) γ0) (sigma ℤ m) :=
    (isStateConditionC_iff_pair hsymm (sigma_isAlt ℤ m)).2
      (isStateConditionPair_liftForm γ0 (pair_of_posSemidef hγ0))
  have hν : cellForm (pullbackKernel S.toBlocks₂₁ (onSiteKernel γ0)) =
      (liftForm (G := ℤ) γ0).comp Cl Cl := by
    rw [cellForm_pullbackKernel_rect, cellForm_onSiteKernel]
  have hsub : laurentSupport S.toBlocks₂₁ ⊆ symbolRange S := by
    intro x hx
    simp only [laurentSupport, symbolRange, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at hx ⊢
    obtain ⟨i, j, h⟩ := hx
    exact ⟨Sum.inr i, Sum.inl j, h⟩
  refine ⟨?_, fun k => gammaHat_pullbackKernel_onSite _ _ k, ?_, ?_⟩
  · intro k u
    convert hst k (fun j => Cl (u j)) using 1
    ext j l
    have h := hpres (u j) (u l)
    simp only [Matrix.of_apply, hν, LinearMap.BilinForm.comp_apply, LinearMap.sub_apply]
    change _ + Complex.I * ((sigma ℤ n (u j) (u l) - sigma ℤ n _ _ : ℝ) : ℂ) = _
    rw [← h]
    push_cast
    ring
  · intro x hx
    simp only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, j, h⟩ := hx
    exact ⟨Sum.inl i, Sum.inl j, h⟩
  · intro d hd
    exact pullbackKernel_eq_zero_of_subset _ _ {0} _ hsub (onSiteKernel_eq_zero _) d
      (fun h => hd (mem_singleton_zero_add.1 h))

/-! ### The Fourier form of (4.34) -/

section Fourier

variable {ι : Type*} [Fintype ι]

/-- Parseval for complex cells of finite range on a finite region: the finite-range case of
`QCALean.Core.parseval_matrix`, with the sites written as a `Finset`. -/
theorem parseval_cells {c : ℤ → Matrix ι ι ℂ} (R : ℕ)
    (hc : ∀ m, (R : ℤ) < |m| → c m = 0) (T : Finset ℤ) (ν : ℤ → ι → ℂ) :
    ∫ k in (-Real.pi)..Real.pi,
      star (fun i => ∑ x ∈ T, ν x i * Complex.exp (-(k : ℂ) * x * Complex.I)) ⬝ᵥ
        ((∑ m ∈ Finset.Icc (-(R : ℤ)) R, Complex.exp (-(k : ℂ) * m * Complex.I) • c m) *ᵥ
          fun i => ∑ x ∈ T, ν x i * Complex.exp (-(k : ℂ) * x * Complex.I)) =
      2 * Real.pi * ∑ x ∈ T, ∑ y ∈ T, ∑ i, ∑ j, conj (ν x i) * ν y j * c (x - y) i j := by
  have hout : ∀ m ∉ Finset.Icc (-(R : ℤ)) R, c m = 0 := fun m hm =>
    hc m (by rw [Finset.mem_Icc, not_and_or] at hm; rw [lt_abs]; omega)
  have hsum : ∀ i j, Summable fun m => ‖c m i j‖ := fun i j =>
    summable_of_ne_finset_zero (s := Finset.Icc (-(R : ℤ)) R) fun m hm => by simp [hout m hm]
  have hC : ∀ (k : ℝ) i j, (∑ m ∈ Finset.Icc (-(R : ℤ)) R,
      Complex.exp (-(k : ℂ) * m * Complex.I) • c m) i j =
      ∑' m : ℤ, c m i j * Complex.exp (-(k : ℂ) * m * Complex.I) := by
    intro k i j
    rw [tsum_eq_sum (s := Finset.Icc (-(R : ℤ)) R) fun m hm => by simp [hout m hm]]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]
  have hP := parseval_matrix hsum hC (fun x : T => (x : ℤ)) fun x i => ν x i
  have e1 : ∀ k : ℝ, (fun i => ∑ x ∈ T, ν x i * Complex.exp (-(k : ℂ) * x * Complex.I)) =
      fun i => ∑ x : T, ν x i * Complex.exp (-(k : ℂ) * ((x : ℤ) : ℤ) * Complex.I) :=
    fun k => funext fun i =>
      (Finset.sum_coe_sort T fun x => ν x i * Complex.exp (-(k : ℂ) * x * Complex.I)).symm
  have e2 : (∑ x ∈ T, ∑ y ∈ T, ∑ i, ∑ j, conj (ν x i) * ν y j * c (x - y) i j) =
      ∑ x : T, ∑ y : T, ∑ i, ∑ j, conj (ν x i) * ν y j * c ((x : ℤ) - y) i j := by
    rw [← Finset.sum_coe_sort T]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_coe_sort T]
  rw [e2, ← hP]
  refine intervalIntegral.integral_congr fun k _ => ?_
  rw [e1 k]

end Fourier

/-- The quadratic form of `γ + iB` on the site vectors of a region, for a cell form `γ` and a
form `B` with cells `h`, as a double sum of the complex cells `γ_d + i h_d`. -/
theorem quad_region_cells (g h : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (B : LinearMap.BilinForm ℝ (PhaseVec ℤ n))
    (hB : ∀ x y i j, B (siteVec x i) (siteVec y j) = h (x - y) i j) (T : Finset ℤ)
    (ν : ℤ → Gaussian.PhaseIndex n → ℂ) :
    star (fun a => ν ((regionEquiv T).symm a).1 ((regionEquiv T).symm a).2) ⬝ᵥ
      ((Matrix.of fun a b => (cellForm g (regionVec T a) (regionVec T b) : ℂ) +
          Complex.I * (B (regionVec T a) (regionVec T b) : ℂ)) *ᵥ
        fun a => ν ((regionEquiv T).symm a).1 ((regionEquiv T).symm a).2) =
      ∑ x ∈ T, ∑ y ∈ T, ∑ i, ∑ j, conj (ν x i) * ν y j *
        ((g (x - y)).map Complex.ofReal + Complex.I • (h (x - y)).map Complex.ofReal) i j := by
  rw [star_dotProduct_mulVec_eq, ← (regionEquiv T).sum_comp, Fintype.sum_prod_type,
    ← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_coe_sort T, Finset.sum_comm (s := (Finset.univ : Finset T))
    (t := (Finset.univ : Finset (Gaussian.PhaseIndex n)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (regionEquiv T).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply, regionVec, Equiv.symm_apply_apply, cellForm_siteVec, hB,
    Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]

/-- For cell data `ν`, the matrix `ν̂(k) + iΩ − i L̂(k)* Ω L̂(k)` of Theorem 30 is Hermitian. -/
theorem isHermitian_channelMatrix (Ls : Sym ℤ n)
    {g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (hg : CellData g) (k : ℝ) :
    (gammaHat g k + Complex.I • (Om n).map Complex.ofReal -
      Complex.I • ((fourierSymbol k Ls)ᴴ * (Om n).map Complex.ofReal *
        fourierSymbol k Ls)).IsHermitian := by
  refine ((gammaHat_isHermitian hg k).add iOmega_isHermitian).sub ?_
  have hΩH : ((Om n).map Complex.ofReal)ᴴ = -(Om n).map Complex.ofReal := by
    rw [conjTranspose_map_ofReal, Gaussian.transpose_symplecticForm]
    ext i j
    simp
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hΩH, Complex.star_def, Complex.conj_I]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_smul, smul_neg, neg_neg, Matrix.mul_assoc]

/-- Milestone Q5b, Theorem 30: the Fourier form of (4.34) for finite-range noise,
`ν̂(k) + iΩ − i L̂(k)* Ω L̂(k) ≥ 0` for all `k`. (notes: `thm:lc-fourier`) -/
theorem isStateConditionC_channel_iff_fourier (Ls : Sym ℤ n)
    {g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (hg : CellData g) (R : ℕ)
    (hR : ∀ m, (R : ℤ) < |m| → g m = 0) :
    IsStateConditionC (cellForm g)
        ((phaseSpace ℤ n).sigma - ((phaseSpace ℤ n).sigma).comp (symbolLin Ls) (symbolLin Ls)) ↔
      ∀ k, (gammaHat g k + Complex.I • (Om n).map Complex.ofReal -
        Complex.I • ((fourierSymbol k Ls)ᴴ * (Om n).map Complex.ofReal *
          fourierSymbol k Ls)).PosSemidef := by
  set K := pullbackKernel Ls (onSiteKernel (Om n)) with hK
  set B : LinearMap.BilinForm ℝ (PhaseVec ℤ n) :=
    (phaseSpace ℤ n).sigma - ((phaseSpace ℤ n).sigma).comp (symbolLin Ls) (symbolLin Ls)
    with hBdef
  set h : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ :=
    fun d => onSiteKernel (Om n) d - K d with hh
  set c : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℂ :=
    fun d => (g d).map Complex.ofReal + Complex.I • (h d).map Complex.ofReal with hc
  set R' : ℕ := R + (symbolRange Ls - symbolRange Ls).sup Int.natAbs with hR'
  have hK0 : ∀ d, (R' : ℤ) < |d| → K d = 0 := by
    intro d hd
    refine pullbackKernel_eq_zero Ls _ {0} (onSiteKernel_eq_zero _) d fun hmem => ?_
    have := Finset.le_sup (f := Int.natAbs) (mem_singleton_zero_add.1 hmem)
    rw [Int.abs_eq_natAbs] at hd
    omega
  have hg0 : ∀ d, (R' : ℤ) < |d| → g d = 0 := fun d hd => hR d (by omega)
  have hcR : ∀ d, (R' : ℤ) < |d| → c d = 0 := by
    intro d hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp only [abs_zero] at hd
      omega
    simp [hc, hh, hg0 d hd, hK0 d hd, onSiteKernel, hd0]
  have hBsite : ∀ x y i j, B (siteVec x i) (siteVec y j) = h (x - y) i j := by
    intro x y i j
    change sigma ℤ n _ _ - (sigma ℤ n).comp (symbolLin Ls) (symbolLin Ls) _ _ = _
    rw [sigma_comp_symbolLin, cellForm_siteVec, sigma_siteVec]
    by_cases hxy : x = y <;> simp [hxy, hh, hK, onSiteKernel, sub_eq_zero]
  have hBalt : B.IsAlt := fun u => by
    change sigma ℤ n u u - sigma ℤ n (symbolLin Ls u) (symbolLin Ls u) = 0
    rw [sigma_isAlt ℤ n u, sigma_isAlt ℤ n, sub_zero]
  have hgs := cellForm_isSymm hg.symm
  have hphase : ∀ (k : ℝ) (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ),
      (∀ d, (R' : ℤ) < |d| → γc d = 0) →
      ∑ m ∈ Finset.Icc (-(R' : ℤ)) R',
        Complex.exp (-(k : ℂ) * m * Complex.I) • (γc m).map Complex.ofReal = gammaHat γc k := by
    intro k γc hγc
    rw [gammaHat, tsum_eq_sum (s := Finset.Icc (-(R' : ℤ)) R') fun m hm => by
      rw [hγc m (by rw [Finset.mem_Icc, not_and_or] at hm; rw [lt_abs]; omega)]
      simp]
  have hΩ0 : ∀ d, (R' : ℤ) < |d| → onSiteKernel (Om n) d = 0 := fun d hd => by
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp only [abs_zero] at hd
      omega
    exact ite_eq_right hd0
  have hcHat : ∀ k : ℝ, ∑ m ∈ Finset.Icc (-(R' : ℤ)) R',
      Complex.exp (-(k : ℂ) * m * Complex.I) • c m =
      gammaHat g k + Complex.I • (Om n).map Complex.ofReal -
        Complex.I • ((fourierSymbol k Ls)ᴴ * (Om n).map Complex.ofReal * fourierSymbol k Ls) := by
    intro k
    rw [fourierSymbol, ← gammaHat_pullbackKernel_onSite, ← hphase k g hg0,
      ← gammaHat_onSiteKernel (Om n) k,
      ← hphase k _ hΩ0, ← hphase k (pullbackKernel Ls (onSiteKernel (Om n))) hK0]
    ext a b
    simp only [hc, hh, hK, Matrix.sum_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul, Complex.ofReal_sub, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have herm := isHermitian_channelMatrix Ls hg
  constructor
  · intro hs k
    have hpair := (isStateConditionC_iff_pair hgs hBalt).1 hs
    have hpsd := posSemidef_of_fejer (c := c) R' hcR k (by rw [hcHat]; exact herm k)
      fun N ν => by
        have hreg := (posSemidef_region_iff (Finset.Ico (0 : ℤ) N) hgs hBalt).2
          fun u _ w _ => hpair u w
        have hq := hreg.dotProduct_mulVec_nonneg
          (fun a => ν ((regionEquiv (Finset.Ico (0 : ℤ) N)).symm a).1
            ((regionEquiv (Finset.Ico (0 : ℤ) N)).symm a).2)
        rw [quad_region_cells g h B hBsite] at hq
        exact (Complex.nonneg_iff.1 hq).1
    rwa [hcHat] at hpsd
  · intro hk
    have hk' : ∀ k : ℝ, (∑ m ∈ Finset.Icc (-(R' : ℤ)) R',
        Complex.exp (-(k : ℂ) * m * Complex.I) • c m).PosSemidef := fun k : ℝ => by
      rw [hcHat]
      exact hk k
    refine (isStateConditionC_iff_pair hgs hBalt).2
      (isStateConditionPair_of_region hBalt fun T => ?_)
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_stateMatrix hgs hBalt _) fun c' => ?_
    set ν : ℤ → Gaussian.PhaseIndex n → ℂ := fun x i =>
      if hx : x ∈ T then c' (regionEquiv T (⟨x, hx⟩, i)) else 0 with hν
    have hc' : c' = fun a => ν ((regionEquiv T).symm a).1 ((regionEquiv T).symm a).2 := by
      funext a
      simp [hν]
    rw [hc', quad_region_cells g h B hBsite]
    exact nonneg_of_integral_eq (fun k => (hk' k).dotProduct_mulVec_nonneg _)
      (parseval_cells R' hcR T ν)

end QCALean.Bosonic
