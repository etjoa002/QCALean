/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.Cells
import BosonicLean.PhaseSpace.Covariance
import BosonicLean.PhaseSpace.Positivity
import BosonicLean.PhaseSpace.Subsystem
import BosonicLean.PhaseSpace.DirectSum
import BosonicLean.PhaseSpace.Examples

/-!
# Covariance matrices of finite regions

Milestone Q3, Section 4.1 and Examples 18, 19, 29. On a finite region `O`, a covariance form
`γ` becomes BosonicLean's covariance matrix of `n|O|` modes,
`cov_O(γ) = P_O Ω_Oᵀ γ_O Ω_O P_Oᵀ`: the matrix `γ_O` of the form on the site vectors, conjugated
by the symplectic form and reordered to all positions before all momenta. The state condition on
`O` is BosonicLean's admissibility of `cov_O(γ)`.

## Main definitions and results

* `QCALean.Bosonic.regionEquiv`, `QCALean.Bosonic.restrictMatrix`,
  `QCALean.Bosonic.covarianceMatrix`, `QCALean.Bosonic.IsStateConditionOn`
* `QCALean.Bosonic.isAdmissible_covarianceMatrix_iff`
-/

open LinearAQFT BosonicLean.Weyl QCALean.Core Matrix Gaussian
open scoped ComplexOrder ComplexConjugate

namespace QCALean.Bosonic

section Region

variable {G : Type*} [AddCommGroup G] {n : ℕ}

/-- Milestone Q3, Definition 13(b): the enumeration `O × PhaseIndex n ≃ PhaseIndex (n|O|)`,
positions first. (notes: `def:gs-covmat`) -/
noncomputable def regionEquiv (O : Finset G) :
    O × Gaussian.PhaseIndex n ≃ Gaussian.PhaseIndex (n * O.card) :=
  (Equiv.prodSumDistrib O (Fin n) (Fin n)).trans <|
    let e : O × Fin n ≃ Fin (n * O.card) :=
      (Equiv.prodComm _ _).trans ((Equiv.prodCongr (Equiv.refl _) O.equivFin).trans
        finProdFinEquiv)
    Equiv.sumCongr e e

/-- The site vector of the mode `a` of the region. (notes: `def:gs-covmat`) -/
noncomputable def regionVec (O : Finset G) (a : Gaussian.PhaseIndex (n * O.card)) :
    PhaseVec G n :=
  siteVec (((regionEquiv O).symm a).1 : G) ((regionEquiv O).symm a).2

/-- Milestone Q3, Definition 13(a): `P_O γ_O P_Oᵀ`, the matrix of `γ` on the site vectors of the
region, in BosonicLean's order. (notes: `def:gs-covmat`) -/
noncomputable def restrictMatrix (O : Finset G) (γ : LinearMap.BilinForm ℝ (PhaseVec G n)) :
    Matrix (Gaussian.PhaseIndex (n * O.card)) (Gaussian.PhaseIndex (n * O.card)) ℝ :=
  Matrix.of fun a b => γ (regionVec O a) (regionVec O b)

/-- Milestone Q3, Definition 13(c): the covariance matrix `cov_O(γ) = Ωᵀ (P_O γ_O P_Oᵀ) Ω`
(Lemma 14(b)). (notes: `def:gs-covmat`) -/
noncomputable def covarianceMatrix (O : Finset G) (γ : LinearMap.BilinForm ℝ (PhaseVec G n)) :
    Matrix (Gaussian.PhaseIndex (n * O.card)) (Gaussian.PhaseIndex (n * O.card)) ℝ :=
  (Gaussian.symplecticForm (n * O.card))ᵀ * restrictMatrix O γ *
    Gaussian.symplecticForm (n * O.card)

/-- Milestone Q3, Section 4.1: the state condition on the vectors supported in `O`, in
real-pair form. (notes: `def:gs-covmat`) -/
def IsStateConditionOn (O : Finset G) (γ : LinearMap.BilinForm ℝ (PhaseVec G n)) : Prop :=
  (∀ u ∈ loc G n (O : Set G), 0 ≤ γ u u) ∧
    ∀ u ∈ loc G n (O : Set G), ∀ w ∈ loc G n (O : Set G), sigma G n u w ^ 2 ≤ γ u u * γ w w

open scoped Classical in
/-- The block-diagonal matrix `P_O (1_O ⊗ X) P_Oᵀ`. (notes: `cor:gs-onsite`) -/
noncomputable def blockDiag (O : Finset G) (X : Matrix (Gaussian.PhaseIndex n)
    (Gaussian.PhaseIndex n) ℝ) :
    Matrix (Gaussian.PhaseIndex (n * O.card)) (Gaussian.PhaseIndex (n * O.card)) ℝ :=
  Matrix.of fun a b => if ((regionEquiv O).symm a).1 = ((regionEquiv O).symm b).1 then
    X ((regionEquiv O).symm a).2 ((regionEquiv O).symm b).2 else 0

omit [AddCommGroup G] in
open scoped Classical in
theorem blockDiag_apply_equiv (O : Finset G) (X : Matrix (Gaussian.PhaseIndex n)
    (Gaussian.PhaseIndex n) ℝ) (p q : O × Gaussian.PhaseIndex n) :
    blockDiag O X (regionEquiv O p) (regionEquiv O q) = if p.1 = q.1 then X p.2 q.2 else 0 := by
  simp [blockDiag]

omit [AddCommGroup G] in
theorem blockDiag_mul (O : Finset G) (X Y : Matrix (Gaussian.PhaseIndex n)
    (Gaussian.PhaseIndex n) ℝ) : blockDiag O X * blockDiag O Y = blockDiag O (X * Y) := by
  ext a c
  obtain ⟨p, rfl⟩ := (regionEquiv O).surjective a
  obtain ⟨q, rfl⟩ := (regionEquiv O).surjective c
  rw [Matrix.mul_apply, ← (regionEquiv O).sum_comp, blockDiag_apply_equiv,
    Fintype.sum_prod_type]
  simp only [blockDiag_apply_equiv, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single p.1]
  · by_cases h : p.1 = q.1
    · simp [h, Matrix.mul_apply]
    · simp [h]
  · intro y _ hy
    exact Finset.sum_eq_zero fun j _ => by simp [Ne.symm hy]
  · simp

omit [AddCommGroup G] in
theorem blockDiag_transpose (O : Finset G) (X : Matrix (Gaussian.PhaseIndex n)
    (Gaussian.PhaseIndex n) ℝ) : (blockDiag O X)ᵀ = blockDiag O Xᵀ := by
  ext a b
  simp only [Matrix.transpose_apply, blockDiag, Matrix.of_apply]
  congr 1
  exact propext eq_comm

omit [AddCommGroup G] in
theorem blockDiag_one (O : Finset G) :
    blockDiag O (1 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) = 1 := by
  ext a b
  obtain ⟨p, rfl⟩ := (regionEquiv O).surjective a
  obtain ⟨q, rfl⟩ := (regionEquiv O).surjective b
  rw [blockDiag_apply_equiv, Matrix.one_apply]
  simp only [Matrix.one_apply, (regionEquiv O).apply_eq_iff_eq, Prod.ext_iff]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff]

theorem liftForm_siteVec [DecidableEq G]
    (B : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (x y : G) (i j : Gaussian.PhaseIndex n) :
    liftForm B (siteVec x i) (siteVec y j) = if x = y then B i j else 0 := by
  rw [liftForm_apply, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp only [coeff_siteVec, ite_true]
    rw [Finsupp.sum_single_index (by simp)]
    by_cases h : x = y
    · subst h; simp
    · simp [h]
  · intro l _ hl; simp [coeff_siteVec, hl]
  · simp
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [coeff_siteVec, hk]
  · simp

/-- The matrix of an on-site form `Σ_x u(x)ᵀ B w(x)` on a region is block diagonal. -/
theorem restrictMatrix_liftForm (O : Finset G)
    (B : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    restrictMatrix O (liftForm B) = blockDiag O B := by
  classical
  ext a b
  simp only [restrictMatrix, regionVec, blockDiag, Matrix.of_apply, liftForm_siteVec,
    Subtype.coe_inj]

omit [AddCommGroup G] in
/-- Milestone Q3, Lemma 14(a): `P_O Ω_O P_Oᵀ = Ω_N`. -/
theorem blockDiag_symplecticForm (O : Finset G) :
    blockDiag O (Gaussian.symplecticForm n) = Gaussian.symplecticForm (n * O.card) := by
  ext a b
  obtain ⟨⟨x, i⟩, rfl⟩ := (regionEquiv O).surjective a
  obtain ⟨⟨y, j⟩, rfl⟩ := (regionEquiv O).surjective b
  rw [blockDiag_apply_equiv]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [regionEquiv, Gaussian.symplecticForm, Matrix.J, Matrix.one_apply, Prod.ext_iff] <;>
    by_cases h : x = y <;> simp [h]

/-- Milestone Q3, Lemma 14(a): the matrix of `σ` on a region is BosonicLean's `Ω`.
(notes: `lem:gs-reorder`) -/
theorem sigma_restrictMatrix (O : Finset G) :
    restrictMatrix O (sigma G n) = Gaussian.symplecticForm (n * O.card) := by
  rw [sigma, restrictMatrix_liftForm, blockDiag_symplecticForm]

theorem siteVec_mem_loc {O : Set G} {x : G} (hx : x ∈ O) (i : Gaussian.PhaseIndex n) :
    siteVec x i ∈ loc G n O := by
  intro z hz
  funext k
  simp only [LatticeSpace.valueAt_apply, Pi.zero_apply]
  rw [coeff_siteVec]
  split_ifs
  · simp [show x ≠ z from fun h => hz (h ▸ hx)]
  · rfl

theorem regionVec_mem (O : Finset G) (a : Gaussian.PhaseIndex (n * O.card)) :
    regionVec O a ∈ loc G n (O : Set G) :=
  siteVec_mem_loc (Finset.mem_coe.2 ((regionEquiv O).symm a).1.2) _

/-- The coordinates of a vector in the site vectors of a region. (notes: `lem:gs-reorder`) -/
noncomputable def regionCoords (O : Finset G) (w : PhaseVec G n)
    (a : Gaussian.PhaseIndex (n * O.card)) : ℝ :=
  (w ((regionEquiv O).symm a).2).coeff ((regionEquiv O).symm a).1

theorem coeff_sum_regionCoords [DecidableEq G] (O : Finset G) (w : PhaseVec G n)
    (k : Gaussian.PhaseIndex n)
    (z : G) : ((∑ a, regionCoords O w a • regionVec O a) k).coeff z =
      if z ∈ O then (w k).coeff z else 0 := by
  rw [← (regionEquiv O).sum_comp]
  simp only [regionCoords, regionVec, Equiv.symm_apply_apply]
  rw [Finset.sum_apply, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp only [Pi.smul_apply, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, coeff_siteVec,
    smul_eq_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_eq_single k]
  · simp only [ite_true]
    by_cases hz : z ∈ O
    · rw [Finset.sum_eq_single ⟨z, hz⟩, ite_eq_left_of_eq_true _ _ (eq_true hz)]
      · simp
      · intro y _ hy
        simp [show (y : G) ≠ z from fun h => hy (Subtype.ext h)]
      · simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hz)]
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [show (y : G) ≠ z from fun h => hz (h ▸ y.2)]
  · intro j _ hj
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [Ne.symm hj]
  · simp

/-- Milestone Q3, Lemma 14(c): a vector supported in `O` is the combination of the site vectors
with its coordinates. (notes: `lem:gs-reorder`) -/
theorem sum_regionCoords (O : Finset G) {w : PhaseVec G n} (hw : w ∈ loc G n (O : Set G)) :
    ∑ a, regionCoords O w a • regionVec O a = w := by
  classical
  funext k
  refine AddMonoidAlgebra.ext (Finsupp.ext fun z => ?_)
  rw [coeff_sum_regionCoords]
  split_ifs with hz
  · rfl
  · have h0 := congrFun (hw z (by simpa using hz)) k
    simp only [LatticeSpace.valueAt_apply, Pi.zero_apply] at h0
    exact h0.symm

/-- The matrix of `γ + iσ'` on the site vectors of a region is positive semidefinite exactly when
the pair form holds on the vectors supported in the region. -/
theorem posSemidef_region_iff (O : Finset G) {γ σ' : LinearMap.BilinForm ℝ (PhaseVec G n)}
    (hγ : γ.IsSymm) (hσ : σ'.IsAlt) :
    (Matrix.of fun a b => (γ (regionVec O a) (regionVec O b) : ℂ) +
        Complex.I * (σ' (regionVec O a) (regionVec O b) : ℂ)).PosSemidef ↔
      ∀ u ∈ loc G n (O : Set G), ∀ w ∈ loc G n (O : Set G), 2 * σ' u w ≤ γ u u + γ w w := by
  constructor
  · intro h u hu w hw
    have h2 := (posSemidef_iff_dotProduct_mulVec.1 h).2
      (fun a => (regionCoords O u a : ℂ) + Complex.I * (regionCoords O w a : ℂ))
    rw [star_dotProduct_mulVec_eq] at h2
    simp only [Matrix.of_apply] at h2
    rw [sum_conj_mul_stateMatrix hγ hσ, Complex.zero_le_real] at h2
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.add_im, Complex.mul_im, zero_mul, mul_zero, sub_zero,
      add_zero, one_mul, zero_add, sum_regionCoords O hu, sum_regionCoords O hw] at h2
    linarith
  · intro h
    refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_stateMatrix hγ hσ _) fun c => ?_
    rw [star_dotProduct_mulVec_eq]
    simp only [Matrix.of_apply]
    rw [sum_conj_mul_stateMatrix hγ hσ, Complex.zero_le_real]
    have hmem : ∀ x : Gaussian.PhaseIndex (n * O.card) → ℝ,
        ∑ k, x k • regionVec O k ∈ loc G n (O : Set G) := fun x =>
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (regionVec_mem O k)
    linarith [h _ (hmem fun k => (c k).re) _ (hmem fun k => (c k).im)]

/-- The state condition on a region in pair form, for either sign of `σ`. -/
theorem isStateConditionOn_iff_pair {O : Finset G} {γ : LinearMap.BilinForm ℝ (PhaseVec G n)}
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    IsStateConditionOn O γ ↔ ∀ u ∈ loc G n (O : Set G), ∀ w ∈ loc G n (O : Set G),
      2 * (s • sigma G n) u w ≤ γ u u + γ w w := by
  have hsq : ∀ u w, ((s • sigma G n) u w) ^ 2 = sigma G n u w ^ 2 := fun u w => by
    rcases hs with rfl | rfl <;> simp
  constructor
  · rintro ⟨hpos, h⟩ a ha b hb
    have h1 := hpos a ha
    have h2 := hpos b hb
    have hab := h a ha b hb
    rw [← hsq] at hab
    nlinarith [sq_nonneg (γ a a - γ b b), sq_nonneg (2 * (s • sigma G n) a b - (γ a a + γ b b))]
  · intro h
    have hpos : ∀ u ∈ loc G n (O : Set G), 0 ≤ γ u u := fun u hu => by
      simpa using h u hu 0 (Submodule.zero_mem _)
    refine ⟨hpos, fun u hu w hw => ?_⟩
    have hq : ∀ t : ℝ, 0 ≤ γ u u * (t * t) + (-2 * (s • sigma G n) u w) * t + γ w w := by
      intro t
      have := h (t • u) (Submodule.smul_mem _ _ hu) w hw
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this ⊢
      linear_combination this
    have := discrim_le_zero hq
    rw [discrim] at this
    rw [← hsq]
    linear_combination this / 4

theorem restrictMatrix_transpose (O : Finset G) {γ : LinearMap.BilinForm ℝ (PhaseVec G n)}
    (hγ : γ.IsSymm) : (restrictMatrix O γ)ᵀ = restrictMatrix O γ := by
  ext a b
  simp [restrictMatrix, hγ.eq (regionVec O b)]

/-- The state condition on a region is admissibility of the reordered site matrix. -/
theorem isStateConditionOn_iff_isAdmissible_restrictMatrix (O : Finset G)
    {γ : LinearMap.BilinForm ℝ (PhaseVec G n)} (hγ : γ.IsSymm) :
    IsStateConditionOn O γ ↔ Gaussian.IsAdmissible (restrictMatrix O γ) := by
  have hσ : ((-1 : ℝ) • sigma G n).IsAlt := fun x => by simp [sigma_isAlt G n x]
  rw [isStateConditionOn_iff_pair (-1) (Or.inr rfl), ← posSemidef_region_iff O hγ hσ,
    Gaussian.IsAdmissible, ← sigma_restrictMatrix O]
  simp only [restrictMatrix_transpose O hγ, true_and]
  congr! 1
  ext a b
  simp [restrictMatrix]
  ring

/-- Congruence by `Ω` preserves admissibility in both directions. -/
theorem isAdmissible_congr_symplecticForm {m : ℕ}
    {A : Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex m) ℝ} :
    Gaussian.IsAdmissible ((Gaussian.symplecticForm m)ᵀ * A * Gaussian.symplecticForm m) ↔
      Gaussian.IsAdmissible A := by
  constructor
  · intro h
    have := Gaussian.isAdmissible_symplecticCongruence h (S := Gaussian.symplecticForm m)
      (by rw [Gaussian.symplecticForm_sq _, Matrix.neg_mul, Matrix.one_mul,
        Gaussian.transpose_symplecticForm, neg_neg])
    have e : Gaussian.symplecticForm m * ((Gaussian.symplecticForm m)ᵀ * A *
        Gaussian.symplecticForm m) * (Gaussian.symplecticForm m)ᵀ = A := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Gaussian.symplecticForm_mul_transpose_self,
        Matrix.one_mul, Matrix.mul_assoc, Gaussian.symplecticForm_mul_transpose_self,
        Matrix.mul_one]
    rwa [e] at this
  · intro h
    have := Gaussian.isAdmissible_symplecticCongruence h (S := (Gaussian.symplecticForm m)ᵀ)
      (by rw [Matrix.transpose_transpose, Gaussian.transpose_symplecticForm_mul_self,
        Matrix.one_mul])
    simpa using this

/-- Milestone Q3, Proposition 15: a symmetric form satisfies the state condition on a finite
region exactly when its covariance matrix is admissible in BosonicLean's sense.
(notes: `prop:gs-admissible`) -/
theorem isAdmissible_covarianceMatrix_iff (O : Finset G)
    {γ : LinearMap.BilinForm ℝ (PhaseVec G n)} (hγ : γ.IsSymm) :
    IsStateConditionOn O γ ↔ Gaussian.IsAdmissible (covarianceMatrix O γ) := by
  rw [isStateConditionOn_iff_isAdmissible_restrictMatrix O hγ, covarianceMatrix,
    isAdmissible_congr_symplecticForm]

/-- The state condition on `V` implies it on every region. -/
theorem _root_.BosonicLean.Weyl.IsStateCondition.isStateConditionOn
    {γ : LinearMap.BilinForm ℝ (PhaseVec G n)}
    (h : IsStateCondition γ (sigma G n)) (O : Finset G) : IsStateConditionOn O γ :=
  ⟨fun u _ => h.1 u, fun u _ w _ => h.2 u w⟩

/-- Milestone Q3, Proposition 15: the covariance form of a Gaussian state restricts on every
finite region to an admissible covariance matrix of `n|O|` modes. (notes: `prop:gs-admissible`) -/
theorem _root_.BosonicLean.Weyl.GaussianState.isAdmissible_covarianceMatrix
    (ω : GaussianState (sigma G n))
    (O : Finset G) : Gaussian.IsAdmissible (covarianceMatrix O ω.cov) :=
  (isAdmissible_covarianceMatrix_iff O ω.isSymm).1
    ((ω.isStateCondition (sigma_isAlt G n)).isStateConditionOn O)

/-- Milestone Q3, Corollary 16(a): the state condition passes to sub-regions.
(notes: `cor:gs-regions`) -/
theorem IsStateConditionOn.mono {O O' : Finset G} (hO : O' ⊆ O)
    {γ : LinearMap.BilinForm ℝ (PhaseVec G n)} (h : IsStateConditionOn O γ) :
    IsStateConditionOn O' γ := by
  have hle := (loc G n).monotone (Finset.coe_subset.2 hO)
  exact ⟨fun u hu => h.1 u (hle hu), fun u hu w hw => h.2 u (hle hu) w (hle hw)⟩

/-- A vector supported in `O₁ ∪ O₂` with `O₁, O₂` disjoint splits into parts supported in each. -/
theorem exists_split_loc [DecidableEq G] {O₁ O₂ : Finset G} {v : PhaseVec G n}
    (hv : v ∈ loc G n ((O₁ ∪ O₂ : Finset G) : Set G)) :
    ∃ v₁ ∈ loc G n (O₁ : Set G), ∃ v₂ ∈ loc G n (O₂ : Set G), v = v₁ + v₂ := by
  set v₁ := ∑ a, regionCoords O₁ v a • regionVec O₁ a
  have h₁ : v₁ ∈ loc G n (O₁ : Set G) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (regionVec_mem O₁ k)
  refine ⟨v₁, h₁, v - v₁, ?_, by abel⟩
  intro z hz
  funext k
  simp only [LatticeSpace.valueAt_apply, Pi.sub_apply, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, Pi.zero_apply, v₁, coeff_sum_regionCoords]
  split_ifs with h
  · exact sub_self _
  · have h0 := congrFun (hv z (by simp_all)) k
    simp only [LatticeSpace.valueAt_apply, Pi.zero_apply] at h0
    rw [h0, sub_zero]

/-- Milestone Q3, Corollary 16(b): for a form without correlations between disjoint regions
`O₁` and `O₂`, the state condition on `O₁ ∪ O₂` is the state condition on both.
(notes: `cor:gs-regions`) -/
theorem isStateConditionOn_union_iff [DecidableEq G] {O₁ O₂ : Finset G} (hd : Disjoint O₁ O₂)
    {γ : LinearMap.BilinForm ℝ (PhaseVec G n)} (hγ : γ.IsSymm)
    (hprod : ∀ u ∈ loc G n (O₁ : Set G), ∀ w ∈ loc G n (O₂ : Set G), γ u w = 0) :
    IsStateConditionOn (O₁ ∪ O₂) γ ↔ IsStateConditionOn O₁ γ ∧ IsStateConditionOn O₂ γ := by
  refine ⟨fun h => ⟨h.mono Finset.subset_union_left, h.mono Finset.subset_union_right⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  rw [isStateConditionOn_iff_pair 1 (Or.inl rfl)] at h₁ h₂ ⊢
  simp only [one_smul] at h₁ h₂ ⊢
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_split_loc ha
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_split_loc hb
  have hdj : Disjoint (O₁ : Set G) (O₂ : Set G) := Finset.disjoint_coe.2 hd
  have s1 := sigma_eq_zero_of_disjoint hdj ha₁ hb₂
  have s2 := sigma_eq_zero_of_disjoint hdj.symm ha₂ hb₁
  have g1 := hprod a₁ ha₁ a₂ ha₂
  have g2 := hprod b₁ hb₁ b₂ hb₂
  have g1' : γ a₂ a₁ = 0 := by rw [hγ.eq]; exact g1
  have g2' : γ b₂ b₁ = 0 := by rw [hγ.eq]; exact g2
  simp only [map_add, LinearMap.add_apply, s1, s2, g1, g2, g1', g2']
  linarith [h₁ a₁ ha₁ b₁ hb₁, h₂ a₂ ha₂ b₂ hb₂]

/-- Milestone Q3, Remark 17: under the state condition on `O`, `γ` is positive definite on the
vectors supported in `O` (through BosonicLean's `IsAdmissible.posDef`). (notes: `rem:gs-posdef`) -/
theorem IsStateConditionOn.pos {O : Finset G} {γ : LinearMap.BilinForm ℝ (PhaseVec G n)}
    (hγ : γ.IsSymm) (h : IsStateConditionOn O γ) {u : PhaseVec G n}
    (hu : u ∈ loc G n (O : Set G)) (hu0 : u ≠ 0) : 0 < γ u u := by
  have hpd := ((isStateConditionOn_iff_isAdmissible_restrictMatrix O hγ).1 h).posDef
  have hξ : regionCoords O u ≠ 0 := by
    intro h0
    apply hu0
    rw [← sum_regionCoords O hu, h0]
    simp
  have := hpd.dotProduct_mulVec_pos hξ
  rw [← sum_regionCoords O hu, bilin_sum_sum]
  rw [star_trivial] at this
  refine this.trans_eq ?_
  simp only [dotProduct, Matrix.mulVec, restrictMatrix, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end Region

/-! ### On-site forms, the vacuum and the squeezed states -/

section Examples

variable {G : Type*} [AddCommGroup G] {n : ℕ}

theorem starTranspose_const (B : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    starTranspose (const G B) = const G Bᵀ := by
  ext i j
  simp [starTranspose, const, Matrix.transpose_apply, Matrix.map_apply]

variable (G) in
/-- The on-site rule `(L_S u)(x) = S u(x)`, as a real-linear map. (notes: `cor:gs-onsite`) -/
noncomputable def onSite (S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    PhaseVec G n →ₗ[ℝ] PhaseVec G n :=
  (Matrix.toLin' (const G S)).restrictScalars ℝ

theorem liftForm_comp_onSite (B S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    (liftForm B).comp (onSite G S) (onSite G S) = liftForm (Sᵀ * B * S) := by
  refine LinearMap.ext₂ fun u w => ?_
  simp only [LinearMap.BilinForm.comp_apply, onSite, LinearMap.restrictScalars_apply]
  rw [liftForm, pairing_toLin', starTranspose_const, liftForm, const_mul, const_mul]

/-- Milestone Q4a, Proposition 3(a): an on-site symplectic matrix gives a symplectic rule.
(notes: `prop:es-iterate`) -/
theorem isSymplectic_const {S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hS : Sᵀ * Gaussian.symplecticForm n * S = Gaussian.symplecticForm n) :
    IsSymplectic (const ℤ S) := by
  rw [IsSymplectic, starTranspose_const, ← const_mul, ← const_mul, hS]

/-- Milestone Q4a, Proposition 3(b): the evolution by an on-site rule acts on the covariance form
by the on-site congruence. -/
theorem _root_.BosonicLean.Weyl.GaussianState.evolve_cov_const
    {S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hS : Sᵀ * Gaussian.symplecticForm n * S = Gaussian.symplecticForm n)
    (ω : GaussianState (sigma ℤ n)) :
    (ω.evolve (isSymplectic_const hS)).cov = ω.cov.compl₁₂ (onSite ℤ S) (onSite ℤ S) :=
  LinearMap.ext₂ fun _ _ => rfl

/-- The on-site form in site coordinates, `Σ_{x ∈ T} u(x)ᵀ B w(x)`. -/
theorem liftForm_eq_sum_sites (B : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (u w : PhaseVec G n) (T : Finset G) (hT : ∀ i, (u i).coeff.support ⊆ T) :
    liftForm B u w = ∑ x ∈ T, ∑ i, ∑ j, (u i).coeff x * B i j * (w j).coeff x := by
  rw [liftForm_apply]
  calc _ = ∑ i, ∑ j, ∑ x ∈ T, (u i).coeff x * B i j * (w j).coeff x := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finsupp.sum_of_support_subset _ (hT i) _ (fun _ _ => by simp), Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ i, ∑ x ∈ T, ∑ j, (u i).coeff x * B i j * (w j).coeff x :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The pair form for an on-site form follows from the pair form of one cell. -/
theorem isStateConditionPair_liftForm
    (B : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (hB : ∀ a b : Gaussian.PhaseIndex n → ℝ,
      2 * ∑ i, ∑ j, a i * Gaussian.symplecticForm n i j * b j ≤
        ∑ i, ∑ j, a i * B i j * a j + ∑ i, ∑ j, b i * B i j * b j) :
    IsStateConditionPair (liftForm (G := G) B) (sigma G n) := by
  classical
  intro a b
  set T := Finset.univ.biUnion (fun i => (a i).coeff.support) ∪
    Finset.univ.biUnion (fun i => (b i).coeff.support)
  have ha : ∀ i, (a i).coeff.support ⊆ T := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => (a i).coeff.support) (Finset.mem_univ i)).trans
      Finset.subset_union_left
  have hb : ∀ i, (b i).coeff.support ⊆ T := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => (b i).coeff.support) (Finset.mem_univ i)).trans
      Finset.subset_union_right
  rw [sigma, liftForm_eq_sum_sites _ _ _ T ha, liftForm_eq_sum_sites _ _ _ T ha,
    liftForm_eq_sum_sites _ _ _ T hb, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => hB (fun i => (a i).coeff x) (fun i => (b i).coeff x)

/-- Milestone Q3, Example 18: the vacuum form `γ(u,w) = Σ_x u(x)ᵀ w(x)`. (notes: `ex:gs-vacuum`) -/
noncomputable def vacuumCov : LinearMap.BilinForm ℝ (PhaseVec G n) := liftForm 1

theorem symplecticForm_quad (a b : Gaussian.PhaseIndex n → ℝ) :
    ∑ i, ∑ j, a i * Gaussian.symplecticForm n i j * b j =
      ∑ r, (a (Sum.inl r) * b (Sum.inr r) - a (Sum.inr r) * b (Sum.inl r)) := by
  simp [Gaussian.symplecticForm, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply,
    Finset.sum_sub_distrib]
  ring

/-- Milestone Q3, Example 18: the vacuum form satisfies the state condition.
(notes: `ex:gs-vacuum`) -/
theorem isStateCondition_vacuum : IsStateCondition (vacuumCov (G := G) (n := n)) (sigma G n) := by
  refine isStateConditionPair_iff.1 (isStateConditionPair_liftForm _ fun a b => ?_)
  have q1 : ∀ c : Gaussian.PhaseIndex n → ℝ,
      ∑ i, ∑ j, c i * (1 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) i j * c j =
        ∑ r, (c (Sum.inl r) ^ 2 + c (Sum.inr r) ^ 2) := by
    intro c
    simp [Matrix.one_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, sq]
  rw [symplecticForm_quad, q1, q1, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  nlinarith [sq_nonneg (a (Sum.inl r) - b (Sum.inr r)), sq_nonneg (a (Sum.inr r) + b (Sum.inl r))]

/-- Milestone Q3, Example 19: the squeezed form with cell `diag(1/t, t)` (one mode per site).
(notes: `ex:gs-squeezed`) -/
noncomputable def squeezedCov (t : ℝ) : LinearMap.BilinForm ℝ (PhaseVec G 1) :=
  liftForm (Gaussian.diagonalOne t⁻¹ t)

/-- Milestone Q3, Example 19: the squeezed form satisfies the state condition.
(notes: `ex:gs-squeezed`) -/
theorem isStateCondition_squeezed {t : ℝ} (ht : 0 < t) :
    IsStateCondition (squeezedCov (G := G) t) (sigma G 1) := by
  refine isStateConditionPair_iff.1 (isStateConditionPair_liftForm _ fun a b => ?_)
  rw [symplecticForm_quad]
  simp only [Gaussian.diagonalOne, Matrix.diagonal_apply, mul_ite, mul_zero,
    Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr,
    Fin.default_eq_zero, ite_true, reduceCtorEq, ite_false]
  have hu0 : 0 ≤ t⁻¹ := (inv_pos.2 ht).le
  have e1 : a (Sum.inl 0) * t⁻¹ * a (Sum.inl 0) + b (Sum.inr 0) * t * b (Sum.inr 0) -
      2 * (a (Sum.inl 0) * b (Sum.inr 0)) = t⁻¹ * (a (Sum.inl 0) - t * b (Sum.inr 0)) ^ 2 := by
    field_simp; ring
  have e2 : b (Sum.inl 0) * t⁻¹ * b (Sum.inl 0) + a (Sum.inr 0) * t * a (Sum.inr 0) +
      2 * (a (Sum.inr 0) * b (Sum.inl 0)) = t⁻¹ * (b (Sum.inl 0) + t * a (Sum.inr 0)) ^ 2 := by
    field_simp; ring
  nlinarith [mul_nonneg hu0 (sq_nonneg (a (Sum.inl 0) - t * b (Sum.inr 0))),
    mul_nonneg hu0 (sq_nonneg (b (Sum.inl 0) + t * a (Sum.inr 0)))]

/-- Milestone Q3, Example 29: an on-site rotation preserves the vacuum form.
(notes: `ex:gs-rotation`) -/
theorem vacuum_rotation (φ : ℝ) :
    (vacuumCov (G := G) (n := 1)).comp (onSite G (rotation φ)) (onSite G (rotation φ)) =
      vacuumCov := by
  rw [vacuumCov, liftForm_comp_onSite, Matrix.mul_one]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fintype.sum_sum_type] <;>
    nlinarith [Real.sin_sq_add_cos_sq φ]


/-- The covariance matrix of an on-site form is block diagonal with the block `Ωᵀ B Ω`. -/
theorem covarianceMatrix_liftForm (O : Finset G)
    (B : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    covarianceMatrix O (liftForm B) =
      blockDiag O ((Gaussian.symplecticForm n)ᵀ * B * Gaussian.symplecticForm n) := by
  rw [covarianceMatrix, restrictMatrix_liftForm, ← blockDiag_symplecticForm, blockDiag_transpose,
    blockDiag_mul, blockDiag_mul]

/-- Milestone Q3, Example 18: the covariance matrix of the vacuum is `1` on every region.
(notes: `ex:gs-vacuum`) -/
theorem covarianceMatrix_vacuum (O : Finset G) :
    covarianceMatrix O (vacuumCov (n := n)) = 1 := by
  rw [vacuumCov, covarianceMatrix_liftForm, Matrix.mul_one,
    Gaussian.transpose_symplecticForm_mul_self, blockDiag_one]

/-- The single site `x` as a mode map into the region `{x}`. -/
noncomputable def siteMode (x : G) (i : Gaussian.PhaseIndex n) :
    Gaussian.PhaseIndex (n * ({x} : Finset G).card) :=
  regionEquiv {x} (⟨x, Finset.mem_singleton_self x⟩, i)

omit [AddCommGroup G] in
theorem blockDiag_single (x : G) (X : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    (blockDiag {x} X).submatrix (siteMode x) (siteMode x) = X := by
  ext i j
  simp [siteMode, blockDiag_apply_equiv]

/-- Milestone Q3, Lemma 14(d): `Ωᵀ diag(α, β) Ω = diag(β, α)` for one mode.
(notes: `lem:gs-reorder`) -/
theorem symplecticForm_conj_diagonalOne (α β : ℝ) :
    (Gaussian.symplecticForm 1)ᵀ * Gaussian.diagonalOne α β * Gaussian.symplecticForm 1 =
      Gaussian.diagonalOne β α := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Gaussian.symplecticForm, Gaussian.diagonalOne, Matrix.J, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.diagonal_apply]

/-- Milestone Q3, Example 18: on one site with one mode the vacuum is BosonicLean's
`diagonalOne 1 1`. (notes: `ex:gs-vacuum`) -/
theorem covarianceMatrix_vacuum_single (x : G) :
    (covarianceMatrix {x} (vacuumCov (n := 1))).submatrix (siteMode x) (siteMode x) =
      Gaussian.diagonalOne 1 1 := by
  rw [vacuumCov, covarianceMatrix_liftForm, blockDiag_single, Matrix.mul_one,
    Gaussian.transpose_symplecticForm_mul_self]
  ext i j
  simp [Gaussian.diagonalOne, Matrix.one_apply, Matrix.diagonal_apply]

/-- Milestone Q3, Example 19: on one site the squeezed form has BosonicLean's covariance
`diagonalOne t t⁻¹`, which is admissible. (notes: `ex:gs-squeezed`) -/
theorem covarianceMatrix_squeezed_single (x : G) (t : ℝ) :
    (covarianceMatrix {x} (squeezedCov t)).submatrix (siteMode x) (siteMode x) =
      Gaussian.diagonalOne t t⁻¹ := by
  rw [squeezedCov, covarianceMatrix_liftForm, blockDiag_single, symplecticForm_conj_diagonalOne]

theorem inv_eq_of_symplectic {S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hS : Sᵀ * Gaussian.symplecticForm n * S = Gaussian.symplecticForm n) :
    S⁻¹ = (Gaussian.symplecticForm n)ᵀ * Sᵀ * Gaussian.symplecticForm n := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Sᵀ, hS,
    Gaussian.transpose_symplecticForm_mul_self]

theorem onSite_siteVec (S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) (x : G)
    (i : Gaussian.PhaseIndex n) : onSite G S (siteVec x i) = ∑ k, S k i • siteVec x k := by
  funext l
  rw [Finset.sum_apply, Finset.sum_eq_single l]
  · simp [onSite, siteVec, Matrix.mulVec_single, const, Algebra.smul_def,
      MulOpposite.smul_eq_mul_unop]
  · intro j _ hj; simp [siteVec, Ne.symm hj]
  · simp

theorem onSite_regionVec (O : Finset G)
    (S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (a : Gaussian.PhaseIndex (n * O.card)) :
    onSite G S (regionVec O a) = ∑ b, blockDiag O S b a • regionVec O b := by
  obtain ⟨⟨x, i⟩, rfl⟩ := (regionEquiv O).surjective a
  rw [← (regionEquiv O).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp [blockDiag_apply_equiv, regionVec, onSite_siteVec]
  · intro y _ hy
    exact Finset.sum_eq_zero fun k _ => by simp [blockDiag_apply_equiv, hy]
  · simp

theorem restrictMatrix_comp_onSite (O : Finset G) (γ : LinearMap.BilinForm ℝ (PhaseVec G n))
    (S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    restrictMatrix O (γ.comp (onSite G S) (onSite G S)) =
      (blockDiag O S)ᵀ * restrictMatrix O γ * blockDiag O S := by
  ext a b
  simp only [restrictMatrix, Matrix.of_apply, LinearMap.BilinForm.comp_apply, onSite_regionVec,
    bilin_sum_sum, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- Milestone Q3, Corollary 28: an on-site symplectic `S` moves the covariance matrix by the
congruence with `T = P_O (1_O ⊗ S⁻¹) P_Oᵀ`. (notes: `cor:gs-onsite`) -/
theorem covarianceMatrix_onSite (O : Finset G) (γ : LinearMap.BilinForm ℝ (PhaseVec G n))
    {S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hS : Sᵀ * Gaussian.symplecticForm n * S = Gaussian.symplecticForm n) :
    covarianceMatrix O (γ.comp (onSite G S) (onSite G S)) =
      blockDiag O S⁻¹ * covarianceMatrix O γ * (blockDiag O S⁻¹)ᵀ := by
  set Ω := Gaussian.symplecticForm (n * O.card)
  have hΩ : Ω * Ωᵀ = 1 := Gaussian.symplecticForm_mul_transpose_self _
  have h1 : blockDiag O S⁻¹ = Ωᵀ * (blockDiag O S)ᵀ * Ω := by
    rw [inv_eq_of_symplectic hS, ← blockDiag_mul, ← blockDiag_mul, ← blockDiag_transpose,
      ← blockDiag_transpose, blockDiag_symplecticForm]
  rw [covarianceMatrix, covarianceMatrix, restrictMatrix_comp_onSite, h1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Ω Ωᵀ, hΩ, Matrix.one_mul, ← Matrix.mul_assoc Ω Ωᵀ, hΩ, Matrix.one_mul]

/-- Milestone Q3, Corollary 28: on-site symplectic evolution preserves the state condition on a
region. (notes: `cor:gs-onsite`) -/
theorem IsStateConditionOn.comp_onSite {O : Finset G}
    {S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hS : Sᵀ * Gaussian.symplecticForm n * S = Gaussian.symplecticForm n)
    {γ : LinearMap.BilinForm ℝ (PhaseVec G n)} (hγ : γ.IsSymm) (h : IsStateConditionOn O γ) :
    IsStateConditionOn O (γ.comp (onSite G S) (onSite G S)) := by
  have hγ' : (γ.comp (onSite G S) (onSite G S)).IsSymm := ⟨fun u w => hγ.eq _ _⟩
  rw [isAdmissible_covarianceMatrix_iff O hγ', covarianceMatrix_onSite O γ hS]
  refine Gaussian.isAdmissible_symplecticCongruence
    ((isAdmissible_covarianceMatrix_iff O hγ).1 h) ?_
  have hinv : S⁻¹ * Gaussian.symplecticForm n * (S⁻¹)ᵀ = Gaussian.symplecticForm n := by
    rw [inv_eq_of_symplectic hS]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Gaussian.symplecticForm n) (Gaussian.symplecticForm n)ᵀ,
      Gaussian.symplecticForm_mul_transpose_self, Matrix.one_mul,
      ← Matrix.mul_assoc (Gaussian.symplecticForm n) S, ← Matrix.mul_assoc Sᵀ,
      ← Matrix.mul_assoc Sᵀ, hS, ← Matrix.mul_assoc,
      Gaussian.transpose_symplecticForm_mul_self, Matrix.one_mul]
  rw [← blockDiag_symplecticForm, blockDiag_transpose, blockDiag_mul, blockDiag_mul, hinv]

end Examples

/-! ### Purity -/

section Purity

theorem map_symplecticForm_one :
    (Gaussian.symplecticForm 1).map Complex.ofReal = (omega : Matrix Cell Cell ℂ) := by
  apply cell_ext <;> simp [← omega_real]

/-- The real data of a Hermitian `2 × 2` matrix `[[a, c], [conj c, b]]`. -/
theorem hermitian_cell_entries {A : Matrix Cell Cell ℂ} (hA : A.IsHermitian) :
    A qIdx qIdx = ((A qIdx qIdx).re : ℂ) ∧ A pIdx pIdx = ((A pIdx pIdx).re : ℂ) ∧
      A pIdx qIdx = conj (A qIdx pIdx) := by
  have h1 := hA.apply qIdx qIdx
  have h2 := hA.apply pIdx pIdx
  have h3 := hA.apply pIdx qIdx
  simp only [Complex.star_def] at h1 h2 h3
  refine ⟨?_, ?_, h3.symm⟩
  · conv_lhs => rw [← h1]
    exact (Complex.conj_eq_iff_re.1 h1).symm ▸ by rw [h1]
  · conv_lhs => rw [← h2]
    exact (Complex.conj_eq_iff_re.1 h2).symm ▸ by rw [h2]

/-- `det(A ± iΩ) = det A − 1 ∓ 2 Im c` (Milestone Q3, Lemma 25, equation (7)). -/
theorem det_add_I_omega {A : Matrix Cell Cell ℂ} (hA : A.IsHermitian) (s : ℝ) :
    (A + ((s : ℂ) * Complex.I) • (omega : Matrix Cell Cell ℂ)).det =
      A.det - (s : ℂ) ^ 2 - 2 * s * (A qIdx pIdx).im := by
  obtain ⟨-, -, h3⟩ := hermitian_cell_entries hA
  rw [← det2_eq_det, ← det2_eq_det]
  simp only [det2, Matrix.add_apply, Matrix.smul_apply, omega_qq, omega_qp, omega_pq, omega_pp,
    smul_eq_mul, mul_zero, add_zero, mul_one, mul_neg, h3]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, sq] <;> ring

/-- Milestone Q3, Lemma 25: for a Hermitian `2 × 2` matrix `A` with `A ± iΩ ≥ 0`,
`det A ≥ 1 + 2 |Im c|`. (notes: `lem:gs-twobytwo`) -/
theorem det_bound_twoByTwo {A : Matrix Cell Cell ℂ} (hA : A.IsHermitian)
    (hp : (A + Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef)
    (hm : (A - Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef) :
    A.det.im = 0 ∧ 1 + 2 * |(A qIdx pIdx).im| ≤ A.det.re := by
  rw [map_symplecticForm_one] at hp hm
  have dp := hp.det_nonneg
  have dm := hm.det_nonneg
  have ep := det_add_I_omega hA 1
  have em := det_add_I_omega hA (-1)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_mul, neg_smul,
    ← sub_eq_add_neg] at ep em
  rw [ep] at dp
  rw [em] at dm
  obtain ⟨hp1, hp2⟩ := Complex.nonneg_iff.1 dp
  obtain ⟨hm1, hm2⟩ := Complex.nonneg_iff.1 dm
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im] at hp1 hp2 hm1 hm2
  norm_num at hp1 hp2 hm1 hm2
  refine ⟨by linarith, ?_⟩
  rcases abs_cases (A qIdx pIdx).im with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- Milestone Q3, Lemma 25 (a) ⇔ (b): `(ΩA)² = −1` exactly when `det A = 1`.
(notes: `lem:gs-twobytwo`) -/
theorem purity_twoByTwo {A : Matrix Cell Cell ℂ} (hA : A.IsHermitian)
    (hp : (A + Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef)
    (hm : (A - Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef) :
    ((Gaussian.symplecticForm 1).map Complex.ofReal * A) ^ 2 = -1 ↔ A.det = 1 := by
  obtain ⟨him, hbd⟩ := det_bound_twoByTwo hA hp hm
  obtain ⟨h1, h2, h3⟩ := hermitian_cell_entries hA
  rw [map_symplecticForm_one, ← det2_eq_det] at *
  set a := (A qIdx qIdx).re
  set b := (A pIdx pIdx).re
  set x := (A qIdx pIdx).re
  set y := (A qIdx pIdx).im
  have hc : A qIdx pIdx = (x : ℂ) + (y : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have hdet : det2 A = ((a * b - x ^ 2 - y ^ 2 : ℝ) : ℂ) := by
    rw [det2, h1, h2, h3, hc]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sq] <;> ring
  rw [hdet, Complex.ofReal_re] at hbd
  rw [hdet, ← Complex.ofReal_one, Complex.ofReal_inj]
  have hsq : ((omega : Matrix Cell Cell ℂ) * A) ^ 2 = -1 ↔
      (x ^ 2 - y ^ 2 - a * b = -1 ∧ x * y = 0) ∧ b * y = 0 ∧ a * y = 0 := by
    rw [sq]
    constructor
    · intro h
      have e1 := congrFun (congrFun h qIdx) qIdx
      have e2 := congrFun (congrFun h qIdx) pIdx
      have e3 := congrFun (congrFun h pIdx) qIdx
      simp only [mul_qq, mul_qp, mul_pq, mul_pp, omega_qq, omega_qp, omega_pq, omega_pp,
        zero_mul, one_mul, neg_mul, zero_add, add_zero, Matrix.neg_apply, one_qq, one_qp,
        one_pq, h1, h2, h3, hc] at e1 e2 e3
      rw [Complex.ext_iff] at e1 e2 e3
      simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I, mul_neg, Complex.add_re,
        Complex.mul_re, Complex.ofReal_re, Complex.neg_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero, add_zero, Complex.add_im,
        Complex.neg_im, Complex.mul_im, zero_add, neg_mul, neg_neg, sub_zero, Complex.one_re,
        zero_mul, Complex.one_im, neg_add_rev, Complex.zero_re, Complex.zero_im] at e1 e2 e3
      refine ⟨⟨by linarith [e1.1], by nlinarith [e1.2]⟩, by nlinarith [e2.2], by nlinarith [e3.2]⟩
    · rintro ⟨⟨e1, e2⟩, e3, e4⟩
      apply cell_ext <;>
        simp only [mul_qq, mul_qp, mul_pq, mul_pp, omega_qq, omega_qp, omega_pq, omega_pp,
          zero_mul, one_mul, neg_mul, zero_add, add_zero, Matrix.neg_apply, one_qq, one_qp,
          one_pq, one_pp, h1, h2, h3, hc] <;>
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith [e1, e2, e3, e4]
  rw [hsq]
  constructor
  · rintro ⟨⟨e1, _⟩, _, _⟩
    have hy : y = 0 := by
      rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hbd <;> nlinarith [sq_nonneg y]
    rw [hy] at e1 ⊢
    linarith
  · intro hd
    have hy : y = 0 := by
      rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hbd <;> linarith
    rw [hy] at hd ⊢
    refine ⟨⟨by linarith, by ring⟩, by ring, by ring⟩

/-- Milestone Q3, Lemma 25 (b) ⇔ (c): `det A = 1` exactly when `A ± iΩ` are both singular.
(notes: `lem:gs-twobytwo`) -/
theorem det_eq_one_iff_singular {A : Matrix Cell Cell ℂ} (hA : A.IsHermitian)
    (hp : (A + Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef)
    (hm : (A - Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef) :
    A.det = 1 ↔ (A + Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).det = 0 ∧
      (A - Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).det = 0 := by
  obtain ⟨him, hbd⟩ := det_bound_twoByTwo hA hp hm
  have ep := det_add_I_omega hA 1
  have em := det_add_I_omega hA (-1)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_mul, neg_smul,
    ← sub_eq_add_neg] at ep em
  rw [map_symplecticForm_one, ep, em]
  have hd : A.det = (A.det.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hd]
  constructor
  · intro h1
    have hre : A.det.re = 1 := by exact_mod_cast h1
    have hy : (A qIdx pIdx).im = 0 := by
      rcases abs_cases (A qIdx pIdx).im with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hbd <;> linarith
    rw [hre, hy]; constructor <;> push_cast <;> ring
  · rintro ⟨h1, h2⟩
    have e1 := congrArg Complex.re h1
    have e2 := congrArg Complex.re h2
    simp at e1 e2
    apply Complex.ext
    · simp only [Complex.ofReal_re, Complex.one_re]; linarith
    · simp

end Purity

section FourierSign

variable {n : ℕ}

/-- `γ̂(−k)ᵀ = γ̂(k)` for admissible cell data. -/
theorem gammaHat_neg_transpose
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (k : ℝ) : (gammaHat γc (-k))ᵀ = gammaHat γc k := by
  rw [gammaHat_neg h.summable]
  exact (gammaHat_isHermitian h k)

/-- Milestone Q3, Remark 24: `γ̂(k) − iΩ = (γ̂(−k) + iΩ)ᵀ`, so the criterion holds with either
sign. (notes: `rem:gs-minus`) -/
theorem gammaHat_sub_eq_transpose
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (k : ℝ) :
    gammaHat γc k - Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal =
      (gammaHat γc (-k) + Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal)ᵀ := by
  rw [Matrix.transpose_add, gammaHat_neg_transpose h, Matrix.transpose_smul,
    ← Matrix.transpose_map, Gaussian.transpose_symplecticForm, Matrix.map_neg _ Complex.ofReal_neg,
    smul_neg, sub_eq_add_neg]

/-- Milestone Q3, Remark 24: under the criterion, both `γ̂(k) ± iΩ` are positive semidefinite.
(notes: `rem:gs-minus`) -/
theorem gammaHat_sub_posSemidef
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (hk : ∀ k, (gammaHat γc k +
      Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal).PosSemidef) (k : ℝ) :
    (gammaHat γc k - Complex.I • (Gaussian.symplecticForm n).map Complex.ofReal).PosSemidef := by
  rw [gammaHat_sub_eq_transpose h]
  exact (hk (-k)).transpose

end FourierSign

/-- Milestone Q3, Corollary 26 (the matrix content of thesis Lemma 4.5(ii)): for one mode per
site and admissible cells with `γ̂(k) + iΩ ≥ 0`, `det γ̂(k) = 1` for all `k` exactly when
`(Ω γ̂(k))² = −1` for all `k`. (notes: `cor:gs-purity`) -/
theorem purity_fourier {γc : ℤ → Matrix Cell Cell ℝ} (h : CellData γc)
    (hk : ∀ k, (gammaHat γc k +
      Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef) :
    (∀ k, (gammaHat γc k).det = 1) ↔
      ∀ k, ((Gaussian.symplecticForm 1).map Complex.ofReal * gammaHat γc k) ^ 2 = -1 :=
  forall_congr' fun k => (purity_twoByTwo (gammaHat_isHermitian h k) (hk k)
    (gammaHat_sub_posSemidef h hk k)).symm

/-- Milestone Q3, Corollary 26: `det γ̂(k) = 1` for all `k` exactly when `γ̂(k) + iΩ` is singular
for all `k`. (notes: `cor:gs-purity`) -/
theorem purity_fourier_singular {γc : ℤ → Matrix Cell Cell ℝ} (h : CellData γc)
    (hk : ∀ k, (gammaHat γc k +
      Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).PosSemidef) :
    (∀ k, (gammaHat γc k).det = 1) ↔
      ∀ k, (gammaHat γc k +
        Complex.I • (Gaussian.symplecticForm 1).map Complex.ofReal).det = 0 := by
  have hm := gammaHat_sub_posSemidef h hk
  constructor
  · intro hd k
    exact ((det_eq_one_iff_singular (gammaHat_isHermitian h k) (hk k) (hm k)).1 (hd k)).1
  · intro hs k
    refine (det_eq_one_iff_singular (gammaHat_isHermitian h k) (hk k) (hm k)).2 ⟨hs k, ?_⟩
    rw [gammaHat_sub_eq_transpose h, Matrix.det_transpose]
    exact hs (-k)

end QCALean.Bosonic
