/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Core.Form
import BosonicLean.PhaseSpace.OneMode
import Mathlib.Algebra.Polynomial.Laurent

/-!
# One mode, nearest neighbour

Symplectic rules on a chain of single modes with nearest-neighbour coupling: symbols
`ℓ₋ z⁻¹ + ℓ₀ + ℓ₊ z` with real `2 × 2` coefficient matrices on BosonicLean's one-mode cell.
The symbol condition `L̂⋆ᵀ Ω L̂ = Ω` is equivalent to five matrix equations, the coefficients of
`z^{±2}, z^{±1}, z⁰` (`nn_symplectic_iff`, thesis (4.11)). From them, Milestone Q1,
Proposition 11 (thesis Prop. 4.4, corrected): a symplectic nearest-neighbour rule is either a pure
shift `S z^{±1}` with `S` symplectic, or has `ℓ₀` symplectic and `ℓ₊ = ℓ₋` singular (rank at most
one). The thesis omits the shifts.

## Main definitions and results

* `QCALean.Bosonic.mono k A`: the monomial symbol `z^k A`.
* `QCALean.Bosonic.nnSymbol ℓ₋ ℓ₀ ℓ₊`.
* `QCALean.Bosonic.nn_symplectic_iff`: the five coefficient equations.
* `QCALean.Bosonic.nn_symplectic`, `QCALean.Bosonic.shift_symplectic`,
  `QCALean.Bosonic.nn_symplectic_of_branch`: Proposition 11 and its converse.
-/

open Matrix LaurentPolynomial QCALean.Core Gaussian

namespace QCALean.Bosonic

/-- Laurent polynomials in one variable with real coefficients. -/
abbrev L := LaurentPolynomial ℝ

section Monomial

variable {ι : Type*}

/-- The monomial symbol `z^k A` of a real matrix. -/
noncomputable def mono (k : ℤ) (A : Matrix ι ι ℝ) : Matrix ι ι L :=
  (T k : L) • const ℤ A

theorem mono_zero_eq (A : Matrix ι ι ℝ) : mono 0 A = const ℤ A := by
  simp [mono, T_zero]

theorem mono_mul [Fintype ι] (a b : ℤ) (A B : Matrix ι ι ℝ) :
    mono a A * mono b B = mono (a + b) (A * B) := by
  simp only [mono, Matrix.smul_mul, Matrix.mul_smul, smul_smul, const_mul, T_add, mul_comm]

theorem T_eq_single (k : ℤ) : (T k : L) = AddMonoidAlgebra.single k 1 := rfl

theorem involution_T (k : ℤ) : involution ℝ ℤ (T k) = T (-k) := by
  rw [T_eq_single, involution_single, T_eq_single]

theorem starTranspose_mono (k : ℤ) (A : Matrix ι ι ℝ) :
    starTranspose (mono k A) = mono (-k) Aᵀ := by
  ext i j
  simp only [starTranspose, mono, const, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, map_mul, involution_T, AlgEquiv.commutes]

theorem starTranspose_add (A B : Matrix ι ι L) :
    starTranspose (A + B) = starTranspose A + starTranspose B := by
  ext i j
  simp [starTranspose]

theorem mono_add (k : ℤ) (A B : Matrix ι ι ℝ) : mono k (A + B) = mono k A + mono k B := by
  ext i j
  simp [mono, const, mul_add]

/-- The coefficient of an entry of a sum. -/
theorem entry_coeff_add (A B : Matrix ι ι L) (i j : ι) (m : ℤ) :
    ((A + B) i j).coeff m = (A i j).coeff m + (B i j).coeff m := rfl

/-- The coefficient of an entry of a monomial symbol. -/
theorem mono_coeff (k m : ℤ) (A : Matrix ι ι ℝ) (i j : ι) :
    (mono k A i j).coeff m = if k = m then A i j else 0 := by
  simp only [mono, const, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, T_eq_single,
    AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AddMonoidAlgebra.single_mul_single, add_zero, one_mul,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem mono_apply (k : ℤ) (A : Matrix ι ι ℝ) (i j : ι) :
    mono k A i j = AddMonoidAlgebra.single k (A i j) := by
  simp only [mono, const, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, T_eq_single,
    AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AddMonoidAlgebra.single_mul_single, add_zero, one_mul]

theorem mono_zero (k : ℤ) : mono k (0 : Matrix ι ι ℝ) = 0 := by
  ext i j; simp [mono, const]

theorem mono_neg (k : ℤ) (A : Matrix ι ι ℝ) : mono k (-A) = -mono k A := by
  ext i j; simp [mono, const]

/-- A monomial rule is a shifted on-site rule: `(z^k A u)(x) = A u(x - k)`. -/
theorem mono_valueAt [Fintype ι] [DecidableEq ι] (k : ℤ) (A : Matrix ι ι ℝ)
    (u : LatticeSpace ℝ ℤ ι) (x : ℤ) :
    LatticeSpace.valueAt (Matrix.toLin' (mono k A) u) x = A *ᵥ LatticeSpace.valueAt u (x - k) := by
  funext i
  rw [toLin'_valueAt]
  simp only [mono_apply, AddMonoidAlgebra.coeff_single, Matrix.mulVec, dotProduct,
    LatticeSpace.valueAt_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _)]

end Monomial

/-- A nearest-neighbour symbol `ℓ₋ z⁻¹ + ℓ₀ + ℓ₊ z`. (notes: `prop:qca-C`) -/
noncomputable def nnSymbol (lm l0 lp : Matrix Cell Cell ℝ) : Matrix Cell Cell L :=
  mono (-1) lm + mono 0 l0 + mono 1 lp

/-- The nine-term product `L̂⋆ᵀ Ω L̂`, collected by powers of `z`. -/
theorem nn_product (lm l0 lp : Matrix Cell Cell ℝ) :
    starTranspose (nnSymbol lm l0 lp) * mono 0 omega * nnSymbol lm l0 lp =
      mono 2 (lmᵀ * omega * lp) + mono (-2) (lpᵀ * omega * lm)
        + mono 1 (lmᵀ * omega * l0 + l0ᵀ * omega * lp)
        + mono (-1) (l0ᵀ * omega * lm + lpᵀ * omega * l0)
        + mono 0 (lmᵀ * omega * lm + l0ᵀ * omega * l0 + lpᵀ * omega * lp) := by
  simp only [nnSymbol, starTranspose_add, starTranspose_mono, add_mul, mul_add, mono_mul,
    mono_add]
  norm_num
  abel

/-- Milestone Q1, the equations (C) (thesis (4.11)): the symbol condition is equivalent to five
coefficient equations. (notes: `prop:qca-C`) -/
theorem nn_symplectic_iff (lm l0 lp : Matrix Cell Cell ℝ) :
    starTranspose (nnSymbol lm l0 lp) * mono 0 omega * nnSymbol lm l0 lp = mono 0 omega ↔
      lmᵀ * omega * lp = 0 ∧ lpᵀ * omega * lm = 0 ∧
      lmᵀ * omega * l0 + l0ᵀ * omega * lp = 0 ∧
      l0ᵀ * omega * lm + lpᵀ * omega * l0 = 0 ∧
      lmᵀ * omega * lm + l0ᵀ * omega * l0 + lpᵀ * omega * lp = omega := by
  rw [nn_product]
  constructor
  · intro h
    have c : ∀ m : ℤ, ∀ i j : Cell, _ := fun m i j =>
      congrArg (fun P : Matrix Cell Cell L => (P i j).coeff m) h
    simp only [entry_coeff_add, mono_coeff] at c
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext i j
    · simpa using c 2 i j
    · simpa using c (-2) i j
    · simpa using c 1 i j
    · simpa using c (-1) i j
    · simpa using c 0 i j
  · rintro ⟨h2, hm2, h1, hm1, h0⟩
    rw [h2, hm2, h1, hm1, h0]
    simp [mono, const]

/-- `AᵀΩB = 0` exactly when `adj(A) B = 0`. -/
theorem transpose_mul_omega_mul_eq_zero {A B : Matrix Cell Cell ℝ} (h : Aᵀ * omega * B = 0) :
    adj2 A * B = 0 :=
  omega_mul_cancel (by rw [← Matrix.mul_assoc, ← transpose_mul_omega_mul, h, Matrix.mul_zero])

theorem transpose_mul_omega_mul_add_eq_zero {A B C D : Matrix Cell Cell ℝ}
    (h : Aᵀ * omega * B + Cᵀ * omega * D = 0) : adj2 A * B + adj2 C * D = 0 :=
  omega_mul_cancel (by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul_omega_mul,
      ← transpose_mul_omega_mul, h, Matrix.mul_zero])

theorem transpose_mul_omega_mul_self_eq_iff (A : Matrix Cell Cell ℝ) :
    Aᵀ * omega * A = omega ↔ det2 A = 1 := by
  rw [transpose_mul_omega_mul_self]
  constructor
  · intro h
    simpa using congrFun (congrFun h qIdx) pIdx
  · intro h
    rw [h, one_smul]

/-- Milestone Q1, Proposition 11 (thesis Prop. 4.4, corrected): a symplectic nearest-neighbour
rule is a pure shift, or has `ℓ₀` symplectic and `ℓ₊ = ℓ₋` singular. (notes: `prop:qca-nn`) -/
theorem nn_symplectic {lm l0 lp : Matrix Cell Cell ℝ}
    (h : starTranspose (nnSymbol lm l0 lp) * mono 0 omega * nnSymbol lm l0 lp = mono 0 omega) :
    (l0 = 0 ∧ ((lp = 0 ∧ lmᵀ * omega * lm = omega) ∨ (lm = 0 ∧ lpᵀ * omega * lp = omega))) ∨
      (l0ᵀ * omega * l0 = omega ∧ lp = lm ∧ det2 lp = 0) := by
  obtain ⟨h2, hm2, h1, hm1, h0⟩ := (nn_symplectic_iff lm l0 lp).1 h
  have e2 := transpose_mul_omega_mul_eq_zero h2
  have em2 := transpose_mul_omega_mul_eq_zero hm2
  have e1 := transpose_mul_omega_mul_add_eq_zero h1
  have em1 := transpose_mul_omega_mul_add_eq_zero hm1
  have c0 : det2 lm + det2 l0 + det2 lp = 1 := by
    have := congrFun (congrFun h0 qIdx) pIdx
    simpa [transpose_mul_omega_mul_self] using this
  simp only [transpose_mul_omega_mul_self_eq_iff]
  by_cases hm : det2 lm = 0
  · by_cases hp : det2 lp = 0
    · -- both singular
      right
      have hl0 : det2 l0 = 1 := by linarith
      have hK : adj2 (adj2 l0 * (lm - lp)) = adj2 l0 * (lm - lp) := by
        rw [adj2_mul_rev, adj2_adj2, adj2_sub, Matrix.sub_mul, Matrix.mul_sub,
          eq_neg_of_add_eq_zero_left e1, eq_neg_of_add_eq_zero_right em1]
        abel
      have hc := eq_smul_one_of_adj2_eq two_ne_zero hK
      set c := (adj2 l0 * (lm - lp)) qIdx qIdx
      have hD : lm - lp = c • l0 := by
        have := congrArg (fun X => l0 * X) hc
        simp only [← Matrix.mul_assoc, mul_adj2, hl0, one_smul, Matrix.one_mul,
          Matrix.mul_smul, Matrix.mul_one] at this
        exact this
      have hdet : det2 (lm - lp) = 0 := by
        rw [sub_eq_add_neg, det2_add, det2_neg, Matrix.mul_neg, e2]
        simp [hm, hp]
      rw [hD, det2_smul, hl0, mul_one] at hdet
      have : c = 0 := pow_eq_zero_iff two_ne_zero |>.1 hdet
      rw [this, zero_smul, sub_eq_zero] at hD
      exact ⟨hl0, hD.symm, hp⟩
    · -- ℓ₊ invertible
      left
      have hu : IsUnit (det2 lp) := isUnit_iff_ne_zero.2 hp
      have hlm := eq_zero_of_adj2_mul_eq_zero hu em2
      rw [hlm, Matrix.mul_zero, zero_add] at em1
      have hl0 := eq_zero_of_adj2_mul_eq_zero hu em1
      refine ⟨hl0, Or.inr ⟨hlm, ?_⟩⟩
      rw [hlm, hl0] at c0
      simpa [det2] using c0
  · -- ℓ₋ invertible
    left
    have hu : IsUnit (det2 lm) := isUnit_iff_ne_zero.2 hm
    have hlp := eq_zero_of_adj2_mul_eq_zero hu e2
    rw [hlp, Matrix.mul_zero, add_zero] at e1
    have hl0 := eq_zero_of_adj2_mul_eq_zero hu e1
    refine ⟨hl0, Or.inl ⟨hlp, ?_⟩⟩
    rw [hlp, hl0] at c0
    simpa [det2] using c0

/-- The converse of Proposition 11 for the shift `S z⁻¹`. (notes: `prop:qca-nn`) -/
theorem shift_symplectic {S : Matrix Cell Cell ℝ} (hS : Sᵀ * omega * S = omega) :
    starTranspose (nnSymbol S 0 0) * mono 0 omega * nnSymbol S 0 0 = mono 0 omega := by
  rw [nn_symplectic_iff]
  simp [hS]

/-- The converse of Proposition 11 for the shift `S z`. (notes: `prop:qca-nn`) -/
theorem shift_symplectic' {S : Matrix Cell Cell ℝ} (hS : Sᵀ * omega * S = omega) :
    starTranspose (nnSymbol 0 0 S) * mono 0 omega * nnSymbol 0 0 S = mono 0 omega := by
  rw [nn_symplectic_iff]
  simp [hS]

/-- The converse of Proposition 11 for branch (ii): `ℓ₀` symplectic, `ℓ₊ = ℓ₋` singular, and the
`z^{±1}` condition `(C₁)`. (notes: `prop:qca-nn`) -/
theorem nn_symplectic_of_branch {l0 l : Matrix Cell Cell ℝ} (h0 : l0ᵀ * omega * l0 = omega)
    (hr : det2 l = 0) (h1 : lᵀ * omega * l0 + l0ᵀ * omega * l = 0) :
    starTranspose (nnSymbol l l0 l) * mono 0 omega * nnSymbol l l0 l = mono 0 omega := by
  rw [nn_symplectic_iff]
  have hl : lᵀ * omega * l = 0 := by rw [transpose_mul_omega_mul_self, hr, zero_smul]
  refine ⟨hl, hl, h1, ?_, ?_⟩
  · rw [add_comm]; exact h1
  · rw [hl, h0]; simp

/-- Proposition 11 as an equivalence: a nearest-neighbour symbol is symplectic exactly in the
two branches, branch (ii) including the condition `(C₁)`. (notes: `prop:qca-nn`) -/
theorem nn_symplectic_iff_branch {lm l0 lp : Matrix Cell Cell ℝ} :
    starTranspose (nnSymbol lm l0 lp) * mono 0 omega * nnSymbol lm l0 lp = mono 0 omega ↔
      (l0 = 0 ∧ ((lp = 0 ∧ lmᵀ * omega * lm = omega) ∨ (lm = 0 ∧ lpᵀ * omega * lp = omega))) ∨
        (l0ᵀ * omega * l0 = omega ∧ lp = lm ∧ det2 lp = 0 ∧
          lpᵀ * omega * l0 + l0ᵀ * omega * lp = 0) := by
  constructor
  · intro h
    rcases nn_symplectic h with h' | ⟨h0, hpm, hd⟩
    · exact Or.inl h'
    · refine Or.inr ⟨h0, hpm, hd, ?_⟩
      have h1 := ((nn_symplectic_iff lm l0 lp).1 h).2.2.1
      rw [hpm] at h1 ⊢; exact h1
  · rintro (⟨rfl, ⟨rfl, hS⟩ | ⟨rfl, hS⟩⟩ | ⟨h0, rfl, hd, h1⟩)
    · exact shift_symplectic hS
    · exact shift_symplectic' hS
    · exact nn_symplectic_of_branch h0 hd h1

/-- The one-mode symplectic matrix is alternating. -/
theorem omega_isAlternating : IsAlternating (omega : Matrix Cell Cell ℝ) := by
  intro v
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, omega, Matrix.J]
  ring

/-- The position row `e₁` of the one-mode cell. -/
def e1 : Cell → ℝ := Pi.single qIdx 1

/-- Milestone Q1, Proposition 13 (thesis (4.12)): if `ℓ₊ = ℓ₋ = e₁ aᵀ` has range in the position
row, then `a` is a multiple of the momentum row of `ℓ₀`. (notes: `prop:qca-form`) -/
theorem nn_form {l0 : Matrix Cell Cell ℝ} {a : Cell → ℝ}
    (h : starTranspose (nnSymbol (vecMulVec e1 a) l0 (vecMulVec e1 a)) * mono 0 omega *
      nnSymbol (vecMulVec e1 a) l0 (vecMulVec e1 a) = mono 0 omega) :
    ∃ lam : ℝ, a = lam • l0 pIdx := by
  have h1 := ((nn_symplectic_iff _ _ _).1 h).2.2.1
  have E : a qIdx * l0 pIdx pIdx - a pIdx * l0 pIdx qIdx = 0 := by
    have := congrFun (congrFun h1 qIdx) pIdx
    simp [e1, vecMulVec_apply] at this
    linear_combination this
  have zero_of : vecMulVec e1 a = 0 → ∃ lam : ℝ, a = lam • l0 pIdx := fun hz =>
    ⟨0, funext fun j => by simpa [e1, vecMulVec_apply] using congrFun (congrFun hz qIdx) j⟩
  rcases nn_symplectic h with ⟨-, ⟨hz, -⟩ | ⟨hz, -⟩⟩ | ⟨h0, -, -⟩
  · exact zero_of hz
  · exact zero_of hz
  rw [transpose_mul_omega_mul_self_eq_iff] at h0
  unfold det2 at h0
  by_cases hq : l0 pIdx qIdx = 0
  · have hp : l0 pIdx pIdx ≠ 0 := by rintro hp; rw [hq, hp] at h0; simp at h0
    refine ⟨a pIdx / l0 pIdx pIdx, funext fun j => ?_⟩
    rcases j with ⟨j⟩ | ⟨j⟩ <;> fin_cases j
    · rw [hq] at E
      have : a qIdx = 0 := by
        rcases mul_eq_zero.1 (by linear_combination E : a qIdx * l0 pIdx pIdx = 0) with h | h
        · exact h
        · exact absurd h hp
      simp [this, hq]
    · simp [div_mul_cancel₀ _ hp]
  · refine ⟨a qIdx / l0 pIdx qIdx, funext fun j => ?_⟩
    rcases j with ⟨j⟩ | ⟨j⟩ <;> fin_cases j
    · simp [div_mul_cancel₀ _ hq]
    · change a pIdx = a qIdx / l0 pIdx qIdx * l0 pIdx pIdx
      field_simp
      linear_combination -E

/-- The `z^{±1}` coefficient of the leapfrog symbol: `[[0,0],[0,1]]`. -/
def leapfrogShift : Matrix Cell Cell ℝ :=
  Matrix.of fun i j => match i, j with
    | Sum.inr _, Sum.inr _ => 1
    | _, _ => 0

/-- The `z⁰` coefficient of the leapfrog symbol: `[[0,1],[-1,-m²]]`. -/
def leapfrogCentre (m2 : ℝ) : Matrix Cell Cell ℝ :=
  Matrix.of fun i j => match i, j with
    | Sum.inl _, Sum.inr _ => 1
    | Sum.inr _, Sum.inl _ => -1
    | Sum.inr _, Sum.inr _ => -m2
    | _, _ => 0

/-- The leapfrog symbol `F̂ = [[0,1],[-1,z+z⁻¹-m²]]` of LinearAQFT's lattice field.
(notes: `ex:qca-leapfrog-rule`) -/
noncomputable def leapfrogSymbol (m2 : ℝ) : Matrix Cell Cell L :=
  nnSymbol leapfrogShift (leapfrogCentre m2) leapfrogShift

/-- Milestone Q1, Example 14: the leapfrog is symplectic for every real `m²`; it lies in
branch (ii) of Proposition 11. (notes: `ex:qca-leapfrog`) -/
theorem leapfrog_symplectic (m2 : ℝ) :
    starTranspose (leapfrogSymbol m2) * mono 0 omega * leapfrogSymbol m2 = mono 0 omega := by
  apply nn_symplectic_of_branch
  · rw [transpose_mul_omega_mul_self_eq_iff]
    simp [det2, leapfrogCentre]
  · simp [det2, leapfrogShift]
  · apply cell_ext <;> simp [leapfrogShift, leapfrogCentre]

/-- The `z^{±1}` coefficient of the inverse leapfrog symbol: `[[1,0],[0,0]]`. -/
def leapfrogInvShift : Matrix Cell Cell ℝ :=
  Matrix.of fun i j => match i, j with
    | Sum.inl _, Sum.inl _ => 1
    | _, _ => 0

/-- The `z⁰` coefficient of the inverse leapfrog symbol: `[[-m²,-1],[1,0]]`. -/
def leapfrogInvCentre (m2 : ℝ) : Matrix Cell Cell ℝ :=
  Matrix.of fun i j => match i, j with
    | Sum.inl _, Sum.inl _ => -m2
    | Sum.inl _, Sum.inr _ => -1
    | Sum.inr _, Sum.inl _ => 1
    | _, _ => 0

/-- The symbol `[[z+z⁻¹-m²,-1],[1,0]]` of `F⁻¹`, Krüger's forward rule for the lattice field.
(notes: `ex:qca-leapfrog`) -/
noncomputable def leapfrogInvSymbol (m2 : ℝ) : Matrix Cell Cell L :=
  nnSymbol leapfrogInvShift (leapfrogInvCentre m2) leapfrogInvShift

/-- Milestone Q1, Example 14: the inverse leapfrog symbol is symplectic.
(notes: `ex:qca-leapfrog`) -/
theorem leapfrogInv_symplectic (m2 : ℝ) :
    starTranspose (leapfrogInvSymbol m2) * mono 0 omega * leapfrogInvSymbol m2 =
      mono 0 omega := by
  apply nn_symplectic_of_branch
  · rw [transpose_mul_omega_mul_self_eq_iff]
    simp [det2, leapfrogInvCentre]
  · simp [det2, leapfrogInvShift]
  · apply cell_ext <;> simp [leapfrogInvShift, leapfrogInvCentre]

/-- Milestone Q1, Example 14: `F̂ F̂⁻¹ = 1`. (notes: `ex:qca-leapfrog`) -/
theorem leapfrog_mul_inv (m2 : ℝ) : leapfrogSymbol m2 * leapfrogInvSymbol m2 = 1 := by
  have h1 : leapfrogShift * leapfrogInvShift = 0 := by
    apply cell_ext <;> simp [leapfrogShift, leapfrogInvShift]
  have h2 : leapfrogCentre m2 * leapfrogInvShift = -(leapfrogShift * leapfrogInvCentre m2) := by
    apply cell_ext <;> simp [leapfrogShift, leapfrogCentre, leapfrogInvShift, leapfrogInvCentre]
  have h3 : leapfrogCentre m2 * leapfrogInvCentre m2 = 1 := by
    apply cell_ext <;> simp [leapfrogCentre, leapfrogInvCentre]
  simp only [leapfrogSymbol, leapfrogInvSymbol, nnSymbol, add_mul, mul_add, mono_mul, h1, h2,
    h3, mono_zero, mono_neg]
  norm_num
  rw [mono_zero_eq, const_one]
  abel

/-- The converse of Proposition 13: for `ℓ₀` symplectic and any `λ`, the rule with
`ℓ₊ = ℓ₋ = λ e₁ rᵀ`, `r` the momentum row of `ℓ₀`, is symplectic. (notes: `prop:qca-form`) -/
theorem nn_form_symplectic {l0 : Matrix Cell Cell ℝ} (h0 : l0ᵀ * omega * l0 = omega) (lam : ℝ) :
    starTranspose (nnSymbol (vecMulVec e1 (lam • l0 pIdx)) l0 (vecMulVec e1 (lam • l0 pIdx))) *
      mono 0 omega * nnSymbol (vecMulVec e1 (lam • l0 pIdx)) l0 (vecMulVec e1 (lam • l0 pIdx)) =
      mono 0 omega := by
  apply nn_symplectic_of_branch h0
  · simp [det2, e1, vecMulVec_apply]
  · apply cell_ext <;> simp [e1, vecMulVec_apply]

/-- Milestone Q1, Example 20: the leapfrog symbol is LinearAQFT's change of slice
`F(d₀, d₁) = (d₁, -d₀ + d₁(· + 1) + d₁(· - 1) - m² d₁)` on the cell `u(x) = (d₀(x), d₁(x))`.
(notes: `ex:qca-leapfrog-rule`) -/
theorem leapfrog_valueAt (m2 : ℝ) (u : LatticeSpace ℝ ℤ Cell) (x : ℤ) :
    LatticeSpace.valueAt (Matrix.toLin' (leapfrogSymbol m2) u) x qIdx =
        LatticeSpace.valueAt u x pIdx ∧
      LatticeSpace.valueAt (Matrix.toLin' (leapfrogSymbol m2) u) x pIdx =
        -LatticeSpace.valueAt u x qIdx + LatticeSpace.valueAt u (x + 1) pIdx +
          LatticeSpace.valueAt u (x - 1) pIdx - m2 * LatticeSpace.valueAt u x pIdx := by
  have hv : ∀ w w' : LatticeSpace ℝ ℤ Cell, LatticeSpace.valueAt (w + w') x =
      LatticeSpace.valueAt w x + LatticeSpace.valueAt w' x := fun _ _ => rfl
  simp only [leapfrogSymbol, nnSymbol, map_add, LinearMap.add_apply, hv, mono_valueAt]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, leapfrogShift, leapfrogCentre]
  simp only [qIdx, pIdx]
  ring

end QCALean.Bosonic
