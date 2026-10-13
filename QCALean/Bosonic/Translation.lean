/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.NearestNeighbour
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The statements in physicists' notation

Milestone Q1, Examples 16–17: the twisted criterion read in BosonicLean's and Krüger's notation,
for `n` modes per cell with BosonicLean's symplectic matrix `Ω = symplecticForm n`.

* `QCALean.Bosonic.onsite_preserves_iff`: an on-site rule `S` preserves the lifted form exactly
  when `S Ω Sᵀ = Ω`, BosonicLean's condition.
* `QCALean.Bosonic.ofCoeffs`: the symbol `Σ_m z^m ℓ_m` of finitely many coefficient matrices.
* `QCALean.Bosonic.preserves_iff_krueger`: the criterion as thesis (4.10),
  `Σ_m Γ⁺_m Γ_{m+u} = δ_{u0}` with `Γ⁺ = Ω⁻¹ Γᵀ Ω`.
-/

open Matrix QCALean.Core

namespace QCALean.Bosonic

variable {n : ℕ}

/-- The coefficient matrix of `z^u` in a symbol. -/
noncomputable def coeffMat {ι : Type*} (u : ℤ) : Matrix ι ι L →+ Matrix ι ι ℝ where
  toFun P := Matrix.of fun i j => (P i j).coeff u
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

theorem coeffMat_mono {ι : Type*} (k u : ℤ) (A : Matrix ι ι ℝ) :
    coeffMat u (mono k A) = if k = u then A else 0 := by
  ext i j
  simp only [coeffMat, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply, mono_coeff]
  split_ifs <;> rfl

theorem eq_iff_coeffMat {ι : Type*} (P Q : Matrix ι ι L) :
    P = Q ↔ ∀ u, coeffMat u P = coeffMat u Q := by
  refine ⟨fun h _ => h ▸ rfl, fun h => ?_⟩
  ext i j u
  exact congrFun (congrFun (h u) i) j

/-- `starTranspose` as an additive map. -/
noncomputable def starTransposeHom {ι : Type*} : Matrix ι ι L →+ Matrix ι ι L where
  toFun := starTranspose
  map_zero' := by ext; simp [starTranspose]
  map_add' := starTranspose_add

/-- Milestone Q1, Example 16: an on-site rule `S` preserves the lifted form exactly when
`S Ω Sᵀ = Ω`, BosonicLean's condition (`Gaussian.isAdmissible_symplecticCongruence`).
(notes: `ex:qca-onsite`) -/
theorem onsite_preserves_iff (S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    starTranspose (const ℤ S) * const ℤ (Gaussian.symplecticForm n) * const ℤ S =
        const ℤ (Gaussian.symplecticForm n) ↔
      S * Gaussian.symplecticForm n * Sᵀ = Gaussian.symplecticForm n := by
  rw [← mono_zero_eq, ← mono_zero_eq, starTranspose_mono, neg_zero, mono_mul, mono_mul,
    eq_iff_coeffMat]
  simp only [coeffMat_mono, zero_add]
  have key : Sᵀ * Gaussian.symplecticForm n * S = Gaussian.symplecticForm n ↔
      S * Gaussian.symplecticForm n * Sᵀ = Gaussian.symplecticForm n := by
    simp only [Gaussian.symplecticForm, Matrix.mul_neg, Matrix.neg_mul, neg_inj]
    rw [← SymplecticGroup.mem_iff', SymplecticGroup.mem_iff]
  rw [← key]
  constructor
  · intro h; simpa using h 0
  · intro h u; split_ifs <;> simp [h]

/-- BosonicLean's symplectic matrix is alternating, so its lifted form is the symplectic form of
the lattice phase space. -/
theorem symplecticForm_isAlternating :
    IsAlternating (Gaussian.symplecticForm n) := by
  intro v
  simp [Gaussian.symplecticForm, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.J,
    Matrix.one_apply, mul_comm]

/-- The symbol `Σ_m z^m ℓ_m` with finitely many coefficient matrices. (notes: `ex:qca-coeff`) -/
noncomputable def ofCoeffs
    (l : ℤ →₀ Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) L :=
  l.sum fun m A => mono m A

/-- The coefficients of `L̂⋆ᵀ Ω L̂`: `Σ_m ℓ_mᵀ Ω ℓ_{m+u}`. -/
theorem coeffMat_product (l : ℤ →₀ Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (B : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) (u : ℤ) :
    coeffMat u (starTranspose (ofCoeffs l) * mono 0 B * ofCoeffs l) =
      l.sum fun m A => Aᵀ * B * l (m + u) := by
  have hs : starTranspose (ofCoeffs l) = l.sum fun m A => mono (-m) Aᵀ := by
    change starTransposeHom (l.sum fun m A => mono m A) = _
    rw [map_finsuppSum]
    simp [starTransposeHom, starTranspose_mono]
  rw [hs, ofCoeffs, Finsupp.sum_mul, Finsupp.sum_mul, map_finsuppSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  dsimp only
  rw [mono_mul, Finsupp.mul_sum, map_finsuppSum]
  simp only [mono_mul, coeffMat_mono, add_zero]
  rw [Finsupp.sum]
  rw [Finset.sum_eq_single (m + u)]
  · simp
  · intro b _ hb
    exact ite_eq_right_iff.2 fun h => absurd (by omega) hb
  · intro hmu
    rw [Finsupp.notMem_support_iff.1 hmu]
    simp

/-- Milestone Q1, Example 17: the twisted criterion in Krüger's form (4.9)–(4.10),
`Σ_m Γ⁺_m Γ_{m+u} = δ_{u0}` with `Γ⁺ = Ω⁻¹ Γᵀ Ω`. (notes: `ex:qca-coeff`) -/
theorem preserves_iff_krueger
    (l : ℤ →₀ Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    starTranspose (ofCoeffs l) * const ℤ (Gaussian.symplecticForm n) * ofCoeffs l =
        const ℤ (Gaussian.symplecticForm n) ↔
      ∀ u : ℤ, (l.sum fun m A =>
        (Gaussian.symplecticForm n)⁻¹ * Aᵀ * Gaussian.symplecticForm n * l (m + u)) =
          if u = 0 then 1 else 0 := by
  rw [eq_iff_coeffMat, ← mono_zero_eq]
  simp only [coeffMat_product, coeffMat_mono]
  refine forall_congr' fun u => ?_
  simp only [show ((0 : ℤ) = u) ↔ (u = 0) from eq_comm]
  have hsum : (l.sum fun m A =>
      (Gaussian.symplecticForm n)⁻¹ * Aᵀ * Gaussian.symplecticForm n * l (m + u)) =
      (Gaussian.symplecticForm n)⁻¹ *
        l.sum fun m A => Aᵀ * Gaussian.symplecticForm n * l (m + u) := by
    rw [Finsupp.mul_sum]
    simp only [Matrix.mul_assoc]
  rw [hsum, Gaussian.symplecticForm_inv _]
  constructor
  · intro h
    rw [h]
    split_ifs <;> simp [Gaussian.symplecticForm_sq _]
  · intro h
    have := congrArg (fun X => Gaussian.symplecticForm n * X) h
    simp only [← Matrix.mul_assoc, Matrix.mul_neg, Gaussian.symplecticForm_sq _, neg_neg,
      Matrix.one_mul] at this
    rw [this]
    split_ifs <;> simp

end QCALean.Bosonic
