/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Core.Lattice
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Symbols of translation-invariant maps

A linear map of lattice phase space is translation invariant when it commutes with every
translation. Such maps are exactly the `R[G]`-linear maps (Milestone Q1, Theorem 3(a)), so they
are matrices over the group algebra, their *symbols*; composition is the product of symbols
(thesis (4.13)), and the value of `L u` at `x` is the convolution `Σ_m ℓ_m u(x - m)` with the
coefficient matrices `ℓ_m` of the symbol (thesis (4.8)). A consequence is finite range: the
support moves by at most the support of the symbol (Q1, Corollary 4).

"Symbol" is used as for Toeplitz and Laurent operators: here the symbol is a matrix of Laurent
polynomials (for `G = ℤ`) rather than a function on the circle.

## Main definitions and results

* `QCALean.Core.IsTranslationInvariant`
* `QCALean.Core.isTranslationInvariant_iff`: translation invariant ⇔ `R[G]`-linear.
* `QCALean.Core.symbolEquiv`: `R[G]`-linear maps ≃ matrices over `R[G]`, as algebras.
* `QCALean.Core.toLin'_valueAt`: the convolution formula.
* `QCALean.Core.symbolRange`, `QCALean.Core.supp_toLin'_subset`: finite range.
-/

open AddMonoidAlgebra
open scoped Pointwise

namespace QCALean.Core

variable {R : Type*} [CommRing R] {G : Type*} [AddCommGroup G] {ι : Type*}

/-- An `R`-linear map commuting with every translation. (notes: `def:qca-invariant`) -/
def IsTranslationInvariant (L : LatticeSpace R G ι →ₗ[R] LatticeSpace R G ι) : Prop :=
  ∀ a, L ∘ₗ translate R G ι a = translate R G ι a ∘ₗ L

/-- A translation-invariant `R`-linear map commutes with the action of every element of `R[G]`. -/
theorem IsTranslationInvariant.map_smul {L : LatticeSpace R G ι →ₗ[R] LatticeSpace R G ι}
    (hL : IsTranslationInvariant L) (c : R[G]) (u : LatticeSpace R G ι) :
    L (c • u) = c • L u := by
  induction c using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_smul, hx, hy]
  | single m r =>
    have e : (single m r : R[G]) = r • single m 1 := by simp
    have h := LinearMap.congr_fun (hL m) u
    simp only [LinearMap.comp_apply, translate_apply] at h
    rw [e, smul_assoc, L.map_smul, h, smul_assoc]

/-- Milestone Q1, Theorem 3(a): the translation-invariant `R`-linear maps are exactly the
`R[G]`-linear maps. (notes: `thm:qca-symbol`) -/
theorem isTranslationInvariant_iff (L : LatticeSpace R G ι →ₗ[R] LatticeSpace R G ι) :
    IsTranslationInvariant L ↔
      ∃ M : LatticeSpace R G ι →ₗ[R[G]] LatticeSpace R G ι, M.restrictScalars R = L := by
  constructor
  · intro hL
    exact ⟨{ toFun := L, map_add' := L.map_add, map_smul' := hL.map_smul }, rfl⟩
  · rintro ⟨M, rfl⟩ a
    ext u : 1
    simp [translate_apply]

variable (R G ι) in
/-- Milestone Q1, Theorem 3(b): `R[G]`-linear maps are matrices over `R[G]`, as algebras, so the
symbol of a composition is the product of the symbols (thesis (4.13)). (notes: `thm:qca-symbol`) -/
noncomputable def symbolEquiv [Fintype ι] [DecidableEq ι] :
    Module.End R[G] (LatticeSpace R G ι) ≃ₐ[R[G]] Matrix ι ι R[G] :=
  (Matrix.toLinAlgEquiv').symm

/-- Milestone Q1, Theorem 3(c), thesis (4.8): the value of `L u` at `x` is `Σ_m ℓ_m u(x - m)`,
with `ℓ_m` the coefficient matrices of the symbol `M`. (notes: `thm:qca-symbol`) -/
theorem toLin'_valueAt [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R[G])
    (u : LatticeSpace R G ι) (x : G) (i : ι) :
    LatticeSpace.valueAt (Matrix.toLin' M u) x i =
      ∑ j, (M i j).coeff.sum fun m c => c * (u j).coeff (x - m) := by
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, coeff_mul_apply_left, neg_add_eq_sub]

/-- The range of a symbol: the union of the supports of its entries. (notes: `cor:qca-range`) -/
def symbolRange [Fintype ι] [DecidableEq G] (M : Matrix ι ι R[G]) : Finset G :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => (M i j).coeff.support

/-- Milestone Q1, Corollary 4: finite range, `supp (L u) ⊆ supp u + N`. (notes: `cor:qca-range`) -/
theorem supp_toLin'_subset [Fintype ι] [DecidableEq ι] [DecidableEq G] (M : Matrix ι ι R[G])
    (u : LatticeSpace R G ι) :
    LatticeSpace.supp (Matrix.toLin' M u) ⊆ LatticeSpace.supp u + symbolRange M := by
  intro x hx
  obtain ⟨i, hi⟩ := LatticeSpace.mem_supp.1 hx
  rw [← LatticeSpace.valueAt_apply, toLin'_valueAt] at hi
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  obtain ⟨m, hm, hm'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  have hu : (u j).coeff (x - m) ≠ 0 := right_ne_zero_of_mul hm'
  refine Finset.mem_add.2 ⟨x - m, LatticeSpace.mem_supp.2 ⟨j, hu⟩, m, ?_, sub_add_cancel x m⟩
  simp only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, j, hm⟩

end QCALean.Core
