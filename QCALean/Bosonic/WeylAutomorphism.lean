/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.Automaton
import BosonicLean.Weyl.Automorphism

/-!
# Automorphisms that move Weyl operators to Weyl operators

Milestone Q2, Theorem 16, on the lattice. The separation of Weyl operators
(Lemma 17) and the automorphism theorem for a nondegenerate symplectic form are BosonicLean's
`BosonicLean.Weyl.weyl_separation` and `BosonicLean.Weyl.weyl_automorphism_of_nondegenerate`.
The lattice form `σ` is nondegenerate, so a star-automorphism `T` of the lattice CCR algebra that
maps each `W(u)` to a multiple `c(u) W(Γ u)` comes from a symplectic `ℝ`-linear bijection `Γ`,
and `c` is a unitary character. This is the statement behind thesis (4.7), with the character
the thesis omits.

## Main results

* `QCALean.Bosonic.sigma_nondegenerate`
* `QCALean.Bosonic.weyl_automorphism`
-/

open LinearAQFT BosonicLean.Weyl QCALean.Core Matrix
open scoped ComplexConjugate CStarAlgebra

namespace QCALean.Bosonic

section Lattice

variable {G : Type*} [AddCommGroup G] {n : ℕ}

/-- `σ` paired with a one-site, one-component vector reads off a coefficient. -/
theorem sigma_single (a : PhaseVec G n) (j : Gaussian.PhaseIndex n) (x : G) :
    sigma G n a (Pi.single j (AddMonoidAlgebra.single x 1)) =
      ∑ i, Gaussian.symplecticForm n i j * (a i).coeff x := by
  classical
  rw [sigma, liftForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Finsupp.sum, Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [Ne.symm hy]
    · intro hx; simp [Finsupp.notMem_support_iff.1 hx]
  · intro k _ hk; simp [hk]
  · simp

/-- The symplectic form of the lattice is nondegenerate. (notes: `thm:weyl-type`) -/
theorem sigma_nondegenerate (a : PhaseVec G n) (h : ∀ w, sigma G n a w = 0) : a = 0 := by
  classical
  funext i
  refine AddMonoidAlgebra.ext (Finsupp.ext fun x => ?_)
  set v : Gaussian.PhaseIndex n → ℝ := fun i => (a i).coeff x with hv
  have hΩv : (Gaussian.symplecticForm n)ᵀ *ᵥ v = 0 := by
    funext j
    have := h (Pi.single j (AddMonoidAlgebra.single x 1))
    rw [sigma_single] at this
    simpa [Matrix.mulVec, dotProduct, hv, mul_comm] using this
  have hT : (Gaussian.symplecticForm n)ᵀ = -Gaussian.symplecticForm n := by
    simp [Gaussian.symplecticForm, Matrix.J_transpose]
  rw [hT, Matrix.neg_mulVec, neg_eq_zero] at hΩv
  have h0 : v = 0 := by
    have := congrArg (fun y => Gaussian.symplecticForm n *ᵥ y) hΩv
    simp only [Matrix.mulVec_mulVec, Gaussian.symplecticForm_sq _, Matrix.neg_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_zero, neg_eq_zero] at this
    exact this
  simpa [hv] using congrFun h0 i

/-- Milestone Q2, Theorem 16: a star-automorphism of the lattice CCR algebra with
`T W(u) = c(u) W(Γ u)` comes from a symplectic linear bijection `Γ`, and `c` is a unitary
character. (notes: `thm:weyl-type`) -/
theorem weyl_automorphism (T : CCR (sigma G n) ≃⋆ₐ[ℂ] CCR (sigma G n))
    (Γ : PhaseVec G n → PhaseVec G n) (c : PhaseVec G n → ℂ)
    (h : ∀ u, (T ⟨weyl _ u, weyl_mem_CCR _ u⟩ : L2 (PhaseVec G n) →L[ℂ] _) =
      c u • weyl (sigma G n) (Γ u)) :
    (∃ L : PhaseVec G n ≃ₗ[ℝ] PhaseVec G n, ⇑L = Γ) ∧
      (∀ u w, sigma G n (Γ u) (Γ w) = sigma G n u w) ∧
      (∀ u w, c (u + w) = c u * c w) ∧ (∀ u, ‖c u‖ = 1) :=
  weyl_automorphism_of_nondegenerate (sigma_isAlt G n)
    ⟨sigma_nondegenerate, fun b hb => sigma_nondegenerate b fun w => by
      rw [← LinearMap.BilinForm.IsAlt.neg_eq (sigma_isAlt G n) w b, hb w, neg_zero]⟩ T Γ c h

end Lattice

end QCALean.Bosonic
