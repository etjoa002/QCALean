/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.Examples
import LinearAQFT.Lattice.Cauchy

/-!
# The leapfrog on Cauchy data

Milestone Q2, Propositions 18 and 19. LinearAQFT's Cauchy data `(d₀, d₁)` of the lattice
Klein–Gordon field are the one-mode lattice phase space over `ℤ`, with `u(x) = (d₀(x), d₁(x))`.
The identification carries the Wronskian to `σ` and LinearAQFT's change of slice `F` to the rule
of the symbol `F̂` of Q1. So `F` is a linear bijection, with the inverse rule `F̂⁻¹`.

Time translation by one step, `(t, x) ↦ (t + 1, x)`, acts on Cauchy data as `F⁻¹`:
`Λ_t ∘ L_{(1,0)} = F⁻¹ ∘ Λ_t`. In the convention `T W(ξ) = W(Γ ξ)` of thesis (4.7), the forward
rule of the lattice field is therefore `F⁻¹`.

## Main definitions and results

* `QCALean.Bosonic.cauchyEquiv`, `QCALean.Bosonic.cauchyEquiv_wronskian`,
  `QCALean.Bosonic.cauchyEquiv_leapfrog`
* `QCALean.Bosonic.leapfrogEquiv`, `QCALean.Bosonic.leapfrogEquiv_apply`
* `QCALean.Bosonic.cauchyMap_translate_time`
-/

open LinearAQFT LinearAQFT.Lattice QCALean.Core Matrix Gaussian

namespace QCALean.Bosonic

/-- Cauchy data as the one-mode lattice phase space: `u(x) = (d₀(x), d₁(x))`. -/
noncomputable def cauchyEquiv : CauchyData ≃ₗ[ℝ] LatticeSpace ℝ ℤ Cell where
  toFun d := Sum.elim (fun _ => AddMonoidAlgebra.ofCoeff d.1)
    (fun _ => AddMonoidAlgebra.ofCoeff d.2)
  map_add' d d' := by funext i; rcases i with i | i <;> rfl
  map_smul' c d := by funext i; rcases i with i | i <;> rfl
  invFun u := ((u qIdx).coeff, (u pIdx).coeff)
  left_inv d := rfl
  right_inv u := by
    funext i
    rcases i with ⟨i, hi⟩ | ⟨i, hi⟩ <;> obtain rfl : i = 0 := by omega
    · rfl
    · rfl

@[simp] theorem cauchyEquiv_apply_q (d : CauchyData) :
    cauchyEquiv d qIdx = AddMonoidAlgebra.ofCoeff d.1 := rfl

@[simp] theorem cauchyEquiv_apply_p (d : CauchyData) :
    cauchyEquiv d pIdx = AddMonoidAlgebra.ofCoeff d.2 := rfl

theorem cauchyEquiv_valueAt (d : CauchyData) (x : ℤ) :
    LatticeSpace.valueAt (cauchyEquiv d) x qIdx = d.1 x ∧
      LatticeSpace.valueAt (cauchyEquiv d) x pIdx = d.2 x := ⟨rfl, rfl⟩

/-- Two vectors with the same values are equal. -/
theorem latticeSpace_ext {u w : LatticeSpace ℝ ℤ Cell}
    (h : ∀ x, LatticeSpace.valueAt u x qIdx = LatticeSpace.valueAt w x qIdx ∧
      LatticeSpace.valueAt u x pIdx = LatticeSpace.valueAt w x pIdx) : u = w := by
  funext i
  rcases i with ⟨i, hi⟩ | ⟨i, hi⟩ <;> obtain rfl : i = 0 := by omega
  · exact AddMonoidAlgebra.ext (Finsupp.ext fun x => (h x).1)
  · exact AddMonoidAlgebra.ext (Finsupp.ext fun x => (h x).2)

/-- Milestone Q2, Proposition 18: the Wronskian is `σ` for one mode.
(notes: `prop:time-direction`) -/
theorem cauchyEquiv_wronskian (d d' : CauchyData) :
    wronskian d d' = sigma ℤ 1 (cauchyEquiv d) (cauchyEquiv d') := by
  rw [wronskian_apply, sigma, liftForm_apply]
  simp [Fintype.sum_sum_type, ← omega_real, sliceDot, sub_eq_add_neg]

/-- Milestone Q2, Proposition 18: LinearAQFT's change of slice is the rule of `F̂`.
(notes: `prop:time-direction`) -/
theorem cauchyEquiv_leapfrog (m2 : ℝ) (d : CauchyData) :
    cauchyEquiv (leapfrog m2 d) = Matrix.toLin' (leapfrogSymbol m2) (cauchyEquiv d) := by
  refine latticeSpace_ext fun x => ?_
  obtain ⟨h1, h2⟩ := leapfrog_valueAt m2 (cauchyEquiv d) x
  obtain ⟨g1, g2⟩ := leapfrog_apply m2 d x
  refine ⟨?_, ?_⟩
  · rw [h1, (cauchyEquiv_valueAt _ x).1, g1]; rfl
  · rw [h2, (cauchyEquiv_valueAt _ x).2, g2]; rfl

/-- The leapfrog as a linear bijection of Cauchy data. -/
noncomputable def leapfrogEquiv (m2 : ℝ) : CauchyData ≃ₗ[ℝ] CauchyData :=
  cauchyEquiv.trans
    ((ruleLinearEquiv (isSymplectic_of_mono (leapfrog_symplectic m2))).trans cauchyEquiv.symm)

theorem leapfrogEquiv_apply (m2 : ℝ) (d : CauchyData) : leapfrogEquiv m2 d = leapfrog m2 d := by
  simp only [leapfrogEquiv, LinearEquiv.trans_apply, ruleLinearEquiv_apply]
  rw [← cauchyEquiv_leapfrog, LinearEquiv.symm_apply_apply]

/-- The inverse of the leapfrog is the rule of `F̂⁻¹`. -/
theorem cauchyEquiv_leapfrogEquiv_symm (m2 : ℝ) (d : CauchyData) :
    cauchyEquiv ((leapfrogEquiv m2).symm d) =
      Matrix.toLin' (leapfrogInvSymbol m2) (cauchyEquiv d) := by
  apply (leapfrogEquiv m2).injective.comp cauchyEquiv.symm.injective |>.eq_iff.1
  simp only [Function.comp_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
    leapfrogEquiv, LinearEquiv.trans_apply, ruleLinearEquiv_apply]
  rw [← Matrix.toLin'_mul_apply, leapfrog_mul_inv, Matrix.toLin'_one, LinearMap.id_apply,
    LinearEquiv.symm_apply_apply]

/-- One time step of a solution moves its Cauchy data at time `t` to the data at time `t - 1`. -/
theorem cauchyMap_translate (m2 : ℝ) (t : ℤ) (u : LinearAQFT.Lattice.PhaseVec m2) :
    cauchyMap m2 t ((LinearAQFT.Lattice.translateIso m2 (1, 0)).T u) = cauchyMap m2 (t - 1) u := by
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    rw [LinearAQFT.Lattice.translateIso, isoOfPointEquiv_T_mk, cauchyMap_mk, cauchyMap_mk,
      sub_add_cancel]
    congr 1 <;> ext x <;>
      simp only [sliceData_apply] <;>
      rw [causalProp_translateFun] <;> congr 1 <;> ext <;> simp

/-- Milestone Q2, Proposition 19 (direction of time): `Λ_t ∘ L_{(1,0)} = F⁻¹ ∘ Λ_t`.
(notes: `prop:time-direction`) -/
theorem cauchyMap_translate_time (m2 : ℝ) (t : ℤ) (u : LinearAQFT.Lattice.PhaseVec m2) :
    cauchyMap m2 t ((LinearAQFT.Lattice.translateIso m2 (1, 0)).T u) =
      (leapfrogEquiv m2).symm (cauchyMap m2 t u) := by
  rw [cauchyMap_translate, LinearEquiv.eq_symm_apply, leapfrogEquiv_apply]
  have := cauchyMap_succ m2 (t - 1)
  rw [sub_add_cancel] at this
  rw [this, LinearMap.comp_apply]

end QCALean.Bosonic
