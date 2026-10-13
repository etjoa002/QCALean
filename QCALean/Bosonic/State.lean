/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.WeylAutomorphism
import BosonicLean.Weyl.State
import QCALean.Bosonic.Fourier
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Matrix.Hermitian

/-!
# States on the lattice CCR algebra: translation invariance and evolution

Milestone Q3, Corollary 6 and Propositions 27 and 32. States on a CCR algebra, their
characteristic functions, Gaussian states and the state condition are BosonicLean's
(`BosonicLean.Weyl.State`, `BosonicLean.Weyl.GaussianState`,
`BosonicLean.Weyl.IsStateCondition`). On the lattice, a state is translation invariant exactly
when its characteristic function is. A symplectic rule acts on states by pullback, on Gaussian
data by composition, and preserves translation invariance, and the rules act on the CCR algebra
through a monoid homomorphism.

## Main definitions and results

* `QCALean.Bosonic.translationInvariant_iff`, `QCALean.Bosonic.charFun_ruleAlpha`
* `BosonicLean.Weyl.GaussianState.evolve`, `QCALean.Bosonic.evolve_translationInvariant`
* `QCALean.Bosonic.ruleAlphaHom`, `QCALean.Bosonic.ruleAlphaUnits`
-/

open LinearAQFT BosonicLean.Weyl QCALean.Core Matrix
open scoped ComplexOrder ComplexConjugate

namespace QCALean.Bosonic

/-! ### Translation invariance and evolution on the lattice -/

section Lattice

variable {G : Type*} [AddCommGroup G] {n : ℕ}

theorem ccrTranslate_wCCR (a : G) (u : PhaseVec G n) :
    ccrTranslate G n (Multiplicative.ofAdd a) (wCCR (sigma G n) u) =
      wCCR (sigma G n) (translateEquiv a u) :=
  CCR.relabel_weyl (translateIso a).symplectic u

/-- Milestone Q3, Corollary 6: a state is translation invariant exactly when its characteristic
function is. (notes: `cor:gs-transl`) -/
theorem translationInvariant_iff (ω : State (sigma G n)) :
    (∀ a : G, ω.comp (ccrTranslate G n (Multiplicative.ofAdd a)) = ω) ↔
      ∀ (a : G) u, ω.charFun (translateEquiv a u) = ω.charFun u := by
  constructor
  · intro h a u
    rw [← State.comp_charFun ω _ _ (ccrTranslate_wCCR a), h a]
  · intro h a
    exact State.ext_charFun (sigma_isAlt G n) fun u => by
      rw [State.comp_charFun ω _ _ (ccrTranslate_wCCR a), h]

theorem ruleAlpha_wCCR {M : Sym G n} (hM : IsSymplectic M) (u : PhaseVec G n) :
    ruleAlpha hM (wCCR (sigma G n) u) = wCCR (sigma G n) (Matrix.toLin' M u) :=
  ruleAlpha_weyl hM u

/-- Milestone Q3, Proposition 27(a): `χ_{ω ∘ α_L} = χ_ω ∘ L`. (notes: `prop:gs-evolve`) -/
theorem charFun_ruleAlpha {M : Sym G n} (hM : IsSymplectic M) (ω : State (sigma G n))
    (u : PhaseVec G n) :
    (ω.comp (ruleAlpha hM)).charFun u = ω.charFun (Matrix.toLin' M u) :=
  State.comp_charFun ω _ _ (ruleAlpha_wCCR hM) u

/-- Milestone Q3, Proposition 27(b): the evolved Gaussian state
`(ω ∘ α_L, γ(L·, L·), d ∘ L)`. (notes: `prop:gs-evolve`) -/
noncomputable def _root_.BosonicLean.Weyl.GaussianState.evolve {M : Sym G n} (hM : IsSymplectic M)
    (ω : GaussianState (sigma G n)) : GaussianState (sigma G n) where
  toState := ω.toState.comp (ruleAlpha hM)
  cov := ω.cov.comp (ruleLinearEquiv hM).toLinearMap (ruleLinearEquiv hM).toLinearMap
  isSymm := ⟨fun u w => ω.isSymm.eq _ _⟩
  disp := ω.disp ∘ₗ (ruleLinearEquiv hM).toLinearMap
  charFun_eq u := by
    rw [charFun_ruleAlpha, ω.charFun_eq]
    rfl

/-- (notes: `prop:gs-evolve`) -/
@[simp] theorem _root_.BosonicLean.Weyl.GaussianState.evolve_cov {M : Sym G n} (hM : IsSymplectic M)
    (ω : GaussianState (sigma G n)) (u w : PhaseVec G n) :
    (ω.evolve hM).cov u w = ω.cov (Matrix.toLin' M u) (Matrix.toLin' M w) := rfl

/-- (notes: `prop:gs-evolve`) -/
@[simp] theorem _root_.BosonicLean.Weyl.GaussianState.evolve_disp
    {M : Sym G n} (hM : IsSymplectic M)
    (ω : GaussianState (sigma G n)) (u : PhaseVec G n) :
    (ω.evolve hM).disp u = ω.disp (Matrix.toLin' M u) := rfl

/-- Milestone Q3, Proposition 27(c): evolution preserves translation invariance.
(notes: `prop:gs-evolve`) -/
theorem evolve_translationInvariant {M : Sym G n} (hM : IsSymplectic M)
    (ω : State (sigma G n)) (h : ∀ a : G, ω.comp (ccrTranslate G n (Multiplicative.ofAdd a)) = ω)
    (a : G) :
    (ω.comp (ruleAlpha hM)).comp (ccrTranslate G n (Multiplicative.ofAdd a)) =
      ω.comp (ruleAlpha hM) := by
  have hχ := (translationInvariant_iff ω).1 h
  refine State.ext_charFun (sigma_isAlt G n) fun u => ?_
  refine (State.comp_charFun _ _ _ (ccrTranslate_wCCR a) u).trans ?_
  refine (charFun_ruleAlpha hM ω _).trans ((congrArg ω.charFun ?_).trans
    ((hχ a _).trans (charFun_ruleAlpha hM ω u).symm))
  rw [translateEquiv_apply, toLin'_translate, translateEquiv_apply]

end Lattice

/-! ### The automorphisms of rules as a monoid homomorphism -/

section Hom

variable (G : Type*) [AddCommGroup G] (n : ℕ)

variable {G n} in
/-- Symplectic symbols are closed under products. (notes: `prop:gs-hom`) -/
theorem isSymplectic_mul {M N : Sym G n} (hM : IsSymplectic M) (hN : IsSymplectic N) :
    IsSymplectic (M * N) := by
  unfold IsSymplectic at *
  rw [starTranspose_mul]
  calc starTranspose N * starTranspose M * const G (Gaussian.symplecticForm n) * (M * N) =
      starTranspose N * (starTranspose M * const G (Gaussian.symplecticForm n) * M) * N := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM, hN]

/-- Milestone Q3, Proposition 32: the symplectic symbols, a submonoid of the symbol ring.
(notes: `prop:gs-hom`) -/
def symplecticSubmonoid : Submonoid (Sym G n) where
  carrier := {M | IsSymplectic M}
  mul_mem' hM hN := isSymplectic_mul hM hN
  one_mem' := isSymplectic_one

/-- Milestone Q3, Proposition 32: `L ↦ α_L` is a monoid homomorphism. (notes: `prop:gs-hom`) -/
noncomputable def ruleAlphaHom :
    symplecticSubmonoid G n →*
      (CCR (phaseSpace G n).sigma ≃⋆ₐ[ℂ] CCR (phaseSpace G n).sigma) where
  toFun M := ruleAlpha M.2
  map_one' := ruleAlpha_one _
  map_mul' M N := ruleAlpha_mul M.2 N.2 _

/-- (notes: `prop:gs-hom`) -/
@[simp] theorem ruleAlphaHom_apply (M : symplecticSubmonoid G n) :
    ruleAlphaHom G n M = ruleAlpha M.2 := rfl

/-- Milestone Q3, Proposition 32: the restriction to units, a group homomorphism.
(notes: `prop:gs-hom`) -/
noncomputable def ruleAlphaUnits :
    (symplecticSubmonoid G n)ˣ →*
      (CCR (phaseSpace G n).sigma ≃⋆ₐ[ℂ] CCR (phaseSpace G n).sigma)ˣ :=
  Units.map (ruleAlphaHom G n)

variable {G n} in
/-- Milestone Q4a, Proposition 3(a): powers of a symplectic rule are symplectic.
(notes: `prop:es-iterate`) -/
theorem isSymplectic_pow {M : Sym G n} (hM : IsSymplectic M) (t : ℕ) : IsSymplectic (M ^ t) :=
  (symplecticSubmonoid G n).pow_mem hM t

end Hom

end QCALean.Bosonic
