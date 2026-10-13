/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.Automaton
import QCALean.Bosonic.Fourier

/-!
# Examples of Gaussian cellular automata

Milestone Q2, Examples 11–14: the automata listed in the thesis [Krüger 2006, p. 70] and its
example system (4.18). Each is a reversible quantum cellular automaton on the lattice CCR net,
with the stated neighbourhood.

* the shifters, `u ↦ u(· - a)`, neighbourhood `{a}`;
* on-site symplectic maps (rotations and squeezing), neighbourhood `{0}`;
* the rotation with symmetric coupling (4.18), neighbourhood `{-1, 0, 1}`;
* the leapfrog `F` and its inverse, neighbourhood `{-1, 0, 1}`, inverse to each other.
-/

open LinearAQFT LinearAQFT.Symplectic BosonicLean.Weyl QCALean.Core QCALean.Net Matrix Gaussian
open scoped Pointwise

namespace QCALean.Bosonic

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {n : ℕ}

/-! ### Neighbourhoods -/

/-- The symbol of translation by `a`. -/
noncomputable def shiftSymbol (a : G) : Sym G n :=
  Matrix.diagonal fun _ => AddMonoidAlgebra.single a (1 : ℝ)

omit [DecidableEq G] in
theorem shiftSymbol_symplectic (a : G) : IsSymplectic (shiftSymbol (n := n) a) := by
  refine (preserves_iff _ _).1 fun u w => ?_
  simp only [shiftSymbol]
  rw [← translate_eq_toLin', ← translate_eq_toLin']
  exact sigma_translate a u w

theorem symbolRange_shiftSymbol (a : G) : symbolRange (shiftSymbol (n := n) a) ⊆ {a} := by
  intro x hx
  simp only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
  obtain ⟨i, j, hx⟩ := hx
  by_cases h : i = j
  · subst h
    simpa [shiftSymbol, AddMonoidAlgebra.coeff_single, Finsupp.support_single] using hx
  · simp [shiftSymbol, h] at hx

/-- Milestone Q2, Example 11: the shifter by `a` is a reversible QCA with neighbourhood `{a}`;
its rule is the translation `α_a`. (notes: `ex:ccr-shift`) -/
noncomputable def shiftQCA (a : G) :
    ReversibleQCA (ccrNet (phaseSpace G n)) (ccrTranslate G n) :=
  (ruleQCA (shiftSymbol_symplectic a)).mono {a} (symbolRange_shiftSymbol a)

/-- (notes: `ex:ccr-shift`) -/
theorem shiftQCA_rule (a : G) :
    (shiftQCA (n := n) a).rule = ccrTranslate G n (Multiplicative.ofAdd a) := by
  change ruleAlpha _ = ccrAlpha (translateIso a)
  refine relabel_congr _ _ ?_
  ext u : 1
  exact (translate_eq_toLin' a u).symm

/-- The range of a nearest-neighbour symbol lies in `{-1, 0, 1}`. -/
theorem symbolRange_nnSymbol_subset (lm l0 lp : Matrix Cell Cell ℝ) :
    symbolRange (nnSymbol lm l0 lp) ⊆ {-1, 0, 1} := by
  intro x hx
  simp only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
  obtain ⟨i, j, hx⟩ := hx
  have hsub := Finsupp.support_add.trans (Finset.union_subset_union_left Finsupp.support_add) hx
  simp only [mono_apply, Finset.mem_union] at hsub
  rcases hsub with (h | h) | h <;>
    · have := Finsupp.support_single_subset h
      simp only [Finset.mem_singleton] at this
      simp [this]

/-! ### On-site rules -/

/-- An on-site symplectic matrix, as a symbol over `ℤ`. -/
theorem const_symplectic {S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hS : S * Gaussian.symplecticForm n * Sᵀ = Gaussian.symplecticForm n) :
    IsSymplectic (const ℤ S) :=
  (onsite_preserves_iff S).2 hS

theorem symbolRange_const (S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    symbolRange (const ℤ S) ⊆ {0} := by
  intro x hx
  simp only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
  obtain ⟨i, j, hx⟩ := hx
  simp [const, AddMonoidAlgebra.coe_algebraMap] at hx
  simp [hx.1]

/-- Milestone Q2, Example 12: an on-site symplectic map is a reversible QCA with neighbourhood
`{0}`. (notes: `ex:ccr-onsite`) -/
noncomputable def onsiteQCA (S : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (hS : S * Gaussian.symplecticForm n * Sᵀ = Gaussian.symplecticForm n) :
    ReversibleQCA (ccrNet (phaseSpace ℤ n)) (ccrTranslate ℤ n) :=
  (ruleQCA (const_symplectic hS)).mono {0} (symbolRange_const S)

/-- For one mode, a matrix is symplectic exactly when its determinant is one. -/
theorem symplectic_one_mode_of_det {S : Matrix Cell Cell ℝ} (h : det2 S = 1) :
    S * Gaussian.symplecticForm 1 * Sᵀ = Gaussian.symplecticForm 1 := by
  rw [← omega_real]
  have := transpose_mul_omega_mul_self Sᵀ
  rw [Matrix.transpose_transpose] at this
  rw [this, show det2 Sᵀ = det2 S by simp [det2]; ring, h, one_smul]

/-- The on-site squeezing `diag(e^r, e^{-r})`. -/
noncomputable def squeeze (r : ℝ) : Matrix Cell Cell ℝ :=
  Matrix.of fun i j => match i, j with
    | Sum.inl _, Sum.inl _ => Real.exp r
    | Sum.inr _, Sum.inr _ => Real.exp (-r)
    | _, _ => 0

/-- Milestone Q2, Example 12: symplectic rotations on every site. (notes: `ex:ccr-onsite`) -/
noncomputable def rotationOnsiteQCA (φ : ℝ) :
    ReversibleQCA (ccrNet (phaseSpace ℤ 1)) (ccrTranslate ℤ 1) :=
  onsiteQCA (rotation φ) (symplectic_one_mode_of_det (by
    simp [det2, rotation]; nlinarith [Real.sin_sq_add_cos_sq φ]))

/-- Milestone Q2, Example 12: continued squeezing, the same squeezing on every site.
(notes: `ex:ccr-onsite`) -/
noncomputable def squeezeQCA (r : ℝ) :
    ReversibleQCA (ccrNet (phaseSpace ℤ 1)) (ccrTranslate ℤ 1) :=
  onsiteQCA (squeeze r) (symplectic_one_mode_of_det (by
    simp [det2, squeeze, ← Real.exp_add]))

/-! ### Nearest-neighbour rules -/

theorem isSymplectic_of_mono {M : Sym ℤ 1}
    (h : starTranspose M * mono 0 omega * M = mono 0 omega) : IsSymplectic M := by
  rwa [mono_zero_eq, omega_real] at h

/-- Milestone Q2, Example 13: the rotation with symmetric coupling (thesis (4.18)) is a reversible
QCA with neighbourhood `{-1, 0, 1}`. (notes: `ex:ccr-rotation`) -/
noncomputable def rotationQCA (φ lam : ℝ) :
    ReversibleQCA (ccrNet (phaseSpace ℤ 1)) (ccrTranslate ℤ 1) :=
  (ruleQCA (isSymplectic_of_mono (rotation_example φ lam 0).1)).mono {-1, 0, 1}
    (symbolRange_nnSymbol_subset _ _ _)

/-- Milestone Q2, Example 14: the leapfrog `F` is a reversible QCA with neighbourhood
`{-1, 0, 1}`. (notes: `ex:ccr-leapfrog`) -/
noncomputable def leapfrogQCA (m2 : ℝ) :
    ReversibleQCA (ccrNet (phaseSpace ℤ 1)) (ccrTranslate ℤ 1) :=
  (ruleQCA (isSymplectic_of_mono (leapfrog_symplectic m2))).mono {-1, 0, 1}
    (symbolRange_nnSymbol_subset _ _ _)

/-- Milestone Q2, Example 14: the inverse leapfrog `F⁻¹`. (notes: `ex:ccr-leapfrog`) -/
noncomputable def leapfrogInvQCA (m2 : ℝ) :
    ReversibleQCA (ccrNet (phaseSpace ℤ 1)) (ccrTranslate ℤ 1) :=
  (ruleQCA (isSymplectic_of_mono (leapfrogInv_symplectic m2))).mono {-1, 0, 1}
    (symbolRange_nnSymbol_subset _ _ _)

/-- Milestone Q2, Example 14: the two leapfrog automata are inverse to each other.
(notes: `ex:ccr-leapfrog`) -/
theorem leapfrogQCA_symm (m2 : ℝ) :
    (leapfrogQCA m2).rule.symm = (leapfrogInvQCA m2).rule :=
  ruleAlpha_symm_of_mul_eq_one _ _ (leapfrog_mul_inv m2)

end QCALean.Bosonic
