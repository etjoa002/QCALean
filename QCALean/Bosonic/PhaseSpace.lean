/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Net.Automaton
import QCALean.Bosonic.Translation
import LinearAQFT.Lattice.Net

/-!
# The lattice CCR net

Milestone Q2, Proposition 2 and Theorem 3. The bosonic lattice phase space `V` with `n` modes per
site carries the symplectic form `σ(u, w) = Σ_x u(x)ᵀ Ω w(x)`. With `D = V`, `cls = id` and
`loc O = {u | supp u ⊆ O}` it is phase-space data over the lattice causal index, and each
translation is an isomorphism of these data. LinearAQFT's theorems then give the CCR net: it is
generating, causal, isotone and translation covariant.

## Main definitions and results

* `QCALean.Bosonic.PhaseVec`, `QCALean.Bosonic.sigma`, `QCALean.Bosonic.sigma_isAlt`
* `QCALean.Bosonic.loc`, `QCALean.Bosonic.phaseSpace`
* `QCALean.Bosonic.translateEquiv`, `QCALean.Bosonic.translateIso`,
  `QCALean.Bosonic.ccrTranslate`
* `QCALean.Bosonic.ccrNet_lattice`
-/

open LinearAQFT LinearAQFT.Symplectic BosonicLean.Weyl QCALean.Core QCALean.Net Matrix
open scoped Pointwise

namespace QCALean.Bosonic

variable (G : Type*) [AddCommGroup G] (n : ℕ)

/-- The bosonic lattice phase space with `n` modes per site. -/
abbrev PhaseVec := LatticeSpace ℝ G (Gaussian.PhaseIndex n)

/-- The symplectic form `σ(u, w) = Σ_x u(x)ᵀ Ω w(x)`. -/
noncomputable def sigma : LinearMap.BilinForm ℝ (PhaseVec G n) :=
  liftForm (Gaussian.symplecticForm n)

theorem sigma_isAlt : (sigma G n).IsAlt := liftForm_isAlt symplecticForm_isAlternating

variable {G n}

/-- Vectors supported in `O`. (notes: `def:ccr-net`) -/
def locSubmodule (O : Set G) : Submodule ℝ (PhaseVec G n) where
  carrier := {u | ∀ x, x ∉ O → LatticeSpace.valueAt u x = 0}
  add_mem' {u w} hu hw x hx := by
    funext i
    have h1 := congrFun (hu x hx) i
    have h2 := congrFun (hw x hx) i
    simp only [LatticeSpace.valueAt_apply, Pi.zero_apply] at h1 h2 ⊢
    simp [h1, h2]
  zero_mem' x _ := by funext i; simp
  smul_mem' c u hu x hx := by
    funext i
    have h1 := congrFun (hu x hx) i
    simp only [LatticeSpace.valueAt_apply, Pi.zero_apply] at h1 ⊢
    simp [h1]

omit [AddCommGroup G] in
theorem mem_locSubmodule {O : Set G} {u : PhaseVec G n} :
    u ∈ locSubmodule O ↔ ∀ x, x ∉ O → LatticeSpace.valueAt u x = 0 := Iff.rfl

omit [AddCommGroup G] in
/-- A vector lies in `locSubmodule O` iff its support is contained in `O`. -/
theorem mem_locSubmodule_iff_supp [DecidableEq G] {O : Set G} {u : PhaseVec G n} :
    u ∈ locSubmodule O ↔ (LatticeSpace.supp u : Set G) ⊆ O := by
  rw [mem_locSubmodule]
  constructor
  · intro h x hx
    by_contra hxO
    obtain ⟨i, hi⟩ := LatticeSpace.mem_supp.1 hx
    exact hi (by simpa using congrFun (h x hxO) i)
  · intro h x hx
    funext i
    by_contra hne
    exact hx (h (LatticeSpace.mem_supp.2 ⟨i, by simpa using hne⟩))

variable (G n) in
/-- `O ↦ {u | supp u ⊆ O}` as a monotone map. -/
def loc : Set G →o Submodule ℝ (PhaseVec G n) where
  toFun := locSubmodule
  monotone' _ _ h _ hu x hx := hu x (fun h' => hx (h h'))

/-- `σ` vanishes on vectors with disjoint supports. (notes: `thm:ccr-net`) -/
theorem sigma_eq_zero_of_disjoint {O₁ O₂ : Set G} (h : Disjoint O₁ O₂) {u w : PhaseVec G n}
    (hu : u ∈ locSubmodule O₁) (hw : w ∈ locSubmodule O₂) : sigma G n u w = 0 := by
  classical
  rw [sigma, liftForm_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_eq_zero fun x hx => ?_
  by_cases hx₁ : x ∈ O₁
  · have hx₂ : x ∉ O₂ := Set.disjoint_left.1 h hx₁
    have := congrFun (hw x hx₂) j
    simp only [LatticeSpace.valueAt_apply, Pi.zero_apply] at this
    simp [this]
  · have := congrFun (hu x hx₁) i
    simp only [LatticeSpace.valueAt_apply, Pi.zero_apply] at this
    exact absurd this (Finsupp.mem_support_iff.1 hx)

variable (G n) in
/-- Milestone Q2, Proposition 2: the lattice phase-space data, with `D = V` and `cls = id`.
(notes: `def:ccr-net`) -/
noncomputable def phaseSpace : PhaseSpace (latticeIndex G) (PhaseVec G n) (PhaseVec G n) where
  loc := loc G n
  exists_mem_loc _ := ⟨Set.univ, fun _ hx => absurd (Set.mem_univ _) hx⟩
  sigma := sigma G n
  isAlt := sigma_isAlt G n
  cls := LinearMap.id
  cls_surjective := Function.surjective_id
  causal _ _ h _ hu _ hw := sigma_eq_zero_of_disjoint h hu hw
  timeSlice _ _ h f hf := ⟨f, (loc G n).monotone h hf, rfl⟩

@[simp] theorem phaseSpace_sigma : (phaseSpace G n).sigma = sigma G n := rfl

/-- Translation by `a` as a linear equivalence of phase space. -/
noncomputable def translateEquiv (a : G) : PhaseVec G n ≃ₗ[ℝ] PhaseVec G n :=
  LinearEquiv.ofLinearMap (translate ℝ G _ a) (translate ℝ G _ (-a))
    (by rw [← translate_add, add_neg_cancel, translate_zero])
    (by rw [← translate_add, neg_add_cancel, translate_zero])

@[simp] theorem translateEquiv_apply (a : G) (u : PhaseVec G n) :
    translateEquiv a u = translate ℝ G _ a u := rfl

/-- The symbol of translation by `a`: the scalar `z^a`. -/
theorem translate_eq_toLin' (a : G) (u : PhaseVec G n) :
    translate ℝ G _ a u =
      Matrix.toLin' (Matrix.diagonal fun _ => (AddMonoidAlgebra.single a (1 : ℝ))) u := by
  funext i
  simp [translate_apply, Matrix.mulVec_diagonal]

/-- Translations preserve `σ`. (notes: `thm:ccr-net`) -/
theorem sigma_translate (a : G) (u w : PhaseVec G n) :
    sigma G n (translate ℝ G _ a u) (translate ℝ G _ a w) = sigma G n u w := by
  rw [translate_eq_toLin', translate_eq_toLin', sigma]
  refine (preserves_iff _ _).2 ?_ u w
  ext i j : 2
  simp only [starTranspose, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul, Matrix.mul_diagonal, involution_single, const, Matrix.map_apply]
  rw [mul_comm, ← mul_assoc, AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul,
    ← AddMonoidAlgebra.one_def, one_mul]

theorem locSubmodule_map_translate (a : G) (O : Set G) :
    (locSubmodule (n := n) O).map
        ((translateEquiv (n := n) a : PhaseVec G n ≃ₗ[ℝ] PhaseVec G n) :
          PhaseVec G n →ₗ[ℝ] PhaseVec G n) =
      locSubmodule (translateAut a O) := by
  ext w
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap]
  simp only [mem_locSubmodule, translateAut_apply, Set.mem_preimage, LinearEquiv.coe_coe]
  have hs : ∀ x, LatticeSpace.valueAt ((translateEquiv a).symm w) x =
      LatticeSpace.valueAt w (x + a) := fun x => by
    change LatticeSpace.valueAt (translate ℝ G _ (-a) w) x = _
    rw [translate_valueAt, sub_neg_eq_add]
  constructor
  · intro h x hx
    have := h (x - a) hx
    rwa [hs, sub_add_cancel] at this
  · intro h x hx
    rw [hs]
    exact h (x + a) (by simpa using hx)

/-- Translation by `a` as an isomorphism of the lattice phase-space data over `O ↦ O + a`. -/
noncomputable def translateIso (a : G) : (phaseSpace G n).Iso (phaseSpace G n) where
  kappa := translateAut a
  push := translateEquiv a
  map_loc O := locSubmodule_map_translate a O
  T := translateEquiv a
  cls_push _ := rfl
  symplectic := sigma_translate a

@[simp] theorem translateIso_T (a : G) : (translateIso (n := n) a).T = translateEquiv a := rfl

theorem translateEquiv_add (a b : G) :
    translateEquiv (n := n) (a + b) = (translateEquiv b).trans (translateEquiv a) := by
  ext u : 1
  simp [translate_add]

theorem translateEquiv_zero : translateEquiv (G := G) (n := n) 0 = LinearEquiv.refl ℝ _ := by
  ext u : 1
  simp [translate_zero]

theorem ccrAlpha_translateIso_zero :
    ccrAlpha (translateIso (G := G) (n := n) 0) = 1 :=
  (ccrAlpha_congr (e' := PhaseSpace.Iso.refl _) translateEquiv_zero).trans (ccrAlpha_refl _)

theorem ccrAlpha_translateIso_add (a b : G) : ccrAlpha (translateIso (n := n) (a + b)) =
    (ccrAlpha (translateIso b)).trans (ccrAlpha (translateIso a)) := by
  rw [← ccrAlpha_trans]
  exact ccrAlpha_congr (translateEquiv_add a b)

variable (G n) in
/-- The translation action on the CCR algebra, `α_a(W(u)) = W(κ_a u)`.
(notes: `def:ccr-net`, `thm:ccr-net`) -/
noncomputable def ccrTranslate :
    Multiplicative G →* (CCR (phaseSpace G n).sigma ≃⋆ₐ[ℂ] CCR (phaseSpace G n).sigma) where
  toFun a := ccrAlpha (translateIso a.toAdd)
  map_one' := ccrAlpha_translateIso_zero
  map_mul' a b := ccrAlpha_translateIso_add a.toAdd b.toAdd

@[simp] theorem ccrTranslate_apply (a : Multiplicative G) :
    ccrTranslate G n a = ccrAlpha (translateIso a.toAdd) := rfl

variable (G n) in
/-- Milestone Q2, Theorem 3: the lattice CCR net is generating, causal and isotone, and
covariant under the lattice translations. (notes: `thm:ccr-net`) -/
theorem ccrNet_lattice :
    (ccrNet (phaseSpace G n)).IsGenerating ∧
      LinearAQFT.Net.IsCausal (latticeIndex G) (ccrNet (phaseSpace G n)) ∧
      LinearAQFT.Net.HasTimeSlice (latticeIndex G) (ccrNet (phaseSpace G n)) ∧
      LinearAQFT.Net.IsCovariantUnder (ccrNet (phaseSpace G n)) translateHom
        (ccrTranslate G n) :=
  ⟨weylNet_isGenerating _ _, weylNet_isCausal _ _, weylNet_hasTimeSlice _ _,
    fun a => ccrNet_isCovariancePair (translateIso a.toAdd)⟩

end QCALean.Bosonic
