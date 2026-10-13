/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.PhaseSpace

/-!
# Gaussian cellular automata on the CCR algebra

Milestone Q2, Definition 4 to Proposition 15. A symplectic rule `L` gives the star-automorphism
`α_L` of the CCR algebra with `α_L(W(u)) = W(L u)`: LinearAQFT's relabelling along the linear
bijection of Q1. It composes, commutes with the translations, and maps `𝒜(O)` into `𝒜(O + N)`
with `N` the range of the symbol. Hence it is a reversible quantum cellular automaton. The
examples are the shifters, on-site rotations and squeezing, the rotation with symmetric coupling
and the leapfrog. A rule is determined by its one-site values, and it is symplectic exactly when
these satisfy the one-cell commutation relations with their translates (the local rule, thesis
Lemma 4.2 in Gaussian form).

## Main definitions and results

* `QCALean.Bosonic.IsSymplectic`, `QCALean.Bosonic.ruleAlpha`, `QCALean.Bosonic.ruleAlpha_weyl`
* `QCALean.Bosonic.ruleAlpha_mul`, `QCALean.Bosonic.ruleAlpha_one`,
  `QCALean.Bosonic.ruleAlpha_comm_translate`, `QCALean.Bosonic.ruleAlpha_local`
* `QCALean.Bosonic.ruleQCA`
* `QCALean.Bosonic.rule_ext`, `QCALean.Bosonic.isSymplectic_iff_cell`
-/

open LinearAQFT LinearAQFT.Symplectic BosonicLean.Weyl QCALean.Core QCALean.Net Matrix
open scoped Pointwise CStarAlgebra

namespace QCALean.Bosonic

variable {G : Type*} [AddCommGroup G] {n : ℕ}

/-- The symbol ring of the bosonic lattice. -/
abbrev Sym (G : Type*) [AddCommGroup G] (n : ℕ) :=
  Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) (AddMonoidAlgebra ℝ G)

/-- A symbol is symplectic: `L̂⋆ᵀ Ω L̂ = Ω`. -/
def IsSymplectic (M : Sym G n) : Prop :=
  starTranspose M * const G (Gaussian.symplecticForm n) * M = const G (Gaussian.symplecticForm n)

theorem isUnit_det_symplecticForm : IsUnit (Gaussian.symplecticForm n).det :=
  Matrix.isUnit_det_of_left_inverse (B := -Gaussian.symplecticForm n)
    (by rw [Matrix.neg_mul, Gaussian.symplecticForm_sq _, neg_neg])

/-- The linear bijection of a symplectic rule. -/
noncomputable def ruleLinearEquiv {M : Sym G n} (hM : IsSymplectic M) :
    PhaseVec G n ≃ₗ[ℝ] PhaseVec G n :=
  ruleEquiv isUnit_det_symplecticForm hM

@[simp] theorem ruleLinearEquiv_apply {M : Sym G n} (hM : IsSymplectic M) (u : PhaseVec G n) :
    ruleLinearEquiv hM u = Matrix.toLin' M u := rfl

theorem sigma_rule {M : Sym G n} (hM : IsSymplectic M) (u w : PhaseVec G n) :
    (phaseSpace G n).sigma (ruleLinearEquiv hM u) (ruleLinearEquiv hM w) =
      (phaseSpace G n).sigma u w :=
  ruleEquiv_preserves isUnit_det_symplecticForm hM u w

/-- Milestone Q2, Definition 4: `α_L`, the star-automorphism of the CCR algebra of a symplectic
rule. -/
noncomputable def ruleAlpha {M : Sym G n} (hM : IsSymplectic M) :
    CCR (phaseSpace G n).sigma ≃⋆ₐ[ℂ] CCR (phaseSpace G n).sigma :=
  CCR.relabel (sigma_rule hM)

/-- A relabelling depends only on the linear map. -/
theorem relabel_congr {T T' : PhaseVec G n ≃ₗ[ℝ] PhaseVec G n}
    (hT : ∀ u v, (phaseSpace G n).sigma (T u) (T v) = (phaseSpace G n).sigma u v)
    (hT' : ∀ u v, (phaseSpace G n).sigma (T' u) (T' v) = (phaseSpace G n).sigma u v)
    (h : T = T') : CCR.relabel hT = CCR.relabel hT' := by
  subst h; rfl

/-- Milestone Q2, Proposition 5(a): `α_L(W(u)) = W(L u)`. (notes: `prop:alpha`) -/
theorem ruleAlpha_weyl {M : Sym G n} (hM : IsSymplectic M) (u : PhaseVec G n) :
    ruleAlpha hM ⟨weyl _ u, weyl_mem_CCR _ u⟩ =
      ⟨weyl _ (Matrix.toLin' M u), weyl_mem_CCR _ _⟩ :=
  CCR.relabel_weyl (sigma_rule hM) u

/-- Milestone Q2, Proposition 5(b): `α_{L N} = α_L α_N`. (notes: `prop:alpha`) -/
theorem ruleAlpha_mul {M N : Sym G n} (hM : IsSymplectic M) (hN : IsSymplectic N)
    (hMN : IsSymplectic (M * N)) : ruleAlpha hMN = (ruleAlpha hN).trans (ruleAlpha hM) := by
  rw [ruleAlpha, ruleAlpha, ruleAlpha, ← CCR.relabel_trans]
  refine relabel_congr _ _ ?_
  ext u : 1
  simp [Matrix.toLin'_mul]

/-- Milestone Q2, Proposition 5(b): `α_1 = id`. (notes: `prop:alpha`) -/
theorem ruleAlpha_one (h1 : IsSymplectic (1 : Sym G n)) :
    ruleAlpha h1 = StarAlgEquiv.refl (R := ℂ) (A := CCR (phaseSpace G n).sigma) := by
  rw [ruleAlpha, ← CCR.relabel_refl]
  refine relabel_congr _ _ ?_
  ext u : 1
  simp

/-- A rule commutes with the translations. -/
theorem toLin'_translate (M : Sym G n) (a : G) (u : PhaseVec G n) :
    Matrix.toLin' M (translate ℝ G _ a u) = translate ℝ G _ a (Matrix.toLin' M u) := by
  rw [translate_apply, translate_apply, map_smul]

/-- Milestone Q2, Proposition 5(c): `α_L` commutes with every translation `α_a`.
(notes: `prop:alpha`) -/
theorem ruleAlpha_comm_translate {M : Sym G n} (hM : IsSymplectic M) (a : Multiplicative G) :
    (ruleAlpha hM).trans (ccrTranslate G n a) = (ccrTranslate G n a).trans (ruleAlpha hM) := by
  rw [ccrTranslate_apply, ccrAlpha, ruleAlpha, ← CCR.relabel_trans, ← CCR.relabel_trans]
  refine relabel_congr _ _ ?_
  ext u : 1
  have := toLin'_translate M a.toAdd u
  simp only [Matrix.toLin'_apply] at this
  simp [this]

/-- A vector supported in `O` is carried by a rule into `O + N`, `N` the range of the symbol. -/
theorem toLin'_mem_locSubmodule [DecidableEq G] (M : Sym G n) {O : Set G} {u : PhaseVec G n}
    (hu : u ∈ locSubmodule O) :
    Matrix.toLin' M u ∈ locSubmodule (O + (symbolRange M : Set G)) := by
  intro x hx
  funext i
  by_contra hne
  have hxs : x ∈ LatticeSpace.supp (Matrix.toLin' M u) := LatticeSpace.mem_supp.2 ⟨i, hne⟩
  obtain ⟨y, hy, m, hm, rfl⟩ := Finset.mem_add.1 (supp_toLin'_subset M u hxs)
  obtain ⟨j, hj⟩ := LatticeSpace.mem_supp.1 hy
  have hyO : y ∈ O := by
    by_contra hyO
    exact hj (by simpa using congrFun (hu y hyO) j)
  exact hx (Set.add_mem_add hyO hm)

/-- The Weyl system of the lattice CCR algebra sends `u` to `W(u)`. -/
theorem weylSystem_W_eq (u : PhaseVec G n) :
    (CCR.weylSystem (phaseSpace G n).sigma (phaseSpace G n).isAlt).W u =
      ⟨weyl _ u, weyl_mem_CCR _ u⟩ :=
  Subtype.ext (CCR.weylSystem_W _ _ u)

/-- Milestone Q2, Theorem 6 (locality): `α_L 𝒜(O) ⊆ 𝒜(O + N)`, `N` the range of the symbol.
(notes: `thm:alpha-local`) -/
theorem ruleAlpha_local [DecidableEq G] {M : Sym G n} (hM : IsSymplectic M) (O : Set G) :
    (ccrNet (phaseSpace G n) O).map (ruleAlpha hM).toStarAlgHom ≤
      ccrNet (phaseSpace G n) (O + (symbolRange M : Set G)) := by
  simp only [ccrNet, weylNet, LinearAQFT.Net.generated_apply]
  refine (StarSubalgebra.map_topologicalClosure_le _ _ (map_continuous _)).trans ?_
  rw [StarAlgHom.map_adjoin]
  refine StarSubalgebra.topologicalClosure_mono (StarAlgebra.adjoin_mono ?_)
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨Matrix.toLin' M u, toLin'_mem_locSubmodule M hu, ?_⟩
  change (CCR.weylSystem (phaseSpace G n).sigma (phaseSpace G n).isAlt).W (Matrix.toLin' M u) =
    ruleAlpha hM ((CCR.weylSystem (phaseSpace G n).sigma (phaseSpace G n).isAlt).W u)
  rw [weylSystem_W_eq, weylSystem_W_eq, ruleAlpha_weyl]

theorem ruleAlpha_congr {M N : Sym G n} (hM : IsSymplectic M) (hN : IsSymplectic N) (h : M = N) :
    ruleAlpha hM = ruleAlpha hN := by
  subst h; rfl

theorem isSymplectic_one : IsSymplectic (1 : Sym G n) := by
  simp [IsSymplectic, starTranspose_one]

/-- The symbol of the inverse rule, `Ω⁻¹ L̂⋆ᵀ Ω`. -/
noncomputable def invSymbol (M : Sym G n) : Sym G n :=
  const G (Gaussian.symplecticForm n)⁻¹ * starTranspose M * const G (Gaussian.symplecticForm n)

theorem mul_invSymbol {M : Sym G n} (hM : IsSymplectic M) : M * invSymbol M = 1 :=
  (inverse_of_preserves isUnit_det_symplecticForm hM).2

/-- If `L̂ N̂ = 1`, then `α_L⁻¹ = α_N`. -/
theorem ruleAlpha_symm_of_mul_eq_one {M N : Sym G n} (hM : IsSymplectic M) (hN : IsSymplectic N)
    (h : M * N = 1) : (ruleAlpha hM).symm = ruleAlpha hN := by
  have h1 : IsSymplectic (M * N) := h.symm ▸ isSymplectic_one
  have key := (ruleAlpha_mul hM hN h1).symm.trans
    ((ruleAlpha_congr h1 isSymplectic_one h).trans (ruleAlpha_one _))
  ext x : 1
  have hx : ruleAlpha hM (ruleAlpha hN x) = x := DFunLike.congr_fun key x
  calc (ruleAlpha hM).symm x = (ruleAlpha hM).symm (ruleAlpha hM (ruleAlpha hN x)) := by rw [hx]
    _ = ruleAlpha hN x := (ruleAlpha hM).symm_apply_apply _

/-- Milestone Q2, Corollary 7: `α_L⁻¹ = α_{L⁻¹}`, with the inverse symbol `Ω⁻¹ L̂⋆ᵀ Ω`.
(notes: `prop:alpha`) -/
theorem ruleAlpha_symm {M : Sym G n} (hM : IsSymplectic M) (hM' : IsSymplectic (invSymbol M)) :
    (ruleAlpha hM).symm = ruleAlpha hM' :=
  ruleAlpha_symm_of_mul_eq_one hM hM' (mul_invSymbol hM)

/-- Milestone Q2, Theorem 10: a symplectic rule is a reversible quantum cellular automaton on the
lattice CCR net, with the range of its symbol as neighbourhood. (notes: `thm:rule-qca`) -/
noncomputable def ruleQCA [DecidableEq G] {M : Sym G n} (hM : IsSymplectic M) :
    ReversibleQCA (ccrNet (phaseSpace G n)) (ccrTranslate G n) where
  rule := ruleAlpha hM
  nbhd := symbolRange M
  covariant := (ccrNet_lattice G n).2.2.2
  comm := ruleAlpha_comm_translate hM
  isLocal := ruleAlpha_local hM

@[simp] theorem ruleQCA_rule [DecidableEq G] {M : Sym G n} (hM : IsSymplectic M) :
    (ruleQCA hM).rule = ruleAlpha hM := rfl

/-- Milestone Q2, Proposition 15(a): a rule is determined by its values on the one-site vectors.
(notes: `prop:local-rule`) -/
theorem rule_ext {M N : Sym G n}
    (h : ∀ i, Matrix.toLin' M (Pi.single i 1) = Matrix.toLin' N (Pi.single i 1)) : M = N := by
  ext i j : 2
  simpa [Matrix.toLin'_apply, Matrix.mulVec_single] using congrFun (h j) i

/-- The translate of a one-site vector. -/
theorem translate_single (x : G) (j : Gaussian.PhaseIndex n) :
    translate ℝ G _ x (Pi.single j 1 : PhaseVec G n) =
      Pi.single j (AddMonoidAlgebra.single x 1) := by
  funext k
  by_cases h : k = j
  · subst h; simp [translate_apply]
  · simp [translate_apply, h]

/-- Milestone Q2, Proposition 15(b): a rule is symplectic if and only if the images of the
one-site vectors satisfy the one-cell commutation relations with their translates.
(notes: `prop:local-rule`) -/
theorem isSymplectic_iff_cell [DecidableEq G] {M : Sym G n} :
    IsSymplectic M ↔ ∀ (i j : Gaussian.PhaseIndex n) (x : G),
      sigma G n (Matrix.toLin' M (Pi.single i 1))
          (translate ℝ G _ x (Matrix.toLin' M (Pi.single j 1))) =
        if x = 0 then Gaussian.symplecticForm n i j else 0 := by
  have hval : ∀ i j x, sigma G n (Matrix.toLin' M (Pi.single i 1))
      (translate ℝ G _ x (Matrix.toLin' M (Pi.single j 1))) =
      ((starTranspose M * const G (Gaussian.symplecticForm n) * M) i j).coeff (-x) := by
    intro i j x
    rw [← toLin'_translate, translate_single, sigma, liftForm, pairing_toLin', pairing_single]
  have hconst : ∀ i j (x : G), ((const G (Gaussian.symplecticForm n)) i j).coeff (-x) =
      if x = 0 then Gaussian.symplecticForm n i j else 0 := by
    intro i j x
    by_cases hx : x = 0
    · subst hx; simp [const]
    · simp [const, hx, AddMonoidAlgebra.coeff_single]
  simp only [hval, ← hconst]
  constructor
  · intro h i j x; rw [h]
  · intro h
    ext i j m : 3
    simpa using h i j (-m)

end QCALean.Bosonic
