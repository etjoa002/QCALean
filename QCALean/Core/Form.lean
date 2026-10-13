/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Core.Symbol
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.NoncommRing

/-!
# Lifted forms and form-preserving cellular automata

A bilinear form `B` on one cell lifts to lattice phase space, `B̃(u,w) = Σ_x u(x)ᵀ B w(x)`. In
terms of symbols it is the coefficient at the origin of `u⋆ᵀ B w`, where `⋆` is the involution of
`R[G]` induced by `g ↦ -g` (for `G = ℤ`, `z ↦ z⁻¹`, Mathlib's `LaurentPolynomial.invert`). A
translation-invariant map with symbol `M` preserves `B̃` if and only if `M⋆ᵀ B M = B` (the twisted
criterion, Milestone Q1, Theorem 7; thesis (4.9)–(4.10)). For invertible `B` such a map is
invertible with symbol `B⁻¹ M⋆ᵀ B` (Q1, Theorem 8), and these maps form a group (Q1, Corollary 10).

The rules here are linear maps of phase space. A Clifford cellular automaton over `ZMod d` is a
symplectic rule together with a phase (a character), and that phase is not part of this layer.

## Main definitions and results

* `QCALean.Core.involution`, `QCALean.Core.coeffZero`
* `QCALean.Core.pairing P`: the form `(u, w) ↦ ε(u⋆ᵀ P w)` for a matrix `P` over `R[G]`.
* `QCALean.Core.liftForm B`: the lifted form, `pairing` of the constant symbol `B`.
* `QCALean.Core.IsAlternating`, `QCALean.Core.isAlternating_of_skew`, `QCALean.Core.liftForm_isAlt`
* `QCALean.Core.starTranspose`, `QCALean.Core.pairing_toLin'`
* `QCALean.Core.preserves_iff`: the twisted criterion.
* `QCALean.Core.inverse_of_preserves`, `QCALean.Core.ruleEquiv`,
  `QCALean.Core.ruleEquiv_preserves`, `QCALean.Core.preservingSubgroup`.
-/

open AddMonoidAlgebra Matrix

namespace QCALean.Core

variable {R : Type*} [CommRing R] {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

variable (R G) in
/-- The involution of `R[G]` induced by `g ↦ -g`; for `G = ℤ` it is `LaurentPolynomial.invert`.
(notes: `def:qca-lift`) -/
noncomputable def involution : R[G] ≃ₐ[R] R[G] :=
  AddMonoidAlgebra.domCongr R R (AddEquiv.neg G)

@[simp] theorem involution_single (a : G) (r : R) :
    involution R G (single a r) = single (-a) r := by
  simp [involution]

theorem involution_involution (p : R[G]) : involution R G (involution R G p) = p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single m r => simp

variable (R G) in
/-- The coefficient at the origin. -/
noncomputable def coeffZero : R[G] →ₗ[R] R :=
  (Finsupp.lapply 0).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem coeffZero_apply (p : R[G]) : coeffZero R G p = p.coeff 0 := rfl

/-- The vector of involuted entries. -/
noncomputable def starVec (u : LatticeSpace R G ι) : LatticeSpace R G ι :=
  fun i => involution R G (u i)

omit [Fintype ι] [DecidableEq ι] in
theorem starVec_add (u u' : LatticeSpace R G ι) : starVec (u + u') = starVec u + starVec u' :=
  funext fun _ => map_add _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem starVec_smul (c : R) (u : LatticeSpace R G ι) : starVec (c • u) = c • starVec u := by
  funext i
  simp [starVec]

/-- The form `(u, w) ↦ ε(u⋆ᵀ P w)` for a matrix `P` over `R[G]`. -/
noncomputable def pairing (P : Matrix ι ι R[G]) : LinearMap.BilinForm R (LatticeSpace R G ι) :=
  LinearMap.mk₂ R (fun u w => coeffZero R G (starVec u ⬝ᵥ (P *ᵥ w)))
    (fun u u' w => by rw [starVec_add, add_dotProduct, map_add])
    (fun c u w => by rw [starVec_smul, smul_dotProduct, map_smul])
    (fun u w w' => by rw [mulVec_add, dotProduct_add, map_add])
    (fun c u w => by rw [mulVec_smul, dotProduct_smul, map_smul])

omit [DecidableEq ι] in
theorem pairing_apply (P : Matrix ι ι R[G]) (u w : LatticeSpace R G ι) :
    pairing P u w = (starVec u ⬝ᵥ (P *ᵥ w)).coeff 0 := rfl

variable (G) in
/-- The constant symbol of a matrix over `R`. -/
noncomputable def const (B : Matrix ι ι R) : Matrix ι ι R[G] := B.map (algebraMap R R[G])

/-- Milestone Q1, Definition 6: the lifted form `B̃(u,w) = Σ_x u(x)ᵀ B w(x)`.
(notes: `def:qca-lift`) -/
noncomputable def liftForm (B : Matrix ι ι R) : LinearMap.BilinForm R (LatticeSpace R G ι) :=
  pairing (const G B)

/-- The adjoint symbol `M⋆ᵀ`. (notes: `def:qca-lift`) -/
noncomputable def starTranspose (M : Matrix ι ι R[G]) : Matrix ι ι R[G] :=
  (M.map (involution R G))ᵀ

omit [DecidableEq ι] in
theorem starVec_mulVec (M : Matrix ι ι R[G]) (u : LatticeSpace R G ι) :
    starVec (M *ᵥ u) = M.map (involution R G) *ᵥ starVec u := by
  funext i
  simp [starVec, mulVec, dotProduct, map_sum]

omit [DecidableEq ι] in
theorem mulVec_dotProduct_eq (A : Matrix ι ι R[G]) (s y : LatticeSpace R G ι) :
    (A *ᵥ s) ⬝ᵥ y = s ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]

/-- The pairing of transformed vectors: `⟨M u, P M w⟩ = ⟨u, M⋆ᵀ P M w⟩`. -/
theorem pairing_toLin' (P M : Matrix ι ι R[G]) (u w : LatticeSpace R G ι) :
    pairing P (Matrix.toLin' M u) (Matrix.toLin' M w) = pairing (starTranspose M * P * M) u w := by
  simp only [pairing_apply, toLin'_apply, starVec_mulVec, starTranspose]
  rw [mulVec_dotProduct_eq, mulVec_mulVec, mulVec_mulVec]

/-! ### The lifted form in coordinates -/

/-- The coefficient at the origin of `p⋆ q` is `Σ_x p_x q_x`. -/
theorem coeff_involution_mul_zero (p q : R[G]) :
    (involution R G p * q).coeff 0 = p.coeff.sum fun x c => c * q.coeff x := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy,
      AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index' (fun _ => zero_mul _)
        (fun _ _ _ => add_mul _ _ _)]
  | single m r => simp [coeff_single_mul_apply]

omit [DecidableEq ι] in
/-- The lifted form in coordinates: `B̃(u,w) = Σ_{i,j} B_{ij} Σ_x u_i(x) w_j(x)`, which is
`Σ_x u(x)ᵀ B w(x)` summed in the other order. (notes: `def:qca-lift`) -/
theorem liftForm_apply (B : Matrix ι ι R) (u w : LatticeSpace R G ι) :
    liftForm B u w = ∑ i, ∑ j, B i j * (u i).coeff.sum fun x c => c * (w j).coeff x := by
  simp only [liftForm, pairing_apply, const, dotProduct, mulVec, starVec, Matrix.map_apply,
    Finset.mul_sum, ← Algebra.smul_def, mul_smul_comm]
  rw [← coeffZero_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, coeffZero_apply, coeff_involution_mul_zero, smul_eq_mul]

omit [DecidableEq ι] in
/-- A matrix is alternating if `vᵀ B v = 0` for every `v`. Over rings of characteristic two this
is stronger than skew-symmetry. (notes: `def:qca-lift`) -/
def IsAlternating (B : Matrix ι ι R) : Prop := ∀ v : ι → R, v ⬝ᵥ (B *ᵥ v) = 0

omit [DecidableEq ι] in
/-- A skew-symmetric matrix with zero diagonal is alternating, over any commutative ring
(characteristic two included). -/
theorem isAlternating_of_skew {B : Matrix ι ι R} (hB : Bᵀ = -B) (hd : ∀ i, B i i = 0) :
    IsAlternating B := by
  intro v
  have hs : ∀ i j, B j i = -B i j := fun i j => by
    simpa using congrFun (congrFun hB i) j
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => (x.2, x.1)) ?_ ?_ (fun x _ => by simp) ?_
  · intro x _
    simp only [hs x.1 x.2]
    ring
  · intro x _ hx heq
    have h12 : x.1 = x.2 := (Prod.ext_iff.1 heq).1.symm
    apply hx
    rw [h12, hd]
    ring
  · intro x _
    simp

omit [DecidableEq ι] in
/-- (notes: `def:qca-lift`) -/
theorem liftForm_isAlt {B : Matrix ι ι R} (hB : IsAlternating B) :
    (liftForm (G := G) B).IsAlt := by
  classical
  intro u
  rw [liftForm_apply]
  set S := LatticeSpace.supp u
  have hs : ∀ i j, ((u i).coeff.sum fun x c => c * (u j).coeff x) =
      ∑ x ∈ S, (u i).coeff x * (u j).coeff x := by
    intro i j
    refine Finsupp.sum_of_support_subset _ (fun x hx => ?_) _ (fun _ _ => zero_mul _)
    exact LatticeSpace.mem_supp.2 ⟨i, Finsupp.mem_support_iff.1 hx⟩
  calc ∑ i, ∑ j, B i j * ((u i).coeff.sum fun x c => c * (u j).coeff x)
      = ∑ i, ∑ j, ∑ x ∈ S, B i j * ((u i).coeff x * (u j).coeff x) := by
        simp_rw [hs, Finset.mul_sum]
    _ = ∑ x ∈ S, ∑ i, ∑ j, B i j * ((u i).coeff x * (u j).coeff x) := by
        symm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x ∈ S, LatticeSpace.valueAt u x ⬝ᵥ (B *ᵥ LatticeSpace.valueAt u x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [dotProduct, mulVec, LatticeSpace.valueAt_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = 0 := Finset.sum_eq_zero fun x _ => hB _

/-! ### The twisted criterion -/

omit [DecidableEq ι] in
theorem pairing_sub (P Q : Matrix ι ι R[G]) (u w : LatticeSpace R G ι) :
    pairing (P - Q) u w = pairing P u w - pairing Q u w := by
  simp [pairing_apply, sub_mulVec, dotProduct_sub]

theorem pairing_single (P : Matrix ι ι R[G]) (i j : ι) (k : G) :
    pairing P (Pi.single i 1) (Pi.single j (single k 1)) = (P i j).coeff (-k) := by
  have hs : starVec (Pi.single i (1 : R[G])) = Pi.single i 1 := by
    funext i'
    by_cases h : i' = i
    · subst h; simp [starVec]
    · simp [starVec, h]
  rw [pairing_apply, hs, single_dotProduct, one_mul, mulVec_single]
  simp [coeff_mul_single_apply]

/-- Milestone Q1, Theorem 7 (twisted criterion; thesis (4.9)–(4.10)): a translation-invariant map
with symbol `M` preserves the lifted form of `B` if and only if `M⋆ᵀ B M = B`.
(notes: `thm:qca-criterion`) -/
theorem preserves_iff (B : Matrix ι ι R) (M : Matrix ι ι R[G]) :
    (∀ u w, liftForm B (Matrix.toLin' M u) (Matrix.toLin' M w) = liftForm B u w) ↔
      starTranspose M * const G B * M = const G B := by
  constructor
  · intro h
    ext i j m
    have h' := h (Pi.single i 1) (Pi.single j (single (-m) 1))
    rw [liftForm, pairing_toLin', ← sub_eq_zero, ← pairing_sub, pairing_single, neg_neg] at h'
    simpa [sub_eq_zero] using h'
  · intro h u w
    rw [liftForm, pairing_toLin', h]

/-! ### The inverse and the group -/

omit [Fintype ι] [DecidableEq ι] in
theorem const_mul [Fintype ι] (A B : Matrix ι ι R) : const G (A * B) = const G A * const G B :=
  Matrix.map_mul

omit [Fintype ι] in
theorem const_one : const G (1 : Matrix ι ι R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

omit [DecidableEq ι] in
theorem starTranspose_mul (A B : Matrix ι ι R[G]) :
    starTranspose (A * B) = starTranspose B * starTranspose A := by
  simp [starTranspose, Matrix.map_mul, Matrix.transpose_mul]

omit [Fintype ι] in
theorem starTranspose_one : starTranspose (1 : Matrix ι ι R[G]) = 1 := by
  simp [starTranspose, Matrix.map_one _ (map_zero _) (map_one _)]

/-- Milestone Q1, Theorem 8: for `B` with invertible determinant, a form-preserving
symbol is invertible, with two-sided inverse `B⁻¹ M⋆ᵀ B`.
(notes: `thm:qca-inverse`, `cor:qca-group`) -/
theorem inverse_of_preserves {B : Matrix ι ι R} (hB : IsUnit B.det) {M : Matrix ι ι R[G]}
    (hM : starTranspose M * const G B * M = const G B) :
    const G B⁻¹ * starTranspose M * const G B * M = 1 ∧
      M * (const G B⁻¹ * starTranspose M * const G B) = 1 := by
  have h1 : const G B⁻¹ * starTranspose M * const G B * M = 1 := by
    calc const G B⁻¹ * starTranspose M * const G B * M
        = const G B⁻¹ * (starTranspose M * const G B * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM, ← const_mul, Matrix.nonsing_inv_mul B hB, const_one]
  exact ⟨h1, mul_eq_one_comm.1 h1⟩

/-- The form-preserving cellular automaton as a linear equivalence. (notes: `thm:qca-inverse`) -/
noncomputable def ruleEquiv {B : Matrix ι ι R} (hB : IsUnit B.det) {M : Matrix ι ι R[G]}
    (hM : starTranspose M * const G B * M = const G B) :
    LatticeSpace R G ι ≃ₗ[R] LatticeSpace R G ι :=
  LinearEquiv.ofLinearMap (f := (Matrix.toLin' M).restrictScalars R)
    (g := (Matrix.toLin' (const G B⁻¹ * starTranspose M * const G B)).restrictScalars R)
    (LinearMap.ext fun u => by
      have h := (inverse_of_preserves hB hM).2
      simp only [Matrix.mul_assoc] at h
      simp [h])
    (LinearMap.ext fun u => by
      have h := (inverse_of_preserves hB hM).1
      simp only [Matrix.mul_assoc] at h
      simp [h])

theorem ruleEquiv_apply {B : Matrix ι ι R} (hB : IsUnit B.det) {M : Matrix ι ι R[G]}
    (hM : starTranspose M * const G B * M = const G B) (u : LatticeSpace R G ι) :
    ruleEquiv hB hM u = Matrix.toLin' M u := rfl

/-- The linear equivalence preserves the lifted form, in the hypothesis shape of
`BosonicLean.Weyl.CCR.relabel`. (notes: `thm:qca-inverse`) -/
theorem ruleEquiv_preserves {B : Matrix ι ι R} (hB : IsUnit B.det) {M : Matrix ι ι R[G]}
    (hM : starTranspose M * const G B * M = const G B) :
    ∀ u w, liftForm B (ruleEquiv hB hM u) (ruleEquiv hB hM w) = liftForm B u w :=
  fun u w => (preserves_iff B M).2 hM u w

/-- The inverse of a form-preserving automaton preserves the form as well.
(notes: `thm:qca-inverse`) -/
theorem ruleEquiv_symm_preserves {B : Matrix ι ι R} (hB : IsUnit B.det)
    {M : Matrix ι ι R[G]} (hM : starTranspose M * const G B * M = const G B) :
    ∀ u w, liftForm B ((ruleEquiv hB hM).symm u) ((ruleEquiv hB hM).symm w) =
      liftForm B u w := by
  intro u w
  conv_rhs => rw [← (ruleEquiv hB hM).apply_symm_apply u,
    ← (ruleEquiv hB hM).apply_symm_apply w]
  rw [ruleEquiv_preserves]

/-- Milestone Q1, Corollary 10: the form-preserving symbols form a subgroup of the units.
(notes: `cor:qca-group`) -/
noncomputable def preservingSubgroup (B : Matrix ι ι R) : Subgroup (Matrix ι ι R[G])ˣ where
  carrier := {U | starTranspose (U : Matrix ι ι R[G]) * const G B * U = const G B}
  one_mem' := by simp [starTranspose_one]
  mul_mem' := by
    intro U V hU hV
    simp only [Set.mem_ofPred_eq, Units.val_mul, starTranspose_mul] at *
    calc starTranspose (V : Matrix ι ι R[G]) * starTranspose (U : Matrix ι ι R[G]) * const G B *
          (U * V)
        = starTranspose (V : Matrix ι ι R[G]) *
            (starTranspose (U : Matrix ι ι R[G]) * const G B * U) * V := by
          simp only [Matrix.mul_assoc]
      _ = const G B := by rw [hU, hV]
  inv_mem' := by
    intro U hU
    simp only [Set.mem_ofPred_eq] at *
    have hinv :
        starTranspose (↑U⁻¹ : Matrix ι ι R[G]) * starTranspose (U : Matrix ι ι R[G]) = 1 := by
      rw [← starTranspose_mul, Units.mul_inv, starTranspose_one]
    calc starTranspose (↑U⁻¹ : Matrix ι ι R[G]) * const G B * ↑U⁻¹
        = starTranspose (↑U⁻¹ : Matrix ι ι R[G]) *
            (starTranspose (U : Matrix ι ι R[G]) * const G B * U) * ↑U⁻¹ := by rw [hU]
      _ = const G B := by
          simp only [← Matrix.mul_assoc, hinv, Matrix.one_mul]
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- If `N² = N'² = −1`, then `N' (A + N' A N) N = A + N' A N`. -/
theorem sandwich_add_sandwich_of_sq_eq_neg_one {R : Type*} [Ring R] (A N NT : R) (hN : N * N = -1)
    (hT : NT * NT = -1) : NT * (A + NT * A * N) * N = A + NT * A * N := by
  have e : NT * (A + NT * A * N) * N = NT * A * N + (NT * NT) * A * (N * N) := by noncomm_ring
  rw [e, hN, hT]
  noncomm_ring

/-- If `N² = N'² = −1`, then `N' (A + N' A N) + (A + N' A N) N = 0`. -/
theorem mul_add_add_mul_eq_zero_of_sq_eq_neg_one {R : Type*} [Ring R] (A N NT : R)
    (hN : N * N = -1) (hT : NT * NT = -1) :
    NT * (A + NT * A * N) + (A + NT * A * N) * N = 0 := by
  have e : NT * (A + NT * A * N) + (A + NT * A * N) * N =
      NT * A + (NT * NT) * A * N + A * N + NT * A * (N * N) := by noncomm_ring
  rw [e, hN, hT]
  noncomm_ring

end QCALean.Core
