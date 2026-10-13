/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.State

/-!
# Lattice cells, cell forms and their Fourier transforms

Milestone Q3. Site vectors of the lattice phase space, covariance forms built from cell
coefficients, their evolution under a rule, and the Fourier transform `gammaHat` of the cells.
-/

open LinearAQFT BosonicLean.Weyl QCALean.Core Matrix
open scoped ComplexOrder ComplexConjugate

namespace QCALean.Bosonic

/-! ### Site vectors and cell coefficients -/

section Site

variable {G : Type*} [AddCommGroup G] {n : ℕ}

/-- The vector `e_{x,i}`: the `i`-th unit vector at the site `x`. -/
noncomputable def siteVec (x : G) (i : Gaussian.PhaseIndex n) : PhaseVec G n :=
  Pi.single i (AddMonoidAlgebra.single x 1)

theorem coeff_siteVec (x : G) (i k : Gaussian.PhaseIndex n) :
    (siteVec x i k).coeff = if k = i then Finsupp.single x 1 else 0 := by
  by_cases h : k = i
  · subst h; simp only [siteVec, Pi.single_eq_same, ite_true]; rfl
  · simp [siteVec, h]

/-- Induction over phase-space vectors: the vectors `r e_{x,i}` span. -/
theorem phaseVec_induction {P : PhaseVec G n → Prop} (u : PhaseVec G n) (h0 : P 0)
    (hadd : ∀ u w, P u → P w → P (u + w)) (hs : ∀ x i (r : ℝ), P (r • siteVec x i)) : P u := by
  classical
  rw [← Finset.univ_sum_single u]
  refine Finset.sum_induction _ P hadd h0 fun i _ => ?_
  induction u i using AddMonoidAlgebra.induction_linear with
  | zero => rw [Pi.single_zero]; exact h0
  | add p q hp hq => rw [Pi.single_add]; exact hadd _ _ hp hq
  | single x r =>
    convert hs x i r using 1
    rw [siteVec, ← Pi.single_smul', AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- Two bilinear forms agreeing on the site vectors are equal. -/
theorem bilinForm_ext_siteVec {B B' : LinearMap.BilinForm ℝ (PhaseVec G n)}
    (h : ∀ x i y j, B (siteVec x i) (siteVec y j) = B' (siteVec x i) (siteVec y j)) :
    B = B' := by
  refine LinearMap.ext₂ fun u w => ?_
  induction u using phaseVec_induction with
  | h0 => simp
  | hadd u u' hu hu' => simp [hu, hu']
  | hs x i r =>
    simp only [map_smul, LinearMap.smul_apply]
    congr 1
    induction w using phaseVec_induction with
    | h0 => simp
    | hadd w w' hw hw' => simp [hw, hw']
    | hs y j r' => simp [h]

end Site

section Cells

variable {n : ℕ}

/-- The pairing `Σ_{x,y} p(x) c_{x−y} q(y)` of two finitely supported sequences. -/
noncomputable def cellPair (c : ℤ → ℝ) (p q : ℤ →₀ ℝ) : ℝ :=
  p.sum fun x a => q.sum fun y b => a * c (x - y) * b

theorem cellPair_eq_sum (c : ℤ → ℝ) {p q : ℤ →₀ ℝ} {A B : Finset ℤ} (hp : p.support ⊆ A)
    (hq : q.support ⊆ B) :
    cellPair c p q = ∑ x ∈ A, ∑ y ∈ B, p x * c (x - y) * q y := by
  rw [cellPair, Finsupp.sum_of_support_subset p hp _ (fun _ _ => by simp)]
  exact Finset.sum_congr rfl fun x _ =>
    Finsupp.sum_of_support_subset q hq _ (fun _ _ => by simp)

theorem cellPair_add_left (c : ℤ → ℝ) (p p' q : ℤ →₀ ℝ) :
    cellPair c (p + p') q = cellPair c p q + cellPair c p' q := by
  classical
  rw [cellPair_eq_sum c (Finsupp.support_add (g₁ := p) (g₂ := p')) subset_rfl,
    cellPair_eq_sum c (Finset.subset_union_left (s₂ := p'.support)) subset_rfl,
    cellPair_eq_sum c (Finset.subset_union_right (s₁ := p.support)) subset_rfl,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by simp only [Finsupp.add_apply]; ring

theorem cellPair_add_right (c : ℤ → ℝ) (p q q' : ℤ →₀ ℝ) :
    cellPair c p (q + q') = cellPair c p q + cellPair c p q' := by
  classical
  rw [cellPair_eq_sum c subset_rfl (Finsupp.support_add (g₁ := q) (g₂ := q')),
    cellPair_eq_sum c subset_rfl (Finset.subset_union_left (s₂ := q'.support)),
    cellPair_eq_sum c subset_rfl (Finset.subset_union_right (s₁ := q.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by simp only [Finsupp.add_apply]; ring

theorem cellPair_smul_left (c : ℤ → ℝ) (r : ℝ) (p q : ℤ →₀ ℝ) :
    cellPair c (r • p) q = r * cellPair c p q := by
  classical
  rw [cellPair_eq_sum c (Finsupp.support_smul) subset_rfl,
    cellPair_eq_sum c subset_rfl subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by simp only [Finsupp.smul_apply, smul_eq_mul]; ring

theorem cellPair_smul_right (c : ℤ → ℝ) (r : ℝ) (p q : ℤ →₀ ℝ) :
    cellPair c p (r • q) = r * cellPair c p q := by
  classical
  rw [cellPair_eq_sum c subset_rfl (Finsupp.support_smul),
    cellPair_eq_sum c subset_rfl subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by simp only [Finsupp.smul_apply, smul_eq_mul]; ring

/-- Milestone Q3, Definition 20: the covariance form of cell coefficients,
`γ(u,w) = Σ_{x,y} u(x)ᵀ γ_{x−y} w(y)`. (notes: `def:gs-cells`) -/
noncomputable def cellForm (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    LinearMap.BilinForm ℝ (PhaseVec ℤ n) :=
  LinearMap.mk₂ ℝ
    (fun u w => ∑ i, ∑ j, cellPair (fun x => γc x i j) (u i).coeff (w j).coeff)
    (fun u u' w => by
      simp only [Pi.add_apply, AddMonoidAlgebra.coeff_add, cellPair_add_left,
        Finset.sum_add_distrib])
    (fun r u w => by
      simp only [Pi.smul_apply, AddMonoidAlgebra.coeff_smul, cellPair_smul_left, smul_eq_mul,
        Finset.mul_sum])
    (fun u w w' => by
      simp only [Pi.add_apply, AddMonoidAlgebra.coeff_add, cellPair_add_right,
        Finset.sum_add_distrib])
    (fun r u w => by
      simp only [Pi.smul_apply, AddMonoidAlgebra.coeff_smul, cellPair_smul_right, smul_eq_mul,
        Finset.mul_sum])

/-- (notes: `def:gs-cells`) -/
theorem cellForm_apply (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (u w : PhaseVec ℤ n) :
    cellForm γc u w = ∑ i, ∑ j, cellPair (fun x => γc x i j) (u i).coeff (w j).coeff := rfl

/-- The covariance form on site vectors: `γ(e_{x,i}, e_{y,j}) = (γ_{x−y})_{ij}`. -/
theorem cellForm_siteVec (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (x y : ℤ) (i j : Gaussian.PhaseIndex n) :
    cellForm γc (siteVec x i) (siteVec y j) = γc (x - y) i j := by
  rw [cellForm_apply, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp only [coeff_siteVec, ite_true]
    rw [cellPair_eq_sum _ Finsupp.support_single_subset Finsupp.support_single_subset]
    simp
  · intro l _ hl
    simp [coeff_siteVec, hl, cellPair]
  · simp
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [coeff_siteVec, hk, cellPair]
  · simp

/-- Milestone Q3, Definition 20: admissible cell data, absolutely summable and symmetric,
`γ_{−x} = γ_xᵀ`. (notes: `def:gs-cells`) -/
structure CellData (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    Prop where
  summable : ∀ i j, Summable fun x => |γc x i j|
  symm : ∀ x, γc (-x) = (γc x)ᵀ

/-- Milestone Q3, Lemma 21(a): the covariance form of symmetric cells is symmetric.
(notes: `lem:gs-cells`) -/
theorem cellForm_isSymm {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ x, γc (-x) = (γc x)ᵀ) : (cellForm γc).IsSymm := by
  have e : cellForm γc = (cellForm γc).flip := bilinForm_ext_siteVec fun x i y j => by
    rw [LinearMap.BilinForm.flip_apply, cellForm_siteVec, cellForm_siteVec, ← neg_sub, h,
      Matrix.transpose_apply]
  exact ⟨fun u w => by conv_lhs => rw [e, LinearMap.BilinForm.flip_apply]⟩

theorem translate_siteVec {G : Type*} [AddCommGroup G] (a x : G) (i : Gaussian.PhaseIndex n) :
    translate ℝ G _ a (siteVec x i) = siteVec (a + x) i := by
  funext k
  by_cases h : k = i
  · subst h
    simp only [translate_apply, siteVec, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      AddMonoidAlgebra.single_mul_single, mul_one]
  · simp [translate_apply, siteVec, h]

/-- Milestone Q3, Lemma 21(a): the covariance form of cells is translation invariant.
(notes: `lem:gs-cells`) -/
theorem cellForm_translate (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (a : ℤ) (u w : PhaseVec ℤ n) :
    cellForm γc (translate ℝ ℤ _ a u) (translate ℝ ℤ _ a w) = cellForm γc u w := by
  have e : (cellForm γc).comp (translate ℝ ℤ _ a) (translate ℝ ℤ _ a) = cellForm γc :=
    bilinForm_ext_siteVec fun x i y j => by
      rw [LinearMap.BilinForm.comp_apply, translate_siteVec, translate_siteVec,
        cellForm_siteVec, cellForm_siteVec, add_sub_add_left_eq_sub]
  exact congrArg (fun B : LinearMap.BilinForm ℝ (PhaseVec ℤ n) => B u w) e

/-- The exponents occurring in a (possibly rectangular) Laurent matrix.
(notes: `def:lc-pullback`) -/
noncomputable def laurentSupport {ι κ : Type*} [Fintype ι] [Fintype κ] (Ls : Matrix κ ι L) :
    Finset ℤ :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => (Ls i j).coeff.support

/-- The coefficient matrix of `z^m` in a (possibly rectangular) Laurent matrix.
(notes: `def:lc-pullback`) -/
noncomputable def laurentCoeff {ι κ : Type*} (Ls : Matrix κ ι L) (m : ℤ) : Matrix κ ι ℝ :=
  Matrix.of fun i j => (Ls i j).coeff m

/-- Milestone Q5b: the pull-back cells `(L*ν)_d = Σ_{m,m'} ℓ_mᵀ ν_{d+m−m'} ℓ_{m'}`, which represent
the form `ν(L·, L·)` (`cellForm_pullbackKernel`). For a square symbol they are the evolved cells of
Q3 (`pullbackKernel_eq_evolveCells`), with Fourier symbol `L̂(k)* ν̂(k) L̂(k)` for summable cells
(`gammaHat_pullbackKernel`). (notes: `def:lc-pullback`) -/
noncomputable def pullbackKernel {ι κ : Type*} [Fintype ι] [Fintype κ] (Ls : Matrix κ ι L)
    (g : ℤ → Matrix κ κ ℝ) : ℤ → Matrix ι ι ℝ :=
  fun d => ∑ m ∈ laurentSupport Ls, ∑ m' ∈ laurentSupport Ls,
    (laurentCoeff Ls m)ᵀ * g (d + m - m') * laurentCoeff Ls m'

/-- Milestone Q5b: the on-site cells `δ_{x,0} g₀`. (notes: `def:lc-pullback`) -/
noncomputable def onSiteKernel {ι : Type*} (g0 : Matrix ι ι ℝ) : ℤ → Matrix ι ι ℝ :=
  fun x => if x = 0 then g0 else 0

/-- The entries of a coefficient matrix. -/
@[simp]
theorem laurentCoeff_apply {ι κ : Type*} (Ls : Matrix κ ι L) (m : ℤ) (k : κ) (i : ι) :
    laurentCoeff Ls m k i = (Ls k i).coeff m :=
  rfl

/-- On-site cells at the origin. -/
@[simp]
theorem onSiteKernel_zero {ι : Type*} (g0 : Matrix ι ι ℝ) : onSiteKernel g0 0 = g0 :=
  ite_eq_left rfl

/-- On-site cells vanish away from the origin. -/
@[simp]
theorem onSiteKernel_of_ne {ι : Type*} (g0 : Matrix ι ι ℝ) {x : ℤ} (hx : x ≠ 0) :
    onSiteKernel g0 x = 0 :=
  ite_eq_right hx

/-- For a square symbol, the exponent set is the range of the symbol. -/
theorem laurentSupport_eq_symbolRange {ι : Type*} [Fintype ι] (Ls : Matrix ι ι L) :
    laurentSupport Ls = symbolRange Ls :=
  rfl

/-- For a square symbol, the coefficient matrices are the matrices `coeffMat` used for the evolved
cells of Q3. -/
theorem laurentCoeff_eq_coeffMat {ι : Type*} (Ls : Matrix ι ι L) (m : ℤ) :
    laurentCoeff Ls m = coeffMat m Ls :=
  rfl

/-- The support of an entry lies in the exponent set of a Laurent matrix. -/
theorem support_coeff_subset_laurentSupport {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ls : Matrix κ ι L) (k : κ) (i : ι) : (Ls k i).coeff.support ⊆ laurentSupport Ls :=
  fun _ hz =>
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hz⟩⟩

/-- The coefficients of the image of a site vector under a rectangular symbol. -/
theorem coeff_toLin'_siteVec_rect {m : ℕ}
    (C : Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex n) L) (x : ℤ)
    (i : Gaussian.PhaseIndex n) (k : Gaussian.PhaseIndex m) (z : ℤ) :
    (Matrix.toLin' C (siteVec x i) k).coeff z = (C k i).coeff (z - x) := by
  simp only [Matrix.toLin'_apply, siteVec, Matrix.mulVec_single, Pi.smul_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, AddMonoidAlgebra.coeff_mul_single_apply,
    mul_one, sub_eq_add_neg]
  rfl

/-- The image of a site vector under a rectangular symbol is supported near the site. -/
theorem support_toLin'_siteVec_rect {m : ℕ}
    (C : Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex n) L) (x : ℤ)
    (i : Gaussian.PhaseIndex n) (k : Gaussian.PhaseIndex m) :
    (Matrix.toLin' C (siteVec x i) k).coeff.support ⊆ (laurentSupport C).image (· + x) := by
  intro z hz
  rw [Finsupp.mem_support_iff, coeff_toLin'_siteVec_rect] at hz
  exact Finset.mem_image.2 ⟨z - x, support_coeff_subset_laurentSupport C k i
    (Finsupp.mem_support_iff.2 hz), sub_add_cancel z x⟩

/-- Lemma 20 for a rectangular symbol. -/
theorem cellForm_pullbackKernel_rect {m : ℕ}
    (C : Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex n) L)
    (g : ℤ → Matrix (Gaussian.PhaseIndex m) (Gaussian.PhaseIndex m) ℝ) :
    cellForm (pullbackKernel C g) =
      (cellForm g).comp ((Matrix.toLin' C).restrictScalars ℝ)
        ((Matrix.toLin' C).restrictScalars ℝ) := by
  refine bilinForm_ext_siteVec fun x i y j => ?_
  rw [LinearMap.BilinForm.comp_apply, cellForm_siteVec, cellForm_apply]
  simp only [LinearMap.restrictScalars_apply]
  simp only [cellPair_eq_sum _ (support_toLin'_siteVec_rect C x i _)
    (support_toLin'_siteVec_rect C y j _), coeff_toLin'_siteVec_rect]
  rw [pullbackKernel]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply, laurentCoeff,
    Matrix.of_apply, Finset.sum_mul]
  simp only [Finset.sum_image (fun a _ b _ (h : a + x = b + x) => add_right_cancel h),
    Finset.sum_image (fun a _ b _ (h : a + y = b + y) => add_right_cancel h),
    add_sub_cancel_right]
  symm
  set S := laurentSupport C
  let F : Gaussian.PhaseIndex m → Gaussian.PhaseIndex m → ℤ → ℤ → ℝ := fun k l a b =>
    (C k i).coeff a * g (x - y + a - b) k l * (C l j).coeff b
  calc ∑ k, ∑ l, ∑ a ∈ S, ∑ b ∈ S,
        (C k i).coeff a * g (a + x - (b + y)) k l * (C l j).coeff b
      = ∑ k, ∑ l, ∑ a ∈ S, ∑ b ∈ S, F k l a b := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        simp only [F]
        congr 3
        ring
    _ = ∑ k, ∑ a ∈ S, ∑ l, ∑ b ∈ S, F k l a b :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ k, ∑ l, ∑ b ∈ S, F k l a b := Finset.sum_comm
    _ = ∑ a ∈ S, ∑ k, ∑ b ∈ S, ∑ l, F k l a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ b ∈ S, ∑ k, ∑ l, F k l a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ b ∈ S, ∑ l, ∑ k, F k l a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- Milestone Q3, Theorem 30: the cells of the evolved covariance,
`γ'_j = Σ_{m,m'} ℓ_mᵀ γ_{j+m−m'} ℓ_{m'}` (thesis (4.17a)), the square case of the pull-back cells
`pullbackKernel`. (notes: `thm:gs-evolution`) -/
noncomputable def evolveCells (M : Sym ℤ n)
    (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ :=
  pullbackKernel M γc

/-- The evolved cells as the double sum (4.17a). -/
theorem evolveCells_apply (M : Sym ℤ n)
    (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) (j : ℤ) :
    evolveCells M γc j = ∑ m ∈ symbolRange M, ∑ m' ∈ symbolRange M,
      (coeffMat m M)ᵀ * γc (j + m - m') * coeffMat m' M :=
  rfl

theorem support_coeff_subset_symbolRange (M : Sym ℤ n) (k i : Gaussian.PhaseIndex n) :
    (M k i).coeff.support ⊆ symbolRange M :=
  support_coeff_subset_laurentSupport M k i

theorem coeff_toLin'_siteVec (M : Sym ℤ n) (x : ℤ) (i k : Gaussian.PhaseIndex n) (z : ℤ) :
    (Matrix.toLin' M (siteVec x i) k).coeff z = (M k i).coeff (z - x) :=
  coeff_toLin'_siteVec_rect M x i k z

theorem support_toLin'_siteVec (M : Sym ℤ n) (x : ℤ) (i k : Gaussian.PhaseIndex n) :
    (Matrix.toLin' M (siteVec x i) k).coeff.support ⊆ (symbolRange M).image (· + x) :=
  support_toLin'_siteVec_rect M x i k

/-- Milestone Q3, Theorem 30: `(γ'_j)` is the cell data of `γ(L·, L·)`; the square case of
`cellForm_pullbackKernel_rect`. (notes: `thm:gs-evolution`) -/
theorem cellForm_evolve (M : Sym ℤ n)
    (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) (u w : PhaseVec ℤ n) :
    cellForm γc (Matrix.toLin' M u) (Matrix.toLin' M w) = cellForm (evolveCells M γc) u w := by
  have e : (cellForm γc).comp ((Matrix.toLin' M).restrictScalars ℝ)
      ((Matrix.toLin' M).restrictScalars ℝ) = cellForm (evolveCells M γc) :=
    (cellForm_pullbackKernel_rect M γc).symm
  exact congrArg (fun B : LinearMap.BilinForm ℝ (PhaseVec ℤ n) => B u w) e

/-- Milestone Q3, Theorem 30: the evolved cells are symmetric. -/
theorem evolveCells_symm (M : Sym ℤ n)
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ x, γc (-x) = (γc x)ᵀ) (j : ℤ) : evolveCells M γc (-j) = (evolveCells M γc j)ᵀ := by
  simp only [evolveCells_apply, Matrix.transpose_sum, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  rw [← h, show -j + m' - m = -(j + m - m') by ring, Matrix.mul_assoc]

/-- Milestone Q3, Theorem 30: the evolved cells are absolutely summable. -/
theorem evolveCells_summable (M : Sym ℤ n)
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (a b : Gaussian.PhaseIndex n) :
    Summable fun j => |evolveCells M γc j a b| := by
  set S := symbolRange M
  have hsum : Summable fun j => ∑ m ∈ S, ∑ m' ∈ S, ∑ k, ∑ l,
      |(coeffMat m M) k a| * |γc (j + (m - m')) k l| * |(coeffMat m' M) l b| := by
    refine summable_sum fun m _ => summable_sum fun m' _ => summable_sum fun k _ =>
      summable_sum fun l _ => ?_
    exact ((h k l).comp_injective (add_left_injective (m - m'))).mul_left _ |>.mul_right _
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun j => ?_) hsum
  simp only [evolveCells_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m' _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun k _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun l _ => ?_
  rw [abs_mul, abs_mul, add_sub_assoc]

/-- Milestone Q3, Theorem 30: the evolved cells are admissible cell data.
(notes: `thm:gs-evolution`) -/
theorem evolveCells_cellData (M : Sym ℤ n)
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc) :
    CellData (evolveCells M γc) :=
  ⟨evolveCells_summable M h.summable, evolveCells_symm M h.symm⟩

theorem norm_exp_phase (k : ℝ) (x : ℤ) : ‖Complex.exp (-(k : ℂ) * x * Complex.I)‖ = 1 := by
  have := Complex.norm_exp_ofReal_mul_I (-k * x)
  push_cast at this
  exact this

theorem summable_smul_cells
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (c : ℤ → ℂ) (hc : ∀ x, ‖c x‖ ≤ 1) :
    Summable fun x => c x • (γc x).map (Complex.ofReal) := by
  refine Pi.summable.2 fun i => Pi.summable.2 fun j => ?_
  refine Summable.of_norm_bounded (h i j) fun x => ?_
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (hc x)

theorem tsum_matrix_apply {ι : Type*} {f : ℤ → Matrix ι ι ℂ} (hf : Summable f) (a b : ι) :
    (∑' x, f x) a b = ∑' x, f x a b := by
  exact (congrFun (Pi.tsum_apply (f := fun x => (f x : ι → ι → ℂ)) hf (x := a)) b).trans
    (Pi.tsum_apply (Pi.summable.1 hf a))

/-- Milestone Q3, Definition 20: the symbol `γ̂(k) = Σ_x γ_x e^{−ikx}` (thesis (4.14)).
(notes: `def:gs-cells`) -/
noncomputable def gammaHat (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)
    (k : ℝ) : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℂ :=
  ∑' x : ℤ, Complex.exp (-(k : ℂ) * x * Complex.I) • (γc x).map Complex.ofReal

theorem gammaHat_apply {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (k : ℝ) (a b : Gaussian.PhaseIndex n) :
    gammaHat γc k a b = ∑' x : ℤ, Complex.exp (-(k : ℂ) * x * Complex.I) * γc x a b := by
  have hs := summable_smul_cells h _ fun x => (norm_exp_phase k x).le
  rw [gammaHat, tsum_matrix_apply hs]
  rfl

theorem summable_phase_mul {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (k : ℝ) (a b : Gaussian.PhaseIndex n) :
    Summable fun x : ℤ => Complex.exp (-(k : ℂ) * x * Complex.I) * γc x a b :=
  Pi.summable.1 (Pi.summable.1 (summable_smul_cells h _ fun x => (norm_exp_phase k x).le) a) b

/-- Milestone Q3, Lemma 21(b): `γ̂` is continuous. (notes: `lem:gs-cells`) -/
theorem continuous_gammaHat
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) : Continuous (gammaHat γc) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  have e : (fun k => gammaHat γc k a b) =
      fun k : ℝ => ∑' x : ℤ, Complex.exp (-(k : ℂ) * x * Complex.I) * γc x a b :=
    funext fun k => gammaHat_apply h k a b
  rw [e]
  refine continuous_tsum (fun x => by fun_prop) (h a b) fun x k => ?_
  rw [norm_mul, norm_exp_phase, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Milestone Q3, Lemma 21(b): `γ̂(−k) = conj γ̂(k)`. (notes: `lem:gs-cells`) -/
theorem gammaHat_neg {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (k : ℝ) :
    gammaHat γc (-k) = (gammaHat γc k).map (starRingEnd ℂ) := by
  ext a b
  rw [Matrix.map_apply, gammaHat_apply h, gammaHat_apply h, Complex.conj_tsum]
  refine tsum_congr fun x => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_ofReal]

/-- Milestone Q3, Lemma 21(b): `γ̂(k)` is Hermitian. (notes: `lem:gs-cells`) -/
theorem gammaHat_isHermitian
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (k : ℝ) : (gammaHat γc k).IsHermitian := by
  ext a b
  rw [Matrix.conjTranspose_apply, gammaHat_apply h.summable, gammaHat_apply h.summable,
    Complex.star_def, Complex.conj_tsum, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Equiv.neg_apply, h.symm,
    Matrix.transpose_apply]
  congr 2
  simp [Complex.conj_ofReal]

theorem map_ofReal_sum {ι α : Type*} (s : Finset α) (f : α → Matrix ι ι ℝ) :
    (∑ a ∈ s, f a).map Complex.ofReal = ∑ a ∈ s, (f a).map Complex.ofReal :=
  map_sum (Complex.ofRealHom.toAddMonoidHom.mapMatrix) f s

theorem map_ofReal_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- The Fourier symbol of a rule as a finite sum, `L̂(k) = Σ_m ℓ_m e^{−ikm}`. -/
theorem fourierSymbol_eq_sum (M : Sym ℤ n) (k : ℝ) :
    fourierSymbol k M = ∑ m ∈ symbolRange M,
      Complex.exp (-(k : ℂ) * m * Complex.I) • (coeffMat m M).map Complex.ofReal := by
  ext a b
  rw [fourierSymbol, Matrix.map_apply, evalCircle_apply, Matrix.sum_apply,
    Finsupp.sum_of_support_subset _ (support_coeff_subset_symbolRange M a b) _
      (fun _ _ => by simp)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeffMat, mul_comm]

theorem summable_shift_cells
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (d : ℤ) :
    ∀ i j, Summable fun x => |γc (x + d) i j| :=
  fun i j => (h i j).comp_injective (add_left_injective d)

theorem tsum_phase_shift {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (k : ℝ) (d : ℤ) :
    ∑' j : ℤ, Complex.exp (-(k : ℂ) * j * Complex.I) • (γc (j + d)).map Complex.ofReal =
      Complex.exp ((k : ℂ) * d * Complex.I) • gammaHat γc k := by
  calc _ = ∑' j : ℤ, Complex.exp ((k : ℂ) * d * Complex.I) •
        (Complex.exp (-(k : ℂ) * ((j + d : ℤ) : ℂ) * Complex.I) •
          (γc (j + d)).map Complex.ofReal) := by
        refine tsum_congr fun j => ?_
        rw [smul_smul, ← Complex.exp_add]
        congr 2
        push_cast
        ring
    _ = ∑' x : ℤ, Complex.exp ((k : ℂ) * d * Complex.I) •
        (Complex.exp (-(k : ℂ) * x * Complex.I) • (γc x).map Complex.ofReal) :=
        (Equiv.addRight d).tsum_eq (fun x : ℤ => Complex.exp ((k : ℂ) * d * Complex.I) •
          (Complex.exp (-(k : ℂ) * x * Complex.I) • (γc x).map Complex.ofReal))
    _ = _ := Summable.tsum_const_smul _ (summable_smul_cells h _ fun x => (norm_exp_phase k x).le)

/-- Milestone Q3, Theorem 30 (thesis (4.17), general form): the symbol of the evolved cells is
`γ̂'(k) = L̂(−k)ᵀ γ̂(k) L̂(k)`. (notes: `thm:gs-evolution`) -/
theorem gammaHat_evolve (M : Sym ℤ n)
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (k : ℝ) :
    gammaHat (evolveCells M γc) k =
      (fourierSymbol (-k) M)ᵀ * gammaHat γc k * fourierSymbol k M := by
  set S := symbolRange M
  set A : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℂ :=
    fun m => (coeffMat m M).map Complex.ofReal
  set e : ℝ → ℤ → ℂ := fun k m => Complex.exp (-(k : ℂ) * m * Complex.I)
  have hsum : ∀ m m', Summable fun j : ℤ => (A m)ᵀ *
      (e k j • (γc (j + (m - m'))).map Complex.ofReal) * A m' := fun m m' =>
    ((summable_smul_cells (summable_shift_cells h (m - m')) _
      fun x => (norm_exp_phase k x).le).mul_left _).mul_right _
  have hterm : ∀ j : ℤ, e k j • (evolveCells M γc j).map Complex.ofReal =
      ∑ m ∈ S, ∑ m' ∈ S, (A m)ᵀ * (e k j • (γc (j + (m - m'))).map Complex.ofReal) * A m' := by
    intro j
    simp only [evolveCells_apply, A, map_ofReal_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    rw [map_ofReal_mul, map_ofReal_mul, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul,
      add_sub_assoc]
  calc gammaHat (evolveCells M γc) k
      = ∑' j : ℤ, ∑ m ∈ S, ∑ m' ∈ S,
          (A m)ᵀ * (e k j • (γc (j + (m - m'))).map Complex.ofReal) * A m' :=
        tsum_congr hterm
    _ = ∑ m ∈ S, ∑ m' ∈ S, (A m)ᵀ *
          (∑' j : ℤ, e k j • (γc (j + (m - m'))).map Complex.ofReal) * A m' := by
        rw [Summable.tsum_finsetSum fun m _ => summable_sum fun m' _ => hsum m m']
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Summable.tsum_finsetSum fun m' _ => hsum m m']
        refine Finset.sum_congr rfl fun m' _ => ?_
        rw [Summable.tsum_mul_right _ (((summable_smul_cells (summable_shift_cells h (m - m')) _
          fun x => (norm_exp_phase k x).le).mul_left _)), Summable.tsum_mul_left _
          (summable_smul_cells (summable_shift_cells h (m - m')) _
            fun x => (norm_exp_phase k x).le)]
    _ = ∑ m ∈ S, ∑ m' ∈ S, (A m)ᵀ *
          (Complex.exp ((k : ℂ) * ((m - m' : ℤ) : ℂ) * Complex.I) • gammaHat γc k) * A m' := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
        rw [← tsum_phase_shift h k (m - m')]
    _ = _ := by
        rw [fourierSymbol_eq_sum, fourierSymbol_eq_sum, Matrix.transpose_sum, Finset.sum_mul,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m' _ => ?_
        simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          ← Complex.exp_add, A]
        congr 2
        push_cast
        ring

/-- `L̂(−k) = conj L̂(k)` for a real symbol. -/
theorem fourierSymbol_neg (M : Sym ℤ n) (k : ℝ) :
    fourierSymbol (-k) M = (fourierSymbol k M).map (starRingEnd ℂ) := by
  rw [fourierSymbol_eq_sum, fourierSymbol_eq_sum]
  ext a b
  simp only [Matrix.map_apply, Matrix.sum_apply, map_sum, Matrix.smul_apply, smul_eq_mul,
    map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 2
  simp [Complex.conj_ofReal]

/-- Milestone Q3, Theorem 30: `γ̂'(k) = L̂(k)ᴴ γ̂(k) L̂(k)`, a congruence at each `k`.
(notes: `thm:gs-evolution`) -/
theorem gammaHat_evolve_conjTranspose (M : Sym ℤ n)
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (k : ℝ) :
    gammaHat (evolveCells M γc) k =
      (fourierSymbol k M)ᴴ * gammaHat γc k * fourierSymbol k M := by
  rw [gammaHat_evolve M h, fourierSymbol_neg]
  rfl

/-- Milestone Q3, Theorem 30: for a reflection-symmetric rule, `ℓ_{−m} = ℓ_m`, the printed form
(4.17b), `γ̂'(k) = L̂(k)ᵀ γ̂(k) L̂(k)`. (notes: `thm:gs-evolution`) -/
theorem gammaHat_evolve_of_symm (M : Sym ℤ n)
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (hM : ∀ m, coeffMat (-m) M = coeffMat m M)
    (k : ℝ) :
    gammaHat (evolveCells M γc) k = (fourierSymbol k M)ᵀ * gammaHat γc k * fourierSymbol k M := by
  rw [gammaHat_evolve M h]
  congr 2
  ext b a
  simp only [Matrix.transpose_apply, fourierSymbol, Matrix.map_apply, evalCircle_apply]
  have hc : ∀ m, (M a b).coeff (-m) = (M a b).coeff m := fun m => by
    simpa [coeffMat] using congrFun (congrFun (hM m) a) b
  classical
  set T := (M a b).coeff.support ∪ (M a b).coeff.support.image Neg.neg
  have hT : (M a b).coeff.support ⊆ T := Finset.subset_union_left
  rw [Finsupp.sum_of_support_subset _ hT _ (fun _ _ => by simp),
    Finsupp.sum_of_support_subset _ hT _ (fun _ _ => by simp)]
  have hmem : ∀ z, z ∈ T ↔ (M a b).coeff z ≠ 0 := fun z => by
    simp only [T, Finset.mem_union, Finset.mem_image, Finsupp.mem_support_iff]
    constructor
    · rintro (h1 | ⟨w, hw, rfl⟩)
      · exact h1
      · rwa [hc]
    · exact Or.inl
  have hTneg : T.map (Equiv.neg ℤ).toEmbedding = T := by
    ext z
    rw [Finset.mem_map_equiv, hmem, hmem, Equiv.neg_symm, Equiv.neg_apply, hc]
  conv_rhs => rw [← hTneg, Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Equiv.coe_toEmbedding, Equiv.neg_apply, hc]
  congr 2
  push_cast
  ring

/-- Milestone Q4a, Proposition 1(a): the symbol of cells is `2π`-periodic; the identity holds
term by term, so no summability is needed. (notes: `prop:es-iterate`) -/
theorem gammaHat_add_two_pi
    (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) (k : ℝ) :
    gammaHat γc (k + 2 * Real.pi) = gammaHat γc k := by
  refine tsum_congr fun x => ?_
  congr 1
  have : -((k + 2 * Real.pi : ℝ) : ℂ) * x * Complex.I =
      -(k : ℂ) * x * Complex.I + ((-x : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Cell data are determined by their covariance form. -/
theorem cells_eq_of_cellForm_eq
    {γc γc' : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ u w, cellForm γc u w = cellForm γc' u w) : γc = γc' := by
  funext x
  ext i j
  have := h (siteVec x i) (siteVec 0 j)
  rwa [cellForm_siteVec, cellForm_siteVec, sub_zero] at this

/-- Milestone Q4a, Proposition 2(a): the identity rule leaves cell data unchanged.
(notes: `prop:es-iterate`) -/
theorem evolveCells_one (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    evolveCells 1 γc = γc :=
  cells_eq_of_cellForm_eq fun u w => by
    rw [← cellForm_evolve, Matrix.toLin'_one, LinearMap.id_apply, LinearMap.id_apply]

/-- Milestone Q4a, Proposition 2(a): `(MN)_* γ = N_*(M_* γ)`. (notes: `prop:es-iterate`) -/
theorem evolveCells_mul (M N : Sym ℤ n)
    (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    evolveCells (M * N) γc = evolveCells N (evolveCells M γc) :=
  cells_eq_of_cellForm_eq fun u w => by
    rw [← cellForm_evolve, ← cellForm_evolve, ← cellForm_evolve, Matrix.toLin'_mul,
      LinearMap.comp_apply, LinearMap.comp_apply]

/-- Milestone Q4a, Proposition 2(b): `(M_*)^t γ = (M^t)_* γ`. (notes: `prop:es-iterate`) -/
theorem evolveCells_iterate (M : Sym ℤ n)
    (γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) (t : ℕ) :
    (evolveCells M)^[t] γc = evolveCells (M ^ t) γc := by
  induction t with
  | zero => rw [Function.iterate_zero_apply, pow_zero, evolveCells_one]
  | succ t ih => rw [Function.iterate_succ_apply', ih, pow_succ, evolveCells_mul]

/-- Milestone Q4a, Proposition 2(c): the iterates preserve admissibility.
(notes: `prop:es-iterate`) -/
theorem cellData_iterate (M : Sym ℤ n)
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (t : ℕ) : CellData ((evolveCells M)^[t] γc) := by
  induction t with
  | zero => exact h
  | succ t ih => rw [Function.iterate_succ_apply']; exact evolveCells_cellData M ih

/-- The symbol entry as a series with the phase on the right. -/
theorem gammaHat_apply'
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (h : ∀ i j, Summable fun x => |γc x i j|) (k : ℝ) (a b : Gaussian.PhaseIndex n) :
    gammaHat γc k a b = ∑' m : ℤ, (γc m a b : ℂ) * Complex.exp (-(k : ℂ) * m * Complex.I) := by
  rw [gammaHat_apply h]
  exact tsum_congr fun m => mul_comm _ _

/-- Milestone Q4a, Lemma 5: reflection-symmetric cells have an even symbol. The identity holds
term by term, so no summability is needed. (notes: `lem:es-refl`) -/
theorem gammaHat_neg_of_refl
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hr : ∀ x, γc (-x) = γc x) (k : ℝ) : gammaHat γc (-k) = gammaHat γc k := by
  rw [gammaHat, gammaHat, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [Equiv.neg_apply, hr]
  congr 2
  push_cast
  ring

/-- Milestone Q4a, Lemma 5: reflection-symmetric cells have a real symmetric symbol, namely its
entrywise real part. (notes: `lem:es-refl`) -/
theorem gammaHat_real
    {γc : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ} (h : CellData γc)
    (hr : ∀ x, γc (-x) = γc x) (k : ℝ) :
    gammaHat γc k = ((gammaHat γc k).map Complex.re).map Complex.ofReal ∧
      ((gammaHat γc k).map Complex.re)ᵀ = (gammaHat γc k).map Complex.re := by
  have hc : ∀ a b, conj (gammaHat γc k a b) = gammaHat γc k a b := fun a b => by
    have := congrFun (congrFun (gammaHat_neg h.summable k) a) b
    rw [gammaHat_neg_of_refl hr, Matrix.map_apply] at this
    exact this.symm
  have hre : gammaHat γc k = ((gammaHat γc k).map Complex.re).map Complex.ofReal := by
    ext a b
    exact (Complex.conj_eq_iff_re.1 (hc a b)).symm
  refine ⟨hre, ?_⟩
  ext a b
  have := (gammaHat_isHermitian h k).apply a b
  rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.map_apply, ← this, Complex.star_def,
    Complex.conj_re]

end Cells

end QCALean.Bosonic
