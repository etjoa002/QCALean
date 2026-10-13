/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import QCALean.Bosonic.Kernels
import QCALean.Bosonic.Automaton
import BosonicLean.Weyl.Channel
import LinearAQFT.Symplectic.NetWeyl

/-!
# Irreversible Gaussian automata on the chain

Milestone Q5b. A Gaussian channel on the chain is a lattice channel if its linear map is the rule
of a symbol, its noise is the form of cell data and its displacement is translation invariant.
Lattice channels commute with the translations and are quantum cellular automata with the range of
the symbol as neighbourhood. Thesis Lemma 4.11 holds in both directions: finite propagation with
`N` holds iff the symbol has range in `N`, and factorization with respect to `M` (`0 ∈ M = −M`)
holds iff the noise cells and the cells of `σ(L·, L·)` vanish outside `M`. The file also proves
thesis Lemma 4.10(v) with explicit data, concatenation of lattice channels, and the lossy example
system.

## Main definitions and results

* `QCALean.Bosonic.IsLatticeChannel`
* `QCALean.Bosonic.IsLatticeChannel.toQCA`: lattice channels are QCA.
* `QCALean.Bosonic.IsLatticeChannel.isLocalWith_iff`,
  `QCALean.Bosonic.IsLatticeChannel.isFactorizing_iff`: thesis Lemma 4.11, both directions.
* `QCALean.Bosonic.exists_isFactorizing_not_isLocalWith`,
  `QCALean.Bosonic.exists_data_not_isFactorizing`: thesis Lemma 4.10(v).
* `QCALean.Bosonic.IsLatticeChannel.comp`: concatenation (thesis p. 96).
* `QCALean.Bosonic.lossy_example`: the lossy example system.

## Implementation notes

The local algebra of a region is the closed span of the Weyl operators supported in it
(`ccrNet_eq_closure_span`); statements about local algebras are reduced to Weyl operators by
continuity (LinearAQFT's `eqOn_ccrNet`, `map_mem_ccrNet`).
-/

open LinearAQFT LinearAQFT.Symplectic BosonicLean.Weyl QCALean.Core QCALean.Net Matrix Gaussian
open scoped ComplexOrder ComplexConjugate Pointwise CStarAlgebra

namespace QCALean.Bosonic

variable {n : ℕ}

local notation "Om" => Gaussian.symplecticForm

/-- Milestone Q5b, Definition 17: a Gaussian channel on the chain is a lattice channel with symbol
`Ls` and noise cells `g` if its linear map is the rule of `Ls`, its noise is the form of the cell
data `g`, and its displacement is translation invariant. (notes: `def:lc-channel`) -/
structure IsLatticeChannel (T : GaussianChannel (phaseSpace ℤ n).sigma) (Ls : Sym ℤ n)
    (g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) : Prop where
  lin_eq : T.lin = symbolLin Ls
  noise_eq : T.noise = cellForm g
  cellData : CellData g
  disp_translate : ∀ a u, T.disp (translateEquiv a u) = T.disp u

/-! ### Auxiliary lemmas: local algebras and their Weyl operators -/

/-- A site vector is supported at its site. -/
theorem supp_siteVec_subset (x : ℤ) (i : Gaussian.PhaseIndex n) :
    (LatticeSpace.supp (siteVec x i) : Set ℤ) ⊆ {x} := by
  intro y hy
  obtain ⟨k, hk⟩ := LatticeSpace.mem_supp.1 hy
  rw [coeff_siteVec] at hk
  split_ifs at hk with h
  · by_contra hyx
    exact hk (by simp [Ne.symm hyx])
  · exact absurd rfl hk

/-- On the chain, the Weyl operators of the test functions localized in `O` are the Weyl operators
of the vectors supported in `O`. -/
theorem weylSet_phaseSpace (O : Set ℤ) :
    weylSet (phaseSpace ℤ n) O = {a | ∃ u : PhaseVec ℤ n, (LatticeSpace.supp u : Set ℤ) ⊆ O ∧
      a = wCCR (phaseSpace ℤ n).sigma u} := by
  ext a
  rw [mem_weylSet]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, mem_locSubmodule_iff_supp.1 hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, mem_locSubmodule_iff_supp.2 hu, rfl⟩

/-- Milestone Q5b, Lemma 18(a): the local algebra of `O` is the closed span of its Weyl
operators; the lattice case of `LinearAQFT.Symplectic.coe_ccrNet_eq_closure_span`.
(notes: `lem:lc-weyl`) -/
theorem ccrNet_eq_closure_span (O : Set ℤ) :
    ((ccrNet (phaseSpace ℤ n) O : StarSubalgebra ℂ _) : Set (CCR (phaseSpace ℤ n).sigma)) =
      closure (Submodule.span ℂ {a | ∃ u : PhaseVec ℤ n,
        (LatticeSpace.supp u : Set ℤ) ⊆ O ∧ a = wCCR (phaseSpace ℤ n).sigma u}) := by
  rw [coe_ccrNet_eq_closure_span, weylSet_phaseSpace]

/-- Milestone Q5b, Lemma 18(b): a Weyl operator lies in the local algebra of `O` iff its vector
is supported in `O`; the lattice case of `LinearAQFT.Symplectic.wCCR_mem_ccrNet_iff_exists`.
(notes: `lem:lc-weyl`) -/
theorem wCCR_mem_ccrNet_iff (O : Set ℤ) (u : PhaseVec ℤ n) :
    wCCR (phaseSpace ℤ n).sigma u ∈ ccrNet (phaseSpace ℤ n) O ↔
      (LatticeSpace.supp u : Set ℤ) ⊆ O := by
  rw [wCCR_mem_ccrNet_iff_exists]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact mem_locSubmodule_iff_supp.1 hf
  · intro hu
    exact ⟨u, mem_locSubmodule_iff_supp.2 hu, rfl⟩

/-! ### Auxiliary lemmas: extension from Weyl operators, and the cell conditions -/

/-- The translation action on Weyl operators, `α_a(W(u)) = W(κ_a u)`. -/
private theorem ccrTranslate_wCCR' (a : Multiplicative ℤ) (u : PhaseVec ℤ n) :
    ccrTranslate ℤ n a (wCCR (phaseSpace ℤ n).sigma u) =
      wCCR (phaseSpace ℤ n).sigma (translateEquiv a.toAdd u) :=
  ccrTranslate_wCCR a.toAdd u

/-- The translation action as a continuous linear map. -/
private noncomputable def ccrTranslateCLM (a : Multiplicative ℤ) :
    CCR (phaseSpace ℤ n).sigma →L[ℂ] CCR (phaseSpace ℤ n).sigma :=
  ⟨(ccrTranslate ℤ n a).toAlgEquiv.toLinearMap, map_continuous (ccrTranslate ℤ n a)⟩

/-- The continuous linear map `ccrTranslateCLM a` is the translation action `α_a`. -/
private theorem ccrTranslateCLM_apply (a : Multiplicative ℤ) (x : CCR (phaseSpace ℤ n).sigma) :
    ccrTranslateCLM a x = ccrTranslate ℤ n a x := rfl

/-- A phase-space vector is the sum of its site components. -/
theorem eq_sum_siteVec (u : PhaseVec ℤ n) :
    u = ∑ x ∈ LatticeSpace.supp u, ∑ i, (u i).coeff x • siteVec x i := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, siteVec, Pi.single_apply, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply AddMonoidAlgebra.ext
  ext z
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ]
  split_ifs with hz
  · rfl
  · by_contra hne
    exact hz (LatticeSpace.mem_supp.2 ⟨k, hne⟩)

/-- A bilinear form vanishing on pairs of site vectors at sites of `S₁ × S₂` vanishes on pairs
of vectors supported in `S₁` and `S₂`. -/
theorem bilin_eq_zero_of_siteVec (B : LinearMap.BilinForm ℝ (PhaseVec ℤ n)) {S₁ S₂ : Set ℤ}
    (h : ∀ x ∈ S₁, ∀ y ∈ S₂, ∀ i j, B (siteVec x i) (siteVec y j) = 0) {u w : PhaseVec ℤ n}
    (hu : (LatticeSpace.supp u : Set ℤ) ⊆ S₁) (hw : (LatticeSpace.supp w : Set ℤ) ⊆ S₂) :
    B u w = 0 := by
  have h1 : ∀ x ∈ S₁, ∀ i, B (siteVec x i) w = 0 := by
    intro x hx i
    rw [eq_sum_siteVec w, map_sum]
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, h x hx y (hw hy) i j, smul_zero]
  rw [eq_sum_siteVec u, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, h1 x (hu hx) i, smul_zero]

/-- If `(O₁ + M) ∩ O₂ = ∅` with `M = −M`, the differences of points of `O₁` and `O₂` avoid `M`. -/
private theorem sub_notMem_of_disjoint {M O₁ O₂ : Set ℤ} (hsymm : ∀ x ∈ M, -x ∈ M)
    (h : Disjoint (O₁ + M) O₂) {x y : ℤ} (hx : x ∈ O₁) (hy : y ∈ O₂) : x - y ∉ M := by
  intro hxy
  have hy' : y ∈ O₁ + M := ⟨x, hx, -(x - y), hsymm _ hxy, by ring⟩
  exact Set.disjoint_left.1 h hy' hy

/-- A number whose real multiples all satisfy `exp(−t c / 2) = 1` vanishes. -/
private theorem eq_zero_of_forall_exp_eq_one {c : ℂ}
    (h : ∀ t : ℝ, Complex.exp (-((t : ℂ) * c) / 2) = 1) : c = 0 := by
  set t : ℝ := 1 / (‖c‖ + 1) with ht
  have htpos : 0 < t := by positivity
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (h t)
  have htc : t * ‖c‖ < 1 := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  have hnorm : ‖-((t : ℂ) * c) / 2‖ < 1 := by
    rw [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    linarith
  have hk0 : k = 0 := by
    by_contra hk0
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have := Int.one_le_abs hk0
      exact_mod_cast this
    have hge : 2 * Real.pi ≤ ‖(k : ℂ) * (2 * Real.pi * Complex.I)‖ := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      nlinarith [Real.pi_pos]
    rw [← hk] at hge
    linarith [Real.two_le_pi]
  rw [hk0, Int.cast_zero, zero_mul] at hk
  have htc0 : (t : ℂ) * c = 0 := by linear_combination -2 * hk
  rcases mul_eq_zero.1 htc0 with h0 | h0
  · exact absurd (Complex.ofReal_eq_zero.1 h0) htpos.ne'
  · exact h0

/-- The form of a sum of cells is the sum of the forms. -/
@[simp]
theorem cellForm_add (g g' : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) :
    cellForm (g + g') = cellForm g + cellForm g' :=
  bilinForm_ext_siteVec fun x i y j => by
    simp only [LinearMap.add_apply, cellForm_siteVec, Pi.add_apply, Matrix.add_apply]

/-- The form of the zero cells vanishes. -/
@[simp]
theorem cellForm_zero : cellForm (0 : ℤ → Matrix (Gaussian.PhaseIndex n)
    (Gaussian.PhaseIndex n) ℝ) = 0 :=
  bilinForm_ext_siteVec fun x i y j => by
    simp only [cellForm_siteVec, Pi.zero_apply, Matrix.zero_apply, LinearMap.zero_apply]

/-- Sums of cell data are cell data. -/
theorem cellData_add {g g' : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}
    (hg : CellData g) (hg' : CellData g') : CellData (g + g') where
  summable i j := Summable.of_nonneg_of_le (fun x => abs_nonneg _)
    (fun x => by simpa using abs_add_le (g x i j) (g' x i j))
    ((hg.summable i j).add (hg'.summable i j))
  symm x := by simp [hg.symm x, hg'.symm x, Matrix.transpose_add]

/-- The zero cells are cell data. -/
theorem cellData_zero :
    CellData (0 : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) where
  summable i j := by simp
  symm x := by simp

/-- The rule of a product of symbols is the composite of the rules. -/
theorem symbolLin_mul {G : Type*} [AddCommGroup G] (L₁ L₂ : Sym G n) :
    symbolLin (L₂ * L₁) = symbolLin L₂ ∘ₗ symbolLin L₁ :=
  LinearMap.ext fun u => by
    simp only [symbolLin, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      Matrix.toLin'_mul_apply]

namespace IsLatticeChannel

variable {T T₁ T₂ : GaussianChannel (phaseSpace ℤ n).sigma} {Ls L₁ L₂ : Sym ℤ n}
  {g g₁ g₂ : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ}

/-- A lattice channel on a Weyl operator. -/
theorem map_wCCR (h : IsLatticeChannel T Ls g) (u : PhaseVec ℤ n) :
    T.map (wCCR (phaseSpace ℤ n).sigma u) =
      Complex.exp (Complex.I * (T.disp u : ℂ) - (cellForm g u u : ℂ) / 4) •
        wCCR (phaseSpace ℤ n).sigma (Matrix.toLin' Ls u) := by
  rw [T.map_weyl, h.noise_eq, h.lin_eq]
  rfl

/-- The linear map of a lattice channel commutes with the translations. -/
theorem lin_translate (h : IsLatticeChannel T Ls g) (b : ℤ) (u : PhaseVec ℤ n) :
    T.lin (translateEquiv b u) = translateEquiv b (T.lin u) := by
  rw [h.lin_eq]
  exact toLin'_translate Ls b u

/-- Milestone Q5b, Proposition 19: a lattice channel commutes with the translations.
(notes: `prop:lc-qca`) -/
theorem map_comm_translate (h : IsLatticeChannel T Ls g) (a : Multiplicative ℤ)
    (x : CCR (phaseSpace ℤ n).sigma) :
    ccrTranslate ℤ n a (T.map x) = T.map (ccrTranslate ℤ n a x) := by
  have key : (ccrTranslateCLM a).comp T.toCLM = T.toCLM.comp (ccrTranslateCLM a) := by
    refine clm_ext_weyl (phaseSpace ℤ n).isAlt fun u => ?_
    simp only [ContinuousLinearMap.comp_apply, GaussianChannel.toCLM_apply,
      ccrTranslateCLM_apply, ccrTranslate_wCCR', T.map_weyl, map_smul]
    rw [h.lin_translate, h.disp_translate, h.noise_eq]
    simp only [translateEquiv_apply, cellForm_translate]
  exact congrArg (fun F : CCR (phaseSpace ℤ n).sigma →L[ℂ] CCR (phaseSpace ℤ n).sigma => F x) key

/-- Sufficiency in thesis Lemma 4.11(I): a lattice channel is local with the range of its symbol
as neighbourhood. -/
theorem isLocalWith_symbolRange (h : IsLatticeChannel T Ls g) :
    IsLocalWith (ccrNet (phaseSpace ℤ n)) T.map (symbolRange Ls : Set ℤ) := by
  intro O x hx
  refine map_mem_ccrNet (f := T.toCLM) (fun u hu' => ?_) hx
  have hu : (LatticeSpace.supp u : Set ℤ) ⊆ O := mem_locSubmodule_iff_supp.1 hu'
  rw [GaussianChannel.toCLM_apply, h.map_wCCR]
  refine StarSubalgebra.smul_mem _ ((wCCR_mem_ccrNet_iff _ _).2 fun y hy => ?_) _
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (supp_toLin'_subset Ls u hy)
  exact Set.add_mem_add (hu ha) hb

/-- Milestone Q5b, Proposition 19: a lattice channel is a QCA (thesis Def. 4.1) with the range
of its symbol as neighbourhood. (notes: `prop:lc-qca`) -/
noncomputable def toQCA (h : IsLatticeChannel T Ls g) :
    QCA (ccrNet (phaseSpace ℤ n)) (ccrTranslate ℤ n) where
  rule := T.map
  map_one := T.map_one
  nbhd := symbolRange Ls
  covariant := (ccrNet_lattice ℤ n).2.2.2
  comm := h.map_comm_translate
  isLocal := h.isLocalWith_symbolRange

/-- The rule of `h.toQCA` is the channel map. (notes: `prop:lc-qca`) -/
@[simp]
theorem toQCA_rule (h : IsLatticeChannel T Ls g) : h.toQCA.rule = T.map := rfl

/-- The neighbourhood of `h.toQCA` is the range of the symbol. (notes: `prop:lc-qca`) -/
@[simp]
theorem toQCA_nbhd (h : IsLatticeChannel T Ls g) : h.toQCA.nbhd = symbolRange Ls := rfl

/-- Milestone Q5b, Theorem 21(I), thesis Lemma 4.11 for notion I, both directions (F4), for an
arbitrary neighbourhood `N ⊆ ℤ` (milestone Q6; Q5b stated it for finite `N`).
(notes: `thm:lc-locality`) -/
theorem isLocalWith_iff (h : IsLatticeChannel T Ls g) (N : Set ℤ) :
    IsLocalWith (ccrNet (phaseSpace ℤ n)) T.map N ↔ (symbolRange Ls : Set ℤ) ⊆ N := by
  constructor
  · intro hloc m hm
    obtain ⟨i, j, hij⟩ : ∃ i j, (Ls i j).coeff m ≠ 0 := by
      simpa only [Finset.mem_coe, symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finsupp.mem_support_iff] using hm
    have h0 : wCCR (phaseSpace ℤ n).sigma (siteVec 0 j) ∈ ccrNet (phaseSpace ℤ n) {0} :=
      (wCCR_mem_ccrNet_iff {0} (siteVec 0 j)).2 (supp_siteVec_subset 0 j)
    have hmem : T.map (wCCR (phaseSpace ℤ n).sigma (siteVec 0 j)) ∈
        ccrNet (phaseSpace ℤ n) ({0} + N) := hloc {0} _ h0
    rw [h.map_wCCR] at hmem
    have hW : wCCR (phaseSpace ℤ n).sigma (Matrix.toLin' Ls (siteVec 0 j)) ∈
        ccrNet (phaseSpace ℤ n) ({0} + N) := by
      have := StarSubalgebra.smul_mem _ hmem
        (Complex.exp (Complex.I * (T.disp (siteVec 0 j) : ℂ) -
          (cellForm g (siteVec 0 j) (siteVec 0 j) : ℂ) / 4))⁻¹
      rwa [inv_smul_smul₀ (Complex.exp_ne_zero _)] at this
    rw [wCCR_mem_ccrNet_iff] at hW
    have hm' : m ∈ LatticeSpace.supp (Matrix.toLin' Ls (siteVec 0 j)) :=
      LatticeSpace.mem_supp.2 ⟨i, by rwa [coeff_toLin'_siteVec, sub_zero]⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.1 (hW hm')
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [zero_add] at hab
    exact hab ▸ hb
  · intro hN
    exact h.isLocalWith_symbolRange.mono hN

/-- Under the cell conditions of thesis Lemma 4.11(II), the dissipation form vanishes on vectors
supported in regions separated by `M`. -/
theorem dissipation_eq_zero (h : IsLatticeChannel T Ls g) {M O₁ O₂ : Set ℤ} (h0 : (0 : ℤ) ∈ M)
    (hsymm : ∀ x ∈ M, -x ∈ M) (hg : ∀ x ∉ M, g x = 0)
    (hK : (symbolRange (starTranspose Ls * const ℤ (Om n) * Ls) : Set ℤ) ⊆ M)
    (hO : Disjoint (O₁ + M) O₂) {u w : PhaseVec ℤ n}
    (hu : (LatticeSpace.supp u : Set ℤ) ⊆ O₁) (hw : (LatticeSpace.supp w : Set ℤ) ⊆ O₂) :
    T.dissipation u w = 0 := by
  have hsep := fun {x y : ℤ} (hx : x ∈ O₁) (hy : y ∈ O₂) =>
    sub_notMem_of_disjoint hsymm hO hx hy
  have hν : T.noise u w = 0 := by
    rw [h.noise_eq]
    refine bilin_eq_zero_of_siteVec _ (fun x hx y hy i j => ?_) hu hw
    rw [cellForm_siteVec, hg _ (hsep hx hy), Matrix.zero_apply]
  have hσ : (phaseSpace ℤ n).sigma u w = 0 := by
    refine bilin_eq_zero_of_siteVec _ (fun x hx y hy i j => ?_) hu hw
    have hxy : x ≠ y := fun e => hsep hx hy (by rw [e, sub_self]; exact h0)
    rw [phaseSpace_sigma, sigma_siteVec, ite_eq_right hxy]
  have hL : (phaseSpace ℤ n).sigma (T.lin u) (T.lin w) = 0 := by
    rw [h.lin_eq]
    refine (pairing_toLin' (const ℤ (Om n)) Ls u w).trans ?_
    refine bilin_eq_zero_of_siteVec _ (fun x hx y hy i j => ?_) hu hw
    rw [pairing_siteVec]
    by_contra hne
    exact hsep hx hy (hK (support_coeff_subset_symbolRange _ i j
      (Finsupp.mem_support_iff.2 hne)))
  rw [GaussianChannel.dissipation_apply, hν, hσ, hL]
  simp

/-- Milestone Q5b, Theorem 21(II), thesis Lemma 4.11 for notion II, both directions (F2, F4):
for `0 ∈ M = −M`, the channel factorizes with respect to `M` iff the noise cells vanish outside
`M` and the symbol of `σ(L·, L·)` has no coefficient outside `M` (thesis (4.36)).
(notes: `thm:lc-locality`) -/
theorem isFactorizing_iff (h : IsLatticeChannel T Ls g) (M : Finset ℤ) (h0 : (0 : ℤ) ∈ M)
    (hsymm : ∀ x ∈ M, -x ∈ M) :
    IsFactorizing (ccrNet (phaseSpace ℤ n)) T.map (M : Set ℤ) ↔
      (∀ x ∉ M, g x = 0) ∧ symbolRange (starTranspose Ls * const ℤ (Om n) * Ls) ⊆ M := by
  constructor
  · intro hfac
    have key : ∀ d ∉ M, ∀ i j, g d i j = 0 ∧
        ((starTranspose Ls * const ℤ (Om n) * Ls) i j).coeff d = 0 := by
      intro d hd i j
      have hd0 : d ≠ 0 := fun e => hd (e ▸ h0)
      have hO : Disjoint (({0} : Set ℤ) + (M : Set ℤ)) {-d} := by
        refine Set.disjoint_left.2 fun a ha had => ?_
        obtain ⟨b, hb, m, hm, hbm⟩ := Set.mem_add.1 ha
        rw [Set.mem_singleton_iff] at hb had
        rw [hb, zero_add] at hbm
        rw [← hbm] at had
        exact hd (by simpa [had] using hsymm m hm)
      have hexp : ∀ t : ℝ, Complex.exp (-((t : ℂ) * T.dissipation (siteVec 0 i)
          (siteVec (-d) j)) / 2) = 1 := by
        intro t
        rw [← GaussianChannel.dissipation_smul_left]
        refine T.exp_dissipation_eq_one (phaseSpace ℤ n).isAlt (hfac {0} {-d} hO _ ?_ _ ?_)
        · exact (wCCR_mem_ccrNet_iff _ _).2 fun x hx =>
            supp_siteVec_subset 0 i (LatticeSpace.supp_smul_subset t _ hx)
        · exact (wCCR_mem_ccrNet_iff _ _).2 (supp_siteVec_subset (-d) j)
      have hC := eq_zero_of_forall_exp_eq_one hexp
      have hσL : (phaseSpace ℤ n).sigma (symbolLin Ls (siteVec 0 i))
          (symbolLin Ls (siteVec (-d) j)) =
            ((starTranspose Ls * const ℤ (Om n) * Ls) i j).coeff d := by
        refine (pairing_toLin' (const ℤ (Om n)) Ls _ _).trans ?_
        rw [pairing_siteVec, zero_sub, neg_neg]
      have hre := congrArg Complex.re hC
      have him := congrArg Complex.im hC
      simp only [GaussianChannel.dissipation_apply, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_im, Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im,
        zero_mul, one_mul, sub_zero, mul_zero, add_zero, zero_add] at hre him
      rw [h.noise_eq, cellForm_siteVec, zero_sub, neg_neg] at hre
      rw [h.lin_eq, hσL, phaseSpace_sigma, sigma_siteVec,
        ite_eq_right (fun e => hd0 (by simpa using e.symm))] at him
      exact ⟨by simpa using hre, by simpa using him⟩
    refine ⟨fun d hd => ?_, fun m hm => ?_⟩
    · ext i j
      exact (key d hd i j).1
    · by_contra hmM
      obtain ⟨i, j, hij⟩ : ∃ i j,
          ((starTranspose Ls * const ℤ (Om n) * Ls) i j).coeff m ≠ 0 := by
        simpa only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and,
          Finsupp.mem_support_iff] using hm
      exact hij (key m hmM i j).2
  · rintro ⟨hg, hK⟩ O₁ O₂ hO a ha b hb
    have hW : ∀ u : PhaseVec ℤ n, (LatticeSpace.supp u : Set ℤ) ⊆ O₁ →
        ∀ w : PhaseVec ℤ n, (LatticeSpace.supp w : Set ℤ) ⊆ O₂ →
          T.map (wCCR (phaseSpace ℤ n).sigma u * wCCR (phaseSpace ℤ n).sigma w) =
            T.map (wCCR (phaseSpace ℤ n).sigma u) * T.map (wCCR (phaseSpace ℤ n).sigma w) := by
      intro u hu w hw
      rw [T.map_weyl_mul (phaseSpace ℤ n).isAlt,
        h.dissipation_eq_zero h0 hsymm hg (by exact_mod_cast hK) hO hu hw]
      rw [neg_zero, zero_div, Complex.exp_zero]; exact one_smul ℂ _
    have hA : ∀ u : PhaseVec ℤ n, (LatticeSpace.supp u : Set ℤ) ⊆ O₁ →
        ∀ b ∈ ccrNet (phaseSpace ℤ n) O₂,
          T.map (wCCR (phaseSpace ℤ n).sigma u * b) =
            T.map (wCCR (phaseSpace ℤ n).sigma u) * T.map b := by
      intro u hu b hb
      exact eqOn_ccrNet (f := T.toCLM.comp
          (ContinuousLinearMap.mul ℂ _ (wCCR (phaseSpace ℤ n).sigma u)))
        (g := (ContinuousLinearMap.mul ℂ _ (T.map (wCCR (phaseSpace ℤ n).sigma u))).comp
          T.toCLM) (fun w hw => hW u hu w (mem_locSubmodule_iff_supp.1 hw)) hb
    exact eqOn_ccrNet
      (f := T.toCLM.comp ((ContinuousLinearMap.mul ℂ (CCR (phaseSpace ℤ n).sigma)).flip b))
      (g := ((ContinuousLinearMap.mul ℂ (CCR (phaseSpace ℤ n).sigma)).flip (T.map b)).comp
        T.toCLM)
      (fun u hu => hA u (mem_locSubmodule_iff_supp.1 hu) b hb) ha

/-- Milestone Q5b, Proposition 25: concatenation of lattice channels (thesis p. 96).
(notes: `prop:lc-comp`) -/
theorem comp (h₁ : IsLatticeChannel T₁ L₁ g₁) (h₂ : IsLatticeChannel T₂ L₂ g₂) :
    IsLatticeChannel (T₂.comp T₁) (L₂ * L₁) (g₁ + pullbackKernel L₁ g₂) where
  lin_eq := by rw [GaussianChannel.comp_lin, h₁.lin_eq, h₂.lin_eq, symbolLin_mul]
  noise_eq := by
    rw [GaussianChannel.comp_noise, h₁.noise_eq, h₂.noise_eq, h₁.lin_eq, cellForm_add,
      cellForm_pullbackKernel]
  cellData := cellData_add h₁.cellData (cellData_pullbackKernel L₁ h₂.cellData)
  disp_translate a u := by
    simp only [GaussianChannel.comp_disp, LinearMap.add_apply, LinearMap.coe_comp,
      Function.comp_apply]
    rw [h₁.disp_translate, h₁.lin_translate, h₂.disp_translate]

/-- A symplectic symbol `L̂` gives a lattice channel with symbol `L̂`, no noise and no
displacement: the relabelling by its rule. The shift is an instance. (notes: `def:lc-channel`) -/
theorem ofRelabel (hL : IsSymplectic Ls) :
    IsLatticeChannel (GaussianChannel.ofRelabel (phaseSpace ℤ n).sigma (sigma_rule hL)) Ls 0 where
  lin_eq := LinearMap.ext fun _ => rfl
  noise_eq := cellForm_zero.symm
  cellData := cellData_zero
  disp_translate _ _ := rfl

end IsLatticeChannel

/-! ### Auxiliary lemmas for the examples -/

/-- The vacuum matrix `1 + iΩ` is positive semidefinite. -/
theorem posSemidef_one_add_iOmega :
    ((1 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℂ) +
      Complex.I • (Om n).map Complex.ofReal).PosSemidef := by
  set B := Complex.I • (Om n).map Complex.ofReal with hB
  have hsq : (Om n).map Complex.ofReal * (Om n).map Complex.ofReal = -1 := by
    rw [← map_ofReal_mul, Gaussian.symplecticForm_sq _]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp
  have hBB : B * B = 1 := by
    rw [hB, smul_mul_smul_comm, hsq, Complex.I_mul_I, neg_smul, smul_neg, one_smul, neg_neg]
  have hH : (1 + B)ᴴ = 1 + B := by
    rw [conjTranspose_add, conjTranspose_one, iOmega_isHermitian.eq]
  have hAA : (1 + B)ᴴ * (1 + B) = (2 : ℂ) • (1 + B) := by
    rw [hH, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hBB, two_smul]
    abel
  have h2 : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.2 (by norm_num)
  have := (posSemidef_conjTranspose_mul_self (1 + B)).smul h2
  rwa [hAA, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at this

/-- The vacuum cells satisfy the state condition (Q3, Example 18). -/
theorem isStateConditionC_vacuum :
    IsStateConditionC (cellForm (onSiteKernel (1 : Matrix (Gaussian.PhaseIndex n)
      (Gaussian.PhaseIndex n) ℝ))) (phaseSpace ℤ n).sigma := by
  have hs := cellForm_isSymm (cellData_onSiteKernel (n := n) transpose_one).symm
  rw [cellForm_onSiteKernel] at hs ⊢
  exact (isStateConditionC_iff hs (sigma_isAlt ℤ n)).2 isStateCondition_vacuum

/-- The complexification of a real multiple of the identity. -/
private theorem map_ofReal_smul_one (r : ℝ) :
    (r • (1 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ)).map Complex.ofReal =
      (r : ℂ) • (1 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℂ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `L̂⋆ᵀ` commutes with real scalars. -/
theorem starTranspose_smul (r : ℝ) (P : Sym ℤ n) :
    starTranspose (r • P) = r • starTranspose P := by
  ext i j : 2
  simp [starTranspose, map_smul]

/-- Milestone Q5b, Proposition 23(a), thesis Lemma 4.10(v), notion II does not imply notion I
(F3): the shift channel factorizes with respect to `{0}` but is not local with neighbourhood
`{0}`. (notes: `prop:lc-independent`) -/
theorem exists_isFactorizing_not_isLocalWith [NeZero n] :
    ∃ T : GaussianChannel (phaseSpace ℤ n).sigma,
      IsFactorizing (ccrNet (phaseSpace ℤ n)) T.map {0} ∧
        ¬ IsLocalWith (ccrNet (phaseSpace ℤ n)) T.map {0} := by
  have hS := shiftSymbol_symplectic (n := n) (1 : ℤ)
  have hK : starTranspose (shiftSymbol (n := n) (1 : ℤ)) * const ℤ (Om n) * shiftSymbol 1 =
      const ℤ (Om n) := hS
  refine ⟨GaussianChannel.ofRelabel (phaseSpace ℤ n).sigma (sigma_rule hS), ?_, ?_⟩
  · have := ((IsLatticeChannel.ofRelabel hS).isFactorizing_iff {0} (by simp) (by simp)).2
      ⟨fun _ _ => rfl, by rw [hK]; exact symbolRange_const (Om n)⟩
    simpa using this
  · intro hloc
    have h1 : (1 : ℤ) ∈ symbolRange (shiftSymbol (n := n) (1 : ℤ)) := by
      simp only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨Sum.inl 0, Sum.inl 0, ?_⟩
      simp [shiftSymbol]
    have := ((IsLatticeChannel.ofRelabel hS).isLocalWith_iff {0}).1 (by simpa using hloc)
      (Finset.mem_coe.2 h1)
    simp at this

/-- Milestone Q5b, Proposition 23(b), thesis Lemma 4.10(v), notion I does not imply notion II:
for every finite `M` there are data with `L = 0` satisfying (4.34) such that no lattice channel
with these data factorizes with respect to `M` (their existence rests on thesis Thm. 2.6).
(notes: `prop:lc-independent`) -/
theorem exists_data_not_isFactorizing [NeZero n] (M : Finset ℤ) :
    ∃ g : ℤ → Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ, CellData g ∧
      (∃ R : ℕ, ∀ m, (R : ℤ) < |m| → g m = 0) ∧
      IsStateConditionC (cellForm g)
        ((phaseSpace ℤ n).sigma - ((phaseSpace ℤ n).sigma).comp 0 0) ∧
      ∀ T : GaussianChannel (phaseSpace ℤ n).sigma, IsLatticeChannel T 0 g →
        ¬ IsFactorizing (ccrNet (phaseSpace ℤ n)) T.map (M : Set ℤ) := by
  set R : ℕ := M.sup Int.natAbs with hR
  set x₀ : ℤ := (R : ℤ) + 1 with hx₀
  have hx₀pos : 0 < x₀ := by positivity
  set c : ℤ → ℝ := fun x => if x = 0 then 2 else if |x| = x₀ then 1 / 2 else 0 with hc
  have hc_neg : ∀ x, c (-x) = c x := fun x => by simp [hc, abs_neg]
  have hc_out : ∀ x, x₀ < |x| → c x = 0 := by
    intro x hx
    have h1 : x ≠ 0 := by rintro rfl; simp at hx; omega
    have h2 : |x| ≠ x₀ := by omega
    simp [hc, h1, h2]
  have hc0 : c 0 = 2 := by simp [hc]
  have hcx : c x₀ = 1 / 2 := by simp [hc, hx₀pos.ne', abs_of_pos hx₀pos]
  have hcnx : c (-x₀) = 1 / 2 := by rw [hc_neg, hcx]
  have hcd : CellData fun x => c x • (1 : Matrix (Gaussian.PhaseIndex n)
      (Gaussian.PhaseIndex n) ℝ) :=
    ⟨fun i j => summable_of_ne_finset_zero (s := Finset.Icc (-x₀) x₀) fun m hm => by
      rw [Finset.mem_Icc, not_and_or] at hm
      rw [hc_out m (by rw [lt_abs]; omega), zero_smul, Matrix.zero_apply, abs_zero],
    fun x => by rw [hc_neg, transpose_smul, transpose_one]⟩
  refine ⟨fun x => c x • 1, hcd, ⟨R + 1, fun m hm => ?_⟩, ?_, ?_⟩
  · change c m • (1 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℝ) = 0
    rw [hc_out m (by push_cast at hm; omega), zero_smul]
  · rw [isStateConditionC_zero_lin]
    refine stateCondition_of_fourier hcd fun k => ?_
    have hgh : gammaHat (fun x => c x • (1 : Matrix (Gaussian.PhaseIndex n)
        (Gaussian.PhaseIndex n) ℝ)) k = ((2 + Real.cos (k * x₀) : ℝ) : ℂ) • 1 := by
      rw [gammaHat, tsum_eq_sum (s := {0, x₀, -x₀}) fun x hx => ?_]
      · have h1 : (0 : ℤ) ∉ ({x₀, -x₀} : Finset ℤ) := by simp; omega
        have h2 : x₀ ∉ ({-x₀} : Finset ℤ) := by simp; omega
        rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, hc0, hcx, hcnx]
        simp only [map_ofReal_smul_one, smul_smul]
        rw [← add_smul, ← add_smul]
        congr 1
        have e1 : -(k : ℂ) * ((x₀ : ℤ) : ℂ) * Complex.I = -((k : ℂ) * (x₀ : ℂ) * Complex.I) := by
          ring
        have e2 : -(k : ℂ) * ((-x₀ : ℤ) : ℂ) * Complex.I = (k : ℂ) * (x₀ : ℂ) * Complex.I := by
          push_cast; ring
        rw [e1, e2]
        push_cast
        rw [Complex.cos]
        simp only [mul_zero, zero_mul, Complex.exp_zero, neg_mul]
        ring_nf
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hxc : c x = 0 := by
          simp only [hc, hx.1, ite_false]
          rw [ite_eq_right]
          intro habs
          rcases abs_eq hx₀pos.le |>.1 habs with h | h
          · exact hx.2.1 h
          · exact hx.2.2 h
        rw [hxc, zero_smul]
        simp
    rw [hgh]
    have e : ((2 + Real.cos (k * x₀) : ℝ) : ℂ) •
          (1 : Matrix (Gaussian.PhaseIndex n) (Gaussian.PhaseIndex n) ℂ) +
        Complex.I • (Om n).map Complex.ofReal =
        ((1 + Real.cos (k * x₀) : ℝ) : ℂ) • 1 +
          (1 + Complex.I • (Om n).map Complex.ofReal) := by
      push_cast
      rw [add_smul, add_smul, one_smul, two_smul]
      abel
    rw [e]
    refine (PosSemidef.one.smul ?_).add posSemidef_one_add_iOmega
    exact Complex.zero_le_real.2 (by linarith [Real.neg_one_le_cos (k * x₀)])
  · intro T hT hfac
    set M' : Finset ℤ := M ∪ M.image Neg.neg ∪ {0} with hM'
    have h0' : (0 : ℤ) ∈ M' := by simp [hM']
    have hsymm' : ∀ x ∈ M', -x ∈ M' := by
      intro x hx
      simp only [hM', Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hx ⊢
      rcases hx with (hx | ⟨a, ha, rfl⟩) | rfl
      · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
      · exact Or.inl (Or.inl (by simpa using ha))
      · exact Or.inr (by simp)
    have hx₀M' : x₀ ∉ M' := by
      simp only [hM', Finset.mem_union, Finset.mem_image, Finset.mem_singleton, not_or]
      refine ⟨⟨fun hm => ?_, fun ⟨a, ha, hax⟩ => ?_⟩, hx₀pos.ne'⟩
      · have := Finset.le_sup (f := Int.natAbs) hm
        rw [← hR] at this
        omega
      · have := Finset.le_sup (f := Int.natAbs) ha
        rw [← hR] at this
        omega
    have hfac' := hfac.mono (M' := (M' : Set ℤ)) (by
      intro x hx
      simp [hM', Finset.mem_coe.1 hx])
    have hg := ((hT.isFactorizing_iff M' h0' hsymm').1 hfac').1 x₀ hx₀M'
    have h00 := congrFun (congrFun hg (Sum.inl 0)) (Sum.inl 0)
    simp [hcx] at h00

/-- Milestone Q5b, Proposition 29 (F8), the lossy example: `√η L(φ, λ)` with vacuum noise
`(1 − η)` on site satisfies (4.34) and the conditions of notion II with `M = {0}`, is not
symplectic, and its two-step concatenation has noise at distance 2 when `λ ≠ 0`.
(notes: `prop:lc-lossy`) -/
theorem lossy_example (φ lam η : ℝ) (h0 : 0 < η) (h1 : η < 1) :
    IsStateConditionC (cellForm (onSiteKernel ((1 - η) • (1 : Matrix Cell Cell ℝ))))
        ((phaseSpace ℤ 1).sigma - ((phaseSpace ℤ 1).sigma).comp
          (symbolLin (Real.sqrt η • rotationSymbol φ lam))
          (symbolLin (Real.sqrt η • rotationSymbol φ lam))) ∧
      symbolRange (starTranspose (Real.sqrt η • rotationSymbol φ lam) * const ℤ (Om 1) *
        (Real.sqrt η • rotationSymbol φ lam)) ⊆ {0} ∧
      ¬ IsSymplectic (Real.sqrt η • rotationSymbol φ lam) ∧
      (lam ≠ 0 → (onSiteKernel ((1 - η) • (1 : Matrix Cell Cell ℝ)) +
        pullbackKernel (Real.sqrt η • rotationSymbol φ lam)
          (onSiteKernel ((1 - η) • (1 : Matrix Cell Cell ℝ)))) 2 ≠ 0) := by
  have hR : starTranspose (rotationSymbol φ lam) * const ℤ (Om 1) * rotationSymbol φ lam =
      const ℤ (Om 1) := isSymplectic_of_mono (rotation_example φ lam 0).1
  have hs : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt h0.le
  have hs0 : Real.sqrt η ≠ 0 := (Real.sqrt_pos.2 h0).ne'
  have hK : starTranspose (Real.sqrt η • rotationSymbol φ lam) * const ℤ (Om 1) *
      (Real.sqrt η • rotationSymbol φ lam) = η • const ℤ (Om 1) := by
    rw [starTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hs, hR]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hσL : ((phaseSpace ℤ 1).sigma).comp (symbolLin (Real.sqrt η • rotationSymbol φ lam))
        (symbolLin (Real.sqrt η • rotationSymbol φ lam)) = η • (phaseSpace ℤ 1).sigma := by
      refine bilinForm_ext_siteVec fun x i y j => ?_
      rw [LinearMap.BilinForm.comp_apply]
      refine (pairing_toLin' (const ℤ (Om 1)) (Real.sqrt η • rotationSymbol φ lam) _ _).trans ?_
      rw [pairing_siteVec, hK, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
        show (phaseSpace ℤ 1).sigma (siteVec x i) (siteVec y j) =
          pairing (const ℤ (Om 1)) (siteVec x i) (siteVec y j) from rfl, pairing_siteVec]
      simp [Matrix.smul_apply]
    have hν : cellForm (onSiteKernel ((1 - η) • (1 : Matrix Cell Cell ℝ))) =
        (1 - η) • cellForm (onSiteKernel (1 : Matrix Cell Cell ℝ)) := by
      refine bilinForm_ext_siteVec fun x i y j => ?_
      simp only [cellForm_siteVec, LinearMap.smul_apply, smul_eq_mul, onSiteKernel]
      split_ifs <;> simp
    have hsub : (phaseSpace ℤ 1).sigma - η • (phaseSpace ℤ 1).sigma =
        (1 - η) • (phaseSpace ℤ 1).sigma := by
      refine LinearMap.ext₂ fun u w => ?_
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hν, hσL, hsub]
    exact isStateConditionC_vacuum.smul (by linarith)
  · rw [hK]
    intro m hm
    obtain ⟨i, j, hij⟩ : ∃ i j, ((η • const ℤ (Om 1)) i j).coeff m ≠ 0 := by
      simpa only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finsupp.mem_support_iff] using hm
    apply symbolRange_const (Om 1)
    simp only [symbolRange, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finsupp.mem_support_iff]
    exact ⟨i, j, fun h => hij (by simp [Matrix.smul_apply, h])⟩
  · intro hsym
    have hsym' : η • const ℤ (Om 1) = const ℤ (Om 1) := hK.symm.trans hsym
    have h := congrArg (fun P : Sym ℤ 1 => (P qIdx pIdx).coeff 0) hsym'
    have hΩ : (Om 1) qIdx pIdx = 1 := by simp [Gaussian.symplecticForm, Matrix.J]
    simp [Matrix.smul_apply, const, hΩ] at h
    linarith
  · intro hlam h
    rw [Pi.add_apply, show onSiteKernel ((1 - η) • (1 : Matrix Cell Cell ℝ)) 2 = 0 by
      simp [onSiteKernel], zero_add, pullbackKernel_smul hs0,
      pullbackKernel_rotation_two, hs,
      smul_smul] at h
    have hc : η * ((1 - η) * lam ^ 2) ≠ 0 :=
      mul_ne_zero h0.ne' (mul_ne_zero (sub_pos.2 h1).ne' (pow_ne_zero 2 hlam))
    have hqq : η * ((1 - η) * lam ^ 2) * (Real.sin φ * Real.sin φ) = 0 := by
      have := congrFun (congrFun h qIdx) qIdx
      simp only [Matrix.smul_apply, vecMulVec_apply, rotation, Matrix.of_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at this
      linear_combination this
    have hpp : η * ((1 - η) * lam ^ 2) * (Real.cos φ * Real.cos φ) = 0 := by
      have := congrFun (congrFun h pIdx) pIdx
      simp only [Matrix.smul_apply, vecMulVec_apply, rotation, Matrix.of_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at this
      linear_combination this
    have hs2 := (mul_eq_zero.1 hqq).resolve_left hc
    have hc2 := (mul_eq_zero.1 hpp).resolve_left hc
    nlinarith [Real.sin_sq_add_cos_sq φ]

end QCALean.Bosonic
