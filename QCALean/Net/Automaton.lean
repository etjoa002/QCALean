/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import LinearAQFT.Causal.Basic
import LinearAQFT.Net.Basic
import LocalAlgebrasLean.Lattice.Basic
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Reversible quantum cellular automata

Milestone Q2, Definition 8 (thesis Def. 4.1, reversible case). Regions of a lattice `G` are its
subsets. They form a causal index with orthogonality = disjointness and dependence = inclusion
(Q2, Definition 1): a lattice without time has no time slice beyond isotony. Translations
`O ↦ O + a` are automorphisms of this index. Since milestone L3 of LocalAlgebrasLean
(6 Oct 2026) the orthogonality of this index is the region index of the sites in that library
(`LocalAlgebrasLean.subsetIndex`), and the translations are its group action
(`translateAut_toIso`); the index itself is LinearAQFT's
`subsetCausalIndex` (L4).

A reversible QCA on a net `𝒜` over the subsets of `G`, covariant under a translation action `α`,
is a star-automorphism `T` with a finite neighbourhood `N`, commuting with the translations and
mapping `𝒜 O` into `𝒜 (O + N)`. The composite of two such automata is one (Q2, Proposition 9;
thesis Cor. 4.3).

## Main definitions and results

* `QCALean.Net.latticeIndex`, `QCALean.Net.translateAut`, `QCALean.Net.translateHom`
* `QCALean.Net.ReversibleQCA`, `QCALean.Net.ReversibleQCA.comp`, `QCALean.Net.ReversibleQCA.mono`
* `QCALean.Net.QCA` (thesis Def. 4.1, milestone Q5a), notions I and II:
  `QCALean.Net.IsLocalWith`, `QCALean.Net.IsFactorizing`; `QCALean.Net.ReversibleQCA.toQCA`
-/

open LinearAQFT
open scoped Pointwise CStarAlgebra

namespace QCALean.Net

variable (G : Type*) [AddCommGroup G]

/-- Milestone Q2, Definition 1: regions are subsets, orthogonal means disjoint, dependent means
contained in. (notes: `def:rqca`) -/
def latticeIndex : CausalIndex (Set G) := LinearAQFT.subsetCausalIndex G

variable {G}

omit [AddCommGroup G] in
@[simp] theorem latticeIndex_orthogonal (O₁ O₂ : Set G) :
    (latticeIndex G).Orthogonal O₁ O₂ ↔ Disjoint O₁ O₂ := Iff.rfl

omit [AddCommGroup G] in
@[simp] theorem latticeIndex_dependent (O O' : Set G) :
    (latticeIndex G).Dependent O O' ↔ O ⊆ O' := Iff.rfl

/-- Translation of regions, `O ↦ O + a = {x | x - a ∈ O}`. -/
def translateOrderIso (a : G) : Set G ≃o Set G where
  toFun O := (fun x => x - a) ⁻¹' O
  invFun O := (fun x => x + a) ⁻¹' O
  left_inv O := by ext x; simp
  right_inv O := by ext x; simp
  map_rel_iff' {O O'} := by
    constructor
    · intro h x hx
      have := @h (x + a) (by simpa using hx)
      simpa using this
    · intro h x hx
      exact h hx

theorem translateOrderIso_eq (a : G) (O : Set G) : translateOrderIso a O = O + {a} := by
  ext x
  simp [translateOrderIso, sub_eq_add_neg]

/-- Translation by `a` as an automorphism of the lattice causal index. -/
def translateAut (a : G) : (latticeIndex G).Aut where
  toOrderIso := translateOrderIso a
  orthogonal_iff' O₁ O₂ := by
    simp only [latticeIndex_orthogonal]
    change Disjoint ((fun x => x - a) ⁻¹' O₁) ((fun x => x - a) ⁻¹' O₂) ↔ _
    exact Set.disjoint_preimage_iff (Equiv.subRight a).surjective
  dependent_iff' O O' := (translateOrderIso a).le_iff_le

@[simp] theorem translateAut_apply (a : G) (O : Set G) :
    translateAut a O = (fun x => x - a) ⁻¹' O := rfl

/-- The translation homomorphism `a ↦ (O ↦ O + a)`. -/
def translateHom : Multiplicative G →* (latticeIndex G).Aut where
  toFun a := translateAut a.toAdd
  map_one' := by
    apply CausalIndex.Iso.ext; intro O; ext x; simp
  map_mul' a b := by
    apply CausalIndex.Iso.ext; intro O; ext x
    simp [sub_sub, CausalIndex.Aut.mul_apply]

/-- The translations are the action of the group `G` on its own sites, as in LocalAlgebrasLean:
the region index underlying `translateAut a` is `actionAut` of `a`. -/
theorem translateAut_toIso (a : G) :
    (translateAut a).toIso = LocalAlgebrasLean.actionAut (Multiplicative.ofAdd a) := by
  apply LocalAlgebrasLean.RegionIndex.Iso.ext
  intro O
  ext x
  change x - a ∈ O ↔ (Multiplicative.ofAdd a)⁻¹ • x ∈ O
  rw [← ofAdd_neg]
  change x - a ∈ O ↔ -a + x ∈ O
  rw [sub_eq_neg_add]

/-- Milestone Q2, Definition 8 (thesis Def. 4.1, reversible case): a reversible quantum cellular
automaton on a net over the subsets of `G`, covariant under the translation action `α`.
(notes: `def:rqca`) -/
structure ReversibleQCA {A : Type*} [CStarAlgebra A] (𝒜 : LinearAQFT.Net (Set G) A)
    (α : Multiplicative G →* (A ≃⋆ₐ[ℂ] A)) where
  /-- The global rule. -/
  rule : A ≃⋆ₐ[ℂ] A
  /-- The neighbourhood scheme. -/
  nbhd : Finset G
  /-- The net is covariant under the translation action. -/
  covariant : LinearAQFT.Net.IsCovariantUnder 𝒜 translateHom α
  comm : ∀ a, rule.trans (α a) = (α a).trans rule
  isLocal : ∀ O, (𝒜 O).map rule.toStarAlgHom ≤ 𝒜 (O + (nbhd : Set G))

namespace ReversibleQCA

variable {A : Type*} [CStarAlgebra A] {𝒜 : LinearAQFT.Net (Set G) A}
  {α : Multiplicative G →* (A ≃⋆ₐ[ℂ] A)}

/-- Enlarging the neighbourhood. -/
def mono [DecidableEq G] (T : ReversibleQCA 𝒜 α) (N : Finset G) (h : T.nbhd ⊆ N) :
    ReversibleQCA 𝒜 α where
  rule := T.rule
  nbhd := N
  covariant := T.covariant
  comm := T.comm
  isLocal O := (T.isLocal O).trans
    (𝒜.toOrderHom.monotone (Set.add_subset_add_left (by exact_mod_cast h)))

/-- Milestone Q2, Proposition 9 (thesis Cor. 4.3): the composite `T₂ T₁` is a reversible QCA
with neighbourhood `N₁ + N₂`. (notes: `prop:rqca-comp`) -/
def comp [DecidableEq G] (T₂ T₁ : ReversibleQCA 𝒜 α) : ReversibleQCA 𝒜 α where
  rule := T₁.rule.trans T₂.rule
  nbhd := T₁.nbhd + T₂.nbhd
  covariant := T₁.covariant
  comm a := by
    ext y
    have h1 := DFunLike.congr_fun (T₁.comm a) y
    have h2 := DFunLike.congr_fun (T₂.comm a) (T₁.rule y)
    simp only [StarAlgEquiv.trans_apply] at h1 h2 ⊢
    rw [h2, h1]
  isLocal O := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : T₁.rule y ∈ 𝒜 (O + (T₁.nbhd : Set G)) := T₁.isLocal O ⟨y, hy, rfl⟩
    have h2 := T₂.isLocal _ ⟨_, h1, rfl⟩
    simpa [Finset.coe_add, add_assoc] using h2

@[simp] theorem comp_rule [DecidableEq G] (T₂ T₁ : ReversibleQCA 𝒜 α) :
    (T₂.comp T₁).rule = T₁.rule.trans T₂.rule := rfl

@[simp] theorem comp_nbhd [DecidableEq G] (T₂ T₁ : ReversibleQCA 𝒜 α) :
    (T₂.comp T₁).nbhd = T₁.nbhd + T₂.nbhd := rfl

end ReversibleQCA

section Irreversible

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Milestone Q5a, Definition 15(a) (thesis Def. 4.1): a quantum cellular automaton on a net `𝒜`
over the subsets of `G`, covariant under the translation action `α`: a unital completely positive
global rule commuting with the translations, with a finite neighbourhood `nbhd` such that the
rule maps `𝒜 O` into `𝒜 (O + nbhd)` (notion I). (notes: `def:ch-qca`) -/
structure QCA (𝒜 : LinearAQFT.Net (Set G) A) (α : Multiplicative G →* (A ≃⋆ₐ[ℂ] A)) where
  /-- The global rule. -/
  rule : A →CP A
  /-- The rule is unital. -/
  map_one : rule 1 = 1
  /-- The neighbourhood scheme. -/
  nbhd : Finset G
  /-- The net is covariant under the translation action. -/
  covariant : LinearAQFT.Net.IsCovariantUnder 𝒜 translateHom α
  /-- The rule commutes with every translation. -/
  comm : ∀ a x, α a (rule x) = rule (α a x)
  /-- Notion I: the rule maps `𝒜 O` into `𝒜 (O + nbhd)`. -/
  isLocal : ∀ O, ∀ x ∈ 𝒜 O, rule x ∈ 𝒜 (O + (nbhd : Set G))

/-- Milestone Q5a, Definition 15(b) (thesis §4.3, notion I): finite propagation with
neighbourhood `N`, `T(𝒜 O) ⊆ 𝒜 (O + N)` for every region `O`. (notes: `def:ch-locality`) -/
def IsLocalWith (𝒜 : LinearAQFT.Net (Set G) A) (T : A → A) (N : Set G) : Prop :=
  ∀ O, ∀ x ∈ 𝒜 O, T x ∈ 𝒜 (O + N)

/-- Milestone Q5a, Definition 15(c) (thesis §4.3, notion II): factorization with respect to `M`,
`T(ab) = T(a) T(b)` for `a ∈ 𝒜 O₁`, `b ∈ 𝒜 O₂` whenever `(O₁ + M) ∩ O₂ = ∅`. The notes write `N′`
for `M` and state the notion only for `0 ∈ N′ = -N′`; `IsLatticeChannel.isFactorizing_iff`
assumes this, while `exists_data_not_isFactorizing` holds for every finite `M`.
(notes: `def:ch-locality`) -/
def IsFactorizing (𝒜 : LinearAQFT.Net (Set G) A) (T : A → A) (M : Set G) : Prop :=
  ∀ O₁ O₂ : Set G, Disjoint (O₁ + M) O₂ → ∀ a ∈ 𝒜 O₁, ∀ b ∈ 𝒜 O₂, T (a * b) = T a * T b

omit [PartialOrder A] [StarOrderedRing A] in
/-- Notion I is monotone in the neighbourhood: finite propagation with `N` implies finite
propagation with every `N' ⊇ N`. -/
theorem IsLocalWith.mono {𝒜 : LinearAQFT.Net (Set G) A} {T : A → A} {N N' : Set G}
    (h : IsLocalWith 𝒜 T N) (hN : N ⊆ N') : IsLocalWith 𝒜 T N' :=
  fun O x hx => 𝒜.toOrderHom.monotone (Set.add_subset_add_left hN) (h O x hx)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Notion II is monotone in `M`: factorization with respect to `M` implies factorization with
respect to every `M' ⊇ M`. -/
theorem IsFactorizing.mono {𝒜 : LinearAQFT.Net (Set G) A} {T : A → A} {M M' : Set G}
    (h : IsFactorizing 𝒜 T M) (hM : M ⊆ M') : IsFactorizing 𝒜 T M' :=
  fun O₁ O₂ hO => h O₁ O₂ (hO.mono_left (Set.add_subset_add_left hM))

/-- A QCA satisfies notion I with its neighbourhood. (notes: `def:ch-qca`) -/
theorem QCA.isLocalWith {𝒜 : LinearAQFT.Net (Set G) A} {α : Multiplicative G →* (A ≃⋆ₐ[ℂ] A)}
    (T : QCA 𝒜 α) : IsLocalWith 𝒜 T.rule (T.nbhd : Set G) :=
  T.isLocal

/-- Milestone Q5a, Proposition 16: a reversible QCA is a QCA, its rule being a
star-automorphism, hence unital and completely positive. (notes: `prop:ch-revqca`) -/
noncomputable def ReversibleQCA.toQCA {𝒜 : LinearAQFT.Net (Set G) A}
    {α : Multiplicative G →* (A ≃⋆ₐ[ℂ] A)} (T : ReversibleQCA 𝒜 α) : QCA 𝒜 α where
  rule := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap T.rule
  map_one := _root_.map_one T.rule
  nbhd := T.nbhd
  covariant := T.covariant
  comm a x := congrArg (fun F : A ≃⋆ₐ[ℂ] A => F x) (T.comm a)
  isLocal O x hx := T.isLocal O ⟨x, hx, rfl⟩

/-- The rule of `T.toQCA` is the rule of `T`. (notes: `prop:ch-revqca`) -/
@[simp]
theorem ReversibleQCA.toQCA_rule_apply {𝒜 : LinearAQFT.Net (Set G) A}
    {α : Multiplicative G →* (A ≃⋆ₐ[ℂ] A)} (T : ReversibleQCA 𝒜 α) (x : A) :
    T.toQCA.rule x = T.rule x := rfl

/-- The neighbourhood of `T.toQCA` is that of `T`. (notes: `prop:ch-revqca`) -/
@[simp]
theorem ReversibleQCA.toQCA_nbhd {𝒜 : LinearAQFT.Net (Set G) A}
    {α : Multiplicative G →* (A ≃⋆ₐ[ℂ] A)} (T : ReversibleQCA 𝒜 α) :
    T.toQCA.nbhd = T.nbhd := rfl

end Irreversible

end QCALean.Net
