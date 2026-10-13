/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Lattice phase space

The phase space of a lattice of identical cells: finitely supported maps from the lattice `G`
(an additive commutative group; `ℤ` for chains) to `R^ι`, the phase space of one cell. They are
represented as vectors `ι → R[G]` of group-algebra elements, so that the `R[G]`-module structure
(translations act by multiplication with the monomials `z^a = single a 1`) comes from Mathlib.
Milestone Q1, Definition 1; thesis [Krüger 2006, p. 76].

## Main definitions

* `QCALean.Core.LatticeSpace R G ι`: the phase space `ι → R[G]`.
* `LatticeSpace.valueAt u x`: the value `u(x) ∈ R^ι` of `u` at the lattice point `x`.
* `LatticeSpace.supp u`: the finite set of points where `u` is nonzero.
* `QCALean.Core.translate R G ι a`: translation by `a`, pushing forward,
  `(κ_{a*} u)(x) = u(x - a)` (`translate_valueAt`).
-/

open AddMonoidAlgebra
open scoped Pointwise

namespace QCALean.Core

variable (R : Type*) [CommRing R] (G : Type*) [AddCommGroup G] (ι : Type*)

/-- Milestone Q1, Definition 1: the lattice phase space, vectors of group-algebra elements.
(notes: `def:qca-space`) -/
abbrev LatticeSpace := ι → R[G]

variable {R G ι}

namespace LatticeSpace

/-- The value of a vector at a point of the lattice. (notes: `def:qca-space`) -/
def valueAt (u : LatticeSpace R G ι) (x : G) : ι → R := fun i => (u i).coeff x

omit [AddCommGroup G] in
@[simp] theorem valueAt_apply (u : LatticeSpace R G ι) (x : G) (i : ι) :
    valueAt u x i = (u i).coeff x :=
  rfl

/-- The support of a vector: the finite set of points where it is nonzero.
(notes: `def:qca-space`) -/
def supp [DecidableEq G] [Fintype ι] (u : LatticeSpace R G ι) : Finset G :=
  Finset.univ.biUnion fun i => (u i).coeff.support

omit [AddCommGroup G] in
theorem mem_supp [DecidableEq G] [Fintype ι] {u : LatticeSpace R G ι} {x : G} :
    x ∈ u.supp ↔ ∃ i, (u i).coeff x ≠ 0 := by
  simp [supp]

/-- The support of a sum lies in the union of the supports. -/
theorem supp_add_subset [DecidableEq G] [Fintype ι] (u w : LatticeSpace R G ι) :
    (u + w).supp ⊆ u.supp ∪ w.supp := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_supp.1 hx
  rw [Finset.mem_union, mem_supp, mem_supp]
  by_contra hc
  push Not at hc
  exact hi (by simp [hc.1 i, hc.2 i])

omit [AddCommGroup G] in
/-- The support of `-u` lies in that of `u`. -/
theorem supp_neg_subset [DecidableEq G] [Fintype ι] (u : LatticeSpace R G ι) :
    (-u).supp ⊆ u.supp := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_supp.1 hx
  exact mem_supp.2 ⟨i, fun h => hi (by simp [h])⟩

omit [AddCommGroup G] in
/-- The support of `r • u` lies in that of `u`. -/
theorem supp_smul_subset [DecidableEq G] [Fintype ι] (r : R) (u : LatticeSpace R G ι) :
    (r • u).supp ⊆ u.supp := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_supp.1 hx
  exact mem_supp.2 ⟨i, fun h => hi (by simp [h])⟩

end LatticeSpace

variable (R G ι)

/-- Translation by `a`, pushing forward: multiplication by the monomial `z^a = single a 1`.
(notes: `def:qca-space`) -/
noncomputable def translate (a : G) : LatticeSpace R G ι →ₗ[R] LatticeSpace R G ι :=
  (LinearMap.lsmul R[G] (LatticeSpace R G ι) (single a 1)).restrictScalars R

variable {R G ι}

theorem translate_apply (a : G) (u : LatticeSpace R G ι) :
    translate R G ι a u = single a (1 : R) • u := by
  simp [translate]

/-- Translation pushes forward: `(κ_{a*} u)(x) = u(x - a)`. (notes: `def:qca-space`) -/
theorem translate_valueAt (a x : G) (u : LatticeSpace R G ι) :
    LatticeSpace.valueAt (translate R G ι a u) x = LatticeSpace.valueAt u (x - a) := by
  funext i
  simp [translate_apply, coeff_single_mul_apply, neg_add_eq_sub]

theorem translate_add (a b : G) :
    translate R G ι (a + b) = translate R G ι a ∘ₗ translate R G ι b := by
  ext u : 1
  simp [translate_apply, smul_smul, single_mul_single]

theorem translate_zero : translate R G ι 0 = LinearMap.id := by
  ext u : 1
  simp [translate_apply, ← one_def]

end QCALean.Core
