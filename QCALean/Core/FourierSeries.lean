/-
Copyright (c) 2026 QCALean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QCALean contributors
-/
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier series of `ℤ`-indexed matrix sequences

Milestone Q6 (closing pass). The two Fourier arguments of milestones Q3 and Q5b, stated once for
a sequence `c : ℤ → Matrix ι ι ℂ` with no symplectic content:

* **Parseval** under absolute summability: for `C(k) = Σ_m c_m e^{−ikm}` and a finite family of
  sites `p : τ → ℤ` with weights `ν`,
  `∫_{−π}^{π} μ̂(k)* C(k) μ̂(k) dk = 2π Σ_{a,b} ν_a* c_{p(a)−p(b)} ν_b`
  with `μ̂(k) = Σ_a ν_a e^{−ik p(a)}` (Q3's proof, for complex cells);
* **Fejér**: for `c` of finite range, if the Hermitian forms `Σ_{x,y ∈ [0,N)} ν_x* c_{x−y} ν_y`
  are non-negative, then `Σ_m e^{−ikm} c_m` is positive semidefinite for every `k` (Q5b's proof).

The real-symmetric cells of Q3 (`QCALean.Bosonic.parseval_region`,
`QCALean.Bosonic.fourier_of_stateConditionPair`) and the complex cells of Q5b
(`QCALean.Bosonic.isStateConditionC_channel_iff_fourier`) are instances.

## Main results

* `QCALean.Core.parseval_matrix`
* `QCALean.Core.posSemidef_of_fejer`
-/

open Matrix
open scoped ComplexOrder ComplexConjugate

namespace QCALean.Core

/-- The complex quadratic form as a double sum (local copy of the identity, which Core cannot
import from BosonicLean). -/
private theorem star_dotProduct_mulVec_sum {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ)
    (c : ι → ℂ) : star c ⬝ᵥ (K *ᵥ c) = ∑ j, ∑ k, conj (c j) * c k * K j k := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Exponentials on `[−π, π]` -/

theorem norm_exp_real_mul_I (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I t

/-- `∫_{−π}^{π} e^{ikj} dk = 2π δ_{j0}`. -/
theorem integral_exp_int (j : ℤ) :
    ∫ k in (-Real.pi)..Real.pi, Complex.exp ((k : ℂ) * j * Complex.I) =
      if j = 0 then 2 * Real.pi else 0 := by
  split_ifs with hj
  · subst hj
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_neg_eq_add, Complex.real_smul, mul_one]
    push_cast; ring
  · have hc : (j : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
    have e : (fun k : ℝ => Complex.exp ((k : ℂ) * j * Complex.I)) =
        fun k : ℝ => Complex.exp ((j : ℂ) * Complex.I * k) := by
      funext k; ring_nf
    rw [e, integral_exp_mul_complex hc]
    have h2 : (j : ℂ) * Complex.I * (Real.pi : ℝ) =
        (j : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) + j * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, zero_div,
      Complex.ofReal_zero]

/-- Parseval for one Fourier series: `∫_{−π}^{π} e^{ikd} Σ_m a_m e^{−ikm} dk = 2π a_d`. -/
theorem integral_fourier_series (a : ℤ → ℂ) (ha : Summable fun m => ‖a m‖) (d : ℤ) :
    ∫ k in (-Real.pi)..Real.pi, Complex.exp ((k : ℂ) * d * Complex.I) *
        ∑' m : ℤ, a m * Complex.exp (-(k : ℂ) * m * Complex.I) = 2 * Real.pi * a d := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  set F : ℤ → ℝ → ℂ := fun m k => a m * Complex.exp ((k : ℂ) * ((d - m : ℤ) : ℂ) * Complex.I)
  have hpt : ∀ k : ℝ, Complex.exp ((k : ℂ) * d * Complex.I) *
      ∑' m : ℤ, a m * Complex.exp (-(k : ℂ) * m * Complex.I) = ∑' m, F m k := by
    intro k
    rw [← Summable.tsum_mul_left]
    · refine tsum_congr fun m => ?_
      simp only [F]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast; ring
    · refine Summable.of_norm_bounded ha fun m => ?_
      rw [norm_mul]
      have : -(k : ℂ) * m * Complex.I = ((-k * m : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, norm_exp_real_mul_I, mul_one]
  have hnorm : ∀ m k, ‖F m k‖ = ‖a m‖ := by
    intro m k
    simp only [F, norm_mul]
    have : (k : ℂ) * ((d - m : ℤ) : ℂ) * Complex.I = ((k * (d - m : ℤ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, norm_exp_real_mul_I, mul_one]
  have hcont : ∀ m, Continuous (F m) := fun m => by fun_prop
  have hint : ∀ m, MeasureTheory.Integrable (F m)
      (MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := fun m =>
    ((hcont m).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hsum : Summable fun m => ∫ k in Set.Ioc (-Real.pi) Real.pi, ‖F m k‖ := by
    simp only [hnorm, MeasureTheory.integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      smul_eq_mul]
    exact ha.mul_left _
  rw [intervalIntegral.integral_congr (fun k _ => hpt k), intervalIntegral.integral_of_le hle,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum]
  have hterm : ∀ m, ∫ k in Set.Ioc (-Real.pi) Real.pi, F m k =
      a m * if d - m = 0 then (2 * Real.pi : ℂ) else 0 := by
    intro m
    rw [← intervalIntegral.integral_of_le hle]
    simp only [F]
    rw [intervalIntegral.integral_const_mul, integral_exp_int]
    split_ifs <;> simp
  simp only [hterm]
  rw [tsum_eq_single d]
  · simp; ring
  · intro m hm
    simp [show d - m ≠ 0 by omega]

/-- A function with values in `[0, ∞)` whose integral over `[−π, π]` is `2π Q` has `Q ≥ 0`. -/
theorem nonneg_of_integral_eq {f : ℝ → ℂ} (hf : ∀ k, 0 ≤ f k) {Q : ℂ}
    (hQ : ∫ k in (-Real.pi)..Real.pi, f k = 2 * Real.pi * Q) : 0 ≤ Q := by
  have hfre : f = fun k => ((f k).re : ℂ) := funext fun k => by
    apply Complex.ext
    · simp
    · simp [← (Complex.nonneg_iff.1 (hf k)).2]
  rw [hfre, intervalIntegral.integral_ofReal] at hQ
  have hnn : 0 ≤ ∫ k in (-Real.pi)..Real.pi, (f k).re :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun k _ =>
      (Complex.nonneg_iff.1 (hf k)).1
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hQ' : Q = (((∫ k in (-Real.pi)..Real.pi, (f k).re) / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    rw [hQ]
    field_simp
  rw [hQ', Complex.zero_le_real]
  exact div_nonneg hnn (by positivity)

/-- The complex conjugate of an integral over `[−π, π]`. -/
theorem conj_integral_pi (f : ℝ → ℂ) :
    starRingEnd ℂ (∫ k in (-Real.pi)..Real.pi, f k) =
      ∫ k in (-Real.pi)..Real.pi, starRingEnd ℂ (f k) := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
    ← integral_conj]

/-! ### Parseval -/

/-- The symbol `Σ_m c_m e^{−ikm}` of an absolutely summable sequence is continuous in `k`. -/
theorem continuous_matrixSeries {ι : Type*} {c : ℤ → Matrix ι ι ℂ}
    (hc : ∀ i j, Summable fun m => ‖c m i j‖) (i j : ι) :
    Continuous fun k : ℝ => ∑' m : ℤ, c m i j * Complex.exp (-(k : ℂ) * m * Complex.I) := by
  refine continuous_tsum (fun m => by fun_prop) (hc i j) fun m k => ?_
  rw [norm_mul]
  have : -(k : ℂ) * m * Complex.I = ((-k * m : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, norm_exp_real_mul_I, mul_one]

/-- Milestone Q6, Parseval for `ℤ`-indexed matrix sequences: for an absolutely summable
`c : ℤ → Matrix ι ι ℂ` with symbol `C(k) = Σ_m c_m e^{−ikm}`, sites `p : τ → ℤ` and weights `ν`,
`∫_{−π}^{π} μ̂(k)* C(k) μ̂(k) dk = 2π Σ_{a,b} Σ_{i,j} ν̄_{a,i} ν_{b,j} (c_{p(a)−p(b)})_{ij}`, where
`μ̂(k)_i = Σ_a ν_{a,i} e^{−ik p(a)}`. -/
theorem parseval_matrix {ι τ : Type*} [Fintype ι] [Fintype τ] {c : ℤ → Matrix ι ι ℂ}
    (hc : ∀ i j, Summable fun m => ‖c m i j‖) {C : ℝ → Matrix ι ι ℂ}
    (hC : ∀ k i j, C k i j = ∑' m : ℤ, c m i j * Complex.exp (-(k : ℂ) * m * Complex.I))
    (p : τ → ℤ) (ν : τ → ι → ℂ) :
    ∫ k in (-Real.pi)..Real.pi,
      star (fun i => ∑ a, ν a i * Complex.exp (-(k : ℂ) * (p a : ℤ) * Complex.I)) ⬝ᵥ
        (C k *ᵥ fun i => ∑ a, ν a i * Complex.exp (-(k : ℂ) * (p a : ℤ) * Complex.I)) =
      2 * Real.pi * ∑ a, ∑ b, ∑ i, ∑ j, conj (ν a i) * ν b j * c (p a - p b) i j := by
  set S : ι → ι → ℝ → ℂ := fun i j k =>
    ∑' m : ℤ, c m i j * Complex.exp (-(k : ℂ) * m * Complex.I)
  have hpt : ∀ k : ℝ,
      star (fun i => ∑ a, ν a i * Complex.exp (-(k : ℂ) * (p a : ℤ) * Complex.I)) ⬝ᵥ
        (C k *ᵥ fun i => ∑ a, ν a i * Complex.exp (-(k : ℂ) * (p a : ℤ) * Complex.I)) =
      ∑ a, ∑ b, ∑ i, ∑ j, conj (ν a i) * ν b j *
        (Complex.exp ((k : ℂ) * ((p a - p b : ℤ) : ℂ) * Complex.I) * S i j k) := by
    intro k
    rw [star_dotProduct_mulVec_sum]
    simp only [hC, map_sum, map_mul, ← Complex.exp_conj, Finset.sum_mul, Finset.mul_sum]
    set G : τ → τ → ι → ι → ℂ := fun a b i j =>
      conj (ν a i) * ν b j *
        (Complex.exp ((k : ℂ) * ((p a - p b : ℤ) : ℂ) * Complex.I) * S i j k)
    calc _ = ∑ i, ∑ j, ∑ b, ∑ a, G a b i j := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
          have : Complex.exp (conj (-(k : ℂ)) * conj ((p a : ℤ) : ℂ) * conj Complex.I) *
              Complex.exp (-(k : ℂ) * ((p b : ℤ) : ℂ) * Complex.I) =
              Complex.exp ((k : ℂ) * ((p a - p b : ℤ) : ℂ) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            simp only [map_neg, Complex.conj_I, Complex.conj_ofReal, map_intCast]
            push_cast; ring
          simp only [G, S]
          linear_combination (conj (ν a i) * ν b j *
            ∑' m : ℤ, c m i j * Complex.exp (-(k : ℂ) * m * Complex.I)) * this
      _ = ∑ i, ∑ j, ∑ a, ∑ b, G a b i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ b, G a b i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ j, ∑ b, G a b i j := Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, ∑ j, G a b i j :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hcont : ∀ (a b : τ) (i j : ι), Continuous fun k : ℝ =>
      conj (ν a i) * ν b j *
        (Complex.exp ((k : ℂ) * ((p a - p b : ℤ) : ℂ) * Complex.I) * S i j k) :=
    fun a b i j => by
      have := continuous_matrixSeries hc i j
      fun_prop
  rw [intervalIntegral.integral_congr (fun k _ => hpt k)]
  rw [intervalIntegral.integral_finsetSum fun a _ =>
    (continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => hcont a b i j).intervalIntegrable _ _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [intervalIntegral.integral_finsetSum fun b _ =>
    (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => hcont a b i j).intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (continuous_finsetSum _ fun j _ => hcont a b i j).intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => (hcont a b i j).intervalIntegrable _ _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  simp only [S]
  rw [integral_fourier_series _ (hc i j)]
  ring

/-! ### Fejér -/

/-- The Fejér count: `Σ_{x,y ∈ [0,N)} f(x − y) = Σ_m f(m) #{x ∈ [0,N) | x − m ∈ [0,N)}` for `f`
supported in `[−R, R]`. -/
theorem double_sum_eq_count (f : ℤ → ℂ) (R : ℕ) (hf : ∀ m, (R : ℤ) < |m| → f m = 0) (N : ℕ) :
    ∑ x ∈ Finset.Ico (0 : ℤ) N, ∑ y ∈ Finset.Ico (0 : ℤ) N, f (x - y) =
      ∑ m ∈ Finset.Icc (-(R : ℤ)) R,
        (((Finset.Ico (0 : ℤ) N).filter fun x => x - m ∈ Finset.Ico (0 : ℤ) N).card : ℂ) *
          f m := by
  set T := Finset.Ico (0 : ℤ) N
  have hsplit : ∀ d : ℤ, f d = ∑ m ∈ Finset.Icc (-(R : ℤ)) R, if d = m then f m else 0 := by
    intro d
    rw [Finset.sum_ite_eq]
    split_ifs with hd
    · rfl
    · refine hf d ?_
      rw [Finset.mem_Icc, not_and_or] at hd
      rw [lt_abs]
      omega
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsplit (x - y)]
  calc _ = ∑ x ∈ T, ∑ m ∈ Finset.Icc (-(R : ℤ)) R, ∑ y ∈ T, if x - y = m then f m else 0 :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ m ∈ Finset.Icc (-(R : ℤ)) R, ∑ x ∈ T, ∑ y ∈ T, if x - y = m then f m else 0 :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        have e : ∀ x y : ℤ, (x - y = m) ↔ (x - m = y) := fun x y => by omega
        simp_rw [e, Finset.sum_ite_eq]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

theorem card_filter_Ico_bounds (N : ℕ) (m : ℤ) :
    ((Finset.Ico (0 : ℤ) N).filter fun x => x - m ∈ Finset.Ico (0 : ℤ) N).card ≤ N ∧
      N ≤ ((Finset.Ico (0 : ℤ) N).filter fun x => x - m ∈ Finset.Ico (0 : ℤ) N).card +
        m.natAbs := by
  have hT : (Finset.Ico (0 : ℤ) N).card = N := by simp
  constructor
  · exact (Finset.card_filter_le _ _).trans hT.le
  · have hsum := Finset.card_filter_add_card_filter_not
      (s := Finset.Ico (0 : ℤ) N) (fun x => x - m ∈ Finset.Ico (0 : ℤ) N)
    have hsub : ((Finset.Ico (0 : ℤ) N).filter fun x => x - m ∉ Finset.Ico (0 : ℤ) N) ⊆
        Finset.Ico 0 m ∪ Finset.Ico (N + m) N := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at hx ⊢
      omega
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [Int.card_Ico] at hc
    omega

/-- The Fejér estimate: `Re Σ_{x,y ∈ [0,N)} f(x−y) ≤ N Re Σ_m f(m) + R Σ_m |f(m)|`. -/
theorem re_double_sum_le (f : ℤ → ℂ) (R : ℕ) (hf : ∀ m, (R : ℤ) < |m| → f m = 0) (N : ℕ) :
    (∑ x ∈ Finset.Ico (0 : ℤ) N, ∑ y ∈ Finset.Ico (0 : ℤ) N, f (x - y)).re ≤
      N * (∑ m ∈ Finset.Icc (-(R : ℤ)) R, f m).re +
        R * ∑ m ∈ Finset.Icc (-(R : ℤ)) R, ‖f m‖ := by
  rw [double_sum_eq_count f R hf, Complex.re_sum, Complex.re_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m hm => ?_
  obtain ⟨h1, h2⟩ := card_filter_Ico_bounds N m
  set c := ((Finset.Ico (0 : ℤ) N).filter fun x => x - m ∈ Finset.Ico (0 : ℤ) N).card
  have hmR : m.natAbs ≤ R := by
    rw [Finset.mem_Icc] at hm; omega
  have hc1 : (c : ℝ) ≤ N := by exact_mod_cast h1
  have hc2 : (N : ℝ) - c ≤ R := by
    have : N ≤ c + R := by omega
    have : (N : ℝ) ≤ c + R := by exact_mod_cast this
    linarith
  have hx := Complex.abs_re_le_norm (f m)
  have hre : ((c : ℂ) * f m).re = c * (f m).re := by
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  rw [hre]
  have hn : 0 ≤ ‖f m‖ := norm_nonneg _
  nlinarith [abs_le.1 hx, mul_le_mul_of_nonneg_right hc2 hn,
    mul_le_mul_of_nonneg_left (neg_le_of_abs_le hx) (sub_nonneg.2 hc1)]

/-- The Hermitian form `Σ_{i,j} conj v_i v_j M_{ij}`, linear in `M`. -/
theorem quad_sum_smul {ι : Type*} [Fintype ι] (v : ι → ℂ) (s : Finset ℤ) (e : ℤ → ℂ)
    (C : ℤ → Matrix ι ι ℂ) :
    star v ⬝ᵥ ((∑ m ∈ s, e m • C m) *ᵥ v) =
      ∑ m ∈ s, e m * ∑ i, ∑ j, conj (v i) * v j * C m i j := by
  rw [star_dotProduct_mulVec_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  calc _ = ∑ i, ∑ m ∈ s, ∑ j, conj (v i) * v j * (e m * C m i j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m ∈ s, ∑ i, ∑ j, conj (v i) * v j * (e m * C m i j) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring

/-- Milestone Q6, the Fejér argument for `ℤ`-indexed matrix sequences of finite range: if the
Hermitian form of the cells is non-negative on every interval, the finite Fourier sum of the
cells is positive semidefinite. -/
theorem posSemidef_of_fejer {ι : Type*} [Fintype ι] {c : ℤ → Matrix ι ι ℂ} (R : ℕ)
    (hc : ∀ m, (R : ℤ) < |m| → c m = 0) (k : ℝ)
    (herm : (∑ m ∈ Finset.Icc (-(R : ℤ)) R,
      Complex.exp (-(k : ℂ) * m * Complex.I) • c m).IsHermitian)
    (hQ : ∀ (N : ℕ) (ν : ℤ → ι → ℂ), 0 ≤ (∑ x ∈ Finset.Ico (0 : ℤ) N,
      ∑ y ∈ Finset.Ico (0 : ℤ) N, ∑ i, ∑ j, conj (ν x i) * ν y j * c (x - y) i j).re) :
    (∑ m ∈ Finset.Icc (-(R : ℤ)) R,
      Complex.exp (-(k : ℂ) * m * Complex.I) • c m).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg herm fun v => ?_
  set F : ℤ → ℂ := fun m => Complex.exp (-(k : ℂ) * m * Complex.I) *
    ∑ i, ∑ j, conj (v i) * v j * c m i j with hF
  have hS : star v ⬝ᵥ ((∑ m ∈ Finset.Icc (-(R : ℤ)) R,
      Complex.exp (-(k : ℂ) * m * Complex.I) • c m) *ᵥ v) =
      ∑ m ∈ Finset.Icc (-(R : ℤ)) R, F m := quad_sum_smul _ _ _ _
  have him := herm.im_star_dotProduct_mulVec_self v
  rw [Complex.nonneg_iff]
  refine ⟨?_, him.symm⟩
  rw [hS]
  by_contra hneg
  push Not at hneg
  have hF0 : ∀ m, (R : ℤ) < |m| → F m = 0 := by
    intro m hm
    simp [hF, hc m hm]
  set C := ∑ m ∈ Finset.Icc (-(R : ℤ)) R, ‖F m‖
  set Sr := (∑ m ∈ Finset.Icc (-(R : ℤ)) R, F m).re
  have hbound : ∀ N : ℕ, 0 ≤ N * Sr + R * C := by
    intro N
    refine le_trans ?_ (re_double_sum_le F R hF0 N)
    have hq := hQ N fun x i => Complex.exp (Complex.I * k * x) * v i
    have e : (∑ x ∈ Finset.Ico (0 : ℤ) N, ∑ y ∈ Finset.Ico (0 : ℤ) N, ∑ i, ∑ j,
        conj (Complex.exp (Complex.I * k * x) * v i) *
          (Complex.exp (Complex.I * k * y) * v j) * c (x - y) i j) =
        ∑ x ∈ Finset.Ico (0 : ℤ) N, ∑ y ∈ Finset.Ico (0 : ℤ) N, F (x - y) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [hF, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← Complex.exp_conj]
      have : Complex.exp (conj (Complex.I * k * x)) * Complex.exp (Complex.I * k * y) =
          Complex.exp (-(k : ℂ) * ((x - y : ℤ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
        push_cast
        ring
      linear_combination (conj (v i) * v j * c (x - y) i j) * this
    rw [e] at hq
    exact hq
  obtain ⟨N, hN⟩ := exists_nat_gt (R * C / (-Sr))
  have := hbound N
  have hpos : 0 < -Sr := by linarith
  rw [div_lt_iff₀ hpos] at hN
  linarith [this, hN]

end QCALean.Core
