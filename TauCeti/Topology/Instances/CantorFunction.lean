/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.Instances.CantorSet
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The Cantor–Lebesgue Function and Non-Absolutely-Continuous Homeomorphism

This file constructs the classical ternary Cantor–Lebesgue function ("devil's staircase")
`cantorFunction : ℝ → ℝ` and the strictly increasing homeomorphism
`cantorHomeomorphFun (t : ℝ) = (t + cantorFunction t) / 2`, and establishes their analytical,
measure-theoretic, and variational properties:

1. **Measure of the ternary Cantor set**:
   * `TauCeti.volume_preCantorSet`: `volume (preCantorSet n) = (2 / 3 : ℝ≥0∞) ^ n`.
   * `TauCeti.volume_cantorSet`: `volume cantorSet = 0`.
2. **Construction and self-similarity of the Cantor–Lebesgue function (`TauCeti.cantorFunction`)**:
   * Defined as the uniform limit of the piecewise-linear approximations `cantorApprox n` generated
     by the functional operator `cantorStepFun f x = (f (3 * x) + f (3 * x - 2)) / 2`.
   * Continuity (`continuous_cantorFunction`), monotonicity (`monotone_cantorFunction`), boundary
     values (`cantorFunction_of_nonpos`, `cantorFunction_zero`, `cantorFunction_of_one_le`,
     `cantorFunction_one`), range (`cantorFunction_nonneg`, `cantorFunction_le_one`,
     `surjOn_cantorFunction_Icc`, `image_cantorFunction_Icc`), self-similarity
     (`cantorFunction_eq_cantorStepFun`, `cantorFunction_div_three`,
     `cantorFunction_add_two_div_three`), constancy on the middle third (`cantorFunction_eq_half`),
     and reflection symmetry (`cantorFunction_sub_one_symm`).
3. **Vanishing derivative outside `cantorSet` and almost everywhere**:
   * For every `x ∉ cantorSet`, `cantorFunction` is constant on a neighborhood of `x`
     (`eventuallyEq_const_cantorFunction_of_not_mem_cantorSet`), hence differentiable at `x` with
     derivative `0` (`hasDerivAt_cantorFunction_zero`, `deriv_cantorFunction_eq_zero`).
   * Consequently `deriv cantorFunction =ᵐ[volume] 0` (`ae_deriv_cantorFunction_eq_zero`),
     `∫⁻ x in Icc 0 1, ‖deriv cantorFunction x‖ₑ = 0` (`lintegral_enorm_deriv_cantorFunction`),
     and `∫ x in (0 : ℝ)..1, deriv cantorFunction x = 0` (`intervalIntegral_deriv_cantorFunction`).
4. **Total variation vs. derivative integral and failure of absolute continuity**:
   * `eVariationOn_cantorFunction_Icc : eVariationOn cantorFunction (Icc 0 1) = 1`.
   * `boundedVariationOn_cantorFunction_Icc : BoundedVariationOn cantorFunction (Icc 0 1)`.
   * `eVariationOn_cantorFunction_ne_lintegral_enorm_deriv`:
     `eVariationOn cantorFunction (Icc 0 1) ≠ ∫⁻ x in Icc 0 1, ‖deriv cantorFunction x‖ₑ`.
   * `not_absolutelyContinuousOnInterval_cantorFunction`:
     `¬ AbsolutelyContinuousOnInterval cantorFunction 0 1`.
5. **Strictly increasing non-absolutely-continuous homeomorphism (`TauCeti.cantorHomeomorphFun`,
   `TauCeti.cantorHomeomorph`)**:
   * `cantorHomeomorphFun t = (t + cantorFunction t) / 2` is strictly monotone, continuous, and
     surjective, inducing `cantorOrderIso : ℝ ≃o ℝ` and `cantorHomeomorph : ℝ ≃ₜ ℝ` mapping
     `Icc 0 1` onto `Icc 0 1`.
   * `eVariationOn_cantorHomeomorphFun_Icc : eVariationOn cantorHomeomorphFun (Icc 0 1) = 1`, while
     `deriv cantorHomeomorphFun x = 1 / 2` for `x ∉ cantorSet`, so
     `∫⁻ x in Icc 0 1, ‖deriv cantorHomeomorphFun x‖ₑ = ENNReal.ofReal (1 / 2) < 1` and
     `¬ AbsolutelyContinuousOnInterval cantorHomeomorphFun 0 1`.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti

/-! ### Preimage characterizations and Lebesgue measure of the ternary Cantor set -/

/-- The left-third rescaling image `(· / 3) '' s` coincides with the preimage `(3 * ·) ⁻¹' s`. -/
theorem image_div_three_eq_preimage (s : Set ℝ) :
    (· / 3) '' s = (3 * ·) ⁻¹' s := by
  ext x
  simp only [mem_image, mem_preimage]
  exact ⟨by rintro ⟨y, hy, rfl⟩; ring_nf; exact hy, fun hx ↦ ⟨3 * x, hx, by ring⟩⟩

/-- The right-third rescaling image `(fun y ↦ (2 + y) / 3) '' s` coincides with the preimage
`(fun x ↦ -2 + 3 * x) ⁻¹' s`. -/
theorem image_two_add_div_three_eq_preimage (s : Set ℝ) :
    (fun y : ℝ ↦ (2 + y) / 3) '' s = ((fun z : ℝ ↦ -2 + z) ∘ (3 * ·)) ⁻¹' s := by
  ext x
  simp only [mem_image, mem_preimage, Function.comp_apply]
  exact ⟨by rintro ⟨y, hy, rfl⟩; ring_nf; exact hy, fun hx ↦ ⟨-2 + 3 * x, hx, by ring⟩⟩

/-- Membership in `preCantorSet (n + 1)` in terms of `3 * x` and `3 * x - 2`. -/
theorem mem_preCantorSet_succ_iff {n : ℕ} {x : ℝ} :
    x ∈ preCantorSet (n + 1) ↔ 3 * x ∈ preCantorSet n ∨ 3 * x - 2 ∈ preCantorSet n := by
  rw [preCantorSet_succ, mem_union, image_div_three_eq_preimage,
    image_two_add_div_three_eq_preimage, mem_preimage, mem_preimage, Function.comp_apply]
  ring_nf

/-- If `x ∉ preCantorSet (n + 1)`, then neither `3 * x` nor `3 * x - 2` lies in
`preCantorSet n`. -/
theorem not_mem_preCantorSet_of_not_mem_succ {n : ℕ} {x : ℝ}
    (hx : x ∉ preCantorSet (n + 1)) :
    3 * x ∉ preCantorSet n ∧ 3 * x - 2 ∉ preCantorSet n := by
  rwa [mem_preCantorSet_succ_iff, not_or] at hx

/-- The Lebesgue measure of `preCantorSet n` is `(2 / 3) ^ n`. -/
theorem volume_preCantorSet (n : ℕ) :
    volume (preCantorSet n) = (2 / 3 : ℝ≥0∞) ^ n := by
  induction n with
  | zero =>
    simp [preCantorSet_zero, Real.volume_Icc]
  | succ n ih =>
    have hdisj : Disjoint ((· / 3) '' preCantorSet n)
        ((fun y : ℝ ↦ (2 + y) / 3) '' preCantorSet n) := by
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hx1 : x ≤ 1 := (preCantorSet_subset_unitInterval hx).2
      have hy0 : 0 ≤ y := (preCantorSet_subset_unitInterval hy).1
      linarith
    have hmeas2 : MeasurableSet ((fun y : ℝ ↦ (2 + y) / 3) '' preCantorSet n) := by
      rw [image_two_add_div_three_eq_preimage]
      exact (isClosed_preCantorSet n).measurableSet.preimage (by fun_prop)
    have hthird : ENNReal.ofReal |(3 : ℝ)⁻¹| = (1 / 3 : ℝ≥0∞) := by
      rw [abs_of_pos (by norm_num), ← one_div, ENNReal.ofReal_div_of_pos (by norm_num),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    rw [preCantorSet_succ, measure_union hdisj hmeas2, image_div_three_eq_preimage,
      image_two_add_div_three_eq_preimage, Set.preimage_comp,
      Real.volume_preimage_mul_left (by norm_num), Real.volume_preimage_mul_left (by norm_num),
      measure_preimage_add, hthird, ih, ← add_mul, pow_succ']
    congr 1
    rw [ENNReal.div_add_div_same]
    norm_num

/-- **The ternary Cantor set has Lebesgue measure zero**. -/
@[simp]
theorem volume_cantorSet : volume cantorSet = 0 := by
  apply le_antisymm _ bot_le
  have hle : ∀ n : ℕ, volume cantorSet ≤ (2 / 3 : ℝ≥0∞) ^ n := fun n ↦ by
    rw [← volume_preCantorSet n]
    exact measure_mono (iInter_subset preCantorSet n)
  have htend : Tendsto (fun n : ℕ ↦ (2 / 3 : ℝ≥0∞) ^ n) atTop (𝓝 0) := by
    refine ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ?_
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num)), one_mul]
    norm_num
  exact ge_of_tendsto htend (Eventually.of_forall hle)

/-! ### The Cantor–Lebesgue functional operator and piecewise-linear approximations -/

/-- One step of the Cantor–Lebesgue functional iteration:
`cantorStepFun f x = (f (3 * x) + f (3 * x - 2)) / 2`.
When `f = 0` on `(-∞, 0]` and `f = 1` on `[1, ∞)`, this equals `f (3 * x) / 2` on `(-∞, 1/3]`,
`1 / 2` on `[1/3, 2/3]`, and `(f (3 * x - 2) + 1) / 2` on `[2/3, ∞)`. -/
def cantorStepFun (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (f (3 * x) + f (3 * x - 2)) / 2

/-- Iterative piecewise-linear approximations to the Cantor–Lebesgue function, starting from the
unit clamp `max 0 (min 1 x)`. -/
def cantorApprox : ℕ → ℝ → ℝ
  | 0 => fun x ↦ max 0 (min 1 x)
  | n + 1 => cantorStepFun (cantorApprox n)

/-- Base step of `cantorApprox`. -/
@[simp]
theorem cantorApprox_zero (x : ℝ) : cantorApprox 0 x = max 0 (min 1 x) := by
  rfl

/-- Inductive step of `cantorApprox`. -/
theorem cantorApprox_succ (n : ℕ) (x : ℝ) :
    cantorApprox (n + 1) x = (cantorApprox n (3 * x) + cantorApprox n (3 * x - 2)) / 2 := by
  rfl

/-- `cantorApprox n` vanishes on `(-∞, 0]`. -/
theorem cantorApprox_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    cantorApprox n x = 0 := by
  induction n generalizing x with
  | zero =>
    simp [cantorApprox_zero, min_eq_right (hx.trans zero_le_one), hx]
  | succ n ih =>
    rw [cantorApprox_succ, ih (by linarith), ih (by linarith)]
    ring

/-- `cantorApprox n` equals `1` on `[1, ∞)`. -/
theorem cantorApprox_of_one_le (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    cantorApprox n x = 1 := by
  induction n generalizing x with
  | zero =>
    simp [cantorApprox_zero, min_eq_left hx]
  | succ n ih =>
    rw [cantorApprox_succ, ih (by linarith), ih (by linarith)]
    ring

/-- Each approximation `cantorApprox n` is continuous. -/
@[fun_prop]
theorem continuous_cantorApprox (n : ℕ) : Continuous (cantorApprox n) := by
  induction n with
  | zero =>
    unfold cantorApprox
    fun_prop
  | succ n ih =>
    unfold cantorApprox cantorStepFun
    fun_prop

/-- Each approximation `cantorApprox n` is monotone. -/
theorem monotone_cantorApprox (n : ℕ) : Monotone (cantorApprox n) := by
  induction n with
  | zero =>
    intro x y hxy
    simp only [cantorApprox_zero]
    exact max_le_max le_rfl (min_le_min le_rfl hxy)
  | succ n ih =>
    intro x y hxy
    rw [cantorApprox_succ, cantorApprox_succ]
    linarith [ih (by linarith : 3 * x ≤ 3 * y), ih (by linarith : 3 * x - 2 ≤ 3 * y - 2)]

/-- `0 ≤ cantorApprox n x` for all `n` and `x`. -/
theorem cantorApprox_nonneg (n : ℕ) (x : ℝ) : 0 ≤ cantorApprox n x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [cantorApprox_of_nonpos n hx]
  · rw [← cantorApprox_of_nonpos n le_rfl]
    exact monotone_cantorApprox n hx.le

/-- `cantorApprox n x ≤ 1` for all `n` and `x`. -/
theorem cantorApprox_le_one (n : ℕ) (x : ℝ) : cantorApprox n x ≤ 1 := by
  rcases le_or_gt 1 x with hx | hx
  · rw [cantorApprox_of_one_le n hx]
  · rw [← cantorApprox_of_one_le n le_rfl]
    exact monotone_cantorApprox n hx.le

/-- Reflection symmetry `cantorApprox n (1 - x) = 1 - cantorApprox n x`. -/
theorem cantorApprox_sub_one_symm (n : ℕ) (x : ℝ) :
    cantorApprox n (1 - x) = 1 - cantorApprox n x := by
  induction n generalizing x with
  | zero =>
    simp only [cantorApprox_zero]
    rcases le_total x 0 with hx | hx
    · have h1 : 1 ≤ 1 - x := by linarith
      rw [min_eq_right (hx.trans zero_le_one), max_eq_left hx, min_eq_left h1,
        max_eq_right zero_le_one, sub_zero]
    · rcases le_total 1 x with hx1 | hx1
      · have h2 : 1 - x ≤ 0 := by linarith
        rw [min_eq_left hx1, max_eq_right zero_le_one, min_eq_right (h2.trans zero_le_one),
          max_eq_left h2, sub_self]
      · have h1 : 1 - x ≤ 1 := by linarith
        have h2 : 0 ≤ 1 - x := by linarith
        rw [min_eq_right hx1, max_eq_right hx, min_eq_right h1, max_eq_right h2]
  | succ n ih =>
    have h1 : 3 * (1 - x) - 2 = 1 - 3 * x := by ring
    have h2 : 3 * (1 - x) = 1 - (3 * x - 2) := by ring
    rw [cantorApprox_succ, cantorApprox_succ, h1, h2, ih (3 * x - 2), ih (3 * x)]
    ring

/-- Uniform geometric contraction between consecutive approximations `cantorApprox n` and
`cantorApprox (n + 1)`. -/
theorem dist_cantorApprox_succ_le (n : ℕ) (x : ℝ) :
    dist (cantorApprox n x) (cantorApprox (n + 1) x) ≤ (1 / 2 : ℝ) ^ n := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero, Real.dist_eq, abs_le]
    have h0 := cantorApprox_nonneg 0 x
    have h1 := cantorApprox_le_one 0 x
    have h2 := cantorApprox_nonneg 1 x
    have h3 := cantorApprox_le_one 1 x
    constructor <;> linarith
  | succ n ih =>
    rw [cantorApprox_succ, cantorApprox_succ, Real.dist_eq]
    rcases le_total x (1 / 2) with hx | hx
    · have hle : 3 * x - 2 ≤ 0 := by linarith
      rw [cantorApprox_of_nonpos n hle, cantorApprox_of_nonpos (n + 1) hle]
      have hdist := ih (3 * x)
      rw [Real.dist_eq] at hdist
      calc |(cantorApprox n (3 * x) + 0) / 2 - (cantorApprox (n + 1) (3 * x) + 0) / 2|
          = |cantorApprox n (3 * x) - cantorApprox (n + 1) (3 * x)| / 2 := by
            rw [add_zero, add_zero, ← sub_div, abs_div, abs_two]
        _ ≤ (1 / 2 : ℝ) ^ n / 2 := by linarith
        _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
    · have hge : 1 ≤ 3 * x := by linarith
      rw [cantorApprox_of_one_le n hge, cantorApprox_of_one_le (n + 1) hge]
      have hdist := ih (3 * x - 2)
      rw [Real.dist_eq] at hdist
      calc |(1 + cantorApprox n (3 * x - 2)) / 2 - (1 + cantorApprox (n + 1) (3 * x - 2)) / 2|
          = |cantorApprox n (3 * x - 2) - cantorApprox (n + 1) (3 * x - 2)| / 2 := by
            rw [show (1 + cantorApprox n (3 * x - 2)) / 2 -
              (1 + cantorApprox (n + 1) (3 * x - 2)) / 2 =
              (cantorApprox n (3 * x - 2) - cantorApprox (n + 1) (3 * x - 2)) / 2 by ring,
              abs_div, abs_two]
        _ ≤ (1 / 2 : ℝ) ^ n / 2 := by linarith
        _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

/-- For each `x : ℝ`, the sequence `n ↦ cantorApprox n x` is Cauchy. -/
theorem cauchySeq_cantorApprox (x : ℝ) : CauchySeq fun n ↦ cantorApprox n x := by
  refine cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num) fun n ↦ ?_
  simpa using dist_cantorApprox_succ_le n x

/-! ### The Cantor–Lebesgue function and its basic properties -/

/-- **The Cantor–Lebesgue function** ("devil's staircase") `cantorFunction : ℝ → ℝ`, defined as the
limit of the piecewise-linear approximations `cantorApprox n`. -/
def cantorFunction (x : ℝ) : ℝ :=
  limUnder atTop fun n ↦ cantorApprox n x

/-- Pointwise convergence of `cantorApprox n x` to `cantorFunction x`. -/
theorem tendsto_cantorApprox (x : ℝ) :
    Tendsto (fun n ↦ cantorApprox n x) atTop (𝓝 (cantorFunction x)) :=
  (cauchySeq_cantorApprox x).tendsto_limUnder

/-- Quantitative uniform error bound between `cantorApprox n` and `cantorFunction`. -/
theorem dist_cantorApprox_cantorFunction_le (n : ℕ) (x : ℝ) :
    dist (cantorApprox n x) (cantorFunction x) ≤ 2 * (1 / 2 : ℝ) ^ n := by
  have h := dist_le_of_le_geometric_of_tendsto (1 / 2) 1 (by norm_num)
    (fun k ↦ by simpa using dist_cantorApprox_succ_le k x) (tendsto_cantorApprox x) n
  ring_nf at h ⊢
  exact h

/-- `cantorApprox` converges uniformly on `ℝ` to `cantorFunction`. -/
theorem tendstoUniformly_cantorApprox :
    TendstoUniformly cantorApprox cantorFunction atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htend : Tendsto (fun n : ℕ ↦ 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul 2
  filter_upwards [(Tendsto.eventually_lt_const hε htend)] with n hn x
  rw [dist_comm]
  exact (dist_cantorApprox_cantorFunction_le n x).trans_lt hn

/-- **Continuity of the Cantor–Lebesgue function**. -/
@[fun_prop]
theorem continuous_cantorFunction : Continuous cantorFunction :=
  tendstoUniformly_cantorApprox.continuous (Eventually.of_forall continuous_cantorApprox).frequently

/-- **Monotonicity of the Cantor–Lebesgue function**. -/
theorem monotone_cantorFunction : Monotone cantorFunction :=
  fun x y hxy ↦ le_of_tendsto_of_tendsto (tendsto_cantorApprox x) (tendsto_cantorApprox y)
    (Eventually.of_forall fun n ↦ monotone_cantorApprox n hxy)

/-- Fixed-point equation of the Cantor–Lebesgue function under `cantorStepFun`:
`cantorFunction x = (cantorFunction (3 * x) + cantorFunction (3 * x - 2)) / 2`. -/
theorem cantorFunction_eq_cantorStepFun (x : ℝ) :
    cantorFunction x = (cantorFunction (3 * x) + cantorFunction (3 * x - 2)) / 2 := by
  have h1 : Tendsto (fun n ↦ cantorApprox (n + 1) x) atTop (𝓝 (cantorFunction x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_cantorApprox x)
  have h2 : Tendsto (fun n ↦ (cantorApprox n (3 * x) + cantorApprox n (3 * x - 2)) / 2) atTop
      (𝓝 ((cantorFunction (3 * x) + cantorFunction (3 * x - 2)) / 2)) :=
    ((tendsto_cantorApprox (3 * x)).add (tendsto_cantorApprox (3 * x - 2))).div_const 2
  exact tendsto_nhds_unique h1 h2

/-- `cantorFunction` vanishes on `(-∞, 0]`. -/
theorem cantorFunction_of_nonpos {x : ℝ} (hx : x ≤ 0) : cantorFunction x = 0 := by
  apply tendsto_nhds_unique (tendsto_cantorApprox x)
  simp [cantorApprox_of_nonpos _ hx]

/-- `cantorFunction 0 = 0`. -/
@[simp]
theorem cantorFunction_zero : cantorFunction 0 = 0 :=
  cantorFunction_of_nonpos le_rfl

/-- `cantorFunction` equals `1` on `[1, ∞)`. -/
theorem cantorFunction_of_one_le {x : ℝ} (hx : 1 ≤ x) : cantorFunction x = 1 := by
  apply tendsto_nhds_unique (tendsto_cantorApprox x)
  simp [cantorApprox_of_one_le _ hx]

/-- `cantorFunction 1 = 1`. -/
@[simp]
theorem cantorFunction_one : cantorFunction 1 = 1 :=
  cantorFunction_of_one_le le_rfl

/-- `0 ≤ cantorFunction x` for all `x : ℝ`. -/
theorem cantorFunction_nonneg (x : ℝ) : 0 ≤ cantorFunction x :=
  ge_of_tendsto (tendsto_cantorApprox x) (Eventually.of_forall fun n ↦ cantorApprox_nonneg n x)

/-- `cantorFunction x ≤ 1` for all `x : ℝ`. -/
theorem cantorFunction_le_one (x : ℝ) : cantorFunction x ≤ 1 :=
  le_of_tendsto (tendsto_cantorApprox x) (Eventually.of_forall fun n ↦ cantorApprox_le_one n x)

/-- `cantorFunction` maps `Icc 0 1` onto `Icc 0 1`. -/
theorem surjOn_cantorFunction_Icc :
    SurjOn cantorFunction (Icc 0 1) (Icc 0 1) := by
  rw [SurjOn]
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  simpa [cantorFunction_zero, cantorFunction_one] using
    intermediate_value_Icc h01 continuous_cantorFunction.continuousOn

/-- Image of `Icc 0 1` under `cantorFunction`. -/
@[simp]
theorem image_cantorFunction_Icc :
    cantorFunction '' Icc 0 1 = Icc 0 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨cantorFunction_nonneg x, cantorFunction_le_one x⟩
  · exact surjOn_cantorFunction_Icc

/-- Self-similarity on `(-∞, 1]`: `cantorFunction (x / 3) = cantorFunction x / 2`. -/
theorem cantorFunction_div_three {x : ℝ} (hx : x ≤ 1) :
    cantorFunction (x / 3) = cantorFunction x / 2 := by
  rw [cantorFunction_eq_cantorStepFun (x / 3),
    show 3 * (x / 3) = x by ring,
    cantorFunction_of_nonpos (by linarith : x - 2 ≤ 0), add_zero]

/-- Self-similarity on `[0, ∞)`: `cantorFunction ((x + 2) / 3) = (cantorFunction x + 1) / 2`. -/
theorem cantorFunction_add_two_div_three {x : ℝ} (hx : 0 ≤ x) :
    cantorFunction ((x + 2) / 3) = (cantorFunction x + 1) / 2 := by
  rw [cantorFunction_eq_cantorStepFun ((x + 2) / 3),
    show 3 * ((x + 2) / 3) - 2 = x by ring,
    cantorFunction_of_one_le (by linarith : 1 ≤ 3 * ((x + 2) / 3)), add_comm]

/-- **Middle-third constancy**: `cantorFunction x = 1 / 2` for all `x ∈ Icc (1 / 3) (2 / 3)`. -/
theorem cantorFunction_eq_half {x : ℝ} (hx : x ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    cantorFunction x = 1 / 2 := by
  rw [cantorFunction_eq_cantorStepFun x,
    cantorFunction_of_one_le (by linarith [hx.1] : 1 ≤ 3 * x),
    cantorFunction_of_nonpos (by linarith [hx.2] : 3 * x - 2 ≤ 0)]
  ring

/-- **Reflection symmetry**: `cantorFunction (1 - x) = 1 - cantorFunction x` for all `x : ℝ`. -/
theorem cantorFunction_sub_one_symm (x : ℝ) :
    cantorFunction (1 - x) = 1 - cantorFunction x := by
  have h1 := tendsto_cantorApprox (1 - x)
  have h2 : Tendsto (fun n ↦ 1 - cantorApprox n x) atTop (𝓝 (1 - cantorFunction x)) :=
    tendsto_const_nhds.sub (tendsto_cantorApprox x)
  simp_rw [← cantorApprox_sub_one_symm] at h2
  exact tendsto_nhds_unique h1 h2

/-! ### Local constancy and vanishing derivative outside `cantorSet` -/

/-- Outside `preCantorSet n`, `cantorApprox (n + 1)` already agrees with `cantorApprox n`. -/
theorem cantorApprox_succ_eq_of_not_mem_preCantorSet (n : ℕ) {x : ℝ}
    (hx : x ∉ preCantorSet n) :
    cantorApprox (n + 1) x = cantorApprox n x := by
  induction n generalizing x with
  | zero =>
    rw [preCantorSet_zero, mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [cantorApprox_of_nonpos 1 hx.le, cantorApprox_of_nonpos 0 hx.le]
    · rw [cantorApprox_of_one_le 1 hx.le, cantorApprox_of_one_le 0 hx.le]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := not_mem_preCantorSet_of_not_mem_succ hx
    rw [cantorApprox_succ (n + 1), ih h1, ih h2, ← cantorApprox_succ]

/-- Outside `preCantorSet n`, `cantorApprox m x = cantorApprox n x` for all `m ≥ n`. -/
theorem cantorApprox_eq_of_not_mem_preCantorSet {n m : ℕ} (hnm : n ≤ m) {x : ℝ}
    (hx : x ∉ preCantorSet n) :
    cantorApprox m x = cantorApprox n x := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ k hnk ih =>
    have hxk : x ∉ preCantorSet k := fun h ↦ hx (preCantorSet_antitone hnk h)
    rw [cantorApprox_succ_eq_of_not_mem_preCantorSet k hxk, ih]

/-- Outside `preCantorSet n`, `cantorFunction` coincides with `cantorApprox n`. -/
theorem cantorFunction_eq_cantorApprox_of_not_mem_preCantorSet {n : ℕ} {x : ℝ}
    (hx : x ∉ preCantorSet n) :
    cantorFunction x = cantorApprox n x := by
  apply tendsto_nhds_unique (tendsto_cantorApprox x)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [ eventually_ge_atTop n ] with m hnm
  exact (cantorApprox_eq_of_not_mem_preCantorSet hnm hx).symm

/-- For every `x ∉ preCantorSet n`, `cantorApprox n` is constant on a neighborhood of `x`. -/
theorem eventuallyEq_const_cantorApprox_of_not_mem_preCantorSet (n : ℕ) {x : ℝ}
    (hx : x ∉ preCantorSet n) :
    cantorApprox n =ᶠ[𝓝 x] Function.const ℝ (cantorApprox n x) := by
  induction n generalizing x with
  | zero =>
    rw [preCantorSet_zero, mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · filter_upwards [Iio_mem_nhds hx] with y hy
      rw [Function.const_apply, cantorApprox_of_nonpos 0 hy.le, cantorApprox_of_nonpos 0 hx.le]
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [Function.const_apply, cantorApprox_of_one_le 0 hy.le, cantorApprox_of_one_le 0 hx.le]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := not_mem_preCantorSet_of_not_mem_succ hx
    have hc1 : Continuous fun y : ℝ ↦ 3 * y := by fun_prop
    have hc2 : Continuous fun y : ℝ ↦ 3 * y - 2 := by fun_prop
    have hev1 := (ih h1).comp_tendsto hc1.continuousAt
    have hev2 := (ih h2).comp_tendsto hc2.continuousAt
    filter_upwards [hev1, hev2] with y hy1 hy2
    dsimp [Function.const] at hy1 hy2 ⊢
    rw [cantorApprox_succ, cantorApprox_succ, hy1, hy2]

/-- **Local constancy outside `cantorSet`**: for every `x ∉ cantorSet`, `cantorFunction` is
constant on a neighborhood of `x`. -/
theorem eventuallyEq_const_cantorFunction_of_not_mem_cantorSet {x : ℝ}
    (hx : x ∉ cantorSet) :
    cantorFunction =ᶠ[𝓝 x] Function.const ℝ (cantorFunction x) := by
  rw [cantorSet, mem_iInter, not_forall] at hx
  obtain ⟨n, hn⟩ := hx
  have hopen : (preCantorSet n)ᶜ ∈ 𝓝 x :=
    (isClosed_preCantorSet n).isOpen_compl.mem_nhds hn
  filter_upwards [hopen, eventuallyEq_const_cantorApprox_of_not_mem_preCantorSet n hn] with
    y hy1 hy2
  rw [Function.const_apply, cantorFunction_eq_cantorApprox_of_not_mem_preCantorSet hy1,
    cantorFunction_eq_cantorApprox_of_not_mem_preCantorSet hn]
  exact hy2

/-- At every point `x ∉ cantorSet`, `cantorFunction` has derivative `0`. -/
theorem hasDerivAt_cantorFunction_zero {x : ℝ} (hx : x ∉ cantorSet) :
    HasDerivAt cantorFunction 0 x :=
  (hasDerivAt_const x (cantorFunction x)).congr_of_eventuallyEq
    (eventuallyEq_const_cantorFunction_of_not_mem_cantorSet hx)

/-- At every point `x ∉ cantorSet`, `deriv cantorFunction x = 0`. -/
theorem deriv_cantorFunction_eq_zero {x : ℝ} (hx : x ∉ cantorSet) :
    deriv cantorFunction x = 0 :=
  (hasDerivAt_cantorFunction_zero hx).deriv

/-- **The Cantor–Lebesgue function has vanishing derivative almost everywhere**. -/
theorem ae_deriv_cantorFunction_eq_zero :
    ∀ᵐ x ∂volume, deriv cantorFunction x = 0 := by
  filter_upwards [compl_mem_ae_iff.mpr volume_cantorSet] with x hx
  exact deriv_cantorFunction_eq_zero hx

/-- The Lebesgue integral of `‖deriv cantorFunction x‖ₑ` on `Icc 0 1` is `0`. -/
@[simp]
theorem lintegral_enorm_deriv_cantorFunction :
    ∫⁻ x in Icc (0 : ℝ) 1, ‖deriv cantorFunction x‖ₑ = 0 := by
  have hae : (fun x ↦ ‖deriv cantorFunction x‖ₑ) =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [ae_deriv_cantorFunction_eq_zero] with x hx
    simp [hx]
  rw [lintegral_congr_ae hae]
  simp

/-- The interval integral of `deriv cantorFunction` on `0..1` is `0`. -/
@[simp]
theorem intervalIntegral_deriv_cantorFunction :
    ∫ x in (0 : ℝ)..1, deriv cantorFunction x = 0 := by
  rw [intervalIntegral.integral_congr_ae (g := 0)]
  · simp
  · filter_upwards [ae_deriv_cantorFunction_eq_zero] with x hx _
    exact hx

/-! ### Total variation and non-absolute-continuity of `cantorFunction` -/

/-- The total variation of `cantorFunction` on `Icc 0 1` is `1`. -/
@[simp]
theorem eVariationOn_cantorFunction_Icc :
    eVariationOn cantorFunction (Icc 0 1) = 1 := by
  have h := (monotone_cantorFunction.monotoneOn (Icc 0 1)).eVariationOn_eq
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  simpa [inter_self, cantorFunction_zero, cantorFunction_one] using h

/-- `cantorFunction` has bounded variation on `Icc 0 1`. -/
theorem boundedVariationOn_cantorFunction_Icc :
    BoundedVariationOn cantorFunction (Icc 0 1) := by
  rw [BoundedVariationOn, eVariationOn_cantorFunction_Icc]
  exact ENNReal.one_ne_top

/-- **Gap between total variation and integral of the derivative**: for the Cantor–Lebesgue
function on `Icc 0 1`,
`eVariationOn cantorFunction (Icc 0 1) = 1 ≠ 0 = ∫⁻ ‖deriv cantorFunction‖ₑ`. -/
theorem eVariationOn_cantorFunction_ne_lintegral_enorm_deriv :
    eVariationOn cantorFunction (Icc 0 1) ≠
      ∫⁻ x in Icc (0 : ℝ) 1, ‖deriv cantorFunction x‖ₑ := by
  rw [eVariationOn_cantorFunction_Icc, lintegral_enorm_deriv_cantorFunction]
  exact one_ne_zero

/-- **The Cantor–Lebesgue function is not absolutely continuous on `[0, 1]`**. -/
theorem not_absolutelyContinuousOnInterval_cantorFunction :
    ¬ AbsolutelyContinuousOnInterval cantorFunction 0 1 := by
  intro h
  have hint := h.integral_deriv_eq_sub
  rw [intervalIntegral_deriv_cantorFunction, cantorFunction_one, cantorFunction_zero,
    sub_zero] at hint
  exact zero_ne_one hint

/-! ### The strictly increasing non-absolutely-continuous homeomorphism `cantorHomeomorph` -/

/-- The strictly increasing function `cantorHomeomorphFun t = (t + cantorFunction t) / 2`. -/
def cantorHomeomorphFun (t : ℝ) : ℝ :=
  (t + cantorFunction t) / 2

/-- `cantorHomeomorphFun 0 = 0`. -/
@[simp]
theorem cantorHomeomorphFun_zero : cantorHomeomorphFun 0 = 0 := by
  simp [cantorHomeomorphFun]

/-- `cantorHomeomorphFun 1 = 1`. -/
@[simp]
theorem cantorHomeomorphFun_one : cantorHomeomorphFun 1 = 1 := by
  norm_num [cantorHomeomorphFun]

/-- `cantorHomeomorphFun` is continuous. -/
@[fun_prop]
theorem continuous_cantorHomeomorphFun : Continuous cantorHomeomorphFun := by
  unfold cantorHomeomorphFun
  fun_prop

/-- `cantorHomeomorphFun` is strictly increasing. -/
theorem strictMono_cantorHomeomorphFun : StrictMono cantorHomeomorphFun := by
  intro x y hxy
  unfold cantorHomeomorphFun
  have hc := monotone_cantorFunction hxy.le
  linarith

/-- `cantorHomeomorphFun` is monotone. -/
theorem monotone_cantorHomeomorphFun : Monotone cantorHomeomorphFun :=
  strictMono_cantorHomeomorphFun.monotone

/-- `cantorHomeomorphFun` is surjective on `ℝ`. -/
theorem surjective_cantorHomeomorphFun : Function.Surjective cantorHomeomorphFun := by
  intro y
  have hle : 2 * y - 1 ≤ 2 * y := by linarith
  have hlow : cantorHomeomorphFun (2 * y - 1) ≤ y := by
    unfold cantorHomeomorphFun
    have h1 := cantorFunction_le_one (2 * y - 1)
    linarith
  have hhigh : y ≤ cantorHomeomorphFun (2 * y) := by
    unfold cantorHomeomorphFun
    have h0 := cantorFunction_nonneg (2 * y)
    linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hle continuous_cantorHomeomorphFun.continuousOn
    ⟨hlow, hhigh⟩
  exact ⟨t, ht⟩

/-- Order isomorphism `ℝ ≃o ℝ` given by `cantorHomeomorphFun`. -/
def cantorOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective cantorHomeomorphFun
    strictMono_cantorHomeomorphFun surjective_cantorHomeomorphFun

/-- Homeomorphism `ℝ ≃ₜ ℝ` given by `cantorHomeomorphFun`. -/
def cantorHomeomorph : ℝ ≃ₜ ℝ :=
  cantorOrderIso.toHomeomorph

/-- `cantorHomeomorph` evaluates as `cantorHomeomorphFun`. -/
@[simp]
theorem cantorHomeomorph_apply (t : ℝ) :
    cantorHomeomorph t = cantorHomeomorphFun t := by
  rfl

/-- `cantorHomeomorphFun` maps `Icc 0 1` onto `Icc 0 1`. -/
@[simp]
theorem image_cantorHomeomorphFun_Icc :
    cantorHomeomorphFun '' Icc 0 1 = Icc 0 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨by simpa using monotone_cantorHomeomorphFun hx.1,
      by simpa using monotone_cantorHomeomorphFun hx.2⟩
  · have h01 : (0 : ℝ) ≤ 1 := zero_le_one
    simpa [cantorHomeomorphFun_zero, cantorHomeomorphFun_one] using
      intermediate_value_Icc h01 continuous_cantorHomeomorphFun.continuousOn

/-- The total variation of `cantorHomeomorphFun` on `Icc 0 1` is `1`. -/
@[simp]
theorem eVariationOn_cantorHomeomorphFun_Icc :
    eVariationOn cantorHomeomorphFun (Icc 0 1) = 1 := by
  have h := (monotone_cantorHomeomorphFun.monotoneOn (Icc 0 1)).eVariationOn_eq
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  simpa [inter_self, cantorHomeomorphFun_zero, cantorHomeomorphFun_one] using h

/-- `cantorHomeomorphFun` has bounded variation on `Icc 0 1`. -/
theorem boundedVariationOn_cantorHomeomorphFun_Icc :
    BoundedVariationOn cantorHomeomorphFun (Icc 0 1) := by
  rw [BoundedVariationOn, eVariationOn_cantorHomeomorphFun_Icc]
  exact ENNReal.one_ne_top

/-- Outside `cantorSet`, `cantorHomeomorphFun` has derivative `1 / 2`. -/
theorem hasDerivAt_cantorHomeomorphFun_of_not_mem_cantorSet {x : ℝ} (hx : x ∉ cantorSet) :
    HasDerivAt cantorHomeomorphFun (1 / 2) x := by
  unfold cantorHomeomorphFun
  simpa using ((hasDerivAt_id x).add (hasDerivAt_cantorFunction_zero hx)).div_const 2

/-- Outside `cantorSet`, `deriv cantorHomeomorphFun x = 1 / 2`. -/
theorem deriv_cantorHomeomorphFun_of_not_mem_cantorSet {x : ℝ} (hx : x ∉ cantorSet) :
    deriv cantorHomeomorphFun x = 1 / 2 :=
  (hasDerivAt_cantorHomeomorphFun_of_not_mem_cantorSet hx).deriv

/-- Almost everywhere, `deriv cantorHomeomorphFun x = 1 / 2`. -/
theorem ae_deriv_cantorHomeomorphFun :
    ∀ᵐ x ∂volume, deriv cantorHomeomorphFun x = 1 / 2 := by
  filter_upwards [compl_mem_ae_iff.mpr volume_cantorSet] with x hx
  exact deriv_cantorHomeomorphFun_of_not_mem_cantorSet hx

/-- The Lebesgue integral of `‖deriv cantorHomeomorphFun x‖ₑ` on `Icc 0 1` is `1 / 2`. -/
@[simp]
theorem lintegral_enorm_deriv_cantorHomeomorphFun :
    ∫⁻ x in Icc (0 : ℝ) 1, ‖deriv cantorHomeomorphFun x‖ₑ = ENNReal.ofReal (1 / 2) := by
  have hae : (fun x ↦ ‖deriv cantorHomeomorphFun x‖ₑ) =ᵐ[volume.restrict (Icc 0 1)]
      fun _ ↦ ENNReal.ofReal (1 / 2) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [ae_deriv_cantorHomeomorphFun] with x hx
    rw [hx, Real.enorm_of_nonneg (by norm_num)]
  rw [lintegral_congr_ae hae, setLIntegral_const, Real.volume_Icc]
  simp

/-- The interval integral of `deriv cantorHomeomorphFun` on `0..1` is `1 / 2`. -/
@[simp]
theorem intervalIntegral_deriv_cantorHomeomorphFun :
    ∫ x in (0 : ℝ)..1, deriv cantorHomeomorphFun x = 1 / 2 := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (1 / 2 : ℝ))]
  · simp
  · filter_upwards [ae_deriv_cantorHomeomorphFun] with x hx _
    exact hx

/-- **Strict variation gap for `cantorHomeomorphFun`**: the naive derivative length integral
`∫⁻ x in Icc 0 1, ‖deriv cantorHomeomorphFun x‖ₑ = 1 / 2` is strictly smaller than the total
variation `eVariationOn cantorHomeomorphFun (Icc 0 1) = 1`. -/
theorem lintegral_enorm_deriv_cantorHomeomorphFun_lt_eVariationOn :
    (∫⁻ x in Icc (0 : ℝ) 1, ‖deriv cantorHomeomorphFun x‖ₑ) <
      eVariationOn cantorHomeomorphFun (Icc 0 1) := by
  rw [lintegral_enorm_deriv_cantorHomeomorphFun, eVariationOn_cantorHomeomorphFun_Icc,
    ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_lt_ofReal_iff zero_lt_one |>.mpr (by norm_num)

/-- **The homeomorphism `cantorHomeomorphFun` is not absolutely continuous on `[0, 1]`**. -/
theorem not_absolutelyContinuousOnInterval_cantorHomeomorphFun :
    ¬ AbsolutelyContinuousOnInterval cantorHomeomorphFun 0 1 := by
  intro h
  have hint := h.integral_deriv_eq_sub
  rw [intervalIntegral_deriv_cantorHomeomorphFun, cantorHomeomorphFun_one,
    cantorHomeomorphFun_zero] at hint
  norm_num at hint

end TauCeti
