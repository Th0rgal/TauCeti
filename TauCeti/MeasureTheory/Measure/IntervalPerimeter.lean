/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.MeasureTheory.Measure.Perimeter

/-!
# One-dimensional variational total variation, step functions, and interval perimeters

This file specializes the distributional/variational theory of bounded variation and sets of finite
perimeter (`TauCeti/MeasureTheory/Measure/Perimeter.lean`) to the real line `ℝ`:

1. **One-dimensional divergence and test functions**: for `φ : ℝ → ℝ`, `divergence φ x = deriv φ x`
   (`divergence_eq_deriv`). By the fundamental theorem of calculus and compact support, the integral
   of `divergence φ` (`φ : 𝓓(Ω, ℝ)`) over any bounded interval `Icc a b`, `Ioo a b`, `Ico a b`, or
   `Ioc a b` (`a ≤ b`) equals `φ b - φ a`, while its integral over `Iic a` or `Iio a` equals `φ a`
   and its integral over `Ici a` or `Ioi a` equals `-φ a`.
2. **Smooth bump test-function separation on `Ω : Opens ℝ`**: using `ContDiffBump`, we construct
   test functions `φ : 𝓓(Ω, ℝ)` with `‖φ x‖ ≤ 1` achieving `φ a = 1` (or `-1`) at a given point
   `a ∈ Ω`, and achieving `φ b = 1`, `φ a = -1`, `φ b - φ a = 2` at any pair of distinct points
   `a, b ∈ Ω`.
3. **One-dimensional step functions and endpoint jump atoms**: for the step function
   `stepFunction c₁ c₂ a x := if x < a then c₁ else c₂`, we compute the distributional pairing
   `∫ x in Ω, stepFunction c₁ c₂ a x * divergence φ x = (c₁ - c₂) * φ a` and deduce the exact
   variational total variation
   `distributionalVariation volume Ω (stepFunction c₁ c₂ a) =
     if a ∈ Ω then ENNReal.ofReal |c₂ - c₁| else 0`
   (and `ENNReal.ofReal |c₂ - c₁|` on `⊤`).
4. **Exact relative and whole-space perimeters of rays and intervals**:
   - Half-infinite rays `Iio a`, `Iic a`, `Ici a`, `Ioi a` have relative perimeter
     `if a ∈ Ω then 1 else 0` in `Ω` and whole-space perimeter `1`, providing concrete examples of
     infinite-volume sets of finite perimeter.
   - Bounded intervals `Ioo a b`, `Icc a b`, `Ico a b`, `Ioc a b` with `a < b` have relative
     perimeter `(if a ∈ Ω then 1 else 0) + (if b ∈ Ω then 1 else 0)` in `Ω` and whole-space
     perimeter `2`.
   - Singletons `{a}` have `perimeter volume {a} = 0 < 1 = Measure.count (frontier {a})`.
5. **Comparison with classical variation and absolute continuity**: for an absolutely continuous
   function `f : ℝ → ℝ` on `[a, b]` (`a ≤ b`), integration by parts against
   `φ : 𝓓(Opens.Ioo a b, ℝ)` yields `HasWeakLineDerivOn` with weak derivative `deriv f`, together
   with `distributionalVariation volume (Opens.Ioo a b) f ≤ ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ ≤
     eVariationOn f (Icc a b)`.

## Main definitions

* `TauCeti.stepFunction`: the one-dimensional step function `fun x : ℝ ↦ if x < a then c₁ else c₂`.
* `TauCeti.Opens.Ioo`: the open interval `Set.Ioo a b` bundled as `Opens ℝ`.

## Main results

* `TauCeti.divergence_eq_deriv`: `divergence φ x = deriv φ x` for `φ : ℝ → ℝ`.
* `TauCeti.integral_Icc_divergence_testFunction`, `TauCeti.integral_Ioo_divergence_testFunction`,
  `TauCeti.integral_Iic_divergence_testFunction`, `TauCeti.integral_Ici_divergence_testFunction`:
  fundamental theorem of calculus for `divergence φ` on intervals and rays.
* `TauCeti.distributionalVariation_stepFunction`,
  `TauCeti.distributionalVariation_top_stepFunction`: exact variational total variation of a step
  function, isolating the endpoint jump atom `|c₂ - c₁|`.
* `TauCeti.relativePerimeter_Iio`, `TauCeti.relativePerimeter_Ici`, `TauCeti.perimeter_Iio`,
  `TauCeti.perimeter_Ici`, `TauCeti.relativePerimeter_Ioo`, `TauCeti.relativePerimeter_Icc`,
  `TauCeti.perimeter_Ioo`, `TauCeti.perimeter_Icc`: exact relative and whole-space perimeters of
  rays and bounded intervals.
* `TauCeti.AbsolutelyContinuousOnInterval.integral_Ioo_mul_divergence_eq_neg`,
  `TauCeti.AbsolutelyContinuousOnInterval.distributionalVariation_Ioo_le`,
  `TauCeti.BoundedVariationOn.lintegral_enorm_deriv_le_eVariationOn`,
  `TauCeti.AbsolutelyContinuousOnInterval.distributionalVariation_Ioo_le_eVariationOn`:
  one-dimensional integration by parts and variational bounds for absolutely continuous functions.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace TestFunction Metric
open scoped ENNReal NNReal Topology Distributions

namespace TauCeti

variable {Ω : Opens ℝ}

/-! ### One-dimensional divergence and the fundamental theorem of calculus for test functions -/

/-- On `ℝ`, the divergence `divergence φ x` of a function `φ : ℝ → ℝ` equals its classical
derivative `deriv φ x`. -/
@[simp]
theorem divergence_eq_deriv (φ : ℝ → ℝ) (x : ℝ) : divergence φ x = deriv φ x := by
  have hL : (fderiv ℝ φ x).toLinearMap = (fderiv ℝ φ x 1) • LinearMap.id :=
    LinearMap.ext_ring (by simp)
  rw [divergence, hL, map_smul, LinearMap.trace_id, Module.finrank_self, Nat.cast_one, smul_eq_mul,
    mul_one]
  rfl

/-- As functions `ℝ → ℝ`, `divergence φ` equals `deriv φ`. -/
theorem fun_divergence_eq_deriv (φ : ℝ → ℝ) : divergence φ = deriv φ :=
  funext (divergence_eq_deriv φ)

/-- For a one-dimensional test function `φ : 𝓓(Ω, ℝ)`, `divergenceTestFunction φ` evaluates to
`deriv (φ : ℝ → ℝ) x`. -/
theorem divergenceTestFunction_eq_deriv (φ : 𝓓(Ω, ℝ)) (x : ℝ) :
    divergenceTestFunction φ x = deriv (φ : ℝ → ℝ) x := by
  rw [divergenceTestFunction_apply, divergence_eq_deriv]

/-- A test function `φ : 𝓓(Ω, ℝ)` vanishes at every point outside `Ω`. -/
theorem testFunction_eq_zero_of_notMem (φ : 𝓓(Ω, ℝ)) {x : ℝ} (hx : x ∉ (Ω : Set ℝ)) :
    φ x = 0 :=
  φ.zero_on_compl hx

/-- Fundamental theorem of calculus for `divergence (φ : ℝ → ℝ)` over `a..b`. -/
theorem intervalIntegral_divergence_testFunction (φ : 𝓓(Ω, ℝ)) (a b : ℝ) :
    ∫ x in a..b, divergence (φ : ℝ → ℝ) x = φ b - φ a := by
  simp_rw [divergence_eq_deriv]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ (φ.contDiff.differentiable (by simp) x).hasDerivAt)
    (((φ.contDiff.of_le (by simp)).continuous_deriv le_rfl).intervalIntegrable a b)

/-- For `φ : 𝓓(Ω, ℝ)` and `a ≤ b`, `∫ x in Ioc a b, divergence φ x = φ b - φ a`. -/
theorem integral_Ioc_divergence_testFunction (φ : 𝓓(Ω, ℝ)) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioc a b, divergence (φ : ℝ → ℝ) x = φ b - φ a := by
  rw [← intervalIntegral.integral_of_le hab, intervalIntegral_divergence_testFunction]

/-- For `φ : 𝓓(Ω, ℝ)` and `a ≤ b`, `∫ x in Icc a b, divergence φ x = φ b - φ a`. -/
theorem integral_Icc_divergence_testFunction (φ : 𝓓(Ω, ℝ)) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Icc a b, divergence (φ : ℝ → ℝ) x = φ b - φ a := by
  rw [integral_Icc_eq_integral_Ioc, integral_Ioc_divergence_testFunction φ hab]

/-- For `φ : 𝓓(Ω, ℝ)` and `a ≤ b`, `∫ x in Ioo a b, divergence φ x = φ b - φ a`. -/
theorem integral_Ioo_divergence_testFunction (φ : 𝓓(Ω, ℝ)) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioo a b, divergence (φ : ℝ → ℝ) x = φ b - φ a := by
  rw [← integral_Icc_eq_integral_Ioo, integral_Icc_divergence_testFunction φ hab]

/-- For `φ : 𝓓(Ω, ℝ)` and `a ≤ b`, `∫ x in Ico a b, divergence φ x = φ b - φ a`. -/
theorem integral_Ico_divergence_testFunction (φ : 𝓓(Ω, ℝ)) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ico a b, divergence (φ : ℝ → ℝ) x = φ b - φ a := by
  rw [← integral_Icc_eq_integral_Ico, integral_Icc_divergence_testFunction φ hab]

/-- For `φ : 𝓓(Ω, ℝ)` and `a : ℝ`, `∫ x in Iic a, divergence φ x = φ a`. -/
theorem integral_Iic_divergence_testFunction (φ : 𝓓(Ω, ℝ)) (a : ℝ) :
    ∫ x in Iic a, divergence (φ : ℝ → ℝ) x = φ a := by
  obtain ⟨m, hm⟩ := (φ.hasCompactSupport.union
    (hasCompactSupport_divergence_testFunction φ)).bddBelow
  let L := min a (m - 1)
  have hLa : L ≤ a := min_le_left _ _
  have hLm : L < m := (min_le_right _ _).trans_lt (sub_one_lt m)
  have hφL : φ L = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hLm.not_ge (hm (Or.inl h))
  have h_eq : ∫ x in Iic a, divergence (φ : ℝ → ℝ) x =
      ∫ x in Icc L a, divergence (φ : ℝ → ℝ) x := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Iic.nullMeasurableSet
      Icc_subset_Iic_self (Eventually.of_forall fun x ⟨hx_le, hx_not⟩ ↦ ?_)
    have hxL : x < L := not_le.1 fun h ↦ hx_not ⟨h, hx_le⟩
    exact image_eq_zero_of_notMem_tsupport fun h ↦ (hxL.trans hLm).not_ge (hm (Or.inr h))
  rw [h_eq, integral_Icc_divergence_testFunction φ hLa, hφL, sub_zero]

/-- For `φ : 𝓓(Ω, ℝ)` and `a : ℝ`, `∫ x in Iio a, divergence φ x = φ a`. -/
theorem integral_Iio_divergence_testFunction (φ : 𝓓(Ω, ℝ)) (a : ℝ) :
    ∫ x in Iio a, divergence (φ : ℝ → ℝ) x = φ a := by
  rw [← integral_Iic_eq_integral_Iio, integral_Iic_divergence_testFunction]

/-- For `φ : 𝓓(Ω, ℝ)` and `a : ℝ`, `∫ x in Ioi a, divergence φ x = -φ a`. -/
theorem integral_Ioi_divergence_testFunction (φ : 𝓓(Ω, ℝ)) (a : ℝ) :
    ∫ x in Ioi a, divergence (φ : ℝ → ℝ) x = -φ a := by
  have hcompl : (Iic a)ᶜ = Ioi a := compl_Iic
  have hsum := integral_add_compl (s := Iic a) measurableSet_Iic
    (integrable_divergence_testFunction (μ := volume) φ)
  have h0 : ∫ x, divergence (φ : ℝ → ℝ) x = 0 := by
    have h1 : ∫ x in (Ω : Set ℝ), divergence (φ : ℝ → ℝ) x =
        ∫ x, divergence (φ : ℝ → ℝ) x := by
      simpa using setIntegral_mul_divergence_eq_integral volume (fun _ ↦ (1 : ℝ)) φ
    rw [← h1, integral_divergence_testFunction_eq_zero]
  rw [hcompl, integral_Iic_divergence_testFunction, h0] at hsum
  linarith

/-- For `φ : 𝓓(Ω, ℝ)` and `a : ℝ`, `∫ x in Ici a, divergence φ x = -φ a`. -/
theorem integral_Ici_divergence_testFunction (φ : 𝓓(Ω, ℝ)) (a : ℝ) :
    ∫ x in Ici a, divergence (φ : ℝ → ℝ) x = -φ a := by
  rw [integral_Ici_eq_integral_Ioi, integral_Ioi_divergence_testFunction]

/-! ### Smooth bump test-function separation on `Ω : Opens ℝ` -/

/-- Given `Metric.closedBall a R ⊆ Ω` with `R > 0`, there is a smooth bump test function
`φ : 𝓓(Ω, ℝ)` supported in `Metric.closedBall a R` with `φ a = 1`, `0 ≤ φ ≤ 1`, and `‖φ x‖ ≤ 1`. -/
theorem exists_testFunction_closedBall_subset {a R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall a R ⊆ Ω) :
    ∃ φ : 𝓓(Ω, ℝ), φ a = 1 ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) ∧ (∀ x, ‖φ x‖ ≤ 1) ∧
      (∀ x ∉ Metric.closedBall a R, φ x = 0) := by
  let χ : ContDiffBump a := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
  have htsupp : tsupport (χ : ℝ → ℝ) ⊆ Ω := χ.tsupport_eq.subset.trans hsub
  let φ : 𝓓(Ω, ℝ) := ⟨χ, χ.contDiff, χ.hasCompactSupport, htsupp⟩
  have hφ_apply (x : ℝ) : φ x = χ x := rfl
  refine ⟨φ, ?_, fun x ↦ χ.nonneg, fun x ↦ χ.le_one, fun x ↦ ?_,
    fun x hx ↦ image_eq_zero_of_notMem_tsupport (χ.tsupport_eq.symm ▸ hx)⟩
  · exact χ.one_of_mem_closedBall (mem_closedBall_self (half_pos hR).le)
  · rw [hφ_apply, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    exact χ.le_one

/-- For any `a ∈ Ω`, there exists `φ : 𝓓(Ω, ℝ)` with `φ a = 1`, `0 ≤ φ ≤ 1`, and `∀ x, ‖φ x‖ ≤ 1`.
-/
theorem exists_testFunction_eq_one_of_mem {a : ℝ} (ha : a ∈ Ω) :
    ∃ φ : 𝓓(Ω, ℝ), φ a = 1 ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) ∧ (∀ x, ‖φ x‖ ≤ 1) := by
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds ha) with ⟨R, hR, hsub⟩
  rcases exists_testFunction_closedBall_subset hR hsub with ⟨φ, h1, h0, hle1, hnorm, -⟩
  exact ⟨φ, h1, h0, hle1, hnorm⟩

/-- For any `a ∈ Ω`, there exists `φ : 𝓓(Ω, ℝ)` with `φ a = -1` and `∀ x, ‖φ x‖ ≤ 1`. -/
theorem exists_testFunction_eq_neg_one_of_mem {a : ℝ} (ha : a ∈ Ω) :
    ∃ φ : 𝓓(Ω, ℝ), φ a = -1 ∧ ∀ x, ‖φ x‖ ≤ 1 := by
  rcases exists_testFunction_eq_one_of_mem ha with ⟨φ, h1, -, -, hnorm⟩
  exact ⟨-φ, by simp [h1], fun x ↦ by simpa using hnorm x⟩

/-- For any two distinct points `a, b ∈ Ω`, there exists `φ : 𝓓(Ω, ℝ)` with `φ a = -1`, `φ b = 1`,
`φ b - φ a = 2`, and `∀ x, ‖φ x‖ ≤ 1`. -/
theorem exists_testFunction_eq_neg_one_and_one {a b : ℝ} (ha : a ∈ Ω) (hb : b ∈ Ω) (hab : a ≠ b) :
    ∃ φ : 𝓓(Ω, ℝ), φ a = -1 ∧ φ b = 1 ∧ φ b - φ a = 2 ∧ ∀ x, ‖φ x‖ ≤ 1 := by
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds ha) with ⟨ra, hra, hsuba⟩
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hb) with ⟨rb, hrb, hsubb⟩
  have hd : 0 < dist a b / 2 := half_pos (dist_pos.mpr hab)
  let R := min (min ra rb) (dist a b / 2)
  have hR : 0 < R := lt_min (lt_min hra hrb) hd
  have hR_ra : R ≤ ra := (min_le_left _ _).trans (min_le_left _ _)
  have hR_rb : R ≤ rb := (min_le_left _ _).trans (min_le_right _ _)
  have hR_d : R < dist a b := (min_le_right _ _).trans_lt (half_lt_self (dist_pos.mpr hab))
  rcases exists_testFunction_closedBall_subset hR
    ((closedBall_subset_closedBall hR_ra).trans hsuba) with ⟨φa, hφa1, hφa0, hφale, -, hφa_out⟩
  rcases exists_testFunction_closedBall_subset hR
    ((closedBall_subset_closedBall hR_rb).trans hsubb) with ⟨φb, hφb1, hφb0, hφble, -, hφb_out⟩
  have hba : a ∉ Metric.closedBall b R := by rw [mem_closedBall, not_le]; exact hR_d
  have hab_out : b ∉ Metric.closedBall a R := by rw [mem_closedBall, dist_comm, not_le]; exact hR_d
  have hsub_apply (x : ℝ) : (φb - φa : 𝓓(Ω, ℝ)) x = φb x - φa x := rfl
  refine ⟨φb - φa, ?_, ?_, ?_, fun x ↦ ?_⟩
  · rw [hsub_apply, hφb_out a hba, hφa1, zero_sub]
  · rw [hsub_apply, hφb1, hφa_out b hab_out, sub_zero]
  · rw [hsub_apply, hsub_apply, hφb1, hφa_out b hab_out, hφb_out a hba, hφa1]
    ring
  · rw [hsub_apply, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hφa0 x, hφale x, hφb0 x, hφble x]

/-! ### One-dimensional step functions and endpoint jump atoms -/

/-- The one-dimensional **step function** taking the value `c₁` on `(-∞, a)` and `c₂` on `[a, ∞)`.
-/
def stepFunction (c₁ c₂ a x : ℝ) : ℝ :=
  if x < a then c₁ else c₂

@[simp]
theorem stepFunction_of_lt {c₁ c₂ a x : ℝ} (h : x < a) : stepFunction c₁ c₂ a x = c₁ := by
  simp [stepFunction, h]

@[simp]
theorem stepFunction_of_ge {c₁ c₂ a x : ℝ} (h : a ≤ x) : stepFunction c₁ c₂ a x = c₂ := by
  simp [stepFunction, not_lt.mpr h]

/-- `stepFunction c₁ c₂ a` decomposes as `(c₁ - c₂) * (Iio a).indicator 1 + c₂`. -/
theorem stepFunction_eq_add_indicator (c₁ c₂ a x : ℝ) :
    stepFunction c₁ c₂ a x = (c₁ - c₂) * (Iio a).indicator (fun _ ↦ (1 : ℝ)) x + c₂ := by
  by_cases hx : x < a <;> simp [stepFunction, hx]

/-- `stepFunction 1 0 a` is the characteristic function of `Iio a`. -/
@[simp]
theorem stepFunction_one_zero (a : ℝ) :
    stepFunction 1 0 a = (Iio a).indicator (fun _ ↦ (1 : ℝ)) := by
  ext x; by_cases hx : x < a <;> simp [stepFunction, hx]

/-- `stepFunction 0 1 a` is the characteristic function of `Ici a`. -/
@[simp]
theorem stepFunction_zero_one (a : ℝ) :
    stepFunction 0 1 a = (Ici a).indicator (fun _ ↦ (1 : ℝ)) := by
  ext x; by_cases hx : x < a <;> simp [stepFunction, hx, not_lt.mp]

/-- Every one-dimensional step function is measurable. -/
theorem measurable_stepFunction (c₁ c₂ a : ℝ) : Measurable (stepFunction c₁ c₂ a) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- Every one-dimensional step function is locally integrable with respect to Lebesgue measure. -/
theorem locallyIntegrable_stepFunction (c₁ c₂ a : ℝ) :
    LocallyIntegrable (stepFunction c₁ c₂ a) volume := by
  have h : stepFunction c₁ c₂ a = fun x ↦ (Iio a).indicator (fun _ ↦ c₁ - c₂) x + c₂ := by
    ext x; by_cases hx : x < a <;> simp [stepFunction, hx]
  rw [h]
  exact ((locallyIntegrable_const (c₁ - c₂)).indicator measurableSet_Iio).add
    (locallyIntegrable_const c₂)

/-- Every one-dimensional step function is locally integrable on any open set `Ω : Opens ℝ`. -/
theorem locallyIntegrableOn_stepFunction (Ω : Opens ℝ) (c₁ c₂ a : ℝ) :
    LocallyIntegrableOn (stepFunction c₁ c₂ a) Ω volume :=
  (locallyIntegrable_stepFunction c₁ c₂ a).locallyIntegrableOn _

/-- Integrating `(Iio a).indicator 1` against `divergence φ` (`φ : 𝓓(Ω, ℝ)`) over `Ω` yields `φ a`.
-/
theorem integral_indicator_Iio_mul_divergence (φ : 𝓓(Ω, ℝ)) (a : ℝ) :
    ∫ x in (Ω : Set ℝ), (Iio a).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : ℝ → ℝ) x =
      φ a := by
  rw [setIntegral_mul_divergence_eq_integral]
  have hind : (fun x ↦ (Iio a).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : ℝ → ℝ) x) =
      (Iio a).indicator (divergence (φ : ℝ → ℝ)) := by
    ext x; by_cases hx : x ∈ Iio a <;> simp [hx]
  rw [hind, integral_indicator measurableSet_Iio, integral_Iio_divergence_testFunction]

/-- **Distributional derivative pairing of a 1D step function**: for any test function
`φ : 𝓓(Ω, ℝ)`, `∫ x in Ω, stepFunction c₁ c₂ a x * divergence φ x = (c₁ - c₂) * φ a`, corresponding
to the endpoint Dirac jump `(c₂ - c₁) • δ_a` for the distributional derivative. -/
theorem integral_stepFunction_mul_divergence (φ : 𝓓(Ω, ℝ)) (c₁ c₂ a : ℝ) :
    ∫ x in (Ω : Set ℝ), stepFunction c₁ c₂ a x * divergence (φ : ℝ → ℝ) x =
      (c₁ - c₂) * φ a := by
  simp_rw [stepFunction_eq_add_indicator c₁ c₂ a]
  rw [integral_add_const_mul_divergence]
  have hmul : (fun x ↦ (c₁ - c₂) * (Iio a).indicator (fun _ ↦ (1 : ℝ)) x *
        divergence (φ : ℝ → ℝ) x) =
      fun x ↦ (c₁ - c₂) * ((Iio a).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : ℝ → ℝ) x) := by
    ext x; ring
  rw [hmul, integral_const_mul, integral_indicator_Iio_mul_divergence]

/-- **Exact variational total variation of a 1D step function on `Ω : Opens ℝ`**: the jump at `a`
contributes an atom of mass `ENNReal.ofReal |c₂ - c₁|` if `a ∈ Ω` and `0` otherwise. -/
theorem distributionalVariation_stepFunction (Ω : Opens ℝ) (c₁ c₂ a : ℝ) [Decidable (a ∈ Ω)] :
    distributionalVariation volume Ω (stepFunction c₁ c₂ a) =
      if a ∈ Ω then ENNReal.ofReal |c₂ - c₁| else 0 := by
  rw [distributionalVariation_eq_iSup_abs]
  simp_rw [integral_stepFunction_mul_divergence, abs_mul, abs_sub_comm c₁ c₂]
  split_ifs with ha
  · refine le_antisymm ?_ ?_
    · refine iSup₂_le fun φ hφ ↦ ENNReal.ofReal_le_ofReal ?_
      have hφa : |φ a| ≤ 1 := by simpa [Real.norm_eq_abs] using hφ a
      exact mul_le_of_le_one_right (abs_nonneg _) hφa
    · rcases exists_testFunction_eq_one_of_mem ha with ⟨φ, hφa, -, -, hnorm⟩
      refine le_iSup₂_of_le φ hnorm ?_
      simp [hφa]
  · simp [testFunction_eq_zero_of_notMem _ ha]

/-- **Exact variational total variation of a 1D step function on the whole real line**:
`distributionalVariation volume ⊤ (stepFunction c₁ c₂ a) = ENNReal.ofReal |c₂ - c₁|`. -/
@[simp]
theorem distributionalVariation_top_stepFunction (c₁ c₂ a : ℝ) :
    distributionalVariation volume (⊤ : Opens ℝ) (stepFunction c₁ c₂ a) =
      ENNReal.ofReal |c₂ - c₁| := by
  classical
  simpa using distributionalVariation_stepFunction ⊤ c₁ c₂ a

/-- Every one-dimensional step function has locally bounded variation on any open set `Ω : Opens ℝ`.
-/
theorem isLocallyBVOn_stepFunction (Ω : Opens ℝ) (c₁ c₂ a : ℝ) :
    IsLocallyBVOn volume Ω (stepFunction c₁ c₂ a) := by
  refine ⟨locallyIntegrableOn_stepFunction Ω c₁ c₂ a, fun U _ _ ↦ ?_⟩
  classical
  rw [distributionalVariation_stepFunction]
  split_ifs <;> simp

/-! ### Exact relative and whole-space perimeters of rays (`Iio`, `Iic`, `Ici`, `Ioi`) -/

/-- **Relative perimeter of `Iio a` in `Ω`**: equals `1` if `a ∈ Ω` and `0` otherwise. -/
theorem relativePerimeter_Iio (Ω : Opens ℝ) (a : ℝ) [Decidable (a ∈ Ω)] :
    relativePerimeter volume Ω (Iio a) = if a ∈ Ω then 1 else 0 := by
  unfold relativePerimeter
  rw [← stepFunction_one_zero, distributionalVariation_stepFunction]
  simp

/-- **Relative perimeter of `Iic a` in `Ω`**: equals `1` if `a ∈ Ω` and `0` otherwise. -/
theorem relativePerimeter_Iic (Ω : Opens ℝ) (a : ℝ) [Decidable (a ∈ Ω)] :
    relativePerimeter volume Ω (Iic a) = if a ∈ Ω then 1 else 0 := by
  rw [relativePerimeter_congr_ae (Measure.restrict_le_self.absolutelyContinuous Iio_ae_eq_Iic.symm),
    relativePerimeter_Iio]

/-- **Relative perimeter of `Ici a` in `Ω`**: equals `1` if `a ∈ Ω` and `0` otherwise. -/
theorem relativePerimeter_Ici (Ω : Opens ℝ) (a : ℝ) [Decidable (a ∈ Ω)] :
    relativePerimeter volume Ω (Ici a) = if a ∈ Ω then 1 else 0 := by
  rw [← compl_Iio, relativePerimeter_compl, relativePerimeter_Iio]

/-- **Relative perimeter of `Ioi a` in `Ω`**: equals `1` if `a ∈ Ω` and `0` otherwise. -/
theorem relativePerimeter_Ioi (Ω : Opens ℝ) (a : ℝ) [Decidable (a ∈ Ω)] :
    relativePerimeter volume Ω (Ioi a) = if a ∈ Ω then 1 else 0 := by
  rw [← compl_Iic, relativePerimeter_compl, relativePerimeter_Iic]

/-- **Whole-space perimeter of `Iio a`**: `perimeter volume (Iio a) = 1`. -/
@[simp]
theorem perimeter_Iio (a : ℝ) : perimeter volume (Iio a) = 1 := by
  classical
  simpa [perimeter] using relativePerimeter_Iio ⊤ a

/-- **Whole-space perimeter of `Iic a`**: `perimeter volume (Iic a) = 1`. -/
@[simp]
theorem perimeter_Iic (a : ℝ) : perimeter volume (Iic a) = 1 := by
  classical
  simpa [perimeter] using relativePerimeter_Iic ⊤ a

/-- **Whole-space perimeter of `Ici a`**: `perimeter volume (Ici a) = 1`. -/
@[simp]
theorem perimeter_Ici (a : ℝ) : perimeter volume (Ici a) = 1 := by
  classical
  simpa [perimeter] using relativePerimeter_Ici ⊤ a

/-- **Whole-space perimeter of `Ioi a`**: `perimeter volume (Ioi a) = 1`. -/
@[simp]
theorem perimeter_Ioi (a : ℝ) : perimeter volume (Ioi a) = 1 := by
  classical
  simpa [perimeter] using relativePerimeter_Ioi ⊤ a

/-- Every ray `Iio a` has finite perimeter in `Ω`. -/
theorem hasFinitePerimeterIn_Iio (Ω : Opens ℝ) (a : ℝ) : HasFinitePerimeterIn volume Ω (Iio a) := by
  classical
  refine ⟨measurableSet_Iio.nullMeasurableSet, ?_⟩
  rw [relativePerimeter_Iio]
  split_ifs <;> simp

/-- Every ray `Iic a` has finite perimeter in `Ω`. -/
theorem hasFinitePerimeterIn_Iic (Ω : Opens ℝ) (a : ℝ) : HasFinitePerimeterIn volume Ω (Iic a) := by
  classical
  refine ⟨measurableSet_Iic.nullMeasurableSet, ?_⟩
  rw [relativePerimeter_Iic]
  split_ifs <;> simp

/-- Every ray `Ici a` has finite perimeter in `Ω`. -/
theorem hasFinitePerimeterIn_Ici (Ω : Opens ℝ) (a : ℝ) : HasFinitePerimeterIn volume Ω (Ici a) := by
  classical
  refine ⟨measurableSet_Ici.nullMeasurableSet, ?_⟩
  rw [relativePerimeter_Ici]
  split_ifs <;> simp

/-- Every ray `Ioi a` has finite perimeter in `Ω`. -/
theorem hasFinitePerimeterIn_Ioi (Ω : Opens ℝ) (a : ℝ) : HasFinitePerimeterIn volume Ω (Ioi a) := by
  classical
  refine ⟨measurableSet_Ioi.nullMeasurableSet, ?_⟩
  rw [relativePerimeter_Ioi]
  split_ifs <;> simp

/-- Every ray `Iio a` has finite whole-space perimeter (`1 < ⊤`) despite having infinite Lebesgue
measure. -/
theorem hasFinitePerimeter_Iio (a : ℝ) : HasFinitePerimeter volume (Iio a) :=
  hasFinitePerimeterIn_Iio ⊤ a

/-- Every ray `Iic a` has finite whole-space perimeter (`1 < ⊤`) despite having infinite Lebesgue
measure. -/
theorem hasFinitePerimeter_Iic (a : ℝ) : HasFinitePerimeter volume (Iic a) :=
  hasFinitePerimeterIn_Iic ⊤ a

/-- Every ray `Ici a` has finite whole-space perimeter (`1 < ⊤`) despite having infinite Lebesgue
measure. -/
theorem hasFinitePerimeter_Ici (a : ℝ) : HasFinitePerimeter volume (Ici a) :=
  hasFinitePerimeterIn_Ici ⊤ a

/-- Every ray `Ioi a` has finite whole-space perimeter (`1 < ⊤`) despite having infinite Lebesgue
measure. -/
theorem hasFinitePerimeter_Ioi (a : ℝ) : HasFinitePerimeter volume (Ioi a) :=
  hasFinitePerimeterIn_Ioi ⊤ a

/-! ### Exact relative and whole-space perimeters of bounded intervals and singletons -/

/-- Integrating `(Ioo a b).indicator 1` (`a ≤ b`) against `divergence φ` (`φ : 𝓓(Ω, ℝ)`) over `Ω`
yields `φ b - φ a`. -/
theorem integral_indicator_Ioo_mul_divergence (φ : 𝓓(Ω, ℝ)) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in (Ω : Set ℝ), (Ioo a b).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : ℝ → ℝ) x =
      φ b - φ a := by
  rw [setIntegral_mul_divergence_eq_integral]
  have hind : (fun x ↦ (Ioo a b).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : ℝ → ℝ) x) =
      (Ioo a b).indicator (divergence (φ : ℝ → ℝ)) := by
    ext x; by_cases hx : x ∈ Ioo a b <;> simp [hx]
  rw [hind, integral_indicator measurableSet_Ioo, integral_Ioo_divergence_testFunction φ hab]

private lemma ofReal_abs_apply_le_ite (φ : 𝓓(Ω, ℝ)) (hφ : ∀ x, ‖φ x‖ ≤ 1) (a : ℝ)
    [Decidable (a ∈ Ω)] :
    ENNReal.ofReal |φ a| ≤ if a ∈ Ω then 1 else 0 := by
  split_ifs with ha
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hφ a)
  · simp [testFunction_eq_zero_of_notMem φ ha]

/-- **Exact relative perimeter of a bounded open interval `Ioo a b` (`a < b`) in `Ω : Opens ℝ`**:
each endpoint inside `Ω` contributes `1` to `relativePerimeter volume Ω (Ioo a b)`. -/
theorem relativePerimeter_Ioo (Ω : Opens ℝ) {a b : ℝ} (hab : a < b) [Decidable (a ∈ Ω)]
    [Decidable (b ∈ Ω)] :
    relativePerimeter volume Ω (Ioo a b) =
      (if a ∈ Ω then 1 else 0) + (if b ∈ Ω then 1 else 0) := by
  rw [relativePerimeter, distributionalVariation_eq_iSup_abs]
  simp_rw [integral_indicator_Ioo_mul_divergence _ hab.le]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun φ hφ ↦ ?_
    have htri : |φ b - φ a| ≤ |φ a| + |φ b| := by
      calc |φ b - φ a| = |(-φ a) + φ b| := by ring_nf
        _ ≤ |-φ a| + |φ b| := abs_add_le _ _
        _ = |φ a| + |φ b| := by rw [abs_neg]
    exact (ENNReal.ofReal_le_ofReal htri).trans
      (ENNReal.ofReal_add_le.trans
        (add_le_add (ofReal_abs_apply_le_ite φ hφ a) (ofReal_abs_apply_le_ite φ hφ b)))
  · split_ifs with ha hb hb
    · rcases exists_testFunction_eq_neg_one_and_one ha hb hab.ne with ⟨φ, -, -, hba, hnorm⟩
      refine le_iSup₂_of_le φ hnorm ?_
      rw [hba, abs_of_nonneg (by positivity)]
      norm_num
    · rcases exists_testFunction_eq_one_of_mem ha with ⟨φ, hφa, -, -, hnorm⟩
      refine le_iSup₂_of_le φ hnorm ?_
      simp [hφa, testFunction_eq_zero_of_notMem φ hb]
    · rcases exists_testFunction_eq_one_of_mem hb with ⟨φ, hφb, -, -, hnorm⟩
      refine le_iSup₂_of_le φ hnorm ?_
      simp [hφb, testFunction_eq_zero_of_notMem φ ha]
    · simp

/-- **Exact relative perimeter of `Icc a b` (`a < b`) in `Ω : Opens ℝ`**. -/
theorem relativePerimeter_Icc (Ω : Opens ℝ) {a b : ℝ} (hab : a < b) [Decidable (a ∈ Ω)]
    [Decidable (b ∈ Ω)] :
    relativePerimeter volume Ω (Icc a b) =
      (if a ∈ Ω then 1 else 0) + (if b ∈ Ω then 1 else 0) := by
  rw [relativePerimeter_congr_ae (Measure.restrict_le_self.absolutelyContinuous Ioo_ae_eq_Icc.symm),
    relativePerimeter_Ioo Ω hab]

/-- **Exact relative perimeter of `Ico a b` (`a < b`) in `Ω : Opens ℝ`**. -/
theorem relativePerimeter_Ico (Ω : Opens ℝ) {a b : ℝ} (hab : a < b) [Decidable (a ∈ Ω)]
    [Decidable (b ∈ Ω)] :
    relativePerimeter volume Ω (Ico a b) =
      (if a ∈ Ω then 1 else 0) + (if b ∈ Ω then 1 else 0) := by
  rw [relativePerimeter_congr_ae (Measure.restrict_le_self.absolutelyContinuous Ioo_ae_eq_Ico.symm),
    relativePerimeter_Ioo Ω hab]

/-- **Exact relative perimeter of `Ioc a b` (`a < b`) in `Ω : Opens ℝ`**. -/
theorem relativePerimeter_Ioc (Ω : Opens ℝ) {a b : ℝ} (hab : a < b) [Decidable (a ∈ Ω)]
    [Decidable (b ∈ Ω)] :
    relativePerimeter volume Ω (Ioc a b) =
      (if a ∈ Ω then 1 else 0) + (if b ∈ Ω then 1 else 0) := by
  rw [relativePerimeter_congr_ae (Measure.restrict_le_self.absolutelyContinuous Ioo_ae_eq_Ioc.symm),
    relativePerimeter_Ioo Ω hab]

/-- When both endpoints `a < b` lie in `Ω`, `relativePerimeter volume Ω (Ioo a b) = 2`. -/
theorem relativePerimeter_Ioo_of_mem {a b : ℝ} (hab : a < b) (ha : a ∈ Ω) (hb : b ∈ Ω) :
    relativePerimeter volume Ω (Ioo a b) = 2 := by
  classical
  rw [relativePerimeter_Ioo Ω hab]
  simp [ha, hb]
  norm_num

/-- When both endpoints `a < b` lie in `Ω`, `relativePerimeter volume Ω (Icc a b) = 2`. -/
theorem relativePerimeter_Icc_of_mem {a b : ℝ} (hab : a < b) (ha : a ∈ Ω) (hb : b ∈ Ω) :
    relativePerimeter volume Ω (Icc a b) = 2 := by
  classical
  rw [relativePerimeter_Icc Ω hab]
  simp [ha, hb]
  norm_num

/-- When both endpoints `a < b` lie in `Ω`, `relativePerimeter volume Ω (Ico a b) = 2`. -/
theorem relativePerimeter_Ico_of_mem {a b : ℝ} (hab : a < b) (ha : a ∈ Ω) (hb : b ∈ Ω) :
    relativePerimeter volume Ω (Ico a b) = 2 := by
  classical
  rw [relativePerimeter_Ico Ω hab]
  simp [ha, hb]
  norm_num

/-- When both endpoints `a < b` lie in `Ω`, `relativePerimeter volume Ω (Ioc a b) = 2`. -/
theorem relativePerimeter_Ioc_of_mem {a b : ℝ} (hab : a < b) (ha : a ∈ Ω) (hb : b ∈ Ω) :
    relativePerimeter volume Ω (Ioc a b) = 2 := by
  classical
  rw [relativePerimeter_Ioc Ω hab]
  simp [ha, hb]
  norm_num

/-- **Whole-space perimeter of a non-degenerate open interval `Ioo a b` (`a < b`)**:
`perimeter volume (Ioo a b) = 2`. -/
theorem perimeter_Ioo {a b : ℝ} (hab : a < b) : perimeter volume (Ioo a b) = 2 :=
  relativePerimeter_Ioo_of_mem (Ω := ⊤) hab trivial trivial

/-- **Whole-space perimeter of a non-degenerate closed interval `Icc a b` (`a < b`)**:
`perimeter volume (Icc a b) = 2`. -/
theorem perimeter_Icc {a b : ℝ} (hab : a < b) : perimeter volume (Icc a b) = 2 :=
  relativePerimeter_Icc_of_mem (Ω := ⊤) hab trivial trivial

/-- **Whole-space perimeter of a non-degenerate half-open interval `Ico a b` (`a < b`)**:
`perimeter volume (Ico a b) = 2`. -/
theorem perimeter_Ico {a b : ℝ} (hab : a < b) : perimeter volume (Ico a b) = 2 :=
  relativePerimeter_Ico_of_mem (Ω := ⊤) hab trivial trivial

/-- **Whole-space perimeter of a non-degenerate half-open interval `Ioc a b` (`a < b`)**:
`perimeter volume (Ioc a b) = 2`. -/
theorem perimeter_Ioc {a b : ℝ} (hab : a < b) : perimeter volume (Ioc a b) = 2 :=
  relativePerimeter_Ioc_of_mem (Ω := ⊤) hab trivial trivial

/-- For `b ≤ a`, `relativePerimeter volume Ω (Ioo a b) = 0`. -/
theorem relativePerimeter_Ioo_of_ge (Ω : Opens ℝ) {a b : ℝ} (hab : b ≤ a) :
    relativePerimeter volume Ω (Ioo a b) = 0 := by
  rw [Ioo_eq_empty hab.not_gt, relativePerimeter_empty]

/-- For `b ≤ a`, `perimeter volume (Ioo a b) = 0`. -/
theorem perimeter_Ioo_of_ge {a b : ℝ} (hab : b ≤ a) : perimeter volume (Ioo a b) = 0 :=
  relativePerimeter_Ioo_of_ge ⊤ hab

/-- A singleton `{a}` in `ℝ` has zero relative perimeter in any open set `Ω`. -/
@[simp]
theorem relativePerimeter_singleton (Ω : Opens ℝ) (a : ℝ) :
    relativePerimeter volume Ω ({a} : Set ℝ) = 0 := by
  have h : ({a} : Set ℝ) = ∅ ∪ {a} := (empty_union _).symm
  rw [h, relativePerimeter_union_null ∅ (measure_singleton a), relativePerimeter_empty]

/-- A singleton `{a}` in `ℝ` has zero whole-space perimeter. -/
@[simp]
theorem perimeter_singleton (a : ℝ) : perimeter volume ({a} : Set ℝ) = 0 :=
  relativePerimeter_singleton ⊤ a

/-- For a singleton `{a}` in `ℝ`, the perimeter `perimeter volume {a} = 0` is strictly smaller than
the counting measure `Measure.count (frontier {a}) = 1` of its topological frontier. -/
theorem perimeter_singleton_lt_count_frontier (a : ℝ) :
    perimeter volume ({a} : Set ℝ) < Measure.count (frontier ({a} : Set ℝ)) := by
  have hfront : frontier ({a} : Set ℝ) = {a} := by
    rw [frontier, isClosed_singleton.closure_eq, interior_singleton, sdiff_empty]
  rw [perimeter_singleton, hfront]
  simp

/-- Every open interval `Ioo a b` has finite whole-space perimeter. -/
theorem hasFinitePerimeter_Ioo (a b : ℝ) : HasFinitePerimeter volume (Ioo a b) := by
  refine ⟨measurableSet_Ioo.nullMeasurableSet, ?_⟩
  rcases lt_or_ge a b with hab | hab
  · rw [← perimeter, perimeter_Ioo hab]; exact ENNReal.ofNat_lt_top
  · rw [← perimeter, perimeter_Ioo_of_ge hab]; exact ENNReal.zero_lt_top

/-- Every closed interval `Icc a b` has finite whole-space perimeter. -/
theorem hasFinitePerimeter_Icc (a b : ℝ) : HasFinitePerimeter volume (Icc a b) := by
  refine ⟨measurableSet_Icc.nullMeasurableSet, ?_⟩
  rw [← perimeter, perimeter_congr_ae Ioo_ae_eq_Icc.symm]
  exact (hasFinitePerimeter_Ioo a b).2

/-- Every half-open interval `Ico a b` has finite whole-space perimeter. -/
theorem hasFinitePerimeter_Ico (a b : ℝ) : HasFinitePerimeter volume (Ico a b) := by
  refine ⟨measurableSet_Ico.nullMeasurableSet, ?_⟩
  rw [← perimeter, perimeter_congr_ae Ioo_ae_eq_Ico.symm]
  exact (hasFinitePerimeter_Ioo a b).2

/-- Every half-open interval `Ioc a b` has finite whole-space perimeter. -/
theorem hasFinitePerimeter_Ioc (a b : ℝ) : HasFinitePerimeter volume (Ioc a b) := by
  refine ⟨measurableSet_Ioc.nullMeasurableSet, ?_⟩
  rw [← perimeter, perimeter_congr_ae Ioo_ae_eq_Ioc.symm]
  exact (hasFinitePerimeter_Ioo a b).2

/-! ### Comparison with classical variation and absolutely continuous functions on intervals -/

/-- The open interval `Set.Ioo a b` bundled as an open subset `Opens ℝ`. -/
def Opens.Ioo (a b : ℝ) : Opens ℝ :=
  ⟨Set.Ioo a b, isOpen_Ioo⟩

@[simp]
theorem Opens.coe_Ioo (a b : ℝ) : ((Opens.Ioo a b : Opens ℝ) : Set ℝ) = Set.Ioo a b :=
  rfl

@[simp]
theorem Opens.mem_Ioo {a b x : ℝ} : x ∈ Opens.Ioo a b ↔ a < x ∧ x < b :=
  Iff.rfl

/-- **Integration by parts on `Opens.Ioo a b` for an absolutely continuous function**: if
`AbsolutelyContinuousOnInterval f a b` (`a ≤ b`), then for every test function
`φ : 𝓓(Opens.Ioo a b, ℝ)`,
`∫ x in Opens.Ioo a b, f x * divergence φ x = - ∫ x in Opens.Ioo a b, deriv f x * φ x`. -/
theorem _root_.AbsolutelyContinuousOnInterval.integral_Ioo_mul_divergence_eq_neg
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b)
    (φ : 𝓓(Opens.Ioo a b, ℝ)) :
    ∫ x in (Opens.Ioo a b : Set ℝ), f x * divergence (φ : ℝ → ℝ) x =
      -∫ x in (Opens.Ioo a b : Set ℝ), deriv f x * φ x := by
  have hφ_ac : AbsolutelyContinuousOnInterval (φ : ℝ → ℝ) a b :=
    (φ.contDiff.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hφa : φ a = 0 := φ.zero_on_compl fun h ↦ lt_irrefl a h.1
  have hφb : φ b = 0 := φ.zero_on_compl fun h ↦ lt_irrefl b h.2
  have hibp := hf.integral_mul_deriv_eq_deriv_mul hφ_ac
  simp only [hφa, hφb, mul_zero, sub_self, zero_sub] at hibp
  simp_rw [Opens.coe_Ioo, divergence_eq_deriv, ← integral_Icc_eq_integral_Ioo,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, hibp]

/-- An absolutely continuous function `f : ℝ → ℝ` on `[a, b]` (`a ≤ b`) has weak line derivative
`deriv f` in direction `1` on `Opens.Ioo a b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.hasWeakLineDerivOn_Ioo
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    HasWeakLineDerivOn volume (Opens.Ioo a b) f (deriv f) 1 := by
  have hf_loc : LocallyIntegrableOn f (Opens.Ioo a b) volume :=
    ((uIcc_of_le hab ▸ hf.continuousOn).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self).locallyIntegrableOn
  have hdf_loc : LocallyIntegrableOn (deriv f) (Opens.Ioo a b) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
      hf.intervalIntegrable_deriv).locallyIntegrableOn
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, hf_loc, hdf_loc, fun φ ↦ ?_⟩
  have hL : ∫ x, lineDeriv ℝ (φ : ℝ → ℝ) x 1 • f x =
      ∫ x in (Opens.Ioo a b : Set ℝ), f x * divergence (φ : ℝ → ℝ) x := by
    rw [setIntegral_mul_divergence_eq_integral]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    have hd : DifferentiableAt ℝ (φ : ℝ → ℝ) x := φ.contDiff.differentiable (by simp) x
    rw [divergence_eq_deriv, hd.lineDeriv_eq_fderiv, smul_eq_mul, mul_comm]
    rfl
  have hR : ∫ x, (φ : ℝ → ℝ) x • deriv f x =
      ∫ x in (Opens.Ioo a b : Set ℝ), deriv f x * φ x := by
    rw [← setIntegral_smul_eq_integral_smul]
    simp_rw [smul_eq_mul, mul_comm]
  rw [hL, hR, hf.integral_Ioo_mul_divergence_eq_neg hab φ]

/-- For an absolutely continuous function `f : ℝ → ℝ` on `[a, b]` (`a ≤ b`), its variational total
variation on `Opens.Ioo a b` is bounded by `∫⁻ x in Ioo a b, ‖deriv f x‖ₑ`. -/
theorem _root_.AbsolutelyContinuousOnInterval.distributionalVariation_Ioo_le
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    distributionalVariation volume (Opens.Ioo a b) f ≤ ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ := by
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [hf.integral_Ioo_mul_divergence_eq_neg hab φ]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [abs_neg, ← Real.enorm_eq_ofReal_abs, Opens.coe_Ioo]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x ↦ ?_)
  have hφ1 : ‖φ x‖ₑ ≤ 1 := by rw [← ofReal_norm, ENNReal.ofReal_le_one]; exact hφ x
  calc ‖deriv f x * φ x‖ₑ = ‖deriv f x‖ₑ * ‖φ x‖ₑ := enorm_mul _ _
    _ ≤ ‖deriv f x‖ₑ * 1 := by gcongr
    _ = ‖deriv f x‖ₑ := mul_one _

/-- For any function `f : ℝ → ℝ` of bounded variation on `Icc a b` (`a ≤ b`), the `L¹` norm of its
classical derivative `∫⁻ x in Ioo a b, ‖deriv f x‖ₑ` is bounded by the classical total variation
`eVariationOn f (Icc a b)`. -/
theorem _root_.BoundedVariationOn.lintegral_enorm_deriv_le_eVariationOn
    {f : ℝ → ℝ} {a b : ℝ} (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ ≤ eVariationOn f (Icc a b) := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  set V := variationOnFromTo f (Icc a b) a
  have hV_mono : MonotoneOn V (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn (left_mem_Icc.2 hab)
  have hV_int : IntegrableOn (deriv V) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hV_mono.intervalIntegrable_deriv
  have hae : ∀ᵐ x ∂volume.restrict (Icc a b), ‖deriv f x‖ ≤ deriv V x := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hV_mono' : MonotoneOn V (Icc a b) := uIcc_of_le hab ▸ hV_mono
    filter_upwards [hf.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem,
      hV_mono'.ae_differentiableWithinAt_of_mem, volume.ae_ne a, volume.ae_ne b]
      with x hfx hVx hxa hxb hx
    have hx_ioo : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩
    have hnhds : Icc a b ∈ 𝓝 x := Icc_mem_nhds hx_ioo.1 hx_ioo.2
    have hdf : HasDerivAt f (deriv f x) x := ((hfx hx).differentiableAt hnhds).hasDerivAt
    have hdV : HasDerivAt V (deriv V x) x := ((hVx hx).differentiableAt hnhds).hasDerivAt
    have hsub_ne : Ioi x ⊆ ({x}ᶜ : Set ℝ) := fun _ hy ↦ ne_of_gt hy
    have hlim_f : Tendsto (fun y ↦ ‖slope f x y‖) (𝓝[>] x) (𝓝 ‖deriv f x‖) :=
      (hdf.tendsto_slope.mono_left (nhdsWithin_mono x hsub_ne)).norm
    have hlim_V : Tendsto (slope V x) (𝓝[>] x) (𝓝 (deriv V x)) :=
      hdV.tendsto_slope.mono_left (nhdsWithin_mono x hsub_ne)
    refine le_of_tendsto_of_tendsto hlim_f hlim_V ?_
    filter_upwards [Ioo_mem_nhdsGT hx_ioo.2] with y hy
    have hy_icc : y ∈ Icc a b := ⟨(hx_ioo.1.trans hy.1).le, hy.2.le⟩
    have hpos : 0 < y - x := sub_pos.mpr hy.1
    rw [slope_def_field, slope_def_field, div_eq_inv_mul, div_eq_inv_mul, norm_mul,
      Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
    gcongr
    have hsub : V y - V x = (eVariationOn f (Icc a b ∩ Icc x y)).toReal := by
      dsimp [V]
      rw [← variationOnFromTo.add hf.locallyBoundedVariationOn (left_mem_Icc.2 hab) hx hy_icc,
        add_sub_cancel_left, variationOnFromTo.eq_of_le _ _ hy.1.le]
    rw [hsub, Real.norm_eq_abs, ← Real.dist_eq, dist_comm, dist_edist]
    exact ENNReal.toReal_mono
      ((eVariationOn.mono f inter_subset_left).trans_lt hf.lt_top).ne
      (eVariationOn.edist_le f ⟨hx, le_rfl, hy.1.le⟩ ⟨hy_icc, hy.1.le, le_rfl⟩)
  rw [show ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ = ∫⁻ x in Icc a b, ‖deriv f x‖ₑ by
    rw [restrict_Ioo_eq_restrict_Icc]]
  calc ∫⁻ x in Icc a b, ‖deriv f x‖ₑ
      ≤ ∫⁻ x in Icc a b, ENNReal.ofReal (deriv V x) := by
        refine lintegral_mono_ae (hae.mono fun x hx ↦ ?_)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal (∫ x in a..b, deriv V x) := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
          ofReal_integral_eq_lintegral_ofReal hV_int (hae.mono fun x hx ↦ (norm_nonneg _).trans hx)]
    _ ≤ ENNReal.ofReal (V b - V a) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hmem := hV_mono.intervalIntegral_deriv_mem_uIcc
        have hle : 0 ≤ V b - V a :=
          sub_nonneg.mpr (hV_mono left_mem_uIcc right_mem_uIcc hab)
        rw [uIcc_of_le hle] at hmem
        exact hmem.2
    _ = eVariationOn f (Icc a b) := by
        dsimp [V]
        rw [variationOnFromTo.self, sub_zero, variationOnFromTo.eq_of_le _ _ hab,
          inter_self, ENNReal.ofReal_toReal hf.lt_top.ne]

/-- For an absolutely continuous function `f : ℝ → ℝ` on `[a, b]` (`a ≤ b`),
`∫⁻ x in Ioo a b, ‖deriv f x‖ₑ ≤ eVariationOn f (Icc a b)`. -/
theorem _root_.AbsolutelyContinuousOnInterval.lintegral_enorm_deriv_le_eVariationOn
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ ≤ eVariationOn f (Icc a b) :=
  (uIcc_of_le hab ▸ hf.boundedVariationOn).lintegral_enorm_deriv_le_eVariationOn hab

/-- For an absolutely continuous function `f : ℝ → ℝ` on `[a, b]` (`a ≤ b`), its variational total
variation on `Opens.Ioo a b` is bounded by `eVariationOn f (Icc a b)`. -/
theorem _root_.AbsolutelyContinuousOnInterval.distributionalVariation_Ioo_le_eVariationOn
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    distributionalVariation volume (Opens.Ioo a b) f ≤ eVariationOn f (Icc a b) :=
  (hf.distributionalVariation_Ioo_le hab).trans (hf.lintegral_enorm_deriv_le_eVariationOn hab)

/-- Every function `f : ℝ → ℝ` that is absolutely continuous on `[a, b]` (`a ≤ b`) belongs to
`IsBVOn volume (Opens.Ioo a b)`. -/
theorem _root_.AbsolutelyContinuousOnInterval.isBVOn_Ioo
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    IsBVOn volume (Opens.Ioo a b) f :=
  ⟨(uIcc_of_le hab ▸ hf.continuousOn).integrableOn_Icc.mono_set Ioo_subset_Icc_self,
    (hf.distributionalVariation_Ioo_le_eVariationOn hab).trans_lt
      (uIcc_of_le hab ▸ hf.boundedVariationOn).lt_top⟩

end TauCeti
