/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation
public import TauCeti.MeasureTheory.Measure.Hausdorff.CurveTrace
public import TauCeti.MeasureTheory.Measure.Hausdorff.Rectifiable

/-!
# Curve Multiplicity Formula, Periodic Closed Curves, Twice-Traversed Circle, and Planar Graphs

This file develops the one-dimensional multiplicity formula relating the integral of fiber
multiplicity `fiberMultiplicity γ (Ico a b)` (and `fiberMultiplicity γ (Icc a b)`) with respect to
`μHE[1]` to the total variation `eVariationOn γ (Icc a b)` of simple, concatenated,
piecewise-simple, and periodic curves, and applies it to the twice-traversed circle and planar
graphs of absolutely continuous functions.

## Main definitions

* `TauCeti.circleCurve c r`: `t ↦ c + !₂[r * cos t, r * sin t]` in `EuclideanSpace ℝ (Fin 2)`.
* `TauCeti.planarGraph f`: the planar graph embedding `t ↦ !₂[t, f t]` of `f : ℝ → ℝ`.

## Main results

* `TauCeti.hausdorffMeasure_one_singleton`, `TauCeti.euclideanHausdorffMeasure_one_singleton`:
  singletons in any Borel extended metric space have `1`-dimensional Hausdorff measure zero.
* `TauCeti.lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn_Ico`,
  `TauCeti.lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn`,
  `TauCeti.lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_simpleClosed`: for injective arcs and
  simple closed curves, `∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1] = eVariationOn γ (Icc a b)`.
* `TauCeti.lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_add`,
  `TauCeti.lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_partition`,
  `TauCeti.lintegral_fiberMultiplicity_Icc_eq_eVariationOn_of_partition`: **piecewise-simple curve
  multiplicity formula** over two concatenated segments and over an arbitrary finite partition.
* `Function.Periodic.image_Icc_mul_period`, `Function.Periodic.fiberMultiplicity_Ico_mul_period`,
  `Function.Periodic.eVariationOn_Icc_mul_period`,
  `Function.Periodic.eVariationOn_Icc_two_mul_period`: `k`-fold and twice-traversed periodic simple
  closed curves preserve trace while scaling multiplicity and variation by `k`.
* `TauCeti.euclideanHausdorffMeasure_sphere_two`,
  `TauCeti.fiberMultiplicity_circleCurve_four_pi_of_mem_sphere`,
  `TauCeti.eVariationOn_circleCurve_four_pi_eq_two_mul_measure`: trace, measure `2πr`, multiplicity
  `2`, and variation `4πr = 2 * μHE[1] (trace)` for the twice-traversed circle.
* `TauCeti.euclideanHausdorffMeasure_planarGraph_eq_eVariationOn`,
  `TauCeti.euclideanHausdorffMeasure_planarGraph_eq_lintegral`,
  `TauCeti.toReal_euclideanHausdorffMeasure_planarGraph_eq_integral`: **one-dimensional graph area /
  arclength formula** `μHE[1] (planarGraph f '' Icc a b) = ∫⁻ t in Icc a b, ofReal √(1 + f'(t)²)`.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal NNReal Topology

namespace TauCeti

export TauCeti.MeasureTheory (fiberMultiplicity fiberMultiplicity_def fiberMultiplicity_empty
  fiberMultiplicity_eq_zero_iff fiberMultiplicity_of_notMem_image fiberMultiplicity_pos_iff
  fiberMultiplicity_mono fiberMultiplicity_union_disjoint fiberMultiplicity_le_one_of_injOn
  fiberMultiplicity_apply_of_injOn fiberMultiplicity_eq_indicator_of_injOn
  fiberMultiplicity_eq_count fiberMultiplicity_eq_hausdorffMeasure_zero
  fiberMultiplicity_eq_euclideanHausdorffMeasure_zero weightedFiberSum weightedFiberSum_def)

/-! ### Disjoint additivity of fiber multiplicity and weighted fiber sums -/

section DisjointAdditivity

variable {X Y : Type*}

/-- `weightedFiberSum` is additive across disjoint sets `s` and `t` when `t ∩ f ⁻¹' {y}` is
measurable. -/
theorem weightedFiberSum_union_disjoint [MeasurableSpace X] {f : X → Y} {s t : Set X}
    (h : Disjoint s t) (g : X → ℝ≥0∞) {y : Y} (ht : MeasurableSet (t ∩ f ⁻¹' {y})) :
    weightedFiberSum f (s ∪ t) g y = weightedFiberSum f s g y + weightedFiberSum f t g y := by
  rw [weightedFiberSum, weightedFiberSum, weightedFiberSum, union_inter_distrib_right,
    lintegral_union ht (h.mono inter_subset_left inter_subset_left)]

/-- For `a ≤ b ≤ c`, `fiberMultiplicity γ (Ico a c) y` splits across `Ico a b` and `Ico b c`. -/
theorem fiberMultiplicity_Ico_add_Ico (γ : ℝ → Y) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (y : Y) :
    fiberMultiplicity γ (Ico a c) y =
      fiberMultiplicity γ (Ico a b) y + fiberMultiplicity γ (Ico b c) y := by
  rw [← Ico_union_Ico_eq_Ico hab hbc,
    fiberMultiplicity_union_disjoint (Set.disjoint_left.2 fun _ hx₁ hx₂ ↦ hx₁.2.not_ge hx₂.1)]

end DisjointAdditivity

/-! ### Singletons in `μH[1]` and comparison between `Ico a b` and `Icc a b` -/

section SimpleAndClosedMultiplicity

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

instance instNullSingletonClassHausdorffOne : NullSingletonClass (μH[1] : Measure X) :=
  nullSingletonClass_hausdorff X one_pos

instance instNullSingletonClassEuclideanHausdorffOne :
    NullSingletonClass (μHE[1] : Measure X) := by
  rw [Measure.euclideanHausdorffMeasure_one]
  exact nullSingletonClass_hausdorff X one_pos

/-- Every singleton in a Borel extended metric space has `1`-dimensional Hausdorff measure zero. -/
theorem hausdorffMeasure_one_singleton (x : X) : μH[1] ({x} : Set X) = 0 := measure_singleton x

/-- Every singleton in a Borel extended metric space has `μHE[1]`-measure zero. -/
theorem euclideanHausdorffMeasure_one_singleton (x : X) : μHE[1] ({x} : Set X) = 0 :=
  measure_singleton x

/-- For `a ≤ b`, `γ '' Icc a b` decomposes as `γ '' Ico a b ∪ {γ b}`. -/
theorem image_Icc_eq_image_Ico_union (γ : ℝ → Y) {a b : ℝ} (hab : a ≤ b) :
    γ '' Icc a b = γ '' Ico a b ∪ {γ b} := by
  rw [← Ico_union_right hab, image_union, image_singleton]

/-- For `a ≤ b`, `γ '' Ico a b` and `γ '' Icc a b` have the same `μH[1]`-measure. -/
theorem hausdorffMeasure_one_image_Ico_eq_image_Icc (γ : ℝ → X) {a b : ℝ} (hab : a ≤ b) :
    μH[1] (γ '' Ico a b) = μH[1] (γ '' Icc a b) := by
  rw [image_Icc_eq_image_Ico_union γ hab]
  exact le_antisymm (measure_mono subset_union_left) ((measure_union_le _ _).trans (by simp))

/-- For `a ≤ b`, `γ '' Ico a b` and `γ '' Icc a b` have the same `μHE[1]`-measure. -/
theorem euclideanHausdorffMeasure_one_image_Ico_eq_image_Icc (γ : ℝ → X) {a b : ℝ} (hab : a ≤ b) :
    μHE[1] (γ '' Ico a b) = μHE[1] (γ '' Icc a b) := by
  rw [Measure.euclideanHausdorffMeasure_one, hausdorffMeasure_one_image_Ico_eq_image_Icc γ hab]

/-- For any `y ≠ γ b`, the fibers of `γ` on `Icc a b` and `Ico a b` over `y` coincide. -/
theorem fiber_Icc_eq_fiber_Ico_of_ne (γ : ℝ → Y) (a b : ℝ) {y : Y} (hy : y ≠ γ b) :
    Icc a b ∩ γ ⁻¹' {y} = Ico a b ∩ γ ⁻¹' {y} := by
  ext x
  simp only [mem_inter_iff, mem_Icc, mem_preimage, mem_singleton_iff, mem_Ico]
  refine ⟨fun ⟨⟨hax, hxb⟩, hxy⟩ ↦ ⟨⟨hax, hxb.lt_of_ne ?_⟩, hxy⟩,
    fun ⟨⟨hax, hxb⟩, hxy⟩ ↦ ⟨⟨hax, hxb.le⟩, hxy⟩⟩
  rintro rfl
  exact hy hxy.symm

/-- For any `y ≠ γ b`, `fiberMultiplicity γ (Icc a b) y = fiberMultiplicity γ (Ico a b) y`. -/
theorem fiberMultiplicity_Icc_eq_Ico_of_ne (γ : ℝ → Y) (a b : ℝ) {y : Y} (hy : y ≠ γ b) :
    fiberMultiplicity γ (Icc a b) y = fiberMultiplicity γ (Ico a b) y := by
  rw [fiberMultiplicity, fiberMultiplicity, fiber_Icc_eq_fiber_Ico_of_ne γ a b hy]

/-- `fiberMultiplicity γ (Icc a b)` and `fiberMultiplicity γ (Ico a b)` agree `μHE[1]`-a.e. -/
theorem fiberMultiplicity_Icc_ae_eq_Ico (γ : ℝ → X) (a b : ℝ) :
    fiberMultiplicity γ (Icc a b) =ᵐ[μHE[1]] fiberMultiplicity γ (Ico a b) := by
  filter_upwards [(μHE[1] : Measure X).ae_ne (γ b)] with y hy
  exact fiberMultiplicity_Icc_eq_Ico_of_ne γ a b hy

/-- The `μHE[1]`-integral of `fiberMultiplicity γ (Icc a b)` equals that on `Ico a b`. -/
theorem lintegral_fiberMultiplicity_Icc_eq_Ico (γ : ℝ → X) (a b : ℝ) :
    ∫⁻ y, fiberMultiplicity γ (Icc a b) y ∂μHE[1] =
      ∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1] :=
  lintegral_congr_ae (fiberMultiplicity_Icc_ae_eq_Ico γ a b)

/-- For any `y ≠ γ b`, `(γ '' Ico a b).indicator 1 y = (γ '' Icc a b).indicator 1 y`. -/
theorem indicator_image_Ico_eq_Icc_of_ne (γ : ℝ → Y) (a b : ℝ) {y : Y} (hy : y ≠ γ b) :
    (γ '' Ico a b).indicator (1 : Y → ℝ≥0∞) y = (γ '' Icc a b).indicator (1 : Y → ℝ≥0∞) y := by
  have hmem : y ∈ γ '' Ico a b ↔ y ∈ γ '' Icc a b := by
    refine ⟨fun h ↦ image_mono Ico_subset_Icc_self h, fun ⟨x, hx, hxy⟩ ↦ ?_⟩
    exact ⟨x, ⟨hx.1, hx.2.lt_of_ne fun hxb ↦ hy (hxy.symm.trans (congrArg γ hxb))⟩, hxy⟩
  by_cases h : y ∈ γ '' Ico a b
  · rw [indicator_of_mem h, indicator_of_mem (hmem.mp h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (mt hmem.mpr h)]

/-- `(γ '' Ico a b).indicator 1` and `(γ '' Icc a b).indicator 1` agree `μHE[1]`-a.e. -/
theorem indicator_image_Ico_ae_eq_Icc (γ : ℝ → X) (a b : ℝ) :
    (γ '' Ico a b).indicator (1 : X → ℝ≥0∞) =ᵐ[μHE[1]]
      (γ '' Icc a b).indicator (1 : X → ℝ≥0∞) := by
  filter_upwards [(μHE[1] : Measure X).ae_ne (γ b)] with y hy
  exact indicator_image_Ico_eq_Icc_of_ne γ a b hy

/-- If `γ` is continuous on `[a, b]` and injective on `[a, b)`, then
`fiberMultiplicity γ (Ico a b)` is `μHE[1]`-a.e. measurable. -/
theorem aemeasurable_fiberMultiplicity_Ico_of_injOn {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    AEMeasurable (fiberMultiplicity γ (Ico a b)) μHE[1] := by
  refine (measurable_one.indicator
    (isCompact_Icc.image_of_continuousOn hγ).isClosed.measurableSet).aemeasurable.congr ?_
  filter_upwards [indicator_image_Ico_ae_eq_Icc γ a b] with y hy
  rw [fiberMultiplicity_eq_indicator_of_injOn hinj, hy]

/-- **Multiplicity integral for curves injective on `[a, b)`**: if `γ : ℝ → X` is continuous on
`[a, b]` and injective on `[a, b)`, then the `μHE[1]`-integral of `fiberMultiplicity γ (Ico a b)`
equals `eVariationOn γ (Icc a b)`. -/
theorem lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn_Ico {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    ∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1] = eVariationOn γ (Icc a b) := by
  have hm : MeasurableSet (γ '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hγ).isClosed.measurableSet
  calc
    ∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1]
      = ∫⁻ y, (γ '' Ico a b).indicator 1 y ∂μHE[1] := by
          simp_rw [fiberMultiplicity_eq_indicator_of_injOn hinj]
    _ = ∫⁻ y, (γ '' Icc a b).indicator 1 y ∂μHE[1] :=
          lintegral_congr_ae (indicator_image_Ico_ae_eq_Icc γ a b)
    _ = μHE[1] (γ '' Icc a b) := lintegral_indicator_one hm
    _ = eVariationOn γ (Icc a b) :=
          euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ hinj

/-- **Multiplicity integral on `Icc a b` for curves injective on `[a, b)`**. -/
theorem lintegral_fiberMultiplicity_Icc_eq_eVariationOn_of_injOn_Ico {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    ∫⁻ y, fiberMultiplicity γ (Icc a b) y ∂μHE[1] = eVariationOn γ (Icc a b) := by
  rw [lintegral_fiberMultiplicity_Icc_eq_Ico,
    lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn_Ico hγ hinj]

/-- **Multiplicity integral for injective arcs**: if `γ : ℝ → X` is continuous and injective on
`[a, b]`, then `∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1] = eVariationOn γ (Icc a b)`. -/
theorem lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    ∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1] = eVariationOn γ (Icc a b) :=
  lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn_Ico hγ (hinj.mono Ico_subset_Icc_self)

/-- **Multiplicity integral for simple closed curves**: if `γ : ℝ → X` is continuous on `[a, b]`,
satisfies `γ a = γ b`, and is injective on `[a, b)`, then
`∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1] = eVariationOn γ (Icc a b)`. -/
theorem lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_simpleClosed {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (_hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    ∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1] = eVariationOn γ (Icc a b) :=
  lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn_Ico hγ hinj

end SimpleAndClosedMultiplicity

/-! ### Multiplicity formula for concatenated and piecewise-simple curves -/

section PiecewiseSimpleMultiplicity

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Variation additivity across `[a, b]` and `[b, c]` (`a ≤ b ≤ c`). -/
theorem eVariationOn_Icc_add_Icc (γ : ℝ → X) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    eVariationOn γ (Icc a b) + eVariationOn γ (Icc b c) = eVariationOn γ (Icc a c) := by
  simpa using eVariationOn.Icc_add_Icc γ hab hbc (mem_univ b)

/-- **Multiplicity formula for two concatenated simple curve segments**. -/
theorem lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_add {γ : ℝ → X} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hγ₁ : ContinuousOn γ (Icc a b)) (hγ₂ : ContinuousOn γ (Icc b c))
    (hinj₁ : InjOn γ (Ico a b)) (hinj₂ : InjOn γ (Ico b c)) :
    ∫⁻ y, fiberMultiplicity γ (Ico a c) y ∂μHE[1] = eVariationOn γ (Icc a c) := by
  simp_rw [fiberMultiplicity_Ico_add_Ico γ hab hbc]
  rw [lintegral_add_left' (aemeasurable_fiberMultiplicity_Ico_of_injOn hγ₁ hinj₁),
    lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn_Ico hγ₁ hinj₁,
    lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn_Ico hγ₂ hinj₂,
    eVariationOn_Icc_add_Icc γ hab hbc]

/-- Along any monotone tuple `t : Fin (m + 1) → ℝ`, the fiber multiplicity of `γ` on
`Ico (t 0) (t (Fin.last m))` equals the sum over `Ico (t i.castSucc) (t i.succ)`. -/
theorem fiberMultiplicity_Ico_eq_sum_of_monotone (γ : ℝ → Y) {m : ℕ} {t : Fin (m + 1) → ℝ}
    (ht : Monotone t) (y : Y) :
    fiberMultiplicity γ (Ico (t 0) (t (Fin.last m))) y =
      ∑ i : Fin m, fiberMultiplicity γ (Ico (t i.castSucc) (t i.succ)) y := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h0 : t 0 ≤ t (Fin.castSucc (Fin.last m)) := ht (Fin.zero_le _)
    have h1 : t (Fin.castSucc (Fin.last m)) ≤ t (Fin.last (m + 1)) := ht (Fin.le_last _)
    have hih : fiberMultiplicity γ (Ico (t 0) (t (Fin.castSucc (Fin.last m)))) y =
        ∑ i : Fin m, fiberMultiplicity γ (Ico (t i.castSucc.castSucc) (t i.castSucc.succ)) y :=
      ih (ht.comp Fin.strictMono_castSucc.monotone)
    rw [fiberMultiplicity_Ico_add_Ico γ h0 h1, Fin.sum_univ_castSucc, hih]
    rfl

/-- If `t : Fin (m + 1) → ℝ` is a monotone partition with `t 0 = a` and `t (Fin.last m) = b`, then
`fiberMultiplicity γ (Ico a b) y` is the sum over `Ico (t i.castSucc) (t i.succ)`. -/
theorem fiberMultiplicity_Ico_eq_sum_of_partition (γ : ℝ → Y) {m : ℕ} {a b : ℝ}
    {t : Fin (m + 1) → ℝ} (ht : Monotone t) (ht₀ : t 0 = a) (ht_last : t (Fin.last m) = b) (y : Y) :
    fiberMultiplicity γ (Ico a b) y =
      ∑ i : Fin m, fiberMultiplicity γ (Ico (t i.castSucc) (t i.succ)) y := by
  rw [← ht₀, ← ht_last, fiberMultiplicity_Ico_eq_sum_of_monotone γ ht]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Along any monotone tuple `t : Fin (m + 1) → ℝ`, the total variation of `γ` on
`Icc (t 0) (t (Fin.last m))` equals the sum over `Icc (t i.castSucc) (t i.succ)`. -/
theorem eVariationOn_Icc_eq_sum_of_monotone (γ : ℝ → X) {m : ℕ} {t : Fin (m + 1) → ℝ}
    (ht : Monotone t) :
    eVariationOn γ (Icc (t 0) (t (Fin.last m))) =
      ∑ i : Fin m, eVariationOn γ (Icc (t i.castSucc) (t i.succ)) := by
  induction m with
  | zero =>
    simp only [Fin.last_zero, Icc_self, Finset.univ_eq_empty, Finset.sum_empty]
    exact eVariationOn.subsingleton γ fun _ hx _ hy ↦ hx.trans hy.symm
  | succ m ih =>
    have h0 : t 0 ≤ t (Fin.castSucc (Fin.last m)) := ht (Fin.zero_le _)
    have h1 : t (Fin.castSucc (Fin.last m)) ≤ t (Fin.last (m + 1)) := ht (Fin.le_last _)
    have hih : eVariationOn γ (Icc (t 0) (t (Fin.castSucc (Fin.last m)))) =
        ∑ i : Fin m, eVariationOn γ (Icc (t i.castSucc.castSucc) (t i.castSucc.succ)) :=
      ih (ht.comp Fin.strictMono_castSucc.monotone)
    rw [← eVariationOn_Icc_add_Icc γ h0 h1, Fin.sum_univ_castSucc, hih]
    rfl

/-- **Piecewise-simple curve multiplicity formula (`Ico` version)**: if `t : Fin (m + 1) → ℝ` is a
monotone partition of `[a, b]` such that `γ` is continuous on `Icc (t i.castSucc) (t i.succ)` and
injective on `Ico (t i.castSucc) (t i.succ)` for each `i`, then
`∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1] = eVariationOn γ (Icc a b)`. -/
theorem lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_partition {γ : ℝ → X} {m : ℕ}
    {a b : ℝ} {t : Fin (m + 1) → ℝ} (ht : Monotone t) (ht₀ : t 0 = a) (ht_last : t (Fin.last m) = b)
    (hγ : ∀ i : Fin m, ContinuousOn γ (Icc (t i.castSucc) (t i.succ)))
    (hinj : ∀ i : Fin m, InjOn γ (Ico (t i.castSucc) (t i.succ))) :
    ∫⁻ y, fiberMultiplicity γ (Ico a b) y ∂μHE[1] = eVariationOn γ (Icc a b) := by
  simp_rw [fiberMultiplicity_Ico_eq_sum_of_partition γ ht ht₀ ht_last]
  rw [lintegral_finsetSum' _ fun i _ ↦ aemeasurable_fiberMultiplicity_Ico_of_injOn (hγ i) (hinj i)]
  have hterm (i : Fin m) :
      ∫⁻ y, fiberMultiplicity γ (Ico (t i.castSucc) (t i.succ)) y ∂μHE[1] =
        eVariationOn γ (Icc (t i.castSucc) (t i.succ)) :=
    lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_injOn_Ico (hγ i) (hinj i)
  simp_rw [hterm, ← ht₀, ← ht_last, eVariationOn_Icc_eq_sum_of_monotone γ ht]

/-- **Piecewise-simple curve multiplicity formula (`Icc` version)**. -/
theorem lintegral_fiberMultiplicity_Icc_eq_eVariationOn_of_partition {γ : ℝ → X} {m : ℕ}
    {a b : ℝ} {t : Fin (m + 1) → ℝ} (ht : Monotone t) (ht₀ : t 0 = a) (ht_last : t (Fin.last m) = b)
    (hγ : ∀ i : Fin m, ContinuousOn γ (Icc (t i.castSucc) (t i.succ)))
    (hinj : ∀ i : Fin m, InjOn γ (Ico (t i.castSucc) (t i.succ))) :
    ∫⁻ y, fiberMultiplicity γ (Icc a b) y ∂μHE[1] = eVariationOn γ (Icc a b) := by
  rw [lintegral_fiberMultiplicity_Icc_eq_Ico,
    lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_partition ht ht₀ ht_last hγ hinj]

end PiecewiseSimpleMultiplicity

/-! ### `k`-Fold traversed periodic simple closed curves -/

section PeriodicClosedCurves

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- For a `T`-periodic function `γ : ℝ → Y` with `0 < T`, `γ '' Ico a (a + T) = range γ`. -/
theorem _root_.Function.Periodic.image_Ico {γ : ℝ → Y} {T : ℝ} (hper : Periodic γ T) (hT : 0 < T)
    (a : ℝ) : γ '' Ico a (a + T) = range γ := by
  rw [← hper.image_Icc hT a]
  refine Subset.antisymm (image_mono Ico_subset_Icc_self) ?_
  rintro _ ⟨x, ⟨hax, hx⟩, rfl⟩
  rcases hx.eq_or_lt with rfl | hlt
  · exact ⟨a, ⟨le_rfl, lt_add_of_pos_right a hT⟩, (hper a).symm⟩
  · exact ⟨x, ⟨hax, hlt⟩, rfl⟩

/-- For a `T`-periodic function `γ : ℝ → Y` with `0 < T`, `γ '' Ico 0 T = γ '' Icc 0 T`. -/
theorem _root_.Function.Periodic.image_Ico_zero_eq_image_Icc {γ : ℝ → Y} {T : ℝ}
    (hper : Periodic γ T) (hT : 0 < T) : γ '' Ico 0 T = γ '' Icc 0 T := by
  simpa using (hper.image_Ico hT 0).trans (hper.image_Icc hT 0).symm

/-- For a `T`-periodic `γ : ℝ → Y` with `0 < T` and `1 ≤ k`, `γ '' Icc 0 (k * T) = γ '' Icc 0 T`. -/
theorem _root_.Function.Periodic.image_Icc_mul_period {γ : ℝ → Y} {T : ℝ} (hper : Periodic γ T)
    (hT : 0 < T) {k : ℕ} (hk : 1 ≤ k) : γ '' Icc 0 (k * T) = γ '' Icc 0 T := by
  have hkT : 0 < (k : ℝ) * T := mul_pos (Nat.cast_pos.mpr hk) hT
  simpa using ((hper.nat_mul k).image_Icc hkT 0).trans (hper.image_Icc hT 0).symm

/-- If `γ : ℝ → Y` is `T`-periodic and injective on `Ico 0 T`, then `γ` is injective on every
shifted period interval `Ico (j * T) ((j + 1) * T)`. -/
theorem _root_.Function.Periodic.injOn_Ico_nat_mul {γ : ℝ → Y} {T : ℝ} (hper : Periodic γ T)
    (hinj : InjOn γ (Ico 0 T)) (j : ℕ) :
    InjOn γ (Ico ((j : ℝ) * T) (((j : ℕ) + 1 : ℝ) * T)) := by
  intro x hx y hy hxy
  have hx' : x - j * T ∈ Ico 0 T := ⟨sub_nonneg.mpr hx.1, by linarith [hx.2]⟩
  have hy' : y - j * T ∈ Ico 0 T := ⟨sub_nonneg.mpr hy.1, by linarith [hy.2]⟩
  have hxeq : γ (x - j * T) = γ x := by
    simpa [sub_add_cancel] using ((hper.nat_mul j) (x - j * T)).symm
  have hyeq : γ (y - j * T) = γ y := by
    simpa [sub_add_cancel] using ((hper.nat_mul j) (y - j * T)).symm
  linarith [hinj hx' hy' (hxeq.trans (hxy.trans hyeq.symm))]

/-- For a `T`-periodic simple closed curve (`0 < T`, `InjOn γ (Ico 0 T)`) and any `k : ℕ`,
`fiberMultiplicity γ (Ico 0 (k * T)) y = k * (γ '' Icc 0 T).indicator 1 y`. -/
theorem _root_.Function.Periodic.fiberMultiplicity_Ico_mul_period {γ : ℝ → Y} {T : ℝ}
    (hper : Periodic γ T) (hT : 0 < T) (hinj : InjOn γ (Ico 0 T)) (k : ℕ) (y : Y) :
    fiberMultiplicity γ (Ico 0 (k * T)) y = k * (γ '' Icc 0 T).indicator 1 y := by
  let t : Fin (k + 1) → ℝ := fun i ↦ (i : ℝ) * T
  have ht : Monotone t := fun i j hij ↦ mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hT.le
  rw [fiberMultiplicity_Ico_eq_sum_of_partition γ ht (by simp [t]) (by simp [t])]
  have hseg (i : Fin k) :
      fiberMultiplicity γ (Ico (t i.castSucc) (t i.succ)) y = (γ '' Icc 0 T).indicator 1 y := by
    dsimp [t]
    rw [Nat.cast_add, Nat.cast_one,
      fiberMultiplicity_eq_indicator_of_injOn (hper.injOn_Ico_nat_mul hinj i)]
    have h1 : ((i : ℕ) + 1 : ℝ) * T = (i : ℝ) * T + T := by ring
    rw [h1, hper.image_Ico hT, ← hper.image_Icc hT 0, zero_add]
  simp [hseg]

/-- For a `T`-periodic simple closed curve (`0 < T`, `InjOn γ (Ico 0 T)`), every point `y` on the
trace `γ '' Icc 0 T` has fiber multiplicity `k` on `Ico 0 (k * T)`. -/
theorem _root_.Function.Periodic.fiberMultiplicity_Ico_mul_period_of_mem {γ : ℝ → Y} {T : ℝ}
    (hper : Periodic γ T) (hT : 0 < T) (hinj : InjOn γ (Ico 0 T)) (k : ℕ) {y : Y}
    (hy : y ∈ γ '' Icc 0 T) : fiberMultiplicity γ (Ico 0 (k * T)) y = k := by
  rw [hper.fiberMultiplicity_Ico_mul_period hT hinj k y, indicator_of_mem hy, Pi.one_apply, mul_one]

/-- For a continuous `T`-periodic simple closed curve (`0 < T`, `InjOn γ (Ico 0 T)`) and any
`k : ℕ`, the total variation on `[0, k * T]` is `k * eVariationOn γ (Icc 0 T)`. -/
theorem _root_.Function.Periodic.eVariationOn_Icc_mul_period {γ : ℝ → X} {T : ℝ}
    (hper : Periodic γ T) (hT : 0 < T) (hγ : Continuous γ) (hinj : InjOn γ (Ico 0 T)) (k : ℕ) :
    eVariationOn γ (Icc 0 (k * T)) = k * eVariationOn γ (Icc 0 T) := by
  let t : Fin (k + 1) → ℝ := fun i ↦ (i : ℝ) * T
  have ht : Monotone t := fun i j hij ↦ mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hT.le
  have ht₀ : t 0 = 0 := by simp [t]
  have ht_last : t (Fin.last k) = k * T := by simp [t]
  conv_lhs => rw [← ht₀, ← ht_last, eVariationOn_Icc_eq_sum_of_monotone γ ht]
  have hseg (i : Fin k) :
      eVariationOn γ (Icc (t i.castSucc) (t i.succ)) = eVariationOn γ (Icc 0 T) := by
    dsimp [t]
    rw [Nat.cast_add, Nat.cast_one,
      ← euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ.continuousOn
        (hper.injOn_Ico_nat_mul hinj i)]
    have h1 : ((i : ℕ) + 1 : ℝ) * T = (i : ℝ) * T + T := by ring
    rw [h1, hper.image_Icc hT, ← hper.image_Icc hT 0, zero_add,
      euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ.continuousOn hinj]
  simp [hseg]

/-- For a continuous `T`-periodic simple closed curve (`0 < T`, `InjOn γ (Ico 0 T)`) and `k ≥ 1`,
`eVariationOn γ (Icc 0 (k * T)) = k * μHE[1] (γ '' Icc 0 (k * T))`. -/
theorem _root_.Function.Periodic.eVariationOn_Icc_mul_period_eq_mul_measure {γ : ℝ → X} {T : ℝ}
    (hper : Periodic γ T) (hT : 0 < T) (hγ : Continuous γ) (hinj : InjOn γ (Ico 0 T))
    {k : ℕ} (hk : 1 ≤ k) :
    eVariationOn γ (Icc 0 (k * T)) = k * μHE[1] (γ '' Icc 0 (k * T)) := by
  rw [hper.eVariationOn_Icc_mul_period hT hγ hinj k, hper.image_Icc_mul_period hT hk,
    euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ.continuousOn hinj]

/-- For a continuous `T`-periodic simple closed curve (`0 < T`, `InjOn γ (Ico 0 T)`) and `k : ℕ`,
`∫⁻ y, fiberMultiplicity γ (Ico 0 (k * T)) y ∂μHE[1] = eVariationOn γ (Icc 0 (k * T))`. -/
theorem _root_.Function.Periodic.lintegral_fiberMultiplicity_Ico_mul_period {γ : ℝ → X} {T : ℝ}
    (hper : Periodic γ T) (hT : 0 < T) (hγ : Continuous γ) (hinj : InjOn γ (Ico 0 T)) (k : ℕ) :
    ∫⁻ y, fiberMultiplicity γ (Ico 0 (k * T)) y ∂μHE[1] = eVariationOn γ (Icc 0 (k * T)) := by
  let t : Fin (k + 1) → ℝ := fun i ↦ (i : ℝ) * T
  have ht : Monotone t := fun i j hij ↦ mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hT.le
  refine lintegral_fiberMultiplicity_Ico_eq_eVariationOn_of_partition ht (by simp [t])
    (by simp [t]) (fun _ ↦ hγ.continuousOn) fun i ↦ ?_
  simpa [t, Nat.cast_add, Nat.cast_one] using hper.injOn_Ico_nat_mul hinj i

/-- **Twice-traversed periodic simple closed curve**: `γ '' Icc 0 (2 * T) = γ '' Icc 0 T`. -/
theorem _root_.Function.Periodic.image_Icc_two_mul_period {γ : ℝ → Y} {T : ℝ} (hper : Periodic γ T)
    (hT : 0 < T) : γ '' Icc 0 (2 * T) = γ '' Icc 0 T := by
  simpa using hper.image_Icc_mul_period hT (by decide : 1 ≤ 2)

/-- **Twice-traversed periodic simple closed curve**: multiplicity `2` on `Ico 0 (2 * T)`. -/
theorem _root_.Function.Periodic.fiberMultiplicity_Ico_two_mul_period {γ : ℝ → Y} {T : ℝ}
    (hper : Periodic γ T) (hT : 0 < T) (hinj : InjOn γ (Ico 0 T)) (y : Y) :
    fiberMultiplicity γ (Ico 0 (2 * T)) y = 2 * (γ '' Icc 0 T).indicator 1 y := by
  simpa using hper.fiberMultiplicity_Ico_mul_period hT hinj 2 y

/-- **Twice-traversed periodic simple closed curve**: the total variation on `[0, 2 * T]` is twice
the variation on `[0, T]` and twice the `μHE[1]`-measure of `γ '' Icc 0 (2 * T)`. -/
theorem _root_.Function.Periodic.eVariationOn_Icc_two_mul_period {γ : ℝ → X} {T : ℝ}
    (hper : Periodic γ T) (hT : 0 < T) (hγ : Continuous γ) (hinj : InjOn γ (Ico 0 T)) :
    eVariationOn γ (Icc 0 (2 * T)) = 2 * eVariationOn γ (Icc 0 T) ∧
      eVariationOn γ (Icc 0 (2 * T)) = 2 * μHE[1] (γ '' Icc 0 (2 * T)) :=
  ⟨by simpa using hper.eVariationOn_Icc_mul_period hT hγ hinj 2,
    by simpa using hper.eVariationOn_Icc_mul_period_eq_mul_measure hT hγ hinj (by decide : 1 ≤ 2)⟩

end PeriodicClosedCurves

/-! ### Calculus in `EuclideanSpace ℝ (Fin 2)` and the twice-traversed circle -/

section PlanarVectorCalculus

/-- Decomposition of `!₂[x, y] : EuclideanSpace ℝ (Fin 2)` in the standard basis. -/
theorem vec2_eq_smul_single (x y : ℝ) :
    (!₂[x, y] : EuclideanSpace ℝ (Fin 2)) =
      x • EuclideanSpace.single 0 1 + y • EuclideanSpace.single 1 1 := by
  ext i; fin_cases i <;> simp

/-- Euclidean norm of `!₂[x, y] : EuclideanSpace ℝ (Fin 2)`. -/
theorem norm_vec2 (x y : ℝ) :
    ‖(!₂[x, y] : EuclideanSpace ℝ (Fin 2))‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Coordinatewise derivative of `s ↦ !₂[f s, g s]` in `EuclideanSpace ℝ (Fin 2)`. -/
theorem hasDerivAt_vec2 {f g : ℝ → ℝ} {df dg t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) :
    HasDerivAt (fun s ↦ (!₂[f s, g s] : EuclideanSpace ℝ (Fin 2))) !₂[df, dg] t := by
  simp_rw [vec2_eq_smul_single]; exact (hf.smul_const _).add (hg.smul_const _)

/-- Continuity of `s ↦ !₂[f s, g s]` in `EuclideanSpace ℝ (Fin 2)`. -/
theorem continuous_vec2 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun s ↦ (!₂[f s, g s] : EuclideanSpace ℝ (Fin 2))) := by
  simp_rw [vec2_eq_smul_single]; exact (hf.smul continuous_const).add (hg.smul continuous_const)

/-- `ContinuousOn` for `s ↦ !₂[f s, g s]` in `EuclideanSpace ℝ (Fin 2)`. -/
theorem continuousOn_vec2 {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun t ↦ (!₂[f t, g t] : EuclideanSpace ℝ (Fin 2))) s := by
  simp_rw [vec2_eq_smul_single]; exact (hf.smul continuousOn_const).add (hg.smul continuousOn_const)

/-- Absolute continuity of `t ↦ !₂[f t, g t]` in `EuclideanSpace ℝ (Fin 2)`. -/
theorem absolutelyContinuousOnInterval_vec2 {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ (!₂[f t, g t] : EuclideanSpace ℝ (Fin 2))) a b := by
  simp_rw [vec2_eq_smul_single]
  have h0 := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).lipschitzWith.comp_absolutelyContinuousOnInterval
    hf
  have h1 := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
    (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))).lipschitzWith.comp_absolutelyContinuousOnInterval
    hg
  exact h0.add h1

end PlanarVectorCalculus

section TwiceTraversedCircle

/-- The standard parametrization `t ↦ c + !₂[r * cos t, r * sin t]` of the circle in
`EuclideanSpace ℝ (Fin 2)` with center `c` and radius `r`. -/
def circleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  c + !₂[r * Real.cos t, r * Real.sin t]

private def euclideanToComplex (p : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨p 0, p 1⟩
private def complexToEuclidean (z : ℂ) : EuclideanSpace ℝ (Fin 2) := !₂[z.re, z.im]
private lemma euclideanToComplex_complexToEuclidean (z : ℂ) :
    euclideanToComplex (complexToEuclidean z) = z := Complex.ext rfl rfl
private lemma complexToEuclidean_euclideanToComplex (p : EuclideanSpace ℝ (Fin 2)) :
    complexToEuclidean (euclideanToComplex p) = p := by ext i; fin_cases i <;> rfl
private lemma circleCurve_eq_complexToEuclidean_circleMap (c : EuclideanSpace ℝ (Fin 2))
    (r t : ℝ) :
    circleCurve c r t = complexToEuclidean (circleMap (euclideanToComplex c) r t) := by
  ext i; fin_cases i <;> simp [circleCurve, complexToEuclidean, euclideanToComplex, circleMap]
private lemma dist_euclideanToComplex (p q : EuclideanSpace ℝ (Fin 2)) :
    dist (euclideanToComplex p) (euclideanToComplex q) = dist p q := by
  rw [Complex.dist_eq, dist_eq_norm, Complex.norm_def, Complex.normSq_apply, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, euclideanToComplex, sq]

/-- `circleCurve c r` is `2π`-periodic. -/
theorem periodic_circleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Periodic (circleCurve c r) (2 * Real.pi) := fun t ↦ by
  simp [circleCurve, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- `circleCurve c r` is continuous. -/
theorem continuous_circleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Continuous (circleCurve c r) :=
  continuous_const.add (continuous_vec2
    (continuous_const.mul Real.continuous_cos) (continuous_const.mul Real.continuous_sin))

/-- Derivative of `circleCurve c r` at `t`. -/
theorem hasDerivAt_circleCurve (c : EuclideanSpace ℝ (Fin 2)) (r t : ℝ) :
    HasDerivAt (circleCurve c r) !₂[-r * Real.sin t, r * Real.cos t] t := by
  have hcos : HasDerivAt (fun s ↦ r * Real.cos s) (-r * Real.sin t) t := by
    simpa [neg_mul] using (Real.hasDerivAt_cos t).const_mul r
  exact (hasDerivAt_vec2 hcos ((Real.hasDerivAt_sin t).const_mul r)).const_add c

/-- `deriv (circleCurve c r) t = !₂[-r * sin t, r * cos t]`. -/
theorem deriv_circleCurve (c : EuclideanSpace ℝ (Fin 2)) (r t : ℝ) :
    deriv (circleCurve c r) t = !₂[-r * Real.sin t, r * Real.cos t] :=
  (hasDerivAt_circleCurve c r t).deriv

/-- The speed `‖deriv (circleCurve c r) t‖` is constantly `|r|`. -/
@[simp]
theorem norm_deriv_circleCurve (c : EuclideanSpace ℝ (Fin 2)) (r t : ℝ) :
    ‖deriv (circleCurve c r) t‖ = |r| := by
  rw [deriv_circleCurve, norm_vec2]
  have h : (-r * Real.sin t) ^ 2 + (r * Real.cos t) ^ 2 = r ^ 2 := by
    calc (-r * Real.sin t) ^ 2 + (r * Real.cos t) ^ 2
      _ = r ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
  rw [h, Real.sqrt_sq_eq_abs]

/-- `circleCurve c r` is absolutely continuous on every interval `[a, b]`. -/
theorem absolutelyContinuousOnInterval_circleCurve (c : EuclideanSpace ℝ (Fin 2)) (r a b : ℝ) :
    AbsolutelyContinuousOnInterval (circleCurve c r) a b := by
  exact contDiff_const.contDiffOn.absolutelyContinuousOnInterval.add
    (absolutelyContinuousOnInterval_vec2
      (contDiff_const.mul Real.contDiff_cos).contDiffOn.absolutelyContinuousOnInterval
      (contDiff_const.mul Real.contDiff_sin).contDiffOn.absolutelyContinuousOnInterval)

/-- For `r ≠ 0`, `circleCurve c r` is injective on `Ico 0 (2 * Real.pi)`. -/
theorem injOn_circleCurve_Ico (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : r ≠ 0) :
    InjOn (circleCurve c r) (Ico 0 (2 * Real.pi)) := by
  intro t₁ ht₁ t₂ ht₂ h
  apply eq_of_circleMap_eq (c := euclideanToComplex c) hr
  · rw [abs_lt]; constructor <;> linarith [ht₁.1, ht₁.2, ht₂.1, ht₂.2]
  · simpa [circleCurve_eq_complexToEuclidean_circleMap, euclideanToComplex_complexToEuclidean]
      using congrArg euclideanToComplex h

/-- The range of `circleCurve c r` is `Metric.sphere c |r|`. -/
@[simp]
theorem range_circleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    range (circleCurve c r) = Metric.sphere c |r| := by
  ext y
  rw [mem_range, mem_sphere, ← dist_euclideanToComplex, ← mem_sphere, ← range_circleMap, mem_range]
  refine ⟨fun ⟨t, ht⟩ ↦ ⟨t, ?_⟩, fun ⟨t, ht⟩ ↦ ⟨t, ?_⟩⟩
  · simpa [circleCurve_eq_complexToEuclidean_circleMap, euclideanToComplex_complexToEuclidean]
      using congrArg euclideanToComplex ht
  · rw [circleCurve_eq_complexToEuclidean_circleMap, ht, complexToEuclidean_euclideanToComplex]

/-- For `0 ≤ r`, `circleCurve c r '' Icc 0 (2 * Real.pi) = Metric.sphere c r`. -/
@[simp]
theorem image_circleCurve_Icc_two_pi (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤ r) :
    circleCurve c r '' Icc 0 (2 * Real.pi) = Metric.sphere c r := by
  have h := (periodic_circleCurve c r).image_Icc Real.two_pi_pos 0
  rwa [zero_add, range_circleCurve, abs_of_nonneg hr] at h

/-- For `0 ≤ r`, the twice-traversed circle on `[0, 4π]` has trace `Metric.sphere c r`. -/
@[simp]
theorem image_circleCurve_Icc_four_pi (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤ r) :
    circleCurve c r '' Icc 0 (4 * Real.pi) = Metric.sphere c r := by
  have h4 : (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) := by ring
  rw [h4, (periodic_circleCurve c r).image_Icc_two_mul_period Real.two_pi_pos,
    image_circleCurve_Icc_two_pi c hr]

/-- For `a ≤ b` and `0 ≤ r`, `eVariationOn (circleCurve c r) (Icc a b) = ofReal ((b - a) * r)`. -/
theorem eVariationOn_circleCurve_Icc (c : EuclideanSpace ℝ (Fin 2)) {r a b : ℝ} (hr : 0 ≤ r)
    (hab : a ≤ b) :
    eVariationOn (circleCurve c r) (Icc a b) = ENNReal.ofReal ((b - a) * r) := by
  have hac := absolutelyContinuousOnInterval_circleCurve c r a b
  rw [hac.eVariationOn_eq_ofReal_integral_norm_deriv hab]
  simp_rw [norm_deriv_circleCurve, abs_of_nonneg hr]; simp

/-- Variation of `circleCurve c r` over one period `[0, 2π]` (`0 ≤ r`). -/
@[simp]
theorem eVariationOn_circleCurve_two_pi (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤ r) :
    eVariationOn (circleCurve c r) (Icc 0 (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi * r) := by
  simpa using eVariationOn_circleCurve_Icc c hr Real.two_pi_pos.le

/-- Variation of `circleCurve c r` over two periods `[0, 4π]` (`0 ≤ r`). -/
@[simp]
theorem eVariationOn_circleCurve_four_pi (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤ r) :
    eVariationOn (circleCurve c r) (Icc 0 (4 * Real.pi)) = ENNReal.ofReal (4 * Real.pi * r) := by
  simpa using eVariationOn_circleCurve_Icc c hr (by positivity : (0 : ℝ) ≤ 4 * Real.pi)

/-- **One-dimensional Hausdorff measure of a planar circle** (`0 ≤ r`). -/
theorem euclideanHausdorffMeasure_sphere_two (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤ r) :
    μHE[1] (Metric.sphere c r) = ENNReal.ofReal (2 * Real.pi * r) := by
  rcases hr.eq_or_lt with rfl | hpos
  · simp
  · rw [← image_circleCurve_Icc_two_pi c hr,
      euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico
        (continuous_circleCurve c r).continuousOn (injOn_circleCurve_Ico c hpos.ne'),
      eVariationOn_circleCurve_two_pi c hr]

/-- **Multiplicity of the twice-traversed circle** (`0 < r`). -/
theorem fiberMultiplicity_circleCurve_four_pi (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (y : EuclideanSpace ℝ (Fin 2)) :
    fiberMultiplicity (circleCurve c r) (Ico 0 (4 * Real.pi)) y =
      2 * (Metric.sphere c r).indicator 1 y := by
  have h4 : (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) := by ring
  rw [h4, (periodic_circleCurve c r).fiberMultiplicity_Ico_two_mul_period Real.two_pi_pos
    (injOn_circleCurve_Ico c hr.ne'), image_circleCurve_Icc_two_pi c hr.le]

/-- Every point `y ∈ Metric.sphere c r` (`0 < r`) has multiplicity `2` on `Ico 0 (4 * Real.pi)`. -/
theorem fiberMultiplicity_circleCurve_four_pi_of_mem_sphere (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Metric.sphere c r) :
    fiberMultiplicity (circleCurve c r) (Ico 0 (4 * Real.pi)) y = 2 := by
  rw [fiberMultiplicity_circleCurve_four_pi c hr y, indicator_of_mem hy, Pi.one_apply, mul_one]

/-- **Twice-traversed circle variation vs. trace measure** (`0 ≤ r`). -/
theorem eVariationOn_circleCurve_four_pi_eq_two_mul_measure (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 ≤ r) :
    eVariationOn (circleCurve c r) (Icc 0 (4 * Real.pi)) =
        2 * eVariationOn (circleCurve c r) (Icc 0 (2 * Real.pi)) ∧
      eVariationOn (circleCurve c r) (Icc 0 (4 * Real.pi)) =
        2 * μHE[1] (circleCurve c r '' Icc 0 (4 * Real.pi)) ∧
      ∫⁻ y, fiberMultiplicity (circleCurve c r) (Ico 0 (4 * Real.pi)) y ∂μHE[1] =
        eVariationOn (circleCurve c r) (Icc 0 (4 * Real.pi)) := by
  rcases hr.eq_or_lt with rfl | hpos
  · have hconst : ∀ t, circleCurve c 0 t = c := fun t ↦ by simp [circleCurve]
    have hae : fiberMultiplicity (circleCurve c 0) (Ico 0 (4 * Real.pi)) =ᵐ[μHE[1]] 0 := by
      filter_upwards [(μHE[1] : Measure (EuclideanSpace ℝ (Fin 2))).ae_ne c] with y hy
      exact fiberMultiplicity_of_notMem_image fun ⟨t, _, ht⟩ ↦ hy (ht.symm.trans (hconst t))
    rw [lintegral_congr_ae hae]
    simp [eVariationOn_circleCurve_four_pi c le_rfl, eVariationOn_circleCurve_two_pi c le_rfl]
  · have h4 : (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) := by ring
    have htwo := (periodic_circleCurve c r).eVariationOn_Icc_two_mul_period Real.two_pi_pos
      (continuous_circleCurve c r) (injOn_circleCurve_Ico c hpos.ne')
    have hlint := (periodic_circleCurve c r).lintegral_fiberMultiplicity_Ico_mul_period
      Real.two_pi_pos (continuous_circleCurve c r) (injOn_circleCurve_Ico c hpos.ne') 2
    exact ⟨by simpa [h4] using htwo.1, by simpa [h4] using htwo.2, by simpa [h4] using hlint⟩

end TwiceTraversedCircle

/-! ### One-dimensional graph area / arclength formula for `planarGraph` -/

section PlanarGraphAreaFormula

/-- The planar graph embedding `t ↦ !₂[t, f t]` of `f : ℝ → ℝ` into `EuclideanSpace ℝ (Fin 2)`. -/
def planarGraph (f : ℝ → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[t, f t]

@[simp] theorem planarGraph_apply_zero (f : ℝ → ℝ) (t : ℝ) : planarGraph f t 0 = t := rfl
@[simp] theorem planarGraph_apply_one (f : ℝ → ℝ) (t : ℝ) : planarGraph f t 1 = f t := rfl

/-- `planarGraph f` is globally injective for every `f : ℝ → ℝ`. -/
theorem injective_planarGraph (f : ℝ → ℝ) : Function.Injective (planarGraph f) :=
  fun _ _ h ↦ congrArg (fun v ↦ v 0) h

/-- `planarGraph f` is injective on any subset `s : Set ℝ`. -/
theorem injOn_planarGraph (f : ℝ → ℝ) (s : Set ℝ) : InjOn (planarGraph f) s :=
  (injective_planarGraph f).injOn

/-- If `f` is continuous on `s`, then `planarGraph f` is continuous on `s`. -/
theorem continuousOn_planarGraph {f : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s) :
    ContinuousOn (planarGraph f) s := continuousOn_vec2 continuousOn_id hf

/-- If `f` is absolutely continuous on `[a, b]`, so is `planarGraph f`. -/
theorem _root_.AbsolutelyContinuousOnInterval.planarGraph {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (TauCeti.planarGraph f) a b :=
  absolutelyContinuousOnInterval_vec2 contDiff_id.contDiffOn.absolutelyContinuousOnInterval hf

/-- If `HasDerivAt f df t`, then `HasDerivAt (planarGraph f) !₂[1, df] t`. -/
theorem hasDerivAt_planarGraph {f : ℝ → ℝ} {df t : ℝ} (hf : HasDerivAt f df t) :
    HasDerivAt (planarGraph f) !₂[1, df] t := hasDerivAt_vec2 (hasDerivAt_id t) hf

/-- At any point `t` where `f` is differentiable, `deriv (planarGraph f) t = !₂[1, deriv f t]`. -/
theorem deriv_planarGraph_of_differentiableAt {f : ℝ → ℝ} {t : ℝ} (hf : DifferentiableAt ℝ f t) :
    deriv (planarGraph f) t = !₂[1, deriv f t] := (hasDerivAt_planarGraph hf.hasDerivAt).deriv

/-- At any point `t` where `f` is differentiable, `‖deriv (planarGraph f) t‖ = √(1 + f'(t)²)`. -/
theorem norm_deriv_planarGraph_of_differentiableAt {f : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) :
    ‖deriv (planarGraph f) t‖ = Real.sqrt (1 + (deriv f t) ^ 2) := by
  rw [deriv_planarGraph_of_differentiableAt hf, norm_vec2, one_pow]

/-- At any point `t` where `f` is differentiable,
`‖deriv (planarGraph f) t‖ₑ = ENNReal.ofReal √(1 + (deriv f t) ^ 2)`. -/
theorem enorm_deriv_planarGraph_of_differentiableAt {f : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) :
    ‖deriv (planarGraph f) t‖ₑ = ENNReal.ofReal (Real.sqrt (1 + (deriv f t) ^ 2)) := by
  rw [← ofReal_norm, norm_deriv_planarGraph_of_differentiableAt hf]

/-- For an absolutely continuous `f : ℝ → ℝ` on `uIcc a b`, `‖deriv (planarGraph f) t‖` equals
`√(1 + (deriv f t) ^ 2)` at almost every `t ∈ uIcc a b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.ae_norm_deriv_planarGraph {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ t, t ∈ uIcc a b → ‖deriv (TauCeti.planarGraph f) t‖ = Real.sqrt (1 + (deriv f t) ^ 2) := by
  filter_upwards [hf.ae_differentiableAt] with t ht hmem
  exact norm_deriv_planarGraph_of_differentiableAt (ht hmem)

/-- For an absolutely continuous `f : ℝ → ℝ` on `uIcc a b`, `‖deriv (planarGraph f) t‖ₑ` equals
`ENNReal.ofReal √(1 + (deriv f t) ^ 2)` at almost every `t ∈ uIcc a b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.ae_enorm_deriv_planarGraph {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ t, t ∈ uIcc a b →
      ‖deriv (TauCeti.planarGraph f) t‖ₑ = ENNReal.ofReal (Real.sqrt (1 + (deriv f t) ^ 2)) := by
  filter_upwards [hf.ae_differentiableAt] with t ht hmem
  exact enorm_deriv_planarGraph_of_differentiableAt (ht hmem)

/-- For any `f : ℝ → ℝ` continuous on `[a, b]`, the `μHE[1]`-measure of `planarGraph f '' Icc a b`
equals `eVariationOn (planarGraph f) (Icc a b)`. -/
theorem euclideanHausdorffMeasure_planarGraph_eq_eVariationOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    μHE[1] (planarGraph f '' Icc a b) = eVariationOn (planarGraph f) (Icc a b) :=
  euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn (continuousOn_planarGraph hf)
    (injOn_planarGraph f (Icc a b))

/-- For an absolutely continuous `f : ℝ → ℝ` on `[a, b]`, `eVariationOn (planarGraph f) (Icc a b)`
equals `∫⁻ t in Icc a b, ENNReal.ofReal √(1 + (deriv f t) ^ 2)`. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_planarGraph_eq_lintegral {f : ℝ → ℝ}
    {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    eVariationOn (TauCeti.planarGraph f) (Icc a b) =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (1 + (deriv f t) ^ 2)) := by
  rw [hf.planarGraph.eVariationOn_eq_lintegral_enorm_deriv]
  refine setLIntegral_congr_fun_ae measurableSet_Icc ?_
  filter_upwards [hf.ae_enorm_deriv_planarGraph] with t ht hmem
  exact ht (Icc_subset_uIcc hmem)

/-- **One-dimensional Graph Area / Arclength Formula (`lintegral` form)**. -/
theorem euclideanHausdorffMeasure_planarGraph_eq_lintegral {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    μHE[1] (planarGraph f '' Icc a b) =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (1 + (deriv f t) ^ 2)) := by
  rw [euclideanHausdorffMeasure_planarGraph_eq_eVariationOn (hf.continuousOn.mono Icc_subset_uIcc),
    hf.eVariationOn_planarGraph_eq_lintegral]

/-- For an absolutely continuous `f : ℝ → ℝ` on `uIcc a b`, `t ↦ √(1 + (deriv f t) ^ 2)` is
interval integrable on `a..b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.intervalIntegrable_sqrt_one_add_sq_deriv {f : ℝ → ℝ}
    {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (fun t ↦ Real.sqrt (1 + (deriv f t) ^ 2)) volume a b := by
  refine hf.planarGraph.intervalIntegrable_norm_deriv.congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hf.ae_norm_deriv_planarGraph] with t ht hmem
  exact ht (uIoc_subset_uIcc hmem)

/-- **One-dimensional Graph Area / Arclength Formula (real-valued interval-integral form)**. -/
theorem toReal_euclideanHausdorffMeasure_planarGraph_eq_integral {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    (μHE[1] (planarGraph f '' Icc a b)).toReal =
      ∫ t in a..b, Real.sqrt (1 + (deriv f t) ^ 2) := by
  rw [euclideanHausdorffMeasure_planarGraph_eq_eVariationOn (hf.continuousOn.mono Icc_subset_uIcc),
    hf.planarGraph.toReal_eVariationOn_eq_integral_norm_deriv hab]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hf.ae_norm_deriv_planarGraph] with t ht hmem
  exact ht (uIoc_subset_uIcc hmem)

/-- **One-dimensional Graph Area / Arclength Formula (`ENNReal.ofReal` interval-integral form)**. -/
theorem euclideanHausdorffMeasure_planarGraph_eq_ofReal_integral {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    μHE[1] (planarGraph f '' Icc a b) =
      ENNReal.ofReal (∫ t in a..b, Real.sqrt (1 + (deriv f t) ^ 2)) := by
  rw [euclideanHausdorffMeasure_planarGraph_eq_eVariationOn (hf.continuousOn.mono Icc_subset_uIcc),
    hf.planarGraph.eVariationOn_eq_ofReal_integral_norm_deriv hab,
    ← hf.planarGraph.toReal_eVariationOn_eq_integral_norm_deriv hab,
    ← euclideanHausdorffMeasure_planarGraph_eq_eVariationOn (hf.continuousOn.mono Icc_subset_uIcc),
    toReal_euclideanHausdorffMeasure_planarGraph_eq_integral hf hab]

end PlanarGraphAreaFormula

end TauCeti
