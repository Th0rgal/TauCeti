/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Zero-Dimensional Hausdorff Measure, Fiber Multiplicities, and Countably Rectifiable Sets

This file establishes the counting-measure normalization of `0`-dimensional Hausdorff measure
(`μH[0]` and `μHE[0]`), extended nonnegative fiber multiplicities and weighted fiber sums, and the
closure and transport theory of purely and countably `k`-rectifiable sets in extended metric spaces
and finite-dimensional normed spaces.

## Main definitions

* `TauCeti.MeasureTheory.fiberMultiplicity`: the extended cardinality `(A ∩ f ⁻¹' {y}).encard` of
  the fiber of `f : X → Y` restricted to `A : Set X` over `y : Y`, valued in `ℝ≥0∞`.
* `TauCeti.MeasureTheory.weightedFiberSum`: the weighted fiber sum
  `∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂Measure.count` over the fiber `A ∩ f ⁻¹' {y}`.
* `TauCeti.MeasureTheory.PurelyRectifiable`: a set `s : Set X` is purely `k`-rectifiable if it is
  contained in a countable union of Lipschitz images of subsets of `EuclideanSpace ℝ (Fin k)`.
* `TauCeti.MeasureTheory.CountablyRectifiable`: a set `s : Set X` is countably `k`-rectifiable if
  it is covered up to a `μH[k]`-null set (equivalently, a `μHE[k]`-null set) by a countable union
  of Lipschitz images of subsets of `EuclideanSpace ℝ (Fin k)`.

## Main results

* `TauCeti.MeasureTheory.hausdorffMeasure_zero_apply` and
  `TauCeti.MeasureTheory.hausdorffMeasure_zero`: `μH[0] s = s.encard` for every `s : Set X` and
  `(μH[0] : Measure X) = Measure.count`.
* `TauCeti.MeasureTheory.euclideanHausdorffMeasure_zero_apply` and
  `TauCeti.MeasureTheory.euclideanHausdorffMeasure_zero_eq_count`: `μHE[0] s = s.encard` and
  `(μHE[0] : Measure X) = Measure.count`.
* `TauCeti.MeasureTheory.fiberMultiplicity_eq_hausdorffMeasure_zero`,
  `TauCeti.MeasureTheory.weightedFiberSum_eq_lintegral_hausdorffMeasure_zero`,
  `TauCeti.MeasureTheory.weightedFiberSum_one_eq_fiberMultiplicity`,
  `TauCeti.MeasureTheory.weightedFiberSum_eq_tsum`, and
  `TauCeti.MeasureTheory.weightedFiberSum_of_injOn`: identities relating fiber multiplicity and
  weighted fiber sums to `μH[0]`, `μHE[0]`, `Measure.count`, and `tsum`.
* Closure and transport properties of `PurelyRectifiable` and `CountablyRectifiable`: subsets,
  intersections, set differences, finite and countable unions, `μH[k]`- and `μHE[k]`-null
  modifications, `LipschitzOnWith` and `LipschitzWith` images, `Isometry` and `IsometryEquiv`
  invariance, `ContinuousLinearMap` images, and rectifiability of all subsets of finite-dimensional
  real normed spaces of dimension at most `k`.
* `TauCeti.MeasureTheory.purelyRectifiable_zero_iff_countable` and
  `TauCeti.MeasureTheory.countablyRectifiable_zero_iff_countable`: in dimension `0`, both pure and
  countable rectifiability coincide with countability (`Set.Countable`).
* `TauCeti.MeasureTheory.PurelyRectifiable.hausdorffMeasure_eq_zero_of_lt` and
  `TauCeti.MeasureTheory.CountablyRectifiable.sigmaFinite_restrict_hausdorffMeasure`: vanishing of
  higher Hausdorff measures on purely `k`-rectifiable sets and `σ`-finiteness of `μH[k].restrict s`
  and `μHE[k].restrict s` on countably `k`-rectifiable sets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure Set Filter Metric
open scoped ENNReal NNReal Finset Topology

namespace TauCeti.MeasureTheory

/-!
### Normalization of `μH[0]` and `μHE[0]` as counting measure
-/

section HausdorffZero

variable {α X : Type*}

/-- On a measurable space with measurable singletons, `Measure.count s` equals `s.encard` for every
subset `s` (measurable or not). -/
theorem count_apply_eq_encard [MeasurableSpace α] [MeasurableSingletonClass α] (s : Set α) :
    Measure.count s = s.encard := by
  by_cases hs : s.Finite
  · rw [Measure.count_apply_finite s hs, hs.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
  · change s.Infinite at hs
    rw [Measure.count_apply_infinite hs, hs.encard_eq, ENat.toENNReal_top]

/-- On a measurable space with measurable singletons, integrating over a measurable set `s` with
respect to `Measure.count` equals the subtype `tsum` over `s`. -/
theorem setLIntegral_count_of_measurableSet [MeasurableSpace α] [MeasurableSingletonClass α]
    (g : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂Measure.count = ∑' x : s, g x := by
  rw [← lintegral_indicator hs, lintegral_count, tsum_subtype s g]

/-- On a measurable space with measurable singletons, integrating over a countable set `s` with
respect to `Measure.count` equals the subtype `tsum` over `s`. -/
theorem setLIntegral_count_of_countable [MeasurableSpace α] [MeasurableSingletonClass α]
    (g : α → ℝ≥0∞) {s : Set α} (hs : s.Countable) :
    ∫⁻ x in s, g x ∂Measure.count = ∑' x : s, g x := by
  rw [lintegral_countable g hs]
  simp

variable [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

@[simp]
theorem hausdorffMeasure_zero_finset (s : Finset X) :
    μH[0] (↑s : Set X) = #s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.coe_insert, ← union_singleton,
      measure_union (disjoint_singleton_right.mpr ha) (measurableSet_singleton a),
      ih, hausdorffMeasure_zero_singleton, Finset.card_insert_of_notMem ha, Nat.cast_add,
      Nat.cast_one]

theorem hausdorffMeasure_zero_finite {s : Set X} (hs : s.Finite) :
    μH[0] s = #hs.toFinset := by
  rw [← hausdorffMeasure_zero_finset hs.toFinset, hs.coe_toFinset]

theorem hausdorffMeasure_zero_infinite {s : Set X} (hs : s.Infinite) :
    μH[0] s = ⊤ := by
  refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n ↦ ?_)
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  rw [← hausdorffMeasure_zero_finset]
  exact measure_mono ht

/-- The `0`-dimensional Hausdorff measure of any set `s : Set X` is its extended cardinality
`s.encard`. -/
theorem hausdorffMeasure_zero_apply (s : Set X) :
    μH[0] s = s.encard := by
  by_cases hs : s.Finite
  · rw [hausdorffMeasure_zero_finite hs, hs.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
  · change s.Infinite at hs
    rw [hausdorffMeasure_zero_infinite hs, hs.encard_eq, ENat.toENNReal_top]

/-- The `0`-dimensional Hausdorff measure `μH[0]` on a Borel extended metric space coincides with
`Measure.count`. -/
theorem hausdorffMeasure_zero :
    (μH[0] : Measure X) = Measure.count := by
  ext s hs
  rw [hausdorffMeasure_zero_apply, Measure.count_apply hs]

theorem hausdorffMeasure_zero_eq_zero_iff (s : Set X) :
    μH[0] s = 0 ↔ s = ∅ := by
  rw [hausdorffMeasure_zero_apply, ENat.toENNReal_eq_zero, encard_eq_zero]

theorem euclideanHausdorffMeasure_zero_singleton (x : X) :
    μHE[0] ({x} : Set X) = 1 := by
  rw [Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton]

/-- The `0`-dimensional normalized Euclidean Hausdorff measure `μHE[0]` of any set `s : Set X` is
its extended cardinality `s.encard`. -/
theorem euclideanHausdorffMeasure_zero_apply (s : Set X) :
    μHE[0] s = s.encard := by
  rw [Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_apply]

/-- The `0`-dimensional normalized Euclidean Hausdorff measure `μHE[0]` coincides with
`Measure.count`. -/
theorem euclideanHausdorffMeasure_zero_eq_count :
    (μHE[0] : Measure X) = Measure.count := by
  rw [Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero]

theorem euclideanHausdorffMeasure_zero_eq_zero_iff (s : Set X) :
    μHE[0] s = 0 ↔ s = ∅ := by
  rw [Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_eq_zero_iff]

end HausdorffZero

/-!
### Extended fiber multiplicity and weighted fiber sums
-/

section FiberMultiplicity

variable {X Y : Type*}

/-- The extended nonnegative fiber multiplicity of `f : X → Y` restricted to `A : Set X` over
`y : Y`, defined as `(A ∩ f ⁻¹' {y}).encard : ℝ≥0∞`. Infinite fibers have value `⊤`. -/
def fiberMultiplicity (f : X → Y) (A : Set X) (y : Y) : ℝ≥0∞ :=
  (A ∩ f ⁻¹' {y}).encard

theorem fiberMultiplicity_def (f : X → Y) (A : Set X) (y : Y) :
    fiberMultiplicity f A y = (A ∩ f ⁻¹' {y}).encard := by
  rfl

@[simp]
theorem fiberMultiplicity_empty (f : X → Y) (y : Y) :
    fiberMultiplicity f ∅ y = 0 := by
  simp [fiberMultiplicity]

@[simp]
theorem fiberMultiplicity_eq_zero_iff {f : X → Y} {A : Set X} {y : Y} :
    fiberMultiplicity f A y = 0 ↔ y ∉ f '' A := by
  rw [fiberMultiplicity, ENat.toENNReal_eq_zero, encard_eq_zero,
    eq_empty_iff_forall_notMem]
  constructor
  · rintro h ⟨x, hxA, rfl⟩
    exact h x ⟨hxA, rfl⟩
  · rintro hy x ⟨hxA, hxy⟩
    exact hy ⟨x, hxA, hxy⟩

theorem fiberMultiplicity_of_notMem_image {f : X → Y} {A : Set X} {y : Y} (hy : y ∉ f '' A) :
    fiberMultiplicity f A y = 0 :=
  fiberMultiplicity_eq_zero_iff.mpr hy

@[simp]
theorem fiberMultiplicity_pos_iff {f : X → Y} {A : Set X} {y : Y} :
    0 < fiberMultiplicity f A y ↔ y ∈ f '' A := by
  rw [pos_iff_ne_zero, Ne, fiberMultiplicity_eq_zero_iff, Classical.not_not]

theorem fiberMultiplicity_mono {f : X → Y} {A B : Set X} (hAB : A ⊆ B) (y : Y) :
    fiberMultiplicity f A y ≤ fiberMultiplicity f B y := by
  rw [fiberMultiplicity, fiberMultiplicity, ENat.toENNReal_le]
  exact encard_le_encard (inter_subset_inter_left _ hAB)

theorem fiberMultiplicity_union_disjoint {f : X → Y} {A B : Set X} (h : Disjoint A B) (y : Y) :
    fiberMultiplicity f (A ∪ B) y = fiberMultiplicity f A y + fiberMultiplicity f B y := by
  rw [fiberMultiplicity, fiberMultiplicity, fiberMultiplicity, union_inter_distrib_right,
    ← ENat.toENNReal_add,
    encard_union_eq (h.mono inter_subset_left inter_subset_left)]

theorem fiberMultiplicity_le_one_of_injOn {f : X → Y} {A : Set X} (hf : Set.InjOn f A) (y : Y) :
    fiberMultiplicity f A y ≤ 1 := by
  have hsub : (A ∩ f ⁻¹' {y}).Subsingleton := by
    rintro x₁ ⟨hx₁, hfx₁⟩ x₂ ⟨hx₂, hfx₂⟩
    exact hf hx₁ hx₂ (hfx₁.trans hfx₂.symm)
  rw [fiberMultiplicity, ← ENat.toENNReal_one, ENat.toENNReal_le, encard_le_one_iff_subsingleton]
  exact hsub

theorem fiberMultiplicity_apply_of_injOn {f : X → Y} {A : Set X} (hf : Set.InjOn f A)
    {x : X} (hx : x ∈ A) :
    fiberMultiplicity f A (f x) = 1 := by
  have heq : A ∩ f ⁻¹' {f x} = {x} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun ⟨hzA, hfz⟩ ↦ hf hzA hx hfz, by rintro rfl; exact ⟨hx, rfl⟩⟩
  rw [fiberMultiplicity, heq, encard_singleton, ENat.toENNReal_one]

theorem fiberMultiplicity_eq_indicator_of_injOn {f : X → Y} {A : Set X} (hf : Set.InjOn f A)
    (y : Y) :
    fiberMultiplicity f A y = (f '' A).indicator 1 y := by
  by_cases hy : y ∈ f '' A
  · rcases hy with ⟨x, hxA, rfl⟩
    rw [indicator_of_mem (mem_image_of_mem f hxA), Pi.one_apply,
      fiberMultiplicity_apply_of_injOn hf hxA]
  · rw [indicator_of_notMem hy, fiberMultiplicity_of_notMem_image hy]

theorem fiberMultiplicity_eq_count [MeasurableSpace X] [MeasurableSingletonClass X]
    (f : X → Y) (A : Set X) (y : Y) :
    fiberMultiplicity f A y = Measure.count (A ∩ f ⁻¹' {y}) :=
  (count_apply_eq_encard _).symm

theorem fiberMultiplicity_eq_hausdorffMeasure_zero [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (f : X → Y) (A : Set X) (y : Y) :
    fiberMultiplicity f A y = μH[0] (A ∩ f ⁻¹' {y}) :=
  (hausdorffMeasure_zero_apply _).symm

theorem fiberMultiplicity_eq_euclideanHausdorffMeasure_zero [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (f : X → Y) (A : Set X) (y : Y) :
    fiberMultiplicity f A y = μHE[0] (A ∩ f ⁻¹' {y}) :=
  (euclideanHausdorffMeasure_zero_apply _).symm

variable [MeasurableSpace X]

/-- The weighted fiber sum of `g : X → ℝ≥0∞` along `f : X → Y` restricted to `A : Set X` over
`y : Y`, defined as the Lebesgue integral `∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂Measure.count`. -/
def weightedFiberSum (f : X → Y) (A : Set X) (g : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂Measure.count

theorem weightedFiberSum_def (f : X → Y) (A : Set X) (g : X → ℝ≥0∞) (y : Y) :
    weightedFiberSum f A g y = ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂Measure.count := by
  rfl

@[simp]
theorem weightedFiberSum_empty (f : X → Y) (g : X → ℝ≥0∞) (y : Y) :
    weightedFiberSum f ∅ g y = 0 := by
  simp [weightedFiberSum]

@[simp]
theorem weightedFiberSum_zero (f : X → Y) (A : Set X) (y : Y) :
    weightedFiberSum f A 0 y = 0 := by
  simp [weightedFiberSum]

theorem weightedFiberSum_of_notMem_image {f : X → Y} {A : Set X} (g : X → ℝ≥0∞) {y : Y}
    (hy : y ∉ f '' A) :
    weightedFiberSum f A g y = 0 := by
  have hemp : A ∩ f ⁻¹' {y} = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxA, hxy⟩
    exact hy ⟨x, hxA, hxy⟩
  simp [weightedFiberSum, hemp]

theorem weightedFiberSum_mono_set {f : X → Y} {A B : Set X} (hAB : A ⊆ B) (g : X → ℝ≥0∞) (y : Y) :
    weightedFiberSum f A g y ≤ weightedFiberSum f B g y :=
  lintegral_mono_set (inter_subset_inter_left _ hAB)

theorem weightedFiberSum_mono_fn {f : X → Y} (A : Set X) {g₁ g₂ : X → ℝ≥0∞} (hg : g₁ ≤ g₂)
    (y : Y) :
    weightedFiberSum f A g₁ y ≤ weightedFiberSum f A g₂ y :=
  lintegral_mono hg

theorem weightedFiberSum_eq_lintegral_hausdorffMeasure_zero [EMetricSpace X] [BorelSpace X]
    (f : X → Y) (A : Set X) (g : X → ℝ≥0∞) (y : Y) :
    weightedFiberSum f A g y = ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μH[0] := by
  rw [weightedFiberSum, hausdorffMeasure_zero]

theorem weightedFiberSum_eq_lintegral_euclideanHausdorffMeasure_zero [EMetricSpace X] [BorelSpace X]
    (f : X → Y) (A : Set X) (g : X → ℝ≥0∞) (y : Y) :
    weightedFiberSum f A g y = ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[0] := by
  rw [weightedFiberSum, euclideanHausdorffMeasure_zero_eq_count]

@[simp]
theorem weightedFiberSum_one_eq_fiberMultiplicity [MeasurableSingletonClass X]
    (f : X → Y) (A : Set X) (y : Y) :
    weightedFiberSum f A 1 y = fiberMultiplicity f A y := by
  rw [weightedFiberSum, Pi.one_def, setLIntegral_one, fiberMultiplicity_eq_count]

theorem weightedFiberSum_const [MeasurableSingletonClass X]
    (f : X → Y) (A : Set X) (c : ℝ≥0∞) (y : Y) :
    weightedFiberSum f A (fun _ ↦ c) y = c * fiberMultiplicity f A y := by
  rw [weightedFiberSum, setLIntegral_const, fiberMultiplicity_eq_count]

theorem weightedFiberSum_eq_tsum [MeasurableSingletonClass X]
    (f : X → Y) {A : Set X} (g : X → ℝ≥0∞) {y : Y} (h : MeasurableSet (A ∩ f ⁻¹' {y})) :
    weightedFiberSum f A g y = ∑' x : ↑(A ∩ f ⁻¹' {y}), g x :=
  setLIntegral_count_of_measurableSet g h

theorem weightedFiberSum_eq_tsum_of_measurable [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    {f : X → Y} (hf : Measurable f) {A : Set X} (hA : MeasurableSet A) (g : X → ℝ≥0∞) (y : Y) :
    weightedFiberSum f A g y = ∑' x : ↑(A ∩ f ⁻¹' {y}), g x :=
  weightedFiberSum_eq_tsum f g (hA.inter (hf (measurableSet_singleton y)))

theorem weightedFiberSum_eq_tsum_of_countable [MeasurableSingletonClass X]
    (f : X → Y) {A : Set X} (g : X → ℝ≥0∞) {y : Y} (h : (A ∩ f ⁻¹' {y}).Countable) :
    weightedFiberSum f A g y = ∑' x : ↑(A ∩ f ⁻¹' {y}), g x :=
  setLIntegral_count_of_countable g h

theorem weightedFiberSum_apply_of_injOn [MeasurableSingletonClass X]
    {f : X → Y} {A : Set X} (hf : Set.InjOn f A) (g : X → ℝ≥0∞) {x : X} (hx : x ∈ A) :
    weightedFiberSum f A g (f x) = g x := by
  have heq : A ∩ f ⁻¹' {f x} = {x} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun ⟨hzA, hfz⟩ ↦ hf hzA hx hfz, by rintro rfl; exact ⟨hx, rfl⟩⟩
  rw [weightedFiberSum, heq, lintegral_singleton, Measure.count_singleton, mul_one]

theorem weightedFiberSum_of_injOn [MeasurableSingletonClass X]
    {f : X → Y} {A : Set X} (hf : Set.InjOn f A) (g : X → ℝ≥0∞) {x : X} {y : Y}
    (hx : x ∈ A) (hxy : f x = y) :
    weightedFiberSum f A g y = g x := by
  subst hxy
  exact weightedFiberSum_apply_of_injOn hf g hx

end FiberMultiplicity

/-!
### Comparison between `μHE[k]` and `μH[k]` for null sets, finiteness, and Lipschitz maps
-/

section EuclideanHausdorffComparison

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

set_option backward.isDefEq.respectTransparency false in
/-- A set is `μHE[k]`-null if and only if it is `μH[k]`-null. -/
@[simp]
theorem euclideanHausdorffMeasure_eq_zero_iff (k : ℕ) (s : Set X) :
    μHE[k] s = 0 ↔ μH[k] s = 0 := by
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    mul_eq_zero, ENNReal.coe_eq_zero]
  exact or_iff_right (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero k)

set_option backward.isDefEq.respectTransparency false in
/-- A set has infinite `μHE[k]` measure if and only if it has infinite `μH[k]` measure. -/
@[simp]
theorem euclideanHausdorffMeasure_eq_top_iff (k : ℕ) (s : Set X) :
    μHE[k] s = ⊤ ↔ μH[k] s = ⊤ := by
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ENNReal.mul_eq_top]
  simp [Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero k]

/-- A set has finite `μHE[k]` measure if and only if it has finite `μH[k]` measure. -/
@[simp]
theorem euclideanHausdorffMeasure_lt_top_iff (k : ℕ) (s : Set X) :
    μHE[k] s < ⊤ ↔ μH[k] s < ⊤ := by
  rw [lt_top_iff_ne_top, lt_top_iff_ne_top, Ne, Ne, euclideanHausdorffMeasure_eq_top_iff]

@[simp]
theorem ae_euclideanHausdorffMeasure_iff (k : ℕ) {p : X → Prop} :
    (∀ᵐ x ∂μHE[k], p x) ↔ ∀ᵐ x ∂μH[k], p x := by
  rw [ae_iff, ae_iff, euclideanHausdorffMeasure_eq_zero_iff]

@[simp]
theorem ae_eq_euclideanHausdorffMeasure_iff (k : ℕ) {s t : Set X} :
    (s =ᵐ[μHE[k]] t) ↔ (s =ᵐ[μH[k]] t) := by
  simp only [ae_eq_set, euclideanHausdorffMeasure_eq_zero_iff]

set_option backward.isDefEq.respectTransparency false in
theorem _root_.LipschitzOnWith.euclideanHausdorffMeasure_image_le
    {K : ℝ≥0} {f : X → Y} {s : Set X} (hf : LipschitzOnWith K f s) (k : ℕ) :
    μHE[k] (f '' s) ≤ (K : ℝ≥0∞) ^ k * μHE[k] s := by
  rw [Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def,
    Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
    smul_eq_mul, ← mul_left_comm]
  gcongr
  simpa [ENNReal.rpow_natCast] using hf.hausdorffMeasure_image_le (Nat.cast_nonneg k)

theorem _root_.LipschitzWith.euclideanHausdorffMeasure_image_le
    {K : ℝ≥0} {f : X → Y} (hf : LipschitzWith K f) (k : ℕ) (s : Set X) :
    μHE[k] (f '' s) ≤ (K : ℝ≥0∞) ^ k * μHE[k] s :=
  hf.lipschitzOnWith.euclideanHausdorffMeasure_image_le k

end EuclideanHausdorffComparison

/-!
### Purely `k`-rectifiable and countably `k`-rectifiable sets
-/

section RectifiableDefinitions

variable {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

/-- A set `s : Set X` in an extended metric space is **purely `k`-rectifiable** if it is contained
in a countable union of Lipschitz images of subsets of `EuclideanSpace ℝ (Fin k)`. -/
def PurelyRectifiable (k : ℕ) (s : Set X) : Prop :=
  ∃ (K : ℕ → ℝ≥0) (A : ℕ → Set (EuclideanSpace ℝ (Fin k)))
    (f : ℕ → EuclideanSpace ℝ (Fin k) → X),
    (∀ i, LipschitzOnWith (K i) (f i) (A i)) ∧ s ⊆ ⋃ i, f i '' A i

/-- A set `s : Set X` in an extended metric space is **countably `k`-rectifiable** if it is covered
up to a `μH[k]`-null set by a countable union of Lipschitz images of subsets of
`EuclideanSpace ℝ (Fin k)`. -/
def CountablyRectifiable [MeasurableSpace X] [BorelSpace X] (k : ℕ) (s : Set X) : Prop :=
  ∃ (K : ℕ → ℝ≥0) (A : ℕ → Set (EuclideanSpace ℝ (Fin k)))
    (f : ℕ → EuclideanSpace ℝ (Fin k) → X),
    (∀ i, LipschitzOnWith (K i) (f i) (A i)) ∧ μH[k] (s \ ⋃ i, f i '' A i) = 0

namespace PurelyRectifiable

theorem of_lipschitzOnWith {k : ℕ} {K : ℝ≥0} {A : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → X} {s : Set X}
    (hf : LipschitzOnWith K f A) (hs : s ⊆ f '' A) :
    PurelyRectifiable k s :=
  ⟨fun _ ↦ K, fun _ ↦ A, fun _ ↦ f, fun _ ↦ hf, hs.trans (subset_iUnion (fun _ ↦ f '' A) 0)⟩

theorem image_of_lipschitzOnWith {k : ℕ} {K : ℝ≥0} {A : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → X} (hf : LipschitzOnWith K f A) :
    PurelyRectifiable k (f '' A) :=
  of_lipschitzOnWith hf Subset.rfl

theorem of_lipschitzWith {k : ℕ} {K : ℝ≥0} {A : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → X} {s : Set X}
    (hf : LipschitzWith K f) (hs : s ⊆ f '' A) :
    PurelyRectifiable k s :=
  of_lipschitzOnWith hf.lipschitzOnWith hs

theorem range_of_lipschitzWith {k : ℕ} {K : ℝ≥0} {f : EuclideanSpace ℝ (Fin k) → X}
    (hf : LipschitzWith K f) :
    PurelyRectifiable k (Set.range f) :=
  of_lipschitzWith (A := Set.univ) hf (by simp)

theorem empty [Nonempty X] (k : ℕ) : PurelyRectifiable k (∅ : Set X) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  exact ⟨fun _ ↦ 0, fun _ ↦ ∅, fun _ _ ↦ x₀,
    fun _ ↦ (LipschitzWith.const x₀).lipschitzOnWith, empty_subset _⟩

theorem singleton (k : ℕ) (x : X) : PurelyRectifiable k ({x} : Set X) :=
  ⟨fun _ ↦ 0, fun _ ↦ {0}, fun _ _ ↦ x,
    fun _ ↦ (LipschitzWith.const x).lipschitzOnWith, by
      intro z hz
      rw [mem_singleton_iff.mp hz]
      exact mem_iUnion.mpr ⟨0, 0, mem_singleton 0, rfl⟩⟩

theorem subsingleton [Nonempty X] (k : ℕ) {s : Set X} (hs : s.Subsingleton) :
    PurelyRectifiable k s := by
  rcases hs.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact empty k
  · exact singleton k x

theorem mono {k : ℕ} {s t : Set X} (ht : PurelyRectifiable k t) (hst : s ⊆ t) :
    PurelyRectifiable k s := by
  rcases ht with ⟨K, A, f, hf, ht⟩
  exact ⟨K, A, f, hf, hst.trans ht⟩

theorem inter_left {k : ℕ} {s : Set X} (hs : PurelyRectifiable k s) (t : Set X) :
    PurelyRectifiable k (s ∩ t) :=
  hs.mono inter_subset_left

theorem inter_right {k : ℕ} {t : Set X} (ht : PurelyRectifiable k t) (s : Set X) :
    PurelyRectifiable k (s ∩ t) :=
  ht.mono inter_subset_right

theorem diff {k : ℕ} {s : Set X} (hs : PurelyRectifiable k s) (t : Set X) :
    PurelyRectifiable k (s \ t) :=
  hs.mono sdiff_subset

theorem union {k : ℕ} {s t : Set X} (hs : PurelyRectifiable k s) (ht : PurelyRectifiable k t) :
    PurelyRectifiable k (s ∪ t) := by
  rcases hs with ⟨K₁, A₁, f₁, hf₁, hs⟩
  rcases ht with ⟨K₂, A₂, f₂, hf₂, ht⟩
  refine ⟨fun n ↦ if n.bodd then K₂ n.div2 else K₁ n.div2,
    fun n ↦ if n.bodd then A₂ n.div2 else A₁ n.div2,
    fun n ↦ if n.bodd then f₂ n.div2 else f₁ n.div2,
    fun n ↦ ?_, ?_⟩
  · dsimp only
    split_ifs <;> [exact hf₂ _; exact hf₁ _]
  · rintro x (hxs | hxt)
    · rcases mem_iUnion.mp (hs hxs) with ⟨i, hi⟩
      refine mem_iUnion.mpr ⟨Nat.bit false i, ?_⟩
      simpa [Nat.bodd_bit, Nat.div2_bit] using hi
    · rcases mem_iUnion.mp (ht hxt) with ⟨i, hi⟩
      refine mem_iUnion.mpr ⟨Nat.bit true i, ?_⟩
      simpa [Nat.bodd_bit, Nat.div2_bit] using hi

theorem iUnion_nat {k : ℕ} {s : ℕ → Set X}
    (hs : ∀ i, PurelyRectifiable k (s i)) :
    PurelyRectifiable k (⋃ i, s i) := by
  choose K A f hf hsub using hs
  refine ⟨fun n ↦ K n.unpair.1 n.unpair.2,
    fun n ↦ A n.unpair.1 n.unpair.2,
    fun n ↦ f n.unpair.1 n.unpair.2,
    fun n ↦ hf n.unpair.1 n.unpair.2, ?_⟩
  rintro x hx
  rcases mem_iUnion.mp hx with ⟨i, hxi⟩
  rcases mem_iUnion.mp (hsub i hxi) with ⟨j, hxj⟩
  refine mem_iUnion.mpr ⟨Nat.pair i j, ?_⟩
  simpa [Nat.unpair_pair] using hxj

theorem iUnion {ι : Type*} [Countable ι] [Nonempty X] {k : ℕ} {s : ι → Set X}
    (hs : ∀ i, PurelyRectifiable k (s i)) :
    PurelyRectifiable k (⋃ i, s i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [iUnion_of_empty]
    exact empty k
  · obtain ⟨p, hp⟩ := exists_surjective_nat ι
    have heq : (⋃ i : ι, s i) = ⋃ n : ℕ, s (p n) := (hp.iUnion_comp s).symm
    rw [heq]
    exact iUnion_nat fun n ↦ hs (p n)

theorem biUnion {ι : Type*} {I : Set ι} (hI : I.Countable) [Nonempty X] {k : ℕ}
    {s : ι → Set X} (hs : ∀ i ∈ I, PurelyRectifiable k (s i)) :
    PurelyRectifiable k (⋃ i ∈ I, s i) := by
  have : Countable I := hI.to_subtype
  rw [biUnion_eq_iUnion]
  exact iUnion fun i : I ↦ hs i.1 i.2

theorem sUnion [Nonempty X] {k : ℕ} {S : Set (Set X)} (hS : S.Countable)
    (hs : ∀ s ∈ S, PurelyRectifiable k s) :
    PurelyRectifiable k (⋃₀ S) := by
  rw [sUnion_eq_biUnion]
  exact biUnion hS hs

theorem of_countable [Nonempty X] (k : ℕ) {s : Set X} (hs : s.Countable) :
    PurelyRectifiable k s := by
  rw [← biUnion_of_singleton s]
  exact biUnion hs fun x _ ↦ singleton k x

/-- Every purely `0`-rectifiable set is countable. -/
theorem countable_of_zero {s : Set X} (hs : PurelyRectifiable 0 s) :
    s.Countable := by
  rcases hs with ⟨_, A, f, _, hs⟩
  exact (countable_iUnion fun i ↦ (to_countable (A i)).image (f i)).mono hs

/-- A purely `k`-rectifiable set is mapped by any `LipschitzOnWith` function to a purely
`k`-rectifiable set. -/
theorem image_lipschitzOnWith {k : ℕ} {s : Set X} {C : ℝ≥0} {g : X → Y}
    (hs : PurelyRectifiable k s) (hg : LipschitzOnWith C g s) :
    PurelyRectifiable k (g '' s) := by
  rcases hs with ⟨K, A, f, hf, hs⟩
  refine ⟨fun i ↦ C * K i, fun i ↦ A i ∩ f i ⁻¹' s, fun i ↦ g ∘ f i,
    fun i ↦ hg.comp ((hf i).mono inter_subset_left) (fun x hx ↦ hx.2), ?_⟩
  rintro y ⟨x, hxs, rfl⟩
  rcases mem_iUnion.mp (hs hxs) with ⟨i, u, hu, hfu⟩
  exact mem_iUnion.mpr ⟨i, u, ⟨hu, by simpa [hfu] using hxs⟩, by simp [hfu]⟩

theorem image_lipschitzWith {k : ℕ} {s : Set X} {C : ℝ≥0} {g : X → Y}
    (hs : PurelyRectifiable k s) (hg : LipschitzWith C g) :
    PurelyRectifiable k (g '' s) :=
  hs.image_lipschitzOnWith hg.lipschitzOnWith

theorem countablyRectifiable [MeasurableSpace X] [BorelSpace X] {k : ℕ} {s : Set X}
    (hs : PurelyRectifiable k s) :
    CountablyRectifiable k s := by
  rcases hs with ⟨K, A, f, hf, hs⟩
  exact ⟨K, A, f, hf, by rw [sdiff_eq_empty.mpr hs, measure_empty]⟩

end PurelyRectifiable

/-- In dimension `0`, pure rectifiability is equivalent to countability. -/
@[simp]
theorem purelyRectifiable_zero_iff_countable [Nonempty X] {s : Set X} :
    PurelyRectifiable 0 s ↔ s.Countable :=
  ⟨PurelyRectifiable.countable_of_zero, PurelyRectifiable.of_countable 0⟩

theorem _root_.Set.Subsingleton.purelyRectifiable [Nonempty X] (k : ℕ) {s : Set X}
    (hs : s.Subsingleton) :
    PurelyRectifiable k s :=
  PurelyRectifiable.subsingleton k hs

theorem _root_.Set.Countable.purelyRectifiable [Nonempty X] (k : ℕ) {s : Set X}
    (hs : s.Countable) :
    PurelyRectifiable k s :=
  PurelyRectifiable.of_countable k hs

theorem _root_.LipschitzOnWith.purelyRectifiable_image {k : ℕ} {s : Set X} {C : ℝ≥0} {g : X → Y}
    (hg : LipschitzOnWith C g s) (hs : PurelyRectifiable k s) :
    PurelyRectifiable k (g '' s) :=
  hs.image_lipschitzOnWith hg

theorem _root_.LipschitzWith.purelyRectifiable_image {k : ℕ} {s : Set X} {C : ℝ≥0} {g : X → Y}
    (hg : LipschitzWith C g) (hs : PurelyRectifiable k s) :
    PurelyRectifiable k (g '' s) :=
  hs.image_lipschitzWith hg

/-- A set is purely `k`-rectifiable if and only if it is covered by a countable union of Lipschitz
images of **bounded** subsets of `EuclideanSpace ℝ (Fin k)`. -/
theorem purelyRectifiable_iff_bounded {k : ℕ} {s : Set X} :
    PurelyRectifiable k s ↔
      ∃ (K : ℕ → ℝ≥0) (A : ℕ → Set (EuclideanSpace ℝ (Fin k)))
        (f : ℕ → EuclideanSpace ℝ (Fin k) → X),
        (∀ i, Bornology.IsBounded (A i)) ∧
          (∀ i, LipschitzOnWith (K i) (f i) (A i)) ∧ s ⊆ ⋃ i, f i '' A i := by
  constructor
  · rintro ⟨K, A, f, hf, hs⟩
    refine ⟨fun n ↦ K n.unpair.1,
      fun n ↦ A n.unpair.1 ∩ Metric.closedBall 0 n.unpair.2,
      fun n ↦ f n.unpair.1,
      fun n ↦ Metric.isBounded_closedBall.subset inter_subset_right,
      fun n ↦ (hf n.unpair.1).mono inter_subset_left, ?_⟩
    intro x hxs
    rcases mem_iUnion.mp (hs hxs) with ⟨i, u, hu, rfl⟩
    refine mem_iUnion.mpr ⟨Nat.pair i ⌈‖u‖⌉₊, ?_⟩
    simp only [Nat.unpair_pair, mem_image]
    refine ⟨u, ⟨hu, ?_⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Nat.le_ceil ‖u‖
  · rintro ⟨K, A, f, _, hf, hs⟩
    exact ⟨K, A, f, hf, hs⟩

end RectifiableDefinitions

/-!
### Closure and transport API for `CountablyRectifiable`
-/

section CountablyRectifiableAPI

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A set `s` is countably `k`-rectifiable if and only if there exists a purely `k`-rectifiable set
`t` such that `μH[k] (s \ t) = 0`. -/
theorem countablyRectifiable_iff_exists_purelyRectifiable {k : ℕ} {s : Set X} :
    CountablyRectifiable k s ↔ ∃ t, PurelyRectifiable k t ∧ μH[k] (s \ t) = 0 := by
  constructor
  · rintro ⟨K, A, f, hf, hnull⟩
    exact ⟨⋃ i, f i '' A i, ⟨K, A, f, hf, Subset.rfl⟩, hnull⟩
  · rintro ⟨t, ⟨K, A, f, hf, ht⟩, hnull⟩
    exact ⟨K, A, f, hf, measure_mono_null (sdiff_subset_sdiff_right ht) hnull⟩

/-- A set `s` is countably `k`-rectifiable if and only if it contains a purely `k`-rectifiable
subset `t ⊆ s` whose complement in `s` has `μH[k]` measure zero. -/
theorem countablyRectifiable_iff_exists_subset_purelyRectifiable {k : ℕ} {s : Set X} :
    CountablyRectifiable k s ↔ ∃ t ⊆ s, PurelyRectifiable k t ∧ μH[k] (s \ t) = 0 := by
  rw [countablyRectifiable_iff_exists_purelyRectifiable]
  constructor
  · rintro ⟨t, ht, hnull⟩
    refine ⟨s ∩ t, inter_subset_left, ht.inter_right s, ?_⟩
    rwa [sdiff_self_inter]
  · rintro ⟨t, _, ht, hnull⟩
    exact ⟨t, ht, hnull⟩

/-- Characterization of `CountablyRectifiable` using the normalized Euclidean Hausdorff measure
`μHE[k]`. -/
theorem countablyRectifiable_iff_euclideanHausdorffMeasure {k : ℕ} {s : Set X} :
    CountablyRectifiable k s ↔
      ∃ (K : ℕ → ℝ≥0) (A : ℕ → Set (EuclideanSpace ℝ (Fin k)))
        (f : ℕ → EuclideanSpace ℝ (Fin k) → X),
        (∀ i, LipschitzOnWith (K i) (f i) (A i)) ∧ μHE[k] (s \ ⋃ i, f i '' A i) = 0 := by
  simp_rw [CountablyRectifiable, euclideanHausdorffMeasure_eq_zero_iff]

/-- A set is countably `k`-rectifiable if and only if it is covered up to a `μH[k]`-null set by a
countable union of Lipschitz images of **bounded** subsets of `EuclideanSpace ℝ (Fin k)`. -/
theorem countablyRectifiable_iff_bounded {k : ℕ} {s : Set X} :
    CountablyRectifiable k s ↔
      ∃ (K : ℕ → ℝ≥0) (A : ℕ → Set (EuclideanSpace ℝ (Fin k)))
        (f : ℕ → EuclideanSpace ℝ (Fin k) → X),
        (∀ i, Bornology.IsBounded (A i)) ∧
          (∀ i, LipschitzOnWith (K i) (f i) (A i)) ∧ μH[k] (s \ ⋃ i, f i '' A i) = 0 := by
  constructor
  · rintro ⟨K, A, f, hf, hnull⟩
    have hpure : PurelyRectifiable k (⋃ i, f i '' A i) := ⟨K, A, f, hf, Subset.rfl⟩
    rcases purelyRectifiable_iff_bounded.mp hpure with ⟨K', A', f', hbdd, hf', hsub⟩
    exact ⟨K', A', f', hbdd, hf', measure_mono_null (sdiff_subset_sdiff_right hsub) hnull⟩
  · rintro ⟨K, A, f, _, hf, hnull⟩
    exact ⟨K, A, f, hf, hnull⟩

namespace CountablyRectifiable

theorem of_lipschitzOnWith {k : ℕ} {K : ℝ≥0} {A : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → X} {s : Set X}
    (hf : LipschitzOnWith K f A) (hs : s ⊆ f '' A) :
    CountablyRectifiable k s :=
  (PurelyRectifiable.of_lipschitzOnWith hf hs).countablyRectifiable

theorem image_of_lipschitzOnWith {k : ℕ} {K : ℝ≥0} {A : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → X} (hf : LipschitzOnWith K f A) :
    CountablyRectifiable k (f '' A) :=
  (PurelyRectifiable.image_of_lipschitzOnWith hf).countablyRectifiable

theorem of_lipschitzWith {k : ℕ} {K : ℝ≥0} {A : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → X} {s : Set X}
    (hf : LipschitzWith K f) (hs : s ⊆ f '' A) :
    CountablyRectifiable k s :=
  (PurelyRectifiable.of_lipschitzWith hf hs).countablyRectifiable

theorem range_of_lipschitzWith {k : ℕ} {K : ℝ≥0} {f : EuclideanSpace ℝ (Fin k) → X}
    (hf : LipschitzWith K f) :
    CountablyRectifiable k (Set.range f) :=
  (PurelyRectifiable.range_of_lipschitzWith hf).countablyRectifiable

theorem empty [Nonempty X] (k : ℕ) : CountablyRectifiable k (∅ : Set X) :=
  (PurelyRectifiable.empty k).countablyRectifiable

theorem singleton (k : ℕ) (x : X) : CountablyRectifiable k ({x} : Set X) :=
  (PurelyRectifiable.singleton k x).countablyRectifiable

theorem subsingleton [Nonempty X] (k : ℕ) {s : Set X} (hs : s.Subsingleton) :
    CountablyRectifiable k s :=
  (PurelyRectifiable.subsingleton k hs).countablyRectifiable

theorem of_countable [Nonempty X] (k : ℕ) {s : Set X} (hs : s.Countable) :
    CountablyRectifiable k s :=
  (PurelyRectifiable.of_countable k hs).countablyRectifiable

/-- Every countably `0`-rectifiable set is countable. -/
theorem countable_of_zero {s : Set X} (hs : CountablyRectifiable 0 s) :
    s.Countable := by
  rcases countablyRectifiable_iff_exists_purelyRectifiable.mp hs with ⟨t, ht, hnull⟩
  have hsub : s ⊆ t := sdiff_eq_empty.mp
    ((hausdorffMeasure_zero_eq_zero_iff (s \ t)).mp (by simpa using hnull))
  exact ht.countable_of_zero.mono hsub

/-- Every countably `0`-rectifiable set is purely `0`-rectifiable. -/
theorem purelyRectifiable_of_zero [Nonempty X] {s : Set X} (hs : CountablyRectifiable 0 s) :
    PurelyRectifiable 0 s :=
  PurelyRectifiable.of_countable 0 hs.countable_of_zero

/-- Any `μH[k]`-null set is countably `k`-rectifiable. -/
theorem of_hausdorffMeasure_eq_zero [Nonempty X] {k : ℕ} {s : Set X} (hs : μH[k] s = 0) :
    CountablyRectifiable k s := by
  rw [countablyRectifiable_iff_exists_purelyRectifiable]
  exact ⟨∅, PurelyRectifiable.empty k, by simpa using hs⟩

/-- Any `μHE[k]`-null set is countably `k`-rectifiable. -/
theorem of_euclideanHausdorffMeasure_eq_zero [Nonempty X] {k : ℕ} {s : Set X}
    (hs : μHE[k] s = 0) :
    CountablyRectifiable k s :=
  of_hausdorffMeasure_eq_zero ((euclideanHausdorffMeasure_eq_zero_iff k s).mp hs)

theorem mono {k : ℕ} {s t : Set X} (ht : CountablyRectifiable k t) (hst : s ⊆ t) :
    CountablyRectifiable k s := by
  rcases ht with ⟨K, A, f, hf, ht⟩
  exact ⟨K, A, f, hf, measure_mono_null (sdiff_subset_sdiff_left hst) ht⟩

theorem inter_left {k : ℕ} {s : Set X} (hs : CountablyRectifiable k s) (t : Set X) :
    CountablyRectifiable k (s ∩ t) :=
  hs.mono inter_subset_left

theorem inter_right {k : ℕ} {t : Set X} (ht : CountablyRectifiable k t) (s : Set X) :
    CountablyRectifiable k (s ∩ t) :=
  ht.mono inter_subset_right

theorem diff {k : ℕ} {s : Set X} (hs : CountablyRectifiable k s) (t : Set X) :
    CountablyRectifiable k (s \ t) :=
  hs.mono sdiff_subset

theorem union {k : ℕ} {s t : Set X}
    (hs : CountablyRectifiable k s) (ht : CountablyRectifiable k t) :
    CountablyRectifiable k (s ∪ t) := by
  rcases countablyRectifiable_iff_exists_purelyRectifiable.mp hs with ⟨s', hs', hns⟩
  rcases countablyRectifiable_iff_exists_purelyRectifiable.mp ht with ⟨t', ht', hnt⟩
  refine countablyRectifiable_iff_exists_purelyRectifiable.mpr ⟨s' ∪ t', hs'.union ht', ?_⟩
  have hsub : (s ∪ t) \ (s' ∪ t') ⊆ (s \ s') ∪ (t \ t') := by
    intro x ⟨hx, hx'⟩
    rcases hx with hxs | hxt
    · exact Or.inl ⟨hxs, fun h ↦ hx' (Or.inl h)⟩
    · exact Or.inr ⟨hxt, fun h ↦ hx' (Or.inr h)⟩
  exact measure_mono_null hsub (measure_union_null hns hnt)

theorem iUnion {ι : Type*} [Countable ι] [Nonempty X] {k : ℕ} {s : ι → Set X}
    (hs : ∀ i, CountablyRectifiable k (s i)) :
    CountablyRectifiable k (⋃ i, s i) := by
  choose t ht hnull using fun i ↦ countablyRectifiable_iff_exists_purelyRectifiable.mp (hs i)
  refine countablyRectifiable_iff_exists_purelyRectifiable.mpr
    ⟨⋃ i, t i, PurelyRectifiable.iUnion ht, ?_⟩
  have hsub : (⋃ i, s i) \ (⋃ i, t i) ⊆ ⋃ i, (s i \ t i) := by
    intro x ⟨hx, hxt⟩
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    exact mem_iUnion.mpr ⟨i, hxi, fun hxti ↦ hxt (mem_iUnion.mpr ⟨i, hxti⟩)⟩
  exact measure_mono_null hsub (measure_iUnion_null hnull)

theorem biUnion {ι : Type*} {I : Set ι} (hI : I.Countable) [Nonempty X] {k : ℕ}
    {s : ι → Set X} (hs : ∀ i ∈ I, CountablyRectifiable k (s i)) :
    CountablyRectifiable k (⋃ i ∈ I, s i) := by
  have : Countable I := hI.to_subtype
  rw [biUnion_eq_iUnion]
  exact iUnion fun i : I ↦ hs i.1 i.2

theorem sUnion [Nonempty X] {k : ℕ} {S : Set (Set X)} (hS : S.Countable)
    (hs : ∀ s ∈ S, CountablyRectifiable k s) :
    CountablyRectifiable k (⋃₀ S) := by
  rw [sUnion_eq_biUnion]
  exact biUnion hS hs

/-- If `s` is countably `k`-rectifiable and `μH[k] (t \ s) = 0`, then `t` is countably
`k`-rectifiable. -/
theorem of_diff_null {k : ℕ} {s t : Set X} (hs : CountablyRectifiable k s)
    (h : μH[k] (t \ s) = 0) :
    CountablyRectifiable k t := by
  rcases countablyRectifiable_iff_exists_purelyRectifiable.mp hs with ⟨u, hu, hsu⟩
  refine countablyRectifiable_iff_exists_purelyRectifiable.mpr ⟨u, hu, ?_⟩
  have hsub : t \ u ⊆ (t \ s) ∪ (s \ u) := by
    intro x ⟨hxt, hxu⟩
    by_cases hxs : x ∈ s
    · exact Or.inr ⟨hxs, hxu⟩
    · exact Or.inl ⟨hxt, hxs⟩
  exact measure_mono_null hsub (measure_union_null h hsu)

/-- If `s` is countably `k`-rectifiable and `μHE[k] (t \ s) = 0`, then `t` is countably
`k`-rectifiable. -/
theorem of_diff_euclideanHausdorffMeasure_null {k : ℕ} {s t : Set X}
    (hs : CountablyRectifiable k s) (h : μHE[k] (t \ s) = 0) :
    CountablyRectifiable k t :=
  hs.of_diff_null ((euclideanHausdorffMeasure_eq_zero_iff k (t \ s)).mp h)

/-- Countable `k`-rectifiability is invariant under `=ᵐ[μH[k]]` modifications. -/
theorem congr_ae {k : ℕ} {s t : Set X} (hs : CountablyRectifiable k s) (h : s =ᵐ[μH[k]] t) :
    CountablyRectifiable k t :=
  hs.of_diff_null (ae_eq_set.mp h).2

/-- Countable `k`-rectifiability is invariant under `=ᵐ[μHE[k]]` modifications. -/
theorem congr_ae_euclideanHausdorffMeasure {k : ℕ} {s t : Set X}
    (hs : CountablyRectifiable k s) (h : s =ᵐ[μHE[k]] t) :
    CountablyRectifiable k t :=
  hs.congr_ae ((ae_eq_euclideanHausdorffMeasure_iff k).mp h)

/-- A countably `k`-rectifiable set is mapped by any `LipschitzOnWith` function to a countably
`k`-rectifiable set. -/
theorem image_lipschitzOnWith {k : ℕ} {s : Set X} {C : ℝ≥0}
    {g : X → Y} (hs : CountablyRectifiable k s) (hg : LipschitzOnWith C g s) :
    CountablyRectifiable k (g '' s) := by
  rcases countablyRectifiable_iff_exists_subset_purelyRectifiable.mp hs with ⟨t, hts, ht, hnull⟩
  refine countablyRectifiable_iff_exists_purelyRectifiable.mpr
    ⟨g '' t, ht.image_lipschitzOnWith (hg.mono hts), ?_⟩
  have hsub : g '' s \ g '' t ⊆ g '' (s \ t) := subset_image_sdiff g s t
  have hlip_diff : LipschitzOnWith C g (s \ t) := hg.mono sdiff_subset
  refine measure_mono_null hsub ?_
  rw [← nonpos_iff_eq_zero]
  calc
    μH[k] (g '' (s \ t)) ≤ (C : ℝ≥0∞) ^ (k : ℝ) * μH[k] (s \ t) :=
      hlip_diff.hausdorffMeasure_image_le (Nat.cast_nonneg k)
    _ = 0 := by simp [hnull]

theorem image_lipschitzWith {k : ℕ} {s : Set X} {C : ℝ≥0}
    {g : X → Y} (hs : CountablyRectifiable k s) (hg : LipschitzWith C g) :
    CountablyRectifiable k (g '' s) :=
  hs.image_lipschitzOnWith hg.lipschitzOnWith

end CountablyRectifiable

/-- In dimension `0`, countable rectifiability is equivalent to countability. -/
@[simp]
theorem countablyRectifiable_zero_iff_countable [Nonempty X] {s : Set X} :
    CountablyRectifiable 0 s ↔ s.Countable :=
  ⟨CountablyRectifiable.countable_of_zero, CountablyRectifiable.of_countable 0⟩

/-- In dimension `0`, countable rectifiability coincides with pure rectifiability. -/
theorem countablyRectifiable_zero_iff_purelyRectifiable [Nonempty X] {s : Set X} :
    CountablyRectifiable 0 s ↔ PurelyRectifiable 0 s :=
  ⟨CountablyRectifiable.purelyRectifiable_of_zero, PurelyRectifiable.countablyRectifiable⟩

theorem countablyRectifiable_congr_ae {k : ℕ} {s t : Set X} (h : s =ᵐ[μH[k]] t) :
    CountablyRectifiable k s ↔ CountablyRectifiable k t :=
  ⟨fun hs ↦ hs.congr_ae h, fun ht ↦ ht.congr_ae h.symm⟩

theorem countablyRectifiable_congr_ae_euclideanHausdorffMeasure {k : ℕ}
    {s t : Set X} (h : s =ᵐ[μHE[k]] t) :
    CountablyRectifiable k s ↔ CountablyRectifiable k t :=
  countablyRectifiable_congr_ae ((ae_eq_euclideanHausdorffMeasure_iff k).mp h)

theorem _root_.Set.Subsingleton.countablyRectifiable [Nonempty X] (k : ℕ) {s : Set X}
    (hs : s.Subsingleton) :
    CountablyRectifiable k s :=
  CountablyRectifiable.subsingleton k hs

theorem _root_.Set.Countable.countablyRectifiable [Nonempty X] (k : ℕ) {s : Set X}
    (hs : s.Countable) :
    CountablyRectifiable k s :=
  CountablyRectifiable.of_countable k hs

theorem _root_.LipschitzOnWith.countablyRectifiable_image
    {k : ℕ} {s : Set X} {C : ℝ≥0} {g : X → Y}
    (hg : LipschitzOnWith C g s) (hs : CountablyRectifiable k s) :
    CountablyRectifiable k (g '' s) :=
  hs.image_lipschitzOnWith hg

theorem _root_.LipschitzWith.countablyRectifiable_image
    {k : ℕ} {s : Set X} {C : ℝ≥0} {g : X → Y}
    (hg : LipschitzWith C g) (hs : CountablyRectifiable k s) :
    CountablyRectifiable k (g '' s) :=
  hs.image_lipschitzWith hg

end CountablyRectifiableAPI

/-!
### Isometries and isometric equivalences
-/

section Isometries

variable {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

/-- An isometry `g : X → Y` preserves pure `k`-rectifiability. -/
theorem _root_.Isometry.purelyRectifiable_image {k : ℕ} {s : Set X} {g : X → Y}
    (hg : Isometry g) (hs : PurelyRectifiable k s) :
    PurelyRectifiable k (g '' s) :=
  hs.image_lipschitzWith hg.lipschitzWith

/-- If `g : X → Y` is an isometry and `g '' s` is purely `k`-rectifiable, then `s` is purely
`k`-rectifiable (assuming `Nonempty X` to handle the case `s = ∅`). -/
theorem _root_.Isometry.purelyRectifiable_of_image [Nonempty X] {k : ℕ} {s : Set X} {g : X → Y}
    (hg : Isometry g) (hs : PurelyRectifiable k (g '' s)) :
    PurelyRectifiable k s := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  rcases hs with ⟨K, A, f, hf, hsub⟩
  let B : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun i ↦ A i ∩ f i ⁻¹' (g '' s)
  let h : ℕ → EuclideanSpace ℝ (Fin k) → X := fun i u ↦
    if hu : f i u ∈ g '' s then hu.choose else x₀
  have hh_spec : ∀ i u (hu : f i u ∈ g '' s), h i u ∈ s ∧ g (h i u) = f i u := by
    intro i u hu
    have heq : h i u = hu.choose := dite_eq_left_of_eq_true (eq_true hu)
    rw [heq]
    exact hu.choose_spec
  refine ⟨K, B, h, fun i ↦ ?_, ?_⟩
  · intro u₁ hu₁ u₂ hu₂
    rw [← hg.edist_eq, (hh_spec i u₁ hu₁.2).2, (hh_spec i u₂ hu₂.2).2]
    exact hf i hu₁.1 hu₂.1
  · intro x hxs
    have hgx : g x ∈ g '' s := mem_image_of_mem g hxs
    rcases mem_iUnion.mp (hsub hgx) with ⟨i, u, huA, hfu⟩
    have huB : u ∈ B i := ⟨huA, by rw [mem_preimage, hfu]; exact hgx⟩
    refine mem_iUnion.mpr ⟨i, u, huB, ?_⟩
    apply hg.injective
    rw [(hh_spec i u huB.2).2, hfu]

@[simp]
theorem _root_.Isometry.purelyRectifiable_image_iff [Nonempty X] {k : ℕ} {s : Set X} {g : X → Y}
    (hg : Isometry g) :
    PurelyRectifiable k (g '' s) ↔ PurelyRectifiable k s :=
  ⟨hg.purelyRectifiable_of_image, hg.purelyRectifiable_image⟩

@[simp]
theorem _root_.IsometryEquiv.purelyRectifiable_image_iff {k : ℕ} {s : Set X} (e : X ≃ᵢ Y) :
    PurelyRectifiable k (e '' s) ↔ PurelyRectifiable k s := by
  refine ⟨fun h ↦ ?_, e.isometry.purelyRectifiable_image⟩
  have h' := e.symm.isometry.purelyRectifiable_image h
  rwa [← Set.image_comp, e.symm_comp_self, Set.image_id] at h'

@[simp]
theorem _root_.IsometryEquiv.purelyRectifiable_preimage_iff {k : ℕ} {t : Set Y} (e : X ≃ᵢ Y) :
    PurelyRectifiable k (e ⁻¹' t) ↔ PurelyRectifiable k t := by
  rw [← e.image_symm, e.symm.purelyRectifiable_image_iff]

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- An isometry `g : X → Y` preserves countable `k`-rectifiability. -/
theorem _root_.Isometry.countablyRectifiable_image {k : ℕ} {s : Set X} {g : X → Y}
    (hg : Isometry g) (hs : CountablyRectifiable k s) :
    CountablyRectifiable k (g '' s) :=
  hs.image_lipschitzWith hg.lipschitzWith

/-- If `g : X → Y` is an isometry and `g '' s` is countably `k`-rectifiable, then `s` is countably
`k`-rectifiable. -/
theorem _root_.Isometry.countablyRectifiable_of_image [Nonempty X] {k : ℕ} {s : Set X} {g : X → Y}
    (hg : Isometry g) (hs : CountablyRectifiable k (g '' s)) :
    CountablyRectifiable k s := by
  rcases countablyRectifiable_iff_exists_subset_purelyRectifiable.mp hs with ⟨t, hts, ht, hnull⟩
  have hpre : t = g '' (s ∩ g ⁻¹' t) := by
    ext y
    constructor
    · intro hyt
      rcases hts hyt with ⟨x, hxs, rfl⟩
      exact ⟨x, ⟨hxs, hyt⟩, rfl⟩
    · rintro ⟨x, ⟨_, hxt⟩, rfl⟩
      exact hxt
  rw [hpre] at ht hnull
  have ht' : PurelyRectifiable k (s ∩ g ⁻¹' t) := hg.purelyRectifiable_of_image ht
  refine countablyRectifiable_iff_exists_purelyRectifiable.mpr ⟨s ∩ g ⁻¹' t, ht', ?_⟩
  rw [← hg.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg k)),
    image_sdiff hg.injective]
  exact hnull

@[simp]
theorem _root_.Isometry.countablyRectifiable_image_iff [Nonempty X] {k : ℕ} {s : Set X}
    {g : X → Y} (hg : Isometry g) :
    CountablyRectifiable k (g '' s) ↔ CountablyRectifiable k s :=
  ⟨hg.countablyRectifiable_of_image, hg.countablyRectifiable_image⟩

@[simp]
theorem _root_.IsometryEquiv.countablyRectifiable_image_iff {k : ℕ} {s : Set X} (e : X ≃ᵢ Y) :
    CountablyRectifiable k (e '' s) ↔ CountablyRectifiable k s := by
  refine ⟨fun h ↦ ?_, e.isometry.countablyRectifiable_image⟩
  have h' := e.symm.isometry.countablyRectifiable_image h
  rwa [← Set.image_comp, e.symm_comp_self, Set.image_id] at h'

@[simp]
theorem _root_.IsometryEquiv.countablyRectifiable_preimage_iff {k : ℕ} {t : Set Y} (e : X ≃ᵢ Y) :
    CountablyRectifiable k (e ⁻¹' t) ↔ CountablyRectifiable k t := by
  rw [← e.image_symm, e.symm.countablyRectifiable_image_iff]

end Isometries

/-!
### Euclidean spaces, finite-dimensional normed spaces, and continuous linear maps
-/

section NormedSpaces

/-- Every subset of `EuclideanSpace ℝ (Fin k)` is purely `k`-rectifiable. -/
theorem purelyRectifiable_subset_euclideanSpace (k : ℕ) (s : Set (EuclideanSpace ℝ (Fin k))) :
    PurelyRectifiable k s :=
  PurelyRectifiable.of_lipschitzWith (A := s) LipschitzWith.id (by simp)

/-- Every subset of `EuclideanSpace ℝ (Fin k)` is countably `k`-rectifiable. -/
theorem countablyRectifiable_subset_euclideanSpace (k : ℕ) (s : Set (EuclideanSpace ℝ (Fin k))) :
    CountablyRectifiable k s :=
  (purelyRectifiable_subset_euclideanSpace k s).countablyRectifiable

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous linear maps between real normed spaces preserve pure `k`-rectifiability. -/
theorem _root_.ContinuousLinearMap.purelyRectifiable_image (L : E →L[ℝ] F) {k : ℕ} {s : Set E}
    (hs : PurelyRectifiable k s) :
    PurelyRectifiable k (L '' s) :=
  hs.image_lipschitzWith L.lipschitzWith

/-- Linear isometries between real normed spaces preserve pure `k`-rectifiability. -/
@[simp]
theorem _root_.LinearIsometry.purelyRectifiable_image_iff (L : E →ₗᵢ[ℝ] F) {k : ℕ} {s : Set E} :
    PurelyRectifiable k (L '' s) ↔ PurelyRectifiable k s :=
  L.isometry.purelyRectifiable_image_iff

/-- Linear isometry equivalences between real normed spaces preserve pure `k`-rectifiability. -/
@[simp]
theorem _root_.LinearIsometryEquiv.purelyRectifiable_image_iff (L : E ≃ₗᵢ[ℝ] F) {k : ℕ}
    {s : Set E} :
    PurelyRectifiable k (L '' s) ↔ PurelyRectifiable k s :=
  L.toIsometryEquiv.purelyRectifiable_image_iff

/-- In a finite-dimensional real normed space `E` with `Module.finrank ℝ E ≤ k`, there exists a
surjective continuous linear map `EuclideanSpace ℝ (Fin k) →L[ℝ] E`. -/
theorem exists_surjective_continuousLinearMap_of_finrank_le [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E ≤ k) :
    ∃ L : EuclideanSpace ℝ (Fin k) →L[ℝ] E, Function.Surjective L := by
  classical
  let n := Module.finrank ℝ E
  let b : Module.Basis (Fin n) ℝ E := Module.finBasis ℝ E
  let e : Module.Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)) :=
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let f : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E :=
    e.constr ℝ fun j : Fin k ↦ if hj : (j : ℕ) < n then b ⟨j, hj⟩ else 0
  have hf_apply (i : Fin n) : f (e (Fin.castLE hk i)) = b i := by
    simp only [f, Module.Basis.constr_basis, Fin.val_castLE,
      dite_eq_left_of_eq_true (eq_true i.isLt), Fin.eta]
  refine ⟨f.toContinuousLinearMap, fun x ↦ ?_⟩
  refine ⟨∑ i : Fin n, b.repr x i • e (Fin.castLE hk i), ?_⟩
  change f (∑ i : Fin n, b.repr x i • e (Fin.castLE hk i)) = x
  rw [_root_.map_sum]
  simp_rw [map_smul, hf_apply]
  exact b.sum_repr x

/-- Every subset of a finite-dimensional real normed space `E` with `Module.finrank ℝ E ≤ k` is
purely `k`-rectifiable. -/
theorem purelyRectifiable_of_finrank_le [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E ≤ k) (s : Set E) :
    PurelyRectifiable k s := by
  obtain ⟨L, hL⟩ := exists_surjective_continuousLinearMap_of_finrank_le hk
  have hs : s = L '' (L ⁻¹' s) := (hL.image_preimage s).symm
  rw [hs]
  exact L.purelyRectifiable_image (purelyRectifiable_subset_euclideanSpace k (L ⁻¹' s))

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Every subset of a finite-dimensional real normed space `E` with `Module.finrank ℝ E ≤ k` is
countably `k`-rectifiable. -/
theorem countablyRectifiable_of_finrank_le [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E ≤ k) (s : Set E) :
    CountablyRectifiable k s :=
  (purelyRectifiable_of_finrank_le hk s).countablyRectifiable

/-- Continuous linear maps between Borel real normed spaces preserve countable
`k`-rectifiability. -/
theorem _root_.ContinuousLinearMap.countablyRectifiable_image (L : E →L[ℝ] F) {k : ℕ} {s : Set E}
    (hs : CountablyRectifiable k s) :
    CountablyRectifiable k (L '' s) :=
  hs.image_lipschitzWith L.lipschitzWith

/-- Linear isometries between Borel real normed spaces preserve countable `k`-rectifiability. -/
@[simp]
theorem _root_.LinearIsometry.countablyRectifiable_image_iff (L : E →ₗᵢ[ℝ] F) {k : ℕ}
    {s : Set E} :
    CountablyRectifiable k (L '' s) ↔ CountablyRectifiable k s :=
  L.isometry.countablyRectifiable_image_iff

/-- Linear isometry equivalences between Borel real normed spaces preserve countable
`k`-rectifiability. -/
@[simp]
theorem _root_.LinearIsometryEquiv.countablyRectifiable_image_iff (L : E ≃ₗᵢ[ℝ] F) {k : ℕ}
    {s : Set E} :
    CountablyRectifiable k (L '' s) ↔ CountablyRectifiable k s :=
  L.toIsometryEquiv.countablyRectifiable_image_iff

end NormedSpaces

/-!
### Vanishing of higher Hausdorff measures and `σ`-finiteness of restricted Hausdorff measure
-/

section HausdorffMeasureProperties

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Any bounded subset of `EuclideanSpace ℝ (Fin k)` has finite `k`-dimensional Hausdorff measure
`μH[k]`. -/
theorem hausdorffMeasure_lt_top_of_isBounded {k : ℕ} {A : Set (EuclideanSpace ℝ (Fin k))}
    (hA : Bornology.IsBounded A) :
    μH[k] A < ⊤ := by
  rcases hA.subset_closedBall 0 with ⟨r, hr⟩
  exact lt_of_le_of_lt (measure_mono hr) measure_closedBall_lt_top

/-- The image of a bounded subset `A ⊆ EuclideanSpace ℝ (Fin k)` under a `LipschitzOnWith` map has
finite `k`-dimensional Hausdorff measure `μH[k]`. -/
theorem _root_.LipschitzOnWith.hausdorffMeasure_image_lt_top {k : ℕ} {K : ℝ≥0}
    {A : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → X}
    (hf : LipschitzOnWith K f A) (hA : Bornology.IsBounded A) :
    μH[k] (f '' A) < ⊤ := by
  refine lt_of_le_of_lt (hf.hausdorffMeasure_image_le (Nat.cast_nonneg k)) ?_
  exact ENNReal.mul_lt_top (by simp) (hausdorffMeasure_lt_top_of_isBounded hA)

/-- The image of a bounded subset `A ⊆ EuclideanSpace ℝ (Fin k)` under a `LipschitzOnWith` map has
finite normalized Euclidean Hausdorff measure `μHE[k]`. -/
theorem _root_.LipschitzOnWith.euclideanHausdorffMeasure_image_lt_top {k : ℕ} {K : ℝ≥0}
    {A : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → X}
    (hf : LipschitzOnWith K f A) (hA : Bornology.IsBounded A) :
    μHE[k] (f '' A) < ⊤ :=
  (euclideanHausdorffMeasure_lt_top_iff k _).mpr (hf.hausdorffMeasure_image_lt_top hA)

/-- For any purely `k`-rectifiable set `s` and any `d > k`, the `d`-dimensional Hausdorff measure
`μH[d] s` vanishes. -/
theorem PurelyRectifiable.hausdorffMeasure_eq_zero_of_lt {k : ℕ} {d : ℝ} {s : Set X}
    (hs : PurelyRectifiable k s) (hkd : (k : ℝ) < d) :
    μH[d] s = 0 := by
  rcases purelyRectifiable_iff_bounded.mp hs with ⟨K, A, f, hbdd, hf, hsub⟩
  refine measure_mono_null hsub (measure_iUnion_null fun i ↦ ?_)
  have hlt : μH[k] (f i '' A i) < ⊤ := (hf i).hausdorffMeasure_image_lt_top (hbdd i)
  rcases hausdorffMeasure_zero_or_top hkd (f i '' A i) with h0 | htop
  · exact h0
  · exact absurd htop hlt.ne

/-- For any purely `k`-rectifiable set `s` and any integer dimension `m > k`, the normalized
Euclidean Hausdorff measure `μHE[m] s` vanishes. -/
theorem PurelyRectifiable.euclideanHausdorffMeasure_eq_zero_of_lt {k m : ℕ} {s : Set X}
    (hs : PurelyRectifiable k s) (hkm : k < m) :
    μHE[m] s = 0 := by
  rw [euclideanHausdorffMeasure_eq_zero_iff]
  exact hs.hausdorffMeasure_eq_zero_of_lt (Nat.cast_lt.mpr hkm)

/-- If a set `s` is covered by a countable family of sets `E n` each of finite `μ`-measure, then
`μ.restrict s` is `σ`-finite. -/
theorem sigmaFinite_restrict_of_subset_iUnion_lt_top {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {s : Set α} {E : ℕ → Set α} (hs : s ⊆ ⋃ n, E n) (hE : ∀ n, μ (E n) < ⊤) :
    SigmaFinite (μ.restrict s) := by
  let T : ℕ → Set α := fun n ↦ toMeasurable μ (E n)
  let U : Set α := ⋃ n, T n
  have hU_meas : MeasurableSet U := MeasurableSet.iUnion fun n ↦ measurableSet_toMeasurable μ (E n)
  have hsU : s ⊆ U := hs.trans (iUnion_mono fun n ↦ subset_toMeasurable μ (E n))
  refine ⟨⟨{
    set := fun n ↦ T n ∪ Uᶜ
    set_mem := fun _ ↦ mem_univ _
    finite := fun n ↦ by
      have hM : MeasurableSet (T n ∪ Uᶜ) :=
        (measurableSet_toMeasurable μ (E n)).union hU_meas.compl
      rw [Measure.restrict_apply hM]
      have hsub : (T n ∪ Uᶜ) ∩ s ⊆ T n := by
        rintro x ⟨hxT | hxU, hxs⟩
        · exact hxT
        · exact False.elim (hxU (hsU hxs))
      exact lt_of_le_of_lt (measure_mono hsub)
        (by rw [measure_toMeasurable]; exact hE n)
    spanning := by
      ext x
      simp only [mem_iUnion, mem_union, mem_compl_iff, mem_univ, iff_true]
      by_cases hx : x ∈ U
      · rcases mem_iUnion.mp hx with ⟨n, hn⟩
        exact ⟨n, Or.inl hn⟩
      · exact ⟨0, Or.inr hx⟩
  }⟩⟩

/-- For any countably `k`-rectifiable set `s`, the restricted Hausdorff measure `μH[k].restrict s`
is `σ`-finite. -/
theorem CountablyRectifiable.sigmaFinite_restrict_hausdorffMeasure {k : ℕ} {s : Set X}
    (hs : CountablyRectifiable k s) :
    SigmaFinite ((μH[k] : Measure X).restrict s) := by
  rcases countablyRectifiable_iff_bounded.mp hs with ⟨K, A, f, hbdd, hf, hnull⟩
  let E : ℕ → Set X := fun n ↦ Nat.casesOn n (s \ ⋃ i, f i '' A i) (fun i ↦ f i '' A i)
  have hsE : s ⊆ ⋃ n, E n := by
    intro x hxs
    by_cases hx : x ∈ ⋃ i, f i '' A i
    · rcases mem_iUnion.mp hx with ⟨i, hi⟩
      exact mem_iUnion.mpr ⟨i + 1, hi⟩
    · exact mem_iUnion.mpr ⟨0, hxs, hx⟩
  have hE : ∀ n, μH[k] (E n) < ⊤ := by
    rintro (_ | i)
    · simp [E, hnull]
    · exact (hf i).hausdorffMeasure_image_lt_top (hbdd i)
  exact sigmaFinite_restrict_of_subset_iUnion_lt_top μH[k] hsE hE

/-- For any countably `k`-rectifiable set `s`, the restricted normalized Euclidean Hausdorff
measure `μHE[k].restrict s` is `σ`-finite. -/
theorem CountablyRectifiable.sigmaFinite_restrict_euclideanHausdorffMeasure {k : ℕ} {s : Set X}
    (hs : CountablyRectifiable k s) :
    SigmaFinite ((μHE[k] : Measure X).restrict s) := by
  have : SigmaFinite ((μH[k] : Measure X).restrict s) := hs.sigmaFinite_restrict_hausdorffMeasure
  rw [Measure.euclideanHausdorffMeasure_def, Measure.restrict_smul]
  infer_instance

end HausdorffMeasureProperties

end TauCeti.MeasureTheory
