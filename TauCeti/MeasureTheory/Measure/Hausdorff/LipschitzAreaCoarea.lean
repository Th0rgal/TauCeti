/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Hausdorff.CurveMultiplicity
import all TauCeti.MeasureTheory.Measure.Hausdorff.CurveMultiplicity
import all TauCeti.MeasureTheory.Measure.Hausdorff.CurveTrace
import all TauCeti.MeasureTheory.Measure.Hausdorff.Rectifiable

/-!
# Extended Fiber Multiplicity, Weighted Fiber Sums, Area & Coarea Formulas, and Isometric Transport

This file develops the extended nonnegative fiber multiplicity and weighted fiber sum calculus,
the general area and coarea formulas with countable rectifiable decomposition, injective
specialization, isometric and similarity Hausdorff measure transport, real Bochner-integral area
identities, and coordinate-projection Tonelli/Fubini coarea slicing:

1. **Extended fiber multiplicity `fiberMultiplicity` and weighted fiber sums `weightedFiberSum`**:
   `TauCeti.weightedFiberSum_one`, `TauCeti.fiberMultiplicity_eq_zero_iff_inter_eq_empty`,
   `TauCeti.fiberMultiplicity_eq_zero_of_notMem_image`,
   `TauCeti.fiberMultiplicity_eq_top_of_infinite`, `TauCeti.fiberMultiplicity_eq_encard`,
   `TauCeti.fiberMultiplicity_eq_tsum`, `TauCeti.weightedFiberSum_eq_zero_of_notMem_image`,
   `TauCeti.weightedFiberSum_apply_of_injective`,
   `TauCeti.fiberMultiplicity_eq_indicator_image_of_injOn`, `TauCeti.weightedFiberSum_mono_weight`,
   `TauCeti.weightedFiberSum_add`, `TauCeti.weightedFiberSum_mul_left`,
   `TauCeti.weightedFiberSum_mul_right`, `TauCeti.weightedFiberSum_Union_disjoint`, and
   `TauCeti.fiberMultiplicity_Union_disjoint`.
2. **Area formula, countable rectifiable decomposition, isometric/dilation transport, and real
   integrable area formula**:
   `TauCeti.AreaFormulaHolds`, `TauCeti.AreaFormulaHolds.lintegral_jacobian`,
   `TauCeti.AreaFormulaHolds.lintegral_jacobian_eq_measure_image_of_injOn`,
   `TauCeti.AreaFormulaHolds.measure_image_eq_zero_of_jacobian_eq_zero`,
   `TauCeti.AreaFormulaHolds.restrict_subset`, `TauCeti.AreaFormulaHolds.iUnion_disjoint`,
   `Isometry.areaFormulaHolds_hausdorffMeasure`, `IsometryEquiv.areaFormulaHolds_hausdorffMeasure`,
   `TauCeti.hausdorffMeasure_smul_of_ne_zero`, and `TauCeti.AreaFormulaHolds.integral_mul_toReal`.
3. **Coarea formula, fiber slice integrals, and product/projection coarea slicing**:
   `TauCeti.coareaFiberIntegral`, `TauCeti.coareaFiberMeasure`, `TauCeti.CoareaFormulaHolds`,
   `TauCeti.coareaFiberIntegral_one`, `TauCeti.CoareaFormulaHolds.lintegral_jacobian`,
   `TauCeti.CoareaFormulaHolds.ae_fiber_measure_eq_zero_of_jacobian_eq_zero`,
   `TauCeti.CoareaFormulaHolds.restrict_subset`, `TauCeti.CoareaFormulaHolds.iUnion_disjoint`,
   `TauCeti.setLIntegral_prod_fst_slice`, `TauCeti.measure_prod_eq_lintegral_fst_slice`,
   `TauCeti.measure_prod_eq_lintegral_snd_slice`, and `TauCeti.setIntegral_prod_fst_slice`.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set
open scoped ENNReal NNReal Topology
open TauCeti.MeasureTheory

namespace TauCeti

export TauCeti.MeasureTheory (weightedFiberSum_empty weightedFiberSum_zero
  weightedFiberSum_of_notMem_image weightedFiberSum_mono_set weightedFiberSum_mono_fn
  weightedFiberSum_eq_lintegral_hausdorffMeasure_zero
  weightedFiberSum_eq_lintegral_euclideanHausdorffMeasure_zero
  weightedFiberSum_one_eq_fiberMultiplicity weightedFiberSum_const weightedFiberSum_eq_tsum
  weightedFiberSum_eq_tsum_of_measurable weightedFiberSum_eq_tsum_of_countable
  weightedFiberSum_apply_of_injOn weightedFiberSum_of_injOn)

/-! ### Section 1: Extended fiber multiplicity and weighted fiber sums -/

section FiberMultiplicityAndSums

variable {X Y : Type*}

/-- `fiberMultiplicity f A y` is the extended cardinality `(A ∩ f ⁻¹' {y}).encard`. -/
theorem fiberMultiplicity_eq_encard (f : X → Y) (A : Set X) (y : Y) :
    fiberMultiplicity f A y = (A ∩ f ⁻¹' {y}).encard := rfl

/-- `fiberMultiplicity f A y = 0` if and only if the fiber `A ∩ f ⁻¹' {y}` is empty. -/
theorem fiberMultiplicity_eq_zero_iff_inter_eq_empty {f : X → Y} {A : Set X} {y : Y} :
    fiberMultiplicity f A y = 0 ↔ A ∩ f ⁻¹' {y} = ∅ := by
  rw [fiberMultiplicity, ENat.toENNReal_eq_zero, encard_eq_zero]

/-- If `y ∉ f '' A`, then `fiberMultiplicity f A y = 0`. -/
theorem fiberMultiplicity_eq_zero_of_notMem_image {f : X → Y} {A : Set X} {y : Y}
    (hy : y ∉ f '' A) : fiberMultiplicity f A y = 0 :=
  fiberMultiplicity_of_notMem_image hy

/-- On any infinite fiber `(A ∩ f ⁻¹' {y}).Infinite`, `fiberMultiplicity f A y = ⊤`. -/
theorem fiberMultiplicity_eq_top_of_infinite {f : X → Y} {A : Set X} {y : Y}
    (hinf : (A ∩ f ⁻¹' {y}).Infinite) : fiberMultiplicity f A y = ⊤ := by
  rw [fiberMultiplicity, hinf.encard_eq, ENat.toENNReal_top]

/-- `fiberMultiplicity f A y = ⊤` if and only if the fiber `A ∩ f ⁻¹' {y}` is infinite. -/
@[simp] theorem fiberMultiplicity_eq_top_iff {f : X → Y} {A : Set X} {y : Y} :
    fiberMultiplicity f A y = ⊤ ↔ (A ∩ f ⁻¹' {y}).Infinite := by
  rw [fiberMultiplicity, ENat.toENNReal_eq_top, encard_eq_top_iff]

/-- `fiberMultiplicity f A y < ⊤` if and only if the fiber `A ∩ f ⁻¹' {y}` is finite. -/
@[simp] theorem fiberMultiplicity_lt_top_iff {f : X → Y} {A : Set X} {y : Y} :
    fiberMultiplicity f A y < ⊤ ↔ (A ∩ f ⁻¹' {y}).Finite := by
  rw [lt_top_iff_ne_top, Ne, fiberMultiplicity_eq_top_iff, Set.not_infinite]

/-- `fiberMultiplicity f A y` is always `≥ 1` on `f '' A`. -/
theorem one_le_fiberMultiplicity_of_mem_image {f : X → Y} {A : Set X} {y : Y} (hy : y ∈ f '' A) :
    1 ≤ fiberMultiplicity f A y := by
  rcases hy with ⟨x, hxA, rfl⟩
  rw [fiberMultiplicity, ← ENat.toENNReal_one, ENat.toENNReal_le, one_le_encard_iff_nonempty]
  exact ⟨x, hxA, rfl⟩

/-- Indicator lower bound `(f '' A).indicator 1 y ≤ fiberMultiplicity f A y`. -/
theorem indicator_image_one_le_fiberMultiplicity (f : X → Y) (A : Set X) (y : Y) :
    (f '' A).indicator 1 y ≤ fiberMultiplicity f A y := by
  by_cases hy : y ∈ f '' A
  · rw [indicator_of_mem hy, Pi.one_apply]
    exact one_le_fiberMultiplicity_of_mem_image hy
  · rw [indicator_of_notMem hy]
    exact zero_le

/-- Characterization of `fiberMultiplicity f A y` as `∑' _ : ↑(A ∩ f ⁻¹' {y}), 1`. -/
theorem fiberMultiplicity_eq_tsum (f : X → Y) (A : Set X) (y : Y) :
    fiberMultiplicity f A y = ∑' _ : ↑(A ∩ f ⁻¹' {y}), (1 : ℝ≥0∞) := by
  let _ : MeasurableSpace X := ⊤
  have : MeasurableSingletonClass X := ⟨fun _ ↦ trivial⟩
  have : DiscreteMeasurableSpace X := ⟨fun _ ↦ trivial⟩
  rw [fiberMultiplicity_eq_count, ← setLIntegral_one,
    setLIntegral_count_of_measurableSet _ MeasurableSet.of_discrete]

/-- When `Set.InjOn f A`, `fiberMultiplicity f A y = (f '' A).indicator 1 y`. -/
theorem fiberMultiplicity_eq_indicator_image_of_injOn {f : X → Y} {A : Set X}
    (hf : Set.InjOn f A) (y : Y) :
    fiberMultiplicity f A y = (f '' A).indicator 1 y :=
  fiberMultiplicity_eq_indicator_of_injOn hf y

/-- Countable additivity of `fiberMultiplicity` across pairwise disjoint sets `A : ι → Set X`. -/
theorem fiberMultiplicity_Union_disjoint {ι : Type*} [Countable ι] (f : X → Y)
    {A : ι → Set X} (hdisj : Pairwise (Disjoint on A)) (y : Y) :
    fiberMultiplicity f (⋃ i, A i) y = ∑' i, fiberMultiplicity f (A i) y := by
  let _ : MeasurableSpace X := ⊤
  have : MeasurableSingletonClass X := ⟨fun _ ↦ trivial⟩
  have : DiscreteMeasurableSpace X := ⟨fun _ ↦ trivial⟩
  simp_rw [fiberMultiplicity_eq_count, iUnion_inter]
  exact measure_iUnion (hdisj.mono fun i j h ↦ h.mono inter_subset_left inter_subset_left)
    fun _ ↦ MeasurableSet.of_discrete

variable [MeasurableSpace X]

/-- Unit-weight specialization `weightedFiberSum f A (fun _ ↦ 1) y = fiberMultiplicity f A y`. -/
theorem weightedFiberSum_one [MeasurableSingletonClass X] (f : X → Y) (A : Set X) (y : Y) :
    weightedFiberSum f A (fun _ ↦ 1) y = fiberMultiplicity f A y :=
  weightedFiberSum_one_eq_fiberMultiplicity f A y

/-- If `y ∉ f '' A`, then `weightedFiberSum f A g y = 0`. -/
theorem weightedFiberSum_eq_zero_of_notMem_image {f : X → Y} {A : Set X} (g : X → ℝ≥0∞) {y : Y}
    (hy : y ∉ f '' A) : weightedFiberSum f A g y = 0 :=
  weightedFiberSum_of_notMem_image g hy

/-- Monotonicity of `weightedFiberSum` in the weight function `g`. -/
theorem weightedFiberSum_mono_weight {f : X → Y} (A : Set X) {g₁ g₂ : X → ℝ≥0∞} (hg : g₁ ≤ g₂)
    (y : Y) : weightedFiberSum f A g₁ y ≤ weightedFiberSum f A g₂ y :=
  weightedFiberSum_mono_fn A hg y

/-- Additivity of `weightedFiberSum` in the weight function. -/
theorem weightedFiberSum_add (f : X → Y) (A : Set X) {g₁ g₂ : X → ℝ≥0∞} (hg₁ : Measurable g₁)
    (y : Y) :
    weightedFiberSum f A (fun x ↦ g₁ x + g₂ x) y =
      weightedFiberSum f A g₁ y + weightedFiberSum f A g₂ y :=
  lintegral_add_left hg₁ g₂

/-- Left scalar multiplication for `weightedFiberSum`. -/
theorem weightedFiberSum_mul_left (f : X → Y) (A : Set X) (c : ℝ≥0∞) {g : X → ℝ≥0∞}
    (hg : Measurable g) (y : Y) :
    weightedFiberSum f A (fun x ↦ c * g x) y = c * weightedFiberSum f A g y :=
  lintegral_const_mul c hg

/-- Right scalar multiplication for `weightedFiberSum`. -/
theorem weightedFiberSum_mul_right (f : X → Y) (A : Set X) {g : X → ℝ≥0∞} (hg : Measurable g)
    (c : ℝ≥0∞) (y : Y) :
    weightedFiberSum f A (fun x ↦ g x * c) y = weightedFiberSum f A g y * c := by
  simp_rw [mul_comm _ c]
  exact weightedFiberSum_mul_left f A c hg y

/-- Indicator restriction law for `weightedFiberSum`: replacing `g` by `B.indicator g` restricts
the domain set `A` to `A ∩ B`. -/
theorem weightedFiberSum_indicator (f : X → Y) (A : Set X) {B : Set X} (hB : MeasurableSet B)
    (g : X → ℝ≥0∞) (y : Y) :
    weightedFiberSum f A (B.indicator g) y = weightedFiberSum f (A ∩ B) g y := by
  rw [weightedFiberSum, weightedFiberSum, lintegral_indicator hB,
    Measure.restrict_restrict hB, ← inter_assoc, inter_comm B A]

/-- For a globally injective map `f : X → Y`, `weightedFiberSum f A g (f x) = A.indicator g x`. -/
theorem weightedFiberSum_apply_of_injective [MeasurableSingletonClass X] {f : X → Y}
    (hf : Function.Injective f) (A : Set X) (g : X → ℝ≥0∞) (x : X) :
    weightedFiberSum f A g (f x) = A.indicator g x := by
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx, weightedFiberSum_apply_of_injOn hf.injOn g hx]
  · have hfx : f x ∉ f '' A := by simpa [hf.mem_set_image] using hx
    rw [indicator_of_notMem hx, weightedFiberSum_of_notMem_image g hfx]

/-- Countable additivity of `weightedFiberSum` across pairwise disjoint measurable sets `A i`. -/
theorem weightedFiberSum_Union_disjoint {ι : Type*} [Countable ι] (f : X → Y)
    {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (g : X → ℝ≥0∞) (y : Y) :
    weightedFiberSum f (⋃ i, A i) g y = ∑' i, weightedFiberSum f (A i) g y := by
  have hrestrict (s : Set X) (hs : MeasurableSet s) :
      weightedFiberSum f s g y =
        ∫⁻ x in s, g x ∂(Measure.count.restrict (f ⁻¹' {y})) := by
    rw [weightedFiberSum, Measure.restrict_restrict hs]
  rw [hrestrict (⋃ i, A i) (MeasurableSet.iUnion hA), lintegral_iUnion hA hdisj]
  exact tsum_congr fun i ↦ (hrestrict (A i) (hA i)).symm

end FiberMultiplicityAndSums

/-! ### Section 2: Area formula, countable rectifiable decomposition, and isometric transport -/

section AreaFormulaAndTransport

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Predicate asserting that the area formula holds for `f : X → Y` on `A : Set X` with Jacobian
factor `J : X → ℝ≥0∞` with respect to `(μX, μY)`:
`∫⁻ x in A, g x * J x ∂μX = ∫⁻ y, weightedFiberSum f A g y ∂μY` for all measurable `g`. -/
def AreaFormulaHolds (μX : Measure X) (μY : Measure Y) (f : X → Y) (J : X → ℝ≥0∞)
    (A : Set X) : Prop :=
  ∀ ⦃g : X → ℝ≥0∞⦄, Measurable g →
    ∫⁻ x in A, g x * J x ∂μX = ∫⁻ y, weightedFiberSum f A g y ∂μY

namespace AreaFormulaHolds

/-- The area formula holds trivially on the empty set `∅`. -/
theorem empty (μX : Measure X) (μY : Measure Y) (f : X → Y) (J : X → ℝ≥0∞) :
    AreaFormulaHolds μX μY f J ∅ := by
  intro g _
  simp [weightedFiberSum_empty]

/-- Unweighted multiplicity specialization of `AreaFormulaHolds` (`g = 1`):
`∫⁻ x in A, J x ∂μX = ∫⁻ y, fiberMultiplicity f A y ∂μY`. -/
theorem lintegral_jacobian [MeasurableSingletonClass X]
    {μX : Measure X} {μY : Measure Y} {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : AreaFormulaHolds μX μY f J A) :
    ∫⁻ x in A, J x ∂μX = ∫⁻ y, fiberMultiplicity f A y ∂μY := by
  simpa [one_mul, weightedFiberSum_one] using h (g := fun _ ↦ 1) measurable_const

/-- Injective specialization of `AreaFormulaHolds`: when `Set.InjOn f A` and `f '' A` is
measurable, `∫⁻ x in A, J x ∂μX = μY (f '' A)`. -/
theorem lintegral_jacobian_eq_measure_image_of_injOn [MeasurableSingletonClass X]
    {μX : Measure X} {μY : Measure Y} {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : AreaFormulaHolds μX μY f J A) (hinj : Set.InjOn f A) (himg : MeasurableSet (f '' A)) :
    ∫⁻ x in A, J x ∂μX = μY (f '' A) := by
  rw [h.lintegral_jacobian]
  simp_rw [fiberMultiplicity_eq_indicator_of_injOn hinj]
  exact lintegral_indicator_one himg

/-- For any measurable image `f '' A`, `μY (f '' A) ≤ ∫⁻ x in A, J x ∂μX`. -/
theorem measure_image_le_lintegral_jacobian [MeasurableSingletonClass X]
    {μX : Measure X} {μY : Measure Y} {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : AreaFormulaHolds μX μY f J A) (himg : MeasurableSet (f '' A)) :
    μY (f '' A) ≤ ∫⁻ x in A, J x ∂μX := by
  rw [h.lintegral_jacobian, ← lintegral_indicator_one himg]
  exact lintegral_mono (indicator_image_one_le_fiberMultiplicity f A)

/-- Critical-set vanishing for `fiberMultiplicity`: if `J x = 0` on a measurable set `A`, then
`∫⁻ y, fiberMultiplicity f A y ∂μY = 0`. -/
theorem lintegral_fiberMultiplicity_eq_zero_of_jacobian_eq_zero [MeasurableSingletonClass X]
    {μX : Measure X} {μY : Measure Y} {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : AreaFormulaHolds μX μY f J A) (hA : MeasurableSet A) (hJ : ∀ x ∈ A, J x = 0) :
    ∫⁻ y, fiberMultiplicity f A y ∂μY = 0 := by
  rw [← h.lintegral_jacobian, setLIntegral_congr_fun hA hJ, lintegral_zero]

/-- Critical-set image vanishing: if `J x = 0` for all `x ∈ A` (`A` and `f '' A` measurable), then
`μY (f '' A) = 0`. -/
theorem measure_image_eq_zero_of_jacobian_eq_zero [MeasurableSingletonClass X]
    {μX : Measure X} {μY : Measure Y} {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : AreaFormulaHolds μX μY f J A) (hA : MeasurableSet A) (hJ : ∀ x ∈ A, J x = 0)
    (himg : MeasurableSet (f '' A)) :
    μY (f '' A) = 0 :=
  nonpos_iff_eq_zero.mp ((h.measure_image_le_lintegral_jacobian himg).trans_eq
    (by rw [h.lintegral_jacobian, h.lintegral_fiberMultiplicity_eq_zero_of_jacobian_eq_zero hA hJ]))

/-- Restriction of `AreaFormulaHolds` to any measurable subset `B ⊆ A`. -/
theorem restrict_subset {μX : Measure X} {μY : Measure Y} {f : X → Y} {J : X → ℝ≥0∞}
    {A B : Set X} (h : AreaFormulaHolds μX μY f J A) (hB : MeasurableSet B) (hBA : B ⊆ A) :
    AreaFormulaHolds μX μY f J B := by
  intro g hg
  have h1 := h (hg.indicator hB)
  have hLHS : ∫⁻ x in A, B.indicator g x * J x ∂μX = ∫⁻ x in B, g x * J x ∂μX := by
    have hmul : (fun x ↦ B.indicator g x * J x) = B.indicator (fun x ↦ g x * J x) := by
      ext x; by_cases hx : x ∈ B <;> simp [hx]
    rw [hmul, lintegral_indicator hB, Measure.restrict_restrict hB,
      inter_eq_self_of_subset_left hBA]
  have hRHS : (fun y ↦ weightedFiberSum f A (B.indicator g) y) = weightedFiberSum f B g := by
    ext y
    rw [weightedFiberSum_indicator f A hB g y, inter_eq_self_of_subset_right hBA]
  rwa [hLHS, hRHS] at h1

/-- Countable rectifiable decomposition for `AreaFormulaHolds`: if `A : ι → Set X` are pairwise
disjoint measurable sets on each of which `AreaFormulaHolds` holds, and the fiber sums are
`μY`-a.e. measurable, then `AreaFormulaHolds` holds on `⋃ i, A i`. -/
theorem iUnion_disjoint {ι : Type*} [Countable ι] {μX : Measure X} {μY : Measure Y}
    {f : X → Y} {J : X → ℝ≥0∞} {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (h : ∀ i, AreaFormulaHolds μX μY f J (A i))
    (hmeas : ∀ i ⦃g : X → ℝ≥0∞⦄, Measurable g → AEMeasurable (weightedFiberSum f (A i) g) μY) :
    AreaFormulaHolds μX μY f J (⋃ i, A i) := by
  intro g hg
  rw [lintegral_iUnion hA hdisj]
  simp_rw [h _ hg, weightedFiberSum_Union_disjoint f hA hdisj g]
  exact (lintegral_tsum fun i ↦ hmeas i hg).symm

/-- **Real Bochner-integral area formula**: when `AreaFormulaHolds μX μY f J A` holds on a
measurable set `A`, any nonnegative measurable function `g : X → ℝ` with integrable
`x ↦ g x * (J x).toReal` on `A` and integrable fiber sum satisfies
`∫ x in A, g x * (J x).toReal ∂μX = ∫ y, (∑' x : ↑(A ∩ f ⁻¹' {y}), g x) ∂μY`. -/
theorem integral_mul_toReal [MeasurableSingletonClass X]
    {μX : Measure X} {μY : Measure Y} {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : AreaFormulaHolds μX μY f J A) (hA : MeasurableSet A) {g : X → ℝ} (hg_meas : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x) (hJ_top : ∀ x ∈ A, J x ≠ ⊤)
    (hfiber_meas : ∀ y, MeasurableSet (A ∩ f ⁻¹' {y}))
    (hfiber_sum : ∀ y, Summable (fun x : ↑(A ∩ f ⁻¹' {y}) ↦ g x))
    (hintL : IntegrableOn (fun x ↦ g x * (J x).toReal) A μX)
    (hintR : Integrable (fun y ↦ ∑' x : ↑(A ∩ f ⁻¹' {y}), g x) μY) :
    ∫ x in A, g x * (J x).toReal ∂μX = ∫ y, (∑' x : ↑(A ∩ f ⁻¹' {y}), g x) ∂μY := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x ↦ mul_nonneg (hg_nonneg x) ENNReal.toReal_nonneg)
      hintL.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y ↦ tsum_nonneg fun x : ↑(A ∩ f ⁻¹' {y}) ↦ hg_nonneg x)
      hintR.aestronglyMeasurable]
  congr 1
  have hLHS : (∫⁻ x in A, ENNReal.ofReal (g x * (J x).toReal) ∂μX) =
      ∫⁻ x in A, ENNReal.ofReal (g x) * J x ∂μX := by
    refine setLIntegral_congr_fun hA fun x hx ↦ ?_
    rw [ENNReal.ofReal_mul (hg_nonneg x), ENNReal.ofReal_toReal (hJ_top x hx)]
  rw [hLHS, h hg_meas.ennreal_ofReal]
  refine lintegral_congr fun y ↦ ?_
  rw [weightedFiberSum_eq_tsum f _ (hfiber_meas y),
    (ENNReal.ofReal_tsum_of_nonneg (fun x : ↑(A ∩ f ⁻¹' {y}) ↦ hg_nonneg x) (hfiber_sum y)).symm]

/-- Congruence of `AreaFormulaHolds` when two Jacobians coincide on the measurable set `A`. -/
theorem congr_jacobian {μX : Measure X} {μY : Measure Y} {f : X → Y} {J₁ J₂ : X → ℝ≥0∞}
    {A : Set X} (h : AreaFormulaHolds μX μY f J₁ A) (hA : MeasurableSet A)
    (hJ : ∀ x ∈ A, J₁ x = J₂ x) :
    AreaFormulaHolds μX μY f J₂ A := by
  intro g hg
  rw [← h hg]
  exact setLIntegral_congr_fun hA fun x hx ↦ by rw [hJ x hx]

/-- Simultaneous scalar scaling of `(μX, μY)` preserves `AreaFormulaHolds`. -/
theorem smul_measure {μX : Measure X} {μY : Measure Y} {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : AreaFormulaHolds μX μY f J A) (c : ℝ≥0∞) :
    AreaFormulaHolds (c • μX) (c • μY) f J A := by
  intro g hg
  rw [Measure.restrict_smul, lintegral_smul_measure, lintegral_smul_measure, h hg]

/-- Scaling a measurable Jacobian by `c` scales the target measure by `c` in `AreaFormulaHolds`. -/
theorem smul_jacobian {μX : Measure X} {μY : Measure Y} {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : AreaFormulaHolds μX μY f J A) (hJ : Measurable J) (c : ℝ≥0∞) :
    AreaFormulaHolds μX (c • μY) f (fun x ↦ c * J x) A := by
  intro g hg
  have hmul : (fun x ↦ g x * (c * J x)) = fun x ↦ c * (g * J) x := by
    ext x; exact mul_left_comm (g x) c (J x)
  rw [hmul, lintegral_const_mul c (hg.mul hJ), lintegral_smul_measure, smul_eq_mul, ← h hg]
  rfl

end AreaFormulaHolds

/-- General area formula for any measurable embedding `f : X → Y` that scales `μX` to `μY` by a
constant factor `c : ℝ≥0∞` on measurable sets (`∀ s, MeasurableSet s → μY (f '' s) = c * μX s`). -/
theorem _root_.MeasurableEmbedding.areaFormulaHolds_of_measure_image_eq [MeasurableSingletonClass X]
    {μX : Measure X} {μY : Measure Y} {f : X → Y} (hemb : MeasurableEmbedding f)
    {c : ℝ≥0∞} (hscale : ∀ s : Set X, MeasurableSet s → μY (f '' s) = c * μX s)
    {A : Set X} (hA : MeasurableSet A) :
    AreaFormulaHolds μX μY f (fun _ ↦ c) A := by
  have hmap : Measure.map f (c • μX) = μY.restrict (range f) := by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply' hemb.measurableSet_range, ← Set.image_preimage_eq_inter_range,
      hscale _ (hemb.measurable hs)]
  intro g hg
  simp_rw [mul_comm _ c]
  rw [lintegral_const_mul c hg, ← lintegral_indicator hA]
  have hsmul : c * ∫⁻ x, A.indicator g x ∂μX = ∫⁻ x, A.indicator g x ∂(c • μX) := by
    rw [lintegral_smul_measure, smul_eq_mul]
  rw [hsmul]
  simp_rw [← weightedFiberSum_apply_of_injective hemb.injective A g]
  rw [← hemb.lintegral_map, hmap, setLIntegral_eq_of_support_subset]
  intro y hy
  by_contra hyr
  exact hy (weightedFiberSum_of_notMem_image g fun ⟨x, _, hxy⟩ ↦ hyr ⟨x, hxy⟩)

/-- For any isometry `f : X → Y` that is a measurable embedding and `0 ≤ d ∨ Surjective f`,
`AreaFormulaHolds μH[d] μH[d] f (fun _ ↦ 1) A` holds for every measurable set `A`. -/
theorem _root_.Isometry.areaFormulaHolds_hausdorffMeasure_of_measurableEmbedding
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Isometry f) (hemb : MeasurableEmbedding f)
    {d : ℝ} (hd : 0 ≤ d ∨ Function.Surjective f) {A : Set X} (hA : MeasurableSet A) :
    AreaFormulaHolds μH[d] μH[d] f (fun _ ↦ 1) A :=
  hemb.areaFormulaHolds_of_measure_image_eq
    (fun s _ ↦ by rw [one_mul, hf.hausdorffMeasure_image hd s]) hA

/-- For any isometry `f : X → Y` from a complete Borel extended metric space `X` (`0 ≤ d`),
`AreaFormulaHolds μH[d] μH[d] f (fun _ ↦ 1) A` holds for every measurable set `A`. -/
theorem _root_.Isometry.areaFormulaHolds_hausdorffMeasure
    {X Y : Type*} [EMetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Isometry f) {d : ℝ} (hd : 0 ≤ d ∨ Function.Surjective f)
    {A : Set X} (hA : MeasurableSet A) :
    AreaFormulaHolds μH[d] μH[d] f (fun _ ↦ 1) A :=
  hf.areaFormulaHolds_hausdorffMeasure_of_measurableEmbedding
    hf.isClosedEmbedding.measurableEmbedding hd hA

/-- For any isometry `f : X → Y` from a complete Borel extended metric space `X` and `k : ℕ`,
`AreaFormulaHolds μHE[k] μHE[k] f (fun _ ↦ 1) A` holds for every measurable set `A`. -/
theorem _root_.Isometry.areaFormulaHolds_euclideanHausdorffMeasure
    {X Y : Type*} [EMetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Isometry f) (k : ℕ) {A : Set X} (hA : MeasurableSet A) :
    AreaFormulaHolds μHE[k] μHE[k] f (fun _ ↦ 1) A :=
  hf.isClosedEmbedding.measurableEmbedding.areaFormulaHolds_of_measure_image_eq
    (fun s _ ↦ by
      rw [one_mul, Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def,
        Measure.smul_apply, Measure.smul_apply,
        hf.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg k)) s]) hA

/-- For any isometry equivalence `e : X ≃ᵢ Y` and `d : ℝ`,
`AreaFormulaHolds μH[d] μH[d] e (fun _ ↦ 1) A` holds for every measurable set `A`. -/
theorem _root_.IsometryEquiv.areaFormulaHolds_hausdorffMeasure
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ᵢ Y) (d : ℝ) {A : Set X} (hA : MeasurableSet A) :
    AreaFormulaHolds μH[d] μH[d] e (fun _ ↦ 1) A :=
  e.isometry.areaFormulaHolds_hausdorffMeasure_of_measurableEmbedding
    e.toHomeomorph.isClosedEmbedding.measurableEmbedding (Or.inr e.surjective) hA

/-- For any isometry equivalence `e : X ≃ᵢ Y` and `k : ℕ`,
`AreaFormulaHolds μHE[k] μHE[k] e (fun _ ↦ 1) A` holds for every measurable set `A`. -/
theorem _root_.IsometryEquiv.areaFormulaHolds_euclideanHausdorffMeasure
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ᵢ Y) (k : ℕ) {A : Set X} (hA : MeasurableSet A) :
    AreaFormulaHolds μHE[k] μHE[k] e (fun _ ↦ 1) A := by
  have hemb : MeasurableEmbedding e := e.toHomeomorph.isClosedEmbedding.measurableEmbedding
  exact hemb.areaFormulaHolds_of_measure_image_eq
    (fun s _ ↦ by
      rw [one_mul, Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def,
        Measure.smul_apply, Measure.smul_apply,
        e.isometry.hausdorffMeasure_image (Or.inr e.surjective) s]) hA

/-- Left translation `x ↦ a + x` on a Borel normed additive group satisfies
`AreaFormulaHolds μH[d] μH[d] (fun x ↦ a + x) (fun _ ↦ 1) A`. -/
theorem areaFormulaHolds_add_left_hausdorffMeasure {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (a : E) (d : ℝ) {A : Set E} (hA : MeasurableSet A) :
    AreaFormulaHolds μH[d] μH[d] (fun x : E ↦ a + x) (fun _ ↦ 1) A :=
  (IsometryEquiv.addLeft a).areaFormulaHolds_hausdorffMeasure d hA

/-- Right translation `x ↦ x + a` on a Borel normed additive group satisfies
`AreaFormulaHolds μH[d] μH[d] (fun x ↦ x + a) (fun _ ↦ 1) A`. -/
theorem areaFormulaHolds_add_right_hausdorffMeasure {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (a : E) (d : ℝ) {A : Set E} (hA : MeasurableSet A) :
    AreaFormulaHolds μH[d] μH[d] (fun x : E ↦ x + a) (fun _ ↦ 1) A :=
  (IsometryEquiv.addRight a).areaFormulaHolds_hausdorffMeasure d hA

/-- Under scalar dilation by `r ≠ 0` on a Borel real normed space `E` and `0 ≤ d`,
`μH[d] (r • s) = (‖r‖₊ : ℝ≥0∞) ^ d * μH[d] s`. -/
theorem hausdorffMeasure_smul_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {r : ℝ} (hr : r ≠ 0) {d : ℝ} (hd : 0 ≤ d) (s : Set E) :
    μH[d] (r • s) = (‖r‖₊ : ℝ≥0∞) ^ d * μH[d] s := by
  have hlip1 : LipschitzWith ‖r‖₊ (fun x : E ↦ r • x) := lipschitzWith_smul r
  have hlip2 : LipschitzWith ‖r⁻¹‖₊ (fun x : E ↦ r⁻¹ • x) := lipschitzWith_smul r⁻¹
  have hle1 : μH[d] (r • s) ≤ (‖r‖₊ : ℝ≥0∞) ^ d * μH[d] s :=
    hlip1.hausdorffMeasure_image_le hd s
  have hle2 : μH[d] s ≤ (‖r⁻¹‖₊ : ℝ≥0∞) ^ d * μH[d] (r • s) := by
    have heq : (fun x : E ↦ r⁻¹ • x) '' (r • s) = s := inv_smul_smul₀ hr s
    simpa [heq] using hlip2.hausdorffMeasure_image_le hd (r • s)
  refine le_antisymm hle1 ?_
  calc (‖r‖₊ : ℝ≥0∞) ^ d * μH[d] s
      ≤ (‖r‖₊ : ℝ≥0∞) ^ d * ((‖r⁻¹‖₊ : ℝ≥0∞) ^ d * μH[d] (r • s)) := by gcongr
    _ = ((‖r‖₊ : ℝ≥0∞) * ‖r⁻¹‖₊) ^ d * μH[d] (r • s) := by
        rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hd]
    _ = μH[d] (r • s) := by
        rw [← ENNReal.coe_mul, ← nnnorm_mul, mul_inv_cancel₀ hr, nnnorm_one, ENNReal.coe_one,
          ENNReal.one_rpow, one_mul]

/-- Under scalar dilation by `r ≠ 0` on a Borel real normed space `E` and `k : ℕ`,
`μHE[k] (r • s) = (‖r‖₊ : ℝ≥0∞) ^ k * μHE[k] s`. -/
theorem euclideanHausdorffMeasure_smul_of_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] {r : ℝ} (hr : r ≠ 0) (k : ℕ) (s : Set E) :
    μHE[k] (r • s) = (‖r‖₊ : ℝ≥0∞) ^ k * μHE[k] s := by
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
    hausdorffMeasure_smul_of_ne_zero hr (Nat.cast_nonneg k) s, ENNReal.rpow_natCast,
    ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- Dilation area formula on a Borel real normed space `E`: for `r ≠ 0` and `0 ≤ d`,
`AreaFormulaHolds μH[d] μH[d] (fun x : E ↦ r • x) (fun _ ↦ (‖r‖₊ : ℝ≥0∞) ^ d) A`. -/
theorem areaFormulaHolds_smul_hausdorffMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {r : ℝ} (hr : r ≠ 0) {d : ℝ} (hd : 0 ≤ d)
    {A : Set E} (hA : MeasurableSet A) :
    AreaFormulaHolds μH[d] μH[d] (fun x : E ↦ r • x) (fun _ ↦ (‖r‖₊ : ℝ≥0∞) ^ d) A :=
  (Homeomorph.smulOfNeZero r hr).isClosedEmbedding.measurableEmbedding
    |>.areaFormulaHolds_of_measure_image_eq
      (fun s _ ↦ hausdorffMeasure_smul_of_ne_zero hr hd s) hA

/-- Dilation area formula for Euclidean-normalized Hausdorff measure `μHE[k]`: for `r ≠ 0`,
`AreaFormulaHolds μHE[k] μHE[k] (fun x : E ↦ r • x) (fun _ ↦ (‖r‖₊ : ℝ≥0∞) ^ k) A`. -/
theorem areaFormulaHolds_smul_euclideanHausdorffMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] {r : ℝ} (hr : r ≠ 0) (k : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    AreaFormulaHolds μHE[k] μHE[k] (fun x : E ↦ r • x) (fun _ ↦ (‖r‖₊ : ℝ≥0∞) ^ k) A :=
  (Homeomorph.smulOfNeZero r hr).isClosedEmbedding.measurableEmbedding
    |>.areaFormulaHolds_of_measure_image_eq
      (fun s _ ↦ euclideanHausdorffMeasure_smul_of_ne_zero hr k s) hA

end AreaFormulaAndTransport

/-! ### Section 3: Coarea formula, fiber slice integrals, and product / projection coarea -/

section CoareaFormulaAndSlicing

variable {X Y : Type*} [MeasurableSpace X]

/-- Fiber slice integral `coareaFiberIntegral μFiber f A g y = ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μFiber`
of `g : X → ℝ≥0∞` along the fiber `A ∩ f ⁻¹' {y}` with respect to `μFiber`. -/
def coareaFiberIntegral (μFiber : Measure X) (f : X → Y) (A : Set X) (g : X → ℝ≥0∞)
    (y : Y) : ℝ≥0∞ :=
  ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μFiber

/-- Fiber slice measure `coareaFiberMeasure μFiber f A y = μFiber (A ∩ f ⁻¹' {y})`. -/
def coareaFiberMeasure (μFiber : Measure X) (f : X → Y) (A : Set X) (y : Y) : ℝ≥0∞ :=
  μFiber (A ∩ f ⁻¹' {y})

@[simp] theorem coareaFiberIntegral_empty (μFiber : Measure X) (f : X → Y) (g : X → ℝ≥0∞) (y : Y) :
    coareaFiberIntegral μFiber f ∅ g y = 0 := by simp [coareaFiberIntegral]

@[simp] theorem coareaFiberMeasure_empty (μFiber : Measure X) (f : X → Y) (y : Y) :
    coareaFiberMeasure μFiber f ∅ y = 0 := by simp [coareaFiberMeasure]

/-- Unit-weight specialization of `coareaFiberIntegral` as `coareaFiberMeasure`. -/
@[simp] theorem coareaFiberIntegral_one (μFiber : Measure X) (f : X → Y) (A : Set X) (y : Y) :
    coareaFiberIntegral μFiber f A (fun _ ↦ 1) y = coareaFiberMeasure μFiber f A y := by
  simp [coareaFiberIntegral, coareaFiberMeasure]

/-- Constant-weight identity for `coareaFiberIntegral`. -/
theorem coareaFiberIntegral_const (μFiber : Measure X) (f : X → Y) (A : Set X) (c : ℝ≥0∞) (y : Y) :
    coareaFiberIntegral μFiber f A (fun _ ↦ c) y = c * coareaFiberMeasure μFiber f A y := by
  simp [coareaFiberIntegral, coareaFiberMeasure]

/-- With `μFiber = Measure.count`, `coareaFiberIntegral` coincides with `weightedFiberSum`. -/
theorem coareaFiberIntegral_count_eq_weightedFiberSum (f : X → Y) (A : Set X) (g : X → ℝ≥0∞)
    (y : Y) : coareaFiberIntegral Measure.count f A g y = weightedFiberSum f A g y := rfl

/-- Indicator restriction law for `coareaFiberIntegral`. -/
theorem coareaFiberIntegral_indicator (μFiber : Measure X) (f : X → Y) (A : Set X) {B : Set X}
    (hB : MeasurableSet B) (g : X → ℝ≥0∞) (y : Y) :
    coareaFiberIntegral μFiber f A (B.indicator g) y =
      coareaFiberIntegral μFiber f (A ∩ B) g y := by
  rw [coareaFiberIntegral, coareaFiberIntegral, lintegral_indicator hB,
    Measure.restrict_restrict hB, ← inter_assoc, inter_comm B A]

/-- Countable additivity of `coareaFiberIntegral` across pairwise disjoint measurable sets `A i`. -/
theorem coareaFiberIntegral_Union_disjoint {ι : Type*} [Countable ι] (μFiber : Measure X)
    (f : X → Y) {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (g : X → ℝ≥0∞) (y : Y) :
    coareaFiberIntegral μFiber f (⋃ i, A i) g y =
      ∑' i, coareaFiberIntegral μFiber f (A i) g y := by
  have hrestrict (s : Set X) (hs : MeasurableSet s) :
      coareaFiberIntegral μFiber f s g y =
        ∫⁻ x in s, g x ∂(μFiber.restrict (f ⁻¹' {y})) := by
    rw [coareaFiberIntegral, Measure.restrict_restrict hs]
  rw [hrestrict (⋃ i, A i) (MeasurableSet.iUnion hA), lintegral_iUnion hA hdisj]
  exact tsum_congr fun i ↦ (hrestrict (A i) (hA i)).symm

/-- Countable additivity of `coareaFiberMeasure` across pairwise disjoint measurable sets `A i`. -/
theorem coareaFiberMeasure_Union_disjoint {ι : Type*} [Countable ι] (μFiber : Measure X)
    (f : X → Y) {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (y : Y) :
    coareaFiberMeasure μFiber f (⋃ i, A i) y =
      ∑' i, coareaFiberMeasure μFiber f (A i) y := by
  simpa only [← coareaFiberIntegral_one] using
    coareaFiberIntegral_Union_disjoint μFiber f hA hdisj (fun _ ↦ 1) y

variable [MeasurableSpace Y]

/-- Predicate asserting that the coarea formula holds for `f : X → Y` on `A : Set X` with coarea
Jacobian `J : X → ℝ≥0∞` and fiber measure `μFiber`:
`∫⁻ x in A, g x * J x ∂μX = ∫⁻ y, coareaFiberIntegral μFiber f A g y ∂μY` for all measurable `g`. -/
def CoareaFormulaHolds (μX : Measure X) (μY : Measure Y) (μFiber : Measure X)
    (f : X → Y) (J : X → ℝ≥0∞) (A : Set X) : Prop :=
  ∀ ⦃g : X → ℝ≥0∞⦄, Measurable g →
    ∫⁻ x in A, g x * J x ∂μX = ∫⁻ y, coareaFiberIntegral μFiber f A g y ∂μY

/-- With `μFiber = Measure.count`, `CoareaFormulaHolds` coincides with `AreaFormulaHolds`. -/
theorem coareaFormulaHolds_count_iff_areaFormulaHolds (μX : Measure X) (μY : Measure Y)
    (f : X → Y) (J : X → ℝ≥0∞) (A : Set X) :
    CoareaFormulaHolds μX μY Measure.count f J A ↔ AreaFormulaHolds μX μY f J A := Iff.rfl

namespace CoareaFormulaHolds

/-- Unweighted specialization of `CoareaFormulaHolds` (`g = 1`):
`∫⁻ x in A, J x ∂μX = ∫⁻ y, coareaFiberMeasure μFiber f A y ∂μY`. -/
theorem lintegral_jacobian {μX : Measure X} {μY : Measure Y} {μFiber : Measure X}
    {f : X → Y} {J : X → ℝ≥0∞} {A : Set X} (h : CoareaFormulaHolds μX μY μFiber f J A) :
    ∫⁻ x in A, J x ∂μX = ∫⁻ y, coareaFiberMeasure μFiber f A y ∂μY := by
  simpa [one_mul, coareaFiberIntegral_one] using h (g := fun _ ↦ 1) measurable_const

/-- If `J x = 0` on a measurable set `A`, then `∫⁻ y, coareaFiberMeasure μFiber f A y ∂μY = 0`. -/
theorem lintegral_fiber_measure_eq_zero_of_jacobian_eq_zero
    {μX : Measure X} {μY : Measure Y} {μFiber : Measure X}
    {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : CoareaFormulaHolds μX μY μFiber f J A) (hA : MeasurableSet A) (hJ : ∀ x ∈ A, J x = 0) :
    ∫⁻ y, coareaFiberMeasure μFiber f A y ∂μY = 0 := by
  rw [← h.lintegral_jacobian, setLIntegral_congr_fun hA hJ, lintegral_zero]

/-- Critical-set fiber vanishing: if `J x = 0` on `A` (`A` measurable) and
`coareaFiberMeasure μFiber f A` is `μY`-a.e. measurable, then
`coareaFiberMeasure μFiber f A y = 0` for `μY`-a.e. `y`. -/
theorem ae_fiber_measure_eq_zero_of_jacobian_eq_zero
    {μX : Measure X} {μY : Measure Y} {μFiber : Measure X}
    {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : CoareaFormulaHolds μX μY μFiber f J A) (hA : MeasurableSet A) (hJ : ∀ x ∈ A, J x = 0)
    (hm : AEMeasurable (coareaFiberMeasure μFiber f A) μY) :
    ∀ᵐ y ∂μY, coareaFiberMeasure μFiber f A y = 0 :=
  (lintegral_eq_zero_iff' hm).mp (h.lintegral_fiber_measure_eq_zero_of_jacobian_eq_zero hA hJ)

/-- Restriction of `CoareaFormulaHolds` to any measurable subset `B ⊆ A`. -/
theorem restrict_subset {μX : Measure X} {μY : Measure Y} {μFiber : Measure X}
    {f : X → Y} {J : X → ℝ≥0∞} {A B : Set X}
    (h : CoareaFormulaHolds μX μY μFiber f J A) (hB : MeasurableSet B) (hBA : B ⊆ A) :
    CoareaFormulaHolds μX μY μFiber f J B := by
  intro g hg
  have h1 := h (hg.indicator hB)
  have hLHS : ∫⁻ x in A, B.indicator g x * J x ∂μX = ∫⁻ x in B, g x * J x ∂μX := by
    have hmul : (fun x ↦ B.indicator g x * J x) = B.indicator (fun x ↦ g x * J x) := by
      ext x; by_cases hx : x ∈ B <;> simp [hx]
    rw [hmul, lintegral_indicator hB, Measure.restrict_restrict hB,
      inter_eq_self_of_subset_left hBA]
  have hRHS : (fun y ↦ coareaFiberIntegral μFiber f A (B.indicator g) y) =
      coareaFiberIntegral μFiber f B g := by
    ext y
    rw [coareaFiberIntegral_indicator μFiber f A hB g y, inter_eq_self_of_subset_right hBA]
  rwa [hLHS, hRHS] at h1

/-- Countable rectifiable decomposition for `CoareaFormulaHolds` across pairwise disjoint
measurable sets `A : ι → Set X`. -/
theorem iUnion_disjoint {ι : Type*} [Countable ι] {μX : Measure X} {μY : Measure Y}
    {μFiber : Measure X} {f : X → Y} {J : X → ℝ≥0∞} {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (h : ∀ i, CoareaFormulaHolds μX μY μFiber f J (A i))
    (hmeas : ∀ i ⦃g : X → ℝ≥0∞⦄, Measurable g →
      AEMeasurable (coareaFiberIntegral μFiber f (A i) g) μY) :
    CoareaFormulaHolds μX μY μFiber f J (⋃ i, A i) := by
  intro g hg
  rw [lintegral_iUnion hA hdisj]
  simp_rw [h _ hg, coareaFiberIntegral_Union_disjoint μFiber f hA hdisj g]
  exact (lintegral_tsum fun i ↦ hmeas i hg).symm

/-- Congruence of `CoareaFormulaHolds` when two Jacobians coincide on the measurable set `A`. -/
theorem congr_jacobian {μX : Measure X} {μY : Measure Y} {μFiber : Measure X}
    {f : X → Y} {J₁ J₂ : X → ℝ≥0∞} {A : Set X}
    (h : CoareaFormulaHolds μX μY μFiber f J₁ A) (hA : MeasurableSet A)
    (hJ : ∀ x ∈ A, J₁ x = J₂ x) :
    CoareaFormulaHolds μX μY μFiber f J₂ A := by
  intro g hg
  rw [← h hg]
  exact setLIntegral_congr_fun hA fun x hx ↦ by rw [hJ x hx]

/-- Simultaneous scalar scaling of `(μX, μY)` preserves `CoareaFormulaHolds`. -/
theorem smul_measure {μX : Measure X} {μY : Measure Y} {μFiber : Measure X}
    {f : X → Y} {J : X → ℝ≥0∞} {A : Set X}
    (h : CoareaFormulaHolds μX μY μFiber f J A) (c : ℝ≥0∞) :
    CoareaFormulaHolds (c • μX) (c • μY) μFiber f J A := by
  intro g hg
  rw [Measure.restrict_smul, lintegral_smul_measure, lintegral_smul_measure, h hg]

end CoareaFormulaHolds

/-- **First-coordinate Tonelli slicing (`Prod.fst` coarea)**: for a `σ`-finite measure `μY`,
a measurable set `A ⊆ X × Y`, and a measurable function `g : X × Y → ℝ≥0∞`,
`∫⁻ p in A, g p ∂(μX.prod μY) = ∫⁻ x, ∫⁻ y in Prod.mk x ⁻¹' A, g (x, y) ∂μY ∂μX`. -/
theorem setLIntegral_prod_fst_slice (μX : Measure X) (μY : Measure Y)
    [SigmaFinite μY] {A : Set (X × Y)} (hA : MeasurableSet A)
    {g : X × Y → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p in A, g p ∂(μX.prod μY) = ∫⁻ x, ∫⁻ y in Prod.mk x ⁻¹' A, g (x, y) ∂μY ∂μX := by
  rw [← lintegral_indicator hA, lintegral_prod _ (hg.indicator hA).aemeasurable]
  refine lintegral_congr fun x ↦ ?_
  rw [← lintegral_indicator (measurable_prodMk_left hA)]
  rfl

/-- **Second-coordinate Tonelli slicing (`Prod.snd` coarea)**: for `σ`-finite measures `μX` and
`μY`, a measurable set `A ⊆ X × Y`, and a measurable function `g : X × Y → ℝ≥0∞`,
`∫⁻ p in A, g p ∂(μX.prod μY) = ∫⁻ y, ∫⁻ x in (fun x ↦ (x, y)) ⁻¹' A, g (x, y) ∂μX ∂μY`. -/
theorem setLIntegral_prod_snd_slice (μX : Measure X) (μY : Measure Y)
    [SigmaFinite μX] [SigmaFinite μY] {A : Set (X × Y)} (hA : MeasurableSet A)
    {g : X × Y → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p in A, g p ∂(μX.prod μY) =
      ∫⁻ y, ∫⁻ x in (fun x ↦ (x, y)) ⁻¹' A, g (x, y) ∂μX ∂μY := by
  rw [← lintegral_indicator hA, lintegral_prod_symm _ (hg.indicator hA).aemeasurable]
  refine lintegral_congr fun y ↦ ?_
  rw [← lintegral_indicator (measurable_prodMk_right hA)]
  rfl

/-- **First-coordinate measure slicing**: `(μX.prod μY) A = ∫⁻ x, μY (Prod.mk x ⁻¹' A) ∂μX`. -/
theorem measure_prod_eq_lintegral_fst_slice (μX : Measure X) (μY : Measure Y)
    [SigmaFinite μY] {A : Set (X × Y)} (hA : MeasurableSet A) :
    (μX.prod μY) A = ∫⁻ x, μY (Prod.mk x ⁻¹' A) ∂μX := by
  simpa using setLIntegral_prod_fst_slice μX μY hA (g := fun _ ↦ 1) measurable_const

/-- **Second-coordinate measure slicing**:
`(μX.prod μY) A = ∫⁻ y, μX ((fun x ↦ (x, y)) ⁻¹' A) ∂μY`. -/
theorem measure_prod_eq_lintegral_snd_slice (μX : Measure X) (μY : Measure Y)
    [SigmaFinite μX] [SigmaFinite μY] {A : Set (X × Y)} (hA : MeasurableSet A) :
    (μX.prod μY) A = ∫⁻ y, μX ((fun x ↦ (x, y)) ⁻¹' A) ∂μY := by
  simpa using setLIntegral_prod_snd_slice μX μY hA (g := fun _ ↦ 1) measurable_const

/-- **First-coordinate Fubini Bochner-integral slicing**: for `σ`-finite measures `μX` and `μY`,
a measurable set `A ⊆ X × Y`, and `h : X × Y → E` integrable on `A`,
`∫ p in A, h p ∂(μX.prod μY) = ∫ x, ∫ y in Prod.mk x ⁻¹' A, h (x, y) ∂μY ∂μX`. -/
theorem setIntegral_prod_fst_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μX : Measure X) (μY : Measure Y) [SigmaFinite μX] [SigmaFinite μY]
    {A : Set (X × Y)} (hA : MeasurableSet A) {h : X × Y → E}
    (hh : IntegrableOn h A (μX.prod μY)) :
    ∫ p in A, h p ∂(μX.prod μY) = ∫ x, ∫ y in Prod.mk x ⁻¹' A, h (x, y) ∂μY ∂μX := by
  rw [← integral_indicator hA, integral_prod _ ((integrable_indicator_iff hA).mpr hh)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [← integral_indicator (measurable_prodMk_left hA)]
  rfl

/-- **Second-coordinate Fubini Bochner-integral slicing**: for `σ`-finite measures `μX` and `μY`,
a measurable set `A ⊆ X × Y`, and `h : X × Y → E` integrable on `A`,
`∫ p in A, h p ∂(μX.prod μY) = ∫ y, ∫ x in (fun x ↦ (x, y)) ⁻¹' A, h (x, y) ∂μX ∂μY`. -/
theorem setIntegral_prod_snd_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μX : Measure X) (μY : Measure Y) [SigmaFinite μX] [SigmaFinite μY]
    {A : Set (X × Y)} (hA : MeasurableSet A) {h : X × Y → E}
    (hh : IntegrableOn h A (μX.prod μY)) :
    ∫ p in A, h p ∂(μX.prod μY) = ∫ y, ∫ x in (fun x ↦ (x, y)) ⁻¹' A, h (x, y) ∂μX ∂μY := by
  rw [← integral_indicator hA, integral_prod_symm _ ((integrable_indicator_iff hA).mpr hh)]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [← integral_indicator (measurable_prodMk_right hA)]
  rfl

end CoareaFormulaAndSlicing

end TauCeti
