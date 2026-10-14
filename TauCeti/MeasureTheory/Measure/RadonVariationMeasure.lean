/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import TauCeti.MeasureTheory.Measure.BallPerimeter
import all TauCeti.MeasureTheory.Measure.BallPerimeter
import all TauCeti.MeasureTheory.Measure.Perimeter

/-!
# Radon Variation Measure, Polar Decomposition, Lebesgue Decomposition, and Weak Gradients

This file develops the measure-valued distributional derivative `Du = σ_u |Du|` of a scalar
function `u : E → ℝ` on a domain `U ⊆ E`, its polar unit-vector representation, the
Lebesgue–Radon–Nikodym decomposition of a variation measure `ν` into its absolutely continuous part
`acVariationMeasure ν = volume.withDensity (ν.rnDeriv volume)` and singular part
`singularVariationMeasure ν = ν.singularPart volume` with approximate gradient density
`approxGradient σ ν`, the equivalence between integrable weak gradients (`HasWeakGradientOn`) and
derivative measures with vanishing singular part (`singularVariationMeasure ν = 0`), and the purely
singular derivative regime (`ν ⟂ₘ volume`) governing jump and Caccioppoli / De Giorgi perimeter
measures:

1. **Smooth compactly supported test fields and polar derivative measure representation**:
   `TauCeti.IsSmoothCompactlySupportedOn`, `TauCeti.HasDerivativeMeasureOn`,
   `TauCeti.HasPolarDerivativeMeasureOn`,
   `TauCeti.HasDerivativeMeasureOn.abs_integral_mul_divergence_le`,
   `TauCeti.HasDerivativeMeasureOn.of_const`, `TauCeti.HasDerivativeMeasureOn.neg`,
   `TauCeti.HasDerivativeMeasureOn.add_const`, `TauCeti.HasDerivativeMeasureOn.smul_nonneg`,
   `TauCeti.HasPolarDerivativeMeasureOn.smul_pos`, `TauCeti.HasDerivativeMeasureOn.mono_subset`,
   `TauCeti.HasDerivativeMeasureOn.distributionalVariation_le`, and
   `TauCeti.HasDerivativeMeasureOn.relativePerimeter_le`.
2. **Lebesgue–Radon–Nikodym decomposition into absolutely continuous and singular parts**:
   `TauCeti.acVariationMeasure`, `TauCeti.singularVariationMeasure`, `TauCeti.approxGradient`,
   `TauCeti.acVariationMeasure_add_singularVariationMeasure`,
   `TauCeti.absolutelyContinuous_acVariationMeasure`,
   `TauCeti.mutuallySingular_singularVariationMeasure`,
   `TauCeti.singularVariationMeasure_eq_zero_iff`, `TauCeti.acVariationMeasure_eq_self_iff`,
   `TauCeti.acVariationMeasure_apply_eq_lintegral_enorm_approxGradient`, and
   `TauCeti.setIntegral_inner_eq_ac_add_singular`.
3. **Weak-gradient equivalence (`HasWeakGradientOn`) and purely singular derivative measures**:
   `TauCeti.HasWeakGradientOn`, `TauCeti.unitDirection`, `TauCeti.gradientVariationMeasure`,
   `TauCeti.HasWeakGradientOn.hasPolarDerivativeMeasureOn`,
   `TauCeti.singularVariationMeasure_gradientVariationMeasure_eq_zero`,
   `TauCeti.HasDerivativeMeasureOn.hasWeakGradientOn_approxGradient_of_absolutelyContinuous`,
   `TauCeti.hasWeakGradientOn_iff_exists_derivativeMeasureOn_singular_eq_zero`, and
   `TauCeti.acVariationMeasure_eq_zero_and_singular_eq_self_of_mutuallySingular`.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Set TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Topology Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Section 1: Smooth test vector fields and polar derivative measure representation -/

section PolarDerivativeMeasure

/-- Predicate asserting that a vector field `φ : E → E` is smooth (`ContDiff ℝ ⊤ φ`), has compact
support, and has topological support `tsupport φ` contained in `U : Set E`. -/
def IsSmoothCompactlySupportedOn (U : Set E) (φ : E → E) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

namespace IsSmoothCompactlySupportedOn

variable {U V : Set E} {φ : E → E}

/-- Smoothness (`ContDiff ℝ ⊤`) of an admissible test vector field. -/
theorem contDiff (hφ : IsSmoothCompactlySupportedOn U φ) : ContDiff ℝ (⊤ : ℕ∞) φ := hφ.1
/-- `C¹` smoothness (`ContDiff ℝ 1`) of an admissible test vector field. -/
theorem contDiff_one (hφ : IsSmoothCompactlySupportedOn U φ) : ContDiff ℝ 1 φ :=
  hφ.1.of_le (by simp)
/-- Continuity of an admissible test vector field. -/
theorem continuous (hφ : IsSmoothCompactlySupportedOn U φ) : Continuous φ := hφ.1.continuous
/-- Compact support of an admissible test vector field. -/
theorem hasCompactSupport (hφ : IsSmoothCompactlySupportedOn U φ) : HasCompactSupport φ := hφ.2.1
/-- Topological support inclusion `tsupport φ ⊆ U` of an admissible test vector field. -/
theorem tsupport_subset (hφ : IsSmoothCompactlySupportedOn U φ) : tsupport φ ⊆ U := hφ.2.2
/-- Every bundled test vector field `φ : 𝓓(Ω, E)` satisfies `IsSmoothCompactlySupportedOn Ω φ`. -/
theorem of_testFunction {Ω : Opens E} (φ : 𝓓(Ω, E)) :
    IsSmoothCompactlySupportedOn (Ω : Set E) (φ : E → E) :=
  ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
/-- Covariant domain monotonicity of `IsSmoothCompactlySupportedOn`. -/
theorem mono (hφ : IsSmoothCompactlySupportedOn U φ) (hUV : U ⊆ V) :
    IsSmoothCompactlySupportedOn V φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUV⟩
/-- The zero vector field is smooth and compactly supported on any set `U`. -/
theorem zero (U : Set E) : IsSmoothCompactlySupportedOn U (0 : E → E) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
/-- Negating an admissible test vector field preserves `IsSmoothCompactlySupportedOn`. -/
theorem neg (hφ : IsSmoothCompactlySupportedOn U φ) : IsSmoothCompactlySupportedOn U (-φ) :=
  ⟨hφ.1.neg, hφ.2.1.neg, by simpa [tsupport_neg] using hφ.2.2⟩
/-- Outside `U`, any `φ` satisfying `IsSmoothCompactlySupportedOn U φ` vanishes. -/
theorem apply_eq_zero_of_notMem (hφ : IsSmoothCompactlySupportedOn U φ) {x : E} (hx : x ∉ U) :
    φ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφ.2.2 h)
/-- Outside `U`, the divergence of `φ` vanishes. -/
theorem divergence_eq_zero_of_notMem (hφ : IsSmoothCompactlySupportedOn U φ) {x : E}
    (hx : x ∉ U) : divergence φ x = 0 := by
  have hev : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hφ.2.2 h)
  simp [divergence, hev.fderiv_eq]
/-- The divergence of an admissible test vector field has compact support. -/
theorem hasCompactSupport_divergence (hφ : IsSmoothCompactlySupportedOn U φ) :
    HasCompactSupport (divergence φ) := by
  refine HasCompactSupport.of_support_subset_isCompact hφ.hasCompactSupport.isCompact fun x hx ↦ ?_
  by_contra hxs
  have hev : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxs
  exact hx (by simp [divergence, hev.fderiv_eq])

variable [MeasurableSpace E]

/-- Integrating `u x * divergence φ x` over `U` agrees with integrating over the whole space `E`. -/
theorem setIntegral_mul_divergence_eq_integral (hφ : IsSmoothCompactlySupportedOn U φ)
    (μ : Measure E) (u : E → ℝ) :
    ∫ x in U, u x * divergence φ x ∂μ = ∫ x, u x * divergence φ x ∂μ :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx ↦ by
    rw [hφ.divergence_eq_zero_of_notMem hx, mul_zero]
/-- If `U ⊆ V`, integrating `u x * divergence φ x` over `V` agrees with integrating over `U`. -/
theorem setIntegral_mul_divergence_mono (hφ : IsSmoothCompactlySupportedOn U φ) (hUV : U ⊆ V)
    (μ : Measure E) (u : E → ℝ) :
    ∫ x in V, u x * divergence φ x ∂μ = ∫ x in U, u x * divergence φ x ∂μ := by
  rw [(hφ.mono hUV).setIntegral_mul_divergence_eq_integral,
    hφ.setIntegral_mul_divergence_eq_integral]

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- `divergence φ` is integrable with respect to any measure that is finite on compact sets. -/
theorem integrable_divergence {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    (hφ : IsSmoothCompactlySupportedOn U φ) : Integrable (divergence φ) μ :=
  (continuous_divergence_of_contDiff_one hφ.contDiff_one).integrable_of_hasCompactSupport
    hφ.hasCompactSupport_divergence
/-- The divergence of an admissible test vector field is integrable on `U`. -/
theorem integrableOn_divergence {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    (hφ : IsSmoothCompactlySupportedOn U φ) : IntegrableOn (divergence φ) U μ :=
  hφ.integrable_divergence.integrableOn
/-- The integral of `divergence φ` over `U` vanishes for any additive Haar measure `μ`. -/
theorem setIntegral_divergence_eq_zero {μ : Measure E} [μ.IsAddHaarMeasure]
    (hφ : IsSmoothCompactlySupportedOn U φ) : ∫ x in U, divergence φ x ∂μ = 0 := by
  have h1 := hφ.setIntegral_mul_divergence_eq_integral μ (fun _ ↦ 1)
  simp only [one_mul] at h1
  exact h1.trans (integral_divergence_eq_zero_of_contDiff_one hφ.contDiff_one hφ.hasCompactSupport)

end IsSmoothCompactlySupportedOn

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Predicate asserting that `u : E → ℝ` has **derivative measure representation** `Du = σ ν` on
`U : Set E`: `σ : E → E` is `(ν.restrict U)`-a.e. strongly measurable with `‖σ x‖ ≤ 1` a.e., and
for every smooth compactly supported test vector field `φ` on `U`, `x ↦ u x * divergence φ x` is
Lebesgue-integrable on `U` and satisfies
`∫ x in U, u x * divergence φ x = - ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν`. -/
def HasDerivativeMeasureOn (u : E → ℝ) (U : Set E) (σ : E → E) (ν : Measure E) : Prop :=
  AEStronglyMeasurable σ (ν.restrict U) ∧ (∀ᵐ x ∂(ν.restrict U), ‖σ x‖ ≤ 1) ∧
    ∀ ⦃φ : E → E⦄, IsSmoothCompactlySupportedOn U φ →
      IntegrableOn (fun x ↦ u x * divergence φ x) U volume ∧
        ∫ x in U, u x * divergence φ x = -∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν
/-- Predicate asserting that `u : E → ℝ` has **polar derivative measure representation**
`Du = σ_u |Du|` on `U : Set E` with unit polar vector field `‖σ x‖ = 1` for `(ν.restrict U)`-a.e.
`x` and total variation measure `ν`. -/
def HasPolarDerivativeMeasureOn (u : E → ℝ) (U : Set E) (σ : E → E) (ν : Measure E) : Prop :=
  HasDerivativeMeasureOn u U σ ν ∧ ∀ᵐ x ∂(ν.restrict U), ‖σ x‖ = 1

namespace HasPolarDerivativeMeasureOn

variable {u : E → ℝ} {U : Set E} {σ : E → E} {ν : Measure E}

/-- Underlying `HasDerivativeMeasureOn` structure of `HasPolarDerivativeMeasureOn`. -/
theorem hasDerivativeMeasureOn (h : HasPolarDerivativeMeasureOn u U σ ν) :
    HasDerivativeMeasureOn u U σ ν := h.1
/-- Almost-everywhere unit-norm property `‖σ x‖ = 1` on `ν.restrict U`. -/
theorem ae_norm_eq_one (h : HasPolarDerivativeMeasureOn u U σ ν) :
    ∀ᵐ x ∂(ν.restrict U), ‖σ x‖ = 1 := h.2

end HasPolarDerivativeMeasureOn

namespace HasDerivativeMeasureOn

variable {u : E → ℝ} {U V : Set E} {σ : E → E} {ν : Measure E}

/-- Almost-everywhere strong measurability of the directional field `σ` on `ν.restrict U`. -/
theorem aestronglyMeasurable (h : HasDerivativeMeasureOn u U σ ν) :
    AEStronglyMeasurable σ (ν.restrict U) := h.1
/-- Almost-everywhere sub-unit norm bound `‖σ x‖ ≤ 1` on `ν.restrict U`. -/
theorem ae_norm_le_one (h : HasDerivativeMeasureOn u U σ ν) :
    ∀ᵐ x ∂(ν.restrict U), ‖σ x‖ ≤ 1 := h.2.1
/-- Integrability of `x ↦ u x * divergence φ x` on `U` for any admissible test field `φ`. -/
theorem integrableOn_mul_divergence (h : HasDerivativeMeasureOn u U σ ν)
    {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ) :
    IntegrableOn (fun x ↦ u x * divergence φ x) U volume := (h.2.2 hφ).1
/-- Distributional integration-by-parts identity
`∫ x in U, u x * divergence φ x = - ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν`. -/
theorem integral_mul_divergence (h : HasDerivativeMeasureOn u U σ ν)
    {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ) :
    ∫ x in U, u x * divergence φ x = -∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν := (h.2.2 hφ).2
/-- When `ν U ≠ ⊤` and `φ : E → E` is continuous with compact support, `x ↦ ⟪σ x, φ x⟫_ℝ` is
`ν`-integrable on `U`. -/
theorem integrableOn_inner_of_measure_ne_top (h : HasDerivativeMeasureOn u U σ ν)
    (hνU : ν U ≠ ⊤) {φ : E → E} (hφ_cont : Continuous φ) (hφ_supp : HasCompactSupport φ) :
    IntegrableOn (fun x ↦ ⟪σ x, φ x⟫_ℝ) U ν := by
  have : IsFiniteMeasure (ν.restrict U) := ⟨by rw [Measure.restrict_apply_univ]; exact hνU.lt_top⟩
  obtain ⟨C, hC⟩ := hφ_supp.exists_bound_of_continuous hφ_cont
  have hmeas : AEStronglyMeasurable (fun x ↦ ⟪σ x, φ x⟫_ℝ) (ν.restrict U) :=
    continuous_inner.comp_aestronglyMeasurable
      (h.aestronglyMeasurable.prodMk hφ_cont.aestronglyMeasurable)
  refine Integrable.mono' (integrable_const (max C 0)) hmeas ?_
  filter_upwards [h.ae_norm_le_one] with x hx
  calc ‖⟪σ x, φ x⟫_ℝ‖ ≤ ‖σ x‖ * ‖φ x‖ := norm_inner_le_norm (σ x) (φ x)
    _ ≤ 1 * max C 0 :=
      mul_le_mul hx ((hC x).trans (le_max_left C 0)) (norm_nonneg _) zero_le_one
    _ = max C 0 := one_mul _
/-- **Variational pairing inequality**: if `HasDerivativeMeasureOn u U σ ν`, `ν U ≠ ⊤`, and
`‖φ x‖ ≤ 1` on `U`, then `|∫ x in U, u x * divergence φ x| ≤ (ν U).toReal`. -/
theorem abs_integral_mul_divergence_le (h : HasDerivativeMeasureOn u U σ ν)
    (hU : MeasurableSet U) (hνU : ν U ≠ ⊤) {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ)
    (hφ_norm : ∀ x ∈ U, ‖φ x‖ ≤ 1) :
    |∫ x in U, u x * divergence φ x| ≤ (ν U).toReal := by
  have : IsFiniteMeasure (ν.restrict U) := ⟨by rw [Measure.restrict_apply_univ]; exact hνU.lt_top⟩
  rw [h.integral_mul_divergence hφ, abs_neg, ← Real.norm_eq_abs]
  have hle : ∀ᵐ x ∂(ν.restrict U), ‖⟪σ x, φ x⟫_ℝ‖ ≤ 1 := by
    filter_upwards [h.ae_norm_le_one, ae_restrict_mem hU] with x hxσ hxU
    calc ‖⟪σ x, φ x⟫_ℝ‖ ≤ ‖σ x‖ * ‖φ x‖ := norm_inner_le_norm (σ x) (φ x)
      _ ≤ 1 * 1 := mul_le_mul hxσ (hφ_norm x hxU) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  simpa [Measure.real, Measure.restrict_apply_univ] using norm_integral_le_of_norm_le_const hle
/-- The zero function has zero derivative measure on any set `U`. -/
theorem zero (U : Set E) : HasDerivativeMeasureOn (0 : E → ℝ) U 0 0 :=
  ⟨aestronglyMeasurable_const, by simp, fun _ _ ↦ ⟨by simp [IntegrableOn], by simp⟩⟩
/-- Any constant function `fun _ ↦ c` has zero derivative measure `ν = 0` with any field `σ`. -/
theorem of_const (c : ℝ) (U : Set E) (σ : E → E) : HasDerivativeMeasureOn (fun _ ↦ c) U σ 0 := by
  refine ⟨by simp, by simp, fun φ hφ ↦ ⟨hφ.integrableOn_divergence.const_mul c, ?_⟩⟩
  rw [integral_const_mul, hφ.setIntegral_divergence_eq_zero, mul_zero, Measure.restrict_zero,
    integral_zero_measure, neg_zero]
/-- Any constant function satisfies `HasPolarDerivativeMeasureOn (fun _ ↦ c) U σ 0`. -/
theorem _root_.TauCeti.HasPolarDerivativeMeasureOn.of_const (c : ℝ) (U : Set E) (σ : E → E) :
    HasPolarDerivativeMeasureOn (fun _ ↦ c) U σ 0 :=
  ⟨HasDerivativeMeasureOn.of_const c U σ, by simp⟩
/-- Negating `u` negates the polar directional field `σ` and preserves the variation measure `ν`. -/
theorem neg (h : HasDerivativeMeasureOn u U σ ν) : HasDerivativeMeasureOn (-u) U (-σ) ν := by
  refine ⟨h.1.neg, ?_, fun φ hφ ↦ ⟨?_, ?_⟩⟩
  · filter_upwards [h.2.1] with x hx; simpa using hx
  · simpa [Pi.neg_apply, neg_mul] using (h.integrableOn_mul_divergence hφ).neg
  · simp_rw [Pi.neg_apply, neg_mul, integral_neg, h.integral_mul_divergence hφ, inner_neg_left,
      integral_neg]
/-- Negating `u` in `HasPolarDerivativeMeasureOn` negates `σ` and preserves `ν`. -/
theorem _root_.TauCeti.HasPolarDerivativeMeasureOn.neg (h : HasPolarDerivativeMeasureOn u U σ ν) :
    HasPolarDerivativeMeasureOn (-u) U (-σ) ν :=
  ⟨h.1.neg, by filter_upwards [h.2] with x hx; simpa using hx⟩
/-- Adding a constant `c` to `u` preserves `HasDerivativeMeasureOn u U σ ν`. -/
theorem add_const (h : HasDerivativeMeasureOn u U σ ν) (c : ℝ) :
    HasDerivativeMeasureOn (fun x ↦ u x + c) U σ ν := by
  refine ⟨h.1, h.2.1, fun φ hφ ↦ ?_⟩
  have hu := h.integrableOn_mul_divergence hφ
  have hc := hφ.integrableOn_divergence (μ := volume).const_mul c
  have hsplit : (fun x ↦ (u x + c) * divergence φ x) =
      fun x ↦ u x * divergence φ x + c * divergence φ x := by ext x; ring
  refine ⟨by rw [hsplit]; exact hu.add hc, ?_⟩
  rw [hsplit, integral_add hu hc, integral_const_mul, hφ.setIntegral_divergence_eq_zero,
    mul_zero, add_zero, h.integral_mul_divergence hφ]
/-- Adding a constant `c` to `u` preserves `HasPolarDerivativeMeasureOn u U σ ν`. -/
theorem _root_.TauCeti.HasPolarDerivativeMeasureOn.add_const
    (h : HasPolarDerivativeMeasureOn u U σ ν) (c : ℝ) :
    HasPolarDerivativeMeasureOn (fun x ↦ u x + c) U σ ν := ⟨h.1.add_const c, h.2⟩
/-- Complement indicator law: if `A.indicator 1` has derivative measure `(σ, ν)` on `U`, then
`Aᶜ.indicator 1` has derivative measure `(-σ, ν)` on `U`. -/
theorem compl_indicator {A : Set E}
    (h : HasDerivativeMeasureOn (A.indicator (fun _ ↦ (1 : ℝ))) U σ ν) :
    HasDerivativeMeasureOn (Aᶜ.indicator (fun _ ↦ (1 : ℝ))) U (-σ) ν := by
  have heq : Aᶜ.indicator (fun _ : E ↦ (1 : ℝ)) =
      fun x ↦ -(A.indicator (fun _ ↦ (1 : ℝ)) x) + 1 := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  rw [heq]; exact h.neg.add_const 1
/-- Positive scalar homogeneity of `HasDerivativeMeasureOn`: for `0 ≤ c`, scaling `u` by `c`
preserves the directional field `σ` and scales the variation measure `ν` by `ENNReal.ofReal c`. -/
theorem smul_nonneg (h : HasDerivativeMeasureOn u U σ ν) {c : ℝ} (hc : 0 ≤ c) :
    HasDerivativeMeasureOn (c • u) U σ (ENNReal.ofReal c • ν) := by
  have h_ac : (ENNReal.ofReal c • ν).restrict U ≪ ν.restrict U := by
    rw [Measure.restrict_smul]; exact Measure.AbsolutelyContinuous.rfl.smul_left _
  have hmul : ∀ φ : E → E,
      (fun x ↦ (c • u) x * divergence φ x) = fun x ↦ c * (u x * divergence φ x) := by
    intro φ; ext x; simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
  refine ⟨h.1.mono_ac h_ac, h_ac.ae_le h.2.1, fun φ hφ ↦ ⟨?_, ?_⟩⟩
  · rw [hmul]; exact (h.integrableOn_mul_divergence hφ).const_mul c
  · rw [hmul, integral_const_mul, h.integral_mul_divergence hφ, Measure.restrict_smul,
      integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul, mul_neg]
/-- Strictly positive scalar homogeneity of `HasPolarDerivativeMeasureOn`. -/
theorem _root_.TauCeti.HasPolarDerivativeMeasureOn.smul_pos
    (h : HasPolarDerivativeMeasureOn u U σ ν) {c : ℝ} (hc : 0 < c) :
    HasPolarDerivativeMeasureOn (c • u) U σ (ENNReal.ofReal c • ν) := by
  refine ⟨h.1.smul_nonneg hc.le, ?_⟩
  rw [Measure.restrict_smul]; exact (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le h.2
/-- **Domain localization (`mono_subset`)**: if `HasDerivativeMeasureOn u U σ ν` and `V ⊆ U` is
measurable, then `HasDerivativeMeasureOn u V σ (ν.restrict V)`. -/
theorem mono_subset (h : HasDerivativeMeasureOn u U σ ν) {V : Set E} (hV : MeasurableSet V)
    (hVU : V ⊆ U) : HasDerivativeMeasureOn u V σ (ν.restrict V) := by
  have hrest : (ν.restrict V).restrict V = (ν.restrict U).restrict V := by
    rw [Measure.restrict_restrict hV, inter_self, Measure.restrict_restrict hV,
      inter_eq_self_of_subset_left hVU]
  refine ⟨by rw [hrest]; exact h.1.restrict, by rw [hrest]; exact ae_restrict_of_ae h.2.1,
    fun φ hφ ↦ ⟨(h.integrableOn_mul_divergence (hφ.mono hVU)).mono_set hVU, ?_⟩⟩
  rw [← hφ.setIntegral_mul_divergence_mono hVU, h.integral_mul_divergence (hφ.mono hVU),
    Measure.restrict_restrict hV, inter_self, neg_inj]
  have hU_int : ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν = ∫ x, ⟪σ x, φ x⟫_ℝ ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [hφ.apply_eq_zero_of_notMem fun hxV ↦ hx (hVU hxV), inner_zero_right]
  have hV_int : ∫ x in V, ⟪σ x, φ x⟫_ℝ ∂ν = ∫ x, ⟪σ x, φ x⟫_ℝ ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [hφ.apply_eq_zero_of_notMem hx, inner_zero_right]
  rw [hU_int, hV_int]
/-- **Domain localization for `HasPolarDerivativeMeasureOn`**: if
`HasPolarDerivativeMeasureOn u U σ ν` and `V ⊆ U` is measurable, then
`HasPolarDerivativeMeasureOn u V σ (ν.restrict V)`. -/
theorem _root_.TauCeti.HasPolarDerivativeMeasureOn.mono_subset
    (h : HasPolarDerivativeMeasureOn u U σ ν) {V : Set E} (hV : MeasurableSet V) (hVU : V ⊆ U) :
    HasPolarDerivativeMeasureOn u V σ (ν.restrict V) := by
  have hrest : (ν.restrict V).restrict V = (ν.restrict U).restrict V := by
    rw [Measure.restrict_restrict hV, inter_self, Measure.restrict_restrict hV,
      inter_eq_self_of_subset_left hVU]
  exact ⟨h.1.mono_subset hV hVU, by rw [hrest]; exact ae_restrict_of_ae h.2⟩
/-- **Variational total variation bound**: if `HasDerivativeMeasureOn u Ω σ ν` on an open set
`Ω : Opens E`, then `distributionalVariation volume Ω u ≤ ν Ω`. -/
theorem distributionalVariation_le {Ω : Opens E} (h : HasDerivativeMeasureOn u Ω σ ν) :
    distributionalVariation volume Ω u ≤ ν Ω := by
  by_cases htop : ν Ω = ⊤
  · rw [htop]; exact le_top
  · refine iSup₂_le fun φ hφ ↦ ?_
    have hle := h.abs_integral_mul_divergence_le Ω.isOpen.measurableSet htop
      (IsSmoothCompactlySupportedOn.of_testFunction φ) (fun x _ ↦ hφ x)
    calc ENNReal.ofReal (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x)
        ≤ ENNReal.ofReal |∫ x in (Ω : Set E), u x * divergence (φ : E → E) x| :=
          ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ENNReal.ofReal (ν Ω).toReal := ENNReal.ofReal_le_ofReal hle
      _ = ν Ω := ENNReal.ofReal_toReal htop
/-- If `HasDerivativeMeasureOn u Ω σ ν` on `Ω : Opens E`, `u` is integrable on `Ω`, and `ν Ω < ⊤`,
then `u` has bounded variation on `Ω` (`IsBVOn volume Ω u`). -/
theorem isBVOn_of_integrableOn {Ω : Opens E} (h : HasDerivativeMeasureOn u Ω σ ν)
    (hu : IntegrableOn u Ω volume) (hν : ν Ω < ⊤) : IsBVOn volume Ω u :=
  ⟨hu, h.distributionalVariation_le.trans_lt hν⟩
/-- **Relative perimeter bound from a derivative measure**: if `s : Set E` has characteristic
function `s.indicator 1` satisfying `HasDerivativeMeasureOn (s.indicator 1) Ω σ ν`, then
`relativePerimeter volume Ω s ≤ ν Ω`. -/
theorem relativePerimeter_le {Ω : Opens E} {s : Set E}
    (h : HasDerivativeMeasureOn (s.indicator (fun _ ↦ (1 : ℝ))) Ω σ ν) :
    relativePerimeter volume Ω s ≤ ν Ω := h.distributionalVariation_le
/-- **Whole-space Caccioppoli perimeter bound from a derivative measure**: if
`HasDerivativeMeasureOn (s.indicator 1) univ σ ν`, then `perimeter volume s ≤ ν univ`. -/
theorem perimeter_le {s : Set E}
    (h : HasDerivativeMeasureOn (s.indicator (fun _ ↦ (1 : ℝ))) univ σ ν) :
    perimeter volume s ≤ ν univ := h.distributionalVariation_le

end HasDerivativeMeasureOn

end PolarDerivativeMeasure

/-! ### Section 2: Lebesgue–Radon–Nikodym decomposition into AC and singular parts -/

section LebesgueRadonNikodymDecomposition

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The **absolutely continuous part**
`acVariationMeasure ν = volume.withDensity (ν.rnDeriv volume)` of `ν` w.r.t. `volume`. -/
def acVariationMeasure (ν : Measure E) : Measure E := volume.withDensity (ν.rnDeriv volume)
/-- The **singular part** `singularVariationMeasure ν = ν.singularPart volume` of a variation
measure `ν : Measure E` with respect to `volume`. -/
def singularVariationMeasure (ν : Measure E) : Measure E := ν.singularPart volume
/-- The **approximate gradient** `approxGradient σ ν x = (ν.rnDeriv volume x).toReal • σ x` of a
polar pair `(σ, ν)` with respect to `volume`. -/
def approxGradient (σ : E → E) (ν : Measure E) (x : E) : E := (ν.rnDeriv volume x).toReal • σ x
@[simp] theorem acVariationMeasure_zero : acVariationMeasure (0 : Measure E) = 0 :=
  (withDensity_congr_ae (Measure.rnDeriv_zero volume)).trans withDensity_zero
@[simp] theorem singularVariationMeasure_zero : singularVariationMeasure (0 : Measure E) = 0 :=
  Measure.singularPart_zero volume
@[simp] theorem approxGradient_zero_left (ν : Measure E) : approxGradient (0 : E → E) ν = 0 := by
  ext x; simp [approxGradient]
/-- **Lebesgue decomposition of a variation measure `ν`**:
`acVariationMeasure ν + singularVariationMeasure ν = ν`. -/
theorem acVariationMeasure_add_singularVariationMeasure (ν : Measure E)
    [ν.HaveLebesgueDecomposition volume] :
    acVariationMeasure ν + singularVariationMeasure ν = ν := by
  rw [add_comm, acVariationMeasure, singularVariationMeasure,
    ← Measure.haveLebesgueDecomposition_add ν volume]
/-- **Lebesgue decomposition of a variation measure `ν`** (`singular + ac = ν`). -/
theorem singularVariationMeasure_add_acVariationMeasure (ν : Measure E)
    [ν.HaveLebesgueDecomposition volume] :
    singularVariationMeasure ν + acVariationMeasure ν = ν :=
  (Measure.haveLebesgueDecomposition_add ν volume).symm
/-- `acVariationMeasure ν` is absolutely continuous with respect to `volume`. -/
theorem absolutelyContinuous_acVariationMeasure (ν : Measure E) :
    acVariationMeasure ν ≪ volume := withDensity_absolutelyContinuous volume (ν.rnDeriv volume)
/-- `singularVariationMeasure ν` is mutually singular with respect to `volume`. -/
theorem mutuallySingular_singularVariationMeasure (ν : Measure E) :
    singularVariationMeasure ν ⟂ₘ volume := Measure.mutuallySingular_singularPart ν volume
/-- The absolutely continuous and singular parts of `ν` are mutually singular. -/
theorem mutuallySingular_singular_acVariationMeasure (ν : Measure E) :
    singularVariationMeasure ν ⟂ₘ acVariationMeasure ν :=
  (mutuallySingular_singularVariationMeasure ν).mono_ac Measure.AbsolutelyContinuous.rfl
    (absolutelyContinuous_acVariationMeasure ν)
/-- Pointwise evaluation of the Lebesgue decomposition on any set `A`:
`ν A = acVariationMeasure ν A + singularVariationMeasure ν A`. -/
theorem variation_apply_eq_ac_add_singular (ν : Measure E) [ν.HaveLebesgueDecomposition volume]
    (A : Set E) : ν A = acVariationMeasure ν A + singularVariationMeasure ν A := by
  conv_lhs => rw [← acVariationMeasure_add_singularVariationMeasure ν, Measure.add_apply]
/-- Integral representation of `acVariationMeasure ν A` on any measurable set `A`:
`acVariationMeasure ν A = ∫⁻ x in A, ν.rnDeriv volume x ∂volume`. -/
theorem acVariationMeasure_apply (ν : Measure E) {A : Set E} (hA : MeasurableSet A) :
    acVariationMeasure ν A = ∫⁻ x in A, ν.rnDeriv volume x ∂volume :=
  withDensity_apply (ν.rnDeriv volume) hA
/-- `acVariationMeasure ν` is bounded above by `ν`. -/
theorem acVariationMeasure_le_self (ν : Measure E) [ν.HaveLebesgueDecomposition volume] :
    acVariationMeasure ν ≤ ν := by
  conv_rhs => rw [← acVariationMeasure_add_singularVariationMeasure ν]
  exact Measure.le_add_right le_rfl
/-- `singularVariationMeasure ν` is bounded above by `ν`. -/
theorem singularVariationMeasure_le_self (ν : Measure E) [ν.HaveLebesgueDecomposition volume] :
    singularVariationMeasure ν ≤ ν := by
  conv_rhs => rw [← singularVariationMeasure_add_acVariationMeasure ν]
  exact Measure.le_add_right le_rfl
/-- The singular variation measure vanishes if and only if `ν ≪ volume`. -/
theorem singularVariationMeasure_eq_zero_iff (ν : Measure E)
    [ν.HaveLebesgueDecomposition volume] : singularVariationMeasure ν = 0 ↔ ν ≪ volume :=
  Measure.singularPart_eq_zero ν volume
/-- The absolutely continuous variation measure equals `ν` if and only if `ν ≪ volume`. -/
theorem acVariationMeasure_eq_self_iff (ν : Measure E) [ν.HaveLebesgueDecomposition volume] :
    acVariationMeasure ν = ν ↔ ν ≪ volume :=
  ⟨fun h ↦ h ▸ absolutelyContinuous_acVariationMeasure ν, Measure.withDensity_rnDeriv_eq ν volume⟩
/-- The absolutely continuous variation measure vanishes if and only if `ν ⟂ₘ volume`. -/
theorem acVariationMeasure_eq_zero_iff (ν : Measure E) [ν.HaveLebesgueDecomposition volume] :
    acVariationMeasure ν = 0 ↔ ν ⟂ₘ volume := Measure.withDensity_rnDeriv_eq_zero ν volume
/-- The singular variation measure equals `ν` if and only if `ν ⟂ₘ volume`. -/
theorem singularVariationMeasure_eq_self_iff (ν : Measure E) :
    singularVariationMeasure ν = ν ↔ ν ⟂ₘ volume := Measure.singularPart_eq_self
/-- The Radon–Nikodym density `ν.rnDeriv volume` vanishes `volume`-a.e. iff `ν ⟂ₘ volume`. -/
theorem rnDeriv_eq_zero_ae_iff (ν : Measure E) [ν.HaveLebesgueDecomposition volume] :
    ν.rnDeriv volume =ᵐ[volume] 0 ↔ ν ⟂ₘ volume := Measure.rnDeriv_eq_zero ν volume
/-- Norm of the approximate gradient:
`‖approxGradient σ ν x‖ = (ν.rnDeriv volume x).toReal * ‖σ x‖`. -/
theorem norm_approxGradient (σ : E → E) (ν : Measure E) (x : E) :
    ‖approxGradient σ ν x‖ = (ν.rnDeriv volume x).toReal * ‖σ x‖ := by
  rw [approxGradient, norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
/-- Extended norm of the approximate gradient when `ν.rnDeriv volume x ≠ ⊤`:
`‖approxGradient σ ν x‖ₑ = ν.rnDeriv volume x * ‖σ x‖ₑ`. -/
theorem enorm_approxGradient {σ : E → E} {ν : Measure E} {x : E} (hx : ν.rnDeriv volume x ≠ ⊤) :
    ‖approxGradient σ ν x‖ₑ = ν.rnDeriv volume x * ‖σ x‖ₑ := by
  rw [← ofReal_norm, norm_approxGradient, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hx, ofReal_norm]
/-- If `‖σ x‖ = 1` for `volume`-a.e. `x`, then
`‖approxGradient σ ν x‖ = (ν.rnDeriv volume x).toReal` `volume`-a.e. -/
theorem ae_norm_approxGradient_of_unit {σ : E → E} (ν : Measure E)
    (hσ : ∀ᵐ x ∂volume, ‖σ x‖ = 1) :
    ∀ᵐ x ∂volume, ‖approxGradient σ ν x‖ = (ν.rnDeriv volume x).toReal := by
  filter_upwards [hσ] with x hx; rw [norm_approxGradient, hx, mul_one]
/-- When `[SigmaFinite ν]` and `‖σ x‖ = 1` for `volume`-a.e. `x`, the absolutely continuous
variation measure of any measurable set `A` is the `L¹` norm integral of `approxGradient σ ν`:
`acVariationMeasure ν A = ∫⁻ x in A, ‖approxGradient σ ν x‖ₑ ∂volume`. -/
theorem acVariationMeasure_apply_eq_lintegral_enorm_approxGradient {σ : E → E} (ν : Measure E)
    [SigmaFinite ν] (hσ : ∀ᵐ x ∂volume, ‖σ x‖ = 1) {A : Set E} (hA : MeasurableSet A) :
    acVariationMeasure ν A = ∫⁻ x in A, ‖approxGradient σ ν x‖ₑ ∂volume := by
  rw [acVariationMeasure_apply ν hA]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [Measure.rnDeriv_lt_top ν volume, hσ] with x htop hx
  rw [enorm_approxGradient htop.ne, ← ofReal_norm, hx, ENNReal.ofReal_one, mul_one]
/-- Integration against `acVariationMeasure ν` over a measurable set `U` equals integration against
`approxGradient σ ν` with respect to `volume`:
`∫ x in U, ⟪σ x, φ x⟫_ℝ ∂(acVariationMeasure ν) = ∫ x in U, ⟪approxGradient σ ν x, φ x⟫_ℝ`. -/
theorem setIntegral_inner_acVariationMeasure (σ φ : E → E) (ν : Measure E) [SigmaFinite ν]
    {U : Set E} (hU : MeasurableSet U) :
    ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂(acVariationMeasure ν) =
      ∫ x in U, ⟪approxGradient σ ν x, φ x⟫_ℝ ∂volume := by
  rw [acVariationMeasure, setIntegral_withDensity_eq_setIntegral_toReal_smul
    (Measure.measurable_rnDeriv ν volume) (ae_restrict_of_ae (Measure.rnDeriv_lt_top ν volume))
    _ hU]
  refine setIntegral_congr_fun hU fun x _ ↦ ?_
  rw [approxGradient, real_inner_smul_left, smul_eq_mul]
/-- **Lebesgue–Radon–Nikodym decomposition of the derivative pairing**:
for any `ν`-integrable pairing `x ↦ ⟪σ x, φ x⟫_ℝ` on a measurable set `U`,
`∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν = (∫ x in U, ⟪approxGradient σ ν x, φ x⟫_ℝ ∂volume) +
  ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂(singularVariationMeasure ν)`. -/
theorem setIntegral_inner_eq_ac_add_singular {σ φ : E → E} (ν : Measure E) [SigmaFinite ν]
    [ν.HaveLebesgueDecomposition volume] {U : Set E} (hU : MeasurableSet U)
    (hint : IntegrableOn (fun x ↦ ⟪σ x, φ x⟫_ℝ) U ν) :
    ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν =
      (∫ x in U, ⟪approxGradient σ ν x, φ x⟫_ℝ ∂volume) +
        ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂(singularVariationMeasure ν) := by
  have hdecomp : ν.restrict U =
      (acVariationMeasure ν).restrict U + (singularVariationMeasure ν).restrict U := by
    rw [← Measure.restrict_add, acVariationMeasure_add_singularVariationMeasure]
  rw [IntegrableOn, hdecomp, integrable_add_measure] at hint
  rw [hdecomp, integral_add_measure hint.1 hint.2, setIntegral_inner_acVariationMeasure σ φ ν hU]
/-- **Decomposed distributional integration-by-parts formula**: if `HasDerivativeMeasureOn u U σ ν`
with `ν U ≠ ⊤`, `[SigmaFinite ν]`, and `[ν.HaveLebesgueDecomposition volume]`, then for every
admissible test vector field `φ` on `U`,
`∫ x in U, u x * divergence φ x = -(∫ x in U, ⟪approxGradient σ ν x, φ x⟫_ℝ ∂volume) -
  ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂(singularVariationMeasure ν)`. -/
theorem HasDerivativeMeasureOn.integral_mul_divergence_eq_neg_ac_add_singular
    {u : E → ℝ} {U : Set E} {σ : E → E} {ν : Measure E} [SigmaFinite ν]
    [ν.HaveLebesgueDecomposition volume] (h : HasDerivativeMeasureOn u U σ ν)
    (hU : MeasurableSet U) (hνU : ν U ≠ ⊤) {φ : E → E}
    (hφ : IsSmoothCompactlySupportedOn U φ) :
    ∫ x in U, u x * divergence φ x =
      -(∫ x in U, ⟪approxGradient σ ν x, φ x⟫_ℝ ∂volume) -
        ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂(singularVariationMeasure ν) := by
  rw [h.integral_mul_divergence hφ,
    setIntegral_inner_eq_ac_add_singular ν hU
      (h.integrableOn_inner_of_measure_ne_top hνU hφ.continuous hφ.hasCompactSupport),
    neg_add, sub_eq_add_neg]

end LebesgueRadonNikodymDecomposition

/-! ### Section 3: Weak-gradient (`W¹,¹`) equivalence and purely singular derivative measures -/

section WeakGradientAndSingularSpecialization

/-- Canonical normalized unit direction `unitDirection g x = (‖g x‖)⁻¹ • g x` of a vector field
`g : E → E`. -/
def unitDirection (g : E → E) (x : E) : E := (‖g x‖)⁻¹ • g x
@[simp] theorem unitDirection_zero (x : E) : unitDirection (0 : E → E) x = 0 := by
  simp [unitDirection]
/-- Pointwise norm bound `‖unitDirection g x‖ ≤ 1`. -/
theorem norm_unitDirection_le_one (g : E → E) (x : E) : ‖unitDirection g x‖ ≤ 1 := by
  by_cases hx : g x = 0
  · simp [unitDirection, hx]
  · rw [unitDirection, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
/-- At any point where `g x ≠ 0`, `‖unitDirection g x‖ = 1`. -/
theorem norm_unitDirection_of_ne_zero {g : E → E} {x : E} (hx : g x ≠ 0) :
    ‖unitDirection g x‖ = 1 := by
  rw [unitDirection, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
/-- Polar reconstruction identity `‖g x‖ • unitDirection g x = g x`. -/
@[simp] theorem norm_smul_unitDirection (g : E → E) (x : E) :
    ‖g x‖ • unitDirection g x = g x := by
  by_cases hx : g x = 0
  · simp [unitDirection, hx]
  · rw [unitDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

variable [MeasurableSpace E]

/-- If `g : E → E` is `μ`-a.e. strongly measurable, then `unitDirection g` is `μ`-a.e. strongly
measurable. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.unitDirection {μ : Measure E} {g : E → E}
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (unitDirection g) μ :=
  (measurable_inv.comp_aemeasurable hg.norm.aemeasurable).aestronglyMeasurable.smul hg

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- Predicate asserting that `u : E → ℝ` has **integrable weak gradient** `g : E → E` on
`U : Set E`: `g` is Lebesgue-integrable on `U`, and for every smooth compactly supported test
vector field `φ` on `U`, `x ↦ u x * divergence φ x` is integrable on `U` and satisfies
`∫ x in U, u x * divergence φ x = - ∫ x in U, ⟪g x, φ x⟫_ℝ`. -/
def HasWeakGradientOn (u : E → ℝ) (g : E → E) (U : Set E) : Prop :=
  IntegrableOn g U volume ∧
    ∀ ⦃φ : E → E⦄, IsSmoothCompactlySupportedOn U φ →
      IntegrableOn (fun x ↦ u x * divergence φ x) U volume ∧
        ∫ x in U, u x * divergence φ x = -∫ x in U, ⟪g x, φ x⟫_ℝ
/-- The absolutely continuous variation measure
`gradientVariationMeasure g U = (volume.restrict U).withDensity (fun x ↦ ‖g x‖ₑ)` associated to a
vector field `g : E → E` on `U : Set E`. -/
def gradientVariationMeasure (g : E → E) (U : Set E) : Measure E :=
  (volume.restrict U).withDensity (fun x ↦ ‖g x‖ₑ)
/-- Total mass of `gradientVariationMeasure g U` on `U` is `∫⁻ x in U, ‖g x‖ₑ ∂volume`. -/
theorem gradientVariationMeasure_apply_self (g : E → E) {U : Set E} (hU : MeasurableSet U) :
    gradientVariationMeasure g U U = ∫⁻ x in U, ‖g x‖ₑ ∂volume := by
  rw [gradientVariationMeasure, withDensity_apply _ hU, Measure.restrict_restrict hU, inter_self]
/-- Total mass of `gradientVariationMeasure g U` on `univ` is `∫⁻ x in U, ‖g x‖ₑ ∂volume`. -/
theorem gradientVariationMeasure_apply_univ (g : E → E) (U : Set E) :
    gradientVariationMeasure g U univ = ∫⁻ x in U, ‖g x‖ₑ ∂volume := by
  rw [gradientVariationMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
/-- Restricting `gradientVariationMeasure g U` to a measurable set `U` is idempotent. -/
theorem restrict_gradientVariationMeasure_self (g : E → E) {U : Set E} (hU : MeasurableSet U) :
    (gradientVariationMeasure g U).restrict U = gradientVariationMeasure g U := by
  rw [gradientVariationMeasure, restrict_withDensity hU, Measure.restrict_restrict hU, inter_self]
/-- `gradientVariationMeasure g U` is absolutely continuous with respect to `volume`. -/
theorem absolutelyContinuous_gradientVariationMeasure (g : E → E) (U : Set E) :
    gradientVariationMeasure g U ≪ volume :=
  (withDensity_absolutelyContinuous (volume.restrict U) _).trans
    Measure.restrict_le_self.absolutelyContinuous
/-- The singular part `singularVariationMeasure (gradientVariationMeasure g U)` vanishes whenever
`gradientVariationMeasure g U` admits a Lebesgue decomposition with respect to `volume`. -/
@[simp] theorem singularVariationMeasure_gradientVariationMeasure_eq_zero (g : E → E) (U : Set E)
    [(gradientVariationMeasure g U).HaveLebesgueDecomposition volume] :
    singularVariationMeasure (gradientVariationMeasure g U) = 0 :=
  (singularVariationMeasure_eq_zero_iff _).mpr (absolutelyContinuous_gradientVariationMeasure g U)

namespace HasWeakGradientOn

variable {u : E → ℝ} {g : E → E} {U : Set E}

/-- Integrability of the weak gradient `g` on `U`. -/
theorem integrableOn (h : HasWeakGradientOn u g U) : IntegrableOn g U volume := h.1
/-- Integrability of `x ↦ u x * divergence φ x` on `U` for any admissible test field `φ`. -/
theorem integrableOn_mul_divergence (h : HasWeakGradientOn u g U)
    {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ) :
    IntegrableOn (fun x ↦ u x * divergence φ x) U volume := (h.2 hφ).1
/-- Weak-gradient integration-by-parts identity
`∫ x in U, u x * divergence φ x = - ∫ x in U, ⟪g x, φ x⟫_ℝ`. -/
theorem integral_mul_divergence (h : HasWeakGradientOn u g U)
    {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ) :
    ∫ x in U, u x * divergence φ x = -∫ x in U, ⟪g x, φ x⟫_ℝ := (h.2 hφ).2
/-- When `HasWeakGradientOn u g U`, `gradientVariationMeasure g U U < ⊤`. -/
theorem gradientVariationMeasure_lt_top (h : HasWeakGradientOn u g U) (hU : MeasurableSet U) :
    gradientVariationMeasure g U U < ⊤ := by
  rw [gradientVariationMeasure_apply_self g hU]; exact h.1.2
/-- **Weak-gradient to polar BV representation (`W¹,¹ → BV` with `D^s u = 0`)**:
if `HasWeakGradientOn u g U` on a measurable set `U`, then `u` satisfies
`HasPolarDerivativeMeasureOn u U (unitDirection g) (gradientVariationMeasure g U)`. -/
theorem hasPolarDerivativeMeasureOn (h : HasWeakGradientOn u g U) (hU : MeasurableSet U) :
    HasPolarDerivativeMeasureOn u U (unitDirection g) (gradientVariationMeasure g U) := by
  have hac : (gradientVariationMeasure g U).restrict U ≪ volume.restrict U := by
    rw [restrict_gradientVariationMeasure_self g hU]
    exact withDensity_absolutelyContinuous (volume.restrict U) _
  have hae_unit : ∀ᵐ x ∂(gradientVariationMeasure g U).restrict U, ‖unitDirection g x‖ = 1 := by
    rw [restrict_gradientVariationMeasure_self g hU, gradientVariationMeasure]
    have hmk := h.1.aestronglyMeasurable.enorm
    rw [withDensity_congr_ae hmk.ae_eq_mk, ae_withDensity_iff hmk.measurable_mk]
    filter_upwards [hmk.ae_eq_mk] with x hx hne
    rw [← hx, ne_eq, enorm_eq_zero] at hne
    exact norm_unitDirection_of_ne_zero hne
  refine ⟨⟨h.1.aestronglyMeasurable.unitDirection.mono_ac hac,
    Eventually.of_forall fun x ↦ norm_unitDirection_le_one g x, fun φ hφ ↦ ⟨(h.2 hφ).1, ?_⟩⟩,
    hae_unit⟩
  rw [h.integral_mul_divergence hφ, neg_inj, restrict_gradientVariationMeasure_self g hU,
    gradientVariationMeasure, integral_withDensity_eq_integral_toReal_smul₀
      h.1.aestronglyMeasurable.enorm (Eventually.of_forall fun _ ↦ enorm_lt_top)]
  refine setIntegral_congr_fun hU fun x _ ↦ ?_
  rw [toReal_enorm, smul_eq_mul, ← real_inner_smul_left, norm_smul_unitDirection]
/-- Underlying `HasDerivativeMeasureOn` of `HasWeakGradientOn`. -/
theorem hasDerivativeMeasureOn (h : HasWeakGradientOn u g U) (hU : MeasurableSet U) :
    HasDerivativeMeasureOn u U (unitDirection g) (gradientVariationMeasure g U) :=
  (h.hasPolarDerivativeMeasureOn hU).hasDerivativeMeasureOn

end HasWeakGradientOn

/-- Under `HasDerivativeMeasureOn u U σ ν` and `ν ≪ volume`, `‖approxGradient σ ν x‖ₑ ≤
ν.rnDeriv volume x` for `(volume.restrict U)`-a.e. `x`. -/
theorem HasDerivativeMeasureOn.ae_enorm_approxGradient_le_rnDeriv {u : E → ℝ} {U : Set E}
    {σ : E → E} {ν : Measure E} [SigmaFinite ν] [ν.HaveLebesgueDecomposition volume]
    (h : HasDerivativeMeasureOn u U σ ν) (hU : MeasurableSet U) (hac : ν ≪ volume) :
    ∀ᵐ x ∂(volume.restrict U), ‖approxGradient σ ν x‖ₑ ≤ ν.rnDeriv volume x := by
  have hν_eq : ν.restrict U = (volume.restrict U).withDensity (ν.rnDeriv volume) := by
    rw [← restrict_withDensity hU, Measure.withDensity_rnDeriv_eq ν volume hac]
  have hnorm : ∀ᵐ x ∂(volume.restrict U), ν.rnDeriv volume x ≠ 0 → ‖σ x‖ ≤ 1 := by
    rw [← ae_withDensity_iff (Measure.measurable_rnDeriv ν volume), ← hν_eq]; exact h.ae_norm_le_one
  filter_upwards [ae_restrict_of_ae (Measure.rnDeriv_lt_top ν volume), hnorm] with x htop hx
  by_cases h0 : ν.rnDeriv volume x = 0
  · simp [approxGradient, h0]
  · rw [enorm_approxGradient htop.ne]
    exact (mul_le_mul_right ((ofReal_norm (σ x)).symm ▸ ENNReal.ofReal_le_one.mpr (hx h0))
      (ν.rnDeriv volume x)).trans_eq (mul_one _)
/-- Under `HasPolarDerivativeMeasureOn u U σ ν` and `ν ≪ volume`, `‖approxGradient σ ν x‖ₑ =
ν.rnDeriv volume x` for `(volume.restrict U)`-a.e. `x`. -/
theorem HasPolarDerivativeMeasureOn.ae_enorm_approxGradient_eq_rnDeriv {u : E → ℝ} {U : Set E}
    {σ : E → E} {ν : Measure E} [SigmaFinite ν] [ν.HaveLebesgueDecomposition volume]
    (h : HasPolarDerivativeMeasureOn u U σ ν) (hU : MeasurableSet U) (hac : ν ≪ volume) :
    ∀ᵐ x ∂(volume.restrict U), ‖approxGradient σ ν x‖ₑ = ν.rnDeriv volume x := by
  have hν_eq : ν.restrict U = (volume.restrict U).withDensity (ν.rnDeriv volume) := by
    rw [← restrict_withDensity hU, Measure.withDensity_rnDeriv_eq ν volume hac]
  have hnorm : ∀ᵐ x ∂(volume.restrict U), ν.rnDeriv volume x ≠ 0 → ‖σ x‖ = 1 := by
    rw [← ae_withDensity_iff (Measure.measurable_rnDeriv ν volume), ← hν_eq]; exact h.ae_norm_eq_one
  filter_upwards [ae_restrict_of_ae (Measure.rnDeriv_lt_top ν volume), hnorm] with x htop hx
  by_cases h0 : ν.rnDeriv volume x = 0
  · simp [approxGradient, h0]
  · rw [enorm_approxGradient htop.ne, ← ofReal_norm, hx h0, ENNReal.ofReal_one, mul_one]
/-- Under `HasDerivativeMeasureOn u U σ ν` and `ν ≪ volume`,
`∫⁻ x in U, ‖approxGradient σ ν x‖ₑ ∂volume ≤ ν U`. -/
theorem HasDerivativeMeasureOn.lintegral_enorm_approxGradient_le_of_absolutelyContinuous
    {u : E → ℝ} {U : Set E} {σ : E → E} {ν : Measure E} [SigmaFinite ν]
    [ν.HaveLebesgueDecomposition volume] (h : HasDerivativeMeasureOn u U σ ν)
    (hU : MeasurableSet U) (hac : ν ≪ volume) :
    ∫⁻ x in U, ‖approxGradient σ ν x‖ₑ ∂volume ≤ ν U := by
  calc ∫⁻ x in U, ‖approxGradient σ ν x‖ₑ ∂volume
      ≤ ∫⁻ x in U, ν.rnDeriv volume x ∂volume :=
        lintegral_mono_ae (h.ae_enorm_approxGradient_le_rnDeriv hU hac)
    _ = acVariationMeasure ν U := (acVariationMeasure_apply ν hU).symm
    _ = ν U := by rw [(acVariationMeasure_eq_self_iff ν).mpr hac]
/-- Under `HasPolarDerivativeMeasureOn u U σ ν` and `ν ≪ volume`,
`∫⁻ x in U, ‖approxGradient σ ν x‖ₑ ∂volume = ν U`. -/
theorem HasPolarDerivativeMeasureOn.lintegral_enorm_approxGradient_eq_of_absolutelyContinuous
    {u : E → ℝ} {U : Set E} {σ : E → E} {ν : Measure E} [SigmaFinite ν]
    [ν.HaveLebesgueDecomposition volume] (h : HasPolarDerivativeMeasureOn u U σ ν)
    (hU : MeasurableSet U) (hac : ν ≪ volume) :
    ∫⁻ x in U, ‖approxGradient σ ν x‖ₑ ∂volume = ν U := by
  calc ∫⁻ x in U, ‖approxGradient σ ν x‖ₑ ∂volume
      = ∫⁻ x in U, ν.rnDeriv volume x ∂volume :=
        lintegral_congr_ae (h.ae_enorm_approxGradient_eq_rnDeriv hU hac)
    _ = acVariationMeasure ν U := (acVariationMeasure_apply ν hU).symm
    _ = ν U := by rw [(acVariationMeasure_eq_self_iff ν).mpr hac]
/-- **Converse (`BV` with `D^s u = 0 → W¹,¹`)**: if `HasDerivativeMeasureOn u U σ ν` holds on a
measurable set `U` with `ν ≪ volume`, `ν U < ⊤`, and `AEStronglyMeasurable σ (volume.restrict U)`,
then `HasWeakGradientOn u (approxGradient σ ν) U`. -/
theorem HasDerivativeMeasureOn.hasWeakGradientOn_approxGradient_of_absolutelyContinuous
    {u : E → ℝ} {U : Set E} {σ : E → E} {ν : Measure E} [SigmaFinite ν]
    [ν.HaveLebesgueDecomposition volume] (h : HasDerivativeMeasureOn u U σ ν)
    (hU : MeasurableSet U) (hac : ν ≪ volume) (hνU : ν U < ⊤)
    (hσ : AEStronglyMeasurable σ (volume.restrict U)) :
    HasWeakGradientOn u (approxGradient σ ν) U := by
  have hint : IntegrableOn (approxGradient σ ν) U volume :=
    ⟨(Measure.measurable_rnDeriv ν volume).ennreal_toReal.aestronglyMeasurable.smul hσ,
      (h.lintegral_enorm_approxGradient_le_of_absolutelyContinuous hU hac).trans_lt hνU⟩
  refine ⟨hint, fun φ hφ ↦ ⟨h.integrableOn_mul_divergence hφ, ?_⟩⟩
  rw [h.integral_mul_divergence hφ, ← setIntegral_inner_acVariationMeasure σ φ ν hU,
    (acVariationMeasure_eq_self_iff ν).mpr hac]
/-- **Equivalence between integrable weak gradients (`W¹,¹`) and finite derivative measures with
vanishing singular part (`D^s u = 0`)**: on a measurable set `U`, `u` admits an integrable weak
gradient on `U` iff there exist `σ` and `ν` with `HasDerivativeMeasureOn u U σ ν`,
`singularVariationMeasure ν = 0`, and `ν U < ⊤`. -/
theorem hasWeakGradientOn_iff_exists_derivativeMeasureOn_singular_eq_zero
    {u : E → ℝ} {U : Set E} (hU : MeasurableSet U) :
    (∃ g : E → E, HasWeakGradientOn u g U) ↔
      ∃ (σ : E → E) (ν : Measure E) (_ : SigmaFinite ν) (_ : ν.HaveLebesgueDecomposition volume),
        AEStronglyMeasurable σ (volume.restrict U) ∧ HasDerivativeMeasureOn u U σ ν ∧
        singularVariationMeasure ν = 0 ∧ ν U < ⊤ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    have : IsFiniteMeasure (gradientVariationMeasure g U) :=
      ⟨by rw [gradientVariationMeasure_apply_univ]; exact hg.1.2⟩
    exact ⟨unitDirection g, gradientVariationMeasure g U, inferInstance, inferInstance,
      hg.1.aestronglyMeasurable.unitDirection, hg.hasDerivativeMeasureOn hU,
      singularVariationMeasure_gradientVariationMeasure_eq_zero g U,
      hg.gradientVariationMeasure_lt_top hU⟩
  · rintro ⟨σ, ν, hsf, hld, hσ, h, hsing, hνU⟩
    exact ⟨approxGradient σ ν, h.hasWeakGradientOn_approxGradient_of_absolutelyContinuous hU
      ((singularVariationMeasure_eq_zero_iff ν).mp hsing) hνU hσ⟩
/-- **Purely singular derivative measure characterization (`ν ⟂ₘ volume`)**: when `ν ⟂ₘ volume`,
`acVariationMeasure ν = 0`, `singularVariationMeasure ν = ν`, and `approxGradient σ ν =ᵐ[volume] 0`.
-/
theorem acVariationMeasure_eq_zero_and_singular_eq_self_of_mutuallySingular
    (σ : E → E) (ν : Measure E) [ν.HaveLebesgueDecomposition volume] (hperp : ν ⟂ₘ volume) :
    acVariationMeasure ν = 0 ∧ singularVariationMeasure ν = ν ∧
      approxGradient σ ν =ᵐ[volume] 0 := by
  refine ⟨(acVariationMeasure_eq_zero_iff ν).mpr hperp,
    (singularVariationMeasure_eq_self_iff ν).mpr hperp, ?_⟩
  filter_upwards [(rnDeriv_eq_zero_ae_iff ν).mpr hperp] with x hx; simp [approxGradient, hx]
/-- **Purely singular integration-by-parts specialization**: if `HasDerivativeMeasureOn u U σ ν`
with `ν ⟂ₘ volume`, then the distributional divergence pairing is carried entirely by
`singularVariationMeasure ν`. -/
theorem HasDerivativeMeasureOn.integral_mul_divergence_eq_neg_singular_of_mutuallySingular
    {u : E → ℝ} {U : Set E} {σ : E → E} {ν : Measure E} (h : HasDerivativeMeasureOn u U σ ν)
    (hperp : ν ⟂ₘ volume) {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ) :
    ∫ x in U, u x * divergence φ x = -∫ x in U, ⟪σ x, φ x⟫_ℝ ∂(singularVariationMeasure ν) := by
  rw [h.integral_mul_divergence hφ, (singularVariationMeasure_eq_self_iff ν).mpr hperp]

end WeakGradientAndSingularSpecialization

end TauCeti
