/-
Copyright (c) 2026 General Intelligence, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module
public import TauCeti.MeasureTheory.Measure.GraphPerimeter
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.HalfSpacePerimeter
import all TauCeti.MeasureTheory.Measure.GraphPerimeter
/-!
# Domain BV Boundary Trace, Zero-Extension, Interface Gluing, and Gauss–Green Extensions
This file develops the distributional boundary trace theory for functions of bounded variation on
domains, interior approximate limits, zero-extension and interface gluing across domain boundaries,
subgraph and half-space trace instances, and noncompact-support Gauss–Green extensions.
-/

public section
noncomputable section
open Filter Function MeasureTheory Set Submodule TopologicalSpace TestFunction
open TauCeti.MeasureTheory
open scoped ENNReal NNReal InnerProductSpace Distributions Topology
namespace TauCeti
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Canonical extension of a bundled test function `φ : 𝓓(U, F)` on an open set `U : Opens E` to a
bundled test function on the whole space `(⊤ : Opens E)`. -/
def testFunctionToTop {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Opens E}
    (φ : 𝓓(U, F)) : 𝓓((⊤ : Opens E), F) :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
@[simp]
theorem coe_testFunctionToTop {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Opens E}
    (φ : 𝓓(U, F)) : (testFunctionToTop φ : E → F) = (φ : E → F) := by rfl
@[simp]
theorem testFunctionToTop_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Opens E}
    (φ : 𝓓(U, F)) (x : E) : testFunctionToTop φ x = φ x := by rfl
/-! ### Section 1: Domain BV Boundary Trace, Zero-Extension, and Interior Approximate Limits -/
variable [MeasurableSpace E] {μ σ : Measure E} {Ω Ω' : Set E} {ν_Ω : E → E}
  {u u' v g_u g_u' g_v : E → E → ℝ}
/-- A scalar function `u : E → ℝ` has interior weak gradient density `g_u : E → E` on `Ω : Set E`
and **boundary trace** `Tu : E → ℝ` with respect to a boundary measure `σ : Measure E` and
outward normal field `ν_Ω : E → E` if for every test vector field `φ : 𝓓((⊤ : Opens E), E)`,
`∫ x in Ω, u x * divergence (φ : E → E) x ∂μ =
  -(∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ) + ∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ`. -/
def HasBVTraceOn (μ : Measure E) (Ω : Set E) (σ : Measure E) (ν_Ω : E → E)
    (u : E → ℝ) (g_u : E → E) (Tu : E → ℝ) : Prop :=
  ∀ φ : 𝓓((⊤ : Opens E), E),
    ∫ x in Ω, u x * divergence (φ : E → E) x ∂μ =
      -(∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ) +
        ∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ
variable {u u' v Tu Tu' Tv : E → ℝ} {g_u g_u' g_v : E → E}
theorem HasBVTraceOn.integral_mul_divergence_eq
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) {U : Opens E} (φ : 𝓓(U, E)) :
    ∫ x in Ω, u x * divergence (φ : E → E) x ∂μ =
      -(∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ) +
        ∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ :=
  hu (testFunctionToTop φ)
theorem HasBVTraceOn.zero : HasBVTraceOn μ Ω σ ν_Ω 0 0 0 := by
  intro φ; simp
theorem HasBVTraceOn.congr_ae
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu)
    (hu' : u =ᵐ[μ.restrict Ω] u') (hg' : g_u =ᵐ[μ.restrict Ω] g_u') (hT : Tu =ᵐ[σ] Tu') :
    HasBVTraceOn μ Ω σ ν_Ω u' g_u' Tu' := by
  intro φ
  have h1 : ∫ x in Ω, u' x * divergence (φ : E → E) x ∂μ =
      ∫ x in Ω, u x * divergence (φ : E → E) x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hu'] with x hx
    rw [hx]
  have h2 : ∫ x in Ω, ⟪g_u' x, (φ : E → E) x⟫_ℝ ∂μ =
      ∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hg'] with x hx
    rw [hx]
  have h3 : ∫ x, Tu' x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ =
      ∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ := by
    refine integral_congr_ae ?_
    filter_upwards [hT] with x hx
    rw [hx]
  rw [h1, h2, h3, hu φ]
theorem HasBVTraceOn.congr_trace_ae
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hT : Tu =ᵐ[σ] Tu') :
    HasBVTraceOn μ Ω σ ν_Ω u g_u Tu' :=
  hu.congr_ae EventuallyEq.rfl EventuallyEq.rfl hT
theorem HasBVTraceOn.congr_set_ae
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hΩ : Ω =ᵐ[μ] Ω') :
    HasBVTraceOn μ Ω' σ ν_Ω u g_u Tu := by
  intro φ
  rw [← setIntegral_congr_set hΩ, ← setIntegral_congr_set hΩ, hu φ]
theorem HasBVTraceOn.neg (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) :
    HasBVTraceOn μ Ω σ ν_Ω (-u) (-g_u) (-Tu) := by
  intro φ
  simp only [Pi.neg_apply, neg_mul, inner_neg_left, integral_neg]
  linarith [hu φ]
theorem HasBVTraceOn.const_mul (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (c : ℝ) :
    HasBVTraceOn μ Ω σ ν_Ω (fun x ↦ c * u x) (fun x ↦ c • g_u x) (fun x ↦ c * Tu x) := by
  intro φ
  simp_rw [mul_assoc, inner_smul_left, RCLike.conj_to_real, integral_const_mul]
  linarith [congrArg (c * ·) (hu φ)]
theorem HasBVTraceOn.smul (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (c : ℝ) :
    HasBVTraceOn μ Ω σ ν_Ω (c • u) (c • g_u) (c • Tu) :=
  hu.const_mul c
theorem HasBVTraceOn.add
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hv : HasBVTraceOn μ Ω σ ν_Ω v g_v Tv)
    (hint_u : ∀ φ : 𝓓((⊤ : Opens E), E),
      IntegrableOn (fun x ↦ u x * divergence (φ : E → E) x) Ω μ)
    (hint_v : ∀ φ : 𝓓((⊤ : Opens E), E),
      IntegrableOn (fun x ↦ v x * divergence (φ : E → E) x) Ω μ)
    (hint_gu : ∀ φ : 𝓓((⊤ : Opens E), E), IntegrableOn (fun x ↦ ⟪g_u x, (φ : E → E) x⟫_ℝ) Ω μ)
    (hint_gv : ∀ φ : 𝓓((⊤ : Opens E), E), IntegrableOn (fun x ↦ ⟪g_v x, (φ : E → E) x⟫_ℝ) Ω μ)
    (hint_Tu : ∀ φ : 𝓓((⊤ : Opens E), E), Integrable (fun x ↦ Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ)
    (hint_Tv : ∀ φ : 𝓓((⊤ : Opens E), E), Integrable (fun x ↦ Tv x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ) :
    HasBVTraceOn μ Ω σ ν_Ω (u + v) (g_u + g_v) (Tu + Tv) := by
  intro φ
  simp only [Pi.add_apply, add_mul, inner_add_left]
  rw [integral_add (hint_u φ) (hint_v φ), integral_add (hint_gu φ) (hint_gv φ),
    integral_add (hint_Tu φ) (hint_Tv φ)]
  linarith [hu φ, hv φ]
theorem HasBVTraceOn.sub
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hv : HasBVTraceOn μ Ω σ ν_Ω v g_v Tv)
    (hint_u : ∀ φ : 𝓓((⊤ : Opens E), E),
      IntegrableOn (fun x ↦ u x * divergence (φ : E → E) x) Ω μ)
    (hint_v : ∀ φ : 𝓓((⊤ : Opens E), E),
      IntegrableOn (fun x ↦ v x * divergence (φ : E → E) x) Ω μ)
    (hint_gu : ∀ φ : 𝓓((⊤ : Opens E), E), IntegrableOn (fun x ↦ ⟪g_u x, (φ : E → E) x⟫_ℝ) Ω μ)
    (hint_gv : ∀ φ : 𝓓((⊤ : Opens E), E), IntegrableOn (fun x ↦ ⟪g_v x, (φ : E → E) x⟫_ℝ) Ω μ)
    (hint_Tu : ∀ φ : 𝓓((⊤ : Opens E), E), Integrable (fun x ↦ Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ)
    (hint_Tv : ∀ φ : 𝓓((⊤ : Opens E), E), Integrable (fun x ↦ Tv x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ) :
    HasBVTraceOn μ Ω σ ν_Ω (u - v) (g_u - g_v) (Tu - Tv) := by
  simp only [sub_eq_add_neg]
  refine hu.add hv.neg hint_u (fun φ ↦ ?_) hint_gu (fun φ ↦ ?_) hint_Tu (fun φ ↦ ?_)
  · simpa [Pi.neg_apply, neg_mul] using (hint_v φ).neg
  · simpa [Pi.neg_apply, inner_neg_left] using (hint_gv φ).neg
  · simpa [Pi.neg_apply, neg_mul] using (hint_Tv φ).neg
theorem HasBVTraceOn.integral_indicator_mul_divergence_eq
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hΩ : MeasurableSet Ω) (φ : 𝓓((⊤ : Opens E), E)) :
    ∫ x, Ω.indicator u x * divergence (φ : E → E) x ∂μ =
      -(∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ) +
        ∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ := by
  rw [indicator_mul_eq, integral_indicator hΩ, hu φ]
theorem HasBVTraceOn.setIntegral_indicator_mul_divergence_eq
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hΩ : MeasurableSet Ω) {U : Opens E} (φ : 𝓓(U, E)) :
    ∫ x in (U : Set E), Ω.indicator u x * divergence (φ : E → E) x ∂μ =
      -(∫ x in (U : Set E) ∩ Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ) +
        ∫ x in (U : Set E), Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ := by
  have h0 := hu.integral_indicator_mul_divergence_eq hΩ (testFunctionToTop φ)
  simp only [coe_testFunctionToTop] at h0
  have h1 : ∫ x in (U : Set E) ∩ Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ =
      ∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ :=
    (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hΩ.nullMeasurableSet inter_subset_right
      (Eventually.of_forall fun x ⟨hxΩ, hxU⟩ ↦ by
        simp [φ.zero_on_compl fun h ↦ hxU ⟨h, hxΩ⟩])).symm
  have h2 : ∫ x in (U : Set E), Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ =
      ∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by simp [φ.zero_on_compl hx]
  rw [setIntegral_mul_divergence_eq_integral, h0, h1, h2]
theorem ofReal_abs_setIntegral_inner_le (s : Set E) (g : E → E) {φ : E → E}
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ENNReal.ofReal |∫ x in s, ⟪g x, φ x⟫_ℝ ∂μ| ≤ ∫⁻ x in s, ‖g x‖ₑ ∂μ := by
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x ↦ ?_)
  rw [enorm_le_iff_norm_le, Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hφ x))
theorem ofReal_abs_integral_mul_inner_le (T : E → ℝ) {φ : E → E} (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hν : ∀ᵐ x ∂σ, ‖ν_Ω x‖ ≤ 1) :
    ENNReal.ofReal |∫ x, T x * ⟪φ x, ν_Ω x⟫_ℝ ∂σ| ≤ ∫⁻ x, ‖T x‖ₑ ∂σ := by
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hν] with x hx
  rw [enorm_mul]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
  exact (abs_real_inner_le_norm _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hφ x)).trans hx)
theorem HasBVTraceOn.enorm_integral_trace_le
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hΩ : MeasurableSet Ω)
    (φ : 𝓓((⊤ : Opens E), E)) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ‖ₑ ≤
      distributionalVariation μ ⊤ (Ω.indicator u) + ∫⁻ x in Ω, ‖g_u x‖ₑ ∂μ := by
  set I_var := ∫ x in (⊤ : Opens E), Ω.indicator u x * divergence (φ : E → E) x ∂μ
  set I_grad := ∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ
  set I_bdry := ∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ
  have hpair : I_var = -I_grad + I_bdry := by
    simpa [I_var, I_grad, I_bdry] using hu.integral_indicator_mul_divergence_eq hΩ φ
  have hle : |I_bdry| ≤ |I_var| + |I_grad| := by
    rw [show I_bdry = I_var + I_grad by linarith [hpair]]; exact abs_add_le _ _
  rw [Real.enorm_eq_ofReal_abs]
  refine (ENNReal.ofReal_le_ofReal hle).trans ?_
  rw [ENNReal.ofReal_add (abs_nonneg I_var) (abs_nonneg I_grad)]
  exact add_le_add (abs_le_distributionalVariation φ hφ _)
    (ofReal_abs_setIntegral_inner_le Ω g_u hφ)
theorem HasBVTraceOn.abs_integral_trace_le
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hΩ : MeasurableSet Ω)
    (hvar : distributionalVariation μ ⊤ (Ω.indicator u) ≠ ⊤) (hg : IntegrableOn g_u Ω μ)
    (φ : 𝓓((⊤ : Opens E), E)) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    |∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ| ≤
      (distributionalVariation μ ⊤ (Ω.indicator u)).toReal + ∫ x in Ω, ‖g_u x‖ ∂μ := by
  have hen := hu.enorm_integral_trace_le hΩ φ hφ
  rw [Real.enorm_eq_ofReal_abs, ← ofReal_integral_norm_eq_lintegral_enorm hg] at hen
  exact (ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.add_ne_top.mpr ⟨hvar, ENNReal.ofReal_ne_top⟩)).mp hen |>.trans
    (by rw [ENNReal.toReal_add hvar ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)])
theorem HasBVTraceOn.distributionalVariation_top_indicator_le
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hΩ : MeasurableSet Ω) (hν : ∀ᵐ x ∂σ, ‖ν_Ω x‖ ≤ 1) :
    distributionalVariation μ ⊤ (Ω.indicator u) ≤
      (∫⁻ x in Ω, ‖g_u x‖ₑ ∂μ) + ∫⁻ x, ‖Tu x‖ₑ ∂σ := by
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [setIntegral_mul_divergence_eq_integral, hu.integral_indicator_mul_divergence_eq hΩ φ]
  set I₁ := ∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ
  set I₂ := ∫ x, Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ
  refine (ENNReal.ofReal_le_ofReal (show -I₁ + I₂ ≤ |I₁| + |I₂| by
    linarith [neg_abs_le I₁, le_abs_self I₂])).trans ?_
  rw [ENNReal.ofReal_add (abs_nonneg I₁) (abs_nonneg I₂)]
  exact add_le_add (ofReal_abs_setIntegral_inner_le Ω g_u hφ)
    (ofReal_abs_integral_mul_inner_le Tu hφ hν)
theorem HasBVTraceOn.distributionalVariation_indicator_le
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hΩ : MeasurableSet Ω)
    (hν : ∀ᵐ x ∂σ, ‖ν_Ω x‖ ≤ 1) (U : Opens E) :
    distributionalVariation μ U (Ω.indicator u) ≤
      (∫⁻ x in (U : Set E) ∩ Ω, ‖g_u x‖ₑ ∂μ) + ∫⁻ x in (U : Set E), ‖Tu x‖ₑ ∂σ := by
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [hu.setIntegral_indicator_mul_divergence_eq hΩ φ]
  set I₁ := ∫ x in (U : Set E) ∩ Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ
  set I₂ := ∫ x in (U : Set E), Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ
  refine (ENNReal.ofReal_le_ofReal (show -I₁ + I₂ ≤ |I₁| + |I₂| by
    linarith [neg_abs_le I₁, le_abs_self I₂])).trans ?_
  rw [ENNReal.ofReal_add (abs_nonneg I₁) (abs_nonneg I₂)]
  exact add_le_add (ofReal_abs_setIntegral_inner_le ((U : Set E) ∩ Ω) g_u hφ)
    (ofReal_abs_integral_mul_inner_le Tu hφ (ae_restrict_of_ae hν))
/-- `HasInteriorApproxLimitAt μ Ω u x L` states that `L : ℝ` is the **`L¹` interior approximate
limit** of `u : E → ℝ` on `Ω : Set E` at `x : E`. -/
def HasInteriorApproxLimitAt (μ : Measure E) (Ω : Set E) (u : E → ℝ) (x : E) (L : ℝ) : Prop :=
  Tendsto (fun r ↦ (μ (Ω ∩ Metric.ball x r))⁻¹ *
    ∫⁻ y in Ω ∩ Metric.ball x r, ‖u y - L‖ₑ ∂μ) (𝓝[>] 0) (𝓝 0)
omit [InnerProductSpace ℝ E] in
theorem HasInteriorApproxLimitAt.const (μ : Measure E) (Ω : Set E) (x : E) (c : ℝ) :
    HasInteriorApproxLimitAt μ Ω (fun _ ↦ c) x c := by simp [HasInteriorApproxLimitAt]
omit [InnerProductSpace ℝ E] in
theorem HasInteriorApproxLimitAt.congr_ae {x : E} {L : ℝ}
    (hu : HasInteriorApproxLimitAt μ Ω u x L) (huv : u =ᵐ[μ.restrict Ω] v) :
    HasInteriorApproxLimitAt μ Ω v x L := by
  refine hu.congr fun r ↦ congrArg (_ * ·) (lintegral_congr_ae ?_)
  filter_upwards [huv.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))]
    with y hy
  rw [hy]
omit [InnerProductSpace ℝ E] in
theorem HasInteriorApproxLimitAt.neg {x : E} {L : ℝ} (hu : HasInteriorApproxLimitAt μ Ω u x L) :
    HasInteriorApproxLimitAt μ Ω (-u) x (-L) := by
  refine hu.congr fun r ↦ congrArg (_ * ·) (lintegral_congr fun y ↦ ?_)
  rw [Pi.neg_apply, ← neg_sub, enorm_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
omit [InnerProductSpace ℝ E] in
theorem HasInteriorApproxLimitAt.smul {x : E} {L : ℝ}
    (hu : HasInteriorApproxLimitAt μ Ω u x L) (c : ℝ) :
    HasInteriorApproxLimitAt μ Ω (c • u) x (c • L) := by
  unfold HasInteriorApproxLimitAt
  have h1 (r : ℝ) : (μ (Ω ∩ Metric.ball x r))⁻¹ *
      ∫⁻ y in Ω ∩ Metric.ball x r, ‖(c • u) y - c • L‖ₑ ∂μ =
      ‖c‖ₑ * ((μ (Ω ∩ Metric.ball x r))⁻¹ *
        ∫⁻ y in Ω ∩ Metric.ball x r, ‖u y - L‖ₑ ∂μ) := by
    simp_rw [Pi.smul_apply, ← smul_sub, enorm_smul]
    rw [lintegral_const_mul' _ _ enorm_ne_top, ← mul_assoc, mul_comm _ ‖c‖ₑ, mul_assoc]
  simp_rw [h1]
  simpa using ENNReal.Tendsto.const_mul hu (Or.inr enorm_ne_top)
omit [InnerProductSpace ℝ E] in
theorem HasInteriorApproxLimitAt.add {x : E} {L₁ L₂ : ℝ}
    (hu : HasInteriorApproxLimitAt μ Ω u x L₁) (hv : HasInteriorApproxLimitAt μ Ω v x L₂)
    (hu_meas : AEMeasurable u (μ.restrict Ω)) :
    HasInteriorApproxLimitAt μ Ω (u + v) x (L₁ + L₂) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using Filter.Tendsto.add hu hv) (fun _ ↦ zero_le) fun r ↦ ?_
  rw [← mul_add]
  have hle (y : E) : ‖(u + v) y - (L₁ + L₂)‖ₑ ≤ ‖u y - L₁‖ₑ + ‖v y - L₂‖ₑ := by
    rw [Pi.add_apply, add_sub_add_comm]
    exact enorm_add_le _ _
  have hmeas_r : AEMeasurable (fun y ↦ ‖u y - L₁‖ₑ) (μ.restrict (Ω ∩ Metric.ball x r)) :=
    ((hu_meas.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)).sub_const L₁).enorm
  exact mul_le_mul_of_nonneg_left
    ((lintegral_mono hle).trans (lintegral_add_left' hmeas_r _).le) zero_le
omit [InnerProductSpace ℝ E] in
theorem HasInteriorApproxLimitAt.sub {x : E} {L₁ L₂ : ℝ}
    (hu : HasInteriorApproxLimitAt μ Ω u x L₁) (hv : HasInteriorApproxLimitAt μ Ω v x L₂)
    (hu_meas : AEMeasurable u (μ.restrict Ω)) :
    HasInteriorApproxLimitAt μ Ω (u - v) x (L₁ - L₂) := by
  simpa [sub_eq_add_neg] using hu.add hv.neg hu_meas
omit [InnerProductSpace ℝ E] in
theorem HasInteriorApproxLimitAt.unique {x : E} {L₁ L₂ : ℝ}
    (h₁ : HasInteriorApproxLimitAt μ Ω u x L₁) (h₂ : HasInteriorApproxLimitAt μ Ω u x L₂)
    (hu_meas : AEMeasurable u (μ.restrict Ω))
    (hμ : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ (Ω ∩ Metric.ball x r) ≠ 0 ∧ μ (Ω ∩ Metric.ball x r) ≠ ⊤) :
    L₁ = L₂ := by
  have hlim : Tendsto (fun r ↦
      ((μ (Ω ∩ Metric.ball x r))⁻¹ * ∫⁻ y in Ω ∩ Metric.ball x r, ‖u y - L₁‖ₑ ∂μ) +
      ((μ (Ω ∩ Metric.ball x r))⁻¹ * ∫⁻ y in Ω ∩ Metric.ball x r, ‖u y - L₂‖ₑ ∂μ))
      (𝓝[>] 0) (𝓝 0) := by simpa using Filter.Tendsto.add h₁ h₂
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖L₁ - L₂‖ₑ ≤
      ((μ (Ω ∩ Metric.ball x r))⁻¹ * ∫⁻ y in Ω ∩ Metric.ball x r, ‖u y - L₁‖ₑ ∂μ) +
      ((μ (Ω ∩ Metric.ball x r))⁻¹ * ∫⁻ y in Ω ∩ Metric.ball x r, ‖u y - L₂‖ₑ ∂μ) := by
    filter_upwards [hμ] with r ⟨hr0, hrt⟩
    set s := Ω ∩ Metric.ball x r
    have htri (y : E) : ‖L₁ - L₂‖ₑ ≤ ‖u y - L₁‖ₑ + ‖u y - L₂‖ₑ := by
      rw [show L₁ - L₂ = -(u y - L₁) + (u y - L₂) by ring]
      exact (enorm_add_le _ _).trans (by rw [enorm_neg])
    have hmeas_r : AEMeasurable (fun y ↦ ‖u y - L₁‖ₑ) (μ.restrict s) :=
      ((hu_meas.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)).sub_const L₁).enorm
    have hint := (setLIntegral_const s ‖L₁ - L₂‖ₑ).symm.trans_le
      ((lintegral_mono htri).trans (lintegral_add_left' hmeas_r _).le)
    rw [← mul_add, ← one_mul ‖L₁ - L₂‖ₑ, ← ENNReal.inv_mul_cancel hr0 hrt, mul_assoc,
      mul_comm (μ s) ‖L₁ - L₂‖ₑ]
    exact mul_le_mul_of_nonneg_left hint zero_le
  have h0 : ‖L₁ - L₂‖ₑ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
  exact sub_eq_zero.mp (enorm_eq_zero.mp (le_antisymm h0 zero_le))
theorem inv_mul_mul_self_le (a c : ℝ≥0∞) : a⁻¹ * (c * a) ≤ c := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  · rcases eq_or_ne a ⊤ with rfl | hat
    · simp
    · rw [mul_comm c a, ← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]
omit [InnerProductSpace ℝ E] in
theorem HasInteriorApproxLimitAt.of_continuousWithinAt [OpensMeasurableSpace E] {x : E}
    (hu : ContinuousWithinAt u Ω x) (hΩ : MeasurableSet Ω) :
    HasInteriorApproxLimitAt μ Ω u x (u x) := by
  rw [HasInteriorApproxLimitAt, ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hε_top
  · exact Eventually.of_forall fun _ ↦ le_top
  · have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
    rcases Metric.continuousWithinAt_iff.mp hu ε.toReal hε' with ⟨δ, hδ, hball⟩
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hrδ⟩
    have hbound : ∀ y ∈ Ω ∩ Metric.ball x r, ‖u y - u x‖ₑ ≤ ε := fun y ⟨hyΩ, hyr⟩ ↦ by
      have hd := (hball hyΩ ((Metric.mem_ball.mp hyr).trans hrδ)).le
      rw [Real.dist_eq, ← Real.norm_eq_abs] at hd
      rw [← ENNReal.ofReal_toReal hε_top, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hd
    have hint : ∫⁻ y in Ω ∩ Metric.ball x r, ‖u y - u x‖ₑ ∂μ ≤ ε * μ (Ω ∩ Metric.ball x r) :=
      (setLIntegral_mono' (hΩ.inter measurableSet_ball) hbound).trans_eq
        (setLIntegral_const (Ω ∩ Metric.ball x r) ε)
    exact (mul_le_mul_of_nonneg_left hint zero_le).trans (inv_mul_mul_self_le _ _)
omit [InnerProductSpace ℝ E] in
theorem HasInteriorApproxLimitAt.of_continuousAt [OpensMeasurableSpace E] {x : E}
    (hu : ContinuousAt u x) :
    HasInteriorApproxLimitAt μ Ω u x (u x) := by
  rw [HasInteriorApproxLimitAt, ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hε_top
  · exact Eventually.of_forall fun _ ↦ le_top
  · have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
    rcases Metric.continuousAt_iff.mp hu ε.toReal hε' with ⟨δ, hδ, hball⟩
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hrδ⟩
    have hbound : ∀ y ∈ Metric.ball x r, ‖u y - u x‖ₑ ≤ ε := fun y hyr ↦ by
      have hd := (hball ((Metric.mem_ball.mp hyr).trans hrδ)).le
      rw [Real.dist_eq, ← Real.norm_eq_abs] at hd
      rw [← ENNReal.ofReal_toReal hε_top, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hd
    have hae : ∀ᵐ y ∂μ.restrict (Ω ∩ Metric.ball x r), ‖u y - u x‖ₑ ≤ ε :=
      ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall hbound)).filter_mono
        (ae_mono (Measure.restrict_mono inter_subset_right le_rfl))
    have hint : ∫⁻ y in Ω ∩ Metric.ball x r, ‖u y - u x‖ₑ ∂μ ≤ ε * μ (Ω ∩ Metric.ball x r) :=
      (lintegral_mono_ae hae).trans_eq (setLIntegral_const (Ω ∩ Metric.ball x r) ε)
    exact (mul_le_mul_of_nonneg_left hint zero_le).trans (inv_mul_mul_self_le _ _)
/-! ### Section 2: Interface Gluing, Trace-Matching Extension, and Graph Domain Instances -/
theorem piecewise_eq_indicator_add_indicator_compl {α : Type*} (Ω : Set α)
    [DecidablePred (· ∈ Ω)] (u v : α → ℝ) (x : α) :
    Ω.piecewise u v x = Ω.indicator u x + Ωᶜ.indicator v x := by
  by_cases hx : x ∈ Ω <;> simp [hx]
theorem HasBVTraceOn.integral_piecewise_mul_divergence_eq [DecidablePred (· ∈ Ω)]
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hv : HasBVTraceOn μ Ωᶜ σ (-ν_Ω) v g_v Tv)
    (hΩ : MeasurableSet Ω) (φ : 𝓓((⊤ : Opens E), E))
    (hint_u : IntegrableOn (fun x ↦ u x * divergence (φ : E → E) x) Ω μ)
    (hint_v : IntegrableOn (fun x ↦ v x * divergence (φ : E → E) x) Ωᶜ μ)
    (hint_Tu : Integrable (fun x ↦ Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ)
    (hint_Tv : Integrable (fun x ↦ Tv x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ) :
    ∫ x, Ω.piecewise u v x * divergence (φ : E → E) x ∂μ =
      -(∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ) -
        (∫ x in Ωᶜ, ⟪g_v x, (φ : E → E) x⟫_ℝ ∂μ) +
        ∫ x, (Tu x - Tv x) * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ := by
  have hsplit : (fun x ↦ Ω.piecewise u v x * divergence (φ : E → E) x) =
      fun x ↦ Ω.indicator u x * divergence (φ : E → E) x +
        Ωᶜ.indicator v x * divergence (φ : E → E) x := by
    ext x; rw [piecewise_eq_indicator_add_indicator_compl, add_mul]
  have hint_u' : Integrable (fun x ↦ Ω.indicator u x * divergence (φ : E → E) x) μ := by
    rw [indicator_mul_eq]; exact (integrable_indicator_iff hΩ).mpr hint_u
  have hint_v' : Integrable (fun x ↦ Ωᶜ.indicator v x * divergence (φ : E → E) x) μ := by
    rw [indicator_mul_eq]; exact (integrable_indicator_iff hΩ.compl).mpr hint_v
  have hv_bdry : ∫ x, Tv x * ⟪(φ : E → E) x, (-ν_Ω) x⟫_ℝ ∂σ =
      -∫ x, Tv x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ := by
    simp_rw [Pi.neg_apply, inner_neg_right, mul_neg, integral_neg]
  have hsub_bdry := integral_sub hint_Tu hint_Tv
  simp_rw [← sub_mul] at hsub_bdry
  rw [hsplit, integral_add hint_u' hint_v', hu.integral_indicator_mul_divergence_eq hΩ φ,
    hv.integral_indicator_mul_divergence_eq hΩ.compl φ, hv_bdry]
  linarith [hsub_bdry]
theorem HasBVTraceOn.distributionalVariation_piecewise_le [DecidablePred (· ∈ Ω)]
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hv : HasBVTraceOn μ Ωᶜ σ (-ν_Ω) v g_v Tv)
    (hΩ : MeasurableSet Ω) (hν : ∀ᵐ x ∂σ, ‖ν_Ω x‖ ≤ 1)
    (hint_u : ∀ φ : 𝓓((⊤ : Opens E), E),
      IntegrableOn (fun x ↦ u x * divergence (φ : E → E) x) Ω μ)
    (hint_v : ∀ φ : 𝓓((⊤ : Opens E), E),
      IntegrableOn (fun x ↦ v x * divergence (φ : E → E) x) Ωᶜ μ)
    (hint_Tu : ∀ φ : 𝓓((⊤ : Opens E), E), Integrable (fun x ↦ Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ)
    (hint_Tv : ∀ φ : 𝓓((⊤ : Opens E), E), Integrable (fun x ↦ Tv x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ) :
    distributionalVariation μ ⊤ (Ω.piecewise u v) ≤
      (∫⁻ x in Ω, ‖g_u x‖ₑ ∂μ) + (∫⁻ x in Ωᶜ, ‖g_v x‖ₑ ∂μ) +
        ∫⁻ x, ‖Tu x - Tv x‖ₑ ∂σ := by
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [setIntegral_mul_divergence_eq_integral,
    hu.integral_piecewise_mul_divergence_eq hv hΩ φ (hint_u φ) (hint_v φ) (hint_Tu φ) (hint_Tv φ)]
  set I₁ := ∫ x in Ω, ⟪g_u x, (φ : E → E) x⟫_ℝ ∂μ
  set I₂ := ∫ x in Ωᶜ, ⟪g_v x, (φ : E → E) x⟫_ℝ ∂μ
  set I₃ := ∫ x, (Tu x - Tv x) * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ
  refine (ENNReal.ofReal_le_ofReal (show -I₁ - I₂ + I₃ ≤ |I₁| + |I₂| + |I₃| by
    linarith [neg_abs_le I₁, neg_abs_le I₂, le_abs_self I₃])).trans ?_
  rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg I₁) (abs_nonneg I₂)) (abs_nonneg I₃),
    ENNReal.ofReal_add (abs_nonneg I₁) (abs_nonneg I₂)]
  exact add_le_add
    (add_le_add (ofReal_abs_setIntegral_inner_le Ω g_u hφ)
      (ofReal_abs_setIntegral_inner_le Ωᶜ g_v hφ))
    (ofReal_abs_integral_mul_inner_le (fun x ↦ Tu x - Tv x) hφ hν)
theorem HasBVTraceOn.integral_piecewise_mul_divergence_eq_of_trace_ae_eq
    [DecidablePred (· ∈ Ω)]
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hv : HasBVTraceOn μ Ωᶜ σ (-ν_Ω) v g_v Tv)
    (hΩ : MeasurableSet Ω) (hT : Tu =ᵐ[σ] Tv) (φ : 𝓓((⊤ : Opens E), E))
    (hint_u : IntegrableOn (fun x ↦ u x * divergence (φ : E → E) x) Ω μ)
    (hint_v : IntegrableOn (fun x ↦ v x * divergence (φ : E → E) x) Ωᶜ μ)
    (hint_gu : IntegrableOn (fun x ↦ ⟪g_u x, (φ : E → E) x⟫_ℝ) Ω μ)
    (hint_gv : IntegrableOn (fun x ↦ ⟪g_v x, (φ : E → E) x⟫_ℝ) Ωᶜ μ)
    (hint_Tu : Integrable (fun x ↦ Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ)
    (hint_Tv : Integrable (fun x ↦ Tv x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ) :
    ∫ x, Ω.piecewise u v x * divergence (φ : E → E) x ∂μ =
      -∫ x, ⟪Ω.piecewise g_u g_v x, (φ : E → E) x⟫_ℝ ∂μ := by
  have hbdry0 : ∫ x, (Tu x - Tv x) * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hT] with x hx
    simp [hx]
  have hgrad_split : (fun x ↦ ⟪Ω.piecewise g_u g_v x, (φ : E → E) x⟫_ℝ) =
      fun x ↦ Ω.indicator (fun y ↦ ⟪g_u y, (φ : E → E) y⟫_ℝ) x +
        Ωᶜ.indicator (fun y ↦ ⟪g_v y, (φ : E → E) y⟫_ℝ) x := by
    ext x; by_cases hx : x ∈ Ω <;> simp [hx]
  rw [hu.integral_piecewise_mul_divergence_eq hv hΩ φ hint_u hint_v hint_Tu hint_Tv, hbdry0,
    add_zero, hgrad_split, integral_add ((integrable_indicator_iff hΩ).mpr hint_gu)
      ((integrable_indicator_iff hΩ.compl).mpr hint_gv),
    integral_indicator hΩ, integral_indicator hΩ.compl]
  ring
theorem HasBVTraceOn.distributionalVariation_piecewise_le_of_trace_ae_eq
    [DecidablePred (· ∈ Ω)]
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) (hv : HasBVTraceOn μ Ωᶜ σ (-ν_Ω) v g_v Tv)
    (hΩ : MeasurableSet Ω) (hν : ∀ᵐ x ∂σ, ‖ν_Ω x‖ ≤ 1) (hT : Tu =ᵐ[σ] Tv)
    (hint_u : ∀ φ : 𝓓((⊤ : Opens E), E),
      IntegrableOn (fun x ↦ u x * divergence (φ : E → E) x) Ω μ)
    (hint_v : ∀ φ : 𝓓((⊤ : Opens E), E),
      IntegrableOn (fun x ↦ v x * divergence (φ : E → E) x) Ωᶜ μ)
    (hint_Tu : ∀ φ : 𝓓((⊤ : Opens E), E), Integrable (fun x ↦ Tu x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ)
    (hint_Tv : ∀ φ : 𝓓((⊤ : Opens E), E), Integrable (fun x ↦ Tv x * ⟪(φ : E → E) x, ν_Ω x⟫_ℝ) σ) :
    distributionalVariation μ ⊤ (Ω.piecewise u v) ≤
      (∫⁻ x in Ω, ‖g_u x‖ₑ ∂μ) + ∫⁻ x in Ωᶜ, ‖g_v x‖ₑ ∂μ := by
  have h0 : ∫⁻ x, ‖Tu x - Tv x‖ₑ ∂σ = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hT] with x hx
    simp [hx]
  simpa [h0] using
    hu.distributionalVariation_piecewise_le hv hΩ hν hint_u hint_v hint_Tu hint_Tv
section GraphInstances
variable [FiniteDimensional ℝ E] [BorelSpace E] {e : E} {f : orthogonalHyperplane e → ℝ}
/-- Pushforward of `volume` on `orthogonalHyperplane e` along `graphPoint e f` to `E`. -/
def graphPointMeasure (e : E) (f : orthogonalHyperplane e → ℝ) : Measure E :=
  Measure.map (graphPoint e f) volume
/-- Extension of the unnormalized graph normal `graphNormalVec e f` to `E` via orthogonal
projection onto `orthogonalHyperplane e`. -/
def graphNormalVecOn (e : E) (f : orthogonalHyperplane e → ℝ) (x : E) : E :=
  graphNormalVec e f ((orthogonalHyperplane e).orthogonalProjectionOnto x)
/-- Pushforward of `volume` on `orthogonalHyperplane e` along `hyperplanePoint e a` to `E`. -/
def hyperplaneMeasure (e : E) (a : ℝ) : Measure E :=
  Measure.map (hyperplanePoint e a) volume
@[simp]
theorem graphPointMeasure_const (e : E) (a : ℝ) :
    graphPointMeasure e (fun _ ↦ a) = hyperplaneMeasure e a := by rfl
omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem graphNormalVecOn_graphPoint (e : E) (f : orthogonalHyperplane e → ℝ)
    (y : orthogonalHyperplane e) :
    graphNormalVecOn e f (graphPoint e f y) = graphNormalVec e f y := by
  simp [graphNormalVecOn]
omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem graphNormalVecOn_const (e : E) (a : ℝ) :
    graphNormalVecOn e (fun _ ↦ a) = fun _ ↦ e := by
  ext x; simp [graphNormalVecOn]
omit [InnerProductSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem neg_const_fun (e : E) : (-fun _ : E ↦ e) = fun _ ↦ -e := by
  ext; simp
omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_graphNormalVec (hf : ContDiff ℝ 1 f) :
    Continuous (graphNormalVec e f) := by
  have hgrad : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (orthogonalHyperplane e)).symm.continuous.comp
      (hf.continuous_fderiv one_ne_zero)
  exact ((orthogonalHyperplane e).subtypeL.continuous.comp hgrad.neg).add continuous_const
omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_graphNormalVecOn (hf : ContDiff ℝ 1 f) :
    Continuous (graphNormalVecOn e f) :=
  (continuous_graphNormalVec hf).comp (orthogonalHyperplane e).orthogonalProjectionOnto.continuous
theorem integral_graphPointMeasure_mul_inner (hf : ContDiff ℝ 1 f)
    {w : E → ℝ} (hw : Continuous w) {ψ : E → E} (hψ : Continuous ψ) :
    ∫ x, w x * ⟪ψ x, graphNormalVecOn e f x⟫_ℝ ∂(graphPointMeasure e f) =
      ∫ y, w (graphPoint e f y) * ⟪ψ (graphPoint e f y), graphNormalVec e f y⟫_ℝ := by
  have hcont : Continuous (fun x : E ↦ w x * ⟪ψ x, graphNormalVecOn e f x⟫_ℝ) :=
    hw.mul (hψ.inner (continuous_graphNormalVecOn hf))
  rw [graphPointMeasure,
    integral_map (continuous_graphPoint e hf.continuous).aemeasurable hcont.aestronglyMeasurable]
  simp_rw [graphNormalVecOn_graphPoint]
theorem hasBVTraceOn_subgraphOn (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) (hu : ContDiff ℝ 1 u) :
    HasBVTraceOn volume (subgraphOn e f) (graphPointMeasure e f) (graphNormalVecOn e f)
      u (gradient u) u := by
  intro φ
  rw [integral_subgraphOn_mul_divergence_eq he hf hu φ,
    integral_graphPointMeasure_mul_inner hf hu.continuous φ.continuous]
theorem hasBVTraceOn_subgraphLEOn (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) (hu : ContDiff ℝ 1 u) :
    HasBVTraceOn volume (subgraphLEOn e f) (graphPointMeasure e f) (graphNormalVecOn e f)
      u (gradient u) u :=
  (hasBVTraceOn_subgraphOn he hf hu).congr_set_ae
    (subgraphOn_ae_eq_subgraphLEOn he hf.continuous.measurable)
theorem hasBVTraceOn_epigraphOn (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) (hu : ContDiff ℝ 1 u) :
    HasBVTraceOn volume (epigraphOn e f) (graphPointMeasure e f) (-graphNormalVecOn e f)
      u (gradient u) u := by
  intro φ
  have hneg : ∫ x, u x * ⟪(φ : E → E) x, (-graphNormalVecOn e f) x⟫_ℝ ∂(graphPointMeasure e f) =
      -∫ y, u (graphPoint e f y) * ⟪φ (graphPoint e f y), graphNormalVec e f y⟫_ℝ := by
    simp_rw [Pi.neg_apply, inner_neg_right, mul_neg, integral_neg]
    rw [integral_graphPointMeasure_mul_inner hf hu.continuous φ.continuous]
  rw [integral_epigraphOn_mul_divergence_eq he hf hu φ, hneg, sub_eq_add_neg]
theorem hasBVTraceOn_halfSpaceLT (he : ‖e‖ = 1) (a : ℝ) (hu : ContDiff ℝ 1 u) :
    HasBVTraceOn volume (halfSpaceLT e a) (hyperplaneMeasure e a) (fun _ ↦ e) u (gradient u) u := by
  simpa using hasBVTraceOn_subgraphOn he (f := fun _ ↦ a) contDiff_const hu
theorem hasBVTraceOn_halfSpaceGT (he : ‖e‖ = 1) (a : ℝ) (hu : ContDiff ℝ 1 u) :
    HasBVTraceOn volume (halfSpaceGT e a) (hyperplaneMeasure e a) (fun _ ↦ -e)
      u (gradient u) u := by
  simpa [neg_const_fun] using
    hasBVTraceOn_epigraphOn he (f := fun _ ↦ a) contDiff_const hu
theorem piecewise_subgraphOn_ae_eq_add_indicator (he : ‖e‖ = 1) (hf : Measurable f)
    [DecidablePred (· ∈ subgraphOn e f)] (u₁ u₂ : E → ℝ) :
    (subgraphOn e f).piecewise u₁ u₂ =ᵐ[volume]
      fun x ↦ (subgraphOn e f).indicator u₁ x + (epigraphOn e f).indicator u₂ x := by
  filter_upwards [compl_mem_ae_iff.mpr (volume_graphOn he hf)] with x hx
  rcases lt_trichotomy ⟪x, e⟫_ℝ (f ((orthogonalHyperplane e).orthogonalProjectionOnto x)) with
    hlt | heq | hgt
  · simp [mem_subgraphOn.mpr hlt, show x ∉ epigraphOn e f from not_lt.mpr hlt.le]
  · exact False.elim (hx heq)
  · simp [show x ∉ subgraphOn e f from not_lt.mpr hgt.le, mem_epigraphOn.mpr hgt]
theorem integral_piecewise_subgraphOn_mul_divergence_eq (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f)
    [DecidablePred (· ∈ subgraphOn e f)] {u₁ u₂ : E → ℝ}
    (hu₁ : ContDiff ℝ 1 u₁) (hu₂ : ContDiff ℝ 1 u₂) {U : Opens E} (Φ : 𝓓(U, E)) :
    ∫ x in (U : Set E), (subgraphOn e f).piecewise u₁ u₂ x * divergence (Φ : E → E) x =
      -(∫ x in (U : Set E) ∩ subgraphOn e f, ⟪gradient u₁ x, Φ x⟫_ℝ) -
        (∫ x in (U : Set E) ∩ epigraphOn e f, ⟪gradient u₂ x, Φ x⟫_ℝ) +
        ∫ y in graphSlice e f U,
          (u₁ (graphPoint e f y) - u₂ (graphPoint e f y)) *
            ⟪Φ (graphPoint e f y), graphNormalVec e f y⟫_ℝ := by
  have hae : (fun x ↦ (subgraphOn e f).piecewise u₁ u₂ x * divergence (Φ : E → E) x) =ᵐ[volume]
      fun x ↦ (subgraphOn e f).indicator u₁ x * divergence (Φ : E → E) x +
        (epigraphOn e f).indicator u₂ x * divergence (Φ : E → E) x := by
    filter_upwards [piecewise_subgraphOn_ae_eq_add_indicator he hf.continuous.measurable u₁ u₂]
      with x hx
    rw [hx, add_mul]
  have hint (w : E → ℝ) (hw : ContDiff ℝ 1 w) (s : Set E) (hs : MeasurableSet s) :
      Integrable (fun x ↦ s.indicator w x * divergence (Φ : E → E) x) volume := by
    rw [indicator_mul_eq]
    have h1 := hw.continuous.mul (continuous_divergence_testFunction Φ)
    exact (h1.integrable_of_hasCompactSupport
      ((hasCompactSupport_divergence_testFunction Φ).smul_left (f := w))).indicator hs
  have hbdry_int (w : E → ℝ) (hw : ContDiff ℝ 1 w) :
      IntegrableOn
        (fun y ↦ w (graphPoint e f y) * ⟪Φ (graphPoint e f y), graphNormalVec e f y⟫_ℝ)
        (graphSlice e f U) volume := by
    have hcont : Continuous
        (fun y ↦ w (graphPoint e f y) * ⟪Φ (graphPoint e f y), graphNormalVec e f y⟫_ℝ) :=
      (hw.continuous.comp (continuous_graphPoint e hf.continuous)).mul
        ((Φ.continuous.comp (continuous_graphPoint e hf.continuous)).inner
          (continuous_graphNormalVec hf))
    exact (hcont.integrable_of_hasCompactSupport
      (hasCompactSupport_graphComp Φ.hasCompactSupport f fun _ h0 ↦ by simp [graphPoint, h0]))
      |>.integrableOn
  have hsub_bdry := integral_sub (hbdry_int u₁ hu₁) (hbdry_int u₂ hu₂)
  simp_rw [← sub_mul] at hsub_bdry
  rw [setIntegral_congr_ae U.isOpen.measurableSet (hae.mono fun _ hx _ ↦ hx),
    integral_add (hint u₁ hu₁ _ (measurableSet_subgraphOn e hf.continuous.measurable)).integrableOn
      (hint u₂ hu₂ _ (measurableSet_epigraphOn e hf.continuous.measurable)).integrableOn,
    setIntegral_mul_divergence_eq_integral, setIntegral_mul_divergence_eq_integral,
    indicator_mul_eq, indicator_mul_eq,
    integral_indicator (measurableSet_subgraphOn e hf.continuous.measurable),
    integral_indicator (measurableSet_epigraphOn e hf.continuous.measurable),
    integral_subgraphOn_mul_divergence_eq he hf hu₁ Φ,
    integral_epigraphOn_mul_divergence_eq he hf hu₂ Φ,
    setIntegral_inter_inner_gradient (measurableSet_subgraphOn e hf.continuous.measurable) u₁ Φ,
    setIntegral_inter_inner_gradient (measurableSet_epigraphOn e hf.continuous.measurable) u₂ Φ,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := graphSlice e f U)
      (f := fun y ↦ u₁ (graphPoint e f y) * ⟪Φ (graphPoint e f y), graphNormalVec e f y⟫_ℝ)
      (fun y hy ↦ by simp [Φ.zero_on_compl hy]),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := graphSlice e f U)
      (f := fun y ↦ u₂ (graphPoint e f y) * ⟪Φ (graphPoint e f y), graphNormalVec e f y⟫_ℝ)
      (fun y hy ↦ by simp [Φ.zero_on_compl hy])]
  linarith [hsub_bdry]
end GraphInstances
/-! ### Section 3: Gauss–Green Domains, Smooth Trace Agreement, and Noncompact Extensions -/
/-- A domain `Ω : Set E` with boundary measure `σ : Measure E` and outward normal field
`ν_Ω : E → E` **satisfies the Gauss–Green formula** (`SatisfiesGaussGreenOn μ Ω σ ν_Ω`) if for
every test vector field `φ : 𝓓((⊤ : Opens E), E)`,
`∫ x in Ω, divergence (φ : E → E) x ∂μ = ∫ x, ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ`. -/
def SatisfiesGaussGreenOn (μ : Measure E) (Ω : Set E) (σ : Measure E) (ν_Ω : E → E) : Prop :=
  ∀ φ : 𝓓((⊤ : Opens E), E),
    ∫ x in Ω, divergence (φ : E → E) x ∂μ = ∫ x, ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ
theorem satisfiesGaussGreenOn_iff_hasBVTraceOn_one :
    SatisfiesGaussGreenOn μ Ω σ ν_Ω ↔
      HasBVTraceOn μ Ω σ ν_Ω (fun _ ↦ 1) (fun _ ↦ 0) (fun _ ↦ 1) := by
  simp [SatisfiesGaussGreenOn, HasBVTraceOn]
theorem SatisfiesGaussGreenOn.hasBVTraceOn_one (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω) :
    HasBVTraceOn μ Ω σ ν_Ω (fun _ ↦ 1) (fun _ ↦ 0) (fun _ ↦ 1) :=
  satisfiesGaussGreenOn_iff_hasBVTraceOn_one.mp hgg
theorem SatisfiesGaussGreenOn.hasBVTraceOn_const (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω)
    (c : ℝ) :
    HasBVTraceOn μ Ω σ ν_Ω (fun _ ↦ c) (fun _ ↦ 0) (fun _ ↦ c) := by
  simpa using hgg.hasBVTraceOn_one.const_mul c
theorem SatisfiesGaussGreenOn.integral_divergence_eq
    (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω) {U : Opens E} (φ : 𝓓(U, E)) :
    ∫ x in Ω, divergence (φ : E → E) x ∂μ = ∫ x, ⟪(φ : E → E) x, ν_Ω x⟫_ℝ ∂σ :=
  hgg (testFunctionToTop φ)
theorem SatisfiesGaussGreenOn.hasBVTraceOn_of_contDiff
    [FiniteDimensional ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts μ]
    (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω) (hu : ContDiff ℝ ⊤ u) :
    HasBVTraceOn μ Ω σ ν_Ω u (gradient u) u := by
  intro φ
  have h1 : Integrable (fun x ↦ u x * divergence (φ : E → E) x) μ :=
    ((hu.continuous.mul (continuous_divergence_testFunction φ)).integrable_of_hasCompactSupport
      ((hasCompactSupport_divergence_testFunction φ).smul_left (f := u)))
  have hgrad : Continuous (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      ((hu.of_le le_top).continuous_fderiv one_ne_zero)
  have h2 : Integrable (fun x ↦ ⟪gradient u x, (φ : E → E) x⟫_ℝ) μ :=
    (hgrad.inner φ.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact φ.hasCompactSupport.isCompact
        fun x hx ↦ subset_tsupport φ fun h0 ↦ hx (by simp [h0]))
  have hdiv : (fun x ↦ divergence (smulTestFunction hu φ : E → E) x) =
      fun x ↦ u x * divergence (φ : E → E) x + ⟪gradient u x, (φ : E → E) x⟫_ℝ :=
    funext fun x ↦ divergence_smul_eq_add_inner_gradient
      ((hu.of_le le_top).differentiable one_ne_zero x)
      (φ.contDiff.differentiable (by simp) x)
  have hgg_smul := hgg (smulTestFunction hu φ)
  simp_rw [hdiv, smulTestFunction_apply, inner_smul_left, RCLike.conj_to_real] at hgg_smul
  rw [integral_add h1.integrableOn h2.integrableOn] at hgg_smul
  linarith [hgg_smul]
theorem SatisfiesGaussGreenOn.relativePerimeter_le
    (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω) (hΩ : MeasurableSet Ω)
    (hν : ∀ᵐ x ∂σ, ‖ν_Ω x‖ ≤ 1) (U : Opens E) :
    relativePerimeter μ U Ω ≤ σ U := by
  simpa [relativePerimeter, Measure.restrict_apply_univ] using
    hgg.hasBVTraceOn_one.distributionalVariation_indicator_le hΩ hν U
theorem SatisfiesGaussGreenOn.perimeter_le
    (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω) (hΩ : MeasurableSet Ω) (hν : ∀ᵐ x ∂σ, ‖ν_Ω x‖ ≤ 1) :
    perimeter μ Ω ≤ σ univ := by
  simpa [perimeter] using hgg.relativePerimeter_le hΩ hν ⊤
theorem SatisfiesGaussGreenOn.toReal_relativePerimeter_le
    (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω) (hΩ : MeasurableSet Ω)
    (hν : ∀ᵐ x ∂σ, ‖ν_Ω x‖ ≤ 1) (U : Opens E) (hfin : σ U ≠ ⊤) :
    (relativePerimeter μ U Ω).toReal ≤ (σ U).toReal :=
  ENNReal.toReal_mono hfin (hgg.relativePerimeter_le hΩ hν U)
section GraphGaussGreen
variable [FiniteDimensional ℝ E] [BorelSpace E] {e : E} {f : orthogonalHyperplane e → ℝ}
theorem satisfiesGaussGreenOn_subgraphOn (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) :
    SatisfiesGaussGreenOn volume (subgraphOn e f) (graphPointMeasure e f)
      (graphNormalVecOn e f) := by
  rw [satisfiesGaussGreenOn_iff_hasBVTraceOn_one]
  simpa using hasBVTraceOn_subgraphOn he hf (u := fun _ ↦ 1) contDiff_const
theorem satisfiesGaussGreenOn_subgraphLEOn (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) :
    SatisfiesGaussGreenOn volume (subgraphLEOn e f) (graphPointMeasure e f)
      (graphNormalVecOn e f) := by
  rw [satisfiesGaussGreenOn_iff_hasBVTraceOn_one]
  simpa using hasBVTraceOn_subgraphLEOn he hf (u := fun _ ↦ 1) contDiff_const
theorem satisfiesGaussGreenOn_epigraphOn (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) :
    SatisfiesGaussGreenOn volume (epigraphOn e f) (graphPointMeasure e f)
      (-graphNormalVecOn e f) := by
  rw [satisfiesGaussGreenOn_iff_hasBVTraceOn_one]
  simpa using hasBVTraceOn_epigraphOn he hf (u := fun _ ↦ 1) contDiff_const
theorem satisfiesGaussGreenOn_halfSpaceLT (he : ‖e‖ = 1) (a : ℝ) :
    SatisfiesGaussGreenOn volume (halfSpaceLT e a) (hyperplaneMeasure e a) (fun _ ↦ e) := by
  simpa using satisfiesGaussGreenOn_subgraphOn he (f := fun _ ↦ a) contDiff_const
theorem satisfiesGaussGreenOn_halfSpaceGT (he : ‖e‖ = 1) (a : ℝ) :
    SatisfiesGaussGreenOn volume (halfSpaceGT e a) (hyperplaneMeasure e a) (fun _ ↦ -e) := by
  simpa [neg_const_fun] using satisfiesGaussGreenOn_epigraphOn he (f := fun _ ↦ a) contDiff_const
end GraphGaussGreen
theorem SatisfiesGaussGreenOn.integral_divergence_eq_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω) {V : E → E} {φ : ι → 𝓓((⊤ : Opens E), E)}
    (hdiv : Tendsto (fun k ↦ ∫ x in Ω, divergence (φ k : E → E) x ∂μ) l
      (𝓝 (∫ x in Ω, divergence V x ∂μ)))
    (hbdry : Tendsto (fun k ↦ ∫ x, ⟪(φ k : E → E) x, ν_Ω x⟫_ℝ ∂σ) l
      (𝓝 (∫ x, ⟪V x, ν_Ω x⟫_ℝ ∂σ))) :
    ∫ x in Ω, divergence V x ∂μ = ∫ x, ⟪V x, ν_Ω x⟫_ℝ ∂σ :=
  tendsto_nhds_unique (hdiv.congr fun k ↦ hgg (φ k)) hbdry
theorem SatisfiesGaussGreenOn.integral_divergence_eq_of_dominated
    (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω) {V : E → E} {φ : ℕ → 𝓓((⊤ : Opens E), E)}
    {bound_div bound_bdry : E → ℝ}
    (hmeas_div : ∀ k, AEStronglyMeasurable (divergence (φ k : E → E)) (μ.restrict Ω))
    (hmeas_bdry : ∀ k, AEStronglyMeasurable (fun x ↦ ⟪(φ k : E → E) x, ν_Ω x⟫_ℝ) σ)
    (hint_div : IntegrableOn bound_div Ω μ) (hint_bdry : Integrable bound_bdry σ)
    (hdom_div : ∀ k, ∀ᵐ x ∂μ.restrict Ω, ‖divergence (φ k : E → E) x‖ ≤ bound_div x)
    (hdom_bdry : ∀ k, ∀ᵐ x ∂σ, ‖⟪(φ k : E → E) x, ν_Ω x⟫_ℝ‖ ≤ bound_bdry x)
    (hlim_div : ∀ᵐ x ∂μ.restrict Ω,
      Tendsto (fun k ↦ divergence (φ k : E → E) x) atTop (𝓝 (divergence V x)))
    (hlim_bdry : ∀ᵐ x ∂σ,
      Tendsto (fun k ↦ ⟪(φ k : E → E) x, ν_Ω x⟫_ℝ) atTop (𝓝 ⟪V x, ν_Ω x⟫_ℝ)) :
    ∫ x in Ω, divergence V x ∂μ = ∫ x, ⟪V x, ν_Ω x⟫_ℝ ∂σ :=
  hgg.integral_divergence_eq_of_tendsto
    (tendsto_integral_of_dominated_convergence bound_div hmeas_div hint_div hdom_div hlim_div)
    (tendsto_integral_of_dominated_convergence bound_bdry hmeas_bdry hint_bdry hdom_bdry hlim_bdry)
/-- Bundled compactly supported test vector field `x ↦ η x • V x` obtained by multiplying a smooth
vector field `V : E → E` (not necessarily compactly supported) by a scalar cutoff test function
`η : 𝓓((⊤ : Opens E), ℝ)`. -/
def cutoffTestVectorField {V : E → E} (hV : ContDiff ℝ ⊤ V)
    (η : 𝓓((⊤ : Opens E), ℝ)) : 𝓓((⊤ : Opens E), E) where
  toFun x := η x • V x
  contDiff' := η.contDiff.smul (hV.of_le le_top)
  hasCompactSupport' := η.hasCompactSupport.smul_right
  tsupport_subset' := subset_univ _
omit [MeasurableSpace E] in
@[simp]
theorem cutoffTestVectorField_apply {V : E → E} (hV : ContDiff ℝ ⊤ V)
    (η : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    cutoffTestVectorField hV η x = η x • V x := by rfl
omit [MeasurableSpace E] in
theorem divergence_cutoffTestVectorField [FiniteDimensional ℝ E] {V : E → E} (hV : ContDiff ℝ ⊤ V)
    (η : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    divergence (cutoffTestVectorField hV η : E → E) x =
      η x * divergence V x + ⟪gradient (η : E → ℝ) x, V x⟫_ℝ :=
  divergence_smul_eq_add_inner_gradient (η.contDiff.differentiable (by simp) x)
    (hV.differentiable (by simp) x)
theorem SatisfiesGaussGreenOn.integral_divergence_eq_of_cutoff
    (hgg : SatisfiesGaussGreenOn μ Ω σ ν_Ω) {V : E → E} (hV : ContDiff ℝ ⊤ V)
    {η : ℕ → 𝓓((⊤ : Opens E), ℝ)}
    (hdiv : Tendsto (fun k ↦ ∫ x in Ω, divergence (cutoffTestVectorField hV (η k) : E → E) x ∂μ)
      atTop (𝓝 (∫ x in Ω, divergence V x ∂μ)))
    (hbdry : Tendsto (fun k ↦ ∫ x, ⟪(cutoffTestVectorField hV (η k) : E → E) x, ν_Ω x⟫_ℝ ∂σ)
      atTop (𝓝 (∫ x, ⟪V x, ν_Ω x⟫_ℝ ∂σ))) :
    ∫ x in Ω, divergence V x ∂μ = ∫ x, ⟪V x, ν_Ω x⟫_ℝ ∂σ :=
  hgg.integral_divergence_eq_of_tendsto hdiv hbdry
theorem HasBVTraceOn.integral_mul_divergence_eq_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (hu : HasBVTraceOn μ Ω σ ν_Ω u g_u Tu) {V : E → E} {φ : ι → 𝓓((⊤ : Opens E), E)}
    (hdiv : Tendsto (fun k ↦ ∫ x in Ω, u x * divergence (φ k : E → E) x ∂μ) l
      (𝓝 (∫ x in Ω, u x * divergence V x ∂μ)))
    (hgrad : Tendsto (fun k ↦ ∫ x in Ω, ⟪g_u x, (φ k : E → E) x⟫_ℝ ∂μ) l
      (𝓝 (∫ x in Ω, ⟪g_u x, V x⟫_ℝ ∂μ)))
    (hbdry : Tendsto (fun k ↦ ∫ x, Tu x * ⟪(φ k : E → E) x, ν_Ω x⟫_ℝ ∂σ) l
      (𝓝 (∫ x, Tu x * ⟪V x, ν_Ω x⟫_ℝ ∂σ))) :
    ∫ x in Ω, u x * divergence V x ∂μ =
      -(∫ x in Ω, ⟪g_u x, V x⟫_ℝ ∂μ) + ∫ x, Tu x * ⟪V x, ν_Ω x⟫_ℝ ∂σ :=
  tendsto_nhds_unique (hdiv.congr fun k ↦ hu (φ k)) (hgrad.neg.add hbdry)
end TauCeti
