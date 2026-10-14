/-
Copyright (c) 2026 General Intelligence Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.Fourier.RectifiableArea

/-!
# Euclidean Invariance, Multi-Traversed Circles, and Ellipses for Rectifiable Signed Area

This file develops the smooth/AC bridge and Euclidean invariance theory for `arcLengthReparam` and
`rectifiableSignedArea`, followed by two canonical families of model curves for the planar
isoperimetric theory (`Isoperimetry` Milestones I3 and I6) and one-dimensional Hausdorff
multiplicity theory (`GeometricMeasureTheory`):

1. **Continuous-speed AC agreement and Euclidean similarity laws**:
   * `rectifiableSignedArea_eq_signedAreaEuclidean_of_continuousOn_norm_deriv`: for any closed
     absolutely continuous curve `γ : ℝ → EuclideanSpace ℝ (Fin 2)` on `[a, b]` (`a ≤ b`) with
     continuous speed `ContinuousOn (fun t ↦ ‖deriv γ t‖) (Icc a b)`, the geometric signed area
     `rectifiableSignedArea γ a b` (defined via `arcLengthReparam`) coincides with the classical
     coordinate integral `signedAreaEuclidean γ a (b - a)`.
   * `Isometry` invariance of `eVariationOn`, `variationOnFromTo`, `arcLengthInv`, and
     `arcLengthReparam`, together with translation invariance (`rectifiableSignedArea_add_const`,
     `rectifiableSignedArea_const_add`) and coordinate-swap orientation reversal
     (`rectifiableSignedArea_swap`) for `rectifiableSignedArea`.

2. **Multi-traversed circles `multiCircleCurve c r m` and `twiceCircleCurve c r`**:
   * `multiCircleCurve c r m t = circleCurve c r ((m : ℝ) * t)` traverses `Metric.sphere c r`
     `m` times on `[0, 2π]` at constant speed `m * |r|`.
   * For `0 < r` and `1 ≤ m`, its trace is `Metric.sphere c r`, its 1D Hausdorff measure is
     `2πr` (independent of `m`), its fiber multiplicity on `Ico 0 (2 * π)` is constantly `m` on
     `Metric.sphere c r`, its total variation on `[0, 2π]` is `2πmr`, its canonical unit-speed
     reparametrization is `s ↦ circleCurve c r (s / r)` on `[0, 2πmr]`, and its signed area is
     `m * π * r ^ 2`.
   * Its length–area isoperimetric deficit is `4 * π ^ 2 * r ^ 2 * m * (m - 1)`, yielding strict
     Hurwitz inequality `4 * π * |rectifiableSignedArea| < (eVariationOn).toReal ^ 2` for `2 ≤ m`
     while simultaneously showing that unweighted Hausdorff trace length satisfies the opposite
     strict inequality `(μHE[1] (trace)).toReal ^ 2 < 4 * π * |rectifiableSignedArea|`.

3. **Parametrized ellipses `ellipseCurve c a b`**:
   * `ellipseCurve c a b t = c + !₂[a * cos t, b * sin t]` is a simple closed smooth curve on
     `[0, 2π]` for `a ≠ 0`, `b ≠ 0`, with trace
     `{p | ((p 0 - c 0) / a) ^ 2 + ((p 1 - c 1) / b) ^ 2 = 1}`, kinetic energy
     `π * (a ^ 2 + b ^ 2)`, and signed area
     `rectifiableSignedArea (ellipseCurve c a b) 0 (2 * π) = π * a * b`.
   * `exists_sphere_trace_ellipseCurve_iff`: for `0 < a` and `0 < b`, the trace of
     `ellipseCurve c a b` on `[0, 2π]` is a Euclidean circle if and only if `a = b`.
   * `four_mul_pi_mul_abs_rectifiableSignedArea_ellipseCurve_lt` and
     `four_mul_pi_mul_abs_rectifiableSignedArea_ellipseCurve_lt_hausdorff`: for `0 < a`, `0 < b`,
     and `a ≠ b`, Hurwitz circle-trace rigidity yields the strict geometric length–area inequality
     `4 * π * |rectifiableSignedArea (ellipseCurve c a b) 0 (2 * π)| < L ^ 2`.
-/

open Set Function Filter MeasureTheory intervalIntegral
open scoped Topology Real ENNReal NNReal

namespace TauCeti

/-! ### Continuous-speed AC agreement and Euclidean invariance for `rectifiableSignedArea` -/

section ContinuousSpeedAndInvariance
/-- At any interior point `t ∈ Ioo a b` of an AC curve `γ` with continuous speed `‖deriv γ ·‖` on
`Icc a b`, cumulative arclength `variationOnFromTo γ (Icc a b) a` has derivative `‖deriv γ t‖`. -/
theorem hasDerivAt_variationOnFromTo_of_continuousOn_norm_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {γ : ℝ → E} {a b t : ℝ} (hab : a ≤ b) (hγ :
    AbsolutelyContinuousOnInterval γ a b) (hcont : ContinuousOn (fun s ↦ ‖deriv γ s‖) (Icc a b))
    (ht : t ∈ Ioo a b) : HasDerivAt (variationOnFromTo γ (Icc a b) a) ‖deriv γ t‖ t := by
  have hmeas : StronglyMeasurableAtFilter (fun s ↦ ‖deriv γ s‖) (𝓝 t) volume :=
    (hcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hγ.intervalIntegrable_norm_deriv.mono_set
      (by rw [uIcc_of_le ht.1.le, uIcc_of_le hab]; exact Icc_subset_Icc_right ht.2.le))
    hmeas (hcont.continuousAt (Icc_mem_nhds ht.1 ht.2))
  have hev : (fun u ↦ ∫ s in a..u, ‖deriv γ s‖) =ᶠ[𝓝 t] variationOnFromTo γ (Icc a b) a := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    have hsub : uIcc a u ⊆ uIcc a b := by
      rw [uIcc_of_le hu.1, uIcc_of_le hab]; exact Icc_subset_Icc_right hu.2
    rw [← (hγ.mono hsub).variationOnFromTo_eq_integral_norm_deriv, uIcc_of_le hu.1,
      variationOnFromTo.eq_of_le _ _ hu.1, variationOnFromTo.eq_of_le _ _ hu.1,
      inter_eq_self_of_subset_right (Icc_subset_Icc_right hu.2), inter_self]
  exact hd.congr_of_eventuallyEq hev.symm
/-- Pulling back a.e.-differentiability of `σ` along a monotone function `f` on `Ioo a b` with
continuous derivative `f'` at points where `0 < f' t`. -/
theorem ae_differentiableAt_comp_of_monotoneOn {σ f f' : ℝ → ℝ} {a b c d : ℝ} (hf_mono :
    MonotoneOn f (Ioo a b)) (hf_maps : MapsTo f (Ioo a b) (uIcc c d)) (hf_cont : ContinuousOn f
    (Ioo a b)) (hf'_cont : ContinuousOn f' (Ioo a b)) (hf' : ∀ t ∈ Ioo a b, HasDerivWithinAt f (f'
    t) (Ioo a b) t) (hσ : ∀ᵐ s ∂volume, s ∈ uIcc c d → DifferentiableAt ℝ σ s) : ∀ᵐ t ∂volume, t ∈
    Ioo a b → 0 < f' t → DifferentiableAt ℝ σ (f t) := by
  let S : Set ℝ := {s | ¬(s ∈ uIcc c d → DifferentiableAt ℝ σ s)}
  have hS_null : volume S = 0 := ae_iff.1 hσ
  let N := toMeasurable volume S
  have hN_meas : MeasurableSet N := measurableSet_toMeasurable volume S
  have hN_null : volume N = 0 := by rw [measure_toMeasurable, hS_null]
  have hlint : ∫⁻ t in Ioo a b, ENNReal.ofReal (f' t) * N.indicator 1 (f t) = 0 := by
    rw [← lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioo hf' hf_mono,
      ← nonpos_iff_eq_zero, ← hN_null]
    exact (setLIntegral_le_lintegral _ _).trans_eq (lintegral_indicator_one hN_meas)
  have hae_meas : AEMeasurable (fun t ↦ ENNReal.ofReal (f' t) * N.indicator 1 (f t))
      (volume.restrict (Ioo a b)) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (hf'_cont.aemeasurable measurableSet_Ioo)).mul
      ((measurable_one.indicator hN_meas).comp_aemeasurable
        (hf_cont.aemeasurable measurableSet_Ioo))
  have hae_ind : ∀ᵐ t ∂volume, t ∈ Ioo a b →
      ENNReal.ofReal (f' t) * N.indicator 1 (f t) = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).1 ((lintegral_eq_zero_iff' hae_meas).1 hlint)
  filter_upwards [hae_ind] with t ht ht_oo hpos
  have hind_zero : N.indicator (1 : ℝ → ℝ≥0∞) (f t) = 0 :=
    (mul_eq_zero.1 (ht ht_oo)).resolve_left (ENNReal.ofReal_pos.2 hpos).ne'
  have hft_not_N : f t ∉ N := fun hmem ↦ by simp [indicator_of_mem hmem] at hind_zero
  have hft_not_S : f t ∉ S := fun hmem ↦ hft_not_N (subset_toMeasurable volume S hmem)
  exact (not_not.1 hft_not_S) (hf_maps ht_oo)
/-- Almost-everywhere chain rule identity relating `arcLengthReparam γ a b` and `γ` on `Ioo a b`. -/
theorem ae_norm_deriv_smul_arcLengthReparam_mul_deriv_eq {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b :
    ℝ} (hab : a ≤ b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hcont : ContinuousOn (fun t ↦
    ‖deriv γ t‖) (Icc a b)) : (fun t ↦ ‖deriv γ t‖ • (arcLengthReparam γ a b (variationOnFromTo γ
    (Icc a b) a t) 0 * deriv (fun u ↦ arcLengthReparam γ a b u 1) (variationOnFromTo γ (Icc a b) a
    t))) =ᵐ[volume.restrict (Ioo a b)] fun t ↦ γ t 0 * deriv (fun u ↦ γ u 1) t := by
  have hbv : BoundedVariationOn γ (Icc a b) := uIcc_of_le hab ▸ hγ.boundedVariationOn
  have hc : ContinuousOn γ (Icc a b) := uIcc_of_le hab ▸ hγ.continuousOn
  have hmaps : MapsTo (variationOnFromTo γ (Icc a b) a) (Ioo a b)
      (uIcc 0 (variationOnFromTo γ (Icc a b) a b)) := by
    rw [uIcc_of_le (variationOnFromTo.nonneg_of_le γ (Icc a b) hab)]
    exact hbv.mapsTo_variationOnFromTo_Icc.mono_left Ioo_subset_Icc_self
  have hae_comp := ae_differentiableAt_comp_of_monotoneOn
    ((variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn (left_mem_Icc.2 hab)).mono
      Ioo_subset_Icc_self) hmaps
    ((hbv.continuousOn_variationOnFromTo_Icc hc).mono Ioo_subset_Icc_self)
    (hcont.mono Ioo_subset_Icc_self)
    (fun t ht ↦ (hasDerivAt_variationOnFromTo_of_continuousOn_norm_deriv hab hγ hcont
      ht).hasDerivWithinAt)
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hbv hc 1 0
      (variationOnFromTo γ (Icc a b) a b)).ae_differentiableAt
  have hae_γ := hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hae_comp, hae_γ] with t ht_comp ht_diff ht_oo
  have ht_cc : t ∈ Icc a b := Ioo_subset_Icc_self ht_oo
  have hdγ : DifferentiableAt ℝ γ t := ht_diff (uIcc_of_le hab ▸ ht_cc)
  have hσ₀_eq : arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a t) 0 = γ t 0 := by
    rw [arcLengthReparam_variationOnFromTo hab hbv hc ht_cc]
  rcases eq_or_lt_of_le (norm_nonneg (deriv γ t)) with h0 | hpos
  · have hd0 : deriv γ t = 0 := norm_eq_zero.1 h0.symm
    have hd1 : deriv (fun u ↦ γ u 1) t = 0 := by
      rw [deriv_euclidean_apply hdγ 1, hd0, PiLp.zero_apply]
    rw [smul_eq_mul, ← h0, hd1, zero_mul, mul_zero]
  · have hcomp_deriv : HasDerivAt
        ((fun u ↦ arcLengthReparam γ a b u 1) ∘ variationOnFromTo γ (Icc a b) a)
        (deriv (fun u ↦ arcLengthReparam γ a b u 1)
          (variationOnFromTo γ (Icc a b) a t) * ‖deriv γ t‖) t :=
      (ht_comp ht_oo hpos).hasDerivAt.comp t
        (hasDerivAt_variationOnFromTo_of_continuousOn_norm_deriv hab hγ hcont ht_oo)
    have hev : (fun u ↦ arcLengthReparam γ a b u 1) ∘ variationOnFromTo γ (Icc a b) a =ᶠ[𝓝 t]
        fun u ↦ γ u 1 := by
      filter_upwards [Icc_mem_nhds ht_oo.1 ht_oo.2] with u hu
      exact congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1)
        (arcLengthReparam_variationOnFromTo hab hbv hc hu)
    rw [smul_eq_mul, hσ₀_eq, (hcomp_deriv.congr_of_eventuallyEq hev.symm).deriv]; ring
/-- **Agreement of `rectifiableSignedArea` and `signedAreaEuclidean`** for closed AC curves with
continuous speed `‖deriv γ ·‖` on `Icc a b`. -/
theorem rectifiableSignedArea_eq_signedAreaEuclidean_of_continuousOn_norm_deriv {γ : ℝ →
    EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab : a ≤ b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hcont : ContinuousOn (fun t ↦ ‖deriv γ t‖) (Icc a b)) :
    rectifiableSignedArea γ a b = signedAreaEuclidean γ a (b - a) := by
  have hbv : BoundedVariationOn γ (Icc a b) := uIcc_of_le hab ▸ hγ.boundedVariationOn
  have hc : ContinuousOn γ (Icc a b) := uIcc_of_le hab ▸ hγ.continuousOn
  have hL_nonneg : 0 ≤ (eVariationOn γ (Icc a b)).toReal := ENNReal.toReal_nonneg
  have hfa : variationOnFromTo γ (Icc a b) a a = 0 := variationOnFromTo.self γ (Icc a b) a
  have hfb : variationOnFromTo γ (Icc a b) a b = (eVariationOn γ (Icc a b)).toReal :=
    variationOnFromTo_Icc_self_right hab
  have hcl_x : γ (a + (b - a)) 0 = γ a 0 := by rw [add_sub_cancel, hclosed]
  have hcl_y : γ (a + (b - a)) 1 = γ a 1 := by rw [add_sub_cancel, hclosed]
  have hx_ac : AbsolutelyContinuousOnInterval (fun t ↦ γ t 0) a (a + (b - a)) := by
    rw [add_sub_cancel]; exact absolutelyContinuousOnInterval_euclidean_coord hγ 0
  have hy_ac : AbsolutelyContinuousOnInterval (fun t ↦ γ t 1) a (a + (b - a)) := by
    rw [add_sub_cancel]; exact absolutelyContinuousOnInterval_euclidean_coord hγ 1
  rw [rectifiableSignedArea_eq_integral_mul_deriv hab hbv hc hclosed,
    signedAreaEuclidean, signedArea_eq_integral_mul_deriv hx_ac hy_ac hcl_x hcl_y,
    add_sub_cancel, intervalIntegral.integral_of_le hL_nonneg,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc, ← hfa, ← hfb,
    ← integral_Icc_deriv_smul_of_deriv_nonneg (hbv.continuousOn_variationOnFromTo_Icc hc)
      (fun t ht ↦ hasDerivAt_variationOnFromTo_of_continuousOn_norm_deriv hab hγ hcont ht)
      (fun _ _ ↦ norm_nonneg _) hab,
    integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  exact setIntegral_congr_ae measurableSet_Ioo <|
    (ae_restrict_iff' measurableSet_Ioo).1
      (ae_norm_deriv_smul_arcLengthReparam_mul_deriv_eq hab hγ hcont)
/-- For a globally `C¹` closed curve `γ` on `[a, b]` (`a ≤ b`), `rectifiableSignedArea γ a b`
equals `signedAreaEuclidean γ a (b - a)`. -/
theorem rectifiableSignedArea_eq_signedAreaEuclidean_of_contDiff {γ : ℝ → EuclideanSpace ℝ (Fin
    2)} {a b : ℝ} (hab : a ≤ b) (hγ : ContDiff ℝ 1 γ) (hclosed : γ a = γ b) :
    rectifiableSignedArea γ a b = signedAreaEuclidean γ a (b - a) :=
    rectifiableSignedArea_eq_signedAreaEuclidean_of_continuousOn_norm_deriv hab
    hγ.contDiffOn.absolutelyContinuousOnInterval hclosed (hγ.continuous_deriv
    le_rfl).norm.continuousOn
/-- Composing a curve with an `Isometry` preserves `eVariationOn`. -/
theorem eVariationOn_comp_isometry {α E F : Type*} [LinearOrder α] [EMetricSpace E] [EMetricSpace
    F] {Φ : E → F} (hΦ : Isometry Φ) (γ : α → E) (s : Set α) : eVariationOn (fun t ↦ Φ (γ t)) s =
    eVariationOn γ s := by
  unfold eVariationOn; congr 1; ext ⟨n, u⟩; simp [hΦ.edist_eq]
/-- Composing a curve with an `Isometry` preserves `BoundedVariationOn`. -/
theorem boundedVariationOn_comp_isometry {α E F : Type*} [LinearOrder α] [EMetricSpace E]
    [EMetricSpace F] {Φ : E → F} (hΦ : Isometry Φ) {γ : α → E} {s : Set α} (hγ :
    BoundedVariationOn γ s) : BoundedVariationOn (fun t ↦ Φ (γ t)) s := by
  simpa [BoundedVariationOn, eVariationOn_comp_isometry hΦ] using hγ
/-- Composing a curve with an `Isometry` preserves `variationOnFromTo`. -/
theorem variationOnFromTo_comp_isometry {α E F : Type*} [LinearOrder α] [EMetricSpace E]
    [EMetricSpace F] {Φ : E → F} (hΦ : Isometry Φ) (γ : α → E) (s : Set α) (a b : α) :
    variationOnFromTo (fun t ↦ Φ (γ t)) s a b = variationOnFromTo γ s a b := by
  rcases le_total a b with hab | hba
  · rw [variationOnFromTo.eq_of_le _ _ hab, variationOnFromTo.eq_of_le _ _ hab,
      eVariationOn_comp_isometry hΦ]
  · rw [variationOnFromTo.eq_of_ge _ _ hba, variationOnFromTo.eq_of_ge _ _ hba,
      eVariationOn_comp_isometry hΦ]
/-- Composing a curve with an `Isometry` preserves `arcLengthInv`. -/
theorem arcLengthInv_comp_isometry {E F : Type*} [EMetricSpace E] [EMetricSpace F] {Φ : E → F} (hΦ
    : Isometry Φ) (γ : ℝ → E) (a b s : ℝ) : arcLengthInv (fun t ↦ Φ (γ t)) a b s = arcLengthInv γ
    a b s := by
  have hfun : variationOnFromTo (fun t ↦ Φ (γ t)) (Icc a b) a =
      variationOnFromTo γ (Icc a b) a := funext (variationOnFromTo_comp_isometry hΦ γ (Icc a b) a)
  simp only [arcLengthInv, hfun]
/-- Composing a curve with an `Isometry` commutes with `arcLengthReparam`. -/
theorem arcLengthReparam_comp_isometry {E F : Type*} [EMetricSpace E] [EMetricSpace F] {Φ : E → F}
    (hΦ : Isometry Φ) (γ : ℝ → E) (a b s : ℝ) : arcLengthReparam (fun t ↦ Φ (γ t)) a b s = Φ
    (arcLengthReparam γ a b s) := by
  simp only [arcLengthReparam, arcLengthInv_comp_isometry hΦ]
/-- Adding a constant vector `c` commutes with `arcLengthReparam`. -/
@[simp] theorem arcLengthReparam_add_const (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace
    ℝ (Fin 2)) (a b s : ℝ) : arcLengthReparam (fun t ↦ γ t + c) a b s = arcLengthReparam γ a b s +
    c := arcLengthReparam_comp_isometry (IsometryEquiv.addRight c).isometry γ a b s
/-- Left-adding a constant vector `c` commutes with `arcLengthReparam`. -/
@[simp] theorem arcLengthReparam_const_add (c : EuclideanSpace ℝ (Fin 2)) (γ : ℝ → EuclideanSpace
    ℝ (Fin 2)) (a b s : ℝ) : arcLengthReparam (fun t ↦ c + γ t) a b s = c + arcLengthReparam γ a b
    s := arcLengthReparam_comp_isometry (IsometryEquiv.addLeft c).isometry γ a b s
/-- **Translation invariance of `signedAreaEuclidean`** (left addition). -/
@[simp] theorem signedAreaEuclidean_const_add {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a T : ℝ} (hγ :
    AbsolutelyContinuousOnInterval γ a (a + T)) (hclosed : γ (a + T) = γ a) (c : EuclideanSpace ℝ
    (Fin 2)) : signedAreaEuclidean (fun t ↦ c + γ t) a T = signedAreaEuclidean γ a T := by
  have hshift := signedArea_add_const
    (absolutelyContinuousOnInterval_euclidean_coord hγ 0)
    (absolutelyContinuousOnInterval_euclidean_coord hγ 1)
    (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hclosed)
    (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hclosed) (c 0) (c 1)
  simpa [signedAreaEuclidean, add_comm (c 0), add_comm (c 1)] using hshift
/-- **Translation invariance of `rectifiableSignedArea`** (right addition). -/
@[simp] theorem rectifiableSignedArea_add_const {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab
    : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a
    = γ b) (c : EuclideanSpace ℝ (Fin 2)) : rectifiableSignedArea (fun t ↦ γ t + c) a b =
    rectifiableSignedArea γ a b := by
  have hcl := arcLengthReparam_add_toReal_eq_zero hab hγ hc hclosed
  have hvar : eVariationOn (fun t ↦ γ t + c) (Icc a b) = eVariationOn γ (Icc a b) :=
    eVariationOn_comp_isometry (IsometryEquiv.addRight c).isometry γ (Icc a b)
  simp only [rectifiableSignedArea, hvar, arcLengthReparam_add_const, PiLp.add_apply]
  exact signedArea_add_const
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 0 0 _)
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 1 0 _)
    (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hcl)
    (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hcl) (c 0) (c 1)
/-- **Translation invariance of `rectifiableSignedArea`** (left addition). -/
@[simp] theorem rectifiableSignedArea_const_add {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab
    : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a
    = γ b) (c : EuclideanSpace ℝ (Fin 2)) : rectifiableSignedArea (fun t ↦ c + γ t) a b =
    rectifiableSignedArea γ a b := by
  simpa [add_comm c] using rectifiableSignedArea_add_const hab hγ hc hclosed c
/-- Reflection across the diagonal `p ↦ !₂[p 1, p 0]` is an isometry. -/
theorem isometry_vec2_swap : Isometry (fun p : EuclideanSpace ℝ (Fin 2) ↦ (!₂[p 1, p 0] :
    EuclideanSpace ℝ (Fin 2))) := by
  refine Isometry.of_dist_eq fun p q ↦ ?_
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_euclidean_sq, dist_euclidean_sq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring
/-- **Orientation reversal of `rectifiableSignedArea` under coordinate swap**. -/
@[simp] theorem rectifiableSignedArea_swap (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    rectifiableSignedArea (fun t ↦ !₂[γ t 1, γ t 0]) a b = -rectifiableSignedArea γ a b := by
  simp only [rectifiableSignedArea, eVariationOn_comp_isometry isometry_vec2_swap,
    arcLengthReparam_comp_isometry isometry_vec2_swap, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  exact signedArea_swap _ _ 0 _
/-- Signed area of `(t ↦ a * cos (ω * t), t ↦ b * sin (ω * t))` on `[t₀, t₀ + T]`. -/
theorem signedArea_cos_sin (a b ω t₀ T : ℝ) : signedArea (fun t ↦ a * Real.cos (ω * t)) (fun t ↦ b
    * Real.sin (ω * t)) t₀ T = (1 / 2) * T * a * b * ω := by
  unfold signedArea
  have hcongr : (fun t ↦ a * Real.cos (ω * t) * deriv (fun s ↦ b * Real.sin (ω * s)) t -
      b * Real.sin (ω * t) * deriv (fun s ↦ a * Real.cos (ω * s)) t) = fun _ ↦ a * b * ω := by
    ext t
    have hω : HasDerivAt (fun s ↦ ω * s) ω t := by simpa using (hasDerivAt_id t).const_mul ω
    rw [(hω.cos.const_mul a).deriv, (hω.sin.const_mul b).deriv]
    calc a * Real.cos (ω * t) * (b * (Real.cos (ω * t) * ω)) -
          b * Real.sin (ω * t) * (a * (-Real.sin (ω * t) * ω))
        = a * b * ω * (Real.cos (ω * t) ^ 2 + Real.sin (ω * t) ^ 2) := by ring
      _ = a * b * ω := by rw [Real.cos_sq_add_sin_sq, mul_one]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]; ring

end ContinuousSpeedAndInvariance

/-! ### Multi-traversed circles `multiCircleCurve` and `twiceCircleCurve` -/

section MultiTraversedCircle
/-- The `m`-times traversed circle `t ↦ circleCurve c r ((m : ℝ) * t)` on `[0, 2π]`. -/
noncomputable def multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) (t : ℝ) :
    EuclideanSpace ℝ (Fin 2) := circleCurve c r ((m : ℝ) * t)
/-- The twice-traversed circle `t ↦ circleCurve c r (2 * t)` on `[0, 2π]`. -/
noncomputable abbrev twiceCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (t : ℝ) :
    EuclideanSpace ℝ (Fin 2) := multiCircleCurve c r 2 t
@[simp] theorem multiCircleCurve_zero_nat (c : EuclideanSpace ℝ (Fin 2)) (r t : ℝ) :
    multiCircleCurve c r 0 t = c + !₂[r, 0] := by simp [multiCircleCurve, circleCurve]
@[simp] theorem multiCircleCurve_one (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) : multiCircleCurve c r
    1 = circleCurve c r := by ext t i; simp [multiCircleCurve]
@[simp] theorem multiCircleCurve_apply_zero (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) (t : ℝ)
    : multiCircleCurve c r m t 0 = c 0 + r * Real.cos ((m : ℝ) * t) := rfl
@[simp] theorem multiCircleCurve_apply_one (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) (t : ℝ)
    : multiCircleCurve c r m t 1 = c 1 + r * Real.sin ((m : ℝ) * t) := rfl
/-- `multiCircleCurve c r m` is periodic with fundamental period `2 * π / m`. -/
theorem periodic_multiCircleCurve_div (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) : Periodic
    (multiCircleCurve c r m) (2 * Real.pi / m) := by
  rcases eq_or_ne m 0 with rfl | hm
  · intro t; simp
  · intro t
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hmul : (m : ℝ) * (t + 2 * Real.pi / m) = (m : ℝ) * t + 2 * Real.pi := by field_simp
    simpa [multiCircleCurve, hmul] using periodic_circleCurve c r ((m : ℝ) * t)
/-- `multiCircleCurve c r m` is `2π`-periodic for every `m : ℕ`. -/
theorem periodic_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) : Periodic
    (multiCircleCurve c r m) (2 * Real.pi) := fun t ↦ by
  simpa [multiCircleCurve, mul_add, mul_comm (m : ℝ) (2 * Real.pi)] using
    (periodic_circleCurve c r).nat_mul m ((m : ℝ) * t)
@[simp] theorem multiCircleCurve_two_pi (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) :
    multiCircleCurve c r m (2 * Real.pi) = multiCircleCurve c r m 0 := by
  simpa using periodic_multiCircleCurve c r m 0
/-- `multiCircleCurve c r m` is smooth (`ContDiff ℝ n`). -/
theorem contDiff_multiCircleCurve {n : WithTop ℕ∞} (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ)
    : ContDiff ℝ n (multiCircleCurve c r m) := by
  unfold multiCircleCurve circleCurve
  refine contDiff_const.add ?_
  rw [show (fun t ↦ (!₂[r * Real.cos ((m : ℝ) * t), r * Real.sin ((m : ℝ) * t)] :
      EuclideanSpace ℝ (Fin 2))) = fun t ↦
      (r * Real.cos ((m : ℝ) * t)) • EuclideanSpace.single 0 1 +
      (r * Real.sin ((m : ℝ) * t)) • EuclideanSpace.single 1 1 by
    ext t : 1; exact vec2_eq_smul_single _ _]
  exact ((contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).smul
    contDiff_const).add
    ((contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))).smul
      contDiff_const)
/-- `multiCircleCurve c r m` is continuous. -/
theorem continuous_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) : Continuous
    (multiCircleCurve c r m) := (continuous_circleCurve c r).comp (continuous_const.mul
    continuous_id)
/-- Derivative of `multiCircleCurve c r m` at `t`. -/
theorem hasDerivAt_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (multiCircleCurve c r m) ((m : ℝ) • !₂[-r * Real.sin ((m : ℝ) * t), r * Real.cos
    ((m : ℝ) * t)]) t := by
  have hmul : HasDerivAt (fun s ↦ (m : ℝ) * s) (m : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (m : ℝ)
  exact (hasDerivAt_circleCurve c r ((m : ℝ) * t)).scomp t hmul
/-- `deriv (multiCircleCurve c r m) t`. -/
theorem deriv_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) (t : ℝ) : deriv
    (multiCircleCurve c r m) t = (m : ℝ) • !₂[-r * Real.sin ((m : ℝ) * t), r * Real.cos ((m : ℝ) *
    t)] := (hasDerivAt_multiCircleCurve c r m t).deriv
/-- The speed `‖deriv (multiCircleCurve c r m) t‖` is constantly `(m : ℝ) * |r|`. -/
@[simp] theorem norm_deriv_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) (t : ℝ)
    : ‖deriv (multiCircleCurve c r m) t‖ = (m : ℝ) * |r| := by
  rw [deriv_multiCircleCurve, ← deriv_circleCurve c r ((m : ℝ) * t), norm_smul,
    Real.norm_of_nonneg m.cast_nonneg, norm_deriv_circleCurve]
/-- `multiCircleCurve c r m` is absolutely continuous on every interval `[a, b]`. -/
theorem absolutelyContinuousOnInterval_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m
    : ℕ) (a b : ℝ) : AbsolutelyContinuousOnInterval (multiCircleCurve c r m) a b :=
    (contDiff_multiCircleCurve c r m).contDiffOn.absolutelyContinuousOnInterval
/-- `multiCircleCurve c r m` has bounded variation on every interval `Icc a b`. -/
theorem boundedVariationOn_multiCircleCurve_Icc (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) (a
    b : ℝ) : BoundedVariationOn (multiCircleCurve c r m) (Icc a b) :=
    (absolutelyContinuousOnInterval_multiCircleCurve c r m a b).boundedVariationOn.mono fun _ hx ↦
    uIcc_of_le (hx.1.trans hx.2) ▸ hx
/-- For `r ≠ 0` and `1 ≤ m`, `multiCircleCurve c r m` is injective on `Ico 0 (2 * π / m)`. -/
theorem injOn_multiCircleCurve_Ico_div (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : r ≠ 0) {m : ℕ}
    (hm : 1 ≤ m) : InjOn (multiCircleCurve c r m) (Ico 0 (2 * Real.pi / m)) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  intro t₁ ht₁ t₂ ht₂ h
  have ht₁' : (m : ℝ) * t₁ ∈ Ico 0 (2 * Real.pi) :=
    ⟨mul_nonneg hm_pos.le ht₁.1, (lt_div_iff₀' hm_pos).1 ht₁.2⟩
  have ht₂' : (m : ℝ) * t₂ ∈ Ico 0 (2 * Real.pi) :=
    ⟨mul_nonneg hm_pos.le ht₂.1, (lt_div_iff₀' hm_pos).1 ht₂.2⟩
  exact mul_left_cancel₀ hm_pos.ne' (injOn_circleCurve_Ico c hr ht₁' ht₂' h)
/-- For `2 ≤ m`, `multiCircleCurve c r m` is **not** injective on `Ico 0 (2 * π)`. -/
theorem not_injOn_multiCircleCurve_Ico (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) {m : ℕ} (hm : 2 ≤ m)
    : ¬ InjOn (multiCircleCurve c r m) (Ico 0 (2 * Real.pi)) := by
  intro hinj
  have hm_pos : (0 : ℝ) < m := by positivity
  have hm_gt : (1 : ℝ) < m := by exact_mod_cast hm
  have h0_mem : (0 : ℝ) ∈ Ico 0 (2 * Real.pi) := ⟨le_rfl, Real.two_pi_pos⟩
  have hT_mem : 2 * Real.pi / m ∈ Ico 0 (2 * Real.pi) :=
    ⟨by positivity, div_lt_self Real.two_pi_pos hm_gt⟩
  have heq : multiCircleCurve c r m (2 * Real.pi / m) = multiCircleCurve c r m 0 := by
    simpa using periodic_multiCircleCurve_div c r m 0
  exact (by positivity : (2 * Real.pi / m : ℝ) ≠ 0) (hinj hT_mem h0_mem heq)
/-- For `1 ≤ m`, the range of `multiCircleCurve c r m` is `Metric.sphere c |r|`. -/
@[simp] theorem range_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) {m : ℕ} (hm : 1 ≤ m)
    : range (multiCircleCurve c r m) = Metric.sphere c |r| := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsurj : Surjective (fun t : ℝ ↦ (m : ℝ) * t) := fun y ↦ ⟨y / m, mul_div_cancel₀ y hm_ne⟩
  change range (circleCurve c r ∘ fun t : ℝ ↦ (m : ℝ) * t) = Metric.sphere c |r|
  rw [hsurj.range_comp, range_circleCurve]
/-- For `0 ≤ r` and `1 ≤ m`, `multiCircleCurve c r m '' Icc 0 (2 * π / m) = Metric.sphere c r`. -/
@[simp] theorem image_multiCircleCurve_Icc_div (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤ r)
    {m : ℕ} (hm : 1 ≤ m) : multiCircleCurve c r m '' Icc 0 (2 * Real.pi / m) = Metric.sphere c r
    := by
  have hT : 0 < 2 * Real.pi / (m : ℝ) := div_pos Real.two_pi_pos (Nat.cast_pos.mpr hm)
  have h := (periodic_multiCircleCurve_div c r m).image_Icc hT 0
  rwa [zero_add, range_multiCircleCurve c r hm, abs_of_nonneg hr] at h
/-- **Trace of `multiCircleCurve c r m` on `[0, 2π]`** (`0 ≤ r`, `1 ≤ m`). -/
@[simp] theorem image_multiCircleCurve_Icc (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤ r) {m
    : ℕ} (hm : 1 ≤ m) : multiCircleCurve c r m '' Icc 0 (2 * Real.pi) = Metric.sphere c r := by
  have hT : 0 < 2 * Real.pi / (m : ℝ) := div_pos Real.two_pi_pos (Nat.cast_pos.mpr hm)
  have hmul := (periodic_multiCircleCurve_div c r m).image_Icc_mul_period hT hm
  have hm_eq : (m : ℝ) * (2 * Real.pi / m) = 2 * Real.pi :=
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))
  rw [← hm_eq, hmul, image_multiCircleCurve_Icc_div c hr hm]
/-- **One-dimensional Hausdorff measure of the trace of `multiCircleCurve c r m`** (`0 ≤ r`,
`1 ≤ m`), which equals `2πr` independently of the winding multiplicity `m`. -/
@[simp] theorem euclideanHausdorffMeasure_image_multiCircleCurve_Icc (c : EuclideanSpace ℝ (Fin
    2)) {r : ℝ} (hr : 0 ≤ r) {m : ℕ} (hm : 1 ≤ m) : μHE[1] (multiCircleCurve c r m '' Icc 0 (2 *
    Real.pi)) = ENNReal.ofReal (2 * Real.pi * r) := by
  rw [image_multiCircleCurve_Icc c hr hm, euclideanHausdorffMeasure_sphere_two c hr]
/-- **Fiber multiplicity of `multiCircleCurve c r m` on `Ico 0 (2 * π)`** (`0 < r`, `1 ≤ m`). -/
theorem fiberMultiplicity_multiCircleCurve_Ico (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    {m : ℕ} (hm : 1 ≤ m) (y : EuclideanSpace ℝ (Fin 2)) : fiberMultiplicity (multiCircleCurve c r
    m) (Ico 0 (2 * Real.pi)) y = m * (Metric.sphere c r).indicator 1 y := by
  have hT : 0 < 2 * Real.pi / (m : ℝ) := div_pos Real.two_pi_pos (Nat.cast_pos.mpr hm)
  have hm_eq : (m : ℝ) * (2 * Real.pi / m) = 2 * Real.pi :=
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))
  rw [← hm_eq, (periodic_multiCircleCurve_div c r m).fiberMultiplicity_Ico_mul_period hT
    (injOn_multiCircleCurve_Ico_div c hr.ne' hm) m y, image_multiCircleCurve_Icc_div c hr.le hm]
/-- Every point `y ∈ Metric.sphere c r` (`0 < r`, `1 ≤ m`) has fiber multiplicity `m` under
`multiCircleCurve c r m` on `Ico 0 (2 * π)`. -/
theorem fiberMultiplicity_multiCircleCurve_Ico_of_mem_sphere (c : EuclideanSpace ℝ (Fin 2)) {r :
    ℝ} (hr : 0 < r) {m : ℕ} (hm : 1 ≤ m) {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Metric.sphere c
    r) : fiberMultiplicity (multiCircleCurve c r m) (Ico 0 (2 * Real.pi)) y = m := by
  rw [fiberMultiplicity_multiCircleCurve_Ico c hr hm y, indicator_of_mem hy, Pi.one_apply, mul_one]
/-- Total variation of `multiCircleCurve c r m` on `Icc a b` (`a ≤ b`). -/
theorem eVariationOn_multiCircleCurve_Icc_abs (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m : ℕ) {a b
    : ℝ} (hab : a ≤ b) : eVariationOn (multiCircleCurve c r m) (Icc a b) = ENNReal.ofReal ((b - a)
    * ((m : ℝ) * |r|)) := by
  have hac := absolutelyContinuousOnInterval_multiCircleCurve c r m a b
  rw [hac.eVariationOn_eq_ofReal_integral_norm_deriv hab]
  simp_rw [norm_deriv_multiCircleCurve]; rw [intervalIntegral.integral_const, smul_eq_mul]
/-- Total variation of `multiCircleCurve c r m` on `Icc 0 (2 * π)` (`0 ≤ r`). -/
@[simp] theorem eVariationOn_multiCircleCurve_two_pi (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr :
    0 ≤ r) (m : ℕ) : eVariationOn (multiCircleCurve c r m) (Icc 0 (2 * Real.pi)) = ENNReal.ofReal
    (2 * Real.pi * (m : ℝ) * r) := by
  rw [eVariationOn_multiCircleCurve_Icc_abs c r m Real.two_pi_pos.le, abs_of_nonneg hr, sub_zero]
  ring_nf
/-- Cumulative arclength of `multiCircleCurve c r m` on `Icc 0 (2 * π)` (`0 ≤ r`). -/
theorem variationOnFromTo_multiCircleCurve_two_pi (c : EuclideanSpace ℝ (Fin 2)) {r t : ℝ} (hr : 0
    ≤ r) (m : ℕ) (ht : t ∈ Icc 0 (2 * Real.pi)) : variationOnFromTo (multiCircleCurve c r m) (Icc
    0 (2 * Real.pi)) 0 t = t * ((m : ℝ) * r) := by
  have hnonneg : 0 ≤ t * ((m : ℝ) * r) := mul_nonneg ht.1 (mul_nonneg m.cast_nonneg hr)
  rw [variationOnFromTo.eq_of_le _ _ ht.1,
    inter_eq_self_of_subset_right (Icc_subset_Icc_right ht.2),
    eVariationOn_multiCircleCurve_Icc_abs c r m ht.1, abs_of_nonneg hr, sub_zero,
    ENNReal.toReal_ofReal hnonneg]
/-- **Canonical unit-speed arclength reparametrization of `multiCircleCurve c r m`** (`0 < r`). -/
theorem arcLengthReparam_multiCircleCurve_apply (c : EuclideanSpace ℝ (Fin 2)) {r s : ℝ} (hr : 0 <
    r) {m : ℕ} (hm : 1 ≤ m) (hs : s ∈ Icc 0 (2 * Real.pi * (m : ℝ) * r)) : arcLengthReparam
    (multiCircleCurve c r m) 0 (2 * Real.pi) s = circleCurve c r (s / r) := by
  have hvar : variationOnFromTo (multiCircleCurve c r m) (Icc 0 (2 * Real.pi)) 0 (2 * Real.pi) =
      2 * Real.pi * (m : ℝ) * r := by
    rw [variationOnFromTo_multiCircleCurve_two_pi c hr.le m (right_mem_Icc.2 Real.two_pi_pos.le)]
    ring
  have hs' : s ∈ Icc 0
      (variationOnFromTo (multiCircleCurve c r m) (Icc 0 (2 * Real.pi)) 0 (2 * Real.pi)) := by
    rwa [hvar]
  exact (eq_arcLengthReparam_of_comp_variationOnFromTo (σ := fun u ↦ circleCurve c r (u / r))
    Real.two_pi_pos.le (boundedVariationOn_multiCircleCurve_Icc c r m 0 (2 * Real.pi))
    (continuous_multiCircleCurve c r m).continuousOn
    (fun t ht ↦ by
      rw [variationOnFromTo_multiCircleCurve_two_pi c hr.le m ht]
      have : t * ((m : ℝ) * r) / r = (m : ℝ) * t := by
        have : r ≠ 0 := hr.ne'; field_simp
      rw [this]; rfl) hs').symm
/-- **Coordinate signed area of `multiCircleCurve c r m` on `[0, 2π]`** equals `m * π * r ^ 2`. -/
@[simp] theorem signedAreaEuclidean_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m :
    ℕ) : signedAreaEuclidean (multiCircleCurve c r m) 0 (2 * Real.pi) = (m : ℝ) * Real.pi * r ^ 2
    := by
  have hdecomp : multiCircleCurve c r m = fun t ↦ c + multiCircleCurve 0 r m t := by
    ext t i; simp [multiCircleCurve, circleCurve]
  have hclosed : multiCircleCurve 0 r m (0 + 2 * Real.pi) = multiCircleCurve 0 r m 0 := by
    rw [zero_add, multiCircleCurve_two_pi]
  rw [hdecomp, signedAreaEuclidean_const_add
    (absolutelyContinuousOnInterval_multiCircleCurve 0 r m 0 (0 + 2 * Real.pi)) hclosed c]
  have heq : signedAreaEuclidean (multiCircleCurve 0 r m) 0 (2 * Real.pi) =
      signedArea (fun t ↦ r * Real.cos ((m : ℝ) * t)) (fun t ↦ r * Real.sin ((m : ℝ) * t))
        0 (2 * Real.pi) := by simp [signedAreaEuclidean]
  rw [heq, signedArea_cos_sin]; ring
/-- **Geometric signed area of `multiCircleCurve c r m` on `[0, 2π]`** equals `m * π * r ^ 2`. -/
@[simp] theorem rectifiableSignedArea_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (m :
    ℕ) : rectifiableSignedArea (multiCircleCurve c r m) 0 (2 * Real.pi) = (m : ℝ) * Real.pi * r ^
    2 := by
  rw [rectifiableSignedArea_eq_signedAreaEuclidean_of_contDiff Real.two_pi_pos.le
    (contDiff_multiCircleCurve c r m) (multiCircleCurve_two_pi c r m).symm,
    sub_zero, signedAreaEuclidean_multiCircleCurve]
/-- **Exact length–area isoperimetric deficit of `multiCircleCurve c r m`** (`0 ≤ r`). -/
theorem isoperimetric_deficit_multiCircleCurve (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤ r)
    (m : ℕ) : (eVariationOn (multiCircleCurve c r m) (Icc 0 (2 * Real.pi))).toReal ^ 2 - 4 *
    Real.pi * |rectifiableSignedArea (multiCircleCurve c r m) 0 (2 * Real.pi)| = 4 * Real.pi ^ 2 *
    r ^ 2 * (m : ℝ) * ((m : ℝ) - 1) := by
  rw [eVariationOn_multiCircleCurve_two_pi c hr m,
    ENNReal.toReal_ofReal (by positivity), rectifiableSignedArea_multiCircleCurve,
    abs_of_nonneg (by positivity)]; ring
/-- **Strict Hurwitz length–area inequality for `multiCircleCurve c r m`** (`0 < r`, `2 ≤ m`). -/
theorem four_mul_pi_mul_abs_rectifiableSignedArea_multiCircleCurve_lt (c : EuclideanSpace ℝ (Fin
    2)) {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 2 ≤ m) : 4 * Real.pi * |rectifiableSignedArea
    (multiCircleCurve c r m) 0 (2 * Real.pi)| < (eVariationOn (multiCircleCurve c r m) (Icc 0 (2 *
    Real.pi))).toReal ^ 2 := by
  have hdef := isoperimetric_deficit_multiCircleCurve c hr.le m
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) - 1 := by linarith
  have hpos : 0 < 4 * Real.pi ^ 2 * r ^ 2 * (m : ℝ) * ((m : ℝ) - 1) := by positivity
  linarith
/-- **Failure of the unweighted Hausdorff-length bound for `multiCircleCurve c r m`** (`0 < r`,
`2 ≤ m`): `(μHE[1] (multiCircleCurve c r m '' Icc 0 (2 * π))).toReal ^ 2` is strictly smaller than
`4 * π * |rectifiableSignedArea (multiCircleCurve c r m) 0 (2 * π)|`. -/
theorem hausdorff_sq_lt_four_mul_pi_mul_abs_rectifiableSignedArea_multiCircleCurve (c :
    EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 2 ≤ m) : (μHE[1]
    (multiCircleCurve c r m '' Icc 0 (2 * Real.pi))).toReal ^ 2 < 4 * Real.pi *
    |rectifiableSignedArea (multiCircleCurve c r m) 0 (2 * Real.pi)| := by
  have hm1 : 1 ≤ m := by omega
  rw [euclideanHausdorffMeasure_image_multiCircleCurve_Icc c hr.le hm1,
    ENNReal.toReal_ofReal (by positivity), rectifiableSignedArea_multiCircleCurve,
    abs_of_nonneg (by positivity)]
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < 4 * Real.pi ^ 2 * r ^ 2 := by positivity
  nlinarith

end MultiTraversedCircle

/-! ### Parametrized ellipses `ellipseCurve` and strict Hurwitz inequality -/

section EllipseCurve
/-- The standard parametrization `t ↦ c + !₂[a * cos t, b * sin t]` of the ellipse with center `c`
and semi-axes `a, b` in `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b t : ℝ) : EuclideanSpace ℝ (Fin
    2) := c + !₂[a * Real.cos t, b * Real.sin t]
@[simp] theorem ellipseCurve_same (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) : ellipseCurve c r r =
    circleCurve c r := rfl
@[simp] theorem ellipseCurve_apply_zero (c : EuclideanSpace ℝ (Fin 2)) (a b t : ℝ) : ellipseCurve
    c a b t 0 = c 0 + a * Real.cos t := rfl
@[simp] theorem ellipseCurve_apply_one (c : EuclideanSpace ℝ (Fin 2)) (a b t : ℝ) : ellipseCurve c
    a b t 1 = c 1 + b * Real.sin t := rfl
/-- `ellipseCurve c a b` is `2π`-periodic. -/
theorem periodic_ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : Periodic (ellipseCurve c
    a b) (2 * Real.pi) := fun t ↦ by
  simp [ellipseCurve, Real.cos_add_two_pi, Real.sin_add_two_pi]
@[simp] theorem ellipseCurve_two_pi (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : ellipseCurve c a b
    (2 * Real.pi) = ellipseCurve c a b 0 := by
  simpa using periodic_ellipseCurve c a b 0
/-- `ellipseCurve c a b` is smooth (`ContDiff ℝ n`). -/
theorem contDiff_ellipseCurve {n : WithTop ℕ∞} (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : ContDiff
    ℝ n (ellipseCurve c a b) := by
  unfold ellipseCurve
  refine contDiff_const.add ?_
  rw [show (fun t ↦ (!₂[a * Real.cos t, b * Real.sin t] : EuclideanSpace ℝ (Fin 2))) = fun t ↦
      (a * Real.cos t) • EuclideanSpace.single 0 1 +
      (b * Real.sin t) • EuclideanSpace.single 1 1 by
    ext t : 1; exact vec2_eq_smul_single _ _]
  exact ((contDiff_const.mul Real.contDiff_cos).smul contDiff_const).add
    ((contDiff_const.mul Real.contDiff_sin).smul contDiff_const)
/-- `ellipseCurve c a b` is continuous. -/
theorem continuous_ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : Continuous
    (ellipseCurve c a b) := (contDiff_ellipseCurve (n := ⊤) c a b).continuous
/-- Derivative of `ellipseCurve c a b` at `t`. -/
theorem hasDerivAt_ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b t : ℝ) : HasDerivAt
    (ellipseCurve c a b) !₂[-a * Real.sin t, b * Real.cos t] t := by
  have hcos : HasDerivAt (fun s ↦ a * Real.cos s) (-a * Real.sin t) t := by
    simpa [neg_mul] using (Real.hasDerivAt_cos t).const_mul a
  exact (hasDerivAt_vec2 hcos ((Real.hasDerivAt_sin t).const_mul b)).const_add c
/-- `deriv (ellipseCurve c a b) t = !₂[-a * sin t, b * cos t]`. -/
theorem deriv_ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b t : ℝ) : deriv (ellipseCurve c a b)
    t = !₂[-a * Real.sin t, b * Real.cos t] := (hasDerivAt_ellipseCurve c a b t).deriv
/-- Speed `‖deriv (ellipseCurve c a b) t‖ = √(a ^ 2 * sin² t + b ^ 2 * cos² t)`. -/
theorem norm_deriv_ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b t : ℝ) : ‖deriv (ellipseCurve
    c a b) t‖ = Real.sqrt (a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2) := by
  rw [deriv_ellipseCurve, norm_vec2]; congr 1; ring
/-- Squared speed `‖deriv (ellipseCurve c a b) t‖ ^ 2 = a ^ 2 * sin² t + b ^ 2 * cos² t`. -/
theorem norm_deriv_ellipseCurve_sq (c : EuclideanSpace ℝ (Fin 2)) (a b t : ℝ) : ‖deriv
    (ellipseCurve c a b) t‖ ^ 2 = a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 := by
  rw [norm_deriv_ellipseCurve, Real.sq_sqrt (by positivity)]
/-- `ellipseCurve c a b` is absolutely continuous on every interval `[u, v]`. -/
theorem absolutelyContinuousOnInterval_ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b u v : ℝ) :
    AbsolutelyContinuousOnInterval (ellipseCurve c a b) u v := (contDiff_ellipseCurve c a
    b).contDiffOn.absolutelyContinuousOnInterval
/-- `ellipseCurve c a b` has bounded variation on every interval `Icc u v`. -/
theorem boundedVariationOn_ellipseCurve_Icc (c : EuclideanSpace ℝ (Fin 2)) (a b u v : ℝ) :
    BoundedVariationOn (ellipseCurve c a b) (Icc u v) :=
    (absolutelyContinuousOnInterval_ellipseCurve c a b u v).boundedVariationOn.mono fun _ hx ↦
    uIcc_of_le (hx.1.trans hx.2) ▸ hx
/-- For `a ≠ 0` and `b ≠ 0`, `ellipseCurve c a b` is injective on `Ico 0 (2 * π)`. -/
theorem injOn_ellipseCurve_Ico (c : EuclideanSpace ℝ (Fin 2)) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    InjOn (ellipseCurve c a b) (Ico 0 (2 * Real.pi)) := by
  intro t₁ ht₁ t₂ ht₂ h
  have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0) h
  have h1 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 1) h
  simp only [ellipseCurve_apply_zero, ellipseCurve_apply_one, add_right_inj] at h0 h1
  have hcos : Real.cos t₁ = Real.cos t₂ := mul_left_cancel₀ ha h0
  have hsin : Real.sin t₁ = Real.sin t₂ := mul_left_cancel₀ hb h1
  refine injOn_circleCurve_Ico 0 one_ne_zero ht₁ ht₂ ?_
  ext i; fin_cases i <;> simp [circleCurve, hcos, hsin]
/-- For `a ≠ 0` and `b ≠ 0`, the 1D Hausdorff measure of the ellipse trace equals its total
variation on `[0, 2π]`. -/
theorem euclideanHausdorffMeasure_image_ellipseCurve_Icc (c : EuclideanSpace ℝ (Fin 2)) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) : μHE[1] (ellipseCurve c a b '' Icc 0 (2 * Real.pi)) = eVariationOn
    (ellipseCurve c a b) (Icc 0 (2 * Real.pi)) :=
    euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico (continuous_ellipseCurve
    c a b).continuousOn (injOn_ellipseCurve_Ico c ha hb)
/-- **Cartesian equation of the trace of `ellipseCurve c a b`** (`a ≠ 0`, `b ≠ 0`). -/
theorem image_ellipseCurve_Icc (c : EuclideanSpace ℝ (Fin 2)) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipseCurve c a b '' Icc 0 (2 * Real.pi) = {p : EuclideanSpace ℝ (Fin 2) | ((p 0 - c 0) / a)
    ^ 2 + ((p 1 - c 1) / b) ^ 2 = 1} := by
  ext p; simp only [mem_image, mem_ofPred]
  refine ⟨?_, ?_⟩
  · rintro ⟨t, _, rfl⟩
    simp only [ellipseCurve_apply_zero, ellipseCurve_apply_one, add_sub_cancel_left,
      mul_div_cancel_left₀ _ ha, mul_div_cancel_left₀ _ hb, Real.cos_sq_add_sin_sq]
  · intro hp
    have hq : (!₂[(p 0 - c 0) / a, (p 1 - c 1) / b] : EuclideanSpace ℝ (Fin 2)) ∈
        Metric.sphere 0 1 := by
      rw [Metric.mem_sphere, ← sq_eq_sq₀ dist_nonneg zero_le_one, dist_euclidean_sq]
      simpa [PiLp.zero_apply, sub_zero] using hp
    rw [← image_circleCurve_Icc_two_pi 0 zero_le_one] at hq
    rcases hq with ⟨t, ht, hteq⟩
    have hcos : Real.cos t = (p 0 - c 0) / a := by
      simpa [circleCurve] using congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hteq
    have hsin : Real.sin t = (p 1 - c 1) / b := by
      simpa [circleCurve] using congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hteq
    refine ⟨t, ht, ?_⟩
    ext i; fin_cases i
    · simp [ellipseCurve_apply_zero, hcos, mul_div_cancel₀ _ ha]
    · simp [ellipseCurve_apply_one, hsin, mul_div_cancel₀ _ hb]
/-- **Coordinate signed area of `ellipseCurve c a b` on `[0, 2π]`** equals `π * a * b`. -/
@[simp] theorem signedAreaEuclidean_ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    signedAreaEuclidean (ellipseCurve c a b) 0 (2 * Real.pi) = Real.pi * a * b := by
  have hdecomp : ellipseCurve c a b = fun t ↦ c + ellipseCurve 0 a b t := by
    ext t i; simp [ellipseCurve]
  have hclosed : ellipseCurve 0 a b (0 + 2 * Real.pi) = ellipseCurve 0 a b 0 := by
    rw [zero_add, ellipseCurve_two_pi]
  rw [hdecomp, signedAreaEuclidean_const_add
    (absolutelyContinuousOnInterval_ellipseCurve 0 a b 0 (0 + 2 * Real.pi)) hclosed c]
  have heq : signedAreaEuclidean (ellipseCurve 0 a b) 0 (2 * Real.pi) =
      signedArea (fun t ↦ a * Real.cos (1 * t)) (fun t ↦ b * Real.sin (1 * t)) 0 (2 * Real.pi) := by
    simp [signedAreaEuclidean]
  rw [heq, signedArea_cos_sin]; ring
/-- **Geometric signed area of `ellipseCurve c a b` on `[0, 2π]`** equals `π * a * b`. -/
@[simp] theorem rectifiableSignedArea_ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    rectifiableSignedArea (ellipseCurve c a b) 0 (2 * Real.pi) = Real.pi * a * b := by
  rw [rectifiableSignedArea_eq_signedAreaEuclidean_of_contDiff Real.two_pi_pos.le
    (contDiff_ellipseCurve c a b) (ellipseCurve_two_pi c a b).symm,
    sub_zero, signedAreaEuclidean_ellipseCurve]
/-- **Kinetic energy of `ellipseCurve c a b` on `[0, 2π]`** equals `π * (a ^ 2 + b ^ 2)`. -/
@[simp] theorem intervalIntegral_norm_deriv_ellipseCurve_sq (c : EuclideanSpace ℝ (Fin 2)) (a b :
    ℝ) : ∫ t in (0 : ℝ)..(2 * Real.pi), ‖deriv (ellipseCurve c a b) t‖ ^ 2 = Real.pi * (a ^ 2 + b
    ^ 2) := by
  let f : ℝ → ℝ := fun t ↦ a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2
  have hf_cont : Continuous f := by dsimp [f]; fun_prop
  have hf_per : Periodic f (2 * Real.pi) := fun t ↦ by
    dsimp [f]; rw [Real.sin_add_two_pi, Real.cos_add_two_pi]
  have hshift : ∫ t in (0 : ℝ)..(2 * Real.pi), f (t + Real.pi / 2) =
      ∫ t in (0 : ℝ)..(2 * Real.pi), f t := by
    rw [intervalIntegral.integral_comp_add_right f (Real.pi / 2), zero_add,
      add_comm (2 * Real.pi), hf_per.intervalIntegral_add_eq (Real.pi / 2) 0, zero_add]
  have hsum : (fun t ↦ f t + f (t + Real.pi / 2)) = fun _ ↦ a ^ 2 + b ^ 2 := by
    ext t; dsimp [f]; rw [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
    calc a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 +
          (a ^ 2 * Real.cos t ^ 2 + b ^ 2 * (-Real.sin t) ^ 2)
        = (a ^ 2 + b ^ 2) * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = a ^ 2 + b ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
  have h2 : 2 * ∫ t in (0 : ℝ)..(2 * Real.pi), f t = 2 * Real.pi * (a ^ 2 + b ^ 2) := by
    calc 2 * ∫ t in (0 : ℝ)..(2 * Real.pi), f t
        = (∫ t in (0 : ℝ)..(2 * Real.pi), f t) +
            ∫ t in (0 : ℝ)..(2 * Real.pi), f (t + Real.pi / 2) := by rw [hshift]; ring
      _ = ∫ t in (0 : ℝ)..(2 * Real.pi), (f t + f (t + Real.pi / 2)) :=
          (intervalIntegral.integral_add (hf_cont.intervalIntegrable _ _)
            ((hf_cont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)).symm
      _ = 2 * Real.pi * (a ^ 2 + b ^ 2) := by
          rw [hsum, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  simp_rw [norm_deriv_ellipseCurve_sq]; change ∫ t in (0 : ℝ)..(2 * Real.pi), f t = _
  linarith
/-- **Exact area–energy deficit of `ellipseCurve c a b` on `[0, 2π]`**. -/
theorem area_energy_deficit_ellipseCurve (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : 2 * Real.pi *
    (∫ t in (0 : ℝ)..(2 * Real.pi), ‖deriv (ellipseCurve c a b) t‖ ^ 2) - 4 * Real.pi *
    rectifiableSignedArea (ellipseCurve c a b) 0 (2 * Real.pi) = 2 * Real.pi ^ 2 * (a - b) ^ 2 :=
    by
  rw [intervalIntegral_norm_deriv_ellipseCurve_sq, rectifiableSignedArea_ellipseCurve]; ring
/-- **Circle-trace characterization for `ellipseCurve c a b`** (`0 < a`, `0 < b`):
the trace `ellipseCurve c a b '' Icc 0 (2 * π)` is a Euclidean circle `Metric.sphere center r`
(`0 ≤ r`) if and only if `a = b`. -/
theorem exists_sphere_trace_ellipseCurve_iff (c : EuclideanSpace ℝ (Fin 2)) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : (∃ (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 ≤ r ∧ ellipseCurve c a b ''
    Icc 0 (2 * Real.pi) = Metric.sphere center r) ↔ a = b := by
  refine ⟨?_, fun hab ↦ ⟨c, a, ha.le, by rw [← hab, ellipseCurve_same,
    image_circleCurve_Icc_two_pi c ha.le]⟩⟩
  rintro ⟨center, r, hr, htrace⟩
  have hmem (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) :
      (ellipseCurve c a b t 0 - center 0) ^ 2 +
        (ellipseCurve c a b t 1 - center 1) ^ 2 = r ^ 2 := by
    have hp : ellipseCurve c a b t ∈ Metric.sphere center r := htrace ▸ ⟨t, ht, rfl⟩
    rwa [Metric.mem_sphere, ← sq_eq_sq₀ dist_nonneg hr, dist_euclidean_sq] at hp
  have h0 := hmem 0 ⟨le_rfl, Real.two_pi_pos.le⟩
  have hpi := hmem Real.pi ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
  have hpi2 := hmem (Real.pi / 2) ⟨by positivity, by linarith [Real.pi_pos]⟩
  have h3pi2 := hmem (3 * Real.pi / 2) ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hsin_3pi2 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi, Real.sin_pi_div_two]
  have hcos_3pi2 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi, Real.cos_pi_div_two,
      neg_zero]
  simp only [ellipseCurve_apply_zero, ellipseCurve_apply_one, Real.cos_zero, Real.sin_zero,
    Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two, hcos_3pi2, hsin_3pi2,
    mul_one, mul_zero, mul_neg, add_zero] at h0 hpi hpi2 h3pi2
  have hc0 : center 0 = c 0 := by nlinarith
  have hc1 : center 1 = c 1 := by nlinarith
  rw [hc0, hc1] at h0 hpi2
  nlinarith
/-- **Strict Hurwitz length–area inequality for a non-circular ellipse** (`0 < a`, `0 < b`, `a ≠ b`)
in terms of total variation `eVariationOn`. -/
theorem four_mul_pi_mul_abs_rectifiableSignedArea_ellipseCurve_lt (c : EuclideanSpace ℝ (Fin 2))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) : 4 * Real.pi * |rectifiableSignedArea
    (ellipseCurve c a b) 0 (2 * Real.pi)| < (eVariationOn (ellipseCurve c a b) (Icc 0 (2 *
    Real.pi))).toReal ^ 2 := by
  refine lt_of_le_of_ne
    (four_mul_pi_mul_abs_rectifiableSignedArea_le Real.two_pi_pos.le
      (boundedVariationOn_ellipseCurve_Icc c a b 0 (2 * Real.pi))
      (continuous_ellipseCurve c a b).continuousOn (ellipseCurve_two_pi c a b).symm)
    fun heq ↦ hab ?_
  exact (exists_sphere_trace_ellipseCurve_iff c ha hb).1
    (exists_sphere_trace_of_rectifiableSignedArea_eq Real.two_pi_pos.le
      (boundedVariationOn_ellipseCurve_Icc c a b 0 (2 * Real.pi))
      (continuous_ellipseCurve c a b).continuousOn (ellipseCurve_two_pi c a b).symm heq)
/-- **Strict Hurwitz length–area inequality for a non-circular ellipse** (`0 < a`, `0 < b`, `a ≠ b`)
in terms of the 1D Hausdorff measure `μHE[1]` of the trace. -/
theorem four_mul_pi_mul_abs_rectifiableSignedArea_ellipseCurve_lt_hausdorff (c : EuclideanSpace ℝ
    (Fin 2)) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) : 4 * Real.pi *
    |rectifiableSignedArea (ellipseCurve c a b) 0 (2 * Real.pi)| < (μHE[1] (ellipseCurve c a b ''
    Icc 0 (2 * Real.pi))).toReal ^ 2 := by
  rw [euclideanHausdorffMeasure_image_ellipseCurve_Icc c ha.ne' hb.ne']
  exact four_mul_pi_mul_abs_rectifiableSignedArea_ellipseCurve_lt c ha hb hab

end EllipseCurve

end TauCeti
