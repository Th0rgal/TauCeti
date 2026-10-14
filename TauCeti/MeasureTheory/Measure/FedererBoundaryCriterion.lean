/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import TauCeti.MeasureTheory.Measure.BoundedVariationSpace
public import TauCeti.MeasureTheory.Measure.FrontierIsoperimetry
public import TauCeti.MeasureTheory.Measure.RelativeIsoperimetry
import all TauCeti.MeasureTheory.Measure.BoundedVariationSpace
import all TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
import all TauCeti.MeasureTheory.Measure.EssentialBoundary
import all TauCeti.MeasureTheory.Measure.FrontierIsoperimetry
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.ReducedBoundary
import all TauCeti.MeasureTheory.Measure.RelativeIsoperimetry

/-!
# Sobolev–Variation Inequality, De Giorgi Boundary Structure, and Federer's Boundary Criterion

This file links the Gagliardo–Nirenberg–Sobolev inequality to variational total variation, proves
the translation and dilation scaling equivalence for the relative isoperimetric inequality on balls,
develops De Giorgi's reduced-boundary surface measure representation, and establishes Federer's
essential-boundary finite-perimeter criterion and topological-frontier perimeter inequalities:
1. **Sobolev variation bounds and ball scaling equivalence**: `deGiorgiRescale`, ball scaling laws,
   and `eLpNorm_le_distributionalVariation_of_contDiff_of_hasCompactSupport` with a.e./`Lᵖ` limits.
2. **De Giorgi reduced-boundary surface measure**: `reducedBoundaryMeasure`,
   `HasDeGiorgiStructureOn`, `H^{n-1}` equality on reduced/essential boundaries, divergence bounds.
3. **Federer's boundary criterion and frontier bounds**: `SatisfiesFedererCriterionOn`, boundary
   measure comparisons, frontier perimeter bounds, and finite/locally-finite perimeter criteria.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Set TopologicalSpace TestFunction
open TauCeti.MeasureTheory
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

/-! ### Section 1: Gagliardo–Nirenberg–Sobolev `BV` bridge and ball scaling equivalence -/

section SobolevVariationBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- Pointwise extended-norm equality `‖∇ u x‖ₑ = ‖fderiv ℝ u x‖ₑ`. -/
@[simp] theorem enorm_gradient_eq_enorm_fderiv (u : E → ℝ) (x : E) :
    ‖∇ u x‖ₑ = ‖fderiv ℝ u x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_gradient_eq_norm_fderiv]
variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
/-- For a `C¹` function `u : E → ℝ`, `distributionalVariation μ ⊤ u = ∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂μ`. -/
theorem distributionalVariation_top_eq_lintegral_enorm_fderiv [μ.IsAddHaarMeasure]
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    distributionalVariation μ ⊤ u = ∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂μ := by
  rw [distributionalVariation_eq_lintegral_enorm_gradient_of_contDiff hu, Opens.coe_top,
    setLIntegral_univ]
  exact lintegral_congr fun x ↦ enorm_gradient_eq_enorm_fderiv u x
/-- For a `C¹` function `u : E → ℝ`, `eLpNorm (fderiv ℝ u) 1 μ = distributionalVariation μ ⊤ u`. -/
theorem eLpNorm_fderiv_one_eq_distributionalVariation_top [μ.IsAddHaarMeasure]
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    eLpNorm (fderiv ℝ u) 1 μ = distributionalVariation μ ⊤ u := by
  rw [eLpNorm_one_eq_lintegral_enorm (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable,
    distributionalVariation_top_eq_lintegral_enorm_fderiv hu]
/-- For a `C¹` function `u : E → ℝ`, `eLpNorm (∇ u) 1 μ = distributionalVariation μ ⊤ u`. -/
theorem eLpNorm_gradient_one_eq_distributionalVariation_top [μ.IsAddHaarMeasure]
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    eLpNorm (∇ u) 1 μ = distributionalVariation μ ⊤ u := by
  have hcont : Continuous (∇ u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hu.continuous_fderiv one_ne_zero)
  rw [eLpNorm_one_eq_lintegral_enorm hcont.aestronglyMeasurable,
    distributionalVariation_eq_lintegral_enorm_gradient_of_contDiff hu, Opens.coe_top,
    setLIntegral_univ]
/-- **Gagliardo–Nirenberg–Sobolev inequality in terms of `distributionalVariation` for `C¹_c`**. -/
theorem eLpNorm_le_distributionalVariation_of_contDiff_of_hasCompactSupport
    [μ.IsAddHaarMeasure] {u : E → ℝ} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p : ℝ≥0} (hp : NNReal.HolderConjugate (Module.finrank ℝ E) p) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p * distributionalVariation μ ⊤ u := by
  rw [← eLpNorm_fderiv_one_eq_distributionalVariation_top hu]
  exact eLpNorm_le_eLpNorm_fderiv_one μ hu h2u hp
/-- Specialization to `p = NNReal.conjExponent (Module.finrank ℝ E)` when `2 ≤ finrank ℝ E`. -/
theorem eLpNorm_conjExponent_le_distributionalVariation_of_contDiff_of_hasCompactSupport
    [μ.IsAddHaarMeasure] (hn : 2 ≤ Module.finrank ℝ E) {u : E → ℝ}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    eLpNorm u (NNReal.conjExponent (Module.finrank ℝ E)) μ ≤
      eLpNormLESNormFDerivOneConst μ (NNReal.conjExponent (Module.finrank ℝ E)) *
        distributionalVariation μ ⊤ u :=
  eLpNorm_le_distributionalVariation_of_contDiff_of_hasCompactSupport hu h2u
    (.conjExponent (by exact_mod_cast hn))
/-- **Gagliardo–Nirenberg–Sobolev `liminf` bound for a.e. limits of `C¹_c` functions**. -/
theorem eLpNorm_le_liminf_distributionalVariation_of_tendsto_ae [μ.IsAddHaarMeasure]
    {uSeq : ℕ → E → ℝ} {u : E → ℝ} (huSeq : ∀ k, ContDiff ℝ 1 (uSeq k))
    (hsupp : ∀ k, HasCompactSupport (uSeq k)) {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (Module.finrank ℝ E) p) (hu : AEStronglyMeasurable u μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun k ↦ uSeq k x) atTop (𝓝 (u x))) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p *
      atTop.liminf (fun k ↦ distributionalVariation μ ⊤ (uSeq k)) := by
  have hle : ∀ k, eLpNorm (uSeq k) p μ ≤
      (eLpNormLESNormFDerivOneConst μ p : ℝ≥0∞) * distributionalVariation μ ⊤ (uSeq k) :=
    fun k ↦ eLpNorm_le_distributionalVariation_of_contDiff_of_hasCompactSupport
      (huSeq k) (hsupp k) hp
  calc eLpNorm u p μ
      ≤ atTop.liminf (fun k ↦ eLpNorm (uSeq k) p μ) :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm
          (fun k ↦ (huSeq k).continuous.aestronglyMeasurable) u hu hae
    _ ≤ atTop.liminf (fun k ↦ (eLpNormLESNormFDerivOneConst μ p : ℝ≥0∞) *
          distributionalVariation μ ⊤ (uSeq k)) := liminf_le_liminf (Eventually.of_forall hle)
    _ = eLpNormLESNormFDerivOneConst μ p *
          atTop.liminf (fun k ↦ distributionalVariation μ ⊤ (uSeq k)) :=
        ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top
/-- **Gagliardo–Nirenberg–Sobolev `BV` bound via a.e. smooth approximation**. -/
theorem eLpNorm_le_distributionalVariation_of_tendsto_ae [μ.IsAddHaarMeasure]
    {uSeq : ℕ → E → ℝ} {u : E → ℝ} (huSeq : ∀ k, ContDiff ℝ 1 (uSeq k))
    (hsupp : ∀ k, HasCompactSupport (uSeq k)) {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (Module.finrank ℝ E) p) (hu : AEStronglyMeasurable u μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun k ↦ uSeq k x) atTop (𝓝 (u x)))
    (hvar : atTop.liminf (fun k ↦ distributionalVariation μ ⊤ (uSeq k)) ≤
      distributionalVariation μ ⊤ u) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p * distributionalVariation μ ⊤ u :=
  (eLpNorm_le_liminf_distributionalVariation_of_tendsto_ae huSeq hsupp hp hu hae).trans
    (mul_le_mul_of_nonneg_left hvar zero_le)
private lemma le_liminf_of_tendsto_zero_of_le_add {a b : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (ha : Tendsto a atTop (𝓝 0)) (hle : ∀ k, L ≤ a k + b k) : L ≤ atTop.liminf b := by
  rw [le_liminf_iff]
  intro c hc
  filter_upwards [(tendsto_order.1 ha).2 (L - c) (tsub_pos_of_lt hc)] with k hk
  have h1 : a k + c < L := tsub_add_cancel_of_le hc.le ▸ ENNReal.add_lt_add_right hc.ne_top hk
  exact (ENNReal.add_lt_add_iff_left (hk.trans_le le_top).ne).1 (h1.trans_le (hle k))
/-- **Gagliardo–Nirenberg–Sobolev `liminf` bound for `Lᵖ` limits of `C¹_c` functions**. -/
theorem eLpNorm_le_liminf_distributionalVariation_of_tendsto_eLpNorm [μ.IsAddHaarMeasure]
    {uSeq : ℕ → E → ℝ} {u : E → ℝ} (huSeq : ∀ k, ContDiff ℝ 1 (uSeq k))
    (hsupp : ∀ k, HasCompactSupport (uSeq k)) {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (Module.finrank ℝ E) p)
    (hLp : Tendsto (fun k ↦ eLpNorm (uSeq k - u) p μ) atTop (𝓝 0)) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p *
      atTop.liminf (fun k ↦ distributionalVariation μ ⊤ (uSeq k)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp.symm.lt.le
  have hle_sum : ∀ k, eLpNorm u p μ ≤ eLpNorm (uSeq k - u) p μ + eLpNorm (uSeq k) p μ := fun k ↦ by
    have hsplit : u = -(uSeq k - u) + uSeq k := by ext x; simp
    calc eLpNorm u p μ = eLpNorm (-(uSeq k - u) + uSeq k) p μ := by rw [← hsplit]
      _ ≤ eLpNorm (-(uSeq k - u)) p μ + eLpNorm (uSeq k) p μ := eLpNorm_add_le hp1
      _ = eLpNorm (uSeq k - u) p μ + eLpNorm (uSeq k) p μ := by rw [eLpNorm_neg]
  have hle : ∀ k, eLpNorm (uSeq k) p μ ≤
      (eLpNormLESNormFDerivOneConst μ p : ℝ≥0∞) * distributionalVariation μ ⊤ (uSeq k) :=
    fun k ↦ eLpNorm_le_distributionalVariation_of_contDiff_of_hasCompactSupport
      (huSeq k) (hsupp k) hp
  calc eLpNorm u p μ
      ≤ atTop.liminf (fun k ↦ eLpNorm (uSeq k) p μ) :=
        le_liminf_of_tendsto_zero_of_le_add hLp hle_sum
    _ ≤ atTop.liminf (fun k ↦ (eLpNormLESNormFDerivOneConst μ p : ℝ≥0∞) *
          distributionalVariation μ ⊤ (uSeq k)) := liminf_le_liminf (Eventually.of_forall hle)
    _ = eLpNormLESNormFDerivOneConst μ p *
          atTop.liminf (fun k ↦ distributionalVariation μ ⊤ (uSeq k)) :=
        ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top
/-- **Gagliardo–Nirenberg–Sobolev `BV` bound via `Lᵖ` smooth approximation**. -/
theorem eLpNorm_le_distributionalVariation_of_tendsto_eLpNorm [μ.IsAddHaarMeasure]
    {uSeq : ℕ → E → ℝ} {u : E → ℝ} (huSeq : ∀ k, ContDiff ℝ 1 (uSeq k))
    (hsupp : ∀ k, HasCompactSupport (uSeq k)) {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (Module.finrank ℝ E) p)
    (hLp : Tendsto (fun k ↦ eLpNorm (uSeq k - u) p μ) atTop (𝓝 0))
    (hvar : atTop.liminf (fun k ↦ distributionalVariation μ ⊤ (uSeq k)) ≤
      distributionalVariation μ ⊤ u) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p * distributionalVariation μ ⊤ u :=
  (eLpNorm_le_liminf_distributionalVariation_of_tendsto_eLpNorm huSeq hsupp hp hLp).trans
    (mul_le_mul_of_nonneg_left hvar zero_le)
/-- **Indicator specialization**: `μ A ^ (1 / p) ≤ C * perimeter μ A` under smooth approximation. -/
theorem measure_rpow_le_perimeter_of_tendsto_ae [μ.IsAddHaarMeasure] {A : Set E}
    (hA : NullMeasurableSet A μ) {uSeq : ℕ → E → ℝ} (huSeq : ∀ k, ContDiff ℝ 1 (uSeq k))
    (hsupp : ∀ k, HasCompactSupport (uSeq k)) {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (Module.finrank ℝ E) p)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun k ↦ uSeq k x) atTop (𝓝 (A.indicator (fun _ ↦ (1 : ℝ)) x)))
    (hvar : atTop.liminf (fun k ↦ distributionalVariation μ ⊤ (uSeq k)) ≤ perimeter μ A) :
    μ A ^ (1 / (p : ℝ)) ≤ eLpNormLESNormFDerivOneConst μ p * perimeter μ A := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.symm.pos.ne'
  have hind : eLpNorm (A.indicator fun _ ↦ (1 : ℝ)) p μ = μ A ^ (1 / (p : ℝ)) := by
    simpa using eLpNorm_indicator_const₀ hA hp0 ENNReal.coe_ne_top (c := (1 : ℝ))
  rw [← hind]
  exact eLpNorm_le_distributionalVariation_of_tendsto_ae huSeq hsupp hp
    (aestronglyMeasurable_const.indicator₀ hA) hae hvar

end SobolevVariationBridge

/-! #### Affine ball rescaling and equivalence of relative isoperimetric inequalities on balls -/

section BallScalingEquivalence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- **Affine ball rescaling** `deGiorgiRescale s c r = {x : E | r⁻¹ • (x - c) ∈ s}`. -/
def deGiorgiRescale (s : Set E) (c : E) (r : ℝ) : Set E := {x : E | r⁻¹ • (x - c) ∈ s}
@[simp] theorem mem_deGiorgiRescale {s : Set E} {c x : E} {r : ℝ} :
    x ∈ deGiorgiRescale s c r ↔ r⁻¹ • (x - c) ∈ s := Iff.rfl
theorem deGiorgiRescale_eq_preimage (s : Set E) (c : E) (r : ℝ) :
    deGiorgiRescale s c r = (fun x : E ↦ r⁻¹ • (x - c)) ⁻¹' s := rfl
@[simp] theorem deGiorgiBlowUp_deGiorgiRescale (s : Set E) (c : E) {r : ℝ} (hr : r ≠ 0) :
    deGiorgiBlowUp (deGiorgiRescale s c r) c r = s := by
  ext z; simp [deGiorgiBlowUp, deGiorgiRescale, add_sub_cancel_left, inv_smul_smul₀ hr]
@[simp] theorem deGiorgiRescale_deGiorgiBlowUp (s : Set E) (c : E) {r : ℝ} (hr : r ≠ 0) :
    deGiorgiRescale (deGiorgiBlowUp s c r) c r = s := by
  ext x; simp [deGiorgiBlowUp, deGiorgiRescale, smul_inv_smul₀ hr, add_sub_cancel]
@[simp] theorem deGiorgiRescale_compl (s : Set E) (c : E) (r : ℝ) :
    deGiorgiRescale sᶜ c r = (deGiorgiRescale s c r)ᶜ := rfl
@[simp] theorem deGiorgiRescale_unitBall (c : E) {r : ℝ} (hr : 0 < r) :
    deGiorgiRescale (Metric.ball (0 : E) 1) c r = Metric.ball c r := by
  have h := deGiorgiRescale_deGiorgiBlowUp (Metric.ball c (r * 1)) c hr.ne'
  rwa [deGiorgiBlowUp_ball c 1 hr, mul_one] at h
variable [MeasurableSpace E] [BorelSpace E]
theorem measurableSet_deGiorgiRescale {s : Set E} (hs : MeasurableSet s) (c : E) (r : ℝ) :
    MeasurableSet (deGiorgiRescale s c r) := hs.preimage (by fun_prop)
variable [FiniteDimensional ℝ E]
private lemma ofReal_rpow_mul_ofReal_rpow_neg {r : ℝ} (hr : 0 < r) (a : ℝ) :
    ENNReal.ofReal (r ^ a) * ENNReal.ofReal (r ^ (-a)) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le a), ← Real.rpow_add hr, add_neg_cancel,
    Real.rpow_zero, ENNReal.ofReal_one]
/-- **Exact ball-volume scaling identity** relating `Metric.ball c r` and `Metric.ball 0 1`. -/
theorem volume_inter_ball_eq_mul_deGiorgiBlowUp (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    volume (s ∩ Metric.ball c r) = ENNReal.ofReal (r ^ (Module.finrank ℝ E : ℝ)) *
      volume (deGiorgiBlowUp s c r ∩ Metric.ball 0 1) := by
  have h := volume_deGiorgiBlowUp_inter_ball s c 1 hr
  rw [mul_one] at h; rw [h, ← mul_assoc, ofReal_rpow_mul_ofReal_rpow_neg hr, one_mul]
/-- **Exact ball-complement volume scaling identity** on `Metric.ball c r \ s`. -/
theorem volume_ball_diff_eq_mul_deGiorgiBlowUp (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball c r \ s) = ENNReal.ofReal (r ^ (Module.finrank ℝ E : ℝ)) *
      volume (Metric.ball 0 1 \ deGiorgiBlowUp s c r) := by
  have h := volume_ball_diff_deGiorgiBlowUp s c 1 hr
  rw [mul_one] at h; rw [h, ← mul_assoc, ofReal_rpow_mul_ofReal_rpow_neg hr, one_mul]
/-- **Exact `relativeVolumeMin` scaling on `Metric.ball c r`** (`0 < r`). -/
theorem relativeVolumeMin_ball_eq_mul_deGiorgiBlowUp (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    relativeVolumeMin (Metric.ball c r) s = ENNReal.ofReal (r ^ (Module.finrank ℝ E : ℝ)) *
      relativeVolumeMin (Metric.ball 0 1) (deGiorgiBlowUp s c r) := by
  have h := relativeVolumeMin_deGiorgiBlowUp_ball s c 1 hr
  rw [mul_one] at h; rw [h, ← mul_assoc, ofReal_rpow_mul_ofReal_rpow_neg hr, one_mul]
/-- **Exact `relativeIsoperimetricLHS` scaling on `Metric.ball c r`** (`0 < r`, `1 ≤ finrank`). -/
theorem relativeIsoperimetricLHS_ball_eq_mul_deGiorgiBlowUp_of_one_le_finrank
    (hdim : 1 ≤ Module.finrank ℝ E) (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    relativeIsoperimetricLHS (Metric.ball c r) s =
      ENNReal.ofReal (r ^ ((Module.finrank ℝ E : ℝ) - 1)) *
        relativeIsoperimetricLHS (Metric.ball 0 1) (deGiorgiBlowUp s c r) := by
  have h := relativeIsoperimetricLHS_deGiorgiBlowUp_ball_of_one_le_finrank hdim s c 1 hr
  have hneg : (1 : ℝ) - (Module.finrank ℝ E : ℝ) = -((Module.finrank ℝ E : ℝ) - 1) := by ring
  rw [mul_one] at h; rw [h, hneg, ← mul_assoc, ofReal_rpow_mul_ofReal_rpow_neg hr, one_mul]
theorem relativeIsoperimetricLHS_ball_eq_mul_deGiorgiBlowUp [Nontrivial E]
    (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    relativeIsoperimetricLHS (Metric.ball c r) s =
      ENNReal.ofReal (r ^ ((Module.finrank ℝ E : ℝ) - 1)) *
        relativeIsoperimetricLHS (Metric.ball 0 1) (deGiorgiBlowUp s c r) :=
  relativeIsoperimetricLHS_ball_eq_mul_deGiorgiBlowUp_of_one_le_finrank
    (Nat.succ_le_of_lt Module.finrank_pos) s c hr
/-- **Exact `relativePerimeter` scaling on `openBall c r`** (`0 < r`). -/
theorem relativePerimeter_openBall_eq_mul_deGiorgiBlowUp (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    relativePerimeter volume (openBall c r) s =
      ENNReal.ofReal (r ^ ((Module.finrank ℝ E : ℝ) - 1)) *
        relativePerimeter volume (openBall 0 1) (deGiorgiBlowUp s c r) := by
  have h := relativePerimeter_deGiorgiBlowUp_ball s c 1 hr
  have hneg : (1 : ℝ) - (Module.finrank ℝ E : ℝ) = -((Module.finrank ℝ E : ℝ) - 1) := by ring
  rw [mul_one] at h; rw [h, hneg, ← mul_assoc, ofReal_rpow_mul_ofReal_rpow_neg hr, one_mul]
/-- Forward scaling of `relativeVolumeMin` under `deGiorgiRescale s c r` (`0 < r`). -/
@[simp] theorem relativeVolumeMin_ball_deGiorgiRescale (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    relativeVolumeMin (Metric.ball c r) (deGiorgiRescale s c r) =
      ENNReal.ofReal (r ^ (Module.finrank ℝ E : ℝ)) * relativeVolumeMin (Metric.ball 0 1) s := by
  rw [relativeVolumeMin_ball_eq_mul_deGiorgiBlowUp _ c hr,
    deGiorgiBlowUp_deGiorgiRescale s c hr.ne']
/-- Forward scaling of `relativeIsoperimetricLHS` under `deGiorgiRescale s c r` (`0 < r`). -/
@[simp] theorem relativeIsoperimetricLHS_ball_deGiorgiRescale [Nontrivial E]
    (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    relativeIsoperimetricLHS (Metric.ball c r) (deGiorgiRescale s c r) =
      ENNReal.ofReal (r ^ ((Module.finrank ℝ E : ℝ) - 1)) *
        relativeIsoperimetricLHS (Metric.ball 0 1) s := by
  rw [relativeIsoperimetricLHS_ball_eq_mul_deGiorgiBlowUp _ c hr,
    deGiorgiBlowUp_deGiorgiRescale s c hr.ne']
/-- Forward scaling of `relativePerimeter` under `deGiorgiRescale s c r` (`0 < r`). -/
@[simp] theorem relativePerimeter_openBall_deGiorgiRescale (s : Set E) (c : E) {r : ℝ}
    (hr : 0 < r) :
    relativePerimeter volume (openBall c r) (deGiorgiRescale s c r) =
      ENNReal.ofReal (r ^ ((Module.finrank ℝ E : ℝ) - 1)) *
        relativePerimeter volume (openBall 0 1) s := by
  rw [relativePerimeter_openBall_eq_mul_deGiorgiBlowUp _ c hr,
    deGiorgiBlowUp_deGiorgiRescale s c hr.ne']
/-- **Pointwise equivalence between the relative isoperimetric inequality on `Metric.ball c r` and
on the unit ball `Metric.ball 0 1` with the exact same constant `C`**. -/
theorem relativeIsoperimetric_ball_iff_unitBall_deGiorgiBlowUp [Nontrivial E]
    {C : ℝ≥0∞} (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    relativeIsoperimetricLHS (Metric.ball c r) s ≤
        C * relativePerimeter volume (openBall c r) s ↔
      relativeIsoperimetricLHS (Metric.ball (0 : E) 1) (deGiorgiBlowUp s c r) ≤
        C * relativePerimeter volume (openBall (0 : E) 1) (deGiorgiBlowUp s c r) := by
  rw [relativeIsoperimetricLHS_ball_eq_mul_deGiorgiBlowUp s c hr,
    relativePerimeter_openBall_eq_mul_deGiorgiBlowUp s c hr, ← mul_assoc, mul_comm C, mul_assoc]
  exact ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.2 (Real.rpow_pos_of_pos hr _)) ENNReal.ofReal_ne_top
/-- **Pointwise equivalence for `deGiorgiRescale s c r` on `Metric.ball c r`**. -/
theorem relativeIsoperimetric_ball_deGiorgiRescale_iff_unitBall [Nontrivial E]
    {C : ℝ≥0∞} (s : Set E) (c : E) {r : ℝ} (hr : 0 < r) :
    relativeIsoperimetricLHS (Metric.ball c r) (deGiorgiRescale s c r) ≤
        C * relativePerimeter volume (openBall c r) (deGiorgiRescale s c r) ↔
      relativeIsoperimetricLHS (Metric.ball (0 : E) 1) s ≤
        C * relativePerimeter volume (openBall (0 : E) 1) s := by
  rw [relativeIsoperimetric_ball_iff_unitBall_deGiorgiBlowUp _ c hr,
    deGiorgiBlowUp_deGiorgiRescale s c hr.ne']
/-- **Equivalence between the relative isoperimetric inequality on all balls `Metric.ball c r`
(`r > 0`) and on the unit ball `Metric.ball 0 1` with the same dimension-only constant `C`**. -/
theorem relativeIsoperimetric_forall_ball_iff_unitBall [Nontrivial E] {C : ℝ≥0∞} :
    (∀ (c : E) {r : ℝ}, 0 < r → ∀ A : Set E, MeasurableSet A →
        relativeIsoperimetricLHS (Metric.ball c r) A ≤
          C * relativePerimeter volume (openBall c r) A) ↔
      (∀ A : Set E, MeasurableSet A →
        relativeIsoperimetricLHS (Metric.ball (0 : E) 1) A ≤
          C * relativePerimeter volume (openBall (0 : E) 1) A) :=
  ⟨fun h A hA ↦ h 0 zero_lt_one A hA,
    fun h c _ hr _ hA ↦ relativeIsoperimetric_forall_ball_of_unitBall h hA c hr⟩

end BallScalingEquivalence

/-! ### Section 2: De Giorgi reduced-boundary surface measure representation -/

section DeGiorgiStructure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {U V : Opens E}
/-- Bridge between `μH[Module.finrank ℝ E - 1]` and `euclideanHausdorffMeasure` on `E`. -/
theorem hausdorffMeasure_finrank_sub_one_eq [Nontrivial E] :
    (μH[Module.finrank ℝ E - 1] : Measure E) =
      euclideanHausdorffMeasure (Module.finrank ℝ E - 1) := by
  dsimp [euclideanHausdorffMeasure]
  rw [Nat.cast_sub (Nat.succ_le_of_lt Module.finrank_pos), Nat.cast_one]
/-- **De Giorgi reduced-boundary surface measure** `H^{n-1}|_{∂*A}`. -/
def reducedBoundaryMeasure (A : Set E) : Measure E :=
  (μH[Module.finrank ℝ E - 1] : Measure E).restrict (reducedBoundary A)
theorem reducedBoundaryMeasure_apply (A : Set E) {s : Set E} (hs : MeasurableSet s) :
    reducedBoundaryMeasure A s = μH[Module.finrank ℝ E - 1] (s ∩ reducedBoundary A) :=
  Measure.restrict_apply hs
theorem reducedBoundaryMeasure_open (A : Set E) (U : Opens E) :
    reducedBoundaryMeasure A U = μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ U) := by
  rw [reducedBoundaryMeasure_apply A U.isOpen.measurableSet, inter_comm]
@[simp] theorem reducedBoundaryMeasure_compl (A : Set E) :
    reducedBoundaryMeasure Aᶜ = reducedBoundaryMeasure A := by simp [reducedBoundaryMeasure]
theorem reducedBoundaryMeasure_congr_ae {A B : Set E} (h : A =ᵐ[volume] B) :
    reducedBoundaryMeasure A = reducedBoundaryMeasure B := by
  rw [reducedBoundaryMeasure, reducedBoundaryMeasure, reducedBoundary_congr_ae h]
/-- **De Giorgi reduced-boundary structure** on an open set `U : Opens E` for `A : Set E` with
outward unit normal field `ν_A : E → E`: finite relative perimeter in `U`, `H^{n-1}`-nullness of
`(essentialBoundary μ A \ reducedBoundary A) ∩ U`, unit normal on `reducedBoundary A ∩ U`, the
Gauss–Green divergence formula, and variation representation by `H^{n-1}(∂*A ∩ U)`. -/
structure HasDeGiorgiStructureOn (μ : Measure E := by volume_tac) (U : Opens E) (A : Set E)
    (ν_A : E → E) : Prop where
  /-- `A` has finite relative perimeter in `U`. -/
  hasFinitePerimeterIn : HasFinitePerimeterIn μ U A
  /-- `∂^e A \ ∂*A` is `H^{n-1}`-null in `U`. -/
  hausdorffMeasure_essentialBoundary_diff_reducedBoundary :
    μH[Module.finrank ℝ E - 1] ((essentialBoundary μ A \ reducedBoundary A) ∩ U) = 0
  /-- `ν_A` has unit norm on `∂*A ∩ U`. -/
  norm_normal : ∀ x ∈ reducedBoundary A ∩ (U : Set E), ‖ν_A x‖ = 1
  /-- Gauss–Green divergence formula against test vector fields `φ : 𝓓(U, E)`. -/
  setIntegral_divergence : ∀ φ : 𝓓(U, E),
    ∫ x in A ∩ (U : Set E), divergence (φ : E → E) x ∂μ =
      ∫ x in reducedBoundary A ∩ (U : Set E), ⟪(φ : E → E) x, ν_A x⟫_ℝ
        ∂μH[Module.finrank ℝ E - 1]
  /-- Exact representation of the variational total variation by `H^{n-1}(∂*A ∩ U)`. -/
  distributionalVariation_eq_reducedBoundary :
    distributionalVariation μ U (A.indicator fun _ ↦ (1 : ℝ)) =
      μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ U)

namespace HasDeGiorgiStructureOn

variable {A : Set E} {ν_A : E → E}
theorem relativePerimeter_eq_reducedBoundary (h : HasDeGiorgiStructureOn μ U A ν_A) :
    relativePerimeter μ U A = μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ U) :=
  h.distributionalVariation_eq_reducedBoundary
theorem relativePerimeter_eq_reducedBoundaryMeasure (h : HasDeGiorgiStructureOn μ U A ν_A) :
    relativePerimeter μ U A = reducedBoundaryMeasure A U := by
  rw [h.relativePerimeter_eq_reducedBoundary, reducedBoundaryMeasure_open]
theorem hausdorffMeasure_reducedBoundary_lt_top (h : HasDeGiorgiStructureOn μ U A ν_A) :
    μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ U) < ⊤ :=
  h.relativePerimeter_eq_reducedBoundary ▸ h.hasFinitePerimeterIn.2
/-- Equality `H^{n-1}(essentialBoundary μ A ∩ U) = H^{n-1}(reducedBoundary A ∩ U)` under
`reducedBoundary A ⊆ essentialBoundary μ A`. -/
theorem hausdorffMeasure_essentialBoundary_eq_of_subset
    (h : HasDeGiorgiStructureOn μ U A ν_A) (hsub : reducedBoundary A ⊆ essentialBoundary μ A) :
    μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) =
      μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ U) := by
  refine le_antisymm ?_ (measure_mono (inter_subset_inter_left _ hsub))
  have hunion : essentialBoundary μ A ∩ (U : Set E) ⊆
      (reducedBoundary A ∩ U) ∪ ((essentialBoundary μ A \ reducedBoundary A) ∩ U) :=
    fun x ⟨hxe, hxU⟩ ↦ (em (x ∈ reducedBoundary A)).elim
      (fun hxr ↦ Or.inl ⟨hxr, hxU⟩) (fun hxr ↦ Or.inr ⟨⟨hxe, hxr⟩, hxU⟩)
  exact (measure_mono hunion).trans ((measure_union_le _ _).trans_eq
    (by rw [h.hausdorffMeasure_essentialBoundary_diff_reducedBoundary, add_zero]))
/-- **Equality of `H^{n-1}` on the essential and reduced boundaries in `U`**. -/
theorem hausdorffMeasure_essentialBoundary_eq (h : HasDeGiorgiStructureOn μ U A ν_A)
    (_hm : MeasurableSet (reducedBoundary A)) (hsub : reducedBoundary A ⊆ essentialBoundary μ A) :
    μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) =
      μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ U) :=
  h.hausdorffMeasure_essentialBoundary_eq_of_subset hsub
/-- Specialization of `hausdorffMeasure_essentialBoundary_eq_of_subset` to `μ = volume`. -/
theorem hausdorffMeasure_essentialBoundary_volume_eq (h : HasDeGiorgiStructureOn volume U A ν_A) :
    μH[Module.finrank ℝ E - 1] (essentialBoundary volume A ∩ U) =
      μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ U) :=
  h.hausdorffMeasure_essentialBoundary_eq_of_subset (reducedBoundary_subset_essentialBoundary A)
/-- **Exact representation of `distributionalVariation` by `H^{n-1}(∂^e A ∩ U)`**. -/
theorem distributionalVariation_eq_essentialBoundary (h : HasDeGiorgiStructureOn μ U A ν_A)
    (hsub : reducedBoundary A ⊆ essentialBoundary μ A) :
    distributionalVariation μ U (A.indicator fun _ ↦ (1 : ℝ)) =
      μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) := by
  rw [h.distributionalVariation_eq_reducedBoundary,
    h.hausdorffMeasure_essentialBoundary_eq_of_subset hsub]
theorem relativePerimeter_eq_essentialBoundary (h : HasDeGiorgiStructureOn μ U A ν_A)
    (hsub : reducedBoundary A ⊆ essentialBoundary μ A) :
    relativePerimeter μ U A = μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) :=
  h.distributionalVariation_eq_essentialBoundary hsub
theorem distributionalVariation_eq_essentialBoundary_volume
    (h : HasDeGiorgiStructureOn volume U A ν_A) :
    distributionalVariation volume U (A.indicator fun _ ↦ (1 : ℝ)) =
      μH[Module.finrank ℝ E - 1] (essentialBoundary volume A ∩ U) :=
  h.distributionalVariation_eq_essentialBoundary (reducedBoundary_subset_essentialBoundary A)
/-- **Gauss–Green divergence bound**: for any test field `φ : 𝓓(U, E)` with `∀ x, ‖φ x‖ ≤ 1`,
`|∫ x in A ∩ U, divergence φ x ∂μ| ≤ (μH[finrank ℝ E - 1] (reducedBoundary A ∩ U)).toReal`. -/
theorem abs_integral_divergence_le (h : HasDeGiorgiStructureOn μ U A ν_A) {φ : 𝓓(U, E)}
    (hφ : ∀ x, ‖(φ : E → E) x‖ ≤ 1) :
    |∫ x in A ∩ (U : Set E), divergence (φ : E → E) x ∂μ| ≤
      (μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ U)).toReal := by
  have hind : (fun x ↦ A.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x) =
      A.indicator (divergence (φ : E → E)) := by ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hint_eq : ∫ x in A ∩ (U : Set E), divergence (φ : E → E) x ∂μ =
      ∫ x in (U : Set E), A.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ := by
    rw [hind, integral_indicator₀ h.hasFinitePerimeterIn.1,
      Measure.restrict_restrict₀ h.hasFinitePerimeterIn.1]
  have hofReal : ENNReal.ofReal |∫ x in A ∩ (U : Set E), divergence (φ : E → E) x ∂μ| ≤
      μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ U) := by
    rw [hint_eq, ← h.distributionalVariation_eq_reducedBoundary,
      distributionalVariation_eq_iSup_abs]
    exact le_iSup₂_of_le φ hφ le_rfl
  exact (ENNReal.ofReal_le_iff_le_toReal h.hausdorffMeasure_reducedBoundary_lt_top.ne).1 hofReal
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma essentialBoundary_compl_inter_open [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    (hA : NullMeasurableSet A (μ.restrict U)) :
    essentialBoundary μ Aᶜ ∩ (U : Set E) = essentialBoundary μ A ∩ (U : Set E) := by
  have hsum : ∀ x ∈ (U : Set E), ∀ᶠ r in 𝓝[>] 0,
      μ (A ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) +
        μ (Aᶜ ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) = 1 := fun x hxU ↦ by
    obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (U.isOpen.mem_nhds hxU)
    filter_upwards [Ioc_mem_nhdsGT hR, eventually_measure_closedBall_ne_zero (μ := μ) x,
      eventually_measure_closedBall_ne_top (μ := μ) x] with r hr h0 htop
    let B := Metric.closedBall x r
    have hBU : B ⊆ (U : Set E) := (closedBall_subset_closedBall hr.2).trans hRU
    have h_eq : ∀ s : Set E, (μ.restrict U) (s ∩ B) = μ (s ∩ B) := fun s ↦ by
      rw [Measure.restrict_apply' U.isOpen.measurableSet,
        inter_eq_left.2 (inter_subset_right.trans hBU)]
    have hadd := measure_inter_add_sdiff₀ B hA
    rw [inter_comm B A, sdiff_eq, h_eq A, inter_comm B Aᶜ, h_eq Aᶜ, ← univ_inter B, h_eq univ,
      univ_inter] at hadd
    rw [← ENNReal.add_div, hadd, ENNReal.div_self h0 htop]
  have h10 : ∀ x ∈ (U : Set E),
      (HasMeasureDensityAt μ Aᶜ x 1 ↔ HasMeasureDensityAt μ A x 0) ∧
        (HasMeasureDensityAt μ Aᶜ x 0 ↔ HasMeasureDensityAt μ A x 1) := fun x hxU ↦ by
    have hcompl : ∀ {s t : Set E} {d : ℝ≥0∞},
        (∀ᶠ r in 𝓝[>] 0, μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) +
          μ (t ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) = 1) →
        HasMeasureDensityAt μ s x d → HasMeasureDensityAt μ t x (1 - d) := fun hst hd ↦ by
      refine (ENNReal.Tendsto.sub tendsto_const_nhds hd (Or.inl ENNReal.one_ne_top)).congr' ?_
      filter_upwards [hst] with r hr
      rw [← hr, add_comm, ENNReal.add_sub_cancel_right]
      exact ((ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right))
        |>.trans_lt ENNReal.one_lt_top).ne
    have hsum' : ∀ᶠ r in 𝓝[>] 0,
        μ (Aᶜ ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) +
          μ (A ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) = 1 :=
      (hsum x hxU).mono fun r hr ↦ by rwa [add_comm]
    exact ⟨⟨fun h ↦ by simpa using hcompl hsum' h, fun h ↦ by simpa using hcompl (hsum x hxU) h⟩,
      ⟨fun h ↦ by simpa using hcompl hsum' h, fun h ↦ by simpa using hcompl (hsum x hxU) h⟩⟩
  ext x; simp only [mem_inter_iff, mem_essentialBoundary_iff]
  exact and_congr_left fun hxU ↦ by rw [(h10 x hxU).1, (h10 x hxU).2, and_comm]
/-- **Complement invariance of `HasDeGiorgiStructureOn`** with reversed unit normal `-ν_A`. -/
theorem compl [μ.IsAddHaarMeasure] (h : HasDeGiorgiStructureOn μ U A ν_A) :
    HasDeGiorgiStructureOn μ U Aᶜ (-ν_A) where
  hasFinitePerimeterIn := h.hasFinitePerimeterIn.compl
  hausdorffMeasure_essentialBoundary_diff_reducedBoundary := by
    have heq : (essentialBoundary μ Aᶜ \ reducedBoundary Aᶜ) ∩ (U : Set E) =
        (essentialBoundary μ A \ reducedBoundary A) ∩ (U : Set E) := by
      rw [reducedBoundary_compl, sdiff_inter_right_comm,
        essentialBoundary_compl_inter_open h.hasFinitePerimeterIn.1, ← sdiff_inter_right_comm]
    rw [heq]; exact h.hausdorffMeasure_essentialBoundary_diff_reducedBoundary
  norm_normal x hx := by rw [reducedBoundary_compl] at hx; simp [h.norm_normal x hx]
  setIntegral_divergence φ := by
    have hA := h.hasFinitePerimeterIn.1
    have hint : IntegrableOn (divergence (φ : E → E)) U μ :=
      (integrable_divergence_testFunction φ).integrableOn
    have hadd := integral_add_compl₀ hA hint
    rw [Measure.restrict_restrict₀ hA, Measure.restrict_restrict₀ hA.compl,
      integral_divergence_testFunction_eq_zero φ, add_eq_zero_iff_eq_neg'] at hadd
    simp only [Pi.neg_apply, inner_neg_right, integral_neg, reducedBoundary_compl, hadd,
      h.setIntegral_divergence φ]
  distributionalVariation_eq_reducedBoundary := by
    change relativePerimeter μ U Aᶜ = μH[Module.finrank ℝ E - 1] (reducedBoundary Aᶜ ∩ U)
    rw [relativePerimeter_compl, reducedBoundary_compl, h.relativePerimeter_eq_reducedBoundary]
/-- **Open localization of `HasDeGiorgiStructureOn`** to an open subset `V ≤ U`. -/
theorem mono_open (h : HasDeGiorgiStructureOn μ U A ν_A) (hVU : V ≤ U)
    (hvar : distributionalVariation μ V (A.indicator fun _ ↦ (1 : ℝ)) =
      μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ V)) :
    HasDeGiorgiStructureOn μ V A ν_A where
  hasFinitePerimeterIn :=
    ⟨h.hasFinitePerimeterIn.1.mono (Measure.restrict_mono hVU le_rfl),
      (relativePerimeter_mono hVU A).trans_lt h.hasFinitePerimeterIn.2⟩
  hausdorffMeasure_essentialBoundary_diff_reducedBoundary :=
    measure_mono_null (inter_subset_inter_right _ hVU)
      h.hausdorffMeasure_essentialBoundary_diff_reducedBoundary
  norm_normal x hx := h.norm_normal x ⟨hx.1, hVU hx.2⟩
  setIntegral_divergence φ := by
    let ψ : 𝓓(U, E) := TestFunction.monoCLM ℝ φ
    have hψ : (ψ : E → E) = (φ : E → E) := funext fun x ↦ by
      simp [ψ, TestFunction.monoCLM_apply, hVU]
    have h_loc : ∀ (ν : Measure E) (S : Set E) (f : E → ℝ), (∀ x ∉ (V : Set E), f x = 0) →
        ∫ x in S ∩ (V : Set E), f x ∂ν = ∫ x in S ∩ (U : Set E), f x ∂ν := fun ν S f hf ↦ by
      rw [inter_comm S (V : Set E), inter_comm S (U : Set E),
        ← Measure.restrict_restrict V.isOpen.measurableSet,
        ← Measure.restrict_restrict U.isOpen.measurableSet,
        setIntegral_eq_integral_of_forall_compl_eq_zero hf,
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hxU ↦ hf x (fun hxV ↦ hxU (hVU hxV))]
    rw [h_loc μ A _ (fun x hx ↦ divergence_testFunction_eq_zero_of_notMem φ hx),
      h_loc _ (reducedBoundary A) _ (fun x hx ↦ by simp [φ.zero_on_compl hx]),
      ← hψ, h.setIntegral_divergence ψ]
  distributionalVariation_eq_reducedBoundary := hvar

end HasDeGiorgiStructureOn

@[simp] theorem hasDeGiorgiStructureOn_compl_iff [μ.IsAddHaarMeasure] {A : Set E} {ν_A : E → E} :
    HasDeGiorgiStructureOn μ U Aᶜ (-ν_A) ↔ HasDeGiorgiStructureOn μ U A ν_A :=
  ⟨fun h ↦ by simpa using h.compl, fun h ↦ h.compl⟩

end DeGiorgiStructure

/-! ### Section 3: Federer's essential-boundary criterion and topological-frontier bounds -/

section FedererCriterion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {U V : Opens E}
/-- **Federer's essential-boundary perimeter inequality** on an open set `U : Opens E`:
`distributionalVariation μ U (A.indicator 1) ≤ μH[finrank ℝ E - 1] (essentialBoundary μ A ∩ U)`. -/
def SatisfiesFedererCriterionOn (μ : Measure E := by volume_tac) (U : Opens E) (A : Set E) :
    Prop :=
  distributionalVariation μ U (A.indicator fun _ ↦ (1 : ℝ)) ≤
    μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U)
theorem satisfiesFedererCriterionOn_iff_relativePerimeter_le {A : Set E} :
    SatisfiesFedererCriterionOn μ U A ↔
      relativePerimeter μ U A ≤ μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) := Iff.rfl
theorem SatisfiesFedererCriterionOn.distributionalVariation_le {A : Set E}
    (h : SatisfiesFedererCriterionOn μ U A) :
    distributionalVariation μ U (A.indicator fun _ ↦ (1 : ℝ)) ≤
      μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) := h
theorem SatisfiesFedererCriterionOn.relativePerimeter_le {A : Set E}
    (h : SatisfiesFedererCriterionOn μ U A) :
    relativePerimeter μ U A ≤ μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) := h
@[simp] theorem satisfiesFedererCriterionOn_empty : SatisfiesFedererCriterionOn μ U ∅ := by
  simp [SatisfiesFedererCriterionOn]
theorem SatisfiesFedererCriterionOn.congr_ae {A B : Set E}
    (h : SatisfiesFedererCriterionOn μ U A) (hAB : A =ᵐ[μ] B) :
    SatisfiesFedererCriterionOn μ U B := by
  rw [satisfiesFedererCriterionOn_iff_relativePerimeter_le,
    ← relativePerimeter_congr_ae (ae_restrict_of_ae hAB), ← essentialBoundary_congr_ae hAB]
  exact h
theorem satisfiesFedererCriterionOn_congr_ae {A B : Set E} (hAB : A =ᵐ[μ] B) :
    SatisfiesFedererCriterionOn μ U A ↔ SatisfiesFedererCriterionOn μ U B :=
  ⟨fun h ↦ h.congr_ae hAB, fun h ↦ h.congr_ae hAB.symm⟩
/-- **Unconditional local Hausdorff measure comparison** between `essentialBoundary` and `frontier`
for any `A, S : Set E` (with no finiteness, measurability, or smoothness hypothesis). -/
theorem hausdorffMeasure_essentialBoundary_inter_le_frontier
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] (A S : Set E) :
    μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ S) ≤
      μH[Module.finrank ℝ E - 1] (frontier A ∩ S) :=
  measure_mono (inter_subset_inter_left S (essentialBoundary_subset_frontier A))
/-- **Unconditional open-set Hausdorff measure comparison** between `essentialBoundary` and
`frontier`. -/
theorem hausdorffMeasure_essentialBoundary_inter_open_le_frontier
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] (U : Opens E) (A : Set E) :
    μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) ≤
      μH[Module.finrank ℝ E - 1] (frontier A ∩ U) :=
  hausdorffMeasure_essentialBoundary_inter_le_frontier A U
/-- **Unconditional global Hausdorff measure comparison** between `essentialBoundary` and
`frontier`. -/
theorem hausdorffMeasure_essentialBoundary_le_frontier
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] (A : Set E) :
    μH[Module.finrank ℝ E - 1] (essentialBoundary μ A) ≤
      μH[Module.finrank ℝ E - 1] (frontier A) :=
  measure_mono (essentialBoundary_subset_frontier A)
/-- **Local extended topological-frontier variation bound** from `SatisfiesFedererCriterionOn`. -/
theorem SatisfiesFedererCriterionOn.distributionalVariation_le_hausdorffMeasure_frontier
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] {A : Set E}
    (h : SatisfiesFedererCriterionOn μ U A) :
    distributionalVariation μ U (A.indicator fun _ ↦ (1 : ℝ)) ≤
      μH[Module.finrank ℝ E - 1] (frontier A ∩ U) :=
  h.trans (hausdorffMeasure_essentialBoundary_inter_open_le_frontier U A)
/-- **Local extended topological-frontier relative perimeter bound**. -/
theorem SatisfiesFedererCriterionOn.relativePerimeter_le_hausdorffMeasure_frontier
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] {A : Set E}
    (h : SatisfiesFedererCriterionOn μ U A) :
    relativePerimeter μ U A ≤ μH[Module.finrank ℝ E - 1] (frontier A ∩ U) :=
  h.distributionalVariation_le_hausdorffMeasure_frontier
/-- **Global extended topological-frontier variation bound (`U = ⊤`)**. -/
theorem SatisfiesFedererCriterionOn.distributionalVariation_top_le_hausdorffMeasure_frontier
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] {A : Set E}
    (h : SatisfiesFedererCriterionOn μ ⊤ A) :
    distributionalVariation μ ⊤ (A.indicator fun _ ↦ (1 : ℝ)) ≤
      μH[Module.finrank ℝ E - 1] (frontier A) := by
  simpa using h.distributionalVariation_le_hausdorffMeasure_frontier
/-- **Global extended topological-frontier perimeter bound (`U = ⊤`)**:
`perimeter μ A ≤ μH[Module.finrank ℝ E - 1] (frontier A)`. -/
theorem SatisfiesFedererCriterionOn.perimeter_le_hausdorffMeasure_frontier
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] {A : Set E}
    (h : SatisfiesFedererCriterionOn μ ⊤ A) :
    perimeter μ A ≤ μH[Module.finrank ℝ E - 1] (frontier A) :=
  h.distributionalVariation_top_le_hausdorffMeasure_frontier
/-- **Federer's converse finite-perimeter criterion (variation form)**. -/
theorem SatisfiesFedererCriterionOn.distributionalVariation_lt_top_of_essentialBoundary_lt_top
    {A : Set E} (h : SatisfiesFedererCriterionOn μ U A)
    (hfin : μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) < ⊤) :
    distributionalVariation μ U (A.indicator fun _ ↦ (1 : ℝ)) < ⊤ := h.trans_lt hfin
theorem SatisfiesFedererCriterionOn.relativePerimeter_lt_top_of_essentialBoundary_lt_top
    {A : Set E} (h : SatisfiesFedererCriterionOn μ U A)
    (hfin : μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) < ⊤) :
    relativePerimeter μ U A < ⊤ := h.trans_lt hfin
/-- **Federer's converse finite-perimeter criterion on `U`**. -/
theorem SatisfiesFedererCriterionOn.hasFinitePerimeterIn_of_essentialBoundary_lt_top
    {A : Set E} (hA : NullMeasurableSet A (μ.restrict U)) (h : SatisfiesFedererCriterionOn μ U A)
    (hfin : μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ U) < ⊤) :
    HasFinitePerimeterIn μ U A := ⟨hA, h.trans_lt hfin⟩
/-- **Global Federer finite-perimeter criterion (`U = ⊤`)**. -/
theorem SatisfiesFedererCriterionOn.hasFinitePerimeter_of_essentialBoundary_lt_top
    {A : Set E} (hA : NullMeasurableSet A μ) (h : SatisfiesFedererCriterionOn μ ⊤ A)
    (hfin : μH[Module.finrank ℝ E - 1] (essentialBoundary μ A) < ⊤) :
    HasFinitePerimeter μ A :=
  ⟨hA.mono Measure.restrict_le_self, h.trans_lt (by simpa using hfin)⟩
/-- **Topological-frontier finite-perimeter criterion (variation form)**. -/
theorem SatisfiesFedererCriterionOn.distributionalVariation_lt_top_of_frontier_lt_top
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] {A : Set E}
    (h : SatisfiesFedererCriterionOn μ U A)
    (hfin : μH[Module.finrank ℝ E - 1] (frontier A ∩ U) < ⊤) :
    distributionalVariation μ U (A.indicator fun _ ↦ (1 : ℝ)) < ⊤ :=
  h.distributionalVariation_le_hausdorffMeasure_frontier.trans_lt hfin
theorem SatisfiesFedererCriterionOn.relativePerimeter_lt_top_of_frontier_lt_top
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] {A : Set E}
    (h : SatisfiesFedererCriterionOn μ U A)
    (hfin : μH[Module.finrank ℝ E - 1] (frontier A ∩ U) < ⊤) :
    relativePerimeter μ U A < ⊤ :=
  h.distributionalVariation_lt_top_of_frontier_lt_top hfin
/-- **Topological-frontier finite-perimeter criterion on `U`**. -/
theorem SatisfiesFedererCriterionOn.hasFinitePerimeterIn_of_frontier_lt_top
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] {A : Set E}
    (hA : NullMeasurableSet A (μ.restrict U)) (h : SatisfiesFedererCriterionOn μ U A)
    (hfin : μH[Module.finrank ℝ E - 1] (frontier A ∩ U) < ⊤) :
    HasFinitePerimeterIn μ U A :=
  ⟨hA, h.relativePerimeter_lt_top_of_frontier_lt_top hfin⟩
/-- **Federer's local finite-perimeter criterion on `U`**. -/
theorem hasLocallyFinitePerimeterIn_of_satisfiesFedererCriterionOn {A : Set E}
    (hA : NullMeasurableSet A (μ.restrict U))
    (hK : ∀ K : Opens E, IsCompact (closure (K : Set E)) → closure (K : Set E) ⊆ U →
      SatisfiesFedererCriterionOn μ K A ∧
        μH[Module.finrank ℝ E - 1] (essentialBoundary μ A ∩ K) < ⊤) :
    HasLocallyFinitePerimeterIn μ U A :=
  ⟨hA, fun K hKc hKU ↦
    (hK K hKc hKU).1.relativePerimeter_lt_top_of_essentialBoundary_lt_top (hK K hKc hKU).2⟩
/-- **Topological-frontier local finite-perimeter criterion on `U`**. -/
theorem hasLocallyFinitePerimeterIn_of_frontier_lt_top
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] {A : Set E}
    (hA : NullMeasurableSet A (μ.restrict U))
    (hK : ∀ K : Opens E, IsCompact (closure (K : Set E)) → closure (K : Set E) ⊆ U →
      SatisfiesFedererCriterionOn μ K A ∧
        μH[Module.finrank ℝ E - 1] (frontier A ∩ K) < ⊤) :
    HasLocallyFinitePerimeterIn μ U A :=
  ⟨hA, fun K hKc hKU ↦
    (hK K hKc hKU).1.relativePerimeter_lt_top_of_frontier_lt_top (hK K hKc hKU).2⟩
variable [FiniteDimensional ℝ E]
@[simp] theorem satisfiesFedererCriterionOn_univ [μ.IsAddHaarMeasure] :
    SatisfiesFedererCriterionOn μ U Set.univ := by simp [SatisfiesFedererCriterionOn]
theorem SatisfiesFedererCriterionOn.compl [μ.IsAddHaarMeasure] {A : Set E}
    (hA : NullMeasurableSet A (μ.restrict U)) (h : SatisfiesFedererCriterionOn μ U A) :
    SatisfiesFedererCriterionOn μ U Aᶜ := by
  rw [satisfiesFedererCriterionOn_iff_relativePerimeter_le, relativePerimeter_compl,
    HasDeGiorgiStructureOn.essentialBoundary_compl_inter_open hA]
  exact h
/-- **Every set with De Giorgi structure on `U` satisfies Federer's boundary inequality on `U`**. -/
theorem HasDeGiorgiStructureOn.satisfiesFedererCriterionOn {A : Set E} {ν_A : E → E}
    (h : HasDeGiorgiStructureOn μ U A ν_A) (hsub : reducedBoundary A ⊆ essentialBoundary μ A) :
    SatisfiesFedererCriterionOn μ U A :=
  (h.distributionalVariation_eq_essentialBoundary hsub).le
/-- Specialization of `HasDeGiorgiStructureOn.satisfiesFedererCriterionOn` to `μ = volume`. -/
theorem HasDeGiorgiStructureOn.satisfiesFedererCriterionOn_volume {A : Set E} {ν_A : E → E}
    (h : HasDeGiorgiStructureOn volume U A ν_A) :
    SatisfiesFedererCriterionOn volume U A :=
  h.satisfiesFedererCriterionOn (reducedBoundary_subset_essentialBoundary A)
/-- **Unconditional Hausdorff measure comparison between reduced and essential boundaries**. -/
theorem hausdorffMeasure_reducedBoundary_inter_le_essentialBoundary (A S : Set E) :
    μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ S) ≤
      μH[Module.finrank ℝ E - 1] (essentialBoundary volume A ∩ S) :=
  measure_mono (inter_subset_inter_left S (reducedBoundary_subset_essentialBoundary A))
theorem hausdorffMeasure_reducedBoundary_le_essentialBoundary (A : Set E) :
    μH[Module.finrank ℝ E - 1] (reducedBoundary A) ≤
      μH[Module.finrank ℝ E - 1] (essentialBoundary volume A) :=
  measure_mono (reducedBoundary_subset_essentialBoundary A)
/-- **Unconditional Hausdorff measure comparison between reduced boundary and `frontier`**. -/
theorem hausdorffMeasure_reducedBoundary_inter_le_frontier (A S : Set E) :
    μH[Module.finrank ℝ E - 1] (reducedBoundary A ∩ S) ≤
      μH[Module.finrank ℝ E - 1] (frontier A ∩ S) :=
  measure_mono (inter_subset_inter_left S (reducedBoundary_subset_frontier A))
theorem hausdorffMeasure_reducedBoundary_le_frontier (A : Set E) :
    μH[Module.finrank ℝ E - 1] (reducedBoundary A) ≤
      μH[Module.finrank ℝ E - 1] (frontier A) :=
  measure_mono (reducedBoundary_subset_frontier A)
/-- Direct deduction of `relativePerimeter μ U A ≤ μH[Module.finrank ℝ E - 1] (frontier A ∩ U)` from
`HasDeGiorgiStructureOn`. -/
theorem HasDeGiorgiStructureOn.relativePerimeter_le_hausdorffMeasure_frontier
    [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] {A : Set E} {ν_A : E → E}
    (h : HasDeGiorgiStructureOn μ U A ν_A) (hsub : reducedBoundary A ⊆ essentialBoundary μ A) :
    relativePerimeter μ U A ≤ μH[Module.finrank ℝ E - 1] (frontier A ∩ U) :=
  (h.satisfiesFedererCriterionOn hsub).relativePerimeter_le_hausdorffMeasure_frontier
/-- **Global topological-frontier finite-perimeter criterion (`U = ⊤`, requiring no measurability
hypothesis on `A`)** when `[Nontrivial E]` and `μH[Module.finrank ℝ E - 1] (frontier A) < ⊤`. -/
theorem SatisfiesFedererCriterionOn.hasFinitePerimeter_of_frontier_lt_top
    [Nontrivial E] [μ.IsAddHaarMeasure] {A : Set E}
    (h : SatisfiesFedererCriterionOn μ ⊤ A)
    (hfin : μH[Module.finrank ℝ E - 1] (frontier A) < ⊤) :
    HasFinitePerimeter μ A := by
  have hfin' : euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier A) < ⊤ := by
    rwa [← hausdorffMeasure_finrank_sub_one_eq]
  obtain ⟨_, hmeas, _, _, _, _⟩ :=
    nullMeasurableSet_and_interior_ae_eq_of_hausdorffMeasure_frontier_lt_top (μ := μ) hfin'
  exact ⟨hmeas.mono Measure.restrict_le_self,
    h.perimeter_le_hausdorffMeasure_frontier.trans_lt hfin⟩
/-- **Extended topological-frontier isoperimetric inequality via `SatisfiesFedererCriterionOn`**. -/
theorem SatisfiesFedererCriterionOn.isoperimetricBound_le_hausdorffMeasure_frontier
    [Nontrivial E] {A : Set E} (h : SatisfiesFedererCriterionOn volume ⊤ A)
    (hiso : volume (frontier A) = 0 → NullMeasurableSet A volume →
      isoperimetricBound (interior A) ≤ perimeter volume (interior A)) :
    isoperimetricBound A ≤ μH[Module.finrank ℝ E - 1] (frontier A) := by
  rw [hausdorffMeasure_finrank_sub_one_eq]
  refine TauCeti.isoperimetricBound_le_hausdorffMeasure_frontier A hiso fun _ _ ↦ ?_
  rw [← hausdorffMeasure_finrank_sub_one_eq]
  exact h.perimeter_le_hausdorffMeasure_frontier

end FedererCriterion

end TauCeti
