/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import TauCeti.MeasureTheory.Measure.PolarIntegration
import all TauCeti.MeasureTheory.Function.SchwarzRearrangement
import all TauCeti.MeasureTheory.Function.SchwarzRadialProfile
import all TauCeti.MeasureTheory.Function.SchwarzLp
import all TauCeti.MeasureTheory.Measure.PolyaSzego
import all TauCeti.MeasureTheory.Measure.PolarIntegration

/-!
# Radial Profile Absolute Continuity on Annuli, Gradient Decomposition, and Origin Decay

This file develops the radial analysis infrastructure connecting spherical polar integration on
`EuclideanSpace ℝ (Fin n)` to compact-interval absolute continuity and boundary decay at the
origin:

1. **Pinned radial profile finiteness (`r > 0`) and monotone pointwise transport**:
   Markov superlevel-volume inequalities in `ℝ` (`mul_toReal_measure_lt_le_integral`,
   `mul_le_integral_of_le_toReal_measure_lt`, `le_div_integral_of_le_toReal_measure_lt`),
   explicit `L¹` radial upper bounds (`unitBallVolume_mul_pow_schwarzRadialProfileReal_le_integral`,
   `schwarzRadialProfileReal_le_integral_div`, `schwarzRearrangementReal_le_integral_div_norm_pow`),
   and pointwise transport on `(0, ∞)` and `[a, b)` upgrading almost-everywhere equality to
   pointwise equality for right-continuous or antitone profiles
   (`eqOn_Ioi_of_continuousWithinAt_Ici_of_ae_eq`,
   `eqOn_Ioi_of_antitoneOn_of_continuousOn_of_ae_eq`,
   `eqOn_Ico_of_continuousWithinAt_Ici_of_continuousOn_of_ae_eq`).
2. **Radial and tangential gradient decomposition and annulus-to-interval integrability**:
   Orthogonal decomposition `g = radialProjection x g + tangentialProjection x g` along
   `radialUnitDir x = ‖x‖⁻¹ • x`, Pythagorean identity
   `‖g‖ ^ 2 = radialComponent x g ^ 2 + ‖tangentialProjection x g‖ ^ 2`, vanishing tangential
   component for radial functions `x ↦ v ‖x‖`, and compact-subinterval `[a, b] ⊆ (0, ∞)` unweighted
   integrability of radial derivative densities from `r ^ (n - 1)`-weighted polar bounds.
3. **Origin decay `r ^ (n - 1) * v r → 0` as `r → 0⁺` for `n ≥ 2`**:
   Two-radius weighted integral bounds `r ^ m * v r ≤ r ^ m * v R + ∫ s in Ioc 0 R, d s * s ^ m`
   for any nonnegative radial derivative density `d` controlling `v r - v R`, and the resulting
   origin limit `Tendsto (fun r ↦ r ^ (n - 1) * v r) (𝓝[>] 0) (𝓝 0)` when `n ≥ 2`.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Gradient

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

/-! ### Section 1: Pinned radial profile finiteness and monotone pointwise transport -/

/-- Lower Lebesgue Markov inequality for the real superlevel set `{x | t < u x}`. -/
theorem ofReal_mul_measure_lt_le_lintegral {μ : Measure α} {u : α → ℝ}
    (hu : AEMeasurable u μ) (t : ℝ) :
    ENNReal.ofReal t * μ {x | t < u x} ≤ ∫⁻ x, ENNReal.ofReal (u x) ∂μ := by
  rcases le_or_gt t 0 with ht | ht
  · simp [ENNReal.ofReal_of_nonpos ht]
  · refine (mul_le_mul_right (measure_mono ?_) (ENNReal.ofReal t)).trans
      (mul_measure_lt_le_lintegral hu.ennreal_ofReal (ENNReal.ofReal t))
    intro x (hx : t < u x)
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hx
/-- For an integrable real-valued function `u` and `t > 0`, the superlevel set `{x | t < u x}` has
finite measure. -/
theorem measure_lt_lt_top_of_integrable {μ : Measure α} {u : α → ℝ}
    (hu : Integrable u μ) {t : ℝ} (ht : 0 < t) :
    μ {x | t < u x} < ⊤ := by
  have hlint_lt_top : ∫⁻ x, ENNReal.ofReal (u x) ∂μ < ⊤ := by
    refine (lintegral_mono fun x ↦ ?_).trans_lt hu.hasFiniteIntegral
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self (u x))
  have hmul := (ofReal_mul_measure_lt_le_lintegral hu.aestronglyMeasurable.aemeasurable t).trans_lt
    hlint_lt_top
  have ht_ne : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  by_contra! htop
  rw [top_le_iff.mp htop, ENNReal.mul_top ht_ne] at hmul
  exact lt_irrefl ⊤ hmul
/-- **Real Markov superlevel-volume inequality**: for a nonnegative integrable function `u` and
`t ≥ 0`, `t * (μ {x | t < u x}).toReal ≤ ∫ x, u x ∂μ`. -/
theorem mul_toReal_measure_lt_le_integral {μ : Measure α} {u : α → ℝ}
    (hu : Integrable u μ) (hu_nn : 0 ≤ᵐ[μ] u) {t : ℝ} (ht : 0 ≤ t) :
    t * (μ {x | t < u x}).toReal ≤ ∫ x, u x ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae hu_nn hu.aestronglyMeasurable]
  have hlint_ne_top : (∫⁻ x, ENNReal.ofReal (u x) ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hu.hasFiniteIntegral.ne (lintegral_mono fun x ↦ ?_)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self (u x))
  have hle := ENNReal.toReal_mono hlint_ne_top
    (ofReal_mul_measure_lt_le_lintegral hu.aestronglyMeasurable.aemeasurable t)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht] at hle
/-- If `V ≤ (μ {x | t < u x}).toReal` for a nonnegative integrable function `u` and `t ≥ 0`, then
`t * V ≤ ∫ x, u x ∂μ`. -/
theorem mul_le_integral_of_le_toReal_measure_lt {μ : Measure α} {u : α → ℝ}
    (hu : Integrable u μ) (hu_nn : 0 ≤ᵐ[μ] u) {t V : ℝ} (ht : 0 ≤ t)
    (hV : V ≤ (μ {x | t < u x}).toReal) :
    t * V ≤ ∫ x, u x ∂μ :=
  (mul_le_mul_of_nonneg_left hV ht).trans (mul_toReal_measure_lt_le_integral hu hu_nn ht)
/-- If `0 < V ≤ (μ {x | t < u x}).toReal` for a nonnegative integrable function `u` and `t ≥ 0`,
then `t ≤ (∫ x, u x ∂μ) / V`. -/
theorem le_div_integral_of_le_toReal_measure_lt {μ : Measure α} {u : α → ℝ}
    (hu : Integrable u μ) (hu_nn : 0 ≤ᵐ[μ] u) {t V : ℝ} (ht : 0 ≤ t) (hV_pos : 0 < V)
    (hV : V ≤ (μ {x | t < u x}).toReal) :
    t ≤ (∫ x, u x ∂μ) / V :=
  (le_div_iff₀ hV_pos).mpr (mul_le_integral_of_le_toReal_measure_lt hu hu_nn ht hV)
/-- **Ball-volume superlevel bound**: if `(unitBallVolume n).toReal * r ^ n` is at most the volume
of `{x | t < u x}` for `t ≥ 0` and an integrable nonnegative function `u`, then
`t * ((unitBallVolume n).toReal * r ^ n) ≤ ∫ x, u x`. -/
theorem mul_unitBallVolume_pow_le_integral_of_le_toReal_volume_lt
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Integrable u volume) (hu_nn : 0 ≤ᵐ[volume] u)
    {t r : ℝ} (ht : 0 ≤ t)
    (hvol : (unitBallVolume n).toReal * r ^ n ≤ (volume {x | t < u x}).toReal) :
    t * ((unitBallVolume n).toReal * r ^ n) ≤ ∫ x, u x :=
  mul_le_integral_of_le_toReal_measure_lt hu hu_nn ht hvol
/-- **Divided ball-volume superlevel bound**: if `(unitBallVolume n).toReal * r ^ n` is at most the
volume of `{x | t < u x}` for `t ≥ 0`, `r > 0`, and an integrable nonnegative function `u`, then
`t ≤ (∫ x, u x) / ((unitBallVolume n).toReal * r ^ n)`. -/
theorem le_div_unitBallVolume_pow_of_le_toReal_volume_lt
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Integrable u volume) (hu_nn : 0 ≤ᵐ[volume] u)
    {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r)
    (hvol : (unitBallVolume n).toReal * r ^ n ≤ (volume {x | t < u x}).toReal) :
    t ≤ (∫ x, u x) / ((unitBallVolume n).toReal * r ^ n) := by
  have hpos : 0 < (unitBallVolume n).toReal * r ^ n :=
    mul_pos (ENNReal.toReal_pos (unitBallVolume_ne_zero n) (unitBallVolume_lt_top n).ne)
      (pow_pos hr n)
  exact le_div_integral_of_le_toReal_measure_lt hu hu_nn ht hpos hvol
/-- **Pinned radial profile `L¹` product bound**: for an integrable nonnegative function
`u : EuclideanSpace ℝ (Fin n) → ℝ` and `r > 0`,
`(unitBallVolume n).toReal * r ^ n * schwarzRadialProfileReal u r ≤ ∫ x, u x`. -/
theorem unitBallVolume_mul_pow_schwarzRadialProfileReal_le_integral [NeZero n]
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Integrable u volume) (hu_nn : 0 ≤ᵐ[volume] u)
    {r : ℝ} (hr : 0 < r) :
    (unitBallVolume n).toReal * r ^ n * schwarzRadialProfileReal u r ≤ ∫ x, u x := by
  have hlp : MemLp u 1 volume := memLp_one_iff_integrable.mpr hu
  have h := rpow_mul_schwarzRadialProfileReal_le_of_memLp hlp one_ne_zero ENNReal.one_ne_top hr
  simp only [ENNReal.toReal_one, Real.rpow_one, ENNReal.rpow_one] at h
  rwa [← integral_eq_lintegral_of_nonneg_ae hu_nn hu.aestronglyMeasurable] at h
/-- **Pinned radial profile `L¹` upper bound (`r > 0`)**: for an integrable nonnegative function
`u : EuclideanSpace ℝ (Fin n) → ℝ` and `r > 0`,
`schwarzRadialProfileReal u r ≤ (∫ x, u x) / ((unitBallVolume n).toReal * r ^ n)`. -/
theorem schwarzRadialProfileReal_le_integral_div [NeZero n]
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Integrable u volume) (hu_nn : 0 ≤ᵐ[volume] u)
    {r : ℝ} (hr : 0 < r) :
    schwarzRadialProfileReal u r ≤ (∫ x, u x) / ((unitBallVolume n).toReal * r ^ n) := by
  have hpos : 0 < (unitBallVolume n).toReal * r ^ n :=
    mul_pos (ENNReal.toReal_pos (unitBallVolume_ne_zero n) (unitBallVolume_lt_top n).ne)
      (pow_pos hr n)
  rw [le_div_iff₀ hpos, mul_comm]
  exact unitBallVolume_mul_pow_schwarzRadialProfileReal_le_integral hu hu_nn hr
/-- **Pointwise `L¹` decay bound for `schwarzRearrangementReal` away from the origin**: for an
integrable nonnegative function `u : EuclideanSpace ℝ (Fin n) → ℝ` and `x ≠ 0`,
`schwarzRearrangementReal u x ≤ (∫ y, u y) / ((unitBallVolume n).toReal * ‖x‖ ^ n)`. -/
theorem schwarzRearrangementReal_le_integral_div_norm_pow [NeZero n]
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Integrable u volume) (hu_nn : 0 ≤ᵐ[volume] u)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    schwarzRearrangementReal u x ≤ (∫ y, u y) / ((unitBallVolume n).toReal * ‖x‖ ^ n) := by
  rw [schwarzRearrangementReal_eq_schwarzRadialProfileReal_norm_of_ne_zero
    hu.aestronglyMeasurable.aemeasurable
    (fun _ ht ↦ measure_lt_lt_top_of_integrable hu ht) hx]
  exact schwarzRadialProfileReal_le_integral_div hu hu_nn (norm_pos_iff.mpr hx)
/-- Every nonempty open interval `Ioo a b ⊆ s` (`a < b`) contains a point satisfying a
`volume.restrict s`-almost-everywhere property. -/
theorem exists_mem_Ioo_of_ae_restrict {s : Set ℝ} {P : ℝ → Prop} {a b : ℝ}
    (hab : a < b) (hsub : Ioo a b ⊆ s) (hae : ∀ᵐ r ∂volume.restrict s, P r) :
    ∃ r ∈ Ioo a b, P r := by
  have hae_Ioo : ∀ᵐ r ∂volume.restrict (Ioo a b), P r :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have : Filter.NeBot (ae (volume.restrict (Ioo a b))) := by
    rw [ae_neBot, ne_eq, Measure.restrict_eq_zero, Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  obtain ⟨r, hrP, hr⟩ := (hae_Ioo.and (ae_restrict_mem measurableSet_Ioo)).exists
  exact ⟨r, hr, hrP⟩
/-- **Pointwise equality at `r₀` from right-continuity and local a.e. equality**: if `v` and `w`
are right-continuous at `r₀` and agree almost everywhere on a set `s` containing `Ioo r₀ b`
(`r₀ < b`), then `v r₀ = w r₀`. -/
theorem eq_of_continuousWithinAt_Ici_of_ae_eq {v w : ℝ → ℝ} {s : Set ℝ} {r₀ b : ℝ}
    (hrb : r₀ < b) (hsub : Ioo r₀ b ⊆ s)
    (hv : ContinuousWithinAt v (Ici r₀) r₀) (hw : ContinuousWithinAt w (Ici r₀) r₀)
    (hae : v =ᵐ[volume.restrict s] w) :
    v r₀ = w r₀ := by
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousWithinAt_iff.mp hv (ε / 2) hε2
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousWithinAt_iff.mp hw (ε / 2) hε2
  set δ := min (min δ₁ δ₂) (b - r₀)
  have hδ_pos : 0 < δ := lt_min (lt_min hδ₁_pos hδ₂_pos) (sub_pos.mpr hrb)
  have hIoo_sub : Ioo r₀ (r₀ + δ) ⊆ s := by
    refine Subset.trans (Ioo_subset_Ioo_right ?_) hsub
    linarith [min_le_right (min δ₁ δ₂) (b - r₀)]
  obtain ⟨r, hr_mem, hvw⟩ :=
    exists_mem_Ioo_of_ae_restrict (lt_add_of_pos_right r₀ hδ_pos) hIoo_sub hae
  have hr_Ici : r ∈ Ici r₀ := hr_mem.1.le
  have hdist_r : dist r r₀ < min δ₁ δ₂ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hr_mem.1)]
    exact (sub_lt_iff_lt_add'.mpr hr_mem.2).trans_le (min_le_left _ _)
  have hv_lt : dist (v r) (v r₀) < ε / 2 :=
    hδ₁ hr_Ici (hdist_r.trans_le (min_le_left δ₁ δ₂))
  have hw_lt : dist (w r) (w r₀) < ε / 2 :=
    hδ₂ hr_Ici (hdist_r.trans_le (min_le_right δ₁ δ₂))
  calc
    dist (v r₀) (w r₀) ≤ dist (v r₀) (v r) + dist (w r) (w r₀) := by
      rw [← hvw]; exact dist_triangle (v r₀) (v r) (w r₀)
    _ = dist (v r) (v r₀) + dist (w r) (w r₀) := by rw [dist_comm (v r₀) (v r)]
    _ ≤ ε := by linarith
/-- **Pointwise transport on `(0, ∞)` for right-continuous functions**: if `v` and `w` are
right-continuous at every `r > 0` and agree `volume`-almost everywhere on `(0, ∞)`, then
`v r = w r` for all `r > 0`. -/
theorem eqOn_Ioi_of_continuousWithinAt_Ici_of_ae_eq {v w : ℝ → ℝ}
    (hv : ∀ r > 0, ContinuousWithinAt v (Ici r) r)
    (hw : ∀ r > 0, ContinuousWithinAt w (Ici r) r)
    (hae : v =ᵐ[volume.restrict (Ioi 0)] w) :
    ∀ r > 0, v r = w r := by
  intro r hr
  exact eq_of_continuousWithinAt_Ici_of_ae_eq (lt_add_one r)
    (fun _ hs ↦ hr.trans hs.1) (hv r hr) (hw r hr) hae
/-- **Pointwise transport on `(0, ∞)` from right-continuity and continuity**: if `v` is
right-continuous at every `r > 0`, `w` is continuous on `(0, ∞)`, and
`v =ᵐ[volume.restrict (Ioi 0)] w`, then `v r = w r` for all `r > 0`. -/
theorem eqOn_Ioi_of_continuousWithinAt_Ici_of_continuousOn_of_ae_eq {v w : ℝ → ℝ}
    (hv : ∀ r > 0, ContinuousWithinAt v (Ici r) r)
    (hw : ContinuousOn w (Ioi 0))
    (hae : v =ᵐ[volume.restrict (Ioi 0)] w) :
    ∀ r > 0, v r = w r :=
  eqOn_Ioi_of_continuousWithinAt_Ici_of_ae_eq hv
    (fun _ hr ↦ (hw.continuousAt (isOpen_Ioi.mem_nhds hr)).continuousWithinAt) hae
/-- **Antitone pointwise transport on `(0, ∞)` without assuming continuity of `v`**: if `v : ℝ → ℝ`
is antitone on `(0, ∞)`, `w : ℝ → ℝ` is continuous on `(0, ∞)`, and `v = w` almost everywhere on
`(0, ∞)`, then `v r = w r` for every `r > 0`. -/
theorem eqOn_Ioi_of_antitoneOn_of_continuousOn_of_ae_eq {v w : ℝ → ℝ}
    (hv : AntitoneOn v (Ioi 0))
    (hw : ContinuousOn w (Ioi 0))
    (hae : v =ᵐ[volume.restrict (Ioi 0)] w) :
    ∀ r > 0, v r = w r := by
  intro r hr
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  have hw_cont : ContinuousAt w r := hw.continuousAt (isOpen_Ioi.mem_nhds hr)
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp hw_cont ε hε
  set δ := min δ₁ (r / 2)
  have hδ_pos : 0 < δ := lt_min hδ₁_pos (half_pos hr)
  have hδ_le₁ : δ ≤ δ₁ := min_le_left δ₁ (r / 2)
  have hδ_le₂ : δ ≤ r / 2 := min_le_right δ₁ (r / 2)
  have hsub₁ : Ioo (r - δ) r ⊆ Ioi 0 := fun s hs ↦ by
    simp only [mem_Ioi]; linarith [hs.1]
  have hsub₂ : Ioo r (r + δ) ⊆ Ioi 0 := fun s hs ↦ hr.trans hs.1
  obtain ⟨s₁, hs₁, hvw₁⟩ := exists_mem_Ioo_of_ae_restrict (sub_lt_self r hδ_pos) hsub₁ hae
  obtain ⟨s₂, hs₂, hvw₂⟩ := exists_mem_Ioo_of_ae_restrict (lt_add_of_pos_right r hδ_pos) hsub₂ hae
  have hle₁ : v r ≤ w s₁ := hvw₁ ▸ hv (hsub₁ hs₁) hr hs₁.2.le
  have hle₂ : w s₂ ≤ v r := hvw₂ ▸ hv hr (hsub₂ hs₂) hs₂.1.le
  have hd₁ : dist (w s₁) (w r) < ε := by
    refine hδ₁ ?_; rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs₁.2)]; linarith [hs₁.1]
  have hd₂ : dist (w s₂) (w r) < ε := by
    refine hδ₁ ?_; rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hs₂.1)]; linarith [hs₂.2]
  rw [Real.dist_eq, abs_lt] at hd₁ hd₂
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith, by linarith⟩
/-- **Pointwise transport on `[a, b)` from right-continuity and continuity on `[a, b]`**: if `v`
is right-continuous on `[a, b)`, `w` is continuous on `[a, b]`, and `v = w` almost everywhere on
`Ioo a b`, then `v r = w r` for all `r ∈ Ico a b`. -/
theorem eqOn_Ico_of_continuousWithinAt_Ici_of_continuousOn_of_ae_eq {v w : ℝ → ℝ} {a b : ℝ}
    (hv : ∀ r ∈ Ico a b, ContinuousWithinAt v (Ici r) r)
    (hw : ContinuousOn w (Icc a b))
    (hae : v =ᵐ[volume.restrict (Ioo a b)] w) :
    ∀ r ∈ Ico a b, v r = w r := by
  intro r hr
  have hw_rc : ContinuousWithinAt w (Ici r) r := by
    have hnhds : Icc a b ∈ 𝓝[≥] r := Icc_mem_nhdsGE_of_mem hr
    exact (hw r (Ico_subset_Icc_self hr)).mono_of_mem_nhdsWithin hnhds
  exact eq_of_continuousWithinAt_Ici_of_ae_eq hr.2
    (Ioo_subset_Ioo_left hr.1) (hv r hr) hw_rc hae

/-! ### Section 2: Radial and tangential gradient decomposition and annulus AC bounds -/

section RadialTangentialDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Unit radial direction `‖x‖⁻¹ • x` at `x : E` (equal to `0` at the origin). -/
@[expose]
def radialUnitDir (x : E) : E :=
  ‖x‖⁻¹ • x
/-- Scalar radial component `⟪g, radialUnitDir x⟫` of a vector `g : E` at `x : E`. -/
@[expose]
def radialComponent (x g : E) : ℝ :=
  ⟪g, radialUnitDir x⟫
/-- Orthogonal projection `radialComponent x g • radialUnitDir x` of `g : E` onto the radial
direction at `x : E`. -/
@[expose]
def radialProjection (x g : E) : E :=
  radialComponent x g • radialUnitDir x
/-- Orthogonal projection `g - radialProjection x g` of `g : E` onto the hyperplane tangent to the
sphere through `x : E`. -/
@[expose]
def tangentialProjection (x g : E) : E :=
  g - radialProjection x g
/-- Unfolding lemma for `radialUnitDir`. -/
theorem radialUnitDir_def (x : E) : radialUnitDir x = ‖x‖⁻¹ • x := rfl
/-- Unfolding lemma for `radialComponent`. -/
theorem radialComponent_def (x g : E) : radialComponent x g = ⟪g, radialUnitDir x⟫ := rfl
/-- Unfolding lemma for `radialProjection`. -/
theorem radialProjection_def (x g : E) :
    radialProjection x g = radialComponent x g • radialUnitDir x := rfl
/-- Unfolding lemma for `tangentialProjection`. -/
theorem tangentialProjection_def (x g : E) :
    tangentialProjection x g = g - radialProjection x g := rfl
/-- At the origin, `radialUnitDir 0 = 0`. -/
@[simp]
theorem radialUnitDir_zero : radialUnitDir (0 : E) = 0 := by
  simp [radialUnitDir]
/-- For `x ≠ 0`, `radialUnitDir x` has unit norm. -/
@[simp]
theorem norm_radialUnitDir {x : E} (hx : x ≠ 0) : ‖radialUnitDir x‖ = 1 := by
  rw [radialUnitDir, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
/-- For all `x : E`, `‖radialUnitDir x‖ ≤ 1`. -/
theorem norm_radialUnitDir_le (x : E) : ‖radialUnitDir x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (norm_radialUnitDir hx).le
/-- For `x ≠ 0`, `⟪radialUnitDir x, radialUnitDir x⟫ = 1`. -/
theorem inner_radialUnitDir_self {x : E} (hx : x ≠ 0) :
    ⟪radialUnitDir x, radialUnitDir x⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_radialUnitDir hx, one_pow]
/-- Positive rescaling preserves `radialUnitDir`. -/
theorem radialUnitDir_smul_pos {x : E} {c : ℝ} (hc : 0 < c) :
    radialUnitDir (c • x) = radialUnitDir x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [radialUnitDir, radialUnitDir, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      mul_inv, smul_smul, mul_right_comm, inv_mul_cancel₀ hc.ne', one_mul]
/-- Every vector `x : E` equals `‖x‖ • radialUnitDir x`. -/
theorem norm_smul_radialUnitDir (x : E) : ‖x‖ • radialUnitDir x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [radialUnitDir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
/-- **Radial-tangential decomposition**: `radialProjection x g + tangentialProjection x g = g`. -/
@[simp]
theorem radialProjection_add_tangentialProjection (x g : E) :
    radialProjection x g + tangentialProjection x g = g :=
  add_sub_cancel _ _
/-- Commuted form of the radial-tangential decomposition:
`tangentialProjection x g + radialProjection x g = g`. -/
@[simp]
theorem tangentialProjection_add_radialProjection (x g : E) :
    tangentialProjection x g + radialProjection x g = g :=
  sub_add_cancel _ _
/-- For `x ≠ 0`, the inner product of `radialProjection x g` with `radialUnitDir x` is
`radialComponent x g`. -/
@[simp]
theorem inner_radialProjection_radialUnitDir {x : E} (hx : x ≠ 0) (g : E) :
    ⟪radialProjection x g, radialUnitDir x⟫ = radialComponent x g := by
  rw [radialProjection, inner_smul_left, RCLike.conj_to_real, inner_radialUnitDir_self hx, mul_one]
/-- **Orthogonality of `tangentialProjection` to the radial direction**: for `x ≠ 0`,
`⟪tangentialProjection x g, radialUnitDir x⟫ = 0`. -/
@[simp]
theorem inner_tangentialProjection_radialUnitDir {x : E} (hx : x ≠ 0) (g : E) :
    ⟪tangentialProjection x g, radialUnitDir x⟫ = 0 := by
  rw [tangentialProjection, inner_sub_left, inner_radialProjection_radialUnitDir hx,
    radialComponent, sub_self]
/-- **Orthogonality of radial and tangential projections**: for `x ≠ 0`,
`⟪radialProjection x g, tangentialProjection x g⟫ = 0`. -/
@[simp]
theorem inner_radialProjection_tangentialProjection {x : E} (hx : x ≠ 0) (g : E) :
    ⟪radialProjection x g, tangentialProjection x g⟫ = 0 := by
  rw [radialProjection, inner_smul_left, RCLike.conj_to_real, real_inner_comm,
    inner_tangentialProjection_radialUnitDir hx, mul_zero]
/-- For `x ≠ 0`, `‖radialProjection x g‖ = |radialComponent x g|`. -/
@[simp]
theorem norm_radialProjection {x : E} (hx : x ≠ 0) (g : E) :
    ‖radialProjection x g‖ = |radialComponent x g| := by
  rw [radialProjection, norm_smul, Real.norm_eq_abs, norm_radialUnitDir hx, mul_one]
/-- Cauchy–Schwarz bound `|radialComponent x g| ≤ ‖g‖`. -/
theorem abs_radialComponent_le_norm (x g : E) : |radialComponent x g| ≤ ‖g‖ := by
  calc
    |radialComponent x g| ≤ ‖g‖ * ‖radialUnitDir x‖ := abs_real_inner_le_norm g (radialUnitDir x)
    _ ≤ ‖g‖ * 1 := mul_le_mul_of_nonneg_left (norm_radialUnitDir_le x) (norm_nonneg g)
    _ = ‖g‖ := mul_one ‖g‖
/-- Contraction bound `‖radialProjection x g‖ ≤ ‖g‖`. -/
theorem norm_radialProjection_le (x g : E) : ‖radialProjection x g‖ ≤ ‖g‖ := by
  by_cases hx : x = 0
  · simp [radialProjection, radialComponent, hx]
  · rw [norm_radialProjection hx]
    exact abs_radialComponent_le_norm x g
/-- **Pythagorean decomposition into radial and tangential components**: for `x ≠ 0`,
`‖g‖ ^ 2 = radialComponent x g ^ 2 + ‖tangentialProjection x g‖ ^ 2`. -/
theorem norm_sq_eq_radialComponent_sq_add_norm_tangentialProjection_sq {x : E} (hx : x ≠ 0)
    (g : E) :
    ‖g‖ ^ 2 = radialComponent x g ^ 2 + ‖tangentialProjection x g‖ ^ 2 := by
  conv_lhs => rw [← radialProjection_add_tangentialProjection x g]
  have horth := inner_radialProjection_tangentialProjection hx g
  have hpyth := norm_add_sq_real (radialProjection x g) (tangentialProjection x g)
  rw [horth, mul_zero, add_zero, norm_radialProjection hx, sq_abs] at hpyth
  exact hpyth
/-- Contraction bound `‖tangentialProjection x g‖ ≤ ‖g‖` for `x ≠ 0`. -/
theorem norm_tangentialProjection_le_norm {x : E} (hx : x ≠ 0) (g : E) :
    ‖tangentialProjection x g‖ ≤ ‖g‖ := by
  have hsq : ‖tangentialProjection x g‖ ^ 2 ≤ ‖g‖ ^ 2 := by
    rw [norm_sq_eq_radialComponent_sq_add_norm_tangentialProjection_sq hx g]
    linarith [sq_nonneg (radialComponent x g)]
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg g) (by linarith)
/-- For `x ≠ 0`, `tangentialProjection x g = 0` if and only if `g` is purely radial at `x`. -/
theorem tangentialProjection_eq_zero_iff {x : E} (_hx : x ≠ 0) (g : E) :
    tangentialProjection x g = 0 ↔ g = radialComponent x g • radialUnitDir x := by
  rw [tangentialProjection, sub_eq_zero, radialProjection]
/-- For `x ≠ 0`, the radial component of `c • radialUnitDir x` is `c`. -/
@[simp]
theorem radialComponent_smul_radialUnitDir {x : E} (hx : x ≠ 0) (c : ℝ) :
    radialComponent x (c • radialUnitDir x) = c := by
  rw [radialComponent, inner_smul_left, RCLike.conj_to_real, inner_radialUnitDir_self hx, mul_one]
/-- For `x ≠ 0`, `radialProjection x (c • radialUnitDir x) = c • radialUnitDir x`. -/
@[simp]
theorem radialProjection_smul_radialUnitDir {x : E} (hx : x ≠ 0) (c : ℝ) :
    radialProjection x (c • radialUnitDir x) = c • radialUnitDir x := by
  rw [radialProjection, radialComponent_smul_radialUnitDir hx]
/-- **Vanishing tangential projection for purely radial vectors**: for `x ≠ 0`,
`tangentialProjection x (c • radialUnitDir x) = 0`. -/
@[simp]
theorem tangentialProjection_smul_radialUnitDir {x : E} (hx : x ≠ 0) (c : ℝ) :
    tangentialProjection x (c • radialUnitDir x) = 0 := by
  rw [tangentialProjection, radialProjection_smul_radialUnitDir hx, sub_self]
/-- For `x ≠ 0`, `‖c • radialUnitDir x‖ = |c|`. -/
@[simp]
theorem norm_smul_radialUnitDir_eq {x : E} (hx : x ≠ 0) (c : ℝ) :
    ‖c • radialUnitDir x‖ = |c| := by
  rw [norm_smul, Real.norm_eq_abs, norm_radialUnitDir hx, mul_one]

section CompleteSpace

variable [CompleteSpace E]

/-- For a radial function `y ↦ v ‖y‖` differentiable at `‖x‖` (`x ≠ 0`), its gradient is
`deriv v ‖x‖ • radialUnitDir x`. -/
theorem gradient_comp_norm_eq_deriv_smul_radialUnitDir {v : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ v ‖x‖) :
    ∇ (fun y : E ↦ v ‖y‖) x = deriv v ‖x‖ • radialUnitDir x := by
  rw [gradient_comp_norm hx hv, radialUnitDir]
/-- For a radial function `y ↦ v ‖y‖` differentiable at `‖x‖` (`x ≠ 0`), the radial component of
its gradient at `x` is `deriv v ‖x‖`. -/
theorem radialComponent_gradient_comp_norm {v : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ v ‖x‖) :
    radialComponent x (∇ (fun y : E ↦ v ‖y‖) x) = deriv v ‖x‖ := by
  rw [gradient_comp_norm_eq_deriv_smul_radialUnitDir hx hv, radialComponent_smul_radialUnitDir hx]
/-- **Vanishing tangential gradient for radial functions**: for `y ↦ v ‖y‖` differentiable at
`‖x‖` (`x ≠ 0`), `tangentialProjection x (∇ (fun y : E ↦ v ‖y‖) x) = 0`. -/
theorem tangentialProjection_gradient_comp_norm {v : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ v ‖x‖) :
    tangentialProjection x (∇ (fun y : E ↦ v ‖y‖) x) = 0 := by
  rw [gradient_comp_norm_eq_deriv_smul_radialUnitDir hx hv,
    tangentialProjection_smul_radialUnitDir hx]

end CompleteSpace

end RadialTangentialDecomposition

/-- Almost everywhere on `EuclideanSpace ℝ (Fin n)`, the gradient of an antitone radial function
`x ↦ v ‖x‖` has radial component `deriv v ‖x‖` and zero tangential component. -/
theorem ae_radialComponent_and_tangentialProjection_gradient_comp_norm [NeZero n]
    {v : ℝ → ℝ} (hv : Antitone v) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      radialComponent x (∇ (fun y ↦ v ‖y‖) x) = deriv v ‖x‖ ∧
        tangentialProjection x (∇ (fun y ↦ v ‖y‖) x) = 0 := by
  filter_upwards [ae_gradient_comp_norm volume (ae_differentiableAt_Ioi_of_antitone hv),
    ae_ne_zero (E := EuclideanSpace ℝ (Fin n)) volume] with x hgrad hx
  rw [hgrad, ← radialUnitDir_def]
  exact ⟨radialComponent_smul_radialUnitDir hx (deriv v ‖x‖),
    tangentialProjection_smul_radialUnitDir hx (deriv v ‖x‖)⟩
/-- On any compact interval `Icc a b` with `0 ≤ a`, `a ^ (n - 1) ≤ r ^ (n - 1)`. -/
theorem pow_pred_le_on_Icc {a b r : ℝ} (ha : 0 ≤ a) (hr : r ∈ Icc a b) (n : ℕ) :
    a ^ (n - 1) ≤ r ^ (n - 1) :=
  pow_le_pow_left₀ ha hr.1 (n - 1)
/-- **Lower Lebesgue weighted derivative bound on `[a, b]`**: for `0 ≤ a`,
`ENNReal.ofReal (a ^ (n - 1)) * ∫⁻ r in Icc a b, ‖d r‖ₑ ≤
  ∫⁻ r in Icc a b, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1))`. -/
theorem mul_setLIntegral_Icc_enorm_le (d : ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ENNReal.ofReal (a ^ (n - 1)) * ∫⁻ r in Icc a b, ‖d r‖ₑ ∂volume ≤
      ∫⁻ r in Icc a b, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1)) ∂volume := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun r hr ↦ ?_
  rw [mul_comm]
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (pow_pred_le_on_Icc ha hr n)) ‖d r‖ₑ
/-- **Spherical-factor lower Lebesgue bound on `[a, b]`**: for `0 ≤ a`,
`(n : ℝ≥0∞) * unitBallVolume n * ENNReal.ofReal (a ^ (n - 1)) * ∫⁻ r in Icc a b, ‖d r‖ₑ ≤
  (n : ℝ≥0∞) * unitBallVolume n * ∫⁻ r in Icc a b, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1))`. -/
theorem unitBallVolume_mul_pow_setLIntegral_Icc_enorm_le (d : ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (n : ℕ) :
    (n : ℝ≥0∞) * unitBallVolume n * ENNReal.ofReal (a ^ (n - 1)) *
        ∫⁻ r in Icc a b, ‖d r‖ₑ ∂volume ≤
      (n : ℝ≥0∞) * unitBallVolume n *
        ∫⁻ r in Icc a b, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1)) ∂volume := by
  rw [mul_assoc ((n : ℝ≥0∞) * unitBallVolume n)]
  exact mul_le_mul_right (mul_setLIntegral_Icc_enorm_le d ha n) _
/-- **Bochner weighted derivative bound on `[a, b]`**: for `0 ≤ a` and `0 ≤ c`,
`c * a ^ (n - 1) * ∫ r in Icc a b, |d r| ≤ c * ∫ r in Icc a b, |d r| * r ^ (n - 1)`. -/
theorem mul_setIntegral_Icc_abs_le {d : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (hd : IntegrableOn (fun r ↦ |d r| * r ^ (n - 1)) (Icc a b) volume)
    (hd0 : IntegrableOn (fun r ↦ |d r|) (Icc a b) volume) {c : ℝ} (hc : 0 ≤ c) :
    c * a ^ (n - 1) * ∫ r in Icc a b, |d r| ≤
      c * ∫ r in Icc a b, |d r| * r ^ (n - 1) := by
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on (hd0.const_mul (a ^ (n - 1))) hd measurableSet_Icc fun r hr ↦ ?_
  rw [mul_comm (a ^ (n - 1)) |d r|]
  exact mul_le_mul_of_nonneg_left (pow_pred_le_on_Icc ha hr n) (abs_nonneg (d r))
/-- **Annulus-to-compact-interval Bochner bound**: for `0 ≤ a`,
`(n : ℝ) * (unitBallVolume n).toReal * a ^ (n - 1) * ∫ r in Icc a b, |d r| ≤
  (n : ℝ) * (unitBallVolume n).toReal * ∫ r in Icc a b, |d r| * r ^ (n - 1)`. -/
theorem unitBallVolume_mul_pow_setIntegral_Icc_abs_le {d : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (hd : IntegrableOn (fun r ↦ |d r| * r ^ (n - 1)) (Icc a b) volume)
    (hd0 : IntegrableOn (fun r ↦ |d r|) (Icc a b) volume) :
    (n : ℝ) * (unitBallVolume n).toReal * a ^ (n - 1) * ∫ r in Icc a b, |d r| ≤
      (n : ℝ) * (unitBallVolume n).toReal * ∫ r in Icc a b, |d r| * r ^ (n - 1) :=
  mul_setIntegral_Icc_abs_le ha n hd hd0
    (mul_nonneg (Nat.cast_nonneg n) ENNReal.toReal_nonneg)
/-- **Upper bound on unweighted `L¹` norm over `[a, b] ⊆ (0, ∞)`** in terms of the global
`r ^ (n - 1)`-weighted polar integral on `(0, ∞)`. -/
theorem setLIntegral_Icc_enorm_le_div_of_pos (d : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (n : ℕ) :
    ∫⁻ r in Icc a b, ‖d r‖ₑ ∂volume ≤
      (∫⁻ r in Ioi 0, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1)) ∂volume) /
        ENNReal.ofReal (a ^ (n - 1)) := by
  have ha_ne_zero : ENNReal.ofReal (a ^ (n - 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos ha (n - 1))).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl ha_ne_zero) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  refine (mul_setLIntegral_Icc_enorm_le d ha.le n).trans (lintegral_mono_set ?_)
  intro r hr
  exact ha.trans_le hr.1
/-- Finiteness of the `r ^ (n - 1)`-weighted integral on `(0, ∞)` implies finiteness of the
unweighted lower Lebesgue integral on every compact interval `[a, b] ⊆ (0, ∞)`. -/
theorem setLIntegral_Icc_enorm_lt_top_of_weighted_lt_top {d : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (n : ℕ) (hfin : ∫⁻ r in Ioi 0, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1)) ∂volume < ⊤) :
    ∫⁻ r in Icc a b, ‖d r‖ₑ ∂volume < ⊤ := by
  refine (setLIntegral_Icc_enorm_le_div_of_pos d ha n).trans_lt ?_
  exact ENNReal.div_lt_top hfin.ne (ENNReal.ofReal_pos.mpr (pow_pos ha (n - 1))).ne'
/-- **Compact-subinterval integrability (`IntegrableOn d (Icc a b)`) from weighted polar
finiteness**: if `d` is a.e. strongly measurable on `(0, ∞)` and
`∫⁻ r in Ioi 0, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1)) < ⊤`, then `d` is integrable on `[a, b]` for
every `0 < a ≤ b`. -/
theorem integrableOn_Icc_of_weighted_lintegral_lt_top {d : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (n : ℕ) (hd_meas : AEStronglyMeasurable d (volume.restrict (Ioi 0)))
    (hfin : ∫⁻ r in Ioi 0, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1)) ∂volume < ⊤) :
    IntegrableOn d (Icc a b) volume := by
  have hsub : Icc a b ⊆ Ioi 0 := fun r hr ↦ ha.trans_le hr.1
  exact ⟨hd_meas.mono_set hsub, setLIntegral_Icc_enorm_lt_top_of_weighted_lt_top ha n hfin⟩
/-- **Compact-subinterval integrability from spherical polar `L¹` finiteness**: when
`(n : ℝ≥0∞) * unitBallVolume n * ∫⁻ r in Ioi 0, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1)) < ⊤`,
`d` is integrable on every compact interval `[a, b] ⊆ (0, ∞)`. -/
theorem integrableOn_Icc_of_polar_lintegral_lt_top [NeZero n] {d : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hd_meas : AEStronglyMeasurable d (volume.restrict (Ioi 0)))
    (hfin : (n : ℝ≥0∞) * unitBallVolume n *
      ∫⁻ r in Ioi 0, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1)) ∂volume < ⊤) :
    IntegrableOn d (Icc a b) volume := by
  have hc_pos : 0 < (n : ℝ≥0∞) * unitBallVolume n :=
    ENNReal.mul_pos (Nat.cast_ne_zero.mpr (NeZero.ne n)) (unitBallVolume_ne_zero n)
  have hw_lt_top : ∫⁻ r in Ioi 0, ‖d r‖ₑ * ENNReal.ofReal (r ^ (n - 1)) ∂volume < ⊤ := by
    by_contra! htop
    rw [top_le_iff.mp htop, ENNReal.mul_top hc_pos.ne'] at hfin
    exact lt_irrefl ⊤ hfin
  exact integrableOn_Icc_of_weighted_lintegral_lt_top ha n hd_meas hw_lt_top

/-! ### Section 3: Origin decay `r ^ (n - 1) * v r → 0` as `r → 0⁺` for `n ≥ 2` -/

/-- For a nonnegative integrable density `d` on `Icc r R` (`0 ≤ r ≤ R`),
`r ^ m * ∫ s in Icc r R, d s ≤ ∫ s in Icc r R, d s * s ^ m`. -/
theorem mul_setIntegral_Icc_le_setIntegral_mul_pow {d : ℝ → ℝ} {r R : ℝ} (hr : 0 ≤ r)
    (hd_nn : ∀ s ∈ Icc r R, 0 ≤ d s) (hd : IntegrableOn d (Icc r R) volume)
    (hd_pow : IntegrableOn (fun s ↦ d s * s ^ m) (Icc r R) volume) :
    r ^ m * ∫ s in Icc r R, d s ≤ ∫ s in Icc r R, d s * s ^ m := by
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on (hd.const_mul (r ^ m)) hd_pow measurableSet_Icc fun s hs ↦ ?_
  rw [mul_comm (r ^ m) (d s)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hs.1 m) (hd_nn s hs)
/-- For a nonnegative integrable density `d` on `Icc r R` (`0 ≤ r ≤ R`), when `d` is integrable on
`Icc r R`, `s ↦ d s * s ^ m` is automatically integrable on `Icc r R`. -/
theorem integrableOn_mul_pow_Icc {d : ℝ → ℝ} {r R : ℝ}
    (hd : IntegrableOn d (Icc r R) volume) (m : ℕ) :
    IntegrableOn (fun s ↦ d s * s ^ m) (Icc r R) volume :=
  hd.mul_continuousOn (continuous_pow m).continuousOn isCompact_Icc
/-- For `0 < r ≤ R` and a nonnegative density `d` on `Ioc 0 R` with `d` integrable on `Icc r R`
and `s ↦ d s * s ^ m` integrable on `Ioc 0 R`,
`r ^ m * ∫ s in Icc r R, d s ≤ ∫ s in Ioc 0 R, d s * s ^ m`. -/
theorem mul_setIntegral_Icc_le_setIntegral_Ioc_mul_pow {d : ℝ → ℝ} {r R : ℝ}
    (hr : 0 < r) (_hrR : r ≤ R) (hd_nn : ∀ s ∈ Ioc 0 R, 0 ≤ d s)
    (hd : IntegrableOn d (Icc r R) volume)
    (hd_pow : IntegrableOn (fun s ↦ d s * s ^ m) (Ioc 0 R) volume) :
    r ^ m * ∫ s in Icc r R, d s ≤ ∫ s in Ioc 0 R, d s * s ^ m := by
  have hd_nn_Icc : ∀ s ∈ Icc r R, 0 ≤ d s := fun s hs ↦ hd_nn s ⟨hr.trans_le hs.1, hs.2⟩
  refine (mul_setIntegral_Icc_le_setIntegral_mul_pow hr.le hd_nn_Icc hd
    (integrableOn_mul_pow_Icc hd m)).trans ?_
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine setIntegral_mono_set hd_pow ?_ (Eventually.of_forall (Ioc_subset_Ioc_left hr.le))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact mul_nonneg (hd_nn s hs) (pow_nonneg hs.1.le m)
/-- **Two-radius bound on `Icc r R`**: if `v r ≤ v R + ∫ s in Icc r R, d s` for `0 ≤ r ≤ R` and a
nonnegative integrable density `d` on `Icc r R`, then
`r ^ m * v r ≤ r ^ m * v R + ∫ s in Icc r R, d s * s ^ m`. -/
theorem pow_mul_le_pow_mul_add_setIntegral_Icc {v d : ℝ → ℝ} {r R : ℝ} (hr : 0 ≤ r)
    (hd_nn : ∀ s ∈ Icc r R, 0 ≤ d s) (hd : IntegrableOn d (Icc r R) volume)
    (hv : v r ≤ v R + ∫ s in Icc r R, d s) (m : ℕ) :
    r ^ m * v r ≤ r ^ m * v R + ∫ s in Icc r R, d s * s ^ m := by
  have h1 : r ^ m * v r ≤ r ^ m * v R + r ^ m * ∫ s in Icc r R, d s := by
    calc
      r ^ m * v r ≤ r ^ m * (v R + ∫ s in Icc r R, d s) :=
        mul_le_mul_of_nonneg_left hv (pow_nonneg hr m)
      _ = r ^ m * v R + r ^ m * ∫ s in Icc r R, d s := mul_add _ _ _
  have h2 := mul_setIntegral_Icc_le_setIntegral_mul_pow hr hd_nn hd
    (integrableOn_mul_pow_Icc hd m)
  linarith
/-- **Two-radius bound on `Ioc 0 R`**: if `v r ≤ v R + ∫ s in Icc r R, d s` for `0 < r ≤ R`,
`d ≥ 0` on `Ioc 0 R`, `d` is integrable on `Icc r R`, and `s ↦ d s * s ^ m` is integrable on
`Ioc 0 R`, then `r ^ m * v r ≤ r ^ m * v R + ∫ s in Ioc 0 R, d s * s ^ m`. -/
theorem pow_mul_le_pow_mul_add_setIntegral_Ioc {v d : ℝ → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hd_nn : ∀ s ∈ Ioc 0 R, 0 ≤ d s)
    (hd : IntegrableOn d (Icc r R) volume)
    (hd_pow : IntegrableOn (fun s ↦ d s * s ^ m) (Ioc 0 R) volume)
    (hv : v r ≤ v R + ∫ s in Icc r R, d s) :
    r ^ m * v r ≤ r ^ m * v R + ∫ s in Ioc 0 R, d s * s ^ m := by
  have h1 : r ^ m * v r ≤ r ^ m * v R + r ^ m * ∫ s in Icc r R, d s := by
    calc
      r ^ m * v r ≤ r ^ m * (v R + ∫ s in Icc r R, d s) :=
        mul_le_mul_of_nonneg_left hv (pow_nonneg hr.le m)
      _ = r ^ m * v R + r ^ m * ∫ s in Icc r R, d s := mul_add _ _ _
  have h2 := mul_setIntegral_Icc_le_setIntegral_Ioc_mul_pow hr hrR hd_nn hd hd_pow
  linarith
/-- Dimension-indexed (`m = n - 1`) two-radius bound:
`r ^ (n - 1) * v r ≤ r ^ (n - 1) * v R + ∫ s in Ioc 0 R, d s * s ^ (n - 1)`. -/
theorem pow_pred_mul_le_pow_pred_mul_add_setIntegral_Ioc {v d : ℝ → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hd_nn : ∀ s ∈ Ioc 0 R, 0 ≤ d s)
    (hd : IntegrableOn d (Icc r R) volume)
    (hd_pow : IntegrableOn (fun s ↦ d s * s ^ (n - 1)) (Ioc 0 R) volume)
    (hv : v r ≤ v R + ∫ s in Icc r R, d s) :
    r ^ (n - 1) * v r ≤ r ^ (n - 1) * v R + ∫ s in Ioc 0 R, d s * s ^ (n - 1) :=
  pow_mul_le_pow_mul_add_setIntegral_Ioc hr hrR hd_nn hd hd_pow hv
/-- **Dominated convergence of set integrals on `Ioc 0 R` as `R → 0⁺`**: if `f` is integrable on
`Ioc 0 R₀` (`R₀ > 0`), then `Tendsto (fun R ↦ ∫ s in Ioc 0 R, f s) (𝓝[>] 0) (𝓝 0)`. -/
theorem tendsto_setIntegral_Ioc_nhdsWithin_zero {f : ℝ → ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hf : IntegrableOn f (Ioc 0 R₀) volume) :
    Tendsto (fun R ↦ ∫ s in Ioc 0 R, f s) (𝓝[>] 0) (𝓝 0) := by
  have htend_res : Tendsto
      (fun R ↦ ∫ s in Ioc 0 R, f s ∂volume.restrict (Ioc 0 R₀)) (𝓝[>] 0) (𝓝 0) := by
    refine Integrable.tendsto_setIntegral_nhds_zero hf ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ≥0∞))) ?_
      (fun _ ↦ zero_le) (fun R ↦ Measure.restrict_apply_le _ (Ioc 0 R))
    have h0 : Tendsto (fun R : ℝ ↦ ENNReal.ofReal R) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa [Function.comp_def, Real.volume_Ioc] using h0
  refine htend_res.congr' ?_
  rw [eventuallyEq_nhdsWithin_iff]
  filter_upwards [gt_mem_nhds hR₀] with R hR_lt _hR_pos
  rw [Measure.restrict_restrict_of_subset (Ioc_subset_Ioc_right hR_lt.le)]
/-- **Origin decay `r ^ m * v r → 0` as `r → 0⁺` (`m ≥ 1`) for radial profiles controlled by a
nonnegative derivative density `d`**: if `v` and `d` are nonnegative on `(0, R₀]` (`R₀ > 0`),
`v r ≤ v R + ∫ s in Icc r R, d s` for `0 < r ≤ R ≤ R₀`, and `s ↦ d s * s ^ m` is integrable on
`Ioc 0 R₀`, then `Tendsto (fun r ↦ r ^ m * v r) (𝓝[>] 0) (𝓝 0)`. -/
theorem tendsto_pow_mul_nhdsWithin_zero_of_le_add_setIntegral {v d : ℝ → ℝ} {R₀ : ℝ}
    (hR₀ : 0 < R₀) {m : ℕ} (hm : 1 ≤ m)
    (hv_nn : ∀ r ∈ Ioc 0 R₀, 0 ≤ v r)
    (hd_nn : ∀ s ∈ Ioc 0 R₀, 0 ≤ d s)
    (hd_int : ∀ r R, 0 < r → r ≤ R → R ≤ R₀ → IntegrableOn d (Icc r R) volume)
    (hv_le : ∀ r R, 0 < r → r ≤ R → R ≤ R₀ → v r ≤ v R + ∫ s in Icc r R, d s)
    (hd_pow : IntegrableOn (fun s ↦ d s * s ^ m) (Ioc 0 R₀) volume) :
    Tendsto (fun r ↦ r ^ m * v r) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have htend_int := tendsto_setIntegral_Ioc_nhdsWithin_zero hR₀ hd_pow
  rw [Metric.tendsto_nhds] at htend_int
  have h_ev := htend_int (ε / 2) hε2
  rw [eventually_nhdsWithin_iff] at h_ev
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp h_ev
  set R₁ := min (R₀ / 2) (δ₁ / 2)
  have hR₁_pos : 0 < R₁ := lt_min (half_pos hR₀) (half_pos hδ₁_pos)
  have hR₁_le_R₀ : R₁ ≤ R₀ := (min_le_left _ _).trans (half_le_self hR₀.le)
  have hR₁_lt_δ₁ : dist R₁ 0 < δ₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hR₁_pos]
    exact (min_le_right _ _).trans_lt (half_lt_self hδ₁_pos)
  have hint_R₁ : |∫ s in Ioc 0 R₁, d s * s ^ m| < ε / 2 := by
    have hlt := hδ₁ hR₁_lt_δ₁ hR₁_pos
    rwa [Real.dist_eq, sub_zero] at hlt
  have hm_ne : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  have hpow_cont : Tendsto (fun r : ℝ ↦ r ^ m * v R₁) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ ↦ r ^ m * v R₁) := by fun_prop
    simpa [zero_pow hm_ne] using hcont.tendsto 0
  rw [Metric.tendsto_nhds] at hpow_cont
  have hpow_ev := hpow_cont (ε / 2) hε2
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hpow_ev, gt_mem_nhds hR₁_pos] with r hr_pow hr_lt_R₁ (hr_pos : 0 < r)
  have hr_le_R₀ : r ≤ R₀ := hr_lt_R₁.le.trans hR₁_le_R₀
  have hr_nonneg : 0 ≤ r ^ m * v r :=
    mul_nonneg (pow_nonneg hr_pos.le m) (hv_nn r ⟨hr_pos, hr_le_R₀⟩)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hr_nonneg]
  have hbound := pow_mul_le_pow_mul_add_setIntegral_Ioc hr_pos hr_lt_R₁.le
    (fun s hs ↦ hd_nn s ⟨hs.1, hs.2.trans hR₁_le_R₀⟩)
    (hd_int r R₁ hr_pos hr_lt_R₁.le hR₁_le_R₀)
    (hd_pow.mono_set (Ioc_subset_Ioc_right hR₁_le_R₀))
    (hv_le r R₁ hr_pos hr_lt_R₁.le hR₁_le_R₀)
  have hr_pow' : r ^ m * v R₁ < ε / 2 :=
    (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hr_pow)
  have hint_R₁' : ∫ s in Ioc 0 R₁, d s * s ^ m < ε / 2 :=
    (le_abs_self _).trans_lt hint_R₁
  linarith
/-- **Origin decay `r ^ (n - 1) * v r → 0` as `r → 0⁺` in dimension `n ≥ 2`** for a radial profile
`v` controlled on `(0, R₀]` by a nonnegative derivative density `d`. -/
theorem tendsto_pow_pred_mul_nhdsWithin_zero_of_le_add_setIntegral {v d : ℝ → ℝ} {R₀ : ℝ}
    (hR₀ : 0 < R₀) (hn : 2 ≤ n)
    (hv_nn : ∀ r ∈ Ioc 0 R₀, 0 ≤ v r)
    (hd_nn : ∀ s ∈ Ioc 0 R₀, 0 ≤ d s)
    (hd_int : ∀ r R, 0 < r → r ≤ R → R ≤ R₀ → IntegrableOn d (Icc r R) volume)
    (hv_le : ∀ r R, 0 < r → r ≤ R → R ≤ R₀ → v r ≤ v R + ∫ s in Icc r R, d s)
    (hd_pow : IntegrableOn (fun s ↦ d s * s ^ (n - 1)) (Ioc 0 R₀) volume) :
    Tendsto (fun r ↦ r ^ (n - 1) * v r) (𝓝[>] 0) (𝓝 0) :=
  tendsto_pow_mul_nhdsWithin_zero_of_le_add_setIntegral hR₀ (Nat.le_sub_one_of_lt hn)
    hv_nn hd_nn hd_int hv_le hd_pow
/-- **Origin decay `r ^ (n - 1) * v r → 0` as `r → 0⁺` (`n ≥ 2`) from global `(0, ∞)` weighted
integrability**: if `v` and `d` are nonnegative on `(0, ∞)`, `s ↦ d s * s ^ (n - 1)` is integrable
on `(0, ∞)`, and `v r ≤ v R + ∫ s in Icc r R, d s` for all `0 < r ≤ R`, then
`Tendsto (fun r ↦ r ^ (n - 1) * v r) (𝓝[>] 0) (𝓝 0)`. -/
theorem tendsto_pow_pred_mul_nhdsWithin_zero_of_integrableOn_Ioi {v d : ℝ → ℝ}
    (hn : 2 ≤ n)
    (hv_nn : ∀ r > 0, 0 ≤ v r)
    (hd_nn : ∀ s > 0, 0 ≤ d s)
    (hd_meas : AEStronglyMeasurable d (volume.restrict (Ioi 0)))
    (hd_pow : IntegrableOn (fun s ↦ d s * s ^ (n - 1)) (Ioi 0) volume)
    (hv_le : ∀ r R, 0 < r → r ≤ R → v r ≤ v R + ∫ s in Icc r R, d s) :
    Tendsto (fun r ↦ r ^ (n - 1) * v r) (𝓝[>] 0) (𝓝 0) := by
  have hfin : ∫⁻ s in Ioi 0, ‖d s‖ₑ * ENNReal.ofReal (s ^ (n - 1)) ∂volume < ⊤ := by
    refine (setLIntegral_mono' measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_).trans_lt
      hd_pow.hasFiniteIntegral
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hd_nn s hs),
      abs_of_nonneg (mul_nonneg (hd_nn s hs) (pow_nonneg hs.le (n - 1))),
      ENNReal.ofReal_mul (hd_nn s hs)]
  exact tendsto_pow_pred_mul_nhdsWithin_zero_of_le_add_setIntegral zero_lt_one hn
    (fun r hr ↦ hv_nn r hr.1) (fun s hs ↦ hd_nn s hs.1)
    (fun r _ hr _ _ ↦ integrableOn_Icc_of_weighted_lintegral_lt_top hr n hd_meas hfin)
    (fun r R hr hrR _ ↦ hv_le r R hr hrR)
    (hd_pow.mono_set Ioc_subset_Ioi_self)

end TauCeti
