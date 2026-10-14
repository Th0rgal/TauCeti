/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import TauCeti.MeasureTheory.Function.SchwarzRadialProfile

/-!
# Power Commutation, Contraction, and Radial Decay of Schwarz Rearrangement

This file develops the functional-analytic and radial-decay properties of the Schwarz symmetric
decreasing rearrangement on `EuclideanSpace ℝ (Fin n)`:
1. **Right-continuity of distribution functions and quantile Galois connection**:
   `measure_lt_eq_iSup_add_inv`, `lt_layerCakeQuantile_iff`, `layerCakeQuantile_le_iff`,
   `superlevel_layerCakeQuantile`, and `ennreal_eq_of_forall_lt_iff`.
2. **Power (`rpow`) commutation**:
   `(f ^ p)* = (f*) ^ p` for `0 < p : ℝ` across `distributionFunction`, `layerCakeQuantile`,
   `schwarzRadialProfile`, `schwarzRearrangement`, `schwarzRadialProfileReal`, and
   `schwarzRearrangementReal`.
3. **Real-valued `L^p` / `L^1` equimeasurability and integral preservation**:
   `eLpNorm_schwarzRearrangementReal_of_memLp`, `eLpNorm_schwarzRearrangementReal_abs`,
   `memLp_schwarzRearrangementReal_abs`, `integrable_schwarzRearrangementReal`, and
   `integral_schwarzRearrangementReal_eq`.
4. **Translation by positive constants, uniform `L^∞` contraction, and Crandall–Tartar `L^1` / `L^p`
   contraction and continuity**:
   `schwarzRearrangement_add_const`, `schwarzRearrangement_tsub_le_iSup_tsub`,
   `abs_schwarzRearrangementReal_sub_le_ae`, `lintegral_tsub_schwarzRearrangement_le`,
   `lintegral_tsub_add_tsub_schwarzRearrangement_le`,
   `integral_abs_sub_schwarzRearrangementReal_le`, and
   `tendsto_eLpNorm_sub_schwarzRearrangementReal`.
5. **Radial profile weighted derivative bounds and origin/infinity decay**:
   For an antitone locally absolutely continuous radial profile `v : ℝ → ℝ` on `(0, ∞)` with
   integrable weighted derivative `|deriv v r| * r ^ m`, we prove
   `r₁ ^ m * (v r₁ - v r₂) ≤ ∫ s in Ioc r₁ r₂, |deriv v s| * s ^ m` and deduce
   `Tendsto (fun r ↦ r ^ (n - 1) * v r) (𝓝[>] 0) (𝓝 0)` for `n ≥ 2`.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

/-! ### Quantile Galois connection and power (`rpow`) commutation -/

/-- Right-continuity of the superlevel measure `t ↦ μ {x | t < f x}` along countable rational-step
approximations `t + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹`. -/
theorem measure_lt_eq_iSup_add_inv (μ : Measure α) (f : α → ℝ≥0∞) (t : ℝ≥0∞) :
    μ {x | t < f x} = ⨆ k : ℕ, μ {x | t + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ < f x} := by
  have hunion : {x | t < f x} = ⋃ k : ℕ, {x | t + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ < f x} := by
    ext x; simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hlt
      have ht : t ≠ ⊤ := ne_top_of_lt hlt
      have hpos : 0 < f x - t := tsub_pos_iff_lt.mpr hlt
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
      refine ⟨k, ?_⟩
      have hle : ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ :=
        ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Nat.le_add_right k 1))
      rw [← add_tsub_cancel_of_le hlt.le]
      exact ENNReal.add_lt_add_left ht (hle.trans_lt hk)
    · rintro ⟨k, hk⟩; exact le_self_add.trans_lt hk
  have hmono : Monotone fun k : ℕ ↦ {x | t + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ < f x} := by
    intro i j hij x (hx : t + ((i + 1 : ℕ) : ℝ≥0∞)⁻¹ < f x)
    refine lt_of_le_of_lt (add_le_add_right ?_ t) hx
    exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Nat.add_le_add_right hij 1))
  rw [hunion, hmono.measure_iUnion]
/-- Strict lower-bound characterization of `layerCakeQuantile`: `s < layerCakeQuantile μ f v` if and
only if the superlevel set `{x | s < f x}` has measure strictly greater than `v`. -/
theorem lt_layerCakeQuantile_iff {μ : Measure α} {f : α → ℝ≥0∞} {v s : ℝ≥0∞} :
    s < layerCakeQuantile μ f v ↔ v < μ {x | s < f x} := by
  rw [layerCakeQuantile_eq_sSup, lt_sSup_iff]
  constructor
  · rintro ⟨t, hvt, hst⟩; exact hvt.trans_le (measure_mono fun x hx ↦ hst.trans hx)
  · intro hv
    rw [measure_lt_eq_iSup_add_inv μ f s, lt_iSup_iff] at hv
    obtain ⟨k, hk⟩ := hv
    refine ⟨s + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹, hk, ?_⟩
    have hne : ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (k + 1))
    have hst : s ≠ ⊤ := by rintro rfl; simp at hk
    exact ENNReal.lt_add_right hst hne
/-- Galois connection between `layerCakeQuantile μ f` and `s ↦ μ {x | s < f x}`:
`layerCakeQuantile μ f v ≤ s ↔ μ {x | s < f x} ≤ v`. -/
theorem layerCakeQuantile_le_iff {μ : Measure α} {f : α → ℝ≥0∞} {v s : ℝ≥0∞} :
    layerCakeQuantile μ f v ≤ s ↔ μ {x | s < f x} ≤ v := by
  rw [← not_lt, lt_layerCakeQuantile_iff, not_lt]
/-- The superlevel set `{v | s < layerCakeQuantile μ f v}` is `Iio (μ {x | s < f x})`. -/
theorem superlevel_layerCakeQuantile (μ : Measure α) (f : α → ℝ≥0∞) (s : ℝ≥0∞) :
    {v : ℝ≥0∞ | s < layerCakeQuantile μ f v} = Iio (μ {x | s < f x}) := by
  ext v; exact lt_layerCakeQuantile_iff
/-- Two `ℝ≥0∞` values are equal if and only if they have the same strict lower bounds. -/
theorem ennreal_eq_of_forall_lt_iff {a b : ℝ≥0∞} (h : ∀ s : ℝ≥0∞, s < a ↔ s < b) :
    a = b := by
  refine le_antisymm ?_ ?_
  · by_contra! hlt; exact ((h b).mp hlt).false
  · by_contra! hlt; exact ((h a).mpr hlt).false
/-- For `0 < p : ℝ`, the distribution function of `f ^ p` at `t` equals the distribution function
of `f` at `t ^ p⁻¹`. -/
theorem distributionFunction_rpow [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (t : ℝ≥0∞) :
    distributionFunction (fun y ↦ f y ^ p) t = distributionFunction f (t ^ p⁻¹) := by
  simp only [distributionFunction_eq_volume]
  congr 1; ext y; simp only [mem_ofPred_eq]
  rw [← ENNReal.rpow_lt_rpow_iff (inv_pos.mpr hp), ENNReal.rpow_rpow_inv hp.ne']
/-- **Power commutation for `layerCakeQuantile`**: for `0 < p : ℝ`,
`layerCakeQuantile μ (fun x ↦ f x ^ p) v = (layerCakeQuantile μ f v) ^ p`. -/
theorem layerCakeQuantile_rpow (μ : Measure α) (f : α → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (v : ℝ≥0∞) :
    layerCakeQuantile μ (fun x ↦ f x ^ p) v = (layerCakeQuantile μ f v) ^ p := by
  refine ennreal_eq_of_forall_lt_iff fun s ↦ ?_
  have h1 : s < layerCakeQuantile μ (fun x ↦ f x ^ p) v ↔ v < μ {x | s < f x ^ p} :=
    lt_layerCakeQuantile_iff
  have h2 : s < (layerCakeQuantile μ f v) ^ p ↔ v < μ {x | s ^ p⁻¹ < f x} := by
    rw [← ENNReal.rpow_lt_rpow_iff (inv_pos.mpr hp), ENNReal.rpow_rpow_inv hp.ne',
      lt_layerCakeQuantile_iff]
  have hset : {x | s < f x ^ p} = {x | s ^ p⁻¹ < f x} := by
    ext x; simp only [mem_ofPred_eq]
    rw [← ENNReal.rpow_lt_rpow_iff (inv_pos.mpr hp), ENNReal.rpow_rpow_inv hp.ne']
  rw [h1, h2, hset]
/-- **Power commutation for `schwarzRadialProfile`**: for `0 < p : ℝ`,
`schwarzRadialProfile (fun y ↦ f y ^ p) r = (schwarzRadialProfile f r) ^ p`. -/
theorem schwarzRadialProfile_rpow [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (r : ℝ) :
    schwarzRadialProfile (fun y ↦ f y ^ p) r = (schwarzRadialProfile f r) ^ p := by
  rw [schwarzRadialProfile_eq_layerCakeQuantile, schwarzRadialProfile_eq_layerCakeQuantile,
    layerCakeQuantile_rpow volume f hp]
/-- **Power commutation for `schwarzRearrangement`**: for `0 < p : ℝ`,
`schwarzRearrangement (fun y ↦ f y ^ p) x = (schwarzRearrangement f x) ^ p`. -/
theorem schwarzRearrangement_rpow [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (x : EuclideanSpace ℝ (Fin n)) :
    schwarzRearrangement (fun y ↦ f y ^ p) x = (schwarzRearrangement f x) ^ p := by
  rw [schwarzRearrangement_apply, schwarzRearrangement_apply, schwarzRadialProfile_rpow f hp]
/-- For `r > 0`, `schwarzRadialProfileReal f r` equals
`(schwarzRadialProfile (ofReal ∘ f) r).toReal` when `f` has finite superlevel volumes. -/
theorem schwarzRadialProfileReal_eq_toReal_of_pos [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) {r : ℝ} (hr : 0 < r) :
    schwarzRadialProfileReal f r =
      (schwarzRadialProfile (fun y ↦ ENNReal.ofReal (f y)) r).toReal := by
  have h := congrArg ENNReal.toReal (ofReal_schwarzRadialProfileReal_of_pos hf hdist hr)
  rwa [ENNReal.toReal_ofReal (schwarzRadialProfileReal_nonneg f r)] at h
/-- If a nonnegative real function `f` has finite superlevel volumes for `t > 0`, then so does
`fun y ↦ f y ^ p` for `0 < p : ℝ`. -/
theorem volume_lt_rpow_lt_top {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_nn : ∀ y, 0 ≤ f y) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    {p : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    volume {y | t < f y ^ p} < ⊤ := by
  have hset : {y | t < f y ^ p} = {y | t ^ (1 / p) < f y} := by
    ext y; simp only [mem_ofPred_eq]
    rw [← Real.rpow_lt_rpow_iff ht.le (Real.rpow_nonneg (hf_nn y) p) (one_div_pos.mpr hp),
      ← Real.rpow_mul (hf_nn y), mul_one_div_cancel hp.ne', Real.rpow_one]
  rw [hset]
  exact hdist (t ^ (1 / p)) (Real.rpow_pos_of_pos ht (1 / p))
/-- **Power commutation for `schwarzRadialProfileReal`**: for a nonnegative a.e. measurable function
`f` with finite superlevel volumes and `0 < p : ℝ`,
`schwarzRadialProfileReal (fun y ↦ f y ^ p) r = (schwarzRadialProfileReal f r) ^ p` for `r > 0`. -/
theorem schwarzRadialProfileReal_rpow [NeZero n] {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f volume) (hf_nn : ∀ y, 0 ≤ f y)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    {p : ℝ} (hp : 0 < p) {r : ℝ} (hr : 0 < r) :
    schwarzRadialProfileReal (fun y ↦ f y ^ p) r = (schwarzRadialProfileReal f r) ^ p := by
  have hfp_meas : AEMeasurable (fun y ↦ f y ^ p) volume := hf.pow_const p
  have hfp_dist : ∀ t : ℝ, 0 < t → volume {y | t < f y ^ p} < ⊤ :=
    fun _ ht ↦ volume_lt_rpow_lt_top hf_nn hdist hp ht
  rw [schwarzRadialProfileReal_eq_toReal_of_pos hfp_meas hfp_dist hr,
    schwarzRadialProfileReal_eq_toReal_of_pos hf hdist hr]
  have hfun : (fun y ↦ ENNReal.ofReal (f y ^ p)) = fun y ↦ ENNReal.ofReal (f y) ^ p := by
    ext y; exact (ENNReal.ofReal_rpow_of_nonneg (hf_nn y) hp.le).symm
  rw [hfun, schwarzRadialProfile_rpow _ hp, ENNReal.toReal_rpow]
/-- **Power commutation for `schwarzRearrangementReal` away from the origin**: for a nonnegative
a.e. measurable function `f` with finite superlevel volumes and `0 < p : ℝ`,
`schwarzRearrangementReal (fun y ↦ f y ^ p) x = (schwarzRearrangementReal f x) ^ p` for `x ≠ 0`. -/
theorem schwarzRearrangementReal_rpow_of_ne_zero [NeZero n] {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f volume) (hf_nn : ∀ y, 0 ≤ f y)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    {p : ℝ} (hp : 0 < p) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    schwarzRearrangementReal (fun y ↦ f y ^ p) x = (schwarzRearrangementReal f x) ^ p := by
  have hfp_meas : AEMeasurable (fun y ↦ f y ^ p) volume := hf.pow_const p
  have hfp_dist : ∀ t : ℝ, 0 < t → volume {y | t < f y ^ p} < ⊤ :=
    fun _ ht ↦ volume_lt_rpow_lt_top hf_nn hdist hp ht
  rw [schwarzRearrangementReal_eq_schwarzRadialProfileReal_norm_of_ne_zero hfp_meas hfp_dist hx,
    schwarzRearrangementReal_eq_schwarzRadialProfileReal_norm_of_ne_zero hf hdist hx,
    schwarzRadialProfileReal_rpow hf hf_nn hdist hp (norm_pos_iff.mpr hx)]
/-- **Almost everywhere power commutation for `schwarzRearrangementReal`**: for a nonnegative
a.e. measurable function `f` with finite superlevel volumes and `0 < p : ℝ`,
`schwarzRearrangementReal (fun y ↦ f y ^ p) =ᵐ[volume] fun x ↦ (schwarzRearrangementReal f x) ^ p`.
-/
theorem schwarzRearrangementReal_rpow_ae [NeZero n] {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f volume) (hf_nn : ∀ y, 0 ≤ f y)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) {p : ℝ} (hp : 0 < p) :
    schwarzRearrangementReal (fun y ↦ f y ^ p) =ᵐ[volume]
      fun x ↦ (schwarzRearrangementReal f x) ^ p := by
  have h0 : volume ({0} : Set (EuclideanSpace ℝ (Fin n))) = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr h0] with x hx
  exact schwarzRearrangementReal_rpow_of_ne_zero hf hf_nn hdist hp hx

/-! ### Real-valued `L^p` / `L^1` equimeasurability and integral preservation -/

/-- **`Lᵖ` norm preservation for `schwarzRearrangementReal`** for a nonnegative function
`f ∈ Lᵖ` (`0 < p < ∞`), without requiring a separate finite-superlevel hypothesis. -/
theorem eLpNorm_schwarzRearrangementReal_of_memLp [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hf_nn : 0 ≤ᵐ[volume] f) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) :
    eLpNorm (schwarzRearrangementReal f) p volume = eLpNorm f p volume :=
  eLpNorm_schwarzRearrangementReal hf.aestronglyMeasurable.aemeasurable hf_nn
    (fun _ ht ↦ volume_lt_lt_top_of_memLp hf hp0 hptop ht) p
/-- **`Lᵖ` norm preservation for `schwarzRearrangementReal (|f|)`** for any signed function `f`
whose absolute value has finite superlevel sets. -/
theorem eLpNorm_schwarzRearrangementReal_abs [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < |f y|} < ⊤) (p : ℝ≥0∞) :
    eLpNorm (schwarzRearrangementReal (fun y ↦ |f y|)) p volume = eLpNorm f p volume := by
  have hmeas : AEMeasurable (fun y ↦ |f y|) volume := by fun_prop
  rw [eLpNorm_schwarzRearrangementReal hmeas
      (Eventually.of_forall fun y ↦ abs_nonneg (f y)) hdist p]
  simp_rw [← Real.norm_eq_abs]
  exact eLpNorm_norm f hf.aestronglyMeasurable
/-- **`MemLp` preservation for `schwarzRearrangementReal (|f|)`** (`0 < p < ∞`). -/
theorem memLp_schwarzRearrangementReal_abs [NeZero n] {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) :
    MemLp (schwarzRearrangementReal (fun y ↦ |f y|)) p volume :=
  memLp_schwarzRearrangementReal hf.abs (Eventually.of_forall fun y ↦ abs_nonneg (f y)) hp0 hptop
/-- **`Lᵖ` norm preservation for `schwarzRearrangementReal (|f|)`** for `f ∈ Lᵖ` (`0 < p < ∞`). -/
theorem eLpNorm_schwarzRearrangementReal_abs_of_memLp [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) :
    eLpNorm (schwarzRearrangementReal (fun y ↦ |f y|)) p volume = eLpNorm f p volume :=
  eLpNorm_schwarzRearrangementReal_abs hf.aestronglyMeasurable.aemeasurable
    (fun _ ht ↦ volume_lt_lt_top_of_memLp hf.abs hp0 hptop ht) p
/-- Lower Lebesgue integral preservation for `schwarzRearrangementReal` on functions with finite
superlevel sets. -/
theorem lintegral_ofReal_schwarzRearrangementReal_eq [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) :
    ∫⁻ x, ENNReal.ofReal (schwarzRearrangementReal f x) = ∫⁻ y, ENNReal.ofReal (f y) := by
  rw [lintegral_congr_ae (ofReal_schwarzRearrangementReal_ae hf hdist),
    lintegral_schwarzRearrangement hf.ennreal_ofReal]
/-- **Integrability of `schwarzRearrangementReal f`** for an integrable nonnegative function `f`. -/
theorem integrable_schwarzRearrangementReal [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f volume) (hf_nn : 0 ≤ᵐ[volume] f) :
    Integrable (schwarzRearrangementReal f) volume := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact memLp_schwarzRearrangementReal hf hf_nn one_ne_zero ENNReal.one_ne_top
/-- **Integrability of `schwarzRearrangementReal (|f|)`** for an integrable function `f`. -/
theorem integrable_schwarzRearrangementReal_abs [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f volume) :
    Integrable (schwarzRearrangementReal (fun y ↦ |f y|)) volume :=
  integrable_schwarzRearrangementReal hf.abs (Eventually.of_forall fun y ↦ abs_nonneg (f y))
/-- **Bochner integral preservation for `schwarzRearrangementReal`** on integrable nonnegative
functions. -/
theorem integral_schwarzRearrangementReal_eq [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f volume) (hf_nn : 0 ≤ᵐ[volume] f) :
    ∫ x, schwarzRearrangementReal f x = ∫ y, f y := by
  have hf_mem : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf
  have hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤ :=
    fun _ ht ↦ volume_lt_lt_top_of_memLp hf_mem one_ne_zero ENNReal.one_ne_top ht
  rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x ↦ schwarzRearrangementReal_nonneg f x)
      (measurable_schwarzRearrangementReal f).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hf_nn hf.aestronglyMeasurable,
    lintegral_ofReal_schwarzRearrangementReal_eq hf.aestronglyMeasurable.aemeasurable hdist]
/-- **Bochner `L¹` norm preservation for `schwarzRearrangementReal (|f|)`** on integrable
functions. -/
theorem integral_schwarzRearrangementReal_abs_eq [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f volume) :
    ∫ x, schwarzRearrangementReal (fun y ↦ |f y|) x = ∫ y, |f y| :=
  integral_schwarzRearrangementReal_eq hf.abs (Eventually.of_forall fun y ↦ abs_nonneg (f y))
/-- `∫ x, |schwarzRearrangementReal (|f|) x| = ∫ y, |f y|` for an integrable function `f`. -/
theorem integral_abs_schwarzRearrangementReal_abs_eq [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f volume) :
    ∫ x, |schwarzRearrangementReal (fun y ↦ |f y|) x| = ∫ y, |f y| := by
  have hcongr : (fun x ↦ |schwarzRearrangementReal (fun y ↦ |f y|) x|) =
      schwarzRearrangementReal (fun y ↦ |f y|) := by
    ext x; exact abs_of_nonneg (schwarzRearrangementReal_nonneg _ x)
  rw [hcongr, integral_schwarzRearrangementReal_abs_eq hf]

/-! ### Additive constant shifts and uniform (`L^∞`) contraction -/

/-- Adding a constant `c : ℝ≥0∞` increases `layerCakeQuantile` by at most `c`. -/
theorem layerCakeQuantile_add_const_le (μ : Measure α) (f : α → ℝ≥0∞) (c v : ℝ≥0∞) :
    layerCakeQuantile μ (fun x ↦ f x + c) v ≤ layerCakeQuantile μ f v + c := by
  rw [layerCakeQuantile_le_iff]
  have hle : μ {x | layerCakeQuantile μ f v < f x} ≤ v := layerCakeQuantile_le_iff.mp le_rfl
  refine (measure_mono fun x (hx : layerCakeQuantile μ f v + c < f x + c) ↦ ?_).trans hle
  simp only [mem_ofPred_eq]; by_contra! hfx; exact not_le_of_gt hx (add_le_add_left hfx c)
/-- **Translation equivariance of `layerCakeQuantile`** when `v < μ univ`:
`layerCakeQuantile μ (fun x ↦ f x + c) v = layerCakeQuantile μ f v + c`. -/
theorem layerCakeQuantile_add_const {μ : Measure α} (f : α → ℝ≥0∞) (c : ℝ≥0∞) {v : ℝ≥0∞}
    (hv : v < μ univ) :
    layerCakeQuantile μ (fun x ↦ f x + c) v = layerCakeQuantile μ f v + c := by
  refine ennreal_eq_of_forall_lt_iff fun s ↦ ?_
  rcases lt_or_ge s c with hsc | hcs
  · have hrhs : s < layerCakeQuantile μ f v + c := hsc.trans_le le_add_self
    have hlhs : s < layerCakeQuantile μ (fun x ↦ f x + c) v := by
      have huniv : {x | s < f x + c} = univ := eq_univ_of_forall fun x ↦ hsc.trans_le le_add_self
      rwa [lt_layerCakeQuantile_iff, huniv]
    exact iff_of_true hlhs hrhs
  · rcases eq_or_ne c ⊤ with rfl | hctop
    · obtain rfl : s = ⊤ := top_unique hcs; simp
    · rw [← tsub_add_cancel_of_le hcs, lt_layerCakeQuantile_iff,
        ENNReal.add_lt_add_iff_right hctop, lt_layerCakeQuantile_iff]
      have hset : {x | s - c + c < f x + c} = {x | s - c < f x} := by
        ext x; exact ENNReal.add_lt_add_iff_right hctop
      rw [hset]
/-- Adding a constant `c : ℝ≥0∞` shifts `schwarzRadialProfile` by `c`. -/
theorem schwarzRadialProfile_add_const [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (c : ℝ≥0∞) (r : ℝ) :
    schwarzRadialProfile (fun y ↦ f y + c) r = schwarzRadialProfile f r + c := by
  rw [schwarzRadialProfile_eq_layerCakeQuantile, schwarzRadialProfile_eq_layerCakeQuantile]
  refine layerCakeQuantile_add_const f c ?_
  set R : ℝ := max r 0 + 1
  have hR_pos : 0 < R := by positivity
  have hlt_R : ENNReal.ofReal r ^ n < ENNReal.ofReal R ^ n := by
    calc ENNReal.ofReal r ^ n ≤ ENNReal.ofReal (max r 0) ^ n := by gcongr; exact le_max_left r 0
      _ = ENNReal.ofReal (max r 0 ^ n) := (ENNReal.ofReal_pow (le_max_right r 0) n).symm
      _ < ENNReal.ofReal (R ^ n) := (ENNReal.ofReal_lt_ofReal_iff (pow_pos hR_pos n)).mpr
          (pow_lt_pow_left₀ (lt_add_one _) (le_max_right r 0) (NeZero.ne n))
      _ = ENNReal.ofReal R ^ n := ENNReal.ofReal_pow hR_pos.le n
  calc unitBallVolume n * ENNReal.ofReal r ^ n < unitBallVolume n * ENNReal.ofReal R ^ n := by
        rw [mul_comm (unitBallVolume n), mul_comm (unitBallVolume n)]
        exact ENNReal.mul_lt_mul_left (unitBallVolume_ne_zero n) (unitBallVolume_ne_top n) hlt_R
    _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) :=
        (volume_ball_euclideanSpace 0 hR_pos.le).symm
    _ ≤ volume (univ : Set (EuclideanSpace ℝ (Fin n))) := measure_mono (subset_univ _)
/-- Adding a constant `c : ℝ≥0∞` shifts `schwarzRearrangement` by `c`. -/
theorem schwarzRearrangement_add_const [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (c : ℝ≥0∞) (x : EuclideanSpace ℝ (Fin n)) :
    schwarzRearrangement (fun y ↦ f y + c) x = schwarzRearrangement f x + c := by
  rw [schwarzRearrangement_apply, schwarzRearrangement_apply, schwarzRadialProfile_add_const]
/-- **One-sided uniform (`L^∞`) contraction for `layerCakeQuantile`**: if `f ≤ᵐ[μ] g + c`, then
`layerCakeQuantile μ f v - layerCakeQuantile μ g v ≤ c`. -/
theorem layerCakeQuantile_tsub_le {μ : Measure α} {f g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hfg : f ≤ᵐ[μ] fun x ↦ g x + c) (v : ℝ≥0∞) :
    layerCakeQuantile μ f v - layerCakeQuantile μ g v ≤ c :=
  tsub_le_iff_left.mpr
    ((layerCakeQuantile_mono_ae hfg v).trans (layerCakeQuantile_add_const_le μ g c v))
/-- Pointwise supremum contraction for `layerCakeQuantile`:
`layerCakeQuantile μ f v - layerCakeQuantile μ g v ≤ ⨆ x, (f x - g x)`. -/
theorem layerCakeQuantile_tsub_le_iSup_tsub (μ : Measure α) (f g : α → ℝ≥0∞) (v : ℝ≥0∞) :
    layerCakeQuantile μ f v - layerCakeQuantile μ g v ≤ ⨆ x, (f x - g x) := by
  refine layerCakeQuantile_tsub_le (Eventually.of_forall fun x ↦ ?_) v
  calc f x ≤ g x + (f x - g x) := le_add_tsub
    _ ≤ g x + ⨆ y, (f y - g y) := add_le_add_right (le_iSup (fun y ↦ f y - g y) x) (g x)
/-- **One-sided uniform (`L^∞`) contraction for `schwarzRadialProfile`**. -/
theorem schwarzRadialProfile_tsub_le [NeZero n] {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    {c : ℝ≥0∞} (hfg : f ≤ᵐ[volume] fun y ↦ g y + c) (r : ℝ) :
    schwarzRadialProfile f r - schwarzRadialProfile g r ≤ c := by
  rw [schwarzRadialProfile_eq_layerCakeQuantile, schwarzRadialProfile_eq_layerCakeQuantile]
  exact layerCakeQuantile_tsub_le hfg _
/-- Pointwise supremum contraction for `schwarzRadialProfile`. -/
theorem schwarzRadialProfile_tsub_le_iSup_tsub [NeZero n]
    (f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (r : ℝ) :
    schwarzRadialProfile f r - schwarzRadialProfile g r ≤ ⨆ y, (f y - g y) := by
  rw [schwarzRadialProfile_eq_layerCakeQuantile, schwarzRadialProfile_eq_layerCakeQuantile]
  exact layerCakeQuantile_tsub_le_iSup_tsub volume f g _
/-- **One-sided uniform (`L^∞`) contraction for `schwarzRearrangement`**. -/
theorem schwarzRearrangement_tsub_le [NeZero n] {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    {c : ℝ≥0∞} (hfg : f ≤ᵐ[volume] fun y ↦ g y + c) (x : EuclideanSpace ℝ (Fin n)) :
    schwarzRearrangement f x - schwarzRearrangement g x ≤ c := by
  rw [schwarzRearrangement_apply, schwarzRearrangement_apply]
  exact schwarzRadialProfile_tsub_le hfg ‖x‖
/-- Pointwise supremum contraction for `schwarzRearrangement`. -/
theorem schwarzRearrangement_tsub_le_iSup_tsub [NeZero n]
    (f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (x : EuclideanSpace ℝ (Fin n)) :
    schwarzRearrangement f x - schwarzRearrangement g x ≤ ⨆ y, (f y - g y) := by
  rw [schwarzRearrangement_apply, schwarzRearrangement_apply]
  exact schwarzRadialProfile_tsub_le_iSup_tsub f g ‖x‖
/-- **Uniform (`L^∞`) contraction for `schwarzRadialProfileReal`** on `(0, ∞)`: if
`|f y - g y| ≤ c` a.e. for some `c ≥ 0`, then
`|schwarzRadialProfileReal f r - schwarzRadialProfileReal g r| ≤ c` for all `r > 0`. -/
theorem abs_schwarzRadialProfileReal_sub_le [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hf_dist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    (hg_dist : ∀ t : ℝ, 0 < t → volume {y | t < g y} < ⊤)
    (hc : 0 ≤ c) (hfg : ∀ᵐ y ∂volume, |f y - g y| ≤ c) {r : ℝ} (hr : 0 < r) :
    |schwarzRadialProfileReal f r - schwarzRadialProfileReal g r| ≤ c := by
  have h1 : (fun y ↦ ENNReal.ofReal (f y)) ≤ᵐ[volume]
      fun y ↦ ENNReal.ofReal (g y) + ENNReal.ofReal c := by
    filter_upwards [hfg] with y hy
    exact (ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp hy).2])).trans ENNReal.ofReal_add_le
  have h2 : (fun y ↦ ENNReal.ofReal (g y)) ≤ᵐ[volume]
      fun y ↦ ENNReal.ofReal (f y) + ENNReal.ofReal c := by
    filter_upwards [hfg] with y hy
    exact (ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp hy).1])).trans ENNReal.ofReal_add_le
  have hle1 := tsub_le_iff_left.mp (schwarzRadialProfile_tsub_le h1 r)
  have hle2 := tsub_le_iff_left.mp (schwarzRadialProfile_tsub_le h2 r)
  rw [← ofReal_schwarzRadialProfileReal_of_pos hf hf_dist hr,
    ← ofReal_schwarzRadialProfileReal_of_pos hg hg_dist hr,
    ← ENNReal.ofReal_add (schwarzRadialProfileReal_nonneg g r) hc,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (schwarzRadialProfileReal_nonneg g r) hc)] at hle1
  rw [← ofReal_schwarzRadialProfileReal_of_pos hf hf_dist hr,
    ← ofReal_schwarzRadialProfileReal_of_pos hg hg_dist hr,
    ← ENNReal.ofReal_add (schwarzRadialProfileReal_nonneg f r) hc,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (schwarzRadialProfileReal_nonneg f r) hc)] at hle2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
/-- **Almost everywhere uniform (`L^∞`) contraction for `schwarzRearrangementReal`**. -/
theorem abs_schwarzRearrangementReal_sub_le_ae [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hf_dist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    (hg_dist : ∀ t : ℝ, 0 < t → volume {y | t < g y} < ⊤)
    (hc : 0 ≤ c) (hfg : ∀ᵐ y ∂volume, |f y - g y| ≤ c) :
    ∀ᵐ x ∂volume, |schwarzRearrangementReal f x - schwarzRearrangementReal g x| ≤ c := by
  filter_upwards [schwarzRearrangementReal_ae_eq_schwarzRadialProfileReal_norm hf hf_dist,
    schwarzRearrangementReal_ae_eq_schwarzRadialProfileReal_norm hg hg_dist,
    compl_mem_ae_iff.mpr (by simp : volume ({0} : Set (EuclideanSpace ℝ (Fin n))) = 0)]
    with x hfx hgx hx0
  rw [hfx, hgx]
  exact abs_schwarzRadialProfileReal_sub_le hf hg hf_dist hg_dist hc hfg (norm_pos_iff.mpr hx0)

/-! ### Crandall–Tartar `tsub` contraction and `L^1` / `L^p` continuity -/

/-- **Crandall–Tartar one-sided `tsub` contraction for `schwarzRearrangement`**: for almost
everywhere measurable `f, g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞` that are finite a.e. and have
finite superlevel volumes for positive thresholds,
`∫⁻ x, (schwarzRearrangement g x - schwarzRearrangement f x) ≤ ∫⁻ y, (g y - f y)`. -/
theorem lintegral_tsub_schwarzRearrangement_le [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hf_dist : ∀ t : ℝ≥0∞, 0 < t → distributionFunction f t < ⊤)
    (hg_dist : ∀ t : ℝ≥0∞, 0 < t → distributionFunction g t < ⊤)
    (hf_top : volume {y | f y = ⊤} = 0) (hg_top : volume {y | g y = ⊤} = 0) :
    ∫⁻ x, (schwarzRearrangement g x - schwarzRearrangement f x) ≤ ∫⁻ y, (g y - f y) := by
  let fR : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦ (f y).toReal
  let gR : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦ (g y).toReal
  have hf_ae_lt : ∀ᵐ y ∂volume, f y < ⊤ := by rw [ae_iff]; simpa [not_lt, top_le_iff] using hf_top
  have hg_ae_lt : ∀ᵐ y ∂volume, g y < ⊤ := by rw [ae_iff]; simpa [not_lt, top_le_iff] using hg_top
  have hfR_ae : (fun y ↦ ENNReal.ofReal (fR y)) =ᵐ[volume] f :=
    hf_ae_lt.mono fun y hy ↦ ENNReal.ofReal_toReal hy.ne
  have hgR_ae : (fun y ↦ ENNReal.ofReal (gR y)) =ᵐ[volume] g :=
    hg_ae_lt.mono fun y hy ↦ ENNReal.ofReal_toReal hy.ne
  have hfR_dist (t : ℝ) (ht : 0 < t) : volume {y | t < fR y} < ⊤ := by
    have hsub : {y | t < fR y} ⊆ {y | ENNReal.ofReal t < f y} := fun y (hy : t < (f y).toReal) ↦
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hy).trans_le ENNReal.ofReal_toReal_le
    exact (measure_mono hsub).trans_lt (by
      simpa [distributionFunction_eq_volume] using
        hf_dist (ENNReal.ofReal t) (ENNReal.ofReal_pos.mpr ht))
  have hgR_dist (t : ℝ) (ht : 0 < t) : volume {y | t < gR y} < ⊤ := by
    have hsub : {y | t < gR y} ⊆ {y | ENNReal.ofReal t < g y} := fun y (hy : t < (g y).toReal) ↦
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hy).trans_le ENNReal.ofReal_toReal_le
    exact (measure_mono hsub).trans_lt (by
      simpa [distributionFunction_eq_volume] using
        hg_dist (ENNReal.ofReal t) (ENNReal.ofReal_pos.mpr ht))
  rw [← schwarzRearrangement_congr_ae hfR_ae, ← schwarzRearrangement_congr_ae hgR_ae]
  have hlhs : (fun x ↦ schwarzRearrangement (fun y ↦ ENNReal.ofReal (gR y)) x -
        schwarzRearrangement (fun y ↦ ENNReal.ofReal (fR y)) x) =ᵐ[volume]
      fun x ↦ ENNReal.ofReal
        (schwarzRearrangementReal gR x - schwarzRearrangementReal fR x - 0) := by
    filter_upwards [ofReal_schwarzRearrangementReal_ae hf.ennreal_toReal hfR_dist,
      ofReal_schwarzRearrangementReal_ae hg.ennreal_toReal hgR_dist] with x hfx hgx
    rw [← hfx, ← hgx, sub_zero, ENNReal.ofReal_sub _ (schwarzRearrangementReal_nonneg fR x)]
  have hrhs : (fun y ↦ g y - f y) =ᵐ[volume] fun y ↦ ENNReal.ofReal (gR y - fR y - 0) := by
    filter_upwards [hfR_ae, hgR_ae] with y hfy hgy
    rw [← hfy, ← hgy, sub_zero, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
  rw [lintegral_congr_ae hlhs, lintegral_congr_ae hrhs]
  exact lintegral_ofReal_sub_sub_schwarzRearrangementReal_le hf.ennreal_toReal hg.ennreal_toReal
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) hfR_dist hgR_dist le_rfl
/-- **Two-sided `tsub` (`L¹`) contraction for `schwarzRearrangement`**. -/
theorem lintegral_tsub_add_tsub_schwarzRearrangement_le [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hf_dist : ∀ t : ℝ≥0∞, 0 < t → distributionFunction f t < ⊤)
    (hg_dist : ∀ t : ℝ≥0∞, 0 < t → distributionFunction g t < ⊤)
    (hf_top : volume {y | f y = ⊤} = 0) (hg_top : volume {y | g y = ⊤} = 0) :
    ∫⁻ x, ((schwarzRearrangement f x - schwarzRearrangement g x) +
        (schwarzRearrangement g x - schwarzRearrangement f x)) ≤
      ∫⁻ y, ((f y - g y) + (g y - f y)) := by
  have hmeas1 : AEMeasurable
      (fun x ↦ schwarzRearrangement f x - schwarzRearrangement g x) volume := by fun_prop
  have hmeas2 : AEMeasurable (fun y ↦ f y - g y) volume := hf.sub hg
  rw [lintegral_add_left' hmeas1, lintegral_add_left' hmeas2]
  exact add_le_add
    (lintegral_tsub_schwarzRearrangement_le hg hf hg_dist hf_dist hg_top hf_top)
    (lintegral_tsub_schwarzRearrangement_le hf hg hf_dist hg_dist hf_top hg_top)
/-- The difference `schwarzRearrangementReal f - schwarzRearrangementReal g` is integrable when
`f, g` are integrable and nonnegative a.e. -/
theorem integrable_sub_schwarzRearrangementReal [NeZero n] {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hf_nn : 0 ≤ᵐ[volume] f) (hg_nn : 0 ≤ᵐ[volume] g) :
    Integrable (fun x ↦ schwarzRearrangementReal f x - schwarzRearrangementReal g x) volume :=
  (integrable_schwarzRearrangementReal hf hf_nn).sub (integrable_schwarzRearrangementReal hg hg_nn)
/-- **Bochner `L¹` contraction of Schwarz rearrangement**: for integrable nonnegative functions
`f, g : EuclideanSpace ℝ (Fin n) → ℝ`,
`∫ x, |schwarzRearrangementReal f x - schwarzRearrangementReal g x| ≤ ∫ y, |f y - g y|`. -/
theorem integral_abs_sub_schwarzRearrangementReal_le [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hf_nn : 0 ≤ᵐ[volume] f) (hg_nn : 0 ≤ᵐ[volume] g) :
    ∫ x, |schwarzRearrangementReal f x - schwarzRearrangementReal g x| ≤ ∫ y, |f y - g y| := by
  have hf_mem : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf
  have hg_mem : MemLp g 1 volume := memLp_one_iff_integrable.mpr hg
  have hsub1 := (integrable_sub_schwarzRearrangementReal hf hg hf_nn hg_nn).abs
  have hsub2 : Integrable (fun y ↦ |f y - g y|) volume := (hf.sub hg).abs
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x ↦ abs_nonneg _)
      hsub1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y ↦ abs_nonneg _)
      hsub2.aestronglyMeasurable]
  simp_rw [← Real.enorm_eq_ofReal_abs]
  exact ENNReal.toReal_mono (hf.sub hg).hasFiniteIntegral.ne
    (lintegral_enorm_sub_schwarzRearrangementReal_le
      hf.aestronglyMeasurable.aemeasurable hg.aestronglyMeasurable.aemeasurable hf_nn hg_nn
      (fun _ ht ↦ volume_lt_lt_top_of_memLp hf_mem one_ne_zero ENNReal.one_ne_top ht)
      (fun _ ht ↦ volume_lt_lt_top_of_memLp hg_mem one_ne_zero ENNReal.one_ne_top ht))
/-- **`Lᵖ` contraction of `schwarzRearrangementReal (|f|)`** for signed functions `f, g ∈ Lᵖ`
(`1 ≤ p < ∞`). -/
theorem eLpNorm_sub_schwarzRearrangementReal_abs_le_of_memLp [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hg : MemLp g p volume) (hp1 : 1 ≤ p) (hptop : p ≠ ⊤) :
    eLpNorm (schwarzRearrangementReal (fun y ↦ |f y|) -
        schwarzRearrangementReal (fun y ↦ |g y|)) p volume ≤ eLpNorm (f - g) p volume := by
  refine (eLpNorm_sub_schwarzRearrangementReal_le_of_memLp hf.abs hg.abs
    (Eventually.of_forall fun y ↦ abs_nonneg (f y))
    (Eventually.of_forall fun y ↦ abs_nonneg (g y)) hp1 hptop).trans ?_
  refine eLpNorm_mono_enorm (hf.abs.sub hg.abs).aestronglyMeasurable fun y ↦ ?_
  simp only [Pi.sub_apply, Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub (f y) (g y))
/-- **`Lᵖ` continuity of `schwarzRearrangementReal`** (`1 ≤ p < ∞`): if `fₖ → f` in `Lᵖ`, then
`schwarzRearrangementReal (fₖ) → schwarzRearrangementReal f` in `Lᵖ`. -/
theorem tendsto_eLpNorm_sub_schwarzRearrangementReal [NeZero n]
    {ι : Type*} {l : Filter ι} {f : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : ∀ i, MemLp (f i) p volume) (hg : MemLp g p volume)
    (hf_nn : ∀ i, 0 ≤ᵐ[volume] f i) (hg_nn : 0 ≤ᵐ[volume] g) (hp1 : 1 ≤ p) (hptop : p ≠ ⊤)
    (htend : Tendsto (fun i ↦ eLpNorm (f i - g) p volume) l (𝓝 0)) :
    Tendsto (fun i ↦
      eLpNorm (schwarzRearrangementReal (f i) - schwarzRearrangementReal g) p volume) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ≥0∞))) htend (fun _ ↦ zero_le)
    (fun i ↦ eLpNorm_sub_schwarzRearrangementReal_le_of_memLp (hf i) hg (hf_nn i) hg_nn hp1 hptop)
/-- **`Lᵖ` continuity of `schwarzRearrangementReal (|f|)`** (`1 ≤ p < ∞`) on signed functions. -/
theorem tendsto_eLpNorm_sub_schwarzRearrangementReal_abs [NeZero n]
    {ι : Type*} {l : Filter ι} {f : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : ∀ i, MemLp (f i) p volume) (hg : MemLp g p volume) (hp1 : 1 ≤ p) (hptop : p ≠ ⊤)
    (htend : Tendsto (fun i ↦ eLpNorm (f i - g) p volume) l (𝓝 0)) :
    Tendsto (fun i ↦
      eLpNorm (schwarzRearrangementReal (fun y ↦ |f i y|) -
        schwarzRearrangementReal (fun y ↦ |g y|)) p volume) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ≥0∞))) htend (fun _ ↦ zero_le)
    (fun i ↦ eLpNorm_sub_schwarzRearrangementReal_abs_le_of_memLp (hf i) hg hp1 hptop)
/-- **Bochner `L¹` continuity of `schwarzRearrangementReal`** on integrable nonnegative
functions. -/
theorem tendsto_integral_abs_sub_schwarzRearrangementReal [NeZero n]
    {ι : Type*} {l : Filter ι} {f : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ i, Integrable (f i) volume) (hg : Integrable g volume)
    (hf_nn : ∀ i, 0 ≤ᵐ[volume] f i) (hg_nn : 0 ≤ᵐ[volume] g)
    (htend : Tendsto (fun i ↦ ∫ y, |f i y - g y|) l (𝓝 0)) :
    Tendsto (fun i ↦
      ∫ x, |schwarzRearrangementReal (f i) x - schwarzRearrangementReal g x|) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ))) htend (fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _)
    (fun i ↦ integral_abs_sub_schwarzRearrangementReal_le (hf i) hg (hf_nn i) hg_nn)

/-! ### Radial profile weighted derivative bounds and origin/infinity decay -/

/-- For an antitone function `v : ℝ → ℝ`, `|deriv v r| = -deriv v r` everywhere. -/
theorem abs_deriv_of_antitone {v : ℝ → ℝ} (hv : Antitone v) (r : ℝ) :
    |deriv v r| = -deriv v r :=
  abs_of_nonpos hv.deriv_nonpos
/-- Any globally `K`-Lipschitz function `v : ℝ → ℝ` is absolutely continuous on every compact
interval `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_lipschitzWith {v : ℝ → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) (a b : ℝ) :
    AbsolutelyContinuousOnInterval v a b :=
  hv.lipschitzOnWith.absolutelyContinuousOnInterval
/-- When `h : EuclideanSpace ℝ (Fin n) → ℝ` is `K`-Lipschitz with finite superlevel volumes for
`t > 0`, its real radial profile `schwarzRadialProfileReal h` is absolutely continuous on every
compact interval `[a, b]`. -/
theorem absolutelyContinuousOnInterval_schwarzRadialProfileReal [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (schwarzRadialProfileReal h) a b :=
  absolutelyContinuousOnInterval_of_lipschitzWith
    (lipschitzWith_schwarzRadialProfileReal hh hdist) a b
/-- Fundamental theorem of calculus for an antitone absolutely continuous radial profile on
`[r₁, r₂]`: `∫ s in r₁..r₂, |deriv v s| = v r₁ - v r₂`. -/
theorem intervalIntegral_abs_deriv_eq_sub_of_antitone {v : ℝ → ℝ} (hv : Antitone v)
    {r₁ r₂ : ℝ} (hAC : AbsolutelyContinuousOnInterval v r₁ r₂) :
    ∫ s in r₁..r₂, |deriv v s| = v r₁ - v r₂ := by
  simp_rw [abs_deriv_of_antitone hv]
  rw [intervalIntegral.integral_neg, hAC.integral_deriv_eq_sub, neg_sub]
/-- Set-integral form of the fundamental theorem of calculus for an antitone absolutely continuous
radial profile on `Ioc r₁ r₂` (`r₁ ≤ r₂`): `∫ s in Ioc r₁ r₂, |deriv v s| = v r₁ - v r₂`. -/
theorem setIntegral_Ioc_abs_deriv_eq_sub_of_antitone {v : ℝ → ℝ} (hv : Antitone v)
    {r₁ r₂ : ℝ} (hle : r₁ ≤ r₂) (hAC : AbsolutelyContinuousOnInterval v r₁ r₂) :
    ∫ s in Ioc r₁ r₂, |deriv v s| = v r₁ - v r₂ := by
  rw [← intervalIntegral.integral_of_le hle,
    intervalIntegral_abs_deriv_eq_sub_of_antitone hv hAC]
/-- Set-integral form of the fundamental theorem of calculus on `Icc r₁ r₂` (`r₁ ≤ r₂`). -/
theorem setIntegral_Icc_abs_deriv_eq_sub_of_antitone {v : ℝ → ℝ} (hv : Antitone v)
    {r₁ r₂ : ℝ} (hle : r₁ ≤ r₂) (hAC : AbsolutelyContinuousOnInterval v r₁ r₂) :
    ∫ s in Icc r₁ r₂, |deriv v s| = v r₁ - v r₂ := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    setIntegral_Ioc_abs_deriv_eq_sub_of_antitone hv hle hAC]
/-- For an absolutely continuous function `v : ℝ → ℝ` on `[r₁, r₂]` (`r₁ ≤ r₂`), the weighted
derivative `s ↦ |deriv v s| * s ^ m` is integrable on `Ioc r₁ r₂`. -/
theorem integrableOn_abs_deriv_mul_pow_Ioc {v : ℝ → ℝ} {r₁ r₂ : ℝ} (hle : r₁ ≤ r₂)
    (hAC : AbsolutelyContinuousOnInterval v r₁ r₂) (m : ℕ) :
    IntegrableOn (fun s ↦ |deriv v s| * s ^ m) (Ioc r₁ r₂) volume := by
  have hint : IntegrableOn (fun s ↦ |deriv v s|) (Icc r₁ r₂) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      hAC.intervalIntegrable_deriv.abs
  have hcont : ContinuousOn (fun s : ℝ ↦ s ^ m) (Icc r₁ r₂) := (continuous_pow m).continuousOn
  exact (hint.mul_continuousOn hcont isCompact_Icc).mono_set Ioc_subset_Icc_self
/-- For an absolutely continuous function `v : ℝ → ℝ` on `[r₁, r₂]` (`r₁ ≤ r₂`), the weighted
derivative `s ↦ |deriv v s| * s ^ m` is integrable on `Icc r₁ r₂`. -/
theorem integrableOn_abs_deriv_mul_pow_Icc {v : ℝ → ℝ} {r₁ r₂ : ℝ} (hle : r₁ ≤ r₂)
    (hAC : AbsolutelyContinuousOnInterval v r₁ r₂) (m : ℕ) :
    IntegrableOn (fun s ↦ |deriv v s| * s ^ m) (Icc r₁ r₂) volume := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact integrableOn_abs_deriv_mul_pow_Ioc hle hAC m
/-- **Weighted derivative lower bound on `[r₁, r₂]`**: for an antitone absolutely continuous profile
`v : ℝ → ℝ` on `[r₁, r₂]` with `0 ≤ r₁ ≤ r₂`,
`r₁ ^ m * (v r₁ - v r₂) ≤ ∫ s in Ioc r₁ r₂, |deriv v s| * s ^ m`. -/
theorem mul_sub_le_setIntegral_Ioc_abs_deriv_mul_pow {v : ℝ → ℝ} (hv : Antitone v)
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hle : r₁ ≤ r₂)
    (hAC : AbsolutelyContinuousOnInterval v r₁ r₂) (m : ℕ) :
    r₁ ^ m * (v r₁ - v r₂) ≤ ∫ s in Ioc r₁ r₂, |deriv v s| * s ^ m := by
  rw [← setIntegral_Ioc_abs_deriv_eq_sub_of_antitone hv hle hAC,
    ← MeasureTheory.integral_const_mul]
  have hint1 : IntegrableOn (fun s ↦ r₁ ^ m * |deriv v s|) (Ioc r₁ r₂) volume := by
    refine Integrable.const_mul ?_ (r₁ ^ m)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hAC.intervalIntegrable_deriv.abs
  have hint2 := integrableOn_abs_deriv_mul_pow_Ioc hle hAC m
  refine setIntegral_mono_on hint1 hint2 measurableSet_Ioc fun s hs ↦ ?_
  rw [mul_comm (r₁ ^ m) |deriv v s|]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr₁ hs.1.le m) (abs_nonneg _)
/-- Closed-interval (`Icc r₁ r₂`) version of `mul_sub_le_setIntegral_Ioc_abs_deriv_mul_pow`. -/
theorem mul_sub_le_setIntegral_Icc_abs_deriv_mul_pow {v : ℝ → ℝ} (hv : Antitone v)
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hle : r₁ ≤ r₂)
    (hAC : AbsolutelyContinuousOnInterval v r₁ r₂) (m : ℕ) :
    r₁ ^ m * (v r₁ - v r₂) ≤ ∫ s in Icc r₁ r₂, |deriv v s| * s ^ m := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact mul_sub_le_setIntegral_Ioc_abs_deriv_mul_pow hv hr₁ hle hAC m
/-- **Two-radius bound for `r ^ m * v r`**: for an antitone absolutely continuous profile
`v : ℝ → ℝ` on `[r₁, r₂]` with `0 ≤ r₁ ≤ r₂`,
`r₁ ^ m * v r₁ ≤ r₁ ^ m * v r₂ + ∫ s in Ioc r₁ r₂, |deriv v s| * s ^ m`. -/
theorem pow_mul_le_pow_mul_add_setIntegral_Ioc_abs_deriv_mul_pow {v : ℝ → ℝ} (hv : Antitone v)
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hle : r₁ ≤ r₂)
    (hAC : AbsolutelyContinuousOnInterval v r₁ r₂) (m : ℕ) :
    r₁ ^ m * v r₁ ≤ r₁ ^ m * v r₂ + ∫ s in Ioc r₁ r₂, |deriv v s| * s ^ m := by
  linarith [mul_sub_le_setIntegral_Ioc_abs_deriv_mul_pow hv hr₁ hle hAC m]
/-- **Origin decay `r ^ m * v r → 0` as `r → 0⁺` (`m ≥ 1`)**: if `v : ℝ → ℝ` is antitone,
nonnegative on `(0, ∞)`, absolutely continuous on `[r₁, r₂]` for all `0 < r₁ ≤ r₂ ≤ R₀`, and
`s ↦ |deriv v s| * s ^ m` is integrable on `Ioc 0 R₀` (`R₀ > 0`, `m ≥ 1`), then
`Tendsto (fun r ↦ r ^ m * v r) (𝓝[>] 0) (𝓝 0)`. -/
theorem tendsto_pow_mul_nhdsWithin_zero_of_antitone {v : ℝ → ℝ} (hv : Antitone v)
    (hv_nn : ∀ r > 0, 0 ≤ v r) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hAC : ∀ r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → r₂ ≤ R₀ → AbsolutelyContinuousOnInterval v r₁ r₂)
    {m : ℕ} (hm : 1 ≤ m)
    (hint : IntegrableOn (fun s ↦ |deriv v s| * s ^ m) (Ioc 0 R₀) volume) :
    Tendsto (fun r ↦ r ^ m * v r) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have htend_int : Tendsto
      (fun R ↦ ∫ s in Ioc 0 R, |deriv v s| * s ^ m ∂volume.restrict (Ioc 0 R₀))
      (𝓝[>] 0) (𝓝 0) := by
    refine Integrable.tendsto_setIntegral_nhds_zero hint ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ≥0∞))) ?_
      (fun _ ↦ zero_le) (fun R ↦ Measure.restrict_apply_le _ (Ioc 0 R))
    have h0 : Tendsto (fun R : ℝ ↦ ENNReal.ofReal R) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa [Function.comp_def, Real.volume_Ioc] using h0
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
  have hint_R₁ : |∫ s in Ioc 0 R₁, |deriv v s| * s ^ m| < ε / 2 := by
    have hrestrict : (volume.restrict (Ioc 0 R₀)).restrict (Ioc 0 R₁) =
        volume.restrict (Ioc 0 R₁) :=
      Measure.restrict_restrict_of_subset (Ioc_subset_Ioc_right hR₁_le_R₀)
    have hlt := hδ₁ hR₁_lt_δ₁ hR₁_pos
    rwa [hrestrict, Real.dist_eq, sub_zero] at hlt
  have hm_ne : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  have hpow_cont : Tendsto (fun r : ℝ ↦ r ^ m * v R₁) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ ↦ r ^ m * v R₁) := by fun_prop
    simpa [zero_pow hm_ne] using hcont.tendsto 0
  rw [Metric.tendsto_nhds] at hpow_cont
  have hpow_ev := hpow_cont (ε / 2) hε2
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hpow_ev, gt_mem_nhds hR₁_pos] with r hr_pow hr_lt_R₁ (hr_pos : 0 < r)
  have hr_nonneg : 0 ≤ r ^ m * v r := mul_nonneg (pow_nonneg hr_pos.le m) (hv_nn r hr_pos)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hr_nonneg]
  have hbound := pow_mul_le_pow_mul_add_setIntegral_Ioc_abs_deriv_mul_pow hv hr_pos.le
    hr_lt_R₁.le (hAC r R₁ hr_pos hr_lt_R₁.le hR₁_le_R₀) m
  have hmono_int : ∫ s in Ioc r R₁, |deriv v s| * s ^ m ≤
      ∫ s in Ioc 0 R₁, |deriv v s| * s ^ m := by
    refine setIntegral_mono_set (hint.mono_set (Ioc_subset_Ioc_right hR₁_le_R₀)) ?_
      (Eventually.of_forall (Ioc_subset_Ioc_left hr_pos.le))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hs.1.le m)
  have hr_pow' : r ^ m * v R₁ < ε / 2 :=
    (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hr_pow)
  have hint_R₁' : ∫ s in Ioc 0 R₁, |deriv v s| * s ^ m < ε / 2 :=
    (le_abs_self _).trans_lt hint_R₁
  linarith
/-- **Origin decay `r ^ (n - 1) * v r → 0` as `r → 0⁺` in dimension `n ≥ 2`**: for an antitone
nonnegative locally absolutely continuous radial profile `v : ℝ → ℝ` on `(0, R₀]` (`R₀ > 0`) with
`IntegrableOn (fun s ↦ |deriv v s| * s ^ (n - 1)) (Ioc 0 R₀) volume`,
`Tendsto (fun r ↦ r ^ (n - 1) * v r) (𝓝[>] 0) (𝓝 0)`. -/
theorem tendsto_pow_pred_mul_nhdsWithin_zero_of_antitone {v : ℝ → ℝ} (hv : Antitone v)
    (hv_nn : ∀ r > 0, 0 ≤ v r) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hAC : ∀ r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → r₂ ≤ R₀ → AbsolutelyContinuousOnInterval v r₁ r₂)
    (hn : 2 ≤ n)
    (hint : IntegrableOn (fun s ↦ |deriv v s| * s ^ (n - 1)) (Ioc 0 R₀) volume) :
    Tendsto (fun r ↦ r ^ (n - 1) * v r) (𝓝[>] 0) (𝓝 0) :=
  tendsto_pow_mul_nhdsWithin_zero_of_antitone hv hv_nn hR₀ hAC (Nat.le_sub_one_of_lt hn) hint
/-- **Origin decay `r ^ (n - 1) * schwarzRadialProfileReal h r → 0` as `r → 0⁺` for a Lipschitz
function `h`** in dimension `n ≥ 2`. -/
theorem tendsto_pow_pred_mul_schwarzRadialProfileReal_nhdsWithin_zero [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤) (hn : 2 ≤ n) :
    Tendsto (fun r ↦ r ^ (n - 1) * schwarzRadialProfileReal h r) (𝓝[>] 0) (𝓝 0) := by
  have hv := antitone_schwarzRadialProfileReal_of_lipschitzWith hh hdist
  have hAC : ∀ r₁ r₂ : ℝ, AbsolutelyContinuousOnInterval (schwarzRadialProfileReal h) r₁ r₂ :=
    absolutelyContinuousOnInterval_schwarzRadialProfileReal hh hdist
  exact tendsto_pow_pred_mul_nhdsWithin_zero_of_antitone hv
    (fun r _ ↦ schwarzRadialProfileReal_nonneg h r) zero_lt_one
    (fun r₁ r₂ _ _ _ ↦ hAC r₁ r₂) hn
    (integrableOn_abs_deriv_mul_pow_Ioc zero_le_one (hAC 0 1) (n - 1))
/-- **Decay at infinity `schwarzRadialProfileReal f r → 0` as `r → ∞`** when `f` has finite
superlevel volumes for all positive thresholds. -/
theorem tendsto_schwarzRadialProfileReal_atTop_zero [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) :
    Tendsto (schwarzRadialProfileReal f) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hfin : volume {y | ε / 2 < f y} ≠ ⊤ := (hdist (ε / 2) hε2).ne
  set R := schwarzRadius {y | ε / 2 < f y}
  refine ⟨max R 1, fun r hr ↦ ?_⟩
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_right R 1).trans hr)
  have hr_ge_R : R ≤ r := (le_max_left R 1).trans hr
  have hle : schwarzRadialProfileReal f r ≤ ε / 2 :=
    (schwarzRadialProfileReal_le_iff_schwarzRadius_le hf hdist hr_pos hε2.le hfin).mpr hr_ge_R
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (schwarzRadialProfileReal_nonneg f r)]
  exact hle.trans_lt (half_lt_self hε)
/-- **Power-weighted Markov bound on `schwarzRadialProfileReal`**: for `f ∈ Lᵖ` (`0 < p < ∞`)
and `r > 0`,
`(unitBallVolume n).toReal * r ^ n * (schwarzRadialProfileReal f r) ^ p.toReal ≤
  (∫⁻ y, ENNReal.ofReal (f y) ^ p.toReal).toReal`. -/
theorem rpow_mul_schwarzRadialProfileReal_le_of_memLp [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) {r : ℝ} (hr : 0 < r) :
    (unitBallVolume n).toReal * r ^ n * (schwarzRadialProfileReal f r) ^ p.toReal ≤
      (∫⁻ y, ENNReal.ofReal (f y) ^ p.toReal).toReal := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤ :=
    fun _ ht ↦ volume_lt_lt_top_of_memLp hf hp0 hptop ht
  have hfin : ∫⁻ y, ENNReal.ofReal (f y) ^ p.toReal ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop hf.eLpNorm_lt_top).ne ?_
    refine lintegral_mono fun y ↦ ENNReal.rpow_le_rpow ?_ hp_pos.le
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self (f y))
  have hmarkov := schwarzRadialProfile_rpow_le_lintegral_rpow_div
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal hp_pos r
  have hvol_ne_zero : unitBallVolume n * ENNReal.ofReal r ^ n ≠ 0 :=
    (ENNReal.mul_pos (unitBallVolume_ne_zero n)
      (pow_ne_zero n (ENNReal.ofReal_pos.mpr hr).ne')).ne'
  have hvol_ne_top : unitBallVolume n * ENNReal.ofReal r ^ n ≠ ⊤ :=
    (ENNReal.mul_lt_top (unitBallVolume_lt_top n)
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)).ne
  have hmul : unitBallVolume n * ENNReal.ofReal r ^ n *
      schwarzRadialProfile (fun y ↦ ENNReal.ofReal (f y)) r ^ p.toReal ≤
      ∫⁻ y, ENNReal.ofReal (f y) ^ p.toReal := by
    rw [mul_comm]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hvol_ne_zero) (Or.inl hvol_ne_top)).mp hmarkov
  have htoReal := ENNReal.toReal_mono hfin hmul
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← ofReal_schwarzRadialProfileReal_of_pos hf.aestronglyMeasurable.aemeasurable hdist hr,
    ← ENNReal.ofReal_pow hr.le, ENNReal.toReal_ofReal (pow_nonneg hr.le n),
    ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (schwarzRadialProfileReal_nonneg f r)] at htoReal

end TauCeti
