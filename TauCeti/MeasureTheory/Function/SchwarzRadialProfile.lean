/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement
public import TauCeti.MeasureTheory.Measure.Lebesgue.PrekopaLeindler

/-!
# Radial Profile of Schwarz Rearrangement, Lipschitz Preservation, and Perspective Calculus

This file develops the real-valued radial profile of the Schwarz rearrangement on
`EuclideanSpace ℝ (Fin n)`, establishes Lipschitz preservation under Schwarz rearrangement via the
Brunn–Minkowski inequality on superlevel sets, and proves the convex perspective monotonicity and
Jensen inequalities underlying the convex-integrand Pólya–Szegő inequality:
1. **Layer-cake quantile, ball-volume characterization, and real-valued radial profile**:
   `layerCakeQuantile μ f v = sSup {t > 0 | v < μ {y | t < f y}}`, its identification with
   `schwarzRadialProfile f r` at `v = volume (Metric.ball 0 r)`, Markov bounds, and the real
   profile `schwarzRadialProfileReal f r = (schwarzRadialProfile (ENNReal.ofReal ∘ f) r).toReal`
   with its Galois connection to `schwarzRadius`.
2. **Superlevel thickening inclusions and Lipschitz preservation under Schwarz rearrangement**:
   Minkowski sum and `Metric.thickening` inclusions for superlevel sets of `K`-Lipschitz functions,
   the Brunn–Minkowski inequality for `schwarzRadius`, and `K`-Lipschitz continuity of
   `schwarzRadialProfileReal h` on `ℝ` and `fun x ↦ schwarzRadialProfileReal h ‖x‖` on
   `EuclideanSpace ℝ (Fin n)`.
3. **Convex perspective calculus (`polyaSzegoPerspective`)**:
   Monotonicity in `s > 0` and `P ≥ 0`, convexity, subadditivity, and the level-set Jensen /
   Pólya–Szegő inequality `polyaSzegoPerspective Φ sStar PStar ≤ ∫ x in A, Φ (g x) ∂μ`.
-/

public section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Pointwise

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

/-! ### Layer-cake quantile and ball-volume characterization of `schwarzRadialProfile` -/

/-- **Layer-cake quantile (decreasing rearrangement on `[0, ∞)`)** of `f : α → ℝ≥0∞` with respect
to a measure `μ`: `layerCakeQuantile μ f v = sSup {t : ℝ≥0∞ | 0 < t ∧ v < μ {y | t < f y}}`. -/
def layerCakeQuantile (μ : Measure α) (f : α → ℝ≥0∞) (v : ℝ≥0∞) : ℝ≥0∞ :=
  sSup {t : ℝ≥0∞ | 0 < t ∧ v < μ {y | t < f y}}
/-- Unrestricted `sSup` characterization of `layerCakeQuantile`. -/
theorem layerCakeQuantile_eq_sSup (μ : Measure α) (f : α → ℝ≥0∞) (v : ℝ≥0∞) :
    layerCakeQuantile μ f v = sSup {t : ℝ≥0∞ | v < μ {y | t < f y}} := by
  refine le_antisymm (sSup_le_sSup fun _ ht ↦ ht.2) (sSup_le fun t ht ↦ ?_)
  rcases eq_or_ne t 0 with rfl | ht0
  · exact bot_le
  · exact le_sSup ⟨pos_iff_ne_zero.mpr ht0, ht⟩
/-- `layerCakeQuantile μ f` is antitone in the volume parameter `v`. -/
theorem antitone_layerCakeQuantile (μ : Measure α) (f : α → ℝ≥0∞) :
    Antitone (layerCakeQuantile μ f) :=
  fun _ _ hv ↦ sSup_le_sSup fun _ ht ↦ ⟨ht.1, hv.trans_lt ht.2⟩
/-- Pointwise a.e. inequality of functions implies inequality of `layerCakeQuantile`. -/
theorem layerCakeQuantile_mono_ae {μ : Measure α} {f g : α → ℝ≥0∞} (h : f ≤ᵐ[μ] g) :
    layerCakeQuantile μ f ≤ layerCakeQuantile μ g := by
  intro v; refine sSup_le_sSup fun t ht ↦ ⟨ht.1, ht.2.trans_le (measure_mono_ae ?_)⟩
  filter_upwards [h] with y hy hyf using hyf.trans_le hy
/-- Markov inequality for strict superlevel sets: `t * μ {y | t < f y} ≤ ∫⁻ y, f y ∂μ`. -/
theorem mul_measure_lt_le_lintegral {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (t : ℝ≥0∞) : t * μ {y | t < f y} ≤ ∫⁻ y, f y ∂μ := by
  have hsub : {y | t < f y} ⊆ {y | t ≤ f y} := fun _ (hy : t < f _) ↦ hy.le
  exact (mul_le_mul_right (measure_mono hsub) t).trans (mul_meas_ge_le_lintegral₀ hf t)
/-- Markov product bound for `layerCakeQuantile`: `v * layerCakeQuantile μ f v ≤ ∫⁻ y, f y ∂μ`. -/
theorem mul_layerCakeQuantile_le_lintegral {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (v : ℝ≥0∞) : v * layerCakeQuantile μ f v ≤ ∫⁻ y, f y ∂μ := by
  rw [layerCakeQuantile, ENNReal.mul_sSup]; refine iSup_le fun t ↦ iSup_le fun ht ↦ ?_
  calc v * t ≤ μ {y | t < f y} * t := mul_le_mul_left ht.2.le t
    _ = t * μ {y | t < f y} := mul_comm _ _
    _ ≤ ∫⁻ y, f y ∂μ := mul_measure_lt_le_lintegral hf t
/-- Markov quotient bound: `layerCakeQuantile μ f v ≤ (∫⁻ y, f y ∂μ) / v`. -/
theorem layerCakeQuantile_le_lintegral_div {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (v : ℝ≥0∞) : layerCakeQuantile μ f v ≤ (∫⁻ y, f y ∂μ) / v := by
  refine sSup_le fun t ht ↦ ?_; have hvt : v ≠ ⊤ := ne_top_of_lt ht.2
  have hmul : t * v ≤ ∫⁻ y, f y ∂μ :=
    (mul_le_mul_right ht.2.le t).trans (mul_measure_lt_le_lintegral hf t)
  have hint0 : ∫⁻ y, f y ∂μ ≠ 0 :=
    ((ENNReal.mul_pos ht.1.ne' (zero_le.trans_lt ht.2).ne').trans_le
      (mul_measure_lt_le_lintegral hf t)).ne'
  exact (ENNReal.le_div_iff_mul_le (Or.inr hint0) (Or.inl hvt)).mpr hmul
/-- If `∫⁻ y, f y ∂μ < ⊤` and `0 < v`, then `layerCakeQuantile μ f v < ⊤`. -/
theorem layerCakeQuantile_lt_top {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hfin : ∫⁻ y, f y ∂μ ≠ ⊤) {v : ℝ≥0∞} (hv : 0 < v) :
    layerCakeQuantile μ f v < ⊤ :=
  (layerCakeQuantile_le_lintegral_div hf v).trans_lt (ENNReal.div_lt_top hfin hv.ne')
/-- For `r ≤ 0`, `schwarzRadialProfile f r = schwarzRadialProfile f 0`. -/
theorem schwarzRadialProfile_of_nonpos
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) {r : ℝ} (hr : r ≤ 0) :
    schwarzRadialProfile f r = schwarzRadialProfile f 0 := by
  rw [schwarzRadialProfile_eq_sSup, schwarzRadialProfile_eq_sSup, ENNReal.ofReal_of_nonpos hr,
    ENNReal.ofReal_zero]
/-- Explicit volume formula: `distributionFunction f t = volume {y | t < f y}`. -/
@[simp] theorem distributionFunction_eq_volume [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (t : ℝ≥0∞) :
    distributionFunction f t = volume {y | t < f y} := by
  have hiff (r : ℝ) : unitBallVolume n * ENNReal.ofReal r ^ n < distributionFunction f t ↔
      unitBallVolume n * ENNReal.ofReal r ^ n < volume {y | t < f y} := by
    set x : EuclideanSpace ℝ (Fin n) := max r 0 • EuclideanSpace.single 0 1
    have hnorm : ‖x‖ = max r 0 := by simp [x, norm_smul, Real.norm_of_nonneg (le_max_right r 0)]
    have henorm : ‖x‖ₑ = ENNReal.ofReal r := by
      rw [← ofReal_norm, hnorm]; rcases le_or_gt r 0 with hr | hr
      · rw [max_eq_right hr, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hr]
      · rw [max_eq_left hr.le]
    have hprof : schwarzRadialProfile f ‖x‖ = schwarzRadialProfile f r := by
      rw [hnorm]; rcases le_or_gt r 0 with hr | hr
      · rw [max_eq_right hr, schwarzRadialProfile_of_nonpos f hr]
      · rw [max_eq_left hr.le]
    rw [← lt_schwarzRadialProfile_iff, ← hprof, ← schwarzRearrangement_apply,
      lt_schwarzRearrangement_iff, mem_schwarzSymmetrization, henorm]
  have hlt_iff (v : ℝ≥0∞) (hv : v ≠ ⊤) :
      v < distributionFunction f t ↔ v < volume {y | t < f y} := by
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have hdiv_ne_top : v / unitBallVolume n ≠ ⊤ := ENNReal.div_ne_top hv (unitBallVolume_ne_zero n)
    set r : ℝ := (v / unitBallVolume n).toReal ^ (1 / (n : ℝ))
    have hr_nn : 0 ≤ r := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hvr : unitBallVolume n * ENNReal.ofReal r ^ n = v := by
      rw [← ENNReal.ofReal_pow hr_nn, ← Real.rpow_natCast,
        ← Real.rpow_mul ENNReal.toReal_nonneg, one_div_mul_cancel hn, Real.rpow_one,
        ENNReal.ofReal_toReal hdiv_ne_top, mul_comm,
        ENNReal.div_mul_cancel (unitBallVolume_ne_zero n) (unitBallVolume_ne_top n)]
    rw [← hvr, hiff r]
  apply le_antisymm
  · by_contra! hlt; exact ((hlt_iff _ (ne_top_of_lt hlt)).mp hlt).false
  · by_contra! hlt; exact ((hlt_iff _ (ne_top_of_lt hlt)).mpr hlt).false
/-- `schwarzRadialProfile f r` is `layerCakeQuantile volume f` at `unitBallVolume n * r ^ n`. -/
theorem schwarzRadialProfile_eq_layerCakeQuantile [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (r : ℝ) : schwarzRadialProfile f r =
      layerCakeQuantile volume f (unitBallVolume n * ENNReal.ofReal r ^ n) := by
  rw [schwarzRadialProfile_eq_sSup, layerCakeQuantile_eq_sSup]
  simp only [distributionFunction_eq_volume]
/-- For `0 ≤ r`, `schwarzRadialProfile f r` is `layerCakeQuantile volume f` at
`volume (Metric.ball 0 r)`. -/
theorem schwarzRadialProfile_eq_layerCakeQuantile_volume_ball [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) {r : ℝ} (hr : 0 ≤ r) : schwarzRadialProfile f r =
      layerCakeQuantile volume f (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)) := by
  rw [schwarzRadialProfile_eq_layerCakeQuantile, volume_ball_euclideanSpace 0 hr]
/-- For `0 ≤ r`, `schwarzRadialProfile f r = sSup {t | volume (Metric.ball 0 r) < μ_f(t)}`. -/
theorem schwarzRadialProfile_eq_sSup_volume_ball [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) {r : ℝ} (hr : 0 ≤ r) : schwarzRadialProfile f r =
      sSup {t : ℝ≥0∞ |
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) < distributionFunction f t} := by
  rw [schwarzRadialProfile_eq_sSup, volume_ball_euclideanSpace 0 hr]
/-- Markov product inequality: `volume (Metric.ball 0 r) * schwarzRadialProfile f r ≤ ∫⁻ y, f y`. -/
theorem volume_ball_mul_schwarzRadialProfile_le_lintegral [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) * schwarzRadialProfile f r ≤
      ∫⁻ y, f y := by
  rw [schwarzRadialProfile_eq_layerCakeQuantile_volume_ball f hr]
  exact mul_layerCakeQuantile_le_lintegral hf _

/-! ### Real-valued radial profile `schwarzRadialProfileReal` and radius Galois connection -/

/-- **Real-valued radial profile** of `f : EuclideanSpace ℝ (Fin n) → ℝ`:
`schwarzRadialProfileReal f r = (schwarzRadialProfile (fun y ↦ ENNReal.ofReal (f y)) r).toReal`. -/
def schwarzRadialProfileReal (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) : ℝ :=
  (schwarzRadialProfile (fun y ↦ ENNReal.ofReal (f y)) r).toReal
/-- Alias for `schwarzRadialProfileReal`. -/
abbrev realSchwarzRadialProfile (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) : ℝ :=
  schwarzRadialProfileReal f r
/-- `schwarzRadialProfileReal f` is nonnegative everywhere. -/
theorem schwarzRadialProfileReal_nonneg (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) :
    0 ≤ schwarzRadialProfileReal f r := ENNReal.toReal_nonneg
/-- `schwarzRadialProfileReal f` is Borel measurable. -/
@[fun_prop] theorem measurable_schwarzRadialProfileReal (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    Measurable (schwarzRadialProfileReal f) :=
  (measurable_schwarzRadialProfile _).ennreal_toReal
/-- Almost everywhere equal real-valued functions have identical real radial profiles. -/
theorem schwarzRadialProfileReal_congr_ae {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : f =ᵐ[volume] g) : schwarzRadialProfileReal f = schwarzRadialProfileReal g := by
  have h' : (fun y ↦ ENNReal.ofReal (f y)) =ᵐ[volume] fun y ↦ ENNReal.ofReal (g y) :=
    h.fun_comp ENNReal.ofReal
  ext r; simp only [schwarzRadialProfileReal, schwarzRadialProfile_congr_ae h']
/-- For `r ≤ 0`, `schwarzRadialProfileReal f r = schwarzRadialProfileReal f 0`. -/
theorem schwarzRadialProfileReal_of_nonpos
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {r : ℝ} (hr : r ≤ 0) :
    schwarzRadialProfileReal f r = schwarzRadialProfileReal f 0 := by
  simp only [schwarzRadialProfileReal, schwarzRadialProfile_of_nonpos _ hr]
/-- Under finite superlevel volumes for `t > 0`, `schwarzRadialProfile (ofReal ∘ f) r < ⊤` for
`r > 0`. -/
theorem schwarzRadialProfile_ofReal_lt_top_of_pos [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) {r : ℝ} (hr : 0 < r) :
    schwarzRadialProfile (fun y ↦ ENNReal.ofReal (f y)) r < ⊤ := by
  refine schwarzRadialProfile_lt_top_of_distributionFunction_lt_top hf.ennreal_ofReal ?_ (by simp)
    hr
  intro t ht; rcases eq_or_ne t ⊤ with rfl | httop
  · simp
  · have ht_pos : 0 < t.toReal := ENNReal.toReal_pos ht.ne' httop
    have hset : {y | t < ENNReal.ofReal (f y)} = {y | t.toReal < f y} := by
      ext y; exact ENNReal.lt_ofReal_iff_toReal_lt httop
    simpa [hset] using hdist t.toReal ht_pos
/-- For `x ≠ 0`, `schwarzRearrangementReal f x = schwarzRadialProfileReal f ‖x‖`. -/
theorem schwarzRearrangementReal_eq_schwarzRadialProfileReal_norm_of_ne_zero
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    schwarzRearrangementReal f x = schwarzRadialProfileReal f ‖x‖ := by
  have h := congrArg ENNReal.toReal (ofReal_schwarzRearrangementReal_of_ne_zero hf hdist hx)
  rwa [ENNReal.toReal_ofReal (schwarzRearrangementReal_nonneg f x), schwarzRearrangement_apply] at h
/-- `schwarzRearrangementReal f =ᵐ[volume] fun x ↦ schwarzRadialProfileReal f ‖x‖`. -/
theorem schwarzRearrangementReal_ae_eq_schwarzRadialProfileReal_norm [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) :
    schwarzRearrangementReal f =ᵐ[volume] fun x ↦ schwarzRadialProfileReal f ‖x‖ := by
  have h0 : volume ({0} : Set (EuclideanSpace ℝ (Fin n))) = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr h0] with x hx
  exact schwarzRearrangementReal_eq_schwarzRadialProfileReal_norm_of_ne_zero hf hdist hx
/-- For `r > 0`, `ENNReal.ofReal (schwarzRadialProfileReal f r)` recovers `schwarzRadialProfile`. -/
theorem ofReal_schwarzRadialProfileReal_of_pos [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (schwarzRadialProfileReal f r) =
      schwarzRadialProfile (fun y ↦ ENNReal.ofReal (f y)) r :=
  ENNReal.ofReal_toReal (schwarzRadialProfile_ofReal_lt_top_of_pos hf hdist hr).ne
/-- `schwarzRadialProfileReal f` is antitone on `Ioi 0` when `f` has finite superlevel volumes. -/
theorem antitoneOn_schwarzRadialProfileReal_Ioi [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) :
    AntitoneOn (schwarzRadialProfileReal f) (Ioi 0) := by
  intro r₁ hr₁ r₂ _ hrle
  refine ENNReal.toReal_mono (schwarzRadialProfile_ofReal_lt_top_of_pos hf hdist hr₁).ne ?_
  exact antitone_schwarzRadialProfile _ hrle
/-- Pointwise a.e. inequality `f ≤ᵐ[volume] g` implies `schwarzRadialProfileReal f r ≤
schwarzRadialProfileReal g r` for `r > 0`. -/
theorem schwarzRadialProfileReal_mono_ae [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : AEMeasurable g volume)
    (hfg : f ≤ᵐ[volume] g) (hg_dist : ∀ t : ℝ, 0 < t → volume {y | t < g y} < ⊤)
    {r : ℝ} (hr : 0 < r) : schwarzRadialProfileReal f r ≤ schwarzRadialProfileReal g r := by
  refine ENNReal.toReal_mono (schwarzRadialProfile_ofReal_lt_top_of_pos hg hg_dist hr).ne ?_
  exact schwarzRadialProfile_mono_ae (hfg.mono fun _ hy ↦ ENNReal.ofReal_le_ofReal hy) r
/-- Strict monotonicity of `r ↦ unitBallVolume n * ENNReal.ofReal r ^ n` on `[0, ∞)`. -/
theorem lt_iff_unitBallVolume_mul_ofReal_pow_lt (n : ℕ) [NeZero n] {a b : ℝ} (ha : 0 ≤ a) :
    a < b ↔ unitBallVolume n * ENNReal.ofReal a ^ n < unitBallVolume n * ENNReal.ofReal b ^ n := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hmul : unitBallVolume n * ENNReal.ofReal a ^ n <
      unitBallVolume n * ENNReal.ofReal b ^ n ↔
      ENNReal.ofReal a ^ n < ENNReal.ofReal b ^ n := by
    rw [← not_le, ← not_le,
      ENNReal.mul_le_mul_iff_right (unitBallVolume_ne_zero n) (unitBallVolume_ne_top n)]
  rw [hmul, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ENNReal.rpow_lt_rpow_iff hn_pos,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha]
/-- For `volume E ≠ ⊤` and `r ≥ 0`, `r < schwarzRadius E ↔ unitBallVolume n * r ^ n < volume E`. -/
theorem lt_schwarzRadius_iff [NeZero n] {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : volume E ≠ ⊤) {r : ℝ} (hr : 0 ≤ r) :
    r < schwarzRadius E ↔ unitBallVolume n * ENNReal.ofReal r ^ n < volume E := by
  rw [← ofReal_schwarzRadius_pow hE, lt_iff_unitBallVolume_mul_ofReal_pow_lt n hr]
/-- For `volume E ≠ ⊤` and `r ≥ 0`, `schwarzRadius E ≤ r ↔ volume E ≤ unitBallVolume n * r ^ n`. -/
theorem schwarzRadius_le_iff [NeZero n] {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : volume E ≠ ⊤) {r : ℝ} (hr : 0 ≤ r) :
    schwarzRadius E ≤ r ↔ volume E ≤ unitBallVolume n * ENNReal.ofReal r ^ n := by
  rw [← not_lt, lt_schwarzRadius_iff hE hr, not_lt]
/-- The Schwarz radius of the empty set is `0`. -/
@[simp] theorem schwarzRadius_empty [NeZero n] :
    schwarzRadius (∅ : Set (EuclideanSpace ℝ (Fin n))) = 0 := by
  refine le_antisymm ?_ (schwarzRadius_nonneg ∅); rw [schwarzRadius_le_iff (by simp) le_rfl]; simp
/-- The Schwarz radius of a centered ball `Metric.ball 0 r` (`r ≥ 0`) is `r`. -/
@[simp] theorem schwarzRadius_ball [NeZero n] {r : ℝ} (hr : 0 ≤ r) :
    schwarzRadius (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) = r := by
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ≠ ⊤ := measure_ball_lt_top.ne
  refine le_antisymm ?_ ?_
  · rw [schwarzRadius_le_iff hfin hr, volume_ball_euclideanSpace 0 hr]
  · rw [← not_lt, lt_iff_unitBallVolume_mul_ofReal_pow_lt n (schwarzRadius_nonneg _),
      ofReal_schwarzRadius_pow hfin, volume_ball_euclideanSpace 0 hr]
    exact lt_irrefl _
/-- Monotonicity of `schwarzRadius` under set inclusion when the larger set has finite volume. -/
theorem schwarzRadius_mono [NeZero n] {E F : Set (EuclideanSpace ℝ (Fin n))}
    (hEF : E ⊆ F) (hF : volume F ≠ ⊤) : schwarzRadius E ≤ schwarzRadius F := by
  have hE : volume E ≠ ⊤ := ne_top_of_le_ne_top hF (measure_mono hEF)
  rw [schwarzRadius_le_iff hE (schwarzRadius_nonneg F), ofReal_schwarzRadius_pow hF]
  exact measure_mono hEF
/-- For a finite-volume set `E`, `0 < schwarzRadius E` if and only if `0 < volume E`. -/
theorem schwarzRadius_pos_iff [NeZero n] {E : Set (EuclideanSpace ℝ (Fin n))} (hE : volume E ≠ ⊤) :
    0 < schwarzRadius E ↔ 0 < volume E := by
  rw [lt_schwarzRadius_iff hE le_rfl, ENNReal.ofReal_zero, zero_pow (NeZero.ne n), mul_zero]
/-- Expressing `(volume E) ^ (1 / (n : ℝ))` in terms of `schwarzRadius E` for `volume E ≠ ⊤`. -/
theorem volume_rpow_inv_eq_mul_ofReal_schwarzRadius [NeZero n]
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : volume E ≠ ⊤) : volume E ^ (1 / (n : ℝ)) =
      unitBallVolume n ^ (1 / (n : ℝ)) * ENNReal.ofReal (schwarzRadius E) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [← ofReal_schwarzRadius_pow hE, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hn, ENNReal.rpow_one]
/-- **Galois connection (`<`) between `schwarzRadialProfileReal` and `schwarzRadius`**. -/
theorem lt_schwarzRadialProfileReal_iff_lt_schwarzRadius [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {y | s < f y} < ⊤)
    {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (ht_fin : volume {y | t < f y} ≠ ⊤) :
    t < schwarzRadialProfileReal f r ↔ r < schwarzRadius {y | t < f y} := by
  rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht,
    ofReal_schwarzRadialProfileReal_of_pos hf hdist hr, lt_schwarzRadialProfile_iff,
    lt_schwarzRadius_iff ht_fin hr.le]
  have hset : {y | ENNReal.ofReal t < ENNReal.ofReal (f y)} = {y | t < f y} := by
    ext y; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht
  simp [hset]
/-- **Galois connection (`≤`) between `schwarzRadialProfileReal` and `schwarzRadius`**. -/
theorem schwarzRadialProfileReal_le_iff_schwarzRadius_le [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {y | s < f y} < ⊤)
    {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (ht_fin : volume {y | t < f y} ≠ ⊤) :
    schwarzRadialProfileReal f r ≤ t ↔ schwarzRadius {y | t < f y} ≤ r := by
  rw [← not_lt, lt_schwarzRadialProfileReal_iff_lt_schwarzRadius hf hdist hr ht ht_fin, not_lt]

/-! ### Superlevel thickening inclusions and Lipschitz preservation via Brunn–Minkowski -/

/-- **Strict superlevel closed-ball Minkowski sum inclusion**: for `K`-Lipschitz `h : E → ℝ`
(`K > 0`), `{x | t₂ < h x} + Metric.closedBall 0 ((t₂ - t₁) / K) ⊆ {x | t₁ < h x}`. -/
theorem superlevel_add_closedBall_subset_superlevel
    {E : Type*} [SeminormedAddCommGroup E] {h : E → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hK : 0 < (K : ℝ)) (t₁ t₂ : ℝ) :
    {x : E | t₂ < h x} + Metric.closedBall (0 : E) ((t₂ - t₁) / K) ⊆ {x : E | t₁ < h x} := by
  rintro _ ⟨x, hx : t₂ < h x, z, hz, rfl⟩; rw [mem_closedBall_zero_iff] at hz
  have hdist : h x - h (x + z) ≤ (K : ℝ) * ‖z‖ := by
    calc h x - h (x + z) ≤ |h x - h (x + z)| := le_abs_self _
      _ = dist (h x) (h (x + z)) := (Real.dist_eq _ _).symm
      _ ≤ (K : ℝ) * dist x (x + z) := hh.dist_le_mul x (x + z)
      _ = (K : ℝ) * ‖z‖ := by simp [dist_eq_norm]
  have hKz : (K : ℝ) * ‖z‖ ≤ t₂ - t₁ :=
    (mul_le_mul_of_nonneg_left hz hK.le).trans_eq (mul_div_cancel₀ (t₂ - t₁) hK.ne')
  change t₁ < h (x + z); linarith
/-- **Strict superlevel open-ball Minkowski sum inclusion**: for `K`-Lipschitz `h : E → ℝ`
(`K > 0`), `{x | t₂ < h x} + Metric.ball 0 ((t₂ - t₁) / K) ⊆ {x | t₁ < h x}`. -/
theorem superlevel_add_ball_subset_superlevel
    {E : Type*} [SeminormedAddCommGroup E] {h : E → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hK : 0 < (K : ℝ)) (t₁ t₂ : ℝ) :
    {x : E | t₂ < h x} + Metric.ball (0 : E) ((t₂ - t₁) / K) ⊆ {x : E | t₁ < h x} :=
  (add_subset_add Subset.rfl ball_subset_closedBall).trans
    (superlevel_add_closedBall_subset_superlevel hh hK t₁ t₂)
/-- **Closed superlevel closed-ball Minkowski sum inclusion**: for `K`-Lipschitz `h : E → ℝ`
(`K > 0`), `{x | t₂ ≤ h x} + Metric.closedBall 0 ((t₂ - t₁) / K) ⊆ {x | t₁ ≤ h x}`. -/
theorem superlevel_ge_add_closedBall_subset_superlevel_ge
    {E : Type*} [SeminormedAddCommGroup E] {h : E → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hK : 0 < (K : ℝ)) (t₁ t₂ : ℝ) :
    {x : E | t₂ ≤ h x} + Metric.closedBall (0 : E) ((t₂ - t₁) / K) ⊆ {x : E | t₁ ≤ h x} := by
  rintro _ ⟨x, hx : t₂ ≤ h x, z, hz, rfl⟩; rw [mem_closedBall_zero_iff] at hz
  have hdist : h x - h (x + z) ≤ (K : ℝ) * ‖z‖ := by
    calc h x - h (x + z) ≤ |h x - h (x + z)| := le_abs_self _
      _ = dist (h x) (h (x + z)) := (Real.dist_eq _ _).symm
      _ ≤ (K : ℝ) * dist x (x + z) := hh.dist_le_mul x (x + z)
      _ = (K : ℝ) * ‖z‖ := by simp [dist_eq_norm]
  have hKz : (K : ℝ) * ‖z‖ ≤ t₂ - t₁ :=
    (mul_le_mul_of_nonneg_left hz hK.le).trans_eq (mul_div_cancel₀ (t₂ - t₁) hK.ne')
  change t₁ ≤ h (x + z); linarith
/-- **Metric thickening inclusion for superlevel sets**: for `K`-Lipschitz `h : E → ℝ` (`K > 0`),
`Metric.thickening ((t₂ - t₁) / K) {x | t₂ < h x} ⊆ {x | t₁ < h x}`. -/
theorem thickening_superlevel_subset_superlevel
    {E : Type*} [SeminormedAddCommGroup E] {h : E → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hK : 0 < (K : ℝ)) (t₁ t₂ : ℝ) :
    Metric.thickening ((t₂ - t₁) / K) {x : E | t₂ < h x} ⊆ {x : E | t₁ < h x} := by
  intro y hy; rw [mem_thickening_iff] at hy; obtain ⟨x, hx, hyx⟩ := hy
  refine superlevel_add_ball_subset_superlevel hh hK t₁ t₂ ⟨x, hx, y - x, ?_, add_sub_cancel x y⟩
  rwa [mem_ball_zero_iff, ← dist_eq_norm]
/-- **Brunn–Minkowski inequality for `schwarzRadius`**: if `A, B ⊆ EuclideanSpace ℝ (Fin n)` are
nonempty null-measurable sets and `A + B ⊆ C` with `volume C ≠ ⊤`, then
`schwarzRadius A + schwarzRadius B ≤ schwarzRadius C`. -/
theorem schwarzRadius_add_le [NeZero n] {A B C : Set (EuclideanSpace ℝ (Fin n))}
    (hAn : A.Nonempty) (hAm : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hBm : NullMeasurableSet B volume)
    (hABC : A + B ⊆ C) (hC : volume C ≠ ⊤) :
    schwarzRadius A + schwarzRadius B ≤ schwarzRadius C := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn_pos : (0 : ℝ) < 1 / n := one_div_pos.mpr (Nat.cast_pos.mpr hn1)
  obtain ⟨b₀, hb₀⟩ := hBn; obtain ⟨a₀, ha₀⟩ := hAn
  have hA_fin : volume A ≠ ⊤ := by
    refine ne_top_of_le_ne_top hC ?_; calc volume A = volume (A + {b₀}) := by simp
      _ ≤ volume (A + B) := measure_mono (add_subset_add_left (singleton_subset_iff.mpr hb₀))
      _ ≤ volume C := measure_mono hABC
  have hB_fin : volume B ≠ ⊤ := by
    refine ne_top_of_le_ne_top hC ?_; calc volume B = volume ({a₀} + B) := by simp
      _ ≤ volume (A + B) := measure_mono (add_subset_add_right (singleton_subset_iff.mpr ha₀))
      _ ≤ volume C := measure_mono hABC
  have hbm := (EuclideanSpace.volume_add_rpow_inv_ge hn1 ⟨a₀, ha₀⟩ hAm ⟨b₀, hb₀⟩ hBm).trans
    (ENNReal.rpow_le_rpow (measure_mono hABC) hn_pos.le)
  rw [volume_rpow_inv_eq_mul_ofReal_schwarzRadius hA_fin,
    volume_rpow_inv_eq_mul_ofReal_schwarzRadius hB_fin,
    volume_rpow_inv_eq_mul_ofReal_schwarzRadius hC, ← mul_add,
    ← ENNReal.ofReal_add (schwarzRadius_nonneg A) (schwarzRadius_nonneg B)] at hbm
  have hω0 : unitBallVolume n ^ (1 / (n : ℝ)) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr (unitBallVolume_ne_zero n))
      (unitBallVolume_ne_top n)).ne'
  have hωtop : unitBallVolume n ^ (1 / (n : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hn_pos.le (unitBallVolume_ne_top n)
  rwa [ENNReal.mul_le_mul_iff_right hω0 hωtop,
    ENNReal.ofReal_le_ofReal_iff (schwarzRadius_nonneg C)] at hbm
/-- **Superlevel Schwarz-radius inequality for a `K`-Lipschitz function**: if `t₁ < t₂`,
`0 < volume {y | t₂ < h y}`, and `volume {y | t₁ < h y} ≠ ⊤`, then
`schwarzRadius {y | t₂ < h y} + (t₂ - t₁) / K ≤ schwarzRadius {y | t₁ < h y}`. -/
theorem schwarzRadius_superlevel_add_le [NeZero n] {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hK : 0 < (K : ℝ)) {t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (ht₂ : 0 < volume {y : EuclideanSpace ℝ (Fin n) | t₂ < h y})
    (ht₁ : volume {y : EuclideanSpace ℝ (Fin n) | t₁ < h y} ≠ ⊤) :
    schwarzRadius {y | t₂ < h y} + (t₂ - t₁) / K ≤ schwarzRadius {y | t₁ < h y} := by
  have hr : 0 < (t₂ - t₁) / K := div_pos (sub_pos.mpr ht) hK
  have hle := schwarzRadius_add_le (nonempty_of_measure_ne_zero ht₂.ne')
    (isOpen_lt continuous_const hh.continuous).measurableSet.nullMeasurableSet
    (nonempty_ball.mpr hr) isOpen_ball.measurableSet.nullMeasurableSet
    (superlevel_add_ball_subset_superlevel hh hK t₁ t₂) ht₁
  rwa [schwarzRadius_ball hr.le] at hle
/-- **Fundamental `ℝ≥0∞` radial-profile difference bound for Lipschitz functions**:
for `0 ≤ r₁ ≤ r₂` with `0 < r₂`, `schwarzRadialProfile (fun y ↦ ENNReal.ofReal (h y)) r₁ ≤
ENNReal.ofReal (schwarzRadialProfileReal h r₂ + K * (r₂ - r₁))`. -/
theorem schwarzRadialProfile_ofReal_le_of_lipschitzWith [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤)
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hrle : r₁ ≤ r₂) (hr₂ : 0 < r₂) :
    schwarzRadialProfile (fun y ↦ ENNReal.ofReal (h y)) r₁ ≤
      ENNReal.ofReal (schwarzRadialProfileReal h r₂ + (K : ℝ) * (r₂ - r₁)) := by
  have hf_meas : AEMeasurable h volume := hh.continuous.measurable.aemeasurable
  rcases eq_or_lt_of_le (NNReal.coe_nonneg K) with hK0 | hK
  · have hK_eq : K = 0 := NNReal.eq hK0.symm
    subst hK_eq; simp only [NNReal.coe_zero, zero_mul, add_zero]
    rw [ofReal_schwarzRadialProfileReal_of_pos hf_meas hdist hr₂, schwarzRadialProfile_eq_sSup]
    refine sSup_le fun t (ht : unitBallVolume n * ENNReal.ofReal r₁ ^ n < _) ↦ ?_
    rcases eq_or_ne t 0 with rfl | ht0
    · exact bot_le
    have hconst (y : EuclideanSpace ℝ (Fin n)) : h y = h 0 := by
      simpa [sub_eq_zero] using hh.dist_le_mul y 0
    have hpos_vol : 0 < volume {y : EuclideanSpace ℝ (Fin n) | t < ENNReal.ofReal (h y)} := by
      simpa using zero_le.trans_lt ht
    obtain ⟨y₀, hy₀⟩ := nonempty_of_measure_ne_zero hpos_vol.ne'
    have hlt_top : t ≠ ⊤ := by rintro rfl; simp at ht
    have hpos : 0 < t.toReal := ENNReal.toReal_pos ht0 hlt_top
    have hset_real : {y : EuclideanSpace ℝ (Fin n) | t.toReal < h y} = univ := by
      ext y
      simp only [mem_ofPred_eq, mem_univ, iff_true, ← ENNReal.lt_ofReal_iff_toReal_lt hlt_top]
      simpa [hconst y, hconst y₀] using hy₀
    have hfin := hdist t.toReal hpos
    rw [hset_real, measure_univ_of_isAddLeftInvariant volume] at hfin; exact absurd rfl hfin.ne
  · have hpos_step {s : ℝ} (hs_pos : 0 < s) (hs_le : s ≤ r₂) :
        schwarzRadialProfile (fun y ↦ ENNReal.ofReal (h y)) s ≤
          ENNReal.ofReal (schwarzRadialProfileReal h r₂ + (K : ℝ) * (r₂ - s)) := by
      rw [schwarzRadialProfile_eq_sSup]
      refine sSup_le fun t (ht : unitBallVolume n * ENNReal.ofReal s ^ n < _) ↦ ?_
      rcases eq_or_ne t 0 with rfl | ht0
      · exact bot_le
      have httop : t ≠ ⊤ := by rintro rfl; simp at ht
      set τ₂ := t.toReal with hτ₂_def
      have hτ₂_pos : 0 < τ₂ := ENNReal.toReal_pos ht0 httop
      have hset₂ : {y : EuclideanSpace ℝ (Fin n) | t < ENNReal.ofReal (h y)} = {y | τ₂ < h y} := by
        ext y; exact ENNReal.lt_ofReal_iff_toReal_lt httop
      have hvol₂_lt : unitBallVolume n * ENNReal.ofReal s ^ n < volume {y | τ₂ < h y} := by
        simpa [hset₂] using ht
      have hvol₂_pos : 0 < volume {y | τ₂ < h y} := zero_le.trans_lt hvol₂_lt
      have hvol₂_fin : volume {y | τ₂ < h y} ≠ ⊤ := (hdist τ₂ hτ₂_pos).ne
      have hs_lt_R₂ : s < schwarzRadius {y | τ₂ < h y} :=
        (lt_schwarzRadius_iff hvol₂_fin hs_pos.le).mpr hvol₂_lt
      rw [← ENNReal.ofReal_toReal httop, ← hτ₂_def]; refine ENNReal.ofReal_le_ofReal ?_
      by_contra! hgt; set v₂ := schwarzRadialProfileReal h r₂
      have hv₂_nn : 0 ≤ v₂ := schwarzRadialProfileReal_nonneg h r₂
      set τ₁ := (v₂ + (τ₂ - (K : ℝ) * (r₂ - s))) / 2 with hτ₁_def
      have hτ₁_gt_v₂ : v₂ < τ₁ := by linarith [hτ₁_def]
      have hτ₁_pos : 0 < τ₁ := hv₂_nn.trans_lt hτ₁_gt_v₂
      have hτ₁_lt_τ₂ : τ₁ < τ₂ := by
        have hdiff_nn : 0 ≤ (K : ℝ) * (r₂ - s) := mul_nonneg hK.le (sub_nonneg.mpr hs_le)
        linarith [hτ₁_def]
      have hvol₁_fin : volume {y | τ₁ < h y} ≠ ⊤ := (hdist τ₁ hτ₁_pos).ne
      have hR₁_le : schwarzRadius {y | τ₁ < h y} ≤ r₂ := by
        rw [← schwarzRadialProfileReal_le_iff_schwarzRadius_le hf_meas hdist hr₂ hτ₁_pos.le
          hvol₁_fin]; exact hτ₁_gt_v₂.le
      have hbm := schwarzRadius_superlevel_add_le hh hK hτ₁_lt_τ₂ hvol₂_pos hvol₁_fin
      have hstep : r₂ - s < (τ₂ - τ₁) / (K : ℝ) := by rw [lt_div_iff₀ hK]; nlinarith [hτ₁_def, hgt]
      linarith
    rcases eq_or_lt_of_le hr₁ with rfl | hr₁_pos
    · simp only [sub_zero]; rw [schwarzRadialProfile_eq_sSup]
      refine sSup_le fun t (ht : unitBallVolume n * ENNReal.ofReal 0 ^ n < _) ↦ ?_
      rcases eq_or_ne t 0 with rfl | ht0
      · exact bot_le
      have httop : t ≠ ⊤ := by rintro rfl; simp at ht
      set τ₂ := t.toReal
      have hτ₂_pos : 0 < τ₂ := ENNReal.toReal_pos ht0 httop
      have hset₂ : {y : EuclideanSpace ℝ (Fin n) | t < ENNReal.ofReal (h y)} = {y | τ₂ < h y} := by
        ext y; exact ENNReal.lt_ofReal_iff_toReal_lt httop
      have hvol₂_pos : 0 < volume {y | τ₂ < h y} := by simpa [hset₂] using zero_le.trans_lt ht
      have hvol₂_fin : volume {y | τ₂ < h y} ≠ ⊤ := (hdist τ₂ hτ₂_pos).ne
      have hR₂_pos : 0 < schwarzRadius {y | τ₂ < h y} :=
        (schwarzRadius_pos_iff hvol₂_fin).mpr hvol₂_pos
      set s := min r₂ (schwarzRadius {y | τ₂ < h y}) / 2
      have hs_pos : 0 < s := half_pos (lt_min hr₂ hR₂_pos)
      have hs_le_r₂ : s ≤ r₂ := (half_lt_self (lt_min hr₂ hR₂_pos)).le.trans (min_le_left _ _)
      have hs_lt_R₂ : s < schwarzRadius {y | τ₂ < h y} :=
        (half_lt_self (lt_min hr₂ hR₂_pos)).trans_le (min_le_right _ _)
      have ht_le_s : t ≤ schwarzRadialProfile (fun y ↦ ENNReal.ofReal (h y)) s := by
        rw [schwarzRadialProfile_eq_sSup]; refine le_sSup ?_
        change unitBallVolume n * ENNReal.ofReal s ^ n <
          distributionFunction (fun y ↦ ENNReal.ofReal (h y)) t
        rw [distributionFunction_eq_volume, hset₂, ← lt_schwarzRadius_iff hvol₂_fin hs_pos.le]
        exact hs_lt_R₂
      refine ht_le_s.trans ((hpos_step hs_pos hs_le_r₂).trans (ENNReal.ofReal_le_ofReal ?_))
      nlinarith [hK.le]
    · exact hpos_step hr₁_pos hrle
/-- For any `K`-Lipschitz `h` with finite superlevel volumes,
`schwarzRadialProfile (fun y ↦ ENNReal.ofReal (h y)) r < ⊤` for all `r : ℝ`. -/
theorem schwarzRadialProfile_ofReal_lt_top_of_lipschitzWith [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤) (r : ℝ) :
    schwarzRadialProfile (fun y ↦ ENNReal.ofReal (h y)) r < ⊤ := by
  have h0 : schwarzRadialProfile (fun y ↦ ENNReal.ofReal (h y)) 0 < ⊤ :=
    (schwarzRadialProfile_ofReal_le_of_lipschitzWith hh hdist le_rfl zero_le_one one_pos).trans_lt
      ENNReal.ofReal_lt_top
  rcases le_or_gt r 0 with hr | hr
  · rw [schwarzRadialProfile_of_nonpos _ hr]; exact h0
  · exact (antitone_schwarzRadialProfile _ hr.le).trans_lt h0
/-- For any `K`-Lipschitz `h` with finite superlevel volumes,
`ENNReal.ofReal (schwarzRadialProfileReal h r) = schwarzRadialProfile (ofReal ∘ h) r`. -/
theorem ofReal_schwarzRadialProfileReal_of_lipschitzWith [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤) (r : ℝ) :
    ENNReal.ofReal (schwarzRadialProfileReal h r) =
      schwarzRadialProfile (fun y ↦ ENNReal.ofReal (h y)) r :=
  ENNReal.ofReal_toReal (schwarzRadialProfile_ofReal_lt_top_of_lipschitzWith hh hdist r).ne
/-- `schwarzRadialProfileReal h` is antitone on `ℝ` when `h` is Lipschitz with finite superlevel
volumes. -/
theorem antitone_schwarzRadialProfileReal_of_lipschitzWith [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤) :
    Antitone (schwarzRadialProfileReal h) := by
  intro r₁ r₂ hrle
  refine ENNReal.toReal_mono
    (schwarzRadialProfile_ofReal_lt_top_of_lipschitzWith hh hdist r₁).ne ?_
  exact antitone_schwarzRadialProfile _ hrle
/-- One-sided Lipschitz difference bound: for `r₁ ≤ r₂`,
`schwarzRadialProfileReal h r₁ - schwarzRadialProfileReal h r₂ ≤ K * (r₂ - r₁)`. -/
theorem schwarzRadialProfileReal_sub_le_of_lipschitzWith [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤)
    {r₁ r₂ : ℝ} (hrle : r₁ ≤ r₂) :
    schwarzRadialProfileReal h r₁ - schwarzRadialProfileReal h r₂ ≤ (K : ℝ) * (r₂ - r₁) := by
  have hK_nn : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
  rcases le_or_gt r₂ 0 with hr₂ | hr₂
  · rw [schwarzRadialProfileReal_of_nonpos h (hrle.trans hr₂),
      schwarzRadialProfileReal_of_nonpos h hr₂, sub_self]
    exact mul_nonneg hK_nn (sub_nonneg.mpr hrle)
  · rcases le_or_gt r₁ 0 with hr₁ | hr₁
    · rw [schwarzRadialProfileReal_of_nonpos h hr₁]
      have h0 := schwarzRadialProfile_ofReal_le_of_lipschitzWith hh hdist le_rfl hr₂.le hr₂
      have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h0
      rw [ENNReal.toReal_ofReal (add_nonneg (schwarzRadialProfileReal_nonneg h r₂)
        (mul_nonneg hK_nn (sub_nonneg.mpr hr₂.le)))] at htoReal
      change schwarzRadialProfileReal h 0 ≤
        schwarzRadialProfileReal h r₂ + (K : ℝ) * (r₂ - 0) at htoReal; nlinarith
    · rcases eq_or_lt_of_le hrle with rfl | hlt
      · simp
      · have hle := schwarzRadialProfile_ofReal_le_of_lipschitzWith hh hdist hr₁.le hrle hr₂
        have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
        rw [ENNReal.toReal_ofReal (add_nonneg (schwarzRadialProfileReal_nonneg h r₂)
          (mul_nonneg hK_nn (sub_nonneg.mpr hrle)))] at htoReal
        change schwarzRadialProfileReal h r₁ ≤
          schwarzRadialProfileReal h r₂ + (K : ℝ) * (r₂ - r₁) at htoReal; linarith
/-- **Lipschitz preservation for the radial profile**: if `h : EuclideanSpace ℝ (Fin n) → ℝ` is
`K`-Lipschitz and has finite superlevel volumes for `t > 0`, then `schwarzRadialProfileReal h` is
`K`-Lipschitz on `ℝ`. -/
theorem lipschitzWith_schwarzRadialProfileReal [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤) :
    LipschitzWith K (schwarzRadialProfileReal h) := by
  rw [lipschitzWith_iff_dist_le_mul]; intro r₁ r₂
  have hant := antitone_schwarzRadialProfileReal_of_lipschitzWith hh hdist
  rcases le_total r₁ r₂ with hle | hle
  · rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hant hle)),
      abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    exact schwarzRadialProfileReal_sub_le_of_lipschitzWith hh hdist hle
  · rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hant hle)), neg_sub,
      abs_of_nonneg (sub_nonneg.mpr hle)]
    exact schwarzRadialProfileReal_sub_le_of_lipschitzWith hh hdist hle
/-- **Global `K`-Lipschitz radial representative of `schwarzRearrangementReal h`**:
`fun x ↦ schwarzRadialProfileReal h ‖x‖` is `K`-Lipschitz on `EuclideanSpace ℝ (Fin n)`. -/
theorem lipschitzWith_schwarzRadialProfileReal_comp_norm [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤) :
    LipschitzWith K (fun x : EuclideanSpace ℝ (Fin n) ↦ schwarzRadialProfileReal h ‖x‖) := by
  rw [lipschitzWith_iff_dist_le_mul]; intro x y
  refine ((lipschitzWith_schwarzRadialProfileReal hh hdist).dist_le_mul ‖x‖ ‖y‖).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg K)
  rw [Real.dist_eq, dist_eq_norm]; exact abs_norm_sub_norm_le x y
/-- `schwarzRearrangementReal h` is `K`-Lipschitz on `{0}ᶜ` when `h` is `K`-Lipschitz with finite
superlevel volumes. -/
theorem lipschitzOnWith_schwarzRearrangementReal_compl_singleton_zero [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤) :
    LipschitzOnWith K (schwarzRearrangementReal h) ({0}ᶜ) := by
  have hf_meas : AEMeasurable h volume := hh.continuous.measurable.aemeasurable
  rw [lipschitzOnWith_iff_dist_le_mul]; intro x hx y hy
  rw [schwarzRearrangementReal_eq_schwarzRadialProfileReal_norm_of_ne_zero hf_meas hdist hx,
    schwarzRearrangementReal_eq_schwarzRadialProfileReal_norm_of_ne_zero hf_meas hdist hy]
  exact (lipschitzWith_schwarzRadialProfileReal_comp_norm hh hdist).dist_le_mul x y
/-- **Existence of a global `K`-Lipschitz representative of `schwarzRearrangementReal h`**. -/
theorem exists_lipschitzWith_ae_eq_schwarzRearrangementReal [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hdist : ∀ t : ℝ, 0 < t → volume {y | t < h y} < ⊤) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      LipschitzWith K g ∧ (∀ x ≠ 0, schwarzRearrangementReal h x = g x) ∧
      schwarzRearrangementReal h =ᵐ[volume] g :=
  ⟨fun x ↦ schwarzRadialProfileReal h ‖x‖,
    lipschitzWith_schwarzRadialProfileReal_comp_norm hh hdist,
    fun _ hx ↦ schwarzRearrangementReal_eq_schwarzRadialProfileReal_norm_of_ne_zero
      hh.continuous.measurable.aemeasurable hdist hx,
    schwarzRearrangementReal_ae_eq_schwarzRadialProfileReal_norm
      hh.continuous.measurable.aemeasurable hdist⟩
/-- **Lipschitz preservation for `MemLp` functions** (`0 < p < ⊤`). -/
theorem lipschitzWith_schwarzRadialProfileReal_of_memLp [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0} {p : ℝ≥0∞}
    (hh : LipschitzWith K h) (hp : MemLp h p volume) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) :
    LipschitzWith K (schwarzRadialProfileReal h) :=
  lipschitzWith_schwarzRadialProfileReal hh
    (fun _ ht ↦ volume_lt_lt_top_of_memLp hp hp0 hptop ht)
/-- **Lipschitz preservation for `L¹` integrable functions**. -/
theorem exists_lipschitzWith_ae_eq_schwarzRearrangementReal_of_integrable [NeZero n]
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (hi : Integrable h volume) : ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      LipschitzWith K g ∧ (∀ x ≠ 0, schwarzRearrangementReal h x = g x) ∧
      schwarzRearrangementReal h =ᵐ[volume] g :=
  exists_lipschitzWith_ae_eq_schwarzRearrangementReal hh
    (fun _ ht ↦ volume_lt_lt_top_of_memLp (memLp_one_iff_integrable.mpr hi)
      one_ne_zero ENNReal.one_ne_top ht)

/-! ### Convex perspective calculus (`polyaSzegoPerspective`) for Pólya–Szegő -/

/-- **Pólya–Szegő perspective function** of `Φ : ℝ → ℝ`:
`polyaSzegoPerspective Φ s P = if s ≤ 0 then 0 else s * Φ (P / s)`. -/
def polyaSzegoPerspective (Φ : ℝ → ℝ) (s P : ℝ) : ℝ :=
  if s ≤ 0 then 0 else s * Φ (P / s)
/-- For `s ≤ 0`, `polyaSzegoPerspective Φ s P = 0`. -/
theorem polyaSzegoPerspective_of_nonpos (Φ : ℝ → ℝ) {s : ℝ} (hs : s ≤ 0) (P : ℝ) :
    polyaSzegoPerspective Φ s P = 0 := by simp [polyaSzegoPerspective, hs]
/-- For `0 < s`, `polyaSzegoPerspective Φ s P = s * Φ (P / s)`. -/
theorem polyaSzegoPerspective_of_pos (Φ : ℝ → ℝ) {s : ℝ} (hs : 0 < s) (P : ℝ) :
    polyaSzegoPerspective Φ s P = s * Φ (P / s) := by simp [polyaSzegoPerspective, not_le.mpr hs]
/-- At `s = 0`, `polyaSzegoPerspective Φ 0 P = 0`. -/
@[simp] theorem polyaSzegoPerspective_zero_left (Φ : ℝ → ℝ) (P : ℝ) :
    polyaSzegoPerspective Φ 0 P = 0 := by simp [polyaSzegoPerspective]
/-- At `s = 1`, `polyaSzegoPerspective Φ 1 P = Φ P`. -/
@[simp] theorem polyaSzegoPerspective_one_left (Φ : ℝ → ℝ) (P : ℝ) :
    polyaSzegoPerspective Φ 1 P = Φ P := by simp [polyaSzegoPerspective]
/-- If `Φ 0 = 0`, then `polyaSzegoPerspective Φ s 0 = 0` for all `s : ℝ`. -/
theorem polyaSzegoPerspective_zero_right {Φ : ℝ → ℝ} (hΦ0 : Φ 0 = 0) (s : ℝ) :
    polyaSzegoPerspective Φ s 0 = 0 := by
  by_cases hs : s ≤ 0 <;> simp [polyaSzegoPerspective, hs, hΦ0]
/-- Nonnegativity of `polyaSzegoPerspective Φ s P` when `Φ ≥ 0` on `Ici 0` and `0 ≤ P`. -/
theorem polyaSzegoPerspective_nonneg {Φ : ℝ → ℝ} (hΦ : ∀ x ≥ 0, 0 ≤ Φ x)
    (s : ℝ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ polyaSzegoPerspective Φ s P := by
  by_cases hs : s ≤ 0
  · simp [polyaSzegoPerspective, hs]
  · have hs_pos : 0 < s := not_le.mp hs
    rw [polyaSzegoPerspective_of_pos Φ hs_pos]
    exact mul_nonneg hs_pos.le (hΦ (P / s) (div_nonneg hP hs_pos.le))
/-- Positive `1`-homogeneity of `polyaSzegoPerspective Φ` for `0 < c`. -/
theorem polyaSzegoPerspective_smul (Φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (s P : ℝ) :
    polyaSzegoPerspective Φ (c * s) (c * P) = c * polyaSzegoPerspective Φ s P := by
  by_cases hs : s ≤ 0
  · simp [polyaSzegoPerspective, hs, mul_nonpos_of_nonneg_of_nonpos hc.le hs]
  · have hs_pos : 0 < s := not_le.mp hs
    rw [polyaSzegoPerspective_of_pos Φ (mul_pos hc hs_pos), polyaSzegoPerspective_of_pos Φ hs_pos,
      mul_div_mul_left P s hc.ne', mul_assoc]
/-- **Ray-slope monotonicity for convex functions on `[0, ∞)` with `Φ 0 ≤ 0`**. -/
theorem div_le_div_of_convexOn_of_nonpos_zero {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (hΦ0 : Φ 0 ≤ 0) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Φ u / u ≤ Φ v / v := by
  have hv : 0 < v := hu.trans_le huv; set θ := u / v
  have hθ0 : 0 ≤ θ := div_nonneg hu.le hv.le
  have hθ1 : 0 ≤ 1 - θ := sub_nonneg.mpr ((div_le_one hv).mpr huv)
  have hconv := hΦ.2 (le_rfl : (0 : ℝ) ∈ Ici 0) hv.le hθ1 hθ0 (sub_add_cancel 1 θ)
  have hpoint : (1 - θ) • (0 : ℝ) + θ • v = u := by simp [θ, div_mul_cancel₀ u hv.ne']
  rw [hpoint] at hconv; simp only [θ, smul_eq_mul] at hconv
  have hle : Φ u ≤ (u / v) * Φ v := by nlinarith
  rw [div_le_iff₀ hu]; calc Φ u ≤ (u / v) * Φ v := hle
    _ = Φ v / v * u := by ring
/-- **Monotonicity of `polyaSzegoPerspective Φ s P` in `s > 0`** (`s ↦ s * Φ (P / s)` is
nonincreasing). -/
theorem polyaSzegoPerspective_le_of_le_left {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (hΦ0 : Φ 0 ≤ 0)
    {P : ℝ} (hP : 0 ≤ P) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) :
    polyaSzegoPerspective Φ s₂ P ≤ polyaSzegoPerspective Φ s₁ P := by
  have hs₂ : 0 < s₂ := hs₁.trans_le hs
  rw [polyaSzegoPerspective_of_pos Φ hs₂, polyaSzegoPerspective_of_pos Φ hs₁]
  rcases eq_or_lt_of_le hP with rfl | hP_pos
  · simp only [zero_div]; exact mul_le_mul_of_nonpos_right hs hΦ0
  · have hu : 0 < P / s₂ := div_pos hP_pos hs₂
    have huv : P / s₂ ≤ P / s₁ := div_le_div_of_nonneg_left hP_pos.le hs₁ hs
    have hslope := div_le_div_of_convexOn_of_nonpos_zero hΦ hΦ0 hu huv
    rw [div_div_eq_mul_div, div_div_eq_mul_div] at hslope
    have hmul := mul_le_mul_of_nonneg_right hslope hP_pos.le
    rw [div_mul_cancel₀ _ hP_pos.ne', div_mul_cancel₀ _ hP_pos.ne'] at hmul; linarith
/-- `s ↦ polyaSzegoPerspective Φ s P` is antitone on `Ioi 0`. -/
theorem antitoneOn_polyaSzegoPerspective_left {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (hΦ0 : Φ 0 ≤ 0) {P : ℝ} (hP : 0 ≤ P) :
    AntitoneOn (fun s ↦ polyaSzegoPerspective Φ s P) (Ioi 0) :=
  fun _ hs₁ _ _ hs ↦ polyaSzegoPerspective_le_of_le_left hΦ hΦ0 hP hs₁ hs
/-- **Monotonicity of `polyaSzegoPerspective Φ s P` in `P ≥ 0`** when `MonotoneOn Φ (Ici 0)`. -/
theorem polyaSzegoPerspective_le_of_le_right {Φ : ℝ → ℝ}
    (hΦ : MonotoneOn Φ (Ici (0 : ℝ))) (s : ℝ) {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂) :
    polyaSzegoPerspective Φ s P₁ ≤ polyaSzegoPerspective Φ s P₂ := by
  by_cases hs : s ≤ 0
  · simp [polyaSzegoPerspective, hs]
  · have hs_pos : 0 < s := not_le.mp hs
    rw [polyaSzegoPerspective_of_pos Φ hs_pos, polyaSzegoPerspective_of_pos Φ hs_pos]
    refine mul_le_mul_of_nonneg_left ?_ hs_pos.le
    exact hΦ (div_nonneg hP₁ hs_pos.le) (div_nonneg (hP₁.trans hP) hs_pos.le)
      (div_le_div_of_nonneg_right hP hs_pos.le)
/-- `P ↦ polyaSzegoPerspective Φ s P` is monotone on `Ici 0` when `MonotoneOn Φ (Ici 0)`. -/
theorem monotoneOn_polyaSzegoPerspective_right {Φ : ℝ → ℝ}
    (hΦ : MonotoneOn Φ (Ici (0 : ℝ))) (s : ℝ) :
    MonotoneOn (polyaSzegoPerspective Φ s) (Ici 0) :=
  fun _ hP₁ _ _ hP ↦ polyaSzegoPerspective_le_of_le_right hΦ s hP₁ hP
/-- **Combined level-set Pólya–Szegő comparison inequality**:
`polyaSzegoPerspective Φ s₂ P₁ ≤ polyaSzegoPerspective Φ s₁ P₂`. -/
theorem polyaSzegoPerspective_le_of_le_of_le {Φ : ℝ → ℝ}
    (hΦ_conv : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (hΦ_mono : MonotoneOn Φ (Ici (0 : ℝ)))
    (hΦ0 : Φ 0 ≤ 0) {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) :
    polyaSzegoPerspective Φ s₂ P₁ ≤ polyaSzegoPerspective Φ s₁ P₂ :=
  (polyaSzegoPerspective_le_of_le_left hΦ_conv hΦ0 hP₁ hs₁ hs).trans
    (polyaSzegoPerspective_le_of_le_right hΦ_mono s₁ hP₁ hP)
/-- `P ↦ polyaSzegoPerspective Φ s P` is convex on `Ici 0` when `ConvexOn ℝ (Ici 0) Φ`. -/
theorem convexOn_polyaSzegoPerspective_right {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (s : ℝ) :
    ConvexOn ℝ (Ici (0 : ℝ)) (polyaSzegoPerspective Φ s) := by
  refine ⟨convex_Ici 0, fun P₁ hP₁ P₂ hP₂ a b ha hb hab ↦ ?_⟩
  by_cases hs : s ≤ 0
  · simp [polyaSzegoPerspective, hs]
  · have hs_pos : 0 < s := not_le.mp hs
    simp only [polyaSzegoPerspective_of_pos Φ hs_pos, smul_eq_mul]
    have hdiv : (a * P₁ + b * P₂) / s = a • (P₁ / s) + b • (P₂ / s) := by
      simp [smul_eq_mul, add_div, mul_div_assoc]
    have hconv := hΦ.2 (div_nonneg hP₁ hs_pos.le) (div_nonneg hP₂ hs_pos.le) ha hb hab
    rw [← hdiv] at hconv
    have hmul := mul_le_mul_of_nonneg_left hconv hs_pos.le
    simp only [smul_eq_mul] at hmul; linarith
/-- **Joint subadditivity of `polyaSzegoPerspective`** for `0 < s₁, s₂` and `0 ≤ P₁, P₂`. -/
theorem polyaSzegoPerspective_add_le {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici (0 : ℝ)) Φ)
    {s₁ s₂ P₁ P₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) :
    polyaSzegoPerspective Φ (s₁ + s₂) (P₁ + P₂) ≤
      polyaSzegoPerspective Φ s₁ P₁ + polyaSzegoPerspective Φ s₂ P₂ := by
  have hs : 0 < s₁ + s₂ := add_pos hs₁ hs₂
  rw [polyaSzegoPerspective_of_pos Φ hs, polyaSzegoPerspective_of_pos Φ hs₁,
    polyaSzegoPerspective_of_pos Φ hs₂]
  set θ₁ := s₁ / (s₁ + s₂); set θ₂ := s₂ / (s₁ + s₂)
  have hθ₁ : 0 ≤ θ₁ := div_nonneg hs₁.le hs.le
  have hθ₂ : 0 ≤ θ₂ := div_nonneg hs₂.le hs.le
  have hsum : θ₁ + θ₂ = 1 := by dsimp [θ₁, θ₂]; rw [← add_div, div_self hs.ne']
  have hcomb : (P₁ + P₂) / (s₁ + s₂) = θ₁ • (P₁ / s₁) + θ₂ • (P₂ / s₂) := by
    dsimp [θ₁, θ₂]
    have h1 : s₁ / (s₁ + s₂) * (P₁ / s₁) = P₁ / (s₁ + s₂) := by field_simp
    have h2 : s₂ / (s₁ + s₂) * (P₂ / s₂) = P₂ / (s₁ + s₂) := by field_simp
    rw [h1, h2, add_div]
  have hconv := hΦ.2 (div_nonneg hP₁ hs₁.le) (div_nonneg hP₂ hs₂.le) hθ₁ hθ₂ hsum
  rw [← hcomb] at hconv
  have hmul := mul_le_mul_of_nonneg_left hconv hs.le
  have h1 : (s₁ + s₂) * (θ₁ • Φ (P₁ / s₁) + θ₂ • Φ (P₂ / s₂)) =
      s₁ * Φ (P₁ / s₁) + s₂ * Φ (P₂ / s₂) := by
    dsimp [θ₁, θ₂]; simp only [left_distrib, ← mul_assoc, mul_div_cancel₀ _ hs.ne']
  linarith
/-- **Level-set Jensen inequality for `polyaSzegoPerspective`**:
`polyaSzegoPerspective Φ (μ A).toReal (∫ x in A, g x ∂μ) ≤ ∫ x in A, Φ (g x) ∂μ`. -/
theorem polyaSzegoPerspective_measure_le_setIntegral
    {μ : Measure α} {A : Set α} {g : α → ℝ} {Φ : ℝ → ℝ}
    (hΦ_conv : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (hΦ_cont : ContinuousOn Φ (Ici (0 : ℝ)))
    (hA_fin : μ A ≠ ⊤) (hg_nn : ∀ᵐ x ∂μ.restrict A, 0 ≤ g x)
    (hg_int : IntegrableOn g A μ) (hΦg_int : IntegrableOn (Φ ∘ g) A μ) :
    polyaSzegoPerspective Φ (μ A).toReal (∫ x in A, g x ∂μ) ≤ ∫ x in A, Φ (g x) ∂μ := by
  rcases eq_or_ne (μ A) 0 with hA0 | hA0
  · simp [hA0, Measure.restrict_eq_zero.mpr hA0]
  · have hA_pos : 0 < (μ A).toReal := ENNReal.toReal_pos hA0 hA_fin
    rw [polyaSzegoPerspective_of_pos Φ hA_pos]
    have hjensen := hΦ_conv.map_set_average_le hΦ_cont isClosed_Ici hA0 hA_fin hg_nn hg_int hΦg_int
    rw [setAverage_eq, setAverage_eq, Measure.real_def, smul_eq_mul, smul_eq_mul,
      ← div_eq_inv_mul, ← div_eq_inv_mul, le_div_iff₀ hA_pos] at hjensen; linarith
/-- **Full level-set Pólya–Szegő inequality** (combining `0 ≤ PStar ≤ ∫ x in A, g x ∂μ`,
`(μ A).toReal ≤ sStar`, and Jensen's inequality, including measure-zero levels via `Φ 0 = 0`):
`polyaSzegoPerspective Φ sStar PStar ≤ ∫ x in A, Φ (g x) ∂μ`. -/
theorem polyaSzegoPerspective_le_setIntegral
    {μ : Measure α} {A : Set α} {g : α → ℝ} {Φ : ℝ → ℝ} {sStar PStar : ℝ}
    (hΦ_conv : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (hΦ_mono : MonotoneOn Φ (Ici (0 : ℝ)))
    (hΦ_cont : ContinuousOn Φ (Ici (0 : ℝ))) (hΦ0 : Φ 0 = 0) (hA_fin : μ A ≠ ⊤)
    (hg_nn : ∀ᵐ x ∂μ.restrict A, 0 ≤ g x)
    (hg_int : IntegrableOn g A μ) (hΦg_int : IntegrableOn (Φ ∘ g) A μ)
    (hP_nn : 0 ≤ PStar) (hP_le : PStar ≤ ∫ x in A, g x ∂μ) (hs_le : (μ A).toReal ≤ sStar) :
    polyaSzegoPerspective Φ sStar PStar ≤ ∫ x in A, Φ (g x) ∂μ := by
  rcases eq_or_ne (μ A) 0 with hA0 | hA0
  · have hint0 : ∫ x in A, g x ∂μ = 0 := by simp [Measure.restrict_eq_zero.mpr hA0]
    have hP0 : PStar = 0 := le_antisymm (hP_le.trans_eq hint0) hP_nn
    subst hP0; rw [polyaSzegoPerspective_zero_right hΦ0]; simp [Measure.restrict_eq_zero.mpr hA0]
  · have hA_pos : 0 < (μ A).toReal := ENNReal.toReal_pos hA0 hA_fin
    refine (polyaSzegoPerspective_le_of_le_of_le hΦ_conv hΦ_mono hΦ0.le hP_nn hP_le hA_pos
      hs_le).trans ?_
    exact polyaSzegoPerspective_measure_le_setIntegral hΦ_conv hΦ_cont hA_fin hg_nn hg_int hΦg_int

end TauCeti

end
