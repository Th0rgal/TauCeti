/-
Copyright (c) 2026 General Intelligence, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module

public import TauCeti.MeasureTheory.Measure.PolyaSzego
public import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Count
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.BallPerimeter
import all TauCeti.MeasureTheory.Measure.BVSobolev
import all TauCeti.MeasureTheory.Measure.PolyaSzego
import all TauCeti.MeasureTheory.Function.SchwarzRearrangement
import all TauCeti.MeasureTheory.Function.SchwarzRadialProfile
import all TauCeti.MeasureTheory.Function.SchwarzLp

/-!
# Polar Integration Formula, Radial Gradient Norm Identities, and `W^{1,1}` Pólya–Szegő

This file establishes the pushforward measure identity for `x ↦ ‖x - c‖` on any finite-dimensional
real inner product space, derives the general polar/radial integration formulas on the whole space,
balls, and concentric annuli, proves the exact `L¹` and Orlicz gradient norm identities for radial
functions together with the `W^{1,1}` gradient Pólya–Szegő inequality `∫ ‖∇(u*)‖ ≤ ∫ ‖∇u‖`, and
proves the normalization `μH[0] = Measure.count` and Hausdorff scaling of spheres.

## Main Definitions

* `TauCeti.polarDensity`: the radial surface density
  `r ↦ (Module.finrank ℝ E : ℝ≥0∞) * μ (Metric.ball (0 : E) 1) * ENNReal.ofReal (r ^ (n - 1))`.

## Main Results

* `TauCeti.map_norm_sub_eq_withDensity_polarDensity`,
  `TauCeti.map_norm_eq_withDensity_polarDensity`,
  `TauCeti.lintegral_comp_norm_sub_eq`, `TauCeti.lintegral_comp_norm_eq`,
  `TauCeti.setLIntegral_ball_comp_norm_sub_eq`, `TauCeti.setLIntegral_annulus_comp_norm_sub_eq`,
  `TauCeti.integral_comp_norm_sub_eq`, `TauCeti.integral_comp_norm_eq`.
* `TauCeti.ae_gradient_comp_norm`, `TauCeti.lintegral_enorm_gradient_comp_norm_eq`,
  `TauCeti.integral_norm_gradient_comp_norm_eq`,
  `TauCeti.lintegral_enorm_gradient_schwarzRearrangementReal_eq`,
  `TauCeti.lintegral_enorm_gradient_schwarzRearrangementReal_le`,
  `TauCeti.integral_norm_gradient_schwarzRearrangementReal_le`.
* `TauCeti.hausdorffMeasure_zero_apply`, `TauCeti.hausdorffMeasure_zero_eq_count`,
  `TauCeti.hausdorffMeasure_zero_sphere_real`, `TauCeti.hausdorffMeasure_sphere`.
-/

open Filter Function InnerProductSpace MeasureTheory Pointwise Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace Gradient Topology Interval MeasureTheory Finset

public section

namespace TauCeti

/-! ### Section 1: Pushforward of `x ↦ ‖x - c‖` and general polar/radial integration formula -/
/-- Fundamental theorem of calculus for `s ↦ (k : ℝ) * s ^ (k - 1)` on `(a, b]` in `lintegral`
form (`0 ≤ a ≤ b`). -/
theorem lintegral_Ioc_mul_pow_pred (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ s in Ioc a b, ENNReal.ofReal ((k : ℝ) * s ^ (k - 1)) =
      ENNReal.ofReal (b ^ k - a ^ k) := by
  have hcont : Continuous (fun s : ℝ ↦ (k : ℝ) * s ^ (k - 1)) := by fun_prop
  have hint : IntegrableOn (fun s : ℝ ↦ (k : ℝ) * s ^ (k - 1)) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (hcont.intervalIntegrable a b)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦
      mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (ha.trans hs.1.le) _)),
    ← intervalIntegral.integral_of_le hab]
  have hd : ∀ s ∈ uIcc a b, HasDerivAt (fun x : ℝ ↦ x ^ k) ((k : ℝ) * s ^ (k - 1)) s :=
    fun s _ ↦ hasDerivAt_pow k s
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable a b)]
/-- Fundamental theorem of calculus for `s ↦ (k : ℝ) * s ^ (k - 1)` on `(a, b)` in `lintegral`
form (`0 ≤ a ≤ b`). -/
theorem lintegral_Ioo_mul_pow_pred_sub (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ s in Ioo a b, ENNReal.ofReal ((k : ℝ) * s ^ (k - 1)) =
      ENNReal.ofReal (b ^ k - a ^ k) := by
  rw [restrict_Ioo_eq_restrict_Ioc, lintegral_Ioc_mul_pow_pred k ha hab]
section PolarMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Radial Surface Density (`polarDensity μ r`)**:
`(Module.finrank ℝ E : ℝ≥0∞) * μ (Metric.ball (0 : E) 1) * ENNReal.ofReal (r ^ (n - 1))`. -/
noncomputable def polarDensity (r : ℝ) : ℝ≥0∞ :=
  (Module.finrank ℝ E : ℝ≥0∞) * μ (Metric.ball (0 : E) 1) *
    ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1))
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `polarDensity μ` is Borel measurable. -/
@[fun_prop]
theorem measurable_polarDensity : Measurable (polarDensity μ) := by
  unfold polarDensity; fun_prop
omit [BorelSpace E] in
/-- `polarDensity μ r < ⊤` for every `r : ℝ` when `μ` is finite on compacts. -/
theorem polarDensity_lt_top [IsFiniteMeasureOnCompacts μ] (r : ℝ) :
    polarDensity μ r < ⊤ :=
  ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) measure_ball_lt_top)
    ENNReal.ofReal_lt_top
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `(polarDensity μ r).toReal` for `r ≥ 0`. -/
theorem toReal_polarDensity {r : ℝ} (hr : 0 ≤ r) :
    (polarDensity μ r).toReal =
      (Module.finrank ℝ E : ℝ) * (μ (Metric.ball (0 : E) 1)).toReal *
        r ^ (Module.finrank ℝ E - 1) := by
  simp only [polarDensity, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hr _)]
/-- For `r > 0` in a nontrivial space `E`, `polarDensity μ r = perimeter μ (Metric.ball c r)`. -/
theorem polarDensity_eq_perimeter_ball [Nontrivial E] [μ.IsAddHaarMeasure] (c : E) {r : ℝ}
    (hr : 0 < r) :
    polarDensity μ r = perimeter μ (Metric.ball c r) := by
  rw [perimeter_ball_eq_unitBall c hr, polarDensity,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  ring
/-- On `EuclideanSpace ℝ (Fin n)`, `polarDensity volume r` is `n * ω_n * ofReal (r^(n-1))`. -/
theorem polarDensity_euclideanSpace (n : ℕ) (r : ℝ) :
    polarDensity (volume : Measure (EuclideanSpace ℝ (Fin n))) r =
      (n : ℝ≥0∞) * unitBallVolume n * ENNReal.ofReal (r ^ (n - 1)) := by
  simp [polarDensity, unitBallVolume]
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `polarDensity μ r = μ (ball 0 1) * ofReal (n * r ^ (n - 1))`. -/
theorem polarDensity_eq_mul_ofReal (r : ℝ) :
    polarDensity μ r =
      μ (Metric.ball (0 : E) 1) *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * r ^ (Module.finrank ℝ E - 1)) := by
  rw [polarDensity, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  ring
omit [BorelSpace E] in
/-- Integral of `polarDensity μ` over `Ioc a b` (`0 ≤ a ≤ b`). -/
theorem setLIntegral_Ioc_polarDensity [IsFiniteMeasureOnCompacts μ]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ r in Ioc a b, polarDensity μ r =
      μ (Metric.ball (0 : E) 1) *
        ENNReal.ofReal (b ^ Module.finrank ℝ E - a ^ Module.finrank ℝ E) := by
  have hcongr : ∀ r ∈ Ioc a b, polarDensity μ r =
      μ (Metric.ball (0 : E) 1) *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * r ^ (Module.finrank ℝ E - 1)) :=
    fun r _ ↦ polarDensity_eq_mul_ofReal μ r
  rw [setLIntegral_congr_fun measurableSet_Ioc hcongr,
    lintegral_const_mul' _ _ measure_ball_lt_top.ne,
    lintegral_Ioc_mul_pow_pred (Module.finrank ℝ E) ha hab]
omit [BorelSpace E] in
/-- Integral of `polarDensity μ` over `Ioo a b` (`0 ≤ a ≤ b`). -/
theorem setLIntegral_Ioo_polarDensity [IsFiniteMeasureOnCompacts μ]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ r in Ioo a b, polarDensity μ r =
      μ (Metric.ball (0 : E) 1) *
        ENNReal.ofReal (b ^ Module.finrank ℝ E - a ^ Module.finrank ℝ E) := by
  rw [restrict_Ioo_eq_restrict_Ioc, setLIntegral_Ioc_polarDensity μ ha hab]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Preimage of `Ioc a b` under `x ↦ ‖x - c‖` is `closedBall c b \ closedBall c a`. -/
theorem preimage_norm_sub_Ioc (c : E) (a b : ℝ) :
    (fun x : E ↦ ‖x - c‖) ⁻¹' Ioc a b = Metric.closedBall c b \ Metric.closedBall c a := by
  ext x
  simp only [mem_preimage, mem_Ioc, Set.mem_sdiff, Metric.mem_closedBall, dist_eq_norm]
  exact ⟨fun h ↦ ⟨h.2, not_le.2 h.1⟩, fun h ↦ ⟨not_le.1 h.2, h.1⟩⟩
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Preimage of `Ioo a b` under `x ↦ ‖x - c‖` is `ball c b \ closedBall c a`. -/
theorem preimage_norm_sub_Ioo (c : E) (a b : ℝ) :
    (fun x : E ↦ ‖x - c‖) ⁻¹' Ioo a b = Metric.ball c b \ Metric.closedBall c a := by
  ext x
  simp only [mem_preimage, mem_Ioo, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall,
    dist_eq_norm]
  exact ⟨fun h ↦ ⟨h.2, not_le.2 h.1⟩, fun h ↦ ⟨not_le.1 h.2, h.1⟩⟩
/-- Measure of `(fun x ↦ ‖x - c‖) ⁻¹' Ioc a b` for `0 ≤ a ≤ b` equals the integral of
`polarDensity μ` over `Ioc a b`. -/
theorem measure_preimage_norm_sub_Ioc [μ.IsAddHaarMeasure] (c : E)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    μ ((fun x : E ↦ ‖x - c‖) ⁻¹' Ioc a b) = ∫⁻ r in Ioc a b, polarDensity μ r := by
  rw [preimage_norm_sub_Ioc,
    measure_sdiff (Metric.closedBall_subset_closedBall hab)
      measurableSet_closedBall.nullMeasurableSet measure_closedBall_lt_top.ne,
    Measure.addHaar_closedBall μ c (ha.trans hab), Measure.addHaar_closedBall μ c ha,
    setLIntegral_Ioc_polarDensity μ ha hab,
    ← ENNReal.sub_mul (fun _ _ ↦ measure_ball_lt_top.ne), mul_comm,
    ENNReal.ofReal_sub _ (pow_nonneg ha _)]
/-- **Pushforward Measure Identity (`map_norm_sub_eq_withDensity_polarDensity`)**:
the pushforward of `μ` under `x ↦ ‖x - c‖` on `[Nontrivial E]` is
`(volume.restrict (Ioi 0)).withDensity (polarDensity μ)`. -/
theorem map_norm_sub_eq_withDensity_polarDensity [Nontrivial E] [μ.IsAddHaarMeasure] (c : E) :
    Measure.map (fun x : E ↦ ‖x - c‖) μ =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (polarDensity μ) := by
  have hmeas : Measurable (fun x : E ↦ ‖x - c‖) := by fun_prop
  refine Measure.ext_of_Ioc' _ _ (fun a b _ ↦ ?_) (fun a b _ ↦ ?_)
  · rw [Measure.map_apply hmeas measurableSet_Ioc, preimage_norm_sub_Ioc]
    exact (measure_mono sdiff_subset).trans_lt measure_closedBall_lt_top |>.ne
  · rw [Measure.map_apply hmeas measurableSet_Ioc,
      withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
    have hinter : Ioc a b ∩ Ioi (0 : ℝ) = Ioc (max a 0) b := by
      ext r; simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]
      tauto
    rw [hinter]
    have hdiff : ((fun x : E ↦ ‖x - c‖) ⁻¹' Ioc a b) \ {c} =
        (fun x : E ↦ ‖x - c‖) ⁻¹' Ioc (max a 0) b := by
      ext x
      simp only [Set.mem_sdiff, mem_preimage, mem_Ioc, mem_singleton_iff, max_lt_iff,
         ← sub_ne_zero (a := x), ← norm_pos_iff]
      tauto
    have hμ_eq : μ ((fun x : E ↦ ‖x - c‖) ⁻¹' Ioc a b) =
        μ ((fun x : E ↦ ‖x - c‖) ⁻¹' Ioc (max a 0) b) := by
      rw [← hdiff, measure_sdiff_null (measure_singleton c)]
    rw [hμ_eq]
    rcases le_or_gt (max a 0) b with hle | hgt
    · exact measure_preimage_norm_sub_Ioc μ c (le_max_right a 0) hle
    · simp [Ioc_eq_empty_of_le hgt.le]
/-- **Pushforward Measure Identity at the Origin (`map_norm_eq_withDensity_polarDensity`)**:
`Measure.map (fun x : E ↦ ‖x‖) μ = (volume.restrict (Ioi 0)).withDensity (polarDensity μ)`. -/
theorem map_norm_eq_withDensity_polarDensity [Nontrivial E] [μ.IsAddHaarMeasure] :
    Measure.map (fun x : E ↦ ‖x‖) μ =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (polarDensity μ) := by
  simpa only [sub_zero] using map_norm_sub_eq_withDensity_polarDensity μ (0 : E)
/-- The radial distance map `x ↦ ‖x - c‖` is quasi-measure-preserving from `μ` to
`volume.restrict (Ioi 0)`. -/
theorem quasiMeasurePreserving_norm_sub [Nontrivial E] [μ.IsAddHaarMeasure] (c : E) :
    Measure.QuasiMeasurePreserving (fun x : E ↦ ‖x - c‖) μ (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨by fun_prop, map_norm_sub_eq_withDensity_polarDensity μ c ▸
    withDensity_absolutelyContinuous _ _⟩
/-- The norm map `x ↦ ‖x‖` is quasi-measure-preserving from `μ` to `volume.restrict (Ioi 0)`. -/
theorem quasiMeasurePreserving_norm [Nontrivial E] [μ.IsAddHaarMeasure] :
    Measure.QuasiMeasurePreserving (fun x : E ↦ ‖x‖) μ (volume.restrict (Ioi (0 : ℝ))) := by
  simpa only [sub_zero] using quasiMeasurePreserving_norm_sub μ (0 : E)
/-- Any property `P : ℝ → Prop` that holds for `volume`-a.e. `r ∈ (0, ∞)` holds for `‖x - c‖` at
`μ`-a.e. `x : E`. -/
theorem ae_comp_norm_sub_of_ae_Ioi [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), P r) :
    ∀ᵐ x ∂μ, P ‖x - c‖ :=
  (quasiMeasurePreserving_norm_sub μ c).ae hP
/-- Any property `P : ℝ → Prop` that holds for `volume`-a.e. `r ∈ (0, ∞)` holds for `‖x‖` at
`μ`-a.e. `x : E`. -/
theorem ae_comp_norm_of_ae_Ioi [Nontrivial E] [μ.IsAddHaarMeasure]
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), P r) :
    ∀ᵐ x ∂μ, P ‖x‖ :=
  (quasiMeasurePreserving_norm μ).ae hP
/-- **General Polar Integration Formula (`lintegral`, centered at `c`)**: for any measurable
`g : ℝ → ℝ≥0∞`,
`∫⁻ x, g ‖x - c‖ ∂μ = ∫⁻ r in Ioi 0, polarDensity μ r * g r`. -/
theorem lintegral_comp_norm_sub_eq [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x : E, g ‖x - c‖ ∂μ = ∫⁻ r in Ioi (0 : ℝ), polarDensity μ r * g r := by
  rw [← lintegral_map hg (by fun_prop), map_norm_sub_eq_withDensity_polarDensity μ c,
    lintegral_withDensity_eq_lintegral_mul₀ (measurable_polarDensity μ).aemeasurable
      hg.aemeasurable]
  rfl
/-- **General Polar Integration Formula (`lintegral`, centered at `0`)**:
`∫⁻ x, g ‖x‖ ∂μ = ∫⁻ r in Ioi 0, polarDensity μ r * g r`. -/
theorem lintegral_comp_norm_eq [Nontrivial E] [μ.IsAddHaarMeasure]
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x : E, g ‖x‖ ∂μ = ∫⁻ r in Ioi (0 : ℝ), polarDensity μ r * g r := by
  simpa only [sub_zero] using lintegral_comp_norm_sub_eq μ (0 : E) hg
/-- **Polar Integration Formula on `Metric.ball c R`**:
`∫⁻ x in ball c R, g ‖x - c‖ ∂μ = ∫⁻ r in Ioo 0 R, polarDensity μ r * g r`. -/
theorem setLIntegral_ball_comp_norm_sub_eq [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    (R : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in Metric.ball c R, g ‖x - c‖ ∂μ =
      ∫⁻ r in Ioo 0 R, polarDensity μ r * g r := by
  have hpre : Metric.ball c R = (fun x : E ↦ ‖x - c‖) ⁻¹' Iio R := by
    ext x; simp [Metric.mem_ball, dist_eq_norm]
  have hind : ∫⁻ x in Metric.ball c R, g ‖x - c‖ ∂μ =
      ∫⁻ x, ((Iio R).indicator g) ‖x - c‖ ∂μ := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun x ↦ ?_
    rw [hpre]; rfl
  rw [hind, lintegral_comp_norm_sub_eq μ c (hg.indicator measurableSet_Iio)]
  have hmul : (fun r ↦ polarDensity μ r * (Iio R).indicator g r) =
      (Iio R).indicator (fun r ↦ polarDensity μ r * g r) := by
    ext r; by_cases hr : r ∈ Iio R <;> simp [hr]
  have hinter : Iio R ∩ Ioi (0 : ℝ) = Ioo 0 R := by
    ext r; simp [and_comm]
  rw [hmul, setLIntegral_indicator measurableSet_Iio, hinter]
/-- **Polar Integration Formula on `Metric.closedBall c R`**:
`∫⁻ x in closedBall c R, g ‖x - c‖ ∂μ = ∫⁻ r in Ioc 0 R, polarDensity μ r * g r`. -/
theorem setLIntegral_closedBall_comp_norm_sub_eq [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    (R : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in Metric.closedBall c R, g ‖x - c‖ ∂μ =
      ∫⁻ r in Ioc 0 R, polarDensity μ r * g r := by
  have hpre : Metric.closedBall c R = (fun x : E ↦ ‖x - c‖) ⁻¹' Iic R := by
    ext x; simp [Metric.mem_closedBall, dist_eq_norm]
  have hind : ∫⁻ x in Metric.closedBall c R, g ‖x - c‖ ∂μ =
      ∫⁻ x, ((Iic R).indicator g) ‖x - c‖ ∂μ := by
    rw [← lintegral_indicator measurableSet_closedBall]
    refine lintegral_congr fun x ↦ ?_
    rw [hpre]; rfl
  rw [hind, lintegral_comp_norm_sub_eq μ c (hg.indicator measurableSet_Iic)]
  have hmul : (fun r ↦ polarDensity μ r * (Iic R).indicator g r) =
      (Iic R).indicator (fun r ↦ polarDensity μ r * g r) := by
    ext r; by_cases hr : r ∈ Iic R <;> simp [hr]
  have hinter : Iic R ∩ Ioi (0 : ℝ) = Ioc 0 R := by
    ext r; simp [and_comm]
  rw [hmul, setLIntegral_indicator measurableSet_Iic, hinter]
/-- **Polar Integration Formula on an Annulus `ball c R \ closedBall c r`** (`0 ≤ r`):
`∫⁻ x in ball c R \ closedBall c r, g ‖x - c‖ ∂μ = ∫⁻ s in Ioo r R, polarDensity μ s * g s`. -/
theorem setLIntegral_annulus_comp_norm_sub_eq [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    {r R : ℝ} (hr : 0 ≤ r) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in Metric.ball c R \ Metric.closedBall c r, g ‖x - c‖ ∂μ =
      ∫⁻ s in Ioo r R, polarDensity μ s * g s := by
  have hind : ∫⁻ x in Metric.ball c R \ Metric.closedBall c r, g ‖x - c‖ ∂μ =
      ∫⁻ x, ((Ioo r R).indicator g) ‖x - c‖ ∂μ := by
    rw [← preimage_norm_sub_Ioo, ← lintegral_indicator
      ((measurableSet_Ioo).preimage (by fun_prop))]
    rfl
  rw [hind, lintegral_comp_norm_sub_eq μ c (hg.indicator measurableSet_Ioo)]
  have hmul : (fun s ↦ polarDensity μ s * (Ioo r R).indicator g s) =
      (Ioo r R).indicator (fun s ↦ polarDensity μ s * g s) := by
    ext s; by_cases hs : s ∈ Ioo r R <;> simp [hs]
  rw [hmul, setLIntegral_indicator measurableSet_Ioo,
    inter_eq_self_of_subset_left (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi hr))]
/-- **Integrability Equivalence for Radial Functions (`integrable_comp_norm_sub_iff`)**:
for `g : ℝ → F` (`AEStronglyMeasurable g (volume.restrict (Ioi 0))`), `x ↦ g ‖x - c‖` is
`μ`-integrable iff `r ↦ (polarDensity μ r).toReal • g r` is integrable on `Ioi 0`. -/
theorem integrable_comp_norm_sub_iff [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ → F}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (fun x : E ↦ g ‖x - c‖) μ ↔
      IntegrableOn (fun r : ℝ ↦ (polarDensity μ r).toReal • g r) (Ioi (0 : ℝ)) volume := by
  have hmap : AEStronglyMeasurable g (Measure.map (fun x : E ↦ ‖x - c‖) μ) := by
    rw [map_norm_sub_eq_withDensity_polarDensity μ c]
    exact hg.mono_ac (withDensity_absolutelyContinuous _ _)
  refine (integrable_map_measure hmap (by fun_prop)).symm.trans ?_
  rw [map_norm_sub_eq_withDensity_polarDensity μ c,
    integrable_withDensity_iff_integrable_smul' (measurable_polarDensity μ)
      (Eventually.of_forall (polarDensity_lt_top μ))]
  rfl
/-- **Integrability Equivalence for Radial Functions Centered at `0`**. -/
theorem integrable_comp_norm_iff [Nontrivial E] [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ → F}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (fun x : E ↦ g ‖x‖) μ ↔
      IntegrableOn (fun r : ℝ ↦ (polarDensity μ r).toReal • g r) (Ioi (0 : ℝ)) volume := by
  simpa only [sub_zero] using integrable_comp_norm_sub_iff μ (0 : E) hg
/-- **Bochner Polar Integration Formula (`integral_comp_norm_sub_eq_smul`)** for vector-valued
radial functions `g : ℝ → F`. -/
theorem integral_comp_norm_sub_eq_smul [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ → F}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) :
    ∫ x : E, g ‖x - c‖ ∂μ =
      ∫ r in Ioi (0 : ℝ), (polarDensity μ r).toReal • g r := by
  have hmap : AEStronglyMeasurable g (Measure.map (fun x : E ↦ ‖x - c‖) μ) := by
    rw [map_norm_sub_eq_withDensity_polarDensity μ c]
    exact hg.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [← integral_map (by fun_prop) hmap, map_norm_sub_eq_withDensity_polarDensity μ c,
    integral_withDensity_eq_integral_toReal_smul (measurable_polarDensity μ)
      (Eventually.of_forall (polarDensity_lt_top μ)) g]
/-- **Bochner Polar Integration Formula (`integral_comp_norm_sub_eq`)** for real-valued radial
functions `g : ℝ → ℝ`:
`∫ x, g ‖x - c‖ ∂μ = n * (μ (ball 0 1)).toReal * ∫ r in Ioi 0, g r * r ^ (n - 1)`. -/
theorem integral_comp_norm_sub_eq [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    {g : ℝ → ℝ} (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) :
    ∫ x : E, g ‖x - c‖ ∂μ =
      (Module.finrank ℝ E : ℝ) * (μ (Metric.ball (0 : E) 1)).toReal *
        ∫ r in Ioi (0 : ℝ), g r * r ^ (Module.finrank ℝ E - 1) := by
  rw [integral_comp_norm_sub_eq_smul μ c hg, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
  rw [toReal_polarDensity μ hr.le, smul_eq_mul]
  ring
/-- **Bochner Polar Integration Formula (`integral_comp_norm_eq`)** centered at `0`:
`∫ x, g ‖x‖ ∂μ = n * (μ (ball 0 1)).toReal * ∫ r in Ioi 0, g r * r ^ (n - 1)`. -/
theorem integral_comp_norm_eq [Nontrivial E] [μ.IsAddHaarMeasure]
    {g : ℝ → ℝ} (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) :
    ∫ x : E, g ‖x‖ ∂μ =
      (Module.finrank ℝ E : ℝ) * (μ (Metric.ball (0 : E) 1)).toReal *
        ∫ r in Ioi (0 : ℝ), g r * r ^ (Module.finrank ℝ E - 1) := by
  simpa only [sub_zero] using integral_comp_norm_sub_eq μ (0 : E) hg
/-- **Bochner Polar Integration Formula on `Metric.ball c R`**:
`∫ x in ball c R, g ‖x - c‖ ∂μ = n * (μ (ball 0 1)).toReal * ∫ r in Ioo 0 R, g r * r ^ (n - 1)`. -/
theorem setIntegral_ball_comp_norm_sub_eq [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    (R : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ x in Metric.ball c R, g ‖x - c‖ ∂μ =
      (Module.finrank ℝ E : ℝ) * (μ (Metric.ball (0 : E) 1)).toReal *
        ∫ r in Ioo 0 R, g r * r ^ (Module.finrank ℝ E - 1) := by
  have hpre : Metric.ball c R = (fun x : E ↦ ‖x - c‖) ⁻¹' Iio R := by
    ext x; simp [Metric.mem_ball, dist_eq_norm]
  have hind : ∫ x in Metric.ball c R, g ‖x - c‖ ∂μ =
      ∫ x, ((Iio R).indicator g) ‖x - c‖ ∂μ := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    rw [hpre]; rfl
  rw [hind, integral_comp_norm_sub_eq μ c
    (hg.indicator measurableSet_Iio).aestronglyMeasurable]
  congr 1
  have hmul : (fun r ↦ (Iio R).indicator g r * r ^ (Module.finrank ℝ E - 1)) =
      (Iio R).indicator (fun r ↦ g r * r ^ (Module.finrank ℝ E - 1)) := by
    ext r; by_cases hr : r ∈ Iio R <;> simp [hr]
  rw [hmul, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
/-- **Bochner Polar Integration Formula on an Annulus `ball c R \ closedBall c r`** (`0 ≤ r ≤ R`):
`∫_{B(c, R) \ clB(c, r)} g ‖x - c‖ dμ = n μ(B(0, 1)) ∫_r^R g(s) s^(n-1) ds`. -/
theorem setIntegral_annulus_comp_norm_sub_eq [Nontrivial E] [μ.IsAddHaarMeasure] (c : E)
    {r R : ℝ} (hr : 0 ≤ r) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ x in Metric.ball c R \ Metric.closedBall c r, g ‖x - c‖ ∂μ =
      (Module.finrank ℝ E : ℝ) * (μ (Metric.ball (0 : E) 1)).toReal *
        ∫ s in Ioo r R, g s * s ^ (Module.finrank ℝ E - 1) := by
  have hind : ∫ x in Metric.ball c R \ Metric.closedBall c r, g ‖x - c‖ ∂μ =
      ∫ x, ((Ioo r R).indicator g) ‖x - c‖ ∂μ := by
    rw [← preimage_norm_sub_Ioo, ← integral_indicator
      ((measurableSet_Ioo).preimage (by fun_prop))]
    rfl
  rw [hind, integral_comp_norm_sub_eq μ c
    (hg.indicator measurableSet_Ioo).aestronglyMeasurable]
  congr 1
  have hmul : (fun s ↦ (Ioo r R).indicator g s * s ^ (Module.finrank ℝ E - 1)) =
      (Ioo r R).indicator (fun s ↦ g s * s ^ (Module.finrank ℝ E - 1)) := by
    ext s; by_cases hs : s ∈ Ioo r R <;> simp [hs]
  rw [hmul, setIntegral_indicator measurableSet_Ioo,
    inter_eq_self_of_subset_right (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi hr))]
end PolarMeasure
/-- **Polar Integration Formula on `EuclideanSpace ℝ (Fin n)` (`lintegral` form)**:
`∫⁻ x, g ‖x‖ = n * unitBallVolume n * ∫⁻ r in Ioi 0, ofReal (r ^ (n - 1)) * g r`. -/
theorem lintegral_comp_norm_euclideanSpace {n : ℕ} [NeZero n]
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), g ‖x‖ =
      (n : ℝ≥0∞) * unitBallVolume n *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * g r := by
  rw [lintegral_comp_norm_eq volume hg,
    ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
      (unitBallVolume_ne_top n))]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
  rw [polarDensity_euclideanSpace, mul_assoc]
/-! ### Section 2: Radial gradient norm identities and `W^{1,1}` Pólya–Szegő inequality -/
/-- Any monotone function `v : ℝ → ℝ` is differentiable a.e. on `Ioi 0`. -/
theorem ae_differentiableAt_Ioi_of_monotone {v : ℝ → ℝ} (hv : Monotone v) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r :=
  ae_restrict_of_ae hv.ae_differentiableAt
/-- Any antitone function `v : ℝ → ℝ` is differentiable a.e. on `Ioi 0`. -/
theorem ae_differentiableAt_Ioi_of_antitone {v : ℝ → ℝ} (hv : Antitone v) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r := by
  filter_upwards [ae_restrict_of_ae hv.neg.ae_differentiableAt] with r hr
  exact differentiableAt_neg_iff.1 hr
section RadialGradientIntegral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Nontrivial E] [μ.IsAddHaarMeasure]
/-- For `μ`-a.e. `x : E`, `x ≠ 0`. -/
theorem ae_ne_zero : ∀ᵐ x ∂μ, x ≠ 0 := by
  simp [ae_iff]
/-- If `v : ℝ → ℝ` is differentiable a.e. on `(0, ∞)`, then for `μ`-a.e. `x : E`:
`v` is differentiable at `‖x‖`, `y ↦ v ‖y‖` is differentiable at `x`,
`∇ (fun y ↦ v ‖y‖) x = deriv v ‖x‖ • (‖x‖⁻¹ • x)`, and
`‖∇ (fun y ↦ v ‖y‖) x‖ = |deriv v ‖x‖|`. -/
theorem ae_differentiableAt_and_gradient_comp_norm {v : ℝ → ℝ}
    (hv : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ v ‖x‖ ∧
      DifferentiableAt ℝ (fun y : E ↦ v ‖y‖) x ∧
      ∇ (fun y : E ↦ v ‖y‖) x = deriv v ‖x‖ • (‖x‖⁻¹ • x) ∧
      ‖∇ (fun y : E ↦ v ‖y‖) x‖ = |deriv v ‖x‖| := by
  filter_upwards [ae_ne_zero μ, ae_comp_norm_of_ae_Ioi μ hv] with x hx hvx
  exact ⟨hvx, (hasFDerivAt_comp_norm hx hvx.hasDerivAt).differentiableAt,
    gradient_comp_norm hx hvx, norm_gradient_comp_norm hx hvx⟩
/-- For `μ`-a.e. `x : E`, `∇ (fun y ↦ v ‖y‖) x = deriv v ‖x‖ • (‖x‖⁻¹ • x)`. -/
theorem ae_gradient_comp_norm {v : ℝ → ℝ}
    (hv : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r) :
    ∀ᵐ x ∂μ, ∇ (fun y : E ↦ v ‖y‖) x = deriv v ‖x‖ • (‖x‖⁻¹ • x) := by
  filter_upwards [ae_differentiableAt_and_gradient_comp_norm μ hv] with x hx using hx.2.2.1
/-- For `μ`-a.e. `x : E`, `‖∇ (fun y ↦ v ‖y‖) x‖ = |deriv v ‖x‖|`. -/
theorem ae_norm_gradient_comp_norm {v : ℝ → ℝ}
    (hv : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r) :
    ∀ᵐ x ∂μ, ‖∇ (fun y : E ↦ v ‖y‖) x‖ = |deriv v ‖x‖| := by
  filter_upwards [ae_differentiableAt_and_gradient_comp_norm μ hv] with x hx using hx.2.2.2
/-- For `μ`-a.e. `x : E`, `‖∇ (fun y ↦ v ‖y‖) x‖ₑ = ENNReal.ofReal |deriv v ‖x‖|`. -/
theorem ae_enorm_gradient_comp_norm {v : ℝ → ℝ}
    (hv : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r) :
    ∀ᵐ x ∂μ, ‖∇ (fun y : E ↦ v ‖y‖) x‖ₑ = ENNReal.ofReal |deriv v ‖x‖| := by
  filter_upwards [ae_norm_gradient_comp_norm μ hv] with x hx
  rw [← ofReal_norm, hx]
/-- **Exact Orlicz / Convex-Integrand Radial Gradient Norm Identity (`lintegral` form)**:
`∫⁻ x, Φ ‖∇ (fun y ↦ v ‖y‖) x‖ ∂μ = ∫⁻ r in Ioi 0, polarDensity μ r * Φ |deriv v r|`. -/
theorem lintegral_comp_norm_gradient_comp_norm_eq {v : ℝ → ℝ}
    (hv : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r)
    {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ x : E, Φ ‖∇ (fun y : E ↦ v ‖y‖) x‖ ∂μ =
      ∫⁻ r in Ioi (0 : ℝ), polarDensity μ r * Φ |deriv v r| := by
  have hae : (fun x : E ↦ Φ ‖∇ (fun y : E ↦ v ‖y‖) x‖) =ᵐ[μ]
      fun x : E ↦ Φ |deriv v ‖x‖| := by
    filter_upwards [ae_norm_gradient_comp_norm μ hv] with x hx
    rw [hx]
  have hmeas : Measurable (fun r : ℝ ↦ Φ |deriv v r|) :=
    hΦ.comp (continuous_abs.measurable.comp (measurable_deriv v))
  rw [lintegral_congr_ae hae, lintegral_comp_norm_eq μ hmeas]
/-- **Exact `L¹` Radial Gradient Norm Identity (`lintegral` form)**:
`∫⁻ x, ‖∇(v ∘ norm) x‖ₑ ∂μ = n * μ(B(0, 1)) * ∫₀^∞ |deriv v r| r^(n-1) dr`. -/
theorem lintegral_enorm_gradient_comp_norm_eq {v : ℝ → ℝ}
    (hv : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r) :
    ∫⁻ x : E, ‖∇ (fun y : E ↦ v ‖y‖) x‖ₑ ∂μ =
      (Module.finrank ℝ E : ℝ≥0∞) * μ (Metric.ball (0 : E) 1) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (|deriv v r| * r ^ (Module.finrank ℝ E - 1)) := by
  have heq : (fun x : E ↦ ‖∇ (fun y : E ↦ v ‖y‖) x‖ₑ) =
      fun x : E ↦ ENNReal.ofReal ‖∇ (fun y : E ↦ v ‖y‖) x‖ := by
    ext x; exact (ofReal_norm _).symm
  rw [heq, lintegral_comp_norm_gradient_comp_norm_eq μ hv (by fun_prop),
    ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
  rw [polarDensity, ENNReal.ofReal_mul (abs_nonneg _)]
  ring
/-- **Exact `L¹` Radial Fréchet Derivative Norm Identity (`lintegral` form)**:
`∫⁻ x, ‖fderiv ℝ (v ∘ norm) x‖ₑ ∂μ = n * μ(B(0, 1)) * ∫₀^∞ |deriv v r| r^(n-1) dr`. -/
theorem lintegral_enorm_fderiv_comp_norm_eq {v : ℝ → ℝ}
    (hv : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r) :
    ∫⁻ x : E, ‖fderiv ℝ (fun y : E ↦ v ‖y‖) x‖ₑ ∂μ =
      (Module.finrank ℝ E : ℝ≥0∞) * μ (Metric.ball (0 : E) 1) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (|deriv v r| * r ^ (Module.finrank ℝ E - 1)) := by
  have h : (fun x : E ↦ ‖fderiv ℝ (fun y : E ↦ v ‖y‖) x‖ₑ) =
      fun x : E ↦ ‖∇ (fun y : E ↦ v ‖y‖) x‖ₑ := by
    ext x; rw [← ofReal_norm, ← ofReal_norm, norm_gradient_eq_norm_fderiv]
  rw [h, lintegral_enorm_gradient_comp_norm_eq μ hv]
/-- **Exact Bochner Radial Gradient Norm Identity (`integral_norm_gradient_comp_norm_eq`)**:
`∫ x, ‖∇(v ∘ norm) x‖ ∂μ = n * μ(B(0, 1)).toReal * ∫₀^∞ |deriv v r| r^(n-1) dr`. -/
theorem integral_norm_gradient_comp_norm_eq {v : ℝ → ℝ}
    (hv : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r) :
    ∫ x : E, ‖∇ (fun y : E ↦ v ‖y‖) x‖ ∂μ =
      (Module.finrank ℝ E : ℝ) * (μ (Metric.ball (0 : E) 1)).toReal *
        ∫ r in Ioi (0 : ℝ), |deriv v r| * r ^ (Module.finrank ℝ E - 1) := by
  have hmeas : Measurable (fun r : ℝ ↦ |deriv v r|) :=
    continuous_abs.measurable.comp (measurable_deriv v)
  rw [integral_congr_ae (ae_norm_gradient_comp_norm μ hv),
    integral_comp_norm_eq μ hmeas.aestronglyMeasurable]
/-- **Exact Bochner Orlicz / Convex-Integrand Radial Gradient Identity**:
`∫ x, Φ ‖∇(v ∘ norm) x‖ ∂μ = n * μ(B(0, 1)).toReal * ∫₀^∞ Φ |deriv v r| r^(n-1) dr`. -/
theorem integral_comp_norm_gradient_comp_norm_eq {v : ℝ → ℝ}
    (hv : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ v r)
    {Φ : ℝ → ℝ} (hΦ : Measurable Φ) :
    ∫ x : E, Φ ‖∇ (fun y : E ↦ v ‖y‖) x‖ ∂μ =
      (Module.finrank ℝ E : ℝ) * (μ (Metric.ball (0 : E) 1)).toReal *
        ∫ r in Ioi (0 : ℝ), Φ |deriv v r| * r ^ (Module.finrank ℝ E - 1) := by
  have hae : (fun x : E ↦ Φ ‖∇ (fun y : E ↦ v ‖y‖) x‖) =ᵐ[μ]
      fun x : E ↦ Φ |deriv v ‖x‖| := by
    filter_upwards [ae_norm_gradient_comp_norm μ hv] with x hx
    rw [hx]
  have hmeas : Measurable (fun r : ℝ ↦ Φ |deriv v r|) :=
    hΦ.comp (continuous_abs.measurable.comp (measurable_deriv v))
  rw [integral_congr_ae hae, integral_comp_norm_eq μ hmeas.aestronglyMeasurable]
end RadialGradientIntegral
section SchwarzGradientPolyaSzego
/-- At any `x ≠ 0`, `schwarzRearrangementReal u` agrees in `𝓝 x` with
`fun y ↦ schwarzRadialProfileReal u ‖y‖`. -/
theorem eventuallyEq_nhds_schwarzRearrangementReal {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < u y} < ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    schwarzRearrangementReal u =ᶠ[𝓝 x] fun y ↦ schwarzRadialProfileReal u ‖y‖ :=
  Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hx) fun _ hy ↦
    schwarzRearrangementReal_eq_schwarzRadialProfileReal_norm_of_ne_zero hu hdist hy
/-- At any `x ≠ 0`, `fderiv ℝ (schwarzRearrangementReal u) x` equals the Fréchet derivative of
`fun y ↦ schwarzRadialProfileReal u ‖y‖`. -/
theorem fderiv_schwarzRearrangementReal_eq_fderiv_comp_norm {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < u y} < ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    fderiv ℝ (schwarzRearrangementReal u) x =
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ schwarzRadialProfileReal u ‖y‖) x :=
  (eventuallyEq_nhds_schwarzRearrangementReal hu hdist hx).fderiv_eq
/-- At any `x ≠ 0`, `∇ (schwarzRearrangementReal u) x` equals the gradient of
`fun y ↦ schwarzRadialProfileReal u ‖y‖`. -/
theorem gradient_schwarzRearrangementReal_eq_gradient_comp_norm {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < u y} < ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ∇ (schwarzRearrangementReal u) x =
      ∇ (fun y : EuclideanSpace ℝ (Fin n) ↦ schwarzRadialProfileReal u ‖y‖) x := by
  apply (toDual ℝ (EuclideanSpace ℝ (Fin n))).injective
  rw [toDual_gradient, toDual_gradient,
    fderiv_schwarzRearrangementReal_eq_fderiv_comp_norm hu hdist hx]
/-- **Radial Gradient Formula for `schwarzRearrangementReal u`** at `x ≠ 0`:
`∇ (schwarzRearrangementReal u) x = deriv (schwarzRadialProfileReal u) ‖x‖ • (‖x‖⁻¹ • x)`. -/
theorem gradient_schwarzRearrangementReal {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < u y} < ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ (schwarzRadialProfileReal u) ‖x‖) :
    ∇ (schwarzRearrangementReal u) x =
      deriv (schwarzRadialProfileReal u) ‖x‖ • (‖x‖⁻¹ • x) := by
  rw [gradient_schwarzRearrangementReal_eq_gradient_comp_norm hu hdist hx,
    gradient_comp_norm hx hv]
/-- **Gradient Norm of `schwarzRearrangementReal u`** at `x ≠ 0`:
`‖∇ (schwarzRearrangementReal u) x‖ = |deriv (schwarzRadialProfileReal u) ‖x‖|`. -/
theorem norm_gradient_schwarzRearrangementReal {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < u y} < ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ (schwarzRadialProfileReal u) ‖x‖) :
    ‖∇ (schwarzRearrangementReal u) x‖ = |deriv (schwarzRadialProfileReal u) ‖x‖| := by
  rw [gradient_schwarzRearrangementReal_eq_gradient_comp_norm hu hdist hx,
    norm_gradient_comp_norm hx hv]
/-- **Exact `L¹` Gradient Norm Identity for `schwarzRearrangementReal u`**:
`∫⁻ x, ‖∇(u*) x‖ₑ = n * ω_n * ∫⁻ r in Ioi 0, ofReal (|(v*)'(r)| * r^(n-1))`. -/
theorem lintegral_enorm_gradient_schwarzRearrangementReal_eq {n : ℕ} [NeZero n]
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < u y} < ⊤)
    (hv_anti : Antitone (schwarzRadialProfileReal u)) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖∇ (schwarzRearrangementReal u) x‖ₑ =
      (n : ℝ≥0∞) * unitBallVolume n *
        ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal (|deriv (schwarzRadialProfileReal u) r| * r ^ (n - 1)) := by
  have hae : (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖∇ (schwarzRearrangementReal u) x‖ₑ) =ᵐ[volume]
      fun x : EuclideanSpace ℝ (Fin n) ↦
        ‖∇ (fun y : EuclideanSpace ℝ (Fin n) ↦ schwarzRadialProfileReal u ‖y‖) x‖ₑ := by
    filter_upwards [ae_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin n)))] with x hx
    rw [gradient_schwarzRearrangementReal_eq_gradient_comp_norm hu hdist hx]
  rw [lintegral_congr_ae hae,
    lintegral_enorm_gradient_comp_norm_eq volume (ae_differentiableAt_Ioi_of_antitone hv_anti),
    finrank_euclideanSpace_fin, unitBallVolume]
/-- **Gradient Norm of `u*` Bounded by Total Variation `|Du|(ℝⁿ)` (`2 ≤ n`)**:
`∫⁻ x, ‖∇(u*) x‖ₑ ≤ |Du|(ℝⁿ)`. -/
theorem lintegral_enorm_gradient_schwarzRearrangementReal_le_distributionalVariation {n : ℕ}
    (hn : 2 ≤ n) {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤)
    (hv_anti : Antitone (schwarzRadialProfileReal u))
    (hAC : ∀ a b, 0 < a → a ≤ b →
      AbsolutelyContinuousOnInterval (schwarzRadialProfileReal u) a b)
    (hcoarea : ∫⁻ t in Ioi (0 : ℝ), perimeter volume {x | t < u x} ≤
      distributionalVariation volume ⊤ u)
    (hisop : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))))⁻¹ *
        (volume {x | t < u x}) ^
          (1 / bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) ≤
        perimeter volume {x | t < u x}) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖∇ (schwarzRearrangementReal u) x‖ₑ ≤
      distributionalVariation volume ⊤ u := by
  have : NeZero n := ⟨by omega⟩
  rw [lintegral_enorm_gradient_schwarzRearrangementReal_eq hu hdist hv_anti]
  exact mul_lintegral_abs_deriv_schwarzRadialProfileReal_le_distributionalVariation
    hn hu hdist hv_anti hAC hcoarea hisop
/-- If `HasWeakFDerivOn μ Ω u (fderiv ℝ u)`, then `|Du|(Ω) ≤ ∫⁻ x in Ω, ‖∇ u x‖ₑ ∂μ`. -/
theorem distributionalVariation_le_lintegral_enorm_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {u : E → ℝ}
    (hw : HasWeakFDerivOn μ Ω u (fderiv ℝ u)) :
    distributionalVariation μ Ω u ≤ ∫⁻ x in (Ω : Set E), ‖∇ u x‖ₑ ∂μ := by
  refine hw.distributionalVariation_le_lintegral_enorm.trans_eq (lintegral_congr fun x ↦ ?_)
  rw [← ofReal_norm, ← ofReal_norm, norm_gradient_eq_norm_fderiv]
/-- **`W^{1,1}` Gradient Pólya–Szegő Inequality (`lintegral` form, `2 ≤ n`)**:
`∫⁻ x, ‖∇(u*) x‖ₑ ≤ ∫⁻ x, ‖∇ u x‖ₑ`. -/
theorem lintegral_enorm_gradient_schwarzRearrangementReal_le {n : ℕ}
    (hn : 2 ≤ n) {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤)
    (hv_anti : Antitone (schwarzRadialProfileReal u))
    (hAC : ∀ a b, 0 < a → a ≤ b →
      AbsolutelyContinuousOnInterval (schwarzRadialProfileReal u) a b)
    (hcoarea : ∫⁻ t in Ioi (0 : ℝ), perimeter volume {x | t < u x} ≤
      distributionalVariation volume ⊤ u)
    (hisop : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))))⁻¹ *
        (volume {x | t < u x}) ^
          (1 / bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) ≤
        perimeter volume {x | t < u x})
    (hw : HasWeakFDerivOn volume ⊤ u (fderiv ℝ u)) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖∇ (schwarzRearrangementReal u) x‖ₑ ≤
      ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖∇ u x‖ₑ := by
  refine (lintegral_enorm_gradient_schwarzRearrangementReal_le_distributionalVariation
    hn hu hdist hv_anti hAC hcoarea hisop).trans ?_
  simpa using distributionalVariation_le_lintegral_enorm_gradient hw
/-- **`W^{1,1}` Gradient Pólya–Szegő Inequality (Bochner `integral` form, `2 ≤ n`)**:
`∫ x, ‖∇(u*) x‖ ≤ ∫ x, ‖∇ u x‖`. -/
theorem integral_norm_gradient_schwarzRearrangementReal_le {n : ℕ}
    (hn : 2 ≤ n) {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤)
    (hv_anti : Antitone (schwarzRadialProfileReal u))
    (hAC : ∀ a b, 0 < a → a ≤ b →
      AbsolutelyContinuousOnInterval (schwarzRadialProfileReal u) a b)
    (hcoarea : ∫⁻ t in Ioi (0 : ℝ), perimeter volume {x | t < u x} ≤
      distributionalVariation volume ⊤ u)
    (hisop : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))))⁻¹ *
        (volume {x | t < u x}) ^
          (1 / bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) ≤
        perimeter volume {x | t < u x})
    (hw : HasWeakFDerivOn volume ⊤ u (fderiv ℝ u))
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖∇ u x‖) volume) :
    ∫ x : EuclideanSpace ℝ (Fin n), ‖∇ (schwarzRearrangementReal u) x‖ ≤
      ∫ x : EuclideanSpace ℝ (Fin n), ‖∇ u x‖ := by
  have hle := lintegral_enorm_gradient_schwarzRearrangementReal_le
    hn hu hdist hv_anti hAC hcoarea hisop hw
  have h1 : (∫⁻ x : EuclideanSpace ℝ (Fin n), ‖∇ u x‖ₑ) =
      ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n), ‖∇ u x‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ ↦ norm_nonneg _)]
    exact lintegral_congr fun _ ↦ (ofReal_norm _).symm
  have hfin : (∫⁻ x : EuclideanSpace ℝ (Fin n), ‖∇ (schwarzRearrangementReal u) x‖ₑ) < ⊤ :=
    hle.trans_lt (h1 ▸ ENNReal.ofReal_lt_top)
  have hintStar : Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦
      ‖∇ (schwarzRearrangementReal u) x‖) volume :=
    ⟨(measurable_gradient _).norm.aestronglyMeasurable,
      by simpa [hasFiniteIntegral_iff_enorm] using hfin⟩
  have h2 : (∫⁻ x : EuclideanSpace ℝ (Fin n), ‖∇ (schwarzRearrangementReal u) x‖ₑ) =
      ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n), ‖∇ (schwarzRearrangementReal u) x‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal hintStar (Eventually.of_forall fun _ ↦ norm_nonneg _)]
    exact lintegral_congr fun _ ↦ (ofReal_norm _).symm
  rw [h1, h2] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ norm_nonneg _)).1 hle
end SchwarzGradientPolyaSzego
/-! ### Section 3: `μH[0] = Measure.count` normalization and sphere Hausdorff scaling -/
section HausdorffZeroAndSphere
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
/-- On any finite set `t : Finset X` in a metric space, `μH[0] t = #t`. -/
theorem hausdorffMeasure_zero_finset (t : Finset X) :
    μH[0] (t : Set X) = #t := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.coe_insert, insert_eq,
      measure_union (disjoint_singleton_left.2 (by simpa using has)) s.measurableSet,
      Measure.hausdorffMeasure_zero_singleton, ih, Finset.card_insert_of_notMem has,
      Nat.cast_add, Nat.cast_one, add_comm]
/-- On any finite set `s : Set X`, `μH[0] s = #hs.toFinset`. -/
theorem hausdorffMeasure_zero_apply_finite {s : Set X} (hs : s.Finite) :
    μH[0] s = #hs.toFinset := by
  conv_lhs => rw [← hs.coe_toFinset]
  exact hausdorffMeasure_zero_finset _
/-- On any infinite set `s : Set X`, `μH[0] s = ⊤`. -/
theorem hausdorffMeasure_zero_apply_infinite {s : Set X} (hs : s.Infinite) :
    μH[0] s = ⊤ := by
  refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n ↦ ?_)
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  exact (hausdorffMeasure_zero_finset t).symm.trans_le (measure_mono ht)
/-- **Evaluation of `0`-Dimensional Hausdorff Measure**: for every subset `s : Set X` of a metric
space `X`, `μH[0] s = s.encard`. -/
@[simp]
theorem hausdorffMeasure_zero_apply (s : Set X) :
    μH[0] s = s.encard := by
  by_cases hs : s.Finite
  · rw [hausdorffMeasure_zero_apply_finite hs, hs.encard_eq_coe_toFinset_card]; rfl
  · rw [hausdorffMeasure_zero_apply_infinite hs, Infinite.encard_eq hs]; rfl
/-- **Normalization of `0`-Dimensional Hausdorff Measure (`μH[0] = Measure.count`)**:
on any metric space `X` equipped with its Borel σ-algebra, `μH[0] = Measure.count`. -/
theorem hausdorffMeasure_zero_eq_count :
    (μH[0] : Measure X) = Measure.count := by
  ext s hs
  rw [hausdorffMeasure_zero_apply, Measure.count_apply hs]
/-- In `ℝ`, the sphere `Metric.sphere c r` (`r ≥ 0`) is `{c + r, c - r}`. -/
theorem real_sphere_eq_pair (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Metric.sphere c r = {c + r, c - r} := by
  ext x
  simp only [Metric.mem_sphere, Real.dist_eq, abs_eq hr, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (h | h) <;> [left; right] <;> linarith
  · rintro (rfl | rfl) <;> [left; right] <;> ring
/-- For `r > 0` in `ℝ`, `μH[0] (Metric.sphere c r) = 2`. -/
theorem hausdorffMeasure_zero_sphere_real (c : ℝ) {r : ℝ} (hr : 0 < r) :
    μH[0] (Metric.sphere c r) = 2 := by
  have hne : c + r ≠ c - r := by linarith
  rw [real_sphere_eq_pair c hr.le, hausdorffMeasure_zero_apply, encard_pair hne]; rfl
/-- In `ℝ`, `polarDensity volume r = 2` for every `r : ℝ`. -/
theorem polarDensity_real_volume (r : ℝ) :
    polarDensity (volume : Measure ℝ) r = 2 := by
  have hball : (volume : Measure ℝ) (Metric.ball (0 : ℝ) 1) = 2 := by
    rw [Real.volume_ball]; norm_num
  simp [polarDensity, hball]
/-- Agreement of `μH[0] (Metric.sphere c r)` with `polarDensity volume r` and
`perimeter volume (Metric.ball c r)` in dimension `1` (`r > 0`). -/
theorem hausdorffMeasure_zero_sphere_real_eq_polarDensity (c : ℝ) {r : ℝ} (hr : 0 < r) :
    μH[0] (Metric.sphere c r) = polarDensity (volume : Measure ℝ) r := by
  rw [hausdorffMeasure_zero_sphere_real c hr, polarDensity_real_volume]
/-- Translation invariance of Hausdorff measure on spheres:
`μH[d] (Metric.sphere c r) = μH[d] (Metric.sphere 0 r)`. -/
theorem hausdorffMeasure_sphere_eq_zero_center {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (c : E) (r : ℝ) (d : ℝ) :
    μH[d] (Metric.sphere c r) = μH[d] (Metric.sphere (0 : E) r) := by
  have himg : (IsometryEquiv.vaddConst c) '' Metric.sphere (0 : E) r = Metric.sphere c r := by
    ext x
    simp only [mem_image, IsometryEquiv.vaddConst_apply, vadd_eq_add, Metric.mem_sphere,
      dist_eq_norm, sub_zero]
    exact ⟨fun ⟨y, hy, hxy⟩ ↦ by rw [← hxy, add_sub_cancel_right, hy],
      fun hx ↦ ⟨x - c, hx, sub_add_cancel x c⟩⟩
  rw [← himg, IsometryEquiv.hausdorffMeasure_image]
/-- **Translation and Dilation Scaling of Hausdorff Measure on Spheres**:
for `r > 0` and `d ≥ 0`,
`μH[d] (Metric.sphere c r) = ENNReal.ofReal (r ^ d) * μH[d] (Metric.sphere (0 : E) 1)`. -/
theorem hausdorffMeasure_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (c : E) {r : ℝ} (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
    μH[d] (Metric.sphere c r) =
      ENNReal.ofReal (r ^ d) * μH[d] (Metric.sphere (0 : E) 1) := by
  have hsmul : r • Metric.sphere (0 : E) 1 = Metric.sphere (0 : E) r := by
    ext x
    simp only [mem_smul_set, Metric.mem_sphere, dist_zero_right]
    refine ⟨fun ⟨y, hy, hxy⟩ ↦ ?_, fun hx ↦ ⟨r⁻¹ • x, ?_, smul_inv_smul₀ hr.ne' x⟩⟩
    · rw [← hxy, norm_smul, Real.norm_of_nonneg hr.le, hy, mul_one]
    · rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, hx, inv_mul_cancel₀ hr.ne']
  rw [hausdorffMeasure_sphere_eq_zero_center c r d, ← hsmul,
    MeasureTheory.Measure.hausdorffMeasure_smul₀ hd hr.ne', ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [Real.nnnorm_of_nonneg hr.le, ENNReal.coe_rpow_of_nonneg _ hd,
    ← ENNReal.ofReal_eq_coe_nnreal hr.le, ENNReal.ofReal_rpow_of_pos hr]
/-- When the unit sphere in `E` satisfies the surface normalization
`μH[n - 1] (sphere 0 1) = n * μ (ball 0 1)`, every sphere `Metric.sphere c r` (`r > 0`) satisfies
`μH[n - 1] (Metric.sphere c r) = polarDensity μ r = perimeter μ (Metric.ball c r)`. -/
theorem hausdorffMeasure_sphere_eq_polarDensity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    (hunit : μH[(Module.finrank ℝ E - 1 : ℕ)] (Metric.sphere (0 : E) 1) =
      (Module.finrank ℝ E : ℝ≥0∞) * μ (Metric.ball (0 : E) 1))
    (c : E) {r : ℝ} (hr : 0 < r) :
    μH[(Module.finrank ℝ E - 1 : ℕ)] (Metric.sphere c r) = polarDensity μ r := by
  rw [hausdorffMeasure_sphere c hr (Nat.cast_nonneg _), hunit, Real.rpow_natCast, polarDensity,
    mul_comm]
end HausdorffZeroAndSphere
end TauCeti
