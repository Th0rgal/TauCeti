/-
Copyright (c) 2026 General Intelligence, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module

public import TauCeti.MeasureTheory.Measure.BVSobolev
public import TauCeti.MeasureTheory.Function.SchwarzLp
public import TauCeti.Analysis.Calculus.Gradient
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.MeasureTheory.Measure.Regular
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.BoxPerimeter
import all TauCeti.MeasureTheory.Measure.BallPerimeter
import all TauCeti.MeasureTheory.Measure.BVSobolev
import all TauCeti.MeasureTheory.Function.SchwarzRearrangement
import all TauCeti.MeasureTheory.Function.SchwarzRadialProfile
import all TauCeti.MeasureTheory.Function.SchwarzLp

/-!
# BV Pólya–Szegő Inequality, Radial Gradient Formula, and Exclusion of Singular Variation

This file proves the `BV` Pólya–Szegő total-variation inequality for nonnegative and signed
functions under Schwarz rearrangement, establishes the radial Fréchet derivative and gradient
formula `∇(v ∘ norm)(x) = v'(‖x‖) • (‖x‖⁻¹ • x)` together with the weighted radial derivative
bound `n ω_n ∫₀^∞ |v'(r)| r^(n-1) dr ≤ |Du|(ℝⁿ)`, and proves the convex-integrand level
Pólya–Szegő inequality and de la Vallée Poussin uniform-integrability estimate excluding singular
variation on Lebesgue-null sets.

## Main Results

* `TauCeti.perimeter_superlevel_schwarzRearrangementReal`,
  `TauCeti.distributionalVariation_schwarzRearrangementReal_le`,
  `TauCeti.distributionalVariation_schwarzRearrangementReal_abs_le`.
* `TauCeti.hasFDerivAt_comp_norm`, `TauCeti.gradient_comp_norm`, `TauCeti.norm_gradient_comp_norm`,
  `TauCeti.mul_lintegral_abs_deriv_schwarzRadialProfileReal_le_distributionalVariation`.
* `TauCeti.setIntegral_polyaSzegoPerspective_le`,
  `TauCeti.setIntegral_le_mul_measure_add_of_superlinear`,
  `TauCeti.exists_threshold_setIntegral_le_mul_measure_add_of_tendsto_div_atTop`,
  `TauCeti.distributionalVariation_le_mul_volume_add_of_tendsto`,
  `TauCeti.iInf_open_distributionalVariation_eq_zero_of_measure_eq_zero`.
-/

open Filter Function InnerProductSpace MeasureTheory Pointwise Set TopologicalSpace TestFunction
open scoped ENNReal NNReal RealInnerProductSpace Gradient Distributions Topology Interval

public section

namespace TauCeti

/-! ### Section 1: BV Pólya–Szegő inequality for nonnegative and signed functions -/
/-- For `n ≠ 0`, `EuclideanSpace ℝ (Fin n)` is nontrivial. -/
instance nontrivial_euclideanSpace_of_neZero (n : ℕ) [NeZero n] :
    Nontrivial (EuclideanSpace ℝ (Fin n)) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) <| by
    rw [finrank_euclideanSpace_fin]; exact NeZero.pos n
/-- On `EuclideanSpace ℝ (Fin n)`, `bvSobolevConstant volume` is `((n : ℝ≥0∞) * ω_n^(1/n))⁻¹`. -/
theorem bvSobolevConstant_euclideanSpace (n : ℕ) :
    bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))) =
      ((n : ℝ≥0∞) * (unitBallVolume n) ^ (1 / (n : ℝ)))⁻¹ := by
  simp [bvSobolevConstant, unitBallVolume]
/-- Exact perimeter of a centered open ball `B(0, r)` (`r > 0`) in `EuclideanSpace ℝ (Fin n)`. -/
theorem perimeter_ball_zero_euclideanSpace (n : ℕ) [NeZero n] {r : ℝ} (hr : 0 < r) :
    perimeter volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) =
      (n : ℝ≥0∞) * unitBallVolume n * ENNReal.ofReal (r ^ (n - 1)) := by
  rw [perimeter_ball_eq_unitBall (0 : EuclideanSpace ℝ (Fin n)) hr, finrank_euclideanSpace_fin,
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, unitBallVolume]
  ring
/-- For `2 ≤ n` and `0 ≤ r`, `perimeter volume (B(0, r)) = n * ω_n * ofReal (r ^ (n - 1))`. -/
theorem perimeter_ball_zero_euclideanSpace_of_two_le {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    perimeter volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) =
      (n : ℝ≥0∞) * unitBallVolume n * ENNReal.ofReal (r ^ (n - 1)) := by
  have : NeZero n := ⟨by omega⟩
  rcases hr.eq_or_lt with rfl | hr_pos
  · have hk : n - 1 ≠ 0 := by omega
    simp [zero_pow hk]
  · exact perimeter_ball_zero_euclideanSpace n hr_pos
/-- Exact perimeter of `schwarzSymmetrization s` for `0 < volume s < ⊤`. -/
theorem perimeter_schwarzSymmetrization_eq_inv_bvSobolevConstant_mul_rpow_of_pos {n : ℕ} [NeZero n]
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs_pos : 0 < volume s) (hs_fin : volume s ≠ ⊤) :
    perimeter volume (schwarzSymmetrization s) =
      (bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))))⁻¹ *
        (volume s) ^ (1 / bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) := by
  have hr_pos : 0 < schwarzRadius s := (schwarzRadius_pos_iff hs_fin).2 hs_pos
  rw [schwarzSymmetrization_eq_ball hs_fin,
    perimeter_ball_eq_inv_bvSobolevConstant_mul_rpow (0 : EuclideanSpace ℝ (Fin n)) hr_pos,
    ← schwarzSymmetrization_eq_ball hs_fin, volume_schwarzSymmetrization]
/-- Exact perimeter of `schwarzSymmetrization s` for `2 ≤ n` and `volume s ≠ ⊤`. -/
theorem perimeter_schwarzSymmetrization_eq_inv_bvSobolevConstant_mul_rpow {n : ℕ} (hn : 2 ≤ n)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs_fin : volume s ≠ ⊤) :
    perimeter volume (schwarzSymmetrization s) =
      (bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))))⁻¹ *
        (volume s) ^ (1 / bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) := by
  have : NeZero n := ⟨by omega⟩
  rcases eq_or_ne (volume s) 0 with hs0 | hs0
  · have hp_pos : 0 < 1 / bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
      rw [finrank_euclideanSpace_fin, inv_bvSobolevExponent]
      have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact div_pos (by linarith) (by linarith)
    rw [schwarzSymmetrization_of_volume_eq_zero hs0, perimeter_empty, hs0,
      ENNReal.zero_rpow_of_pos hp_pos, mul_zero]
  · exact perimeter_schwarzSymmetrization_eq_inv_bvSobolevConstant_mul_rpow_of_pos
      (pos_iff_ne_zero.2 hs0) hs_fin
/-- Exact perimeter of `schwarzSymmetrization s` in terms of `unitBallVolume n` (`2 ≤ n`). -/
theorem perimeter_schwarzSymmetrization_eq_unitBallVolume_mul_rpow {n : ℕ} (hn : 2 ≤ n)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs_fin : volume s ≠ ⊤) :
    perimeter volume (schwarzSymmetrization s) =
      (n : ℝ≥0∞) * (unitBallVolume n) ^ (1 / (n : ℝ)) *
        (volume s) ^ (((n : ℝ) - 1) / (n : ℝ)) := by
  rw [perimeter_schwarzSymmetrization_eq_inv_bvSobolevConstant_mul_rpow hn hs_fin,
    bvSobolevConstant_euclideanSpace, inv_inv, finrank_euclideanSpace_fin, inv_bvSobolevExponent]
/-- For `t > 0`, `{y | t < schwarzRearrangementReal u y}` agrees a.e. with the centered ball of
radius `schwarzRadius {x | t < u x}`. -/
theorem superlevel_schwarzRearrangementReal_ae_eq_ball {n : ℕ} [NeZero n]
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤) {t : ℝ} (ht : 0 < t) :
    {y | t < schwarzRearrangementReal u y} =ᵐ[volume]
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (schwarzRadius {x | t < u x}) := by
  rw [← schwarzSymmetrization_eq_ball (hdist t ht).ne]
  exact superlevel_schwarzRearrangementReal_ae hu hdist ht.le
/-- The perimeter of `{y | t < schwarzRearrangementReal u y}` equals the perimeter of the centered
open ball of radius `schwarzRadius {x | t < u x}` (`t > 0`). -/
theorem perimeter_superlevel_schwarzRearrangementReal_eq_perimeter_ball {n : ℕ} [NeZero n]
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤) {t : ℝ} (ht : 0 < t) :
    perimeter volume {y | t < schwarzRearrangementReal u y} =
      perimeter volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (schwarzRadius {x | t < u x})) :=
  perimeter_congr_ae (superlevel_schwarzRearrangementReal_ae_eq_ball hu hdist ht)
/-- Exact perimeter of the superlevel set `{y | t < schwarzRearrangementReal u y}` (`2 ≤ n`). -/
theorem perimeter_superlevel_schwarzRearrangementReal {n : ℕ} (hn : 2 ≤ n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤) {t : ℝ} (ht : 0 < t) :
    perimeter volume {y | t < schwarzRearrangementReal u y} =
      (n : ℝ≥0∞) * (unitBallVolume n) ^ (1 / (n : ℝ)) *
        (volume {x | t < u x}) ^ (((n : ℝ) - 1) / (n : ℝ)) := by
  have : NeZero n := ⟨by omega⟩
  rw [perimeter_congr_ae (superlevel_schwarzRearrangementReal_ae hu hdist ht.le),
    perimeter_schwarzSymmetrization_eq_unitBallVolume_mul_rpow hn (hdist t ht).ne]
/-- Exact perimeter of `{y | t < schwarzRearrangementReal u y}` in `bvSobolevConstant` form. -/
theorem perimeter_superlevel_schwarzRearrangementReal_eq_inv_bvSobolevConstant {n : ℕ} (hn : 2 ≤ n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤) {t : ℝ} (ht : 0 < t) :
    perimeter volume {y | t < schwarzRearrangementReal u y} =
      (bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))))⁻¹ *
        (volume {x | t < u x}) ^
          (1 / bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) := by
  have : NeZero n := ⟨by omega⟩
  rw [perimeter_congr_ae (superlevel_schwarzRearrangementReal_ae hu hdist ht.le),
    perimeter_schwarzSymmetrization_eq_inv_bvSobolevConstant_mul_rpow hn (hdist t ht).ne]
/-- Integrated superlevel perimeter comparison under Schwarz rearrangement (`2 ≤ n`). -/
theorem lintegral_perimeter_superlevel_schwarzRearrangementReal_le {n : ℕ} (hn : 2 ≤ n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤)
    (hisop : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))))⁻¹ *
        (volume {x | t < u x}) ^
          (1 / bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) ≤
        perimeter volume {x | t < u x}) :
    ∫⁻ t in Ioi (0 : ℝ), perimeter volume {y | t < schwarzRearrangementReal u y} ≤
      ∫⁻ t in Ioi (0 : ℝ), perimeter volume {x | t < u x} := by
  refine lintegral_mono_ae ?_
  filter_upwards [hisop, ae_restrict_mem measurableSet_Ioi] with t ht ht_pos
  rwa [perimeter_superlevel_schwarzRearrangementReal_eq_inv_bvSobolevConstant hn hu hdist ht_pos]
/-- **BV Pólya–Szegő Inequality for Nonnegative / Positive-Part Functions (`2 ≤ n`)**:
`|D(u*)|(ℝⁿ) ≤ |Du|(ℝⁿ)`. -/
theorem distributionalVariation_schwarzRearrangementReal_le {n : ℕ} (hn : 2 ≤ n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤)
    (hloc : LocallyIntegrable (schwarzRearrangementReal u) volume)
    (hcoarea : ∫⁻ t in Ioi (0 : ℝ), perimeter volume {x | t < u x} ≤
      distributionalVariation volume ⊤ u)
    (hisop : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))))⁻¹ *
        (volume {x | t < u x}) ^
          (1 / bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) ≤
        perimeter volume {x | t < u x}) :
    distributionalVariation volume ⊤ (schwarzRearrangementReal u) ≤
      distributionalVariation volume ⊤ u :=
  (distributionalVariation_top_le_lintegral_perimeter_superlevel hloc
    (schwarzRearrangementReal_nonneg u)).trans
    ((lintegral_perimeter_superlevel_schwarzRearrangementReal_le hn hu hdist hisop).trans hcoarea)
/-- Decomposition of `|a|` into positive and negative parts: `max a 0 + max (-a) 0 = |a|`. -/
theorem max_zero_add_max_neg_zero (a : ℝ) : max a 0 + max (-a) 0 = |a| := by
  rcases le_total 0 a with ha | ha
  · rw [max_eq_left ha, max_eq_right (neg_nonpos.2 ha), abs_of_nonneg ha, add_zero]
  · rw [max_eq_right ha, max_eq_left (neg_nonneg.2 ha), abs_of_nonpos ha, zero_add]
section SignedTruncation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [SFinite μ]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [SFinite μ] in
/-- If `u` is locally integrable on `Ω`, so is its positive part `fun x ↦ max (u x) 0`. -/
theorem locallyIntegrableOn_posPart {Ω : Opens E} {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ) :
    LocallyIntegrableOn (fun x ↦ max (u x) 0) Ω μ := by
  have heq : (fun x ↦ max (u x) 0) = (2⁻¹ : ℝ) • (u + fun x ↦ ‖u x‖) := by
    ext x; dsimp
    rcases le_total 0 (u x) with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_nonpos h, max_eq_right h]; ring
  rw [heq]
  exact fun x hx ↦ ((hu x hx).add (hu.norm x hx)).smul (2⁻¹ : ℝ)
/-- Variation of the positive part `u⁺ = max u 0` is bounded by its superlevel perimeter
integral. -/
theorem distributionalVariation_posPart_le_lintegral_perimeter {Ω : Opens E} {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) :
    distributionalVariation μ Ω (fun x ↦ max (u x) 0) ≤
      ∫⁻ t in Ioi (0 : ℝ), relativePerimeter μ Ω {x | t < u x} := by
  refine (distributionalVariation_le_lintegral_relativePerimeter_superlevel
    (locallyIntegrableOn_posPart hu) (fun x _ ↦ le_max_right _ _)).trans_eq
    (setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_)
  congr 1; ext x; exact lt_max_iff.trans (or_iff_left (not_lt.2 (mem_Ioi.1 ht).le))
/-- Variation of the negative part `(-u)⁺ = max (-u) 0` is bounded by its sublevel perimeter
integral. -/
theorem distributionalVariation_negPart_le_lintegral_perimeter {Ω : Opens E} {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) :
    distributionalVariation μ Ω (fun x ↦ max (-u x) 0) ≤
      ∫⁻ t in Ioi (0 : ℝ), relativePerimeter μ Ω {x | u x < -t} := by
  have h1 := distributionalVariation_posPart_le_lintegral_perimeter (hu := hu.neg)
  refine h1.trans_eq (setLIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_)
  congr 1; ext x; exact lt_neg
omit [SFinite μ] in
/-- Variation of `|u| = u⁺ + (-u)⁺` is bounded by the sum of variations of `u⁺` and `(-u)⁺`. -/
theorem distributionalVariation_abs_le_add_posPart_negPart {Ω : Opens E} {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) :
    distributionalVariation μ Ω (fun x ↦ |u x|) ≤
      distributionalVariation μ Ω (fun x ↦ max (u x) 0) +
        distributionalVariation μ Ω (fun x ↦ max (-u x) 0) := by
  have heq : (fun x ↦ |u x|) = (fun x ↦ max (u x) 0) + (fun x ↦ max (-u x) 0) := by
    ext x; exact (max_zero_add_max_neg_zero (u x)).symm
  rw [heq]
  exact distributionalVariation_add_le (locallyIntegrableOn_posPart hu)
    (locallyIntegrableOn_posPart hu.neg)
/-- Variation of `|u|` is bounded by the sum of positive and negative superlevel perimeters. -/
theorem distributionalVariation_abs_le_add_lintegral_perimeter {u : E → ℝ}
    (hu : LocallyIntegrable u μ) :
    distributionalVariation μ ⊤ (fun x ↦ |u x|) ≤
      (∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | t < u x}) +
        ∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | u x < -t} :=
  (distributionalVariation_abs_le_add_posPart_negPart (hu.locallyIntegrableOn ⊤)).trans
    (add_le_add (distributionalVariation_posPart_le_lintegral_perimeter (hu.locallyIntegrableOn ⊤))
      (distributionalVariation_negPart_le_lintegral_perimeter (hu.locallyIntegrableOn ⊤)))
/-- When the two-sided coarea equality holds for `u`, `|D|u||(E) ≤ |Du|(E)`. -/
theorem distributionalVariation_abs_le {u : E → ℝ} (hu : LocallyIntegrable u μ)
    (hcoarea : (∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | t < u x}) +
      ∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | u x < -t} ≤ distributionalVariation μ ⊤ u) :
    distributionalVariation μ ⊤ (fun x ↦ |u x|) ≤ distributionalVariation μ ⊤ u :=
  (distributionalVariation_abs_le_add_lintegral_perimeter hu).trans hcoarea
end SignedTruncation
/-- **Signed BV Pólya–Szegő Superlevel Perimeter Bound (`2 ≤ n`)**:
`∫₀^∞ P({|u|* > t}) dt ≤ ∫₀^∞ P({u > t}) dt + ∫₀^∞ P({u < -t}) dt`. -/
theorem lintegral_perimeter_superlevel_schwarzRearrangementReal_abs_le {n : ℕ} (hn : 2 ≤ n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEStronglyMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < |u x|} < ⊤)
    (hisop : HasSuperlevelIsoperimetry (volume : Measure (EuclideanSpace ℝ (Fin n))) u) :
    ∫⁻ t in Ioi (0 : ℝ),
        perimeter volume {y | t < schwarzRearrangementReal (fun x ↦ |u x|) y} ≤
      (∫⁻ t in Ioi (0 : ℝ), perimeter volume {x | t < u x}) +
        ∫⁻ t in Ioi (0 : ℝ), perimeter volume {x | u x < -t} := by
  have : NeZero n := ⟨by omega⟩
  set C := (bvSobolevConstant (volume : Measure (EuclideanSpace ℝ (Fin n))))⁻¹
  set p := bvSobolevExponent (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
  have hp : 1 ≤ p := (one_lt_bvSobolevExponent (by rwa [finrank_euclideanSpace_fin])).le
  have hanti₁ : AntitoneOn (fun t : ℝ ↦ C * (volume {x | t < u x}) ^ (1 / p)) (Ioi 0) :=
    fun a _ b _ hab ↦ mul_le_mul_of_nonneg_left
      (ENNReal.rpow_le_rpow (measure_mono fun x hx ↦ hab.trans_lt hx) (by positivity)) zero_le
  have h1 : ∫⁻ t in Ioi (0 : ℝ),
        perimeter volume {y | t < schwarzRearrangementReal (fun x ↦ |u x|) y} ≤
      (∫⁻ t in Ioi (0 : ℝ), C * (volume {x | t < u x}) ^ (1 / p)) +
        ∫⁻ t in Ioi (0 : ℝ), C * (volume {x | u x < -t}) ^ (1 / p) := by
    rw [← lintegral_add_left' (aemeasurable_of_antitoneOn_Ioi_ennreal hanti₁)]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hu_abs : AEMeasurable (fun x ↦ |u x|) volume := by
      simpa only [Real.norm_eq_abs] using hu.norm.aemeasurable
    rw [perimeter_superlevel_schwarzRearrangementReal_eq_inv_bvSobolevConstant hn
      hu_abs hdist ht, ← mul_add]
    exact mul_le_mul_of_nonneg_left (measure_abs_lt_rpow_inv_le hu hp ht) zero_le
  exact h1.trans (add_le_add (lintegral_mono_ae hisop.1) (lintegral_mono_ae hisop.2))
/-- **BV Pólya–Szegő Inequality for Signed Real Functions (`2 ≤ n`)**:
`|D(|u|*)|(ℝⁿ) ≤ |Du|(ℝⁿ)`. -/
theorem distributionalVariation_schwarzRearrangementReal_abs_le {n : ℕ} (hn : 2 ≤ n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEStronglyMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < |u x|} < ⊤)
    (hloc : LocallyIntegrable (schwarzRearrangementReal (fun x ↦ |u x|)) volume)
    (hcoarea : (∫⁻ t in Ioi (0 : ℝ), perimeter volume {x | t < u x}) +
      ∫⁻ t in Ioi (0 : ℝ), perimeter volume {x | u x < -t} ≤
        distributionalVariation volume ⊤ u)
    (hisop : HasSuperlevelIsoperimetry (volume : Measure (EuclideanSpace ℝ (Fin n))) u) :
    distributionalVariation volume ⊤ (schwarzRearrangementReal (fun x ↦ |u x|)) ≤
      distributionalVariation volume ⊤ u :=
  (distributionalVariation_top_le_lintegral_perimeter_superlevel hloc
    (schwarzRearrangementReal_nonneg _)).trans
    ((lintegral_perimeter_superlevel_schwarzRearrangementReal_abs_le hn hu hdist hisop).trans
      hcoarea)
/-! ### Section 2: Radial Fréchet derivative, gradient formula, and weighted radial variation -/
section RadialDerivative
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- At any `x ≠ 0` in a real inner product space, `y ↦ ‖y‖` has strict Fréchet derivative
`‖x‖⁻¹ • innerSL ℝ x`. -/
theorem hasStrictFDerivAt_norm {x : E} (hx : x ≠ 0) :
    HasStrictFDerivAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).rpow_const (p := 1 / 2) (by simp [hx])
  convert h using 1
  · ext y; rw [← Real.rpow_natCast_mul (norm_nonneg y)]; norm_num
  · rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← Real.rpow_natCast_mul (norm_nonneg x)]
    norm_num; rw [Real.rpow_neg_one]; ring_nf
/-- At any `x ≠ 0` in a real inner product space, `y ↦ ‖y‖` has Fréchet derivative
`‖x‖⁻¹ • innerSL ℝ x`. -/
theorem hasFDerivAt_norm {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x :=
  (hasStrictFDerivAt_norm hx).hasFDerivAt
/-- At any `x ≠ 0`, `fderiv ℝ (fun y : E ↦ ‖y‖) x = ‖x‖⁻¹ • innerSL ℝ x`. -/
theorem fderiv_norm {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E ↦ ‖y‖) x = ‖x‖⁻¹ • innerSL ℝ x :=
  (hasFDerivAt_norm hx).fderiv
/-- Chain rule for a radial function `y ↦ v ‖y‖` at `x ≠ 0`. -/
theorem hasFDerivAt_comp_norm {v : ℝ → ℝ} {v' : ℝ} {x : E} (hx : x ≠ 0)
    (hv : HasDerivAt v v' ‖x‖) :
    HasFDerivAt (fun y : E ↦ v ‖y‖) ((v' * ‖x‖⁻¹) • innerSL ℝ x) x := by
  have hd := hv.comp_hasFDerivAt x (hasFDerivAt_norm hx)
  rwa [smul_smul] at hd
/-- Fréchet derivative of a radial function `y ↦ v ‖y‖` at `x ≠ 0`. -/
theorem fderiv_comp_norm {v : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hv : DifferentiableAt ℝ v ‖x‖) :
    fderiv ℝ (fun y : E ↦ v ‖y‖) x = (deriv v ‖x‖ * ‖x‖⁻¹) • innerSL ℝ x :=
  (hasFDerivAt_comp_norm hx hv.hasDerivAt).fderiv
/-- Operator norm of the Fréchet derivative of `y ↦ v ‖y‖` at `x ≠ 0`:
`‖fderiv ℝ (fun y ↦ v ‖y‖) x‖ = |deriv v ‖x‖|`. -/
theorem norm_fderiv_comp_norm {v : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hv : DifferentiableAt ℝ v ‖x‖) :
    ‖fderiv ℝ (fun y : E ↦ v ‖y‖) x‖ = |deriv v ‖x‖| := by
  rw [fderiv_comp_norm hx hv, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul,
    abs_inv, abs_norm, mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx), mul_one]
/-- Vanishing of the tangential directional derivative of `y ↦ v ‖y‖` along any vector `w`
orthogonal to `x` (`⟪x, w⟫ = 0`). -/
theorem fderiv_comp_norm_apply_eq_zero_of_inner_eq_zero {v : ℝ → ℝ} {x w : E} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ v ‖x‖) (hw : ⟪x, w⟫ = 0) :
    fderiv ℝ (fun y : E ↦ v ‖y‖) x w = 0 := by
  rw [fderiv_comp_norm hx hv, smul_apply, innerSL_apply_apply, hw, smul_zero]
/-- At `x ≠ 0` in a Hilbert space `E`, `y ↦ ‖y‖` has gradient `‖x‖⁻¹ • x`. -/
theorem hasGradientAt_norm [CompleteSpace E] {x : E} (hx : x ≠ 0) :
    HasGradientAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt,
    show toDual ℝ E (‖x‖⁻¹ • x) = ‖x‖⁻¹ • innerSL ℝ x by ext y; simp]
  exact hasFDerivAt_norm hx
/-- At `x ≠ 0` in a Hilbert space `E`, `y ↦ v ‖y‖` has gradient `v' • (‖x‖⁻¹ • x)`. -/
theorem hasGradientAt_comp_norm [CompleteSpace E] {v : ℝ → ℝ} {v' : ℝ} {x : E} (hx : x ≠ 0)
    (hv : HasDerivAt v v' ‖x‖) :
    HasGradientAt (fun y : E ↦ v ‖y‖) (v' • (‖x‖⁻¹ • x)) x := by
  have h : toDual ℝ E (v' • (‖x‖⁻¹ • x)) = (v' * ‖x‖⁻¹) • innerSL ℝ x := by ext y; simp [mul_assoc]
  rw [hasGradientAt_iff_hasFDerivAt, h]
  exact hasFDerivAt_comp_norm hx hv
/-- **Radial Gradient Formula** (`x ≠ 0`):
`∇ (fun y ↦ v ‖y‖) x = deriv v ‖x‖ • (‖x‖⁻¹ • x)`. -/
theorem gradient_comp_norm [CompleteSpace E] {v : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ v ‖x‖) :
    ∇ (fun y : E ↦ v ‖y‖) x = deriv v ‖x‖ • (‖x‖⁻¹ • x) :=
  (hasGradientAt_comp_norm hx hv.hasDerivAt).gradient
/-- Quotient form of the radial gradient formula:
`∇ (fun y ↦ v ‖y‖) x = (deriv v ‖x‖ / ‖x‖) • x`. -/
theorem gradient_comp_norm_eq_div_smul [CompleteSpace E] {v : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ v ‖x‖) :
    ∇ (fun y : E ↦ v ‖y‖) x = (deriv v ‖x‖ / ‖x‖) • x := by
  rw [gradient_comp_norm hx hv, smul_smul, div_eq_mul_inv]
/-- Norm of the gradient of a radial function `y ↦ v ‖y‖` at `x ≠ 0`:
`‖∇ (fun y ↦ v ‖y‖) x‖ = |deriv v ‖x‖|`. -/
theorem norm_gradient_comp_norm [CompleteSpace E] {v : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ v ‖x‖) :
    ‖∇ (fun y : E ↦ v ‖y‖) x‖ = |deriv v ‖x‖| := by
  rw [norm_gradient_eq_norm_fderiv, norm_fderiv_comp_norm hx hv]
/-- Vanishing of the tangential component of `∇ (fun y ↦ v ‖y‖) x` orthogonal to `x`. -/
theorem inner_gradient_comp_norm_eq_zero_of_inner_eq_zero [CompleteSpace E] {v : ℝ → ℝ} {x w : E}
    (hx : x ≠ 0) (hv : DifferentiableAt ℝ v ‖x‖) (hw : ⟪x, w⟫ = 0) :
    ⟪∇ (fun y : E ↦ v ‖y‖) x, w⟫ = 0 := by
  rw [inner_gradient_left, fderiv_comp_norm_apply_eq_zero_of_inner_eq_zero hx hv hw]
end RadialDerivative
/-- Fundamental theorem of calculus for `s ↦ (k : ℝ) * s ^ (k - 1)` on `(0, r)` in `lintegral`
form (`k ≥ 1`, `r ≥ 0`). -/
theorem lintegral_Ioo_mul_pow_pred {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in Ioi (0 : ℝ), (Ioo 0 r).indicator (fun s ↦ ENNReal.ofReal ((k : ℝ) * s ^ (k - 1))) s =
      ENNReal.ofReal (r ^ k) := by
  rw [setLIntegral_indicator measurableSet_Ioo, inter_eq_self_of_subset_left Ioo_subset_Ioi_self]
  have hcont : Continuous (fun s : ℝ ↦ (k : ℝ) * s ^ (k - 1)) := by fun_prop
  have hint : IntegrableOn (fun s : ℝ ↦ (k : ℝ) * s ^ (k - 1)) (Ioo 0 r) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).1
      (hcont.intervalIntegrable 0 r) |>.mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs ↦
      mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hs.1.le _)),
    restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hr]
  have hd : ∀ s ∈ uIcc 0 r, HasDerivAt (fun x : ℝ ↦ x ^ k) ((k : ℝ) * s ^ (k - 1)) s :=
    fun s _ ↦ hasDerivAt_pow k s
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable 0 r),
    zero_pow (Nat.one_le_iff_ne_zero.1 hk), sub_zero]
/-- **1D Weighted Radial Derivative Integral Bound (`k ≥ 1`)**: for any antitone function
`v : ℝ → ℝ` that is nonnegative on `(0, ∞)` and absolutely continuous on compact intervals in
`(0, ∞)`,
`∫₀^∞ |deriv v r| r^k dr ≤ ∫₀^∞ k s^(k-1) v(s) ds`. -/
theorem lintegral_abs_deriv_mul_pow_le {v : ℝ → ℝ} (hv : Antitone v) (hv_nn : ∀ r > 0, 0 ≤ v r)
    (hAC : ∀ a b, 0 < a → a ≤ b → AbsolutelyContinuousOnInterval v a b) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (|deriv v r| * r ^ k) ≤
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((k : ℝ) * s ^ (k - 1)) * ENNReal.ofReal (v s) := by
  have hmeas_d : Measurable (fun r : ℝ ↦ ENNReal.ofReal |deriv v r|) := by fun_prop
  have hbound_R : ∀ R : ℝ, 0 < R →
      ∫⁻ r in Ioo 0 R, ENNReal.ofReal (|deriv v r| * r ^ k) ≤
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((k : ℝ) * s ^ (k - 1)) * ENNReal.ofReal (v s) := by
    intro R hR
    have h1 : ∫⁻ r in Ioo 0 R, ENNReal.ofReal (|deriv v r| * r ^ k) =
        ∫⁻ r in Ioo 0 R, ∫⁻ s in Ioi (0 : ℝ),
          (Ioo 0 r).indicator (fun s ↦
            ENNReal.ofReal |deriv v r| * ENNReal.ofReal ((k : ℝ) * s ^ (k - 1))) s := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
      rw [ENNReal.ofReal_mul (abs_nonneg _), ← lintegral_Ioo_mul_pow_pred hk hr.1.le,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioi fun s _ ↦ ?_
      by_cases hsr : s ∈ Ioo 0 r <;> simp [hsr]
    rw [h1, lintegral_lintegral_swap]
    · refine setLIntegral_mono' measurableSet_Ioi fun s hs ↦ ?_
      by_cases hsR : s < R
      · have hset : ∀ r ∈ Ioo 0 R,
            (Ioo 0 r).indicator (fun s ↦
              ENNReal.ofReal |deriv v r| * ENNReal.ofReal ((k : ℝ) * s ^ (k - 1))) s =
            (Ioo s R).indicator (fun r ↦
              ENNReal.ofReal ((k : ℝ) * s ^ (k - 1)) * ENNReal.ofReal |deriv v r|) r := by
          intro r hr
          have : (s ∈ Ioo 0 r) ↔ (r ∈ Ioo s R) := ⟨fun h ↦ ⟨h.2, hr.2⟩, fun h ↦ ⟨hs, h.1⟩⟩
          by_cases hsr : s ∈ Ioo 0 r
          · rw [indicator_of_mem hsr, indicator_of_mem (this.1 hsr), mul_comm]
          · rw [indicator_of_notMem hsr, indicator_of_notMem (mt this.2 hsr)]
        rw [setLIntegral_congr_fun measurableSet_Ioo hset,
          setLIntegral_indicator measurableSet_Ioo,
          inter_eq_self_of_subset_left (Ioo_subset_Ioo_left hs.le),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        have hint : IntegrableOn (fun r ↦ |deriv v r|) (Ioo s R) volume :=
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hsR.le).1
            (hAC s R hs hsR.le).intervalIntegrable_deriv.abs).mono_set Ioo_subset_Ioc_self
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun _ ↦ abs_nonneg _),
          restrict_Ioo_eq_restrict_Ioc,
          setIntegral_Ioc_abs_deriv_eq_sub_of_antitone hv hsR.le (hAC s R hs hsR.le)]
        exact ENNReal.ofReal_le_ofReal (sub_le_self _ (hv_nn R hR))
      · have h0 : ∀ r ∈ Ioo 0 R,
            (Ioo 0 r).indicator (fun s ↦
              ENNReal.ofReal |deriv v r| * ENNReal.ofReal ((k : ℝ) * s ^ (k - 1))) s = 0 := by
          intro r hr; exact indicator_of_notMem (fun (hsr : s ∈ Ioo 0 r) ↦ hsR (hsr.2.trans hr.2)) _
        rw [setLIntegral_congr_fun measurableSet_Ioo h0, lintegral_zero]; exact zero_le
    · refine Measurable.aemeasurable ?_
      have hS : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioo 0 p.1} :=
        (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_fst)
      have hF : Measurable (fun p : ℝ × ℝ ↦
          ENNReal.ofReal |deriv v p.1| * ENNReal.ofReal ((k : ℝ) * p.2 ^ (k - 1))) :=
        (hmeas_d.comp measurable_fst).mul (by fun_prop)
      exact hF.indicator hS
  have hcov : Ioi (0 : ℝ) = ⋃ m : ℕ, Ioo (0 : ℝ) (m + 1 : ℝ) := by
    ext r; simp only [mem_Ioi, mem_iUnion, mem_Ioo]
    exact ⟨fun hr ↦ (exists_nat_gt r).imp fun m hm ↦ ⟨hr, hm.trans (lt_add_one _)⟩,
      fun ⟨_, hr, _⟩ ↦ hr⟩
  have hmono : Monotone (fun m : ℕ ↦ Ioo (0 : ℝ) (m + 1 : ℝ)) :=
    fun a b hab ↦ Ioo_subset_Ioo_right (by exact_mod_cast Nat.add_le_add_right hab 1)
  conv_lhs => rw [hcov, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  exact iSup_le fun m ↦ hbound_R (m + 1 : ℝ) (Nat.cast_add_one_pos m)
/-- Layer-cake identity for the weighted radial profile integral (`k ≥ 1`). -/
theorem lintegral_mul_pow_pred_schwarzRadialProfileReal_eq {n : ℕ} [NeZero n]
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal ((k : ℝ) * s ^ (k - 1)) * ENNReal.ofReal (schwarzRadialProfileReal u s) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (schwarzRadius {x | t < u x} ^ k) := by
  set v := schwarzRadialProfileReal u
  have hv_meas : Measurable v :=
    (measurable_schwarzRadialProfile (fun x ↦ ENNReal.ofReal (u x))).ennreal_toReal
  have h1 : ∀ s ∈ Ioi (0 : ℝ),
      ENNReal.ofReal ((k : ℝ) * s ^ (k - 1)) * ENNReal.ofReal (v s) =
        ∫⁻ t in Ioi (0 : ℝ),
          {p : ℝ × ℝ | p.2 < v p.1}.indicator
            (fun p ↦ ENNReal.ofReal ((k : ℝ) * p.1 ^ (k - 1))) (s, t) := by
    intro s hs
    have hconst : ∫⁻ t in Ioi (0 : ℝ),
        {p : ℝ × ℝ | p.2 < v p.1}.indicator
          (fun p ↦ ENNReal.ofReal ((k : ℝ) * p.1 ^ (k - 1))) (s, t) =
      ∫⁻ t in Ioi (0 : ℝ),
        (Ioo 0 (v s)).indicator (fun _ ↦ ENNReal.ofReal ((k : ℝ) * s ^ (k - 1))) t := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have : ((s, t) ∈ {p : ℝ × ℝ | p.2 < v p.1}) ↔ t ∈ Ioo 0 (v s) :=
        ⟨fun h ↦ ⟨ht, h⟩, fun h ↦ h.2⟩
      by_cases htv : t ∈ Ioo 0 (v s)
      · rw [indicator_of_mem (this.2 htv), indicator_of_mem htv]
      · rw [indicator_of_notMem (mt this.1 htv), indicator_of_notMem htv]
    rw [hconst, setLIntegral_indicator measurableSet_Ioo,
      inter_eq_self_of_subset_left Ioo_subset_Ioi_self,
      setLIntegral_const, Real.volume_Ioo, sub_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_lintegral_swap]
  · refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [← lintegral_Ioo_mul_pow_pred hk (schwarzRadius_nonneg {x | t < u x})]
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
    have hiff : ((s, t) ∈ {p : ℝ × ℝ | p.2 < v p.1}) ↔ s ∈ Ioo 0 (schwarzRadius {x | t < u x}) := by
      simp only [Set.mem_ofPred_eq, mem_Ioo]
      rw [lt_schwarzRadialProfileReal_iff_lt_schwarzRadius hu hdist hs ht.le (hdist t ht).ne]
      exact ⟨fun h ↦ ⟨hs, h⟩, fun h ↦ h.2⟩
    by_cases hsR : s ∈ Ioo 0 (schwarzRadius {x | t < u x})
    · rw [indicator_of_mem (hiff.2 hsR), indicator_of_mem hsR]
    · rw [indicator_of_notMem (mt hiff.1 hsR), indicator_of_notMem hsR]
  · refine Measurable.aemeasurable ?_
    have hS : MeasurableSet {p : ℝ × ℝ | p.2 < v p.1} :=
      measurableSet_lt measurable_snd (hv_meas.comp measurable_fst)
    exact (by fun_prop : Measurable fun p : ℝ × ℝ ↦
      ENNReal.ofReal ((k : ℝ) * p.1 ^ (k - 1))).indicator hS
/-- **Weighted Radial Derivative Bound by Superlevel Perimeter (`2 ≤ n`)**:
`n * ω_n * ∫₀^∞ |v'(r)| r^(n-1) dr ≤ ∫₀^∞ P({u* > t}) dt`. -/
theorem mul_lintegral_abs_deriv_schwarzRadialProfileReal_le_lintegral_perimeter {n : ℕ}
    (hn : 2 ≤ n) {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : AEMeasurable u volume)
    (hdist : ∀ s : ℝ, 0 < s → volume {x | s < u x} < ⊤)
    (hv_anti : Antitone (schwarzRadialProfileReal u))
    (hAC : ∀ a b, 0 < a → a ≤ b →
      AbsolutelyContinuousOnInterval (schwarzRadialProfileReal u) a b) :
    (n : ℝ≥0∞) * unitBallVolume n *
        ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal (|deriv (schwarzRadialProfileReal u) r| * r ^ (n - 1)) ≤
      ∫⁻ t in Ioi (0 : ℝ), perimeter volume {y | t < schwarzRearrangementReal u y} := by
  have : NeZero n := ⟨by omega⟩
  have hk : 1 ≤ n - 1 := by omega
  have h1 := (lintegral_abs_deriv_mul_pow_le hv_anti
    (fun r _ ↦ schwarzRadialProfileReal_nonneg u r) hAC hk).trans_eq
    (lintegral_mul_pow_pred_schwarzRadialProfileReal_eq hu hdist hk)
  refine (mul_le_mul_of_nonneg_left h1 zero_le).trans_eq ?_
  rw [← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (unitBallVolume_ne_top n))]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  rw [perimeter_superlevel_schwarzRearrangementReal_eq_perimeter_ball hu hdist ht,
    perimeter_ball_zero_euclideanSpace_of_two_le hn (schwarzRadius_nonneg _)]
/-- **Weighted Radial Derivative Bound by Total Variation (`2 ≤ n`)**:
`n * ω_n * ∫₀^∞ |v'(r)| r^(n-1) dr ≤ |Du|(ℝⁿ)`. -/
theorem mul_lintegral_abs_deriv_schwarzRadialProfileReal_le_distributionalVariation {n : ℕ}
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
    (n : ℝ≥0∞) * unitBallVolume n *
        ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal (|deriv (schwarzRadialProfileReal u) r| * r ^ (n - 1)) ≤
      distributionalVariation volume ⊤ u :=
  (mul_lintegral_abs_deriv_schwarzRadialProfileReal_le_lintegral_perimeter hn hu hdist hv_anti
    hAC).trans
    ((lintegral_perimeter_superlevel_schwarzRearrangementReal_le hn hu hdist hisop).trans hcoarea)
/-! ### Section 3: Convex-integrand level Pólya–Szegő, de la Vallée Poussin, and null variation -/
/-- Integrated `lintegral` convex-integrand level Pólya–Szegő inequality on `(0, ∞)`. -/
theorem lintegral_polyaSzegoPerspective_le {Φ m mStar P PStar : ℝ → ℝ}
    (hΦ_conv : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (hΦ_mono : MonotoneOn Φ (Ici (0 : ℝ)))
    (hΦ0 : Φ 0 ≤ 0)
    (hm_pos : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 < m t)
    (hm_le : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), m t ≤ mStar t)
    (hP_nn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ PStar t)
    (hP_le : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), PStar t ≤ P t) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (polyaSzegoPerspective Φ (mStar t) (PStar t)) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (polyaSzegoPerspective Φ (m t) (P t)) := by
  refine lintegral_mono_ae ?_
  filter_upwards [hm_pos, hm_le, hP_nn, hP_le] with t h1 h2 h3 h4
  exact ENNReal.ofReal_le_ofReal
    (polyaSzegoPerspective_le_of_le_of_le hΦ_conv hΦ_mono hΦ0 h3 h4 h1 h2)
/-- Integrated Bochner-integral convex-integrand level Pólya–Szegő inequality on `(0, ∞)`. -/
theorem setIntegral_polyaSzegoPerspective_le {Φ m mStar P PStar : ℝ → ℝ}
    (hΦ_conv : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (hΦ_mono : MonotoneOn Φ (Ici (0 : ℝ)))
    (hΦ0 : Φ 0 ≤ 0)
    (hm_pos : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 < m t)
    (hm_le : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), m t ≤ mStar t)
    (hP_nn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ PStar t)
    (hP_le : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), PStar t ≤ P t)
    (hintStar : IntegrableOn (fun t ↦ polyaSzegoPerspective Φ (mStar t) (PStar t)) (Ioi 0) volume)
    (hint : IntegrableOn (fun t ↦ polyaSzegoPerspective Φ (m t) (P t)) (Ioi 0) volume) :
    ∫ t in Ioi (0 : ℝ), polyaSzegoPerspective Φ (mStar t) (PStar t) ≤
      ∫ t in Ioi (0 : ℝ), polyaSzegoPerspective Φ (m t) (P t) := by
  refine setIntegral_mono_ae_restrict hintStar hint ?_
  filter_upwards [hm_pos, hm_le, hP_nn, hP_le] with t h1 h2 h3 h4
  exact polyaSzegoPerspective_le_of_le_of_le hΦ_conv hΦ_mono hΦ0 h3 h4 h1 h2
/-- Integrated level Pólya–Szegő combined with level-set Jensen upper bound `G`. -/
theorem setIntegral_polyaSzegoPerspective_le_setIntegral {Φ m mStar P PStar G : ℝ → ℝ}
    (hΦ_conv : ConvexOn ℝ (Ici (0 : ℝ)) Φ) (hΦ_mono : MonotoneOn Φ (Ici (0 : ℝ)))
    (hΦ0 : Φ 0 ≤ 0)
    (hm_pos : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 < m t)
    (hm_le : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), m t ≤ mStar t)
    (hP_nn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ PStar t)
    (hP_le : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), PStar t ≤ P t)
    (hG : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), polyaSzegoPerspective Φ (m t) (P t) ≤ G t)
    (hintStar : IntegrableOn (fun t ↦ polyaSzegoPerspective Φ (mStar t) (PStar t)) (Ioi 0) volume)
    (hintG : IntegrableOn G (Ioi 0) volume) :
    ∫ t in Ioi (0 : ℝ), polyaSzegoPerspective Φ (mStar t) (PStar t) ≤
      ∫ t in Ioi (0 : ℝ), G t := by
  refine setIntegral_mono_ae_restrict hintStar hintG ?_
  filter_upwards [hm_pos, hm_le, hP_nn, hP_le, hG] with t h1 h2 h3 h4 h5
  exact (polyaSzegoPerspective_le_of_le_of_le hΦ_conv hΦ_mono hΦ0 h3 h4 h1 h2).trans h5
/-- Pointwise de la Vallée Poussin bound: if `Φ ≥ 0` on `[0, ∞)` and `K * t ≤ Φ t` for `t ≥ T`,
then `t ≤ T + Φ t / K` for all `t ≥ 0`. -/
theorem le_add_div_of_superlinear {Φ : ℝ → ℝ} (hΦ_nn : ∀ t ≥ 0, 0 ≤ Φ t)
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 < K) (hsuper : ∀ t ≥ T, K * t ≤ Φ t)
    {t : ℝ} (ht : 0 ≤ t) :
    t ≤ T + Φ t / K := by
  rcases lt_or_ge t T with hlt | hge
  · have : 0 ≤ Φ t / K := div_nonneg (hΦ_nn t ht) hK.le
    linarith
  · have : t ≤ Φ t / K := (le_div_iff₀ hK).2 (by linarith [hsuper t hge])
    linarith
/-- **De La Vallée Poussin Superlinear Tail Bound (`lintegral` form)**:
`∫⁻ x in A, ofReal (w x) ∂μ ≤ ofReal T * μ A + ofReal (M / K)`. -/
theorem lintegral_le_mul_measure_add_of_superlinear {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Φ : ℝ → ℝ} (hΦ_nn : ∀ t ≥ 0, 0 ≤ Φ t)
    {T K M : ℝ} (hT : 0 ≤ T) (hK : 0 < K) (hM_nn : 0 ≤ M) (hsuper : ∀ t ≥ T, K * t ≤ Φ t)
    {w : α → ℝ} (hw_nn : ∀ x, 0 ≤ w x) (hM : ∫⁻ x, ENNReal.ofReal (Φ (w x)) ∂μ ≤ ENNReal.ofReal M)
    (A : Set α) :
    ∫⁻ x in A, ENNReal.ofReal (w x) ∂μ ≤
      ENNReal.ofReal T * μ A + ENNReal.ofReal (M / K) := by
  have h1 : ∫⁻ x in A, ENNReal.ofReal (w x) ∂μ ≤
      ∫⁻ x in A, (ENNReal.ofReal T + ENNReal.ofReal (Φ (w x)) * ENNReal.ofReal K⁻¹) ∂μ := by
    refine lintegral_mono fun x ↦ ?_
    rw [← ENNReal.ofReal_mul (hΦ_nn (w x) (hw_nn x)), ← div_eq_mul_inv,
      ← ENNReal.ofReal_add hT (div_nonneg (hΦ_nn (w x) (hw_nn x)) hK.le)]
    exact ENNReal.ofReal_le_ofReal (le_add_div_of_superlinear hΦ_nn hT hK hsuper (hw_nn x))
  rw [lintegral_add_left' measurable_const.aemeasurable, setLIntegral_const,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top] at h1
  refine h1.trans (add_le_add le_rfl ?_)
  have hle : (∫⁻ x in A, ENNReal.ofReal (Φ (w x)) ∂μ) * ENNReal.ofReal K⁻¹ ≤
      ENNReal.ofReal M * ENNReal.ofReal K⁻¹ :=
    mul_le_mul_of_nonneg_right ((setLIntegral_le_lintegral A _).trans hM) zero_le
  rwa [← ENNReal.ofReal_mul hM_nn, ← div_eq_mul_inv] at hle
/-- **De La Vallée Poussin Superlinear Tail Bound (Bochner integral form)**:
`∫ x in A, w x ∂μ ≤ T * (μ A).toReal + M / K`. -/
theorem setIntegral_le_mul_measure_add_of_superlinear {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Φ : ℝ → ℝ} (hΦ_nn : ∀ t ≥ 0, 0 ≤ Φ t)
    {T K M : ℝ} (hT : 0 ≤ T) (hK : 0 < K) (hM_nn : 0 ≤ M) (hsuper : ∀ t ≥ T, K * t ≤ Φ t)
    {w : α → ℝ} (hw_nn : ∀ x, 0 ≤ w x) (hw_int : Integrable w μ)
    (hΦw_int : Integrable (fun x ↦ Φ (w x)) μ) (hM : ∫ x, Φ (w x) ∂μ ≤ M)
    {A : Set α} (hA_fin : μ A ≠ ⊤) :
    ∫ x in A, w x ∂μ ≤ T * (μ A).toReal + M / K := by
  have hM' : ∫⁻ x, ENNReal.ofReal (Φ (w x)) ∂μ ≤ ENNReal.ofReal M := by
    rw [← ofReal_integral_eq_lintegral_ofReal hΦw_int
      (Eventually.of_forall fun x ↦ hΦ_nn (w x) (hw_nn x))]
    exact ENNReal.ofReal_le_ofReal hM
  have h1 := lintegral_le_mul_measure_add_of_superlinear hΦ_nn hT hK hM_nn hsuper hw_nn hM' A
  rw [← ofReal_integral_eq_lintegral_ofReal hw_int.integrableOn
    (Eventually.of_forall hw_nn), ← ENNReal.ofReal_toReal hA_fin,
    ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_add (mul_nonneg hT ENNReal.toReal_nonneg)
    (div_nonneg hM_nn hK.le)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (mul_nonneg hT ENNReal.toReal_nonneg) (div_nonneg hM_nn hK.le))).1 h1
/-- **De La Vallée Poussin Uniform Integrability Criterion**: if `Φ(t) / t → ∞` as `t → ∞` and
`∫ Φ(w_j) ≤ M`, then for every `ε > 0` there is `T > 0` such that
`∫ x in A, w j x ∂μ ≤ T * (μ A).toReal + ε` uniformly in `j` and `A`. -/
theorem exists_threshold_setIntegral_le_mul_measure_add_of_tendsto_div_atTop
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {Φ : ℝ → ℝ} (hΦ_nn : ∀ t ≥ 0, 0 ≤ Φ t)
    (htend : Tendsto (fun t : ℝ ↦ Φ t / t) atTop atTop)
    {M : ℝ} (hM_nn : 0 ≤ M) {w : ι → α → ℝ} (hw_nn : ∀ j x, 0 ≤ w j x)
    (hw_int : ∀ j, Integrable (w j) μ) (hΦw_int : ∀ j, Integrable (fun x ↦ Φ (w j x)) μ)
    (hM : ∀ j, ∫ x, Φ (w j x) ∂μ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∀ j : ι, ∀ A : Set α, μ A ≠ ⊤ →
      ∫ x in A, w j x ∂μ ≤ T * (μ A).toReal + ε := by
  let K : ℝ := (M + 1) / ε
  have hK : 0 < K := div_pos (by linarith) hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (htend.eventually_ge_atTop K)
  let T : ℝ := max T₀ 1
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right T₀ 1)
  have hsuper : ∀ t ≥ T, K * t ≤ Φ t := fun t ht ↦ by
    have ht_pos : 0 < t := hT_pos.trans_le ht
    exact (le_div_iff₀ ht_pos).1 (hT₀ t ((le_max_left T₀ 1).trans ht))
  refine ⟨T, hT_pos, fun j A hA_fin ↦ ?_⟩
  have hMK : M / K ≤ ε := by
    rw [div_le_iff₀ hK]
    have : ε * K = M + 1 := mul_div_cancel₀ (M + 1) hε.ne'
    linarith
  exact (setIntegral_le_mul_measure_add_of_superlinear hΦ_nn hT_pos.le hK hM_nn hsuper
    (hw_nn j) (hw_int j) (hΦw_int j) (hM j) hA_fin).trans (add_le_add le_rfl hMK)
section ExclusionOfSingularVariation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
/-- Convergence in `L¹(μ.restrict Ω)` implies convergence of `∫ x in Ω, uSeq j x * divergence φ x`
for every test vector field `φ : 𝓓(Ω, E)`. -/
theorem tendsto_integral_mul_divergence_of_tendsto_eLpNorm_one
    {Ω : Opens E} {ι : Type*} {l : Filter ι} {uSeq : ι → E → ℝ} {u : E → ℝ}
    (huSeq : ∀ j, LocallyIntegrableOn (uSeq j) Ω μ) (hu : LocallyIntegrableOn u Ω μ)
    (htend : Tendsto (fun j ↦ eLpNorm (uSeq j - u) 1 (μ.restrict Ω)) l (𝓝 0))
    (φ : 𝓓(Ω, E)) :
    Tendsto (fun j ↦ ∫ x in (Ω : Set E), uSeq j x * divergence (φ : E → E) x ∂μ) l
      (𝓝 (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ)) := by
  obtain ⟨C, hC⟩ := (continuous_divergence_testFunction φ).norm.bddAbove_range_of_hasCompactSupport
    (hasCompactSupport_divergence_testFunction φ).norm
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlim : Tendsto (fun j ↦ ENNReal.ofReal C * eLpNorm (uSeq j - u) 1 (μ.restrict Ω)) l
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))] with j hj
  rw [Real.dist_eq, ← integral_sub (integrableOn_mul_divergence_of_locallyIntegrableOn (huSeq j) φ)
    (integrableOn_mul_divergence_of_locallyIntegrableOn hu φ)]
  have hbound : ENNReal.ofReal |∫ x in (Ω : Set E),
      (uSeq j x * divergence (φ : E → E) x - u x * divergence (φ : E → E) x) ∂μ| ≤
      ENNReal.ofReal C * eLpNorm (uSeq j - u) 1 (μ.restrict Ω) := by
    rw [← Real.enorm_eq_ofReal_abs, MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    · refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x ↦ ?_)
      rw [← sub_mul, Real.enorm_eq_ofReal_abs, Pi.sub_apply, Real.enorm_eq_ofReal_abs,
        abs_mul, mul_comm |uSeq j x - u x|, ENNReal.ofReal_mul (abs_nonneg _)]
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hC ⟨x, rfl⟩)) zero_le
    · exact (huSeq j).aestronglyMeasurable.sub hu.aestronglyMeasurable
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (hbound.trans_lt hj)
/-- **Lower Semicontinuity of Variation under `L¹` Convergence**: if `uSeq j → u` in `L¹(Ω)`, then
`|Du|(Ω) ≤ liminf_{j → l} |Du_j|(Ω)`. -/
theorem distributionalVariation_le_liminf_of_tendsto_eLpNorm_one
    {Ω : Opens E} {ι : Type*} {l : Filter ι} {uSeq : ι → E → ℝ} {u : E → ℝ}
    (huSeq : ∀ j, LocallyIntegrableOn (uSeq j) Ω μ) (hu : LocallyIntegrableOn u Ω μ)
    (htend : Tendsto (fun j ↦ eLpNorm (uSeq j - u) 1 (μ.restrict Ω)) l (𝓝 0)) :
    distributionalVariation μ Ω u ≤
      liminf (fun j ↦ distributionalVariation μ Ω (uSeq j)) l :=
  distributionalVariation_le_liminf
    (tendsto_integral_mul_divergence_of_tendsto_eLpNorm_one huSeq hu htend)
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Passage of Uniform-Integrability Variation Bound to the Limit**: if
`|Du_lim|(U) ≤ liminf |Du_j|(U)` for every open `U` and `|Du_j|(U) ≤ T μ(U) + ε` uniformly in `j`,
then `|Du_lim|(U) ≤ T μ(U) + ε` for every open `U`. -/
theorem distributionalVariation_le_mul_volume_add_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {uSeq : ι → E → ℝ} {u : E → ℝ}
    (hlsc : ∀ U : Opens E,
      distributionalVariation μ U u ≤ liminf (fun j ↦ distributionalVariation μ U (uSeq j)) l)
    {T ε : ℝ} (hbound : ∀ j : ι, ∀ U : Opens E,
      distributionalVariation μ U (uSeq j) ≤ ENNReal.ofReal T * μ (U : Set E) + ENNReal.ofReal ε)
    (U : Opens E) :
    distributionalVariation μ U u ≤ ENNReal.ofReal T * μ (U : Set E) + ENNReal.ofReal ε :=
  (hlsc U).trans (liminf_le_of_frequently_le' (Eventually.of_forall fun j ↦ hbound j U).frequently)
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Exclusion of Singular Variation on Null Sets**: if `μ` is outer regular and for every `ε > 0`
there exists `T ≥ 0` such that `|Du|(U) ≤ T μ(U) + ε` for every open `U`, then for every set `N`
with `μ N = 0`, the outer variation `⨅ (U : Opens E) (_ : N ⊆ U), |Du|(U)` vanishes. -/
theorem iInf_open_distributionalVariation_eq_zero_of_measure_eq_zero [μ.OuterRegular] {u : E → ℝ}
    (hUI : ∀ ε > 0, ∃ T ≥ 0, ∀ U : Opens E,
      distributionalVariation μ U u ≤ ENNReal.ofReal T * μ (U : Set E) + ENNReal.ofReal ε)
    {N : Set E} (hN : μ N = 0) :
    (⨅ (U : Opens E) (_ : N ⊆ (U : Set E)), distributionalVariation μ U u) = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun δ hδ ↦ ?_) zero_le
  rw [zero_add]
  rcases eq_or_ne δ ⊤ with rfl | hδ_top
  · exact le_top
  have hδ_real : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδ_top
  obtain ⟨T, hT_nn, hT⟩ := hUI (δ.toReal / 2) (half_pos hδ_real)
  let η : ℝ := δ.toReal / (2 * (T + 1))
  have hη_pos : 0 < η := div_pos hδ_real (by linarith)
  obtain ⟨V, hNV, hV_open, hμV⟩ :=
    Set.exists_isOpen_lt_of_lt N (ENNReal.ofReal η) (hN ▸ ENNReal.ofReal_pos.2 hη_pos)
  refine iInf₂_le_of_le ⟨V, hV_open⟩ hNV ?_
  calc
    distributionalVariation μ ⟨V, hV_open⟩ u
      ≤ ENNReal.ofReal T * μ V + ENNReal.ofReal (δ.toReal / 2) := hT ⟨V, hV_open⟩
    _ ≤ ENNReal.ofReal T * ENNReal.ofReal η + ENNReal.ofReal (δ.toReal / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hμV.le zero_le) le_rfl
    _ ≤ ENNReal.ofReal (δ.toReal / 2) + ENNReal.ofReal (δ.toReal / 2) := by
        refine add_le_add ?_ le_rfl
        rw [← ENNReal.ofReal_mul hT_nn]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : T * η ≤ (T + 1) * η := mul_le_mul_of_nonneg_right (by linarith) hη_pos.le
        have h2 : (T + 1) * η = δ.toReal / 2 := by
          dsimp [η]; rw [← mul_div_assoc, mul_comm (T + 1), div_mul_eq_div_div_swap,
            mul_div_cancel_right₀ _ (by linarith)]
        linarith
    _ = δ := by
        rw [← ENNReal.ofReal_add (half_pos hδ_real).le (half_pos hδ_real).le, add_halves,
          ENNReal.ofReal_toReal hδ_top]
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Exclusion of Point-Mass Atoms**: under the uniform-integrability variation bound, the outer
variation of `u` at any singleton `{x}` (in particular at the origin `{0}`) is `0`. -/
theorem iInf_open_distributionalVariation_singleton_eq_zero [μ.OuterRegular]
    [NullSingletonClass μ] {u : E → ℝ}
    (hUI : ∀ ε > 0, ∃ T ≥ 0, ∀ U : Opens E,
      distributionalVariation μ U u ≤ ENNReal.ofReal T * μ (U : Set E) + ENNReal.ofReal ε)
    (x : E) :
    (⨅ (U : Opens E) (_ : ({x} : Set E) ⊆ (U : Set E)), distributionalVariation μ U u) = 0 :=
  iInf_open_distributionalVariation_eq_zero_of_measure_eq_zero hUI (measure_singleton x)
/-- **Exclusion of Spherical Jumps**: under the uniform-integrability variation bound, the outer
variation of `u` on any sphere `Metric.sphere c r` vanishes (`[Nontrivial E]`). -/
theorem iInf_open_distributionalVariation_sphere_eq_zero [Nontrivial E] [μ.IsAddHaarMeasure]
    {u : E → ℝ}
    (hUI : ∀ ε > 0, ∃ T ≥ 0, ∀ U : Opens E,
      distributionalVariation μ U u ≤ ENNReal.ofReal T * μ (U : Set E) + ENNReal.ofReal ε)
    (c : E) (r : ℝ) :
    (⨅ (U : Opens E) (_ : Metric.sphere c r ⊆ (U : Set E)), distributionalVariation μ U u) = 0 :=
  iInf_open_distributionalVariation_eq_zero_of_measure_eq_zero hUI (Measure.addHaar_sphere μ c r)
end ExclusionOfSingularVariation
end TauCeti
