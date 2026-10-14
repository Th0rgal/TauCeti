/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
import all TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
import all TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski
import all TauCeti.MeasureTheory.Measure.Lebesgue.PrekopaLeindler
import all TauCeti.MeasureTheory.Measure.MinkowskiContent

/-!
# Brunn–Minkowski Homothety Calculus, Scale Reductions, Support Widths, and Ball Rigidity

This file establishes the positive-homothety and Brunn–Minkowski equality infrastructure for
`Isoperimetry` Milestones I1 (`Isoperimetry/README.md` lines 136–142) and I4 (lines 273–276):
1. **Positive-homothety relation `IsPositiveHomothetic A B` (`B = {c} + r • A`, `0 < r`),
   translate relation `IsTranslateOf A B` (`B = {c} + A`), ball homothety, and exact Brunn–Minkowski
   equality for homothetic convex sets**:
   `TauCeti.IsTranslateOf`, `TauCeti.IsPositiveHomothetic`,
   `TauCeti.isPositiveHomothetic_iff_isTranslateOf_of_measure_eq`,
   `TauCeti.isPositiveHomothetic_closedBall_zero_one_iff`,
   `TauCeti.isPositiveHomothetic_ball_zero_one_iff`,
   `TauCeti.weighted_brunnMinkowski_eq_of_isPositiveHomothetic`, and
   `TauCeti.unweighted_brunnMinkowski_eq_of_isPositiveHomothetic`.
2. **Weighted-to-unweighted reduction via `θ = 1 / 2` on `2 • A` and `2 • B` & equal-volume
   normalization (`bmScale`, `bmNormalized`, `bmNormalizedSet`, `bmWeight`)**:
   `TauCeti.add_eq_half_smul_two_smul_add_half_smul_two_smul`,
   `TauCeti.unweighted_brunnMinkowski_eq_iff_weighted_half_two_smul`,
   `TauCeti.isPositiveHomothetic_two_smul_iff`,
   `TauCeti.isPositiveHomothetic_of_unweighted_brunnMinkowski_eq_of_weighted_half`,
   `TauCeti.bmScale`, `TauCeti.bmNormalizedSet`, `TauCeti.bmWeight`,
   `TauCeti.weighted_brunnMinkowski_eq_iff_equal_volume`, and
   `TauCeti.isTranslateOf_bmNormalizedSet_iff_isPositiveHomothetic`.
3. **Positive-volume vs nonempty-interior bridge, unconditional 1D compact convex homothety,
   directional support width `supportWidth`, coordinate-box homothety, and Milestone I4 convex-body
   ball rigidity bridge**:
   `Convex.interior_nonempty_iff_measure_pos`,
   `TauCeti.isPositiveHomothetic_of_isCompact_of_convex_real`,
   `TauCeti.unweighted_brunnMinkowski_eq_iff_isPositiveHomothetic_real`,
   `TauCeti.weighted_brunnMinkowski_eq_iff_isPositiveHomothetic_real`,
   `TauCeti.supportWidth`, `TauCeti.supportWidth_add`,
   `TauCeti.supportWidth_of_isPositiveHomothetic`, `TauCeti.isPositiveHomothetic_Icc_pi_iff`,
   `TauCeti.unweighted_brunnMinkowski_eq_closedBall_of_minkowskiContent_eq`,
   `TauCeti.eq_closedBall_and_ae_eq_ball_of_isPositiveHomothetic_closedBall`, and
   `TauCeti.eq_closedBall_and_ae_eq_ball_of_minkowskiContent_eq`.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology
open TauCeti.MeasureTheory

namespace TauCeti

/-! ### Section 1: Positive homothety `IsPositiveHomothetic`, ball characterization & BM equality -/
section PositiveHomothety
variable {E : Type*} [AddCommGroup E]
/-- `IsTranslateOf A B` means `B` is a translate `{c} + A` of `A`. -/
def IsTranslateOf (A B : Set E) : Prop := ∃ c : E, B = {c} + A
@[refl] theorem IsTranslateOf.refl (A : Set E) : IsTranslateOf A A := ⟨0, by simp⟩
@[symm] theorem IsTranslateOf.symm {A B : Set E} (h : IsTranslateOf A B) : IsTranslateOf B A := by
  rcases h with ⟨c, rfl⟩
  exact ⟨-c, by rw [← add_assoc, singleton_add_singleton, neg_add_cancel, singleton_zero, zero_add]⟩
@[trans] theorem IsTranslateOf.trans {A B C : Set E} (hAB : IsTranslateOf A B)
    (hBC : IsTranslateOf B C) : IsTranslateOf A C := by
  rcases hAB with ⟨c₁, rfl⟩; rcases hBC with ⟨c₂, rfl⟩
  exact ⟨c₂ + c₁, by rw [← add_assoc, singleton_add_singleton]⟩

variable [Module ℝ E]
/-- `IsPositiveHomothetic A B` means `B = {c} + r • A` for some `c : E` and `r > 0`. -/
def IsPositiveHomothetic (A B : Set E) : Prop := ∃ (c : E) (r : ℝ), 0 < r ∧ B = {c} + r • A
/-- Every translate of `A` is positively homothetic to `A` (with `r = 1`). -/
theorem IsTranslateOf.isPositiveHomothetic {A B : Set E} (h : IsTranslateOf A B) :
    IsPositiveHomothetic A B := by rcases h with ⟨c, rfl⟩; exact ⟨c, 1, one_pos, by simp⟩
@[refl] theorem IsPositiveHomothetic.refl (A : Set E) : IsPositiveHomothetic A A :=
  (IsTranslateOf.refl A).isPositiveHomothetic
theorem smul_singleton_eq (r : ℝ) (c : E) : r • ({c} : Set E) = {r • c} :=
  Set.image_singleton
@[symm] theorem IsPositiveHomothetic.symm {A B : Set E} (h : IsPositiveHomothetic A B) :
    IsPositiveHomothetic B A := by
  rcases h with ⟨c, r, hr, rfl⟩
  refine ⟨-(r⁻¹ • c), r⁻¹, inv_pos.2 hr, ?_⟩
  rw [smul_add, smul_singleton_eq, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, ← add_assoc,
    singleton_add_singleton, neg_add_cancel, singleton_zero, zero_add]
@[trans] theorem IsPositiveHomothetic.trans {A B C : Set E} (hAB : IsPositiveHomothetic A B)
    (hBC : IsPositiveHomothetic B C) : IsPositiveHomothetic A C := by
  rcases hAB with ⟨c₁, r₁, hr₁, rfl⟩; rcases hBC with ⟨c₂, r₂, hr₂, rfl⟩
  refine ⟨c₂ + r₂ • c₁, r₂ * r₁, mul_pos hr₂ hr₁, ?_⟩
  rw [smul_add, smul_singleton_eq, smul_smul, ← add_assoc, singleton_add_singleton]
theorem IsPositiveHomothetic.nonempty_iff {A B : Set E} (h : IsPositiveHomothetic A B) :
    A.Nonempty ↔ B.Nonempty := by
  rcases h with ⟨c, r, _, rfl⟩
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨c + r • a, c, rfl, r • a, ⟨a, ha, rfl⟩, rfl⟩,
    fun ⟨_, _, rfl, _, ⟨a, ha, rfl⟩, _⟩ ↦ ⟨a, ha⟩⟩
/-- Convex Minkowski combination identity when `B = {c} + r • A` (`a, b, r ≥ 0`):
`a • A + b • B = {b • c} + (a + b * r) • A`. -/
theorem smul_add_smul_singleton_add_smul_of_convex {A B : Set E} (hA : Convex ℝ A)
    {c : E} {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hB : B = {c} + r • A) :
    a • A + b • B = {b • c} + (a + b * r) • A := by
  rw [hB, smul_add, smul_singleton_eq, smul_smul, add_left_comm,
    ← hA.add_smul ha (mul_nonneg hb hr)]
/-- Unweighted Minkowski sum identity when `B = {c} + r • A` (`r ≥ 0`):
`A + B = {c} + (1 + r) • A`. -/
theorem add_singleton_add_smul_of_convex {A B : Set E} (hA : Convex ℝ A)
    {c : E} {r : ℝ} (hr : 0 ≤ r) (hB : B = {c} + r • A) :
    A + B = {c} + (1 + r) • A := by
  simpa using smul_add_smul_singleton_add_smul_of_convex hA zero_le_one zero_le_one hr hB
end PositiveHomothety

section NormedPositiveHomothety
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Translating and dilating `Metric.closedBall (0 : E) 1` by `c` and `r > 0` yields
`Metric.closedBall c r`. -/
theorem singleton_add_smul_closedBall_zero_one (c : E) {r : ℝ} (hr : 0 < r) :
    {c} + r • Metric.closedBall (0 : E) 1 = Metric.closedBall c r := by
  ext x; simp only [singleton_add, mem_image, mem_smul_set, Metric.mem_closedBall,
    dist_eq_norm, sub_zero]
  refine ⟨?_, fun hx ↦ ⟨x - c, ⟨r⁻¹ • (x - c), ?_, smul_inv_smul₀ hr.ne' _⟩, add_sub_cancel _ _⟩⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le hy
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul, div_le_one hr]
    exact hx
/-- Translating and dilating `Metric.ball (0 : E) 1` by `c` and `r > 0` yields `Metric.ball c r`. -/
theorem singleton_add_smul_ball_zero_one (c : E) {r : ℝ} (hr : 0 < r) :
    {c} + r • Metric.ball (0 : E) 1 = Metric.ball c r := by
  ext x; simp only [singleton_add, mem_image, mem_smul_set, Metric.mem_ball,
    dist_eq_norm, sub_zero]
  refine ⟨?_, fun hx ↦ ⟨x - c, ⟨r⁻¹ • (x - c), ?_, smul_inv_smul₀ hr.ne' _⟩, add_sub_cancel _ _⟩⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_of_lt_one_right hr hy
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul, div_lt_one hr]
    exact hx
/-- **Characterization of sets positively homothetic to `Metric.closedBall (0 : E) 1`**. -/
theorem isPositiveHomothetic_closedBall_zero_one_iff {K : Set E} :
    IsPositiveHomothetic (Metric.closedBall (0 : E) 1) K ↔
      ∃ (c : E) (r : ℝ), 0 < r ∧ K = Metric.closedBall c r :=
  ⟨by rintro ⟨c, r, hr, rfl⟩; exact ⟨c, r, hr, singleton_add_smul_closedBall_zero_one c hr⟩,
   by rintro ⟨c, r, hr, rfl⟩; exact ⟨c, r, hr, (singleton_add_smul_closedBall_zero_one c hr).symm⟩⟩
/-- **Characterization of sets positively homothetic to `Metric.ball (0 : E) 1`**. -/
theorem isPositiveHomothetic_ball_zero_one_iff {K : Set E} :
    IsPositiveHomothetic (Metric.ball (0 : E) 1) K ↔
      ∃ (c : E) (r : ℝ), 0 < r ∧ K = Metric.ball c r :=
  ⟨by rintro ⟨c, r, hr, rfl⟩; exact ⟨c, r, hr, singleton_add_smul_ball_zero_one c hr⟩,
   by rintro ⟨c, r, hr, rfl⟩; exact ⟨c, r, hr, (singleton_add_smul_ball_zero_one c hr).symm⟩⟩

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
/-- Haar measure root scaling under `B = {c} + r • A` (`0 ≤ r`, `1 ≤ dim E`). -/
theorem measure_rpow_inv_finrank_of_eq_singleton_add_smul {A B : Set E} {c : E} {r : ℝ}
    (hr : 0 ≤ r) (hB : B = {c} + r • A) (hn : 1 ≤ Module.finrank ℝ E) :
    μ B ^ (1 / (Module.finrank ℝ E : ℝ)) =
      ENNReal.ofReal r * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rw [hB, measure_singleton_add, measure_smul_rpow_inv_finrank_of_nonneg μ hr A hn]
/-- Haar measure `.toReal` root scaling under `B = {c} + r • A` (`0 ≤ r`, `1 ≤ dim E`). -/
theorem measure_toReal_rpow_inv_finrank_of_eq_singleton_add_smul {A B : Set E} {c : E} {r : ℝ}
    (hr : 0 ≤ r) (hB : B = {c} + r • A) (hn : 1 ≤ Module.finrank ℝ E) :
    (μ B).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
      r * (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have h := congrArg ENNReal.toReal (measure_rpow_inv_finrank_of_eq_singleton_add_smul μ hr hB hn)
  simpa [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr] using h
/-- **Equal-measure positive homothety is translation**: if `1 ≤ dim E`, `0 < μ A < ⊤`, and
`μ A = μ B`, then `IsPositiveHomothetic A B ↔ IsTranslateOf A B`. -/
theorem isPositiveHomothetic_iff_isTranslateOf_of_measure_eq (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hA_pos : 0 < μ A) (hA_top : μ A ≠ ⊤) (hAB : μ A = μ B) :
    IsPositiveHomothetic A B ↔ IsTranslateOf A B := by
  refine ⟨?_, IsTranslateOf.isPositiveHomothetic⟩; rintro ⟨c, r, hr, hB⟩
  set p : ℝ := 1 / (Module.finrank ℝ E : ℝ); have hp : 0 < p := by positivity
  have hAp_0 : μ A ^ p ≠ 0 := (ENNReal.rpow_pos hA_pos hA_top).ne'
  have hAp_top : μ A ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le hA_top
  have hscale := measure_rpow_inv_finrank_of_eq_singleton_add_smul μ hr.le hB hn
  rw [← hAB] at hscale
  have hr1_enn : ENNReal.ofReal r = 1 :=
    (ENNReal.mul_left_inj hAp_0 hAp_top).1 (by rw [← hscale, one_mul])
  have hr1 : r = 1 := by
    simpa [ENNReal.toReal_ofReal hr.le] using congrArg ENNReal.toReal hr1_enn
  exact ⟨c, by simpa [hr1] using hB⟩
/-- **Converse of weighted Brunn–Minkowski equality for positively homothetic convex sets**
(`ℝ≥0∞` form). -/
theorem weighted_brunnMinkowski_ennreal_eq_of_isPositiveHomothetic (hn : 1 ≤ Module.finrank ℝ E)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) {A B : Set E} (hA : Convex ℝ A)
    (hAB : IsPositiveHomothetic A B) :
    μ ((1 - θ) • A + θ • B) ^ (1 / (Module.finrank ℝ E : ℝ)) =
      ENNReal.ofReal (1 - θ) * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) +
        ENNReal.ofReal θ * μ B ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rcases hAB with ⟨c, r, hr, hB⟩; have h1θ : 0 ≤ 1 - θ := sub_nonneg.2 hθ₁
  rw [smul_add_smul_singleton_add_smul_of_convex hA h1θ hθ₀ hr.le hB, measure_singleton_add,
    measure_smul_rpow_inv_finrank_of_nonneg μ (by positivity) A hn,
    measure_rpow_inv_finrank_of_eq_singleton_add_smul μ hr.le hB hn,
    ENNReal.ofReal_add h1θ (mul_nonneg hθ₀ hr.le), ENNReal.ofReal_mul hθ₀, add_mul, mul_assoc]
/-- **Converse of unweighted Brunn–Minkowski equality for positively homothetic convex sets**
(`ℝ≥0∞` form). -/
theorem unweighted_brunnMinkowski_ennreal_eq_of_isPositiveHomothetic (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hA : Convex ℝ A) (hAB : IsPositiveHomothetic A B) :
    μ (A + B) ^ (1 / (Module.finrank ℝ E : ℝ)) =
      μ A ^ (1 / (Module.finrank ℝ E : ℝ)) + μ B ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rcases hAB with ⟨c, r, hr, hB⟩
  rw [add_singleton_add_smul_of_convex hA hr.le hB, measure_singleton_add,
    measure_smul_rpow_inv_finrank_of_nonneg μ (by positivity) A hn,
    measure_rpow_inv_finrank_of_eq_singleton_add_smul μ hr.le hB hn,
    ENNReal.ofReal_add zero_le_one hr.le, ENNReal.ofReal_one, add_mul, one_mul]
/-- **Converse of weighted Brunn–Minkowski equality for positively homothetic convex sets**
(real-valued `.toReal` form). -/
theorem weighted_brunnMinkowski_eq_of_isPositiveHomothetic (hn : 1 ≤ Module.finrank ℝ E)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) {A B : Set E} (hA : Convex ℝ A)
    (hAB : IsPositiveHomothetic A B) :
    (μ ((1 - θ) • A + θ • B)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
      (1 - θ) * (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) +
        θ * (μ B).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rcases hAB with ⟨c, r, hr, hB⟩; have h1θ : 0 ≤ 1 - θ := sub_nonneg.2 hθ₁
  rw [measure_toReal_rpow_inv_finrank_of_eq_singleton_add_smul μ (by positivity)
      (smul_add_smul_singleton_add_smul_of_convex hA h1θ hθ₀ hr.le hB) hn,
    measure_toReal_rpow_inv_finrank_of_eq_singleton_add_smul μ hr.le hB hn]
  ring
/-- **Converse of unweighted Brunn–Minkowski equality for positively homothetic convex sets**
(real-valued `.toReal` form). -/
theorem unweighted_brunnMinkowski_eq_of_isPositiveHomothetic (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hA : Convex ℝ A) (hAB : IsPositiveHomothetic A B) :
    (μ (A + B)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
      (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) +
        (μ B).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rcases hAB with ⟨c, r, hr, hB⟩
  rw [measure_toReal_rpow_inv_finrank_of_eq_singleton_add_smul μ (by positivity)
      (add_singleton_add_smul_of_convex hA hr.le hB) hn,
    measure_toReal_rpow_inv_finrank_of_eq_singleton_add_smul μ hr.le hB hn]
  ring
end NormedPositiveHomothety

/-! ### Section 2: Weighted-to-unweighted (`θ = 1/2` on `2 • A, 2 • B`) & equal-volume reductions -/
section WeightedToUnweightedAndScaleReduction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Rescaling `(2 : ℝ) • A` by `1 / 2` recovers `A`. -/
theorem half_smul_two_smul (A : Set E) : (1 / 2 : ℝ) • ((2 : ℝ) • A) = A := by
  rw [smul_smul, one_div_mul_cancel two_ne_zero, one_smul]
/-- **Minkowski sum as unweighted midpoint combination of `2 • A` and `2 • B`**
(`Isoperimetry/README.md` lines 139–142). -/
theorem add_eq_half_smul_two_smul_add_half_smul_two_smul (A B : Set E) :
    A + B = (1 / 2 : ℝ) • ((2 : ℝ) • A) + (1 / 2 : ℝ) • ((2 : ℝ) • B) := by
  rw [half_smul_two_smul, half_smul_two_smul]
/-- `IsPositiveHomothetic` is invariant under simultaneous dilation by `2`. -/
@[simp] theorem isPositiveHomothetic_two_smul_iff (A B : Set E) :
    IsPositiveHomothetic ((2 : ℝ) • A) ((2 : ℝ) • B) ↔ IsPositiveHomothetic A B := by
  refine ⟨?_, ?_⟩
  · rintro ⟨c, r, hr, h2⟩
    have h := congrArg (fun s : Set E ↦ (1 / 2 : ℝ) • s) h2
    rw [smul_smul, one_div_mul_cancel two_ne_zero, one_smul, smul_add, smul_singleton_eq,
      smul_smul, smul_smul, mul_comm (1 / 2 : ℝ) r, mul_assoc,
      one_div_mul_cancel two_ne_zero, mul_one] at h
    exact ⟨(1 / 2 : ℝ) • c, r, hr, h⟩
  · rintro ⟨c, r, hr, rfl⟩
    refine ⟨(2 : ℝ) • c, r, hr, ?_⟩
    rw [smul_add, smul_singleton_eq, smul_smul, smul_smul, mul_comm (2 : ℝ) r]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
/-- Scaling of `μ ((2 : ℝ) • A) ^ (1 / dim E)` (`ℝ≥0∞` form). -/
theorem measure_two_smul_rpow_inv_finrank (hn : 1 ≤ Module.finrank ℝ E) (A : Set E) :
    μ ((2 : ℝ) • A) ^ (1 / (Module.finrank ℝ E : ℝ)) =
      2 * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  simpa using measure_smul_rpow_inv_finrank_of_nonneg μ zero_le_two A hn
/-- Scaling of `(μ ((2 : ℝ) • A)).toReal ^ (1 / dim E)` (real-valued form). -/
theorem measure_two_smul_toReal_rpow_inv_finrank (hn : 1 ≤ Module.finrank ℝ E) (A : Set E) :
    (μ ((2 : ℝ) • A)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
      2 * (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have h := congrArg ENNReal.toReal (measure_two_smul_rpow_inv_finrank μ hn A)
  simpa [← ENNReal.toReal_rpow, ENNReal.toReal_mul] using h
/-- **Equivalence between unweighted Brunn–Minkowski equality for `(A, B)` and weighted
Brunn–Minkowski equality at `θ = 1 / 2` for `((2 : ℝ) • A, (2 : ℝ) • B)`** (`ℝ≥0∞` form). -/
theorem unweighted_brunnMinkowski_ennreal_eq_iff_weighted_half_two_smul
    (hn : 1 ≤ Module.finrank ℝ E) (A B : Set E) :
    μ (A + B) ^ (1 / (Module.finrank ℝ E : ℝ)) =
        μ A ^ (1 / (Module.finrank ℝ E : ℝ)) + μ B ^ (1 / (Module.finrank ℝ E : ℝ)) ↔
      μ ((1 / 2 : ℝ) • ((2 : ℝ) • A) + (1 / 2 : ℝ) • ((2 : ℝ) • B)) ^
          (1 / (Module.finrank ℝ E : ℝ)) =
        ENNReal.ofReal (1 / 2 : ℝ) * μ ((2 : ℝ) • A) ^ (1 / (Module.finrank ℝ E : ℝ)) +
          ENNReal.ofReal (1 / 2 : ℝ) * μ ((2 : ℝ) • B) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) * 2 = 1 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
      one_div_mul_cancel two_ne_zero, ENNReal.ofReal_one]
  rw [← add_eq_half_smul_two_smul_add_half_smul_two_smul A B,
    measure_two_smul_rpow_inv_finrank μ hn A, measure_two_smul_rpow_inv_finrank μ hn B,
    ← mul_assoc, ← mul_assoc, hhalf, one_mul, one_mul]
/-- **Equivalence between unweighted Brunn–Minkowski equality for `(A, B)` and weighted
Brunn–Minkowski equality at `θ = 1 / 2` for `((2 : ℝ) • A, (2 : ℝ) • B)`** (real-valued form). -/
theorem unweighted_brunnMinkowski_eq_iff_weighted_half_two_smul
    (hn : 1 ≤ Module.finrank ℝ E) (A B : Set E) :
    (μ (A + B)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
        (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) +
          (μ B).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) ↔
      (μ ((1 / 2 : ℝ) • ((2 : ℝ) • A) + (1 / 2 : ℝ) • ((2 : ℝ) • B))).toReal ^
          (1 / (Module.finrank ℝ E : ℝ)) =
        (1 / 2 : ℝ) * (μ ((2 : ℝ) • A)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) +
          (1 / 2 : ℝ) * (μ ((2 : ℝ) • B)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rw [← add_eq_half_smul_two_smul_add_half_smul_two_smul A B,
    measure_two_smul_toReal_rpow_inv_finrank μ hn A,
    measure_two_smul_toReal_rpow_inv_finrank μ hn B]
  ring_nf
/-- **Weighted-to-unweighted homothety transfer (`Isoperimetry/README.md` lines 139–142)**:
if weighted Brunn–Minkowski equality at `θ = 1 / 2` for `((2 : ℝ) • A, (2 : ℝ) • B)` implies
`IsPositiveHomothetic ((2 : ℝ) • A) ((2 : ℝ) • B)`, then unweighted Brunn–Minkowski equality for
`(A, B)` implies `IsPositiveHomothetic A B`. -/
theorem isPositiveHomothetic_of_unweighted_brunnMinkowski_eq_of_weighted_half
    (hn : 1 ≤ Module.finrank ℝ E) {A B : Set E}
    (h_weighted :
      (μ ((1 / 2 : ℝ) • ((2 : ℝ) • A) + (1 / 2 : ℝ) • ((2 : ℝ) • B))).toReal ^
          (1 / (Module.finrank ℝ E : ℝ)) =
        (1 / 2 : ℝ) * (μ ((2 : ℝ) • A)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) +
          (1 / 2 : ℝ) * (μ ((2 : ℝ) • B)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) →
      IsPositiveHomothetic ((2 : ℝ) • A) ((2 : ℝ) • B))
    (h_unweighted :
      (μ (A + B)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
        (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) +
          (μ B).toReal ^ (1 / (Module.finrank ℝ E : ℝ))) :
    IsPositiveHomothetic A B :=
  (isPositiveHomothetic_two_smul_iff A B).1
    (h_weighted ((unweighted_brunnMinkowski_eq_iff_weighted_half_two_smul μ hn A B).1 h_unweighted))
/-- **Brunn–Minkowski relative dilation factor**:
`bmScale μ A B = ((μ B).toReal / (μ A).toReal) ^ (1 / dim E)`. -/
def bmScale (A B : Set E) : ℝ :=
  ((μ B).toReal / (μ A).toReal) ^ (1 / (Module.finrank ℝ E : ℝ))
/-- **Equal-measure normalized companion set**: `bmNormalizedSet μ A B = (bmScale μ A B)⁻¹ • B`. -/
def bmNormalizedSet (A B : Set E) : Set E := (bmScale μ A B)⁻¹ • B
/-- **Normalized convex weight**:
`bmWeight μ A B θ = (θ * bmScale μ A B) / ((1 - θ) + θ * bmScale μ A B)`. -/
def bmWeight (A B : Set E) (θ : ℝ) : ℝ :=
  (θ * bmScale μ A B) / ((1 - θ) + θ * bmScale μ A B)
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem bmScale_pos {A B : Set E} (hA : 0 < (μ A).toReal) (hB : 0 < (μ B).toReal) :
    0 < bmScale μ A B := Real.rpow_pos_of_pos (div_pos hB hA) _
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem bmScale_mul_rpow (A B : Set E) (hA : 0 < (μ A).toReal) :
    bmScale μ A B * (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
      (μ B).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  dsimp [bmScale]
  rw [Real.div_rpow ENNReal.toReal_nonneg hA.le,
    div_mul_cancel₀ _ (Real.rpow_pos_of_pos hA _).ne']
/-- `bmNormalizedSet μ A B` has the same `(1 / dim E)`-th measure root as `A`. -/
theorem measure_bmNormalizedSet_toReal_rpow (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hA : 0 < (μ A).toReal) (hB : 0 < (μ B).toReal) :
    (μ (bmNormalizedSet μ A B)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
      (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have hr : 0 < bmScale μ A B := bmScale_pos μ hA hB
  have h := congrArg ENNReal.toReal
    (measure_smul_rpow_inv_finrank_of_nonneg μ (inv_nonneg.2 hr.le) B hn)
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hr.le),
    ← ENNReal.toReal_rpow, ← bmScale_mul_rpow μ A B hA, inv_mul_cancel_left₀ hr.ne'] at h
  simpa [bmNormalizedSet] using h
/-- `bmNormalizedSet μ A B` has the same measure `(μ ·).toReal` as `A`. -/
theorem measure_bmNormalizedSet_toReal (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hA : 0 < (μ A).toReal) (hB : 0 < (μ B).toReal) :
    (μ (bmNormalizedSet μ A B)).toReal = (μ A).toReal := by
  have h := congrArg (fun x : ℝ ↦ x ^ (Module.finrank ℝ E : ℝ))
    (measure_bmNormalizedSet_toReal_rpow μ hn hA hB)
  have hn0 : (Module.finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rwa [← Real.rpow_mul ENNReal.toReal_nonneg, ← Real.rpow_mul ENNReal.toReal_nonneg,
    one_div_mul_cancel hn0, Real.rpow_one, Real.rpow_one] at h
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem bmWeight_mem_Ioo {A B : Set E} (hA : 0 < (μ A).toReal) (hB : 0 < (μ B).toReal)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    bmWeight μ A B θ ∈ Set.Ioo 0 1 := by
  have hr : 0 < bmScale μ A B := bmScale_pos μ hA hB
  have hnum : 0 < θ * bmScale μ A B := mul_pos hθ₀ hr
  have hden : 0 < (1 - θ) + θ * bmScale μ A B := add_pos (sub_pos.2 hθ₁) hnum
  exact ⟨div_pos hnum hden, (div_lt_one hden).2 (by linarith)⟩
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Algebraic identity expressing `(1 - θ) • A + θ • B` as a dilation of the equal-volume convex
combination `(1 - bmWeight μ A B θ) • A + bmWeight μ A B θ • bmNormalizedSet μ A B`. -/
theorem smul_add_smul_eq_smul_bmNormalizedSet {A B : Set E}
    (hA : 0 < (μ A).toReal) (hB : 0 < (μ B).toReal) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    (1 - θ) • A + θ • B =
      ((1 - θ) + θ * bmScale μ A B) •
        ((1 - bmWeight μ A B θ) • A + bmWeight μ A B θ • bmNormalizedSet μ A B) := by
  have hr : 0 < bmScale μ A B := bmScale_pos μ hA hB
  have hden : 0 < (1 - θ) + θ * bmScale μ A B := add_pos (sub_pos.2 hθ₁) (mul_pos hθ₀ hr)
  have h1 : 1 - bmWeight μ A B θ = (1 - θ) / ((1 - θ) + θ * bmScale μ A B) := by
    dsimp [bmWeight]; rw [sub_div' hden.ne']; ring
  rw [smul_add, smul_smul, smul_smul, h1, mul_div_cancel₀ _ hden.ne']
  dsimp [bmWeight, bmNormalizedSet]
  rw [smul_smul, mul_div_cancel₀ _ hden.ne', mul_inv_cancel_right₀ hr.ne']
/-- **Reduction of general weighted Brunn–Minkowski equality to the equal-volume case**. -/
theorem weighted_brunnMinkowski_eq_iff_equal_volume (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hA : 0 < (μ A).toReal) (hB : 0 < (μ B).toReal)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    (μ ((1 - θ) • A + θ • B)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
        (1 - θ) * (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) +
          θ * (μ B).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) ↔
      (μ ((1 - bmWeight μ A B θ) • A + bmWeight μ A B θ • bmNormalizedSet μ A B)).toReal =
        (μ A).toReal := by
  rw [smul_add_smul_eq_smul_bmNormalizedSet μ hA hB hθ₀ hθ₁]
  set p : ℝ := 1 / (Module.finrank ℝ E : ℝ); set r : ℝ := bmScale μ A B
  set C : Set E := (1 - bmWeight μ A B θ) • A + bmWeight μ A B θ • bmNormalizedSet μ A B
  have hr : 0 < r := bmScale_pos μ hA hB
  have hden : 0 < (1 - θ) + θ * r := add_pos (sub_pos.2 hθ₁) (mul_pos hθ₀ hr)
  have hscale_C : (μ (((1 - θ) + θ * r) • C)).toReal ^ p =
      ((1 - θ) + θ * r) * (μ C).toReal ^ p := by
    have h := congrArg ENNReal.toReal (measure_smul_rpow_inv_finrank_of_nonneg μ hden.le C hn)
    simpa [p, ← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hden.le] using h
  have hrhs : (1 - θ) * (μ A).toReal ^ p + θ * (μ B).toReal ^ p =
      ((1 - θ) + θ * r) * (μ A).toReal ^ p := by rw [← bmScale_mul_rpow μ A B hA]; ring
  rw [hscale_C, hrhs, mul_right_inj' hden.ne']
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  have h1 := congrArg (fun x : ℝ ↦ x ^ (Module.finrank ℝ E : ℝ)) h
  have hn0 : (Module.finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  dsimp [p] at h1
  rwa [← Real.rpow_mul ENNReal.toReal_nonneg, ← Real.rpow_mul ENNReal.toReal_nonneg,
    one_div_mul_cancel hn0, Real.rpow_one, Real.rpow_one] at h1
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem convex_bmNormalizedSet (A : Set E) {B : Set E} (hB : Convex ℝ B) :
    Convex ℝ (bmNormalizedSet μ A B) := hB.smul _
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem isCompact_bmNormalizedSet (A : Set E) {B : Set E} (hB : IsCompact B) :
    IsCompact (bmNormalizedSet μ A B) := hB.smul _
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem nonempty_bmNormalizedSet (A : Set E) {B : Set E} (hB : B.Nonempty) :
    (bmNormalizedSet μ A B).Nonempty := hB.smul_set
/-- `bmNormalizedSet μ A B` has the exact same Haar measure `μ` as `A`. -/
theorem measure_bmNormalizedSet_eq (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hA : 0 < (μ A).toReal) (hB : 0 < (μ B).toReal) :
    μ (bmNormalizedSet μ A B) = μ A := by
  have hA_top : μ A ≠ ⊤ := (ENNReal.toReal_pos_iff.1 hA).2.ne
  have hnorm_top : μ (bmNormalizedSet μ A B) ≠ ⊤ := by
    rw [bmNormalizedSet, Measure.addHaar_smul μ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.toReal_pos_iff.1 hB).2.ne
  exact (ENNReal.toReal_eq_toReal_iff' hnorm_top hA_top).1
    (measure_bmNormalizedSet_toReal μ hn hA hB)
/-- **Equal-volume translation ↔ general positive homothety**:
`IsTranslateOf A (bmNormalizedSet μ A B) ↔ IsPositiveHomothetic A B`. -/
theorem isTranslateOf_bmNormalizedSet_iff_isPositiveHomothetic (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hA : 0 < (μ A).toReal) (hB : 0 < (μ B).toReal) :
    IsTranslateOf A (bmNormalizedSet μ A B) ↔ IsPositiveHomothetic A B := by
  have hr : 0 < bmScale μ A B := bmScale_pos μ hA hB
  refine ⟨?_, ?_⟩
  · rintro ⟨c, hc⟩
    refine ⟨bmScale μ A B • c, bmScale μ A B, hr, ?_⟩
    have h := congrArg (fun s : Set E ↦ bmScale μ A B • s) hc
    dsimp [bmNormalizedSet] at h
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, smul_add, smul_singleton_eq] at h
    exact h
  · intro hAB
    have hA_pos : 0 < μ A := (ENNReal.toReal_pos_iff.1 hA).1
    have hA_top : μ A ≠ ⊤ := (ENNReal.toReal_pos_iff.1 hA).2.ne
    have hnorm_hom : IsPositiveHomothetic A (bmNormalizedSet μ A B) :=
      hAB.trans ⟨0, (bmScale μ A B)⁻¹, inv_pos.2 hr, by simp [bmNormalizedSet]⟩
    exact (isPositiveHomothetic_iff_isTranslateOf_of_measure_eq μ hn hA_pos hA_top
      (measure_bmNormalizedSet_eq μ hn hA hB).symm).1 hnorm_hom
/-- **Master equal-volume reduction for weighted Brunn–Minkowski equality (`Isoperimetry/README.md`
lines 136–142)**: if equal-volume weighted Brunn–Minkowski equality at weight `bmWeight μ A B θ`
between `A` and `bmNormalizedSet μ A B` implies `IsTranslateOf A (bmNormalizedSet μ A B)`, then
weighted Brunn–Minkowski equality for `(A, B)` at `θ ∈ (0, 1)` is equivalent to
`IsPositiveHomothetic A B`. -/
theorem weighted_brunnMinkowski_eq_iff_isPositiveHomothetic_of_equal_volume_rigidity
    (hn : 1 ≤ Module.finrank ℝ E) {A B : Set E} (hA_conv : Convex ℝ A)
    (hA : 0 < (μ A).toReal) (hB : 0 < (μ B).toReal) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (h_eq_vol :
      (μ ((1 - bmWeight μ A B θ) • A + bmWeight μ A B θ • bmNormalizedSet μ A B)).toReal =
        (μ A).toReal →
      IsTranslateOf A (bmNormalizedSet μ A B)) :
    (μ ((1 - θ) • A + θ • B)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) =
        (1 - θ) * (μ A).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) +
          θ * (μ B).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) ↔
      IsPositiveHomothetic A B :=
  ⟨fun h ↦ (isTranslateOf_bmNormalizedSet_iff_isPositiveHomothetic μ hn hA hB).1
    (h_eq_vol ((weighted_brunnMinkowski_eq_iff_equal_volume μ hn hA hB hθ₀ hθ₁).1 h)),
   weighted_brunnMinkowski_eq_of_isPositiveHomothetic μ hn hθ₀.le hθ₁.le hA_conv⟩
end WeightedToUnweightedAndScaleReduction

/-! ### Section 3: Nonempty-interior bridge, 1D homothety, support width, boxes & ball rigidity -/
section RigidityBridges
/-- **Positive Haar measure ↔ nonempty topological interior for convex sets**
(`Isoperimetry/README.md` line 138). -/
theorem _root_.Convex.interior_nonempty_iff_measure_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E} (hK : Convex ℝ K) :
    (interior K).Nonempty ↔ 0 < μ K :=
  ⟨fun hne ↦ (isOpen_interior.measure_pos μ hne).trans_le (measure_mono interior_subset),
    hK.interior_nonempty_of_measure_pos⟩
/-- **1D compact convex characterization**: a nonempty subset `K ⊆ ℝ` is compact and convex if and
only if `K = Set.Icc (sInf K) (sSup K)` with `sInf K ≤ sSup K`. -/
theorem isCompact_and_convex_iff_Icc_real {K : Set ℝ} (hK_ne : K.Nonempty) :
    IsCompact K ∧ Convex ℝ K ↔ K = Set.Icc (sInf K) (sSup K) ∧ sInf K ≤ sSup K := by
  refine ⟨fun ⟨hKc, hKconv⟩ ↦ ?_, fun ⟨hK_eq, _⟩ ↦ ?_⟩
  · have h_eq := hKconv.eq_Icc_of_isCompact hK_ne hKc
    obtain ⟨x, hx⟩ := hK_ne; rw [h_eq] at hx
    exact ⟨h_eq, hx.1.trans hx.2⟩
  · rw [hK_eq]; exact ⟨isCompact_Icc, convex_Icc _ _⟩
/-- **Unconditional 1D positive homothety of positive-volume compact convex subsets of `ℝ`**. -/
theorem isPositiveHomothetic_of_isCompact_of_convex_real {A B : Set ℝ}
    (hAc : IsCompact A) (hAconv : Convex ℝ A) (hApos : 0 < volume A)
    (hBc : IsCompact B) (hBconv : Convex ℝ B) (hBpos : 0 < volume B) :
    IsPositiveHomothetic A B :=
  hAconv.exists_singleton_add_pos_smul_of_isCompact_of_volume_pos hAc hApos hBc hBconv hBpos
/-- **1D unweighted Brunn–Minkowski equality ↔ `IsPositiveHomothetic A B`**. -/
theorem unweighted_brunnMinkowski_eq_iff_isPositiveHomothetic_real {A B : Set ℝ}
    (hAc : IsCompact A) (hAconv : Convex ℝ A) (hApos : 0 < volume A)
    (hBc : IsCompact B) (hBconv : Convex ℝ B) (hBpos : 0 < volume B) :
    volume (A + B) = volume A + volume B ↔ IsPositiveHomothetic A B :=
  hAconv.volume_add_eq_iff_of_isCompact hAc hApos hBc hBconv hBpos
/-- **1D weighted Brunn–Minkowski equality ↔ `IsPositiveHomothetic A B`**. -/
theorem weighted_brunnMinkowski_eq_iff_isPositiveHomothetic_real {A B : Set ℝ}
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hAc : IsCompact A) (hAconv : Convex ℝ A) (hApos : 0 < volume A)
    (hBc : IsCompact B) (hBconv : Convex ℝ B) (hBpos : 0 < volume B) :
    volume ((1 - θ) • A + θ • B) =
      ENNReal.ofReal (1 - θ) * volume A + ENNReal.ofReal θ * volume B ↔
    IsPositiveHomothetic A B :=
  hAconv.volume_smul_add_smul_eq_iff_of_isCompact hθ₀ hθ₁ hAc hApos hBc hBconv hBpos

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Directional support width of `A ⊆ E` along `e : E`:
`supportWidth e A = sSup ((⟪·, e⟫_ℝ) '' A) - sInf ((⟪·, e⟫_ℝ) '' A)`. -/
def supportWidth (e : E) (A : Set E) : ℝ :=
  sSup ((fun x : E ↦ ⟪x, e⟫_ℝ) '' A) - sInf ((fun x : E ↦ ⟪x, e⟫_ℝ) '' A)
theorem supportWidth_nonneg (e : E) {A : Set E} (hAn : A.Nonempty) (hAc : IsCompact A) :
    0 ≤ supportWidth e A := by
  have h_img_ne : ((fun x : E ↦ ⟪x, e⟫_ℝ) '' A).Nonempty := hAn.image _
  have h_img_c : IsCompact ((fun x : E ↦ ⟪x, e⟫_ℝ) '' A) :=
    hAc.image (continuous_id.inner continuous_const)
  exact sub_nonneg.2 (csInf_le h_img_c.bddBelow (h_img_c.sSup_mem h_img_ne))
/-- Translation invariance of `supportWidth e`. -/
theorem supportWidth_singleton_add (e c : E) {A : Set E} (hAn : A.Nonempty)
    (hAc : IsCompact A) : supportWidth e ({c} + A) = supportWidth e A := by
  set IA := (fun x : E ↦ ⟪x, e⟫_ℝ) '' A
  have h_img : (fun x : E ↦ ⟪x, e⟫_ℝ) '' ({c} + A) = (fun t : ℝ ↦ ⟪c, e⟫_ℝ + t) '' IA := by
    ext t; simp only [IA, Set.mem_image, Set.mem_add, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨_, rfl, a, ha, rfl⟩, rfl⟩
      exact ⟨⟪a, e⟫_ℝ, ⟨a, ha, rfl⟩, (inner_add_left _ a e).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨c + a, ⟨c, rfl, a, ha, rfl⟩, inner_add_left c a e⟩
  have h_ne : IA.Nonempty := hAn.image _
  have h_c : IsCompact IA := hAc.image (continuous_id.inner continuous_const)
  have h_c' : IsCompact ((fun t : ℝ ↦ ⟪c, e⟫_ℝ + t) '' IA) :=
    h_c.image (continuous_const.add continuous_id)
  have hsup : sSup ((fun t : ℝ ↦ ⟪c, e⟫_ℝ + t) '' IA) = ⟪c, e⟫_ℝ + sSup IA := by
    refine le_antisymm (csSup_le (h_ne.image _) ?_) ?_
    · rintro _ ⟨t, ht, rfl⟩; exact add_le_add_right (le_csSup h_c.bddAbove ht) _
    · exact le_csSup h_c'.bddAbove ⟨sSup IA, h_c.sSup_mem h_ne, rfl⟩
  have hinf : sInf ((fun t : ℝ ↦ ⟪c, e⟫_ℝ + t) '' IA) = ⟪c, e⟫_ℝ + sInf IA := by
    refine le_antisymm ?_ (le_csInf (h_ne.image _) ?_)
    · exact csInf_le h_c'.bddBelow ⟨sInf IA, h_c.sInf_mem h_ne, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩; exact add_le_add_right (csInf_le h_c.bddBelow ht) _
  dsimp [supportWidth]; rw [h_img, hsup, hinf]; ring
/-- Nonnegative homogeneity of `supportWidth e`. -/
theorem supportWidth_smul_of_nonneg (e : E) {r : ℝ} (hr : 0 ≤ r) {A : Set E}
    (hAn : A.Nonempty) (hAc : IsCompact A) :
    supportWidth e (r • A) = r * supportWidth e A := by
  rcases eq_or_lt_of_le hr with rfl | hr_pos
  · obtain ⟨x, hx⟩ := hAn
    have h0 : (0 : ℝ) • A = {0} := zero_smul_set ⟨x, hx⟩
    simp [supportWidth, h0]
  · set IA := (fun x : E ↦ ⟪x, e⟫_ℝ) '' A
    have h_img : (fun x : E ↦ ⟪x, e⟫_ℝ) '' (r • A) = r • IA := by
      ext t; simp [IA, Set.mem_smul_set, real_inner_smul_left]
    have h_ne : IA.Nonempty := hAn.image _
    have h_c : IsCompact IA := hAc.image (continuous_id.inner continuous_const)
    have hsup : sSup (r • IA) = r * sSup IA := by
      refine le_antisymm (csSup_le h_ne.smul_set ?_) ?_
      · rintro _ ⟨t, ht, rfl⟩; exact mul_le_mul_of_nonneg_left (le_csSup h_c.bddAbove ht) hr_pos.le
      · exact le_csSup (h_c.smul r).bddAbove ⟨sSup IA, h_c.sSup_mem h_ne, rfl⟩
    have hinf : sInf (r • IA) = r * sInf IA := by
      refine le_antisymm ?_ (le_csInf h_ne.smul_set ?_)
      · exact csInf_le (h_c.smul r).bddBelow ⟨sInf IA, h_c.sInf_mem h_ne, rfl⟩
      · rintro _ ⟨t, ht, rfl⟩; exact mul_le_mul_of_nonneg_left (csInf_le h_c.bddBelow ht) hr_pos.le
    dsimp [supportWidth]; rw [h_img, hsup, hinf]; ring
/-- **Uniform directional support-width scaling under `IsPositiveHomothetic`**. -/
theorem supportWidth_of_isPositiveHomothetic (e : E) {A B : Set E}
    (hAn : A.Nonempty) (hAc : IsCompact A) {c : E} {r : ℝ} (hr : 0 ≤ r) (hB : B = {c} + r • A) :
    supportWidth e B = r * supportWidth e A := by
  rw [hB, supportWidth_singleton_add e c hAn.smul_set (hAc.smul r),
    supportWidth_smul_of_nonneg e hr hAn hAc]
/-- **Minkowski additivity of directional support width** for nonempty compact sets `A, B ⊆ E`. -/
theorem supportWidth_add (e : E) {A B : Set E} (hAn : A.Nonempty) (hAc : IsCompact A)
    (hBn : B.Nonempty) (hBc : IsCompact B) :
    supportWidth e (A + B) = supportWidth e A + supportWidth e B := by
  set IA := (fun x : E ↦ ⟪x, e⟫_ℝ) '' A; set IB := (fun x : E ↦ ⟪x, e⟫_ℝ) '' B
  have h_img : (fun x : E ↦ ⟪x, e⟫_ℝ) '' (A + B) = IA + IB := by
    ext t; simp only [IA, IB, Set.mem_image, Set.mem_add]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨⟪a, e⟫_ℝ, ⟨a, ha, rfl⟩, ⟪b, e⟫_ℝ, ⟨b, hb, rfl⟩, (inner_add_left a b e).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, inner_add_left a b e⟩
  have hIA_ne : IA.Nonempty := hAn.image _; have hIB_ne : IB.Nonempty := hBn.image _
  have hIA_c : IsCompact IA := hAc.image (continuous_id.inner continuous_const)
  have hIB_c : IsCompact IB := hBc.image (continuous_id.inner continuous_const)
  have hAB_c : IsCompact (IA + IB) := hIA_c.add hIB_c
  have hsup : sSup (IA + IB) = sSup IA + sSup IB := by
    refine le_antisymm (csSup_le (hIA_ne.add hIB_ne) ?_) ?_
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact add_le_add (le_csSup hIA_c.bddAbove ha) (le_csSup hIB_c.bddAbove hb)
    · exact le_csSup hAB_c.bddAbove
        (add_mem_add (hIA_c.sSup_mem hIA_ne) (hIB_c.sSup_mem hIB_ne))
  have hinf : sInf (IA + IB) = sInf IA + sInf IB := by
    refine le_antisymm ?_ (le_csInf (hIA_ne.add hIB_ne) ?_)
    · exact csInf_le hAB_c.bddBelow
        (add_mem_add (hIA_c.sInf_mem hIA_ne) (hIB_c.sInf_mem hIB_ne))
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact add_le_add (csInf_le hIA_c.bddBelow ha) (csInf_le hIB_c.bddBelow hb)
  dsimp [supportWidth]; rw [h_img, hsup, hinf]; ring
/-- **Linearity of directional support width under nonnegative Minkowski combinations**. -/
theorem supportWidth_smul_add_smul (e : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {A B : Set E} (hAn : A.Nonempty) (hAc : IsCompact A) (hBn : B.Nonempty) (hBc : IsCompact B) :
    supportWidth e (a • A + b • B) = a * supportWidth e A + b * supportWidth e B := by
  rw [supportWidth_add e hAn.smul_set (hAc.smul a) hBn.smul_set (hBc.smul b),
    supportWidth_smul_of_nonneg e ha hAn hAc, supportWidth_smul_of_nonneg e hb hBn hBc]
/-- **Coordinate-box positive homothety characterization in `Fin n → ℝ`**. -/
theorem isPositiveHomothetic_Icc_pi_iff {n : ℕ} {a₁ b₁ a₂ b₂ : Fin n → ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    IsPositiveHomothetic (Set.Icc a₁ b₁) (Set.Icc a₂ b₂) ↔
      ∃ r : ℝ, 0 < r ∧ ∀ i : Fin n, b₂ i - a₂ i = r * (b₁ i - a₁ i) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨c, r, hr, hbox⟩
    refine ⟨r, hr, fun i ↦ ?_⟩
    have ha₂ : a₂ ∈ {c} + r • Set.Icc a₁ b₁ := hbox ▸ ⟨le_rfl, h₂⟩
    have hb₂ : b₂ ∈ {c} + r • Set.Icc a₁ b₁ := hbox ▸ ⟨h₂, le_rfl⟩
    rw [Set.singleton_add] at ha₂ hb₂
    rcases ha₂ with ⟨_, ⟨x, hx, rfl⟩, ha₂_eq⟩
    rcases hb₂ with ⟨_, ⟨y, hy, rfl⟩, hb₂_eq⟩
    have ha₁_mem : c + r • a₁ ∈ Set.Icc a₂ b₂ := by
      rw [hbox]; exact ⟨c, rfl, r • a₁, ⟨a₁, ⟨le_rfl, h₁⟩, rfl⟩, rfl⟩
    have hb₁_mem : c + r • b₁ ∈ Set.Icc a₂ b₂ := by
      rw [hbox]; exact ⟨c, rfl, r • b₁, ⟨b₁, ⟨h₁, le_rfl⟩, rfl⟩, rfl⟩
    have ha_le : a₂ i ≤ c i + r * a₁ i := ha₁_mem.1 i
    have ha_ge : c i + r * a₁ i ≤ a₂ i := by
      have := congrFun ha₂_eq i; dsimp at this; rw [← this]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (hx.1 i) hr.le) _
    have hb_ge : c i + r * b₁ i ≤ b₂ i := hb₁_mem.2 i
    have hb_le : b₂ i ≤ c i + r * b₁ i := by
      have := congrFun hb₂_eq i; dsimp at this; rw [← this]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (hy.2 i) hr.le) _
    linarith
  · rintro ⟨r, hr, hside⟩
    refine ⟨a₂ - r • a₁, r, hr, ?_⟩
    ext x; simp only [Set.mem_Icc, singleton_add, Set.mem_image, Set.mem_smul_set]
    refine ⟨fun ⟨hx₁, hx₂⟩ ↦ ?_, ?_⟩
    · refine ⟨x - (a₂ - r • a₁), ⟨r⁻¹ • (x - (a₂ - r • a₁)), ⟨fun i ↦ ?_, fun i ↦ ?_⟩,
        smul_inv_smul₀ hr.ne' _⟩, add_sub_cancel _ _⟩
      · dsimp; rw [← div_eq_inv_mul, le_div_iff₀ hr]; linarith [hx₁ i]
      · dsimp; rw [← div_eq_inv_mul, div_le_iff₀ hr]; linarith [hx₂ i, hside i]
    · rintro ⟨_, ⟨y, ⟨hy₁, hy₂⟩, rfl⟩, rfl⟩
      refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
      · dsimp; nlinarith [hy₁ i]
      · dsimp; nlinarith [hy₂ i, hside i]
/-- **Milestone I4 Step 1 (`Isoperimetry/README.md` lines 273–275)**:
if a nonempty bounded convex body `K ⊆ EuclideanSpace ℝ (Fin n)` (`1 ≤ n`, `0 < (volume K).toReal`)
achieves Minkowski-content isoperimetric equality, then `K` and `Metric.closedBall 0 1` achieve
exact equality in the unweighted Brunn–Minkowski inequality. -/
theorem unweighted_brunnMinkowski_eq_closedBall_of_minkowskiContent_eq {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hK_bdd : Bornology.IsBounded K) (hK_pos : 0 < (volume K).toReal) {S : ℝ}
    (hderiv : HasDerivWithinAt (fun t : ℝ ↦ (volume (outerParallel K t)).toReal) S (Set.Ici 0) 0)
    (hM_eq : (lowerMinkowskiContent volume K).toReal ≤
      (n : ℝ) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) *
        (volume K).toReal ^ (((n : ℝ) - 1) / (n : ℝ))) :
    (volume (K + Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) =
      (volume K).toReal ^ (1 / (n : ℝ)) +
        (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using Nat.pos_of_ne_zero (by omega))
  have hlin := parallelVolumeRoot_eq_linear_of_minkowskiContent_eq hn hK hK_bdd hK_pos hderiv
    hM_eq zero_le_one
  rw [parallelVolumeRoot, parallelVolumeRoot_zero, one_smul, one_mul,
    ← Measure.addHaar_closedBall_eq_addHaar_ball] at hlin
  exact hlin
/-- **Milestone I4 Step 2 (`Isoperimetry/README.md` lines 273–276)**:
if `IsPositiveHomothetic (Metric.closedBall (0 : E) 1) K`, then there exist `c : E` and `r > 0`
such that `K = Metric.closedBall c r`, `K =ᵐ[volume] Metric.ball c r`,
`interior K = Metric.ball c r`, and `frontier K = Metric.sphere c r`. -/
theorem eq_closedBall_and_ae_eq_ball_of_isPositiveHomothetic_closedBall
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {K : Set E} (h : IsPositiveHomothetic (Metric.closedBall (0 : E) 1) K) :
    ∃ (c : E) (r : ℝ), 0 < r ∧ K = Metric.closedBall c r ∧
      (K =ᵐ[volume] Metric.ball c r) ∧ interior K = Metric.ball c r ∧
      frontier K = Metric.sphere c r := by
  obtain ⟨c, r, hr, rfl⟩ := isPositiveHomothetic_closedBall_zero_one_iff.1 h
  exact ⟨c, r, hr, rfl, closedBall_ae_eq_ball c r, interior_closedBall c hr.ne',
    frontier_closedBall c hr.ne'⟩
/-- **Milestone I4 Complete Convex-Body-to-Ball Rigidity Bridge (`Isoperimetry/README.md` lines
273–276)**:
if `K ⊆ EuclideanSpace ℝ (Fin n)` (`1 ≤ n`) is a bounded convex body with `0 < (volume K).toReal`
achieving Minkowski-content isoperimetric equality, and unweighted Brunn–Minkowski equality for
`(K, Metric.closedBall 0 1)` implies `IsPositiveHomothetic (Metric.closedBall 0 1) K`, then there
exist `c : EuclideanSpace ℝ (Fin n)` and `r > 0` such that `K = Metric.closedBall c r`,
`K =ᵐ[volume] Metric.ball c r`, and every set `s =ᵐ[volume] K` satisfies
`s =ᵐ[volume] Metric.ball c r` and Caccioppoli isoperimetric equality. -/
theorem eq_closedBall_and_ae_eq_ball_of_minkowskiContent_eq {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hK_bdd : Bornology.IsBounded K) (hK_pos : 0 < (volume K).toReal) {S : ℝ}
    (hderiv : HasDerivWithinAt (fun t : ℝ ↦ (volume (outerParallel K t)).toReal) S (Set.Ici 0) 0)
    (hM_eq : (lowerMinkowskiContent volume K).toReal ≤
      (n : ℝ) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) *
        (volume K).toReal ^ (((n : ℝ) - 1) / (n : ℝ)))
    (hBM_rigidity :
      (volume (K + Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) =
        (volume K).toReal ^ (1 / (n : ℝ)) +
          (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) →
      IsPositiveHomothetic (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) K) :
    ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r ∧ K = Metric.closedBall c r ∧
      (K =ᵐ[volume] Metric.ball c r) ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin n)), (s =ᵐ[volume] K) →
        (s =ᵐ[volume] Metric.ball c r) ∧
        perimeter volume s ^ n =
          (n : ℝ≥0∞) ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
            volume s ^ (n - 1) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using Nat.pos_of_ne_zero (by omega))
  have hBM := unweighted_brunnMinkowski_eq_closedBall_of_minkowskiContent_eq hn hK hK_bdd hK_pos
    hderiv hM_eq
  obtain ⟨c, r, hr, hK_eq, hK_ae, _, _⟩ :=
    eq_closedBall_and_ae_eq_ball_of_isPositiveHomothetic_closedBall (hBM_rigidity hBM)
  refine ⟨c, r, hr, hK_eq, hK_ae, fun s hs ↦ ?_⟩
  have hs_ball : s =ᵐ[volume] Metric.ball c r := hs.trans hK_ae
  refine ⟨hs_ball, ?_⟩
  simpa using isoperimetric_equality_of_ae_eq_ball hr hs_ball
end RigidityBridges
end TauCeti
