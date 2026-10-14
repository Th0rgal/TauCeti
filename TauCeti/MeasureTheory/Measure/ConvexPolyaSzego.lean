/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.MeasureTheory.Measure.Regular
public import TauCeti.MeasureTheory.Measure.RadonVariationMeasure
public import TauCeti.MeasureTheory.Measure.StrictApproximation
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.RadonVariationMeasure
import all TauCeti.MeasureTheory.Measure.StrictApproximation

/-!
# Convex Perspective Inequality, Superlinear Uniform Integrability, and Singular Exclusion

This file develops the convex perspective function `convexPerspective Φ P s = s * Φ (P / s)` for
convex nondecreasing integrands `Φ : ℝ → ℝ` with `Φ 0 = 0`, the level-set and integral
convex-integrand Pólya–Szegő comparison chain, the de la Vallée Poussin superlinear uniform
integrability estimate `∫_A w_j ≤ T |A| + ε`, the outer-regularity open-covering criterion for
absolute continuity `ν ≪ μ`, the exclusion of singular variation measures
(`singularVariationMeasure ν = 0`, ruling out jump, Cantor, and point concentration on null sets),
the recovery of an integrable weak gradient `D u = (approxGradient σ ν) · volume`, and the
positive/negative-part truncation decomposition of distributional total variation:

1. **Convex perspective function and level-set Pólya–Szegő chain**:
   `TauCeti.convexPerspective`, `TauCeti.nonneg_of_convexOn_of_map_zero`,
   `TauCeti.mul_le_of_convexOn_of_map_zero`, `TauCeti.le_mul_of_convexOn_of_map_zero_of_one_le`,
   `TauCeti.div_mono_of_convexOn_of_map_zero`, `TauCeti.convexPerspective_nonneg`,
   `TauCeti.convexPerspective_zero_left`, `TauCeti.convexPerspective_of_nonpos`,
   `TauCeti.convexPerspective_id`, `TauCeti.convexPerspective_mono_left`,
   `TauCeti.convexPerspective_antitone_right`, `TauCeti.convexPerspective_le_of_le_of_le`,
   `TauCeti.convexPerspective_add_le`, `TauCeti.setIntegral_Ioi_convexPerspective_le`, and
   `TauCeti.setLIntegral_Ioi_ofReal_convexPerspective_le`.
2. **De la Vallée Poussin superlinear uniform integrability**:
   `TauCeti.le_add_inv_mul_of_superlinear_on_Ici`, `TauCeti.pointwise_deLaValleePoussin_le`,
   `TauCeti.setIntegral_deLaValleePoussin_le`,
   `TauCeti.setLIntegral_ofReal_deLaValleePoussin_le`,
   `TauCeti.exists_superlinear_cutoff_of_tendsto_div_atTop`,
   `TauCeti.uniform_setLIntegral_bound_of_superlinear`,
   `TauCeti.uniform_setLIntegral_bound_of_tendsto_div_atTop`, and
   `TauCeti.uniform_setIntegral_bound_of_tendsto_div_atTop`.
3. **Outer-regularity absolute continuity, singular exclusion, and truncation subadditivity**:
   `TauCeti.HasOpenLinearBound`, `TauCeti.measure_eq_zero_of_open_linear_bound`,
   `TauCeti.absolutelyContinuous_of_open_linear_bound`,
   `TauCeti.singularVariationMeasure_eq_zero_of_open_linear_bound`,
   `TauCeti.measure_null_eq_zero_of_open_linear_bound`,
   `TauCeti.HasPolarDerivativeMeasureOn.hasWeakGradientOn_of_open_linear_bound`,
   `TauCeti.abs_eq_max_zero_add_max_neg_zero`, and
   `TauCeti.distributionalVariation_abs_le_add_max_zero`.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

/-! ### Section 1: Convex perspective function and level-set Pólya–Szegő chain -/

section ConvexPerspective

/-- Any function `Φ : ℝ → ℝ` that is monotone on `[0, ∞)` and satisfies `Φ 0 = 0` is nonnegative on
`[0, ∞)`. -/
theorem nonneg_of_monotoneOn_of_map_zero {Φ : ℝ → ℝ} (hmono : MonotoneOn Φ (Ici 0))
    (h0 : Φ 0 = 0) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Φ x :=
  h0 ▸ hmono (le_rfl : (0 : ℝ) ∈ Ici 0) hx hx

/-- Any convex nondecreasing function `Φ : ℝ → ℝ` on `[0, ∞)` with `Φ 0 = 0` is nonnegative on
`[0, ∞)`. -/
theorem nonneg_of_convexOn_of_map_zero {Φ : ℝ → ℝ} (_hconv : ConvexOn ℝ (Ici 0) Φ)
    (hmono : MonotoneOn Φ (Ici 0)) (h0 : Φ 0 = 0) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Φ x :=
  nonneg_of_monotoneOn_of_map_zero hmono h0 hx

/-- **Star-shapedness at `0` of convex functions with `Φ 0 = 0`**: if `ConvexOn ℝ (Ici 0) Φ` and
`Φ 0 = 0`, then `Φ (θ * x) ≤ θ * Φ x` for all `0 ≤ θ ≤ 1` and `0 ≤ x`. -/
theorem mul_le_of_convexOn_of_map_zero {Φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) Φ) (h0 : Φ 0 = 0)
    {θ x : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) :
    Φ (θ * x) ≤ θ * Φ x := by
  have h := hconv.2 (le_rfl : (0 : ℝ) ∈ Ici 0) hx (sub_nonneg.mpr hθ1) hθ0 (sub_add_cancel 1 θ)
  simpa [smul_eq_mul, h0] using h

/-- **Superhomogeneous scaling for `c ≥ 1`**: if `ConvexOn ℝ (Ici 0) Φ` and `Φ 0 = 0`, then
`c * Φ x ≤ Φ (c * x)` for all `1 ≤ c` and `0 ≤ x`. -/
theorem le_mul_of_convexOn_of_map_zero_of_one_le {Φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) Φ)
    (h0 : Φ 0 = 0) {c x : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x) :
    c * Φ x ≤ Φ (c * x) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hinv : Φ (c⁻¹ * (c * x)) ≤ c⁻¹ * Φ (c * x) :=
    mul_le_of_convexOn_of_map_zero hconv h0 (inv_nonneg.mpr hc0.le) (inv_le_one_of_one_le₀ hc)
      (mul_nonneg hc0.le hx)
  rw [inv_mul_cancel_left₀ hc0.ne'] at hinv
  exact (le_inv_mul_iff₀ hc0).mp hinv

/-- **Secant-slope monotonicity (`t ↦ Φ t / t`)**: if `ConvexOn ℝ (Ici 0) Φ` and `Φ 0 = 0`, then
`Φ x / x ≤ Φ y / y` for `0 < x ≤ y`. -/
theorem div_mono_of_convexOn_of_map_zero {Φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) Φ)
    (h0 : Φ 0 = 0) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Φ x / x ≤ Φ y / y := by
  have hy : 0 < y := hx.trans_le hxy
  have hθ : Φ ((x / y) * y) ≤ (x / y) * Φ y :=
    mul_le_of_convexOn_of_map_zero hconv h0 (div_nonneg hx.le hy.le) ((div_le_one hy).mpr hxy) hy.le
  rw [div_mul_cancel₀ _ hy.ne'] at hθ
  calc Φ x / x
      ≤ (x / y * Φ y) / x := div_le_div_of_nonneg_right hθ hx.le
    _ = Φ y / y := by
      rw [div_mul_eq_mul_div, mul_comm x (Φ y), mul_div_right_comm, mul_div_cancel_right₀ _ hx.ne']

/-- The **convex perspective function** `convexPerspective Φ P s` associated to `Φ : ℝ → ℝ`,
defined by `s * Φ (P / s)` for `s > 0` and `0` for `s ≤ 0`. -/
def convexPerspective (Φ : ℝ → ℝ) (P s : ℝ) : ℝ :=
  if 0 < s then s * Φ (P / s) else 0

/-- Evaluation of `convexPerspective Φ P s` when `0 < s`. -/
@[simp] theorem convexPerspective_of_pos (Φ : ℝ → ℝ) (P : ℝ) {s : ℝ} (hs : 0 < s) :
    convexPerspective Φ P s = s * Φ (P / s) := by
  simp [convexPerspective, hs]

/-- Evaluation of `convexPerspective Φ P s` when `s ≤ 0`. -/
theorem convexPerspective_of_nonpos (Φ : ℝ → ℝ) (P : ℝ) {s : ℝ} (hs : s ≤ 0) :
    convexPerspective Φ P s = 0 := by
  simp [convexPerspective, not_lt.mpr hs]

/-- At `s = 0`, `convexPerspective Φ P 0 = 0`. -/
@[simp] theorem convexPerspective_zero_right (Φ : ℝ → ℝ) (P : ℝ) :
    convexPerspective Φ P 0 = 0 := convexPerspective_of_nonpos Φ P le_rfl

/-- When `Φ 0 = 0`, `convexPerspective Φ 0 s = 0` for all `s : ℝ`. -/
@[simp] theorem convexPerspective_zero_left {Φ : ℝ → ℝ} (h0 : Φ 0 = 0) (s : ℝ) :
    convexPerspective Φ 0 s = 0 := by
  by_cases hs : 0 < s <;> simp [convexPerspective, hs, h0]

/-- At `s = 1`, `convexPerspective Φ P 1 = Φ P`. -/
theorem convexPerspective_one (Φ : ℝ → ℝ) (P : ℝ) :
    convexPerspective Φ P 1 = Φ P := by
  simp [convexPerspective]

/-- For the identity function `Φ = id` and `0 < s`, `convexPerspective id P s = P`, recovering the
linear coarea integrand. -/
theorem convexPerspective_id {P s : ℝ} (hs : 0 < s) :
    convexPerspective id P s = P := by
  rw [convexPerspective_of_pos id P hs, id_eq, mul_div_cancel₀ P hs.ne']

/-- Scalar-multiple linearity of `convexPerspective` in the integrand `Φ`. -/
theorem convexPerspective_const_mul (Φ : ℝ → ℝ) (c P s : ℝ) :
    convexPerspective (fun t ↦ c * Φ t) P s = c * convexPerspective Φ P s := by
  by_cases hs : 0 < s
  · simp [convexPerspective, hs, mul_left_comm]
  · simp [convexPerspective, hs]

/-- Additivity of `convexPerspective` in the integrand `Φ`. -/
theorem convexPerspective_add (Φ₁ Φ₂ : ℝ → ℝ) (P s : ℝ) :
    convexPerspective (fun t ↦ Φ₁ t + Φ₂ t) P s =
      convexPerspective Φ₁ P s + convexPerspective Φ₂ P s := by
  by_cases hs : 0 < s
  · simp [convexPerspective, hs, mul_add]
  · simp [convexPerspective, hs]

/-- Positive 1-homogeneity of `convexPerspective Φ` in `(P, s)` for `c > 0`. -/
theorem convexPerspective_scale (Φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (P s : ℝ) :
    convexPerspective Φ (c * P) (c * s) = c * convexPerspective Φ P s := by
  by_cases hs : 0 < s
  · rw [convexPerspective_of_pos Φ _ (mul_pos hc hs), convexPerspective_of_pos Φ P hs,
      mul_div_mul_left P s hc.ne', mul_assoc]
  · have hcs : c * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le (not_lt.mp hs)
    rw [convexPerspective_of_nonpos Φ _ hcs, convexPerspective_of_nonpos Φ P (not_lt.mp hs),
      mul_zero]

/-- Nonnegativity of `convexPerspective Φ P s` for `P ≥ 0` when `Φ` is monotone on `[0, ∞)` with
`Φ 0 = 0`. -/
theorem convexPerspective_nonneg {Φ : ℝ → ℝ} (hmono : MonotoneOn Φ (Ici 0)) (h0 : Φ 0 = 0)
    {P : ℝ} (hP : 0 ≤ P) (s : ℝ) :
    0 ≤ convexPerspective Φ P s := by
  by_cases hs : 0 < s
  · rw [convexPerspective_of_pos Φ P hs]
    exact mul_nonneg hs.le (nonneg_of_monotoneOn_of_map_zero hmono h0 (div_nonneg hP hs.le))
  · rw [convexPerspective_of_nonpos Φ P (not_lt.mp hs)]

/-- **Monotonicity of `convexPerspective Φ P s` in the perimeter argument `P ≥ 0`**: if `Φ` is
monotone on `[0, ∞)` and `0 ≤ P₁ ≤ P₂`, then
`convexPerspective Φ P₁ s ≤ convexPerspective Φ P₂ s`. -/
theorem convexPerspective_mono_left {Φ : ℝ → ℝ} (hmono : MonotoneOn Φ (Ici 0))
    {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂) (s : ℝ) :
    convexPerspective Φ P₁ s ≤ convexPerspective Φ P₂ s := by
  by_cases hs : 0 < s
  · rw [convexPerspective_of_pos Φ P₁ hs, convexPerspective_of_pos Φ P₂ hs]
    refine mul_le_mul_of_nonneg_left ?_ hs.le
    exact hmono (div_nonneg hP₁ hs.le) (div_nonneg (hP₁.trans hP) hs.le)
      (div_le_div_of_nonneg_right hP hs.le)
  · rw [convexPerspective_of_nonpos Φ P₁ (not_lt.mp hs),
      convexPerspective_of_nonpos Φ P₂ (not_lt.mp hs)]

/-- **Antitonicity of `convexPerspective Φ P s` in the scale argument `s > 0`**: if
`ConvexOn ℝ (Ici 0) Φ` and `Φ 0 = 0`, then for every `P ≥ 0` and `0 < s₁ ≤ s₂`,
`convexPerspective Φ P s₂ ≤ convexPerspective Φ P s₁`. -/
theorem convexPerspective_antitone_right {Φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) Φ)
    (h0 : Φ 0 = 0) {P s₁ s₂ : ℝ} (hP : 0 ≤ P) (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) :
    convexPerspective Φ P s₂ ≤ convexPerspective Φ P s₁ := by
  have hs₂ : 0 < s₂ := hs₁.trans_le hs
  rw [convexPerspective_of_pos Φ P hs₂, convexPerspective_of_pos Φ P hs₁]
  have hdiv_eq : P / s₂ = (s₁ / s₂) * (P / s₁) := by
    rw [div_mul_div_comm, mul_comm s₁ P, mul_div_mul_right P s₂ hs₁.ne']
  have hstar : Φ (P / s₂) ≤ (s₁ / s₂) * Φ (P / s₁) := by
    rw [hdiv_eq]
    exact mul_le_of_convexOn_of_map_zero hconv h0 (div_nonneg hs₁.le hs₂.le)
      ((div_le_one hs₂).mpr hs) (div_nonneg hP hs₁.le)
  calc s₂ * Φ (P / s₂)
      ≤ s₂ * ((s₁ / s₂) * Φ (P / s₁)) := mul_le_mul_of_nonneg_left hstar hs₂.le
    _ = s₁ * Φ (P / s₁) := by rw [← mul_assoc, mul_div_cancel₀ _ hs₂.ne']

/-- **Combined level-set Pólya–Szegő comparison**: if `ConvexOn ℝ (Ici 0) Φ`,
`MonotoneOn Φ (Ici 0)`, `Φ 0 = 0`, `0 ≤ P_star ≤ P_h` (isoperimetric perimeter comparison on
superlevel sets), and `0 < m_h ≤ m_star` (Steiner/Schwarz distribution-derivative comparison), then
`convexPerspective Φ P_star m_star ≤ convexPerspective Φ P_h m_h`. -/
theorem convexPerspective_le_of_le_of_le {Φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) Φ)
    (hmono : MonotoneOn Φ (Ici 0)) (h0 : Φ 0 = 0) {P_star P_h m_h m_star : ℝ}
    (hP0 : 0 ≤ P_star) (hP : P_star ≤ P_h) (hm0 : 0 < m_h) (hm : m_h ≤ m_star) :
    convexPerspective Φ P_star m_star ≤ convexPerspective Φ P_h m_h :=
  (convexPerspective_antitone_right hconv h0 hP0 hm0 hm).trans
    (convexPerspective_mono_left hmono hP0 hP m_h)

/-- **Joint subadditivity of `convexPerspective` for `s₁, s₂ > 0`**: if `ConvexOn ℝ (Ici 0) Φ`,
`0 ≤ P₁`, `0 ≤ P₂`, `0 < s₁`, and `0 < s₂`, then
`convexPerspective Φ (P₁ + P₂) (s₁ + s₂) ≤
  convexPerspective Φ P₁ s₁ + convexPerspective Φ P₂ s₂`. -/
theorem convexPerspective_add_le {Φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) Φ)
    {P₁ P₂ s₁ s₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    convexPerspective Φ (P₁ + P₂) (s₁ + s₂) ≤
      convexPerspective Φ P₁ s₁ + convexPerspective Φ P₂ s₂ := by
  have hs : 0 < s₁ + s₂ := add_pos hs₁ hs₂
  rw [convexPerspective_of_pos Φ _ hs, convexPerspective_of_pos Φ P₁ hs₁,
    convexPerspective_of_pos Φ P₂ hs₂]
  set θ₁ := s₁ / (s₁ + s₂)
  set θ₂ := s₂ / (s₁ + s₂)
  have hθ₁ : 0 ≤ θ₁ := div_nonneg hs₁.le hs.le
  have hθ₂ : 0 ≤ θ₂ := div_nonneg hs₂.le hs.le
  have hsum : θ₁ + θ₂ = 1 := by simp [θ₁, θ₂, ← add_div, div_self hs.ne']
  have hcomb : (P₁ + P₂) / (s₁ + s₂) = θ₁ * (P₁ / s₁) + θ₂ * (P₂ / s₂) := by
    simp only [θ₁, θ₂, add_div]
    rw [div_mul_div_comm, mul_comm s₁ P₁, mul_div_mul_right P₁ (s₁ + s₂) hs₁.ne',
      div_mul_div_comm, mul_comm s₂ P₂, mul_div_mul_right P₂ (s₁ + s₂) hs₂.ne']
  have hconv_ineq := hconv.2 (div_nonneg hP₁ hs₁.le) (div_nonneg hP₂ hs₂.le) hθ₁ hθ₂ hsum
  simp only [smul_eq_mul] at hconv_ineq
  rw [← hcomb] at hconv_ineq
  calc (s₁ + s₂) * Φ ((P₁ + P₂) / (s₁ + s₂))
      ≤ (s₁ + s₂) * (θ₁ * Φ (P₁ / s₁) + θ₂ * Φ (P₂ / s₂)) :=
        mul_le_mul_of_nonneg_left hconv_ineq hs.le
    _ = s₁ * Φ (P₁ / s₁) + s₂ * Φ (P₂ / s₂) := by
        simp only [θ₁, θ₂, mul_add, ← mul_assoc, mul_div_cancel₀ _ hs.ne']

/-- Almost-everywhere level-set comparison for `convexPerspective Φ`. -/
theorem ae_convexPerspective_le_of_levelSet_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) Φ) (hmono : MonotoneOn Φ (Ici 0)) (h0 : Φ 0 = 0)
    {S : Set α} {P_star P_h m_h m_star : α → ℝ}
    (hP0 : ∀ᵐ t ∂(μ.restrict S), 0 ≤ P_star t)
    (hP : ∀ᵐ t ∂(μ.restrict S), P_star t ≤ P_h t)
    (hm0 : ∀ᵐ t ∂(μ.restrict S), 0 < m_h t)
    (hm : ∀ᵐ t ∂(μ.restrict S), m_h t ≤ m_star t) :
    ∀ᵐ t ∂(μ.restrict S),
      convexPerspective Φ (P_star t) (m_star t) ≤ convexPerspective Φ (P_h t) (m_h t) := by
  filter_upwards [hP0, hP, hm0, hm] with t hP0t hPt hm0t hmt
  exact convexPerspective_le_of_le_of_le hconv hmono h0 hP0t hPt hm0t hmt

/-- **Bochner-integral level-set convex-integrand Pólya–Szegő inequality on `Ioi 0`**: if for a.e.
`t ∈ Ioi 0`, `0 ≤ P_star t ≤ P_h t` and `0 < m_h t ≤ m_star t`, then
`∫ t in Ioi 0, convexPerspective Φ (P_star t) (m_star t) ≤
  ∫ t in Ioi 0, convexPerspective Φ (P_h t) (m_h t)`. -/
theorem setIntegral_Ioi_convexPerspective_le {Φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) Φ)
    (hmono : MonotoneOn Φ (Ici 0)) (h0 : Φ 0 = 0) {P_star P_h m_h m_star : ℝ → ℝ}
    (hint_star : IntegrableOn (fun t ↦ convexPerspective Φ (P_star t) (m_star t)) (Ioi 0) volume)
    (hint_h : IntegrableOn (fun t ↦ convexPerspective Φ (P_h t) (m_h t)) (Ioi 0) volume)
    (hP0 : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ P_star t)
    (hP : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), P_star t ≤ P_h t)
    (hm0 : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 < m_h t)
    (hm : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), m_h t ≤ m_star t) :
    ∫ t in Ioi (0 : ℝ), convexPerspective Φ (P_star t) (m_star t) ≤
      ∫ t in Ioi (0 : ℝ), convexPerspective Φ (P_h t) (m_h t) :=
  integral_mono_ae hint_star hint_h
    (ae_convexPerspective_le_of_levelSet_bounds hconv hmono h0 hP0 hP hm0 hm)

/-- **Lebesgue-integral (`∫⁻`) level-set convex-integrand Pólya–Szegő inequality on `Ioi 0`**:
without any integrability hypotheses, if for a.e. `t ∈ Ioi 0`, `0 ≤ P_star t ≤ P_h t` and
`0 < m_h t ≤ m_star t`, then
`∫⁻ t in Ioi 0, ENNReal.ofReal (convexPerspective Φ (P_star t) (m_star t)) ≤
  ∫⁻ t in Ioi 0, ENNReal.ofReal (convexPerspective Φ (P_h t) (m_h t))`. -/
theorem setLIntegral_Ioi_ofReal_convexPerspective_le {Φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) Φ)
    (hmono : MonotoneOn Φ (Ici 0)) (h0 : Φ 0 = 0) {P_star P_h m_h m_star : ℝ → ℝ}
    (hP0 : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ P_star t)
    (hP : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), P_star t ≤ P_h t)
    (hm0 : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 < m_h t)
    (hm : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), m_h t ≤ m_star t) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (convexPerspective Φ (P_star t) (m_star t)) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (convexPerspective Φ (P_h t) (m_h t)) := by
  refine lintegral_mono_ae ?_
  filter_upwards [ae_convexPerspective_le_of_levelSet_bounds hconv hmono h0 hP0 hP hm0 hm] with t ht
  exact ENNReal.ofReal_le_ofReal ht

end ConvexPerspective

/-! ### Section 2: De la Vallée Poussin superlinear uniform integrability -/

section DeLaValleePoussin

/-- **Scalar de la Vallée Poussin splitting inequality**: if `0 < M`, `0 ≤ K`, `0 ≤ Φ t`, and
`K ≤ t → M * t ≤ Φ t`, then `t ≤ K + M⁻¹ * Φ t`. -/
theorem le_add_inv_mul_of_superlinear_on_Ici {Φ : ℝ → ℝ} {M K t : ℝ} (hM : 0 < M) (hK : 0 ≤ K)
    (hΦ_nonneg : 0 ≤ Φ t) (hsuper : K ≤ t → M * t ≤ Φ t) :
    t ≤ K + M⁻¹ * Φ t := by
  by_cases hKt : K ≤ t
  · have h1 : t ≤ M⁻¹ * Φ t := (le_inv_mul_iff₀ hM).mpr (hsuper hKt)
    linarith
  · have h2 : 0 ≤ M⁻¹ * Φ t := mul_nonneg (inv_nonneg.mpr hM.le) hΦ_nonneg
    linarith

/-- **Pointwise de la Vallée Poussin bound**: if `0 ≤ w x` on `A`, `0 < M`, `0 ≤ K`,
`∀ t ≥ 0, 0 ≤ Φ t`, and `∀ t ≥ K, M * t ≤ Φ t`, then for every `x ∈ A`,
`w x ≤ K + M⁻¹ * Φ (w x)`. -/
theorem pointwise_deLaValleePoussin_le {α : Type*} {Φ : ℝ → ℝ} {w : α → ℝ} {A : Set α}
    {M K : ℝ} (hM : 0 < M) (hK : 0 ≤ K) (hw : ∀ x ∈ A, 0 ≤ w x) (hΦ_nonneg : ∀ t ≥ 0, 0 ≤ Φ t)
    (hsuper : ∀ t ≥ K, M * t ≤ Φ t) {x : α} (hx : x ∈ A) :
    w x ≤ K + M⁻¹ * Φ (w x) :=
  le_add_inv_mul_of_superlinear_on_Ici hM hK (hΦ_nonneg (w x) (hw x hx)) (hsuper (w x))

/-- Extended-real (`ℝ≥0∞`) pointwise de la Vallée Poussin bound:
`ENNReal.ofReal (w x) ≤ ENNReal.ofReal K + ENNReal.ofReal M⁻¹ * ENNReal.ofReal (Φ (w x))`. -/
theorem ofReal_pointwise_deLaValleePoussin_le {α : Type*} {Φ : ℝ → ℝ} {w : α → ℝ} {A : Set α}
    {M K : ℝ} (hM : 0 < M) (hK : 0 ≤ K) (hw : ∀ x ∈ A, 0 ≤ w x) (hΦ_nonneg : ∀ t ≥ 0, 0 ≤ Φ t)
    (hsuper : ∀ t ≥ K, M * t ≤ Φ t) {x : α} (hx : x ∈ A) :
    ENNReal.ofReal (w x) ≤
      ENNReal.ofReal K + ENNReal.ofReal M⁻¹ * ENNReal.ofReal (Φ (w x)) := by
  calc ENNReal.ofReal (w x)
      ≤ ENNReal.ofReal (K + M⁻¹ * Φ (w x)) :=
        ENNReal.ofReal_le_ofReal (pointwise_deLaValleePoussin_le hM hK hw hΦ_nonneg hsuper hx)
    _ ≤ ENNReal.ofReal K + ENNReal.ofReal (M⁻¹ * Φ (w x)) := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal K + ENNReal.ofReal M⁻¹ * ENNReal.ofReal (Φ (w x)) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Bochner-integral de la Vallée Poussin inequality**: if `0 ≤ w x` on a measurable set `A` of
finite measure `μ A < ⊤`, `0 < M`, `0 ≤ K`, `∀ t ≥ 0, 0 ≤ Φ t`, and `∀ t ≥ K, M * t ≤ Φ t`, then
`∫ x in A, w x ∂μ ≤ K * (μ A).toReal + M⁻¹ * ∫ x in A, Φ (w x) ∂μ`. -/
theorem setIntegral_deLaValleePoussin_le {Φ : ℝ → ℝ} {w : α → ℝ} {A : Set α} {M K : ℝ}
    (hA : MeasurableSet A) (hμA : μ A < ⊤) (hM : 0 < M) (hK : 0 ≤ K)
    (hw : ∀ x ∈ A, 0 ≤ w x) (hΦ_nonneg : ∀ t ≥ 0, 0 ≤ Φ t) (hsuper : ∀ t ≥ K, M * t ≤ Φ t)
    (hint_w : IntegrableOn w A μ) (hint_Φ : IntegrableOn (fun x ↦ Φ (w x)) A μ) :
    ∫ x in A, w x ∂μ ≤ K * (μ A).toReal + M⁻¹ * ∫ x in A, Φ (w x) ∂μ := by
  have : IsFiniteMeasure (μ.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hμA⟩
  have hint_rhs : IntegrableOn (fun x ↦ K + M⁻¹ * Φ (w x)) A μ :=
    (integrable_const K).add (hint_Φ.const_mul M⁻¹)
  have hle : ∫ x in A, w x ∂μ ≤ ∫ x in A, (K + M⁻¹ * Φ (w x)) ∂μ := by
    refine setIntegral_mono_on hint_w hint_rhs hA fun x hx ↦ ?_
    exact pointwise_deLaValleePoussin_le hM hK hw hΦ_nonneg hsuper hx
  refine hle.trans_eq ?_
  rw [integral_add (integrable_const K) (hint_Φ.const_mul M⁻¹), integral_const_mul,
    setIntegral_const, smul_eq_mul, mul_comm (μ.real A) K, Measure.real_def]

/-- **Lebesgue-integral (`∫⁻`) de la Vallée Poussin inequality**: for any measurable set `A`,
`∫⁻ x in A, ENNReal.ofReal (w x) ∂μ ≤
  ENNReal.ofReal K * μ A + ENNReal.ofReal M⁻¹ * ∫⁻ x in A, ENNReal.ofReal (Φ (w x)) ∂μ`. -/
theorem setLIntegral_ofReal_deLaValleePoussin_le {Φ : ℝ → ℝ} {w : α → ℝ} {A : Set α} {M K : ℝ}
    (hA : MeasurableSet A) (hM : 0 < M) (hK : 0 ≤ K) (hw : ∀ x ∈ A, 0 ≤ w x)
    (hΦ_nonneg : ∀ t ≥ 0, 0 ≤ Φ t) (hsuper : ∀ t ≥ K, M * t ≤ Φ t)
    (hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (w x))) (μ.restrict A)) :
    ∫⁻ x in A, ENNReal.ofReal (w x) ∂μ ≤
      ENNReal.ofReal K * μ A +
        ENNReal.ofReal M⁻¹ * ∫⁻ x in A, ENNReal.ofReal (Φ (w x)) ∂μ := by
  have hmono : ∫⁻ x in A, ENNReal.ofReal (w x) ∂μ ≤
      ∫⁻ x in A,
        (ENNReal.ofReal K + ENNReal.ofReal M⁻¹ * ENNReal.ofReal (Φ (w x))) ∂μ := by
    refine setLIntegral_mono' hA fun x hx ↦ ?_
    exact ofReal_pointwise_deLaValleePoussin_le hM hK hw hΦ_nonneg hsuper hx
  refine hmono.trans_eq ?_
  rw [lintegral_add_left' aemeasurable_const, lintegral_const, Measure.restrict_apply_univ,
    lintegral_const_mul'' _ hmeas]

/-- Global superlinear bound specialization of `setLIntegral_ofReal_deLaValleePoussin_le`: if
`∫⁻ x, ENNReal.ofReal (Φ (w x)) ∂μ ≤ ENNReal.ofReal C` with `0 ≤ C`, then on every measurable set
`A`, `∫⁻ x in A, ENNReal.ofReal (w x) ∂μ ≤ ENNReal.ofReal K * μ A + ENNReal.ofReal (M⁻¹ * C)`. -/
theorem setLIntegral_ofReal_le_of_lintegral_comp_le {Φ : ℝ → ℝ} {w : α → ℝ} {A : Set α}
    {M K C : ℝ} (hA : MeasurableSet A) (hM : 0 < M) (hK : 0 ≤ K) (_hC : 0 ≤ C)
    (hw : ∀ x ∈ A, 0 ≤ w x) (hΦ_nonneg : ∀ t ≥ 0, 0 ≤ Φ t) (hsuper : ∀ t ≥ K, M * t ≤ Φ t)
    (hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (w x))) μ)
    (hbound : ∫⁻ x, ENNReal.ofReal (Φ (w x)) ∂μ ≤ ENNReal.ofReal C) :
    ∫⁻ x in A, ENNReal.ofReal (w x) ∂μ ≤
      ENNReal.ofReal K * μ A + ENNReal.ofReal (M⁻¹ * C) := by
  refine (setLIntegral_ofReal_deLaValleePoussin_le hA hM hK hw hΦ_nonneg hsuper
    hmeas.restrict).trans ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]
  gcongr
  exact (setLIntegral_le_lintegral _ _).trans hbound

/-- From superlinear growth `Tendsto (fun t ↦ Φ t / t) atTop atTop`, for every slope `M > 0` there
exists a threshold `K ≥ 0` such that `M * t ≤ Φ t` for all `t ≥ K`. -/
theorem exists_superlinear_cutoff_of_tendsto_div_atTop {Φ : ℝ → ℝ}
    (htend : Tendsto (fun t ↦ Φ t / t) atTop atTop) {M : ℝ} (_hM : 0 < M) :
    ∃ K ≥ 0, ∀ t ≥ K, M * t ≤ Φ t := by
  rcases (tendsto_atTop.mp htend M).exists_forall_of_atTop with ⟨K₀, hK₀⟩
  refine ⟨max K₀ 1, le_trans zero_le_one (le_max_right K₀ 1), fun t ht ↦ ?_⟩
  have ht1 : 0 < t := zero_lt_one.trans_le ((le_max_right K₀ 1).trans ht)
  exact (le_div_iff₀ ht1).mp (hK₀ t ((le_max_left K₀ 1).trans ht))

/-- **De la Vallée Poussin uniform-integrability theorem (`∫⁻_A w_j ≤ T μ A + ε`)**: if a family
`w : ι → α → ℝ` of nonnegative functions satisfies a uniform superlinear bound
`∀ j, ∫⁻ x, ENNReal.ofReal (Φ (w j x)) ∂μ ≤ ENNReal.ofReal C` where
`∀ M > 0, ∃ K ≥ 0, ∀ t ≥ K, M * t ≤ Φ t`, then for every `ε > 0` there exists `T : ℝ≥0` such that
for every `j : ι` and every measurable set `A : Set α`,
`∫⁻ x in A, ENNReal.ofReal (w j x) ∂μ ≤ T * μ A + ENNReal.ofReal ε`. -/
theorem uniform_setLIntegral_bound_of_superlinear {ι : Type*} {Φ : ℝ → ℝ} {w : ι → α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ j x, 0 ≤ w j x) (hΦ_nonneg : ∀ t ≥ 0, 0 ≤ Φ t)
    (hsuper : ∀ M > 0, ∃ K ≥ 0, ∀ t ≥ K, M * t ≤ Φ t)
    (hmeas : ∀ j, AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (w j x))) μ)
    (hbound : ∀ j, ∫⁻ x, ENNReal.ofReal (Φ (w j x)) ∂μ ≤ ENNReal.ofReal C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ≥0, ∀ (j : ι) ⦃A : Set α⦄, MeasurableSet A →
      ∫⁻ x in A, ENNReal.ofReal (w j x) ∂μ ≤ T * μ A + ENNReal.ofReal ε := by
  set M := (C + 1) / ε
  have hM : 0 < M := div_pos (by linarith) hε
  rcases hsuper M hM with ⟨K, hK, hKM⟩
  refine ⟨Real.toNNReal K, fun j A hA ↦ ?_⟩
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal K hK]
  refine (setLIntegral_ofReal_le_of_lintegral_comp_le hA hM hK hC (fun x _ ↦ hw j x) hΦ_nonneg
    hKM (hmeas j) (hbound j)).trans ?_
  have hMC : M⁻¹ * C ≤ ε := by
    rw [inv_mul_le_iff₀ hM]
    calc C ≤ C + 1 := by linarith
      _ = M * ε := (div_mul_cancel₀ (C + 1) hε.ne').symm
  gcongr

/-- **De la Vallée Poussin uniform-integrability theorem from `Φ t / t → ∞`**: if
`Tendsto (fun t ↦ Φ t / t) atTop atTop` and `∀ j, ∫⁻ x, ENNReal.ofReal (Φ (w j x)) ∂μ ≤
ENNReal.ofReal C`, then for every `ε > 0` there exists `T : ℝ≥0` such that for all `j : ι` and all
measurable `A : Set α`,
`∫⁻ x in A, ENNReal.ofReal (w j x) ∂μ ≤ T * μ A + ENNReal.ofReal ε`. -/
theorem uniform_setLIntegral_bound_of_tendsto_div_atTop {ι : Type*} {Φ : ℝ → ℝ} {w : ι → α → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ j x, 0 ≤ w j x) (hΦ_nonneg : ∀ t ≥ 0, 0 ≤ Φ t)
    (htend : Tendsto (fun t ↦ Φ t / t) atTop atTop)
    (hmeas : ∀ j, AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (w j x))) μ)
    (hbound : ∀ j, ∫⁻ x, ENNReal.ofReal (Φ (w j x)) ∂μ ≤ ENNReal.ofReal C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ≥0, ∀ (j : ι) ⦃A : Set α⦄, MeasurableSet A →
      ∫⁻ x in A, ENNReal.ofReal (w j x) ∂μ ≤ T * μ A + ENNReal.ofReal ε :=
  uniform_setLIntegral_bound_of_superlinear hC hw hΦ_nonneg
    (fun _ hM ↦ exists_superlinear_cutoff_of_tendsto_div_atTop htend hM) hmeas hbound hε

/-- **Bochner-integral de la Vallée Poussin uniform-integrability theorem (`∫_A w_j ≤ T |A| + ε`)**:
under `Tendsto (fun t ↦ Φ t / t) atTop atTop` and `∀ j, ∫ x, Φ (w j x) ∂μ ≤ C`, for every `ε > 0`
there exists `T : ℝ≥0` such that for all `j : ι` and all measurable sets `A` with `μ A < ⊤`,
`∫ x in A, w j x ∂μ ≤ T * (μ A).toReal + ε`. -/
theorem uniform_setIntegral_bound_of_tendsto_div_atTop {ι : Type*} {Φ : ℝ → ℝ} {w : ι → α → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ j x, 0 ≤ w j x) (hΦ_nonneg : ∀ t ≥ 0, 0 ≤ Φ t)
    (htend : Tendsto (fun t ↦ Φ t / t) atTop atTop)
    (hint_w : ∀ j ⦃A : Set α⦄, MeasurableSet A → μ A < ⊤ → IntegrableOn (w j) A μ)
    (hint_Φ : ∀ j, Integrable (fun x ↦ Φ (w j x)) μ)
    (hbound : ∀ j, ∫ x, Φ (w j x) ∂μ ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ≥0, ∀ (j : ι) ⦃A : Set α⦄, MeasurableSet A → μ A < ⊤ →
      ∫ x in A, w j x ∂μ ≤ T * (μ A).toReal + ε := by
  set M := (C + 1) / ε
  have hM : 0 < M := div_pos (by linarith) hε
  rcases exists_superlinear_cutoff_of_tendsto_div_atTop htend hM with ⟨K, hK, hKM⟩
  refine ⟨Real.toNNReal K, fun j A hA hμA ↦ ?_⟩
  rw [Real.coe_toNNReal K hK]
  have hle := setIntegral_deLaValleePoussin_le hA hμA hM hK (fun x _ ↦ hw j x) hΦ_nonneg hKM
    (hint_w j hA hμA) (hint_Φ j).integrableOn
  have hset_le : ∫ x in A, Φ (w j x) ∂μ ≤ C :=
    (setIntegral_le_integral (hint_Φ j) (Eventually.of_forall fun x ↦ hΦ_nonneg _ (hw j x))).trans
      (hbound j)
  have hMC : M⁻¹ * ∫ x in A, Φ (w j x) ∂μ ≤ ε := by
    calc M⁻¹ * ∫ x in A, Φ (w j x) ∂μ
        ≤ M⁻¹ * C := mul_le_mul_of_nonneg_left hset_le (inv_nonneg.mpr hM.le)
      _ ≤ ε := by
        rw [inv_mul_le_iff₀ hM]
        calc C ≤ C + 1 := by linarith
          _ = M * ε := (div_mul_cancel₀ (C + 1) hε.ne').symm
  linarith

end DeLaValleePoussin

/-! ### Section 3: Outer-regularity absolute continuity, singular exclusion, and truncation -/

section OuterRegularityAndSingularExclusion

/-- Predicate asserting that a measure `ν` satisfies a uniform open-set linear bound with respect to
`μ`: for every `ε > 0`, there exists `T : ℝ≥0` such that `ν U ≤ T * μ U + ENNReal.ofReal ε` for
every open set `U`. -/
def HasOpenLinearBound {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (ν μ : Measure α) : Prop :=
  ∀ ε > 0, ∃ T : ℝ≥0, ∀ U : Set α, IsOpen U → ν U ≤ T * μ U + ENNReal.ofReal ε

/-- If `ν U ≤ liminf (fun j : ℕ ↦ F j U) atTop` on every open set `U` and the sequence `F j`
satisfies `F j U ≤ T * μ U + ENNReal.ofReal ε` on every open set `U`, then `ν` satisfies
`HasOpenLinearBound ν μ`. -/
theorem hasOpenLinearBound_of_liminf_le {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {ν μ : Measure α} {F : ℕ → Set α → ℝ≥0∞}
    (hlsc : ∀ U : Set α, IsOpen U → ν U ≤ liminf (fun j ↦ F j U) atTop)
    (hunif : ∀ ε > 0, ∃ T : ℝ≥0, ∀ (j : ℕ) (U : Set α), IsOpen U →
      F j U ≤ T * μ U + ENNReal.ofReal ε) :
    HasOpenLinearBound ν μ := by
  intro ε hε
  rcases hunif ε hε with ⟨T, hT⟩
  refine ⟨T, fun U hU ↦ (hlsc U hU).trans ?_⟩
  exact liminf_le_of_frequently_le' (Eventually.of_forall fun j ↦ hT j U hU).frequently

/-- **Outer-regularity null-set theorem**: if `[μ.OuterRegular]` and for every `ε > 0` there exists
`T : ℝ≥0` such that `ν U ≤ T * μ U + ENNReal.ofReal ε` for all open sets `U`, then every `μ`-null
set `N` (`μ N = 0`) is also `ν`-null (`ν N = 0`). -/
theorem measure_eq_zero_of_open_linear_bound {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {ν μ : Measure α} [μ.OuterRegular] (hbound : HasOpenLinearBound ν μ)
    {N : Set α} (hN : μ N = 0) :
    ν N = 0 := by
  refine nonpos_iff_eq_zero.mp (ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_)
  rw [zero_add]
  have hε : 0 < (δ : ℝ) / 2 := half_pos (NNReal.coe_pos.mpr hδ)
  rcases hbound ((δ : ℝ) / 2) hε with ⟨T, hT⟩
  set η : ℝ≥0∞ := ENNReal.ofReal ((δ : ℝ) / 2) / ((T : ℝ≥0∞) + 1)
  have hη_ne : η ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨(ENNReal.ofReal_pos.mpr hε).ne', by simp⟩
  rcases exists_isOpen_le_add N μ hη_ne with ⟨U, hNU, hU_open, hμU⟩
  rw [hN, zero_add] at hμU
  have hT_mul : (T : ℝ≥0∞) * μ U ≤ ENNReal.ofReal ((δ : ℝ) / 2) := by
    calc (T : ℝ≥0∞) * μ U
        ≤ ((T : ℝ≥0∞) + 1) * η := mul_le_mul' (self_le_add_right _ 1) hμU
      _ = ENNReal.ofReal ((δ : ℝ) / 2) :=
        ENNReal.mul_div_cancel (by simp) (by simp)
  calc ν N ≤ ν U := measure_mono hNU
    _ ≤ T * μ U + ENNReal.ofReal ((δ : ℝ) / 2) := hT U hU_open
    _ ≤ ENNReal.ofReal ((δ : ℝ) / 2) + ENNReal.ofReal ((δ : ℝ) / 2) := by gcongr
    _ = ENNReal.ofReal ((δ : ℝ) / 2 + (δ : ℝ) / 2) := (ENNReal.ofReal_add hε.le hε.le).symm
    _ = δ := by rw [add_halves, ENNReal.ofReal_coe_nnreal]

/-- **Outer-regularity absolute-continuity theorem (`ν ≪ μ`)**: if `[μ.OuterRegular]` and
`HasOpenLinearBound ν μ` holds, then `ν` is absolutely continuous with respect to `μ` (`ν ≪ μ`). -/
theorem absolutelyContinuous_of_open_linear_bound {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {ν μ : Measure α} [μ.OuterRegular] (hbound : HasOpenLinearBound ν μ) :
    ν ≪ μ :=
  Measure.AbsolutelyContinuous.mk fun _ _ hN ↦ measure_eq_zero_of_open_linear_bound hbound hN

/-- Method alias for `absolutelyContinuous_of_open_linear_bound`. -/
theorem HasOpenLinearBound.absolutelyContinuous {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {ν μ : Measure α} [μ.OuterRegular] (hbound : HasOpenLinearBound ν μ) :
    ν ≪ μ :=
  absolutelyContinuous_of_open_linear_bound hbound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Vanishing of the singular variation measure (`singularVariationMeasure ν = 0`)**: if a Radon
variation measure `ν : Measure E` satisfies `HasOpenLinearBound ν volume`, then
`singularVariationMeasure ν = 0` and `acVariationMeasure ν = ν`. -/
theorem singularVariationMeasure_eq_zero_of_open_linear_bound {ν : Measure E}
    [ν.HaveLebesgueDecomposition volume] (hbound : HasOpenLinearBound ν volume) :
    singularVariationMeasure ν = 0 ∧ acVariationMeasure ν = ν :=
  ⟨(singularVariationMeasure_eq_zero_iff ν).mpr hbound.absolutelyContinuous,
   (acVariationMeasure_eq_self_iff ν).mpr hbound.absolutelyContinuous⟩

/-- **Exclusion of jump, Cantor, and point singular concentration**: if
`HasOpenLinearBound ν volume` holds, then `ν S = 0` for every Lebesgue-null set `S : Set E`
(`volume S = 0`). -/
theorem measure_null_eq_zero_of_open_linear_bound {ν : Measure E}
    (hbound : HasOpenLinearBound ν volume) {S : Set E} (hS : volume S = 0) :
    ν S = 0 :=
  measure_eq_zero_of_open_linear_bound hbound hS

/-- Under `HasOpenLinearBound ν volume` and `[NullSingletonClass (volume : Measure E)]`,
`ν {x} = 0` for every point `x : E` (in particular `ν {0} = 0`, ruling out point-mass concentration
at the origin). -/
theorem measure_singleton_eq_zero_of_open_linear_bound {ν : Measure E}
    [NullSingletonClass (volume : Measure E)] (hbound : HasOpenLinearBound ν volume) (x : E) :
    ν {x} = 0 :=
  measure_null_eq_zero_of_open_linear_bound hbound (measure_singleton x)

/-- **Weak-gradient recovery and singular exclusion on `U`**: if `HasDerivativeMeasureOn u U σ ν`
holds on a measurable set `U` with `ν U < ⊤`, `AEStronglyMeasurable σ (volume.restrict U)`, and
`HasOpenLinearBound ν volume`, then `singularVariationMeasure ν = 0`,
`HasWeakGradientOn u (approxGradient σ ν) U`, and
`∫⁻ x in U, ‖approxGradient σ ν x‖ₑ ∂volume ≤ ν U`. -/
theorem HasDerivativeMeasureOn.hasWeakGradientOn_of_open_linear_bound {u : E → ℝ} {U : Set E}
    {σ : E → E} {ν : Measure E} [SigmaFinite ν] [ν.HaveLebesgueDecomposition volume]
    (h : HasDerivativeMeasureOn u U σ ν) (hU : MeasurableSet U) (hνU : ν U < ⊤)
    (hσ : AEStronglyMeasurable σ (volume.restrict U)) (hbound : HasOpenLinearBound ν volume) :
    singularVariationMeasure ν = 0 ∧
      HasWeakGradientOn u (approxGradient σ ν) U ∧
      ∫⁻ x in U, ‖approxGradient σ ν x‖ₑ ∂volume ≤ ν U :=
  ⟨(singularVariationMeasure_eq_zero_iff ν).mpr hbound.absolutelyContinuous,
   h.hasWeakGradientOn_approxGradient_of_absolutelyContinuous hU hbound.absolutelyContinuous hνU hσ,
   h.lintegral_enorm_approxGradient_le_of_absolutelyContinuous hU hbound.absolutelyContinuous⟩

/-- **Polar weak-gradient recovery, singular exclusion, and `L¹` gradient-norm identity**: if
`HasPolarDerivativeMeasureOn u_star univ σ ν` holds with `ν univ < ⊤`,
`AEStronglyMeasurable σ volume`, and `HasOpenLinearBound ν volume`, then:
1. `singularVariationMeasure ν = 0` and `acVariationMeasure ν = ν`,
2. `HasWeakGradientOn u_star (approxGradient σ ν) univ`,
3. `∫⁻ x, ‖approxGradient σ ν x‖ₑ ∂volume = ν univ`. -/
theorem HasPolarDerivativeMeasureOn.hasWeakGradientOn_of_open_linear_bound {u_star : E → ℝ}
    {σ : E → E} {ν : Measure E} [SigmaFinite ν] [ν.HaveLebesgueDecomposition volume]
    (h : HasPolarDerivativeMeasureOn u_star univ σ ν) (hν : ν univ < ⊤)
    (hσ : AEStronglyMeasurable σ volume) (hbound : HasOpenLinearBound ν volume) :
    singularVariationMeasure ν = 0 ∧
      acVariationMeasure ν = ν ∧
      HasWeakGradientOn u_star (approxGradient σ ν) univ ∧
      ∫⁻ x, ‖approxGradient σ ν x‖ₑ ∂volume = ν univ := by
  have hac := hbound.absolutelyContinuous
  have hσ_univ : AEStronglyMeasurable σ (volume.restrict univ) := by
    rwa [Measure.restrict_univ]
  have h_eq := h.lintegral_enorm_approxGradient_eq_of_absolutelyContinuous MeasurableSet.univ hac
  rw [Measure.restrict_univ] at h_eq
  exact ⟨(singularVariationMeasure_eq_zero_iff ν).mpr hac,
    (acVariationMeasure_eq_self_iff ν).mpr hac,
    h.hasDerivativeMeasureOn.hasWeakGradientOn_approxGradient_of_absolutelyContinuous
      MeasurableSet.univ hac hν hσ_univ,
    h_eq⟩

/-- **Gradient `L¹`-norm Pólya–Szegő deduction (`∫ ‖g‖ ≤ ∫ ‖∇u‖`)**: under the hypotheses of
`HasPolarDerivativeMeasureOn.hasWeakGradientOn_of_open_linear_bound`, if `grad_u : E → E` is
Lebesgue-integrable and `ν univ ≤ ∫⁻ x, ‖grad_u x‖ₑ ∂volume`, then `approxGradient σ ν` is
Lebesgue-integrable and satisfies
`∫ x, ‖approxGradient σ ν x‖ ∂volume ≤ ∫ x, ‖grad_u x‖ ∂volume`. -/
theorem HasPolarDerivativeMeasureOn.integral_norm_approxGradient_le_of_open_linear_bound
    {u_star : E → ℝ} {σ grad_u : E → E} {ν : Measure E} [SigmaFinite ν]
    [ν.HaveLebesgueDecomposition volume] (h : HasPolarDerivativeMeasureOn u_star univ σ ν)
    (hν : ν univ < ⊤) (hσ : AEStronglyMeasurable σ volume) (hbound : HasOpenLinearBound ν volume)
    (hgrad : Integrable grad_u volume)
    (hle : ν univ ≤ ∫⁻ x, ‖grad_u x‖ₑ ∂volume) :
    ∫ x, ‖approxGradient σ ν x‖ ∂volume ≤ ∫ x, ‖grad_u x‖ ∂volume := by
  rcases h.hasWeakGradientOn_of_open_linear_bound hν hσ hbound with ⟨_, _, hwg, heq⟩
  have hint_g : Integrable (approxGradient σ ν) volume := by
    simpa [IntegrableOn, Measure.restrict_univ] using hwg.integrableOn
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ norm_nonneg _),
    ofReal_integral_norm_eq_lintegral_enorm hint_g, ofReal_integral_norm_eq_lintegral_enorm hgrad]
  exact heq.trans_le hle

/-! ### Positive/negative-part truncation and variation subadditivity -/

/-- Real identity decomposing `|t|` into positive and negative parts:
`|t| = max t 0 + max (-t) 0`. -/
theorem abs_eq_max_zero_add_max_neg_zero (t : ℝ) :
    |t| = max t 0 + max (-t) 0 := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), add_zero]
  · rw [abs_of_nonpos ht, max_eq_right ht, max_eq_left (neg_nonneg.mpr ht), zero_add]

/-- Real identity decomposing `t` into positive and negative parts:
`t = max t 0 - max (-t) 0`. -/
theorem self_eq_max_zero_sub_max_neg_zero (t : ℝ) :
    t = max t 0 - max (-t) 0 := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), sub_zero]
  · rw [max_eq_right ht, max_eq_left (neg_nonneg.mpr ht), zero_sub, neg_neg]

/-- Real identity expressing `max t 0 = 2⁻¹ * (t + |t|)`. -/
theorem max_zero_eq_half_add_abs (t : ℝ) :
    max t 0 = 2⁻¹ * (t + |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, abs_of_nonneg ht]; ring
  · rw [max_eq_right ht, abs_of_nonpos ht]; ring

/-- Function-level positive/negative-part decomposition of `fun x ↦ |u x|`. -/
theorem abs_fun_eq_add_max_zero {α : Type*} (u : α → ℝ) :
    (fun x ↦ |u x|) = (fun x ↦ max (u x) 0) + fun x ↦ max (-u x) 0 := by
  ext x; exact abs_eq_max_zero_add_max_neg_zero (u x)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If `u : E → ℝ` is locally integrable on `s`, then its positive part `fun x ↦ max (u x) 0` is
locally integrable on `s`. -/
theorem _root_.MeasureTheory.LocallyIntegrableOn.max_zero {s : Set E} {μ : Measure E} {u : E → ℝ}
    (hu : LocallyIntegrableOn u s μ) :
    LocallyIntegrableOn (fun x ↦ max (u x) 0) s μ := by
  have habs : LocallyIntegrableOn (fun x ↦ |u x|) s μ := by
    simpa only [Real.norm_eq_abs] using hu.norm
  have heq : (fun x ↦ max (u x) 0) = (2⁻¹ : ℝ) • (u + fun x ↦ |u x|) := by
    ext x; exact max_zero_eq_half_add_abs (u x)
  rw [heq]
  exact (hu.add habs).smul 2⁻¹

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If `u : E → ℝ` is locally integrable on `s`, then its negative part `fun x ↦ max (-u x) 0` is
locally integrable on `s`. -/
theorem _root_.MeasureTheory.LocallyIntegrableOn.max_neg_zero {s : Set E} {μ : Measure E}
    {u : E → ℝ} (hu : LocallyIntegrableOn u s μ) :
    LocallyIntegrableOn (fun x ↦ max (-u x) 0) s μ :=
  hu.neg.max_zero

/-- **Truncation subadditivity of distributional total variation for `|u|`**: for any locally
integrable function `u : E → ℝ` on `Ω : Opens E`,
`distributionalVariation μ Ω (fun x ↦ |u x|) ≤
  distributionalVariation μ Ω (fun x ↦ max (u x) 0) +
    distributionalVariation μ Ω (fun x ↦ max (-u x) 0)`. -/
theorem distributionalVariation_abs_le_add_max_zero {μ : Measure E} {Ω : Opens E} {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) :
    distributionalVariation μ Ω (fun x ↦ |u x|) ≤
      distributionalVariation μ Ω (fun x ↦ max (u x) 0) +
        distributionalVariation μ Ω (fun x ↦ max (-u x) 0) := by
  rw [abs_fun_eq_add_max_zero]
  exact distributionalVariation_add_le hu.max_zero hu.max_neg_zero

/-- **Positive/negative-part subadditivity of distributional total variation for `u`**: for any
locally integrable function `u : E → ℝ` on `Ω : Opens E`,
`distributionalVariation μ Ω u ≤
  distributionalVariation μ Ω (fun x ↦ max (u x) 0) +
    distributionalVariation μ Ω (fun x ↦ max (-u x) 0)`. -/
theorem distributionalVariation_le_add_max_zero {μ : Measure E} {Ω : Opens E} {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) :
    distributionalVariation μ Ω u ≤
      distributionalVariation μ Ω (fun x ↦ max (u x) 0) +
        distributionalVariation μ Ω (fun x ↦ max (-u x) 0) := by
  have heq : u = (fun x ↦ max (u x) 0) + -(fun x ↦ max (-u x) 0) := by
    ext x; exact self_eq_max_zero_sub_max_neg_zero (u x)
  conv_lhs => rw [heq]
  refine (distributionalVariation_add_le hu.max_zero hu.max_neg_zero.neg).trans ?_
  rw [distributionalVariation_neg]

end OuterRegularityAndSingularExclusion

end TauCeti
