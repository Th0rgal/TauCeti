/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.MeasureTheory.Measure.ConvexPolyaSzego
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.RadonVariationMeasure
import all TauCeti.MeasureTheory.Measure.StrictApproximation
import all TauCeti.MeasureTheory.Measure.ConvexPolyaSzego

/-!
# Superlevel Distribution Derivative, Sharp BV Sobolev Equality Analysis, and Ball Near-Extremizers

This file develops the superlevel distribution function
`distributionFunc μ h t = (μ {h > t}).toReal`, the coarea level-weight inequality
`m_h(t) ≤ -μ_h'(t)` and its equality `m_{h*}(t) = -μ_h'(t)` when flat sets have measure zero, the
sign-cancellation and superlevel-constancy equality analysis for the sharp BV Sobolev inequality,
the nonattainment of the sharp BV Sobolev constant by any nonzero `W¹,¹` function
(`HasWeakGradientOn`), and explicit radial near-extremizers `radialBallNearExtremizer a r ε`
converging to the ball indicator with asymptotic Sobolev quotient equal to the sharp constant
`n * ω_n ^ (1 / n)`:

1. **Superlevel distribution function and level-weight derivative comparison**:
   `TauCeti.superlevelSet`, `TauCeti.slabSet`, `TauCeti.distributionFunc`,
   `TauCeti.superlevelSet_antitone`, `TauCeti.distributionFunc_nonneg`,
   `TauCeti.distributionFunc_sub_eq_toReal_slabSet`, `TauCeti.distributionFunc_antitone`,
   `TauCeti.slab_integral_le_distributionFunc_sub`,
   `TauCeti.levelWeight_le_neg_hasDerivAt_distributionFunc`,
   `TauCeti.levelWeight_le_neg_deriv_distributionFunc`,
   `TauCeti.slab_integral_eq_distributionFunc_sub_of_flat_null`, and
   `TauCeti.levelWeight_eq_neg_deriv_distributionFunc_of_flat_null`.
2. **Sharp BV Sobolev equality analysis and nonattainment by nonzero `W¹,¹` functions**:
   `TauCeti.rpow_add_rpow_lt_add_rpow_of_pos`, `TauCeti.rpow_add_rpow_inv_le_add`,
   `TauCeti.rpow_add_rpow_inv_eq_add_iff`,
   `TauCeti.single_sign_of_sobolev_equality`,
   `TauCeti.measure_between_eq_zero_of_superlevel_const`,
   `TauCeti.ae_eq_indicator_of_superlevel_step`,
   `TauCeti.eq_zero_of_ac_and_mutuallySingular_eq`,
   `TauCeti.HasWeakGradientOn.eq_zero_of_gradientVariationMeasure_eq_mutuallySingular`, and
   `TauCeti.HasWeakGradientOn.eq_zero_const_of_singular_perimeter_eq`.
3. **Explicit radial ball near-extremizers and asymptotic sharp Sobolev quotient**:
   `TauCeti.radialCutoffProfile`, `TauCeti.radialBallNearExtremizer`,
   `TauCeti.radialBallNearExtremizer_nonneg`, `TauCeti.radialBallNearExtremizer_le_one`,
   `TauCeti.radialBallNearExtremizer_eq_one_of_mem_closedBall`,
   `TauCeti.radialBallNearExtremizer_eq_zero_of_notMem_ball`,
   `TauCeti.indicator_closedBall_le_radialBallNearExtremizer`,
   `TauCeti.radialBallNearExtremizer_le_indicator_ball`,
   `TauCeti.lipschitzWith_radialBallNearExtremizer`,
   `TauCeti.hasDerivAt_radialCutoffProfile_of_mem_Ioo`,
   `TauCeti.tendsto_shell_gradient_energy`, and
   `TauCeti.tendsto_sobolev_quotient_sharp_constant`.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

/-! ### Section 1: Superlevel distribution function and level-weight derivative comparison -/

section DistributionFunction

variable {α : Type*}

/-- The strict superlevel set `{x | t < h x}` of a real-valued function `h : α → ℝ` at level `t`. -/
def superlevelSet (h : α → ℝ) (t : ℝ) : Set α :=
  {x | t < h x}

/-- The half-open slab set `{x | t₁ < h x ∧ h x ≤ t₂}` between levels `t₁` and `t₂`. -/
def slabSet (h : α → ℝ) (t₁ t₂ : ℝ) : Set α :=
  {x | t₁ < h x ∧ h x ≤ t₂}

/-- Membership in `superlevelSet h t`. -/
@[simp] theorem mem_superlevelSet_iff {h : α → ℝ} {t : ℝ} {x : α} :
    x ∈ superlevelSet h t ↔ t < h x := Iff.rfl

/-- Membership in `slabSet h t₁ t₂`. -/
@[simp] theorem mem_slabSet_iff {h : α → ℝ} {t₁ t₂ : ℝ} {x : α} :
    x ∈ slabSet h t₁ t₂ ↔ t₁ < h x ∧ h x ≤ t₂ := Iff.rfl

/-- `t ↦ superlevelSet h t` is antitone. -/
theorem superlevelSet_antitone (h : α → ℝ) : Antitone (superlevelSet h) :=
  fun _ _ ht _ hx ↦ ht.trans_lt hx

/-- Decomposition `slabSet h t₁ t₂ = superlevelSet h t₁ \ superlevelSet h t₂`. -/
theorem slabSet_eq_diff (h : α → ℝ) (t₁ t₂ : ℝ) :
    slabSet h t₁ t₂ = superlevelSet h t₁ \ superlevelSet h t₂ := by
  ext x; simp [slabSet, superlevelSet]

/-- For `t₁ ≤ t₂`, `superlevelSet h t₂ ∪ slabSet h t₁ t₂ = superlevelSet h t₁`. -/
theorem superlevelSet_union_slabSet (h : α → ℝ) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    superlevelSet h t₂ ∪ slabSet h t₁ t₂ = superlevelSet h t₁ := by
  rw [slabSet_eq_diff, union_sdiff_cancel (superlevelSet_antitone h ht)]

/-- `superlevelSet h t₂` and `slabSet h t₁ t₂` are disjoint. -/
theorem disjoint_superlevelSet_slabSet (h : α → ℝ) (t₁ t₂ : ℝ) :
    Disjoint (superlevelSet h t₂) (slabSet h t₁ t₂) := by
  rw [slabSet_eq_diff]; exact disjoint_sdiff_self_right

variable [MeasurableSpace α]

/-- Measurability of `superlevelSet h t` for measurable `h : α → ℝ`. -/
theorem _root_.Measurable.measurableSet_superlevelSet {h : α → ℝ} (hh : Measurable h) (t : ℝ) :
    MeasurableSet (superlevelSet h t) :=
  hh measurableSet_Ioi

/-- Measurability of `slabSet h t₁ t₂` for measurable `h : α → ℝ`. -/
theorem _root_.Measurable.measurableSet_slabSet {h : α → ℝ} (hh : Measurable h) (t₁ t₂ : ℝ) :
    MeasurableSet (slabSet h t₁ t₂) := by
  rw [slabSet_eq_diff]
  exact (hh.measurableSet_superlevelSet t₁).diff (hh.measurableSet_superlevelSet t₂)

/-- The **distribution function** `distributionFunc μ h t = (μ (superlevelSet h t)).toReal`
measuring the volume of `{x | t < h x}`. -/
def distributionFunc (μ : Measure α) (h : α → ℝ) (t : ℝ) : ℝ :=
  (μ (superlevelSet h t)).toReal

/-- Nonnegativity of `distributionFunc μ h t`. -/
theorem distributionFunc_nonneg (μ : Measure α) (h : α → ℝ) (t : ℝ) :
    0 ≤ distributionFunc μ h t :=
  ENNReal.toReal_nonneg

/-- Exact slab-measure increment formula: if `Measurable h`, `t₀ ≤ t₁ ≤ t₂`, and
`μ (superlevelSet h t₀) ≠ ⊤`, then
`distributionFunc μ h t₁ - distributionFunc μ h t₂ = (μ (slabSet h t₁ t₂)).toReal`. -/
theorem distributionFunc_sub_eq_toReal_slabSet {μ : Measure α} {h : α → ℝ} (hh : Measurable h)
    {t₀ t₁ t₂ : ℝ} (ht₀ : t₀ ≤ t₁) (ht : t₁ ≤ t₂) (hfin : μ (superlevelSet h t₀) ≠ ⊤) :
    distributionFunc μ h t₁ - distributionFunc μ h t₂ = (μ (slabSet h t₁ t₂)).toReal := by
  have hfin₁ : μ (superlevelSet h t₁) ≠ ⊤ :=
    ((measure_mono (superlevelSet_antitone h ht₀)).trans_lt hfin.lt_top).ne
  have hfin₂ : μ (superlevelSet h t₂) ≠ ⊤ :=
    ((measure_mono (superlevelSet_antitone h (ht₀.trans ht))).trans_lt hfin.lt_top).ne
  have hfin_slab : μ (slabSet h t₁ t₂) ≠ ⊤ := by
    rw [slabSet_eq_diff]
    exact ((measure_mono sdiff_subset).trans_lt hfin₁.lt_top).ne
  have hunion : μ (superlevelSet h t₁) = μ (superlevelSet h t₂) + μ (slabSet h t₁ t₂) := by
    rw [← superlevelSet_union_slabSet h ht,
      measure_union (disjoint_superlevelSet_slabSet h t₁ t₂) (hh.measurableSet_slabSet t₁ t₂)]
  simp only [distributionFunc, hunion, ENNReal.toReal_add hfin₂ hfin_slab, add_sub_cancel_left]

/-- Antitonicity of `distributionFunc μ h` on `[t₀, ∞)` when `μ (superlevelSet h t₀) ≠ ⊤`. -/
theorem distributionFunc_antitone {μ : Measure α} {h : α → ℝ} {t₀ t₁ t₂ : ℝ}
    (ht₀ : t₀ ≤ t₁) (ht : t₁ ≤ t₂) (hfin : μ (superlevelSet h t₀) ≠ ⊤) :
    distributionFunc μ h t₂ ≤ distributionFunc μ h t₁ := by
  have hfin₁ : μ (superlevelSet h t₁) ≠ ⊤ :=
    ((measure_mono (superlevelSet_antitone h ht₀)).trans_lt hfin.lt_top).ne
  exact ENNReal.toReal_mono hfin₁ (measure_mono (superlevelSet_antitone h ht))

/-- **Coarea slab-integral bound (`∫_{t₁}^{t₂} m_h ≤ μ_h(t₁) - μ_h(t₂)`)**: if `m_h : ℝ → ℝ`
satisfies the coarea bound `∫ τ in Ioc t₁ t₂, m_h τ ≤ (μ (slabSet h t₁ t₂ ∩ S)).toReal` for some
set `S : Set α` (such as `{x | grad_h x ≠ 0}`), `Measurable h`, `t₀ ≤ t₁ ≤ t₂`, and
`μ (superlevelSet h t₀) ≠ ⊤`, then
`∫ τ in Ioc t₁ t₂, m_h τ ≤ distributionFunc μ h t₁ - distributionFunc μ h t₂`. -/
theorem slab_integral_le_distributionFunc_sub {μ : Measure α} {h : α → ℝ} {m_h : ℝ → ℝ}
    {S : Set α} (hh : Measurable h) {t₀ t₁ t₂ : ℝ} (ht₀ : t₀ ≤ t₁) (ht : t₁ ≤ t₂)
    (hfin : μ (superlevelSet h t₀) ≠ ⊤)
    (hcoarea : ∫ τ in Ioc t₁ t₂, m_h τ ≤ (μ (slabSet h t₁ t₂ ∩ S)).toReal) :
    ∫ τ in Ioc t₁ t₂, m_h τ ≤ distributionFunc μ h t₁ - distributionFunc μ h t₂ := by
  have hfin₁ : μ (superlevelSet h t₁) ≠ ⊤ :=
    ((measure_mono (superlevelSet_antitone h ht₀)).trans_lt hfin.lt_top).ne
  have hfin_slab : μ (slabSet h t₁ t₂) ≠ ⊤ := by
    rw [slabSet_eq_diff]
    exact ((measure_mono sdiff_subset).trans_lt hfin₁.lt_top).ne
  rw [distributionFunc_sub_eq_toReal_slabSet hh ht₀ ht hfin]
  exact hcoarea.trans (ENNReal.toReal_mono hfin_slab (measure_mono inter_subset_left))

/-- Right-hand difference quotient convergence `(s - t)⁻¹ * (f t - f s) → -d` as `s → t⁺` from
`HasDerivAt f d t`. -/
theorem tendsto_neg_slope_nhdsWithin_Ioi_of_hasDerivAt {f : ℝ → ℝ} {d t : ℝ}
    (hd : HasDerivAt f d t) :
    Tendsto (fun s ↦ (s - t)⁻¹ * (f t - f s)) (𝓝[>] t) (𝓝 (-d)) := by
  have hslope : Tendsto (slope f t) (𝓝[>] t) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono t fun s (hs : t < s) ↦ hs.ne')
  have hneg := hslope.neg
  refine hneg.congr' (Eventually.of_forall fun s ↦ ?_)
  simp [slope_def_field, div_eq_inv_mul, mul_sub]

/-- **Coarea level-weight derivative inequality (`m_h(t) ≤ -μ_h'(t)`)**: if
`∫ τ in Ioc t s, m_h τ ≤ distributionFunc μ h t - distributionFunc μ h s` for all `s > t`,
`HasDerivAt (distributionFunc μ h) d_μ t`, and the right-hand average of `m_h` over `(t, s]`
converges to `m_h t` as `s → t⁺`, then `m_h t ≤ -d_μ`. -/
theorem levelWeight_le_neg_hasDerivAt_distributionFunc {μ : Measure α} {h : α → ℝ} {m_h : ℝ → ℝ}
    {t d_μ : ℝ}
    (hslab : ∀ s > t, ∫ τ in Ioc t s, m_h τ ≤ distributionFunc μ h t - distributionFunc μ h s)
    (hd : HasDerivAt (distributionFunc μ h) d_μ t)
    (hlebesgue : Tendsto (fun s ↦ (s - t)⁻¹ * ∫ τ in Ioc t s, m_h τ) (𝓝[>] t) (𝓝 (m_h t))) :
    m_h t ≤ -d_μ := by
  refine le_of_tendsto_of_tendsto hlebesgue (tendsto_neg_slope_nhdsWithin_Ioi_of_hasDerivAt hd) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
  exact mul_le_mul_of_nonneg_left (hslab s hs) (inv_nonneg.mpr (sub_pos.mpr hs).le)

/-- Derivative form of `levelWeight_le_neg_hasDerivAt_distributionFunc`: if `distributionFunc μ h`
is differentiable at `t`, then `m_h t ≤ -deriv (distributionFunc μ h) t`. -/
theorem levelWeight_le_neg_deriv_distributionFunc {μ : Measure α} {h : α → ℝ} {m_h : ℝ → ℝ}
    {t : ℝ}
    (hslab : ∀ s > t, ∫ τ in Ioc t s, m_h τ ≤ distributionFunc μ h t - distributionFunc μ h s)
    (hd : DifferentiableAt ℝ (distributionFunc μ h) t)
    (hlebesgue : Tendsto (fun s ↦ (s - t)⁻¹ * ∫ τ in Ioc t s, m_h τ) (𝓝[>] t) (𝓝 (m_h t))) :
    m_h t ≤ -deriv (distributionFunc μ h) t :=
  levelWeight_le_neg_hasDerivAt_distributionFunc hslab hd.hasDerivAt hlebesgue

/-- When the flat/critical set `{x | 0 < h x ∧ x ∉ S}` has measure zero and `0 ≤ t₁ ≤ t₂`,
`μ (slabSet h t₁ t₂ ∩ S) = μ (slabSet h t₁ t₂)`. -/
theorem measure_slabSet_inter_eq_of_flat_null {μ : Measure α} {h : α → ℝ} {S : Set α}
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (hflat : μ {x | 0 < h x ∧ x ∉ S} = 0) :
    μ (slabSet h t₁ t₂ ∩ S) = μ (slabSet h t₁ t₂) := by
  refine measure_eq_measure_of_null_sdiff inter_subset_left ?_
  refine measure_mono_null (fun x ⟨⟨hx1, _⟩, hxS⟩ ↦ ?_) hflat
  exact ⟨ht₁.trans_lt hx1, fun hmem ↦ hxS ⟨⟨hx1, by assumption⟩, hmem⟩⟩

/-- **Exact slab-integral identity when flat sets have measure zero**: if `Measurable h`,
`0 ≤ t₀ ≤ t₁ ≤ t₂`, `μ (superlevelSet h t₀) ≠ ⊤`, `μ {x | 0 < h x ∧ x ∉ S} = 0`, and
`∫ τ in Ioc t₁ t₂, m_h τ = (μ (slabSet h t₁ t₂ ∩ S)).toReal`, then
`∫ τ in Ioc t₁ t₂, m_h τ = distributionFunc μ h t₁ - distributionFunc μ h t₂`. -/
theorem slab_integral_eq_distributionFunc_sub_of_flat_null {μ : Measure α} {h : α → ℝ}
    {m_h : ℝ → ℝ} {S : Set α} (hh : Measurable h) {t₀ t₁ t₂ : ℝ} (ht₀0 : 0 ≤ t₀)
    (ht₀ : t₀ ≤ t₁) (ht : t₁ ≤ t₂) (hfin : μ (superlevelSet h t₀) ≠ ⊤)
    (hflat : μ {x | 0 < h x ∧ x ∉ S} = 0)
    (hcoarea : ∫ τ in Ioc t₁ t₂, m_h τ = (μ (slabSet h t₁ t₂ ∩ S)).toReal) :
    ∫ τ in Ioc t₁ t₂, m_h τ = distributionFunc μ h t₁ - distributionFunc μ h t₂ := by
  rw [hcoarea, measure_slabSet_inter_eq_of_flat_null (ht₀0.trans ht₀) hflat,
    distributionFunc_sub_eq_toReal_slabSet hh ht₀ ht hfin]

/-- **Exact level-weight derivative identity (`m_{h*}(t) = -μ_h'(t)`)**: if
`∫ τ in Ioc t s, m_h τ = distributionFunc μ h t - distributionFunc μ h s` for all `s > t`,
`HasDerivAt (distributionFunc μ h) d_μ t`, and the right-hand average of `m_h` over `(t, s]`
converges to `m_h t` as `s → t⁺`, then `m_h t = -d_μ`. -/
theorem levelWeight_eq_neg_hasDerivAt_distributionFunc_of_flat_null {μ : Measure α} {h : α → ℝ}
    {m_h : ℝ → ℝ} {t d_μ : ℝ}
    (hslab : ∀ s > t, ∫ τ in Ioc t s, m_h τ = distributionFunc μ h t - distributionFunc μ h s)
    (hd : HasDerivAt (distributionFunc μ h) d_μ t)
    (hlebesgue : Tendsto (fun s ↦ (s - t)⁻¹ * ∫ τ in Ioc t s, m_h τ) (𝓝[>] t) (𝓝 (m_h t))) :
    m_h t = -d_μ := by
  have hev : (fun s ↦ (s - t)⁻¹ * ∫ τ in Ioc t s, m_h τ) =ᶠ[𝓝[>] t]
      fun s ↦ (s - t)⁻¹ * (distributionFunc μ h t - distributionFunc μ h s) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
    rw [hslab s hs]
  exact tendsto_nhds_unique hlebesgue
    ((tendsto_neg_slope_nhdsWithin_Ioi_of_hasDerivAt hd).congr' hev.symm)

/-- Derivative form of `levelWeight_eq_neg_hasDerivAt_distributionFunc_of_flat_null`:
`m_h t = -deriv (distributionFunc μ h) t`. -/
theorem levelWeight_eq_neg_deriv_distributionFunc_of_flat_null {μ : Measure α} {h : α → ℝ}
    {m_h : ℝ → ℝ} {t : ℝ}
    (hslab : ∀ s > t, ∫ τ in Ioc t s, m_h τ = distributionFunc μ h t - distributionFunc μ h s)
    (hd : DifferentiableAt ℝ (distributionFunc μ h) t)
    (hlebesgue : Tendsto (fun s ↦ (s - t)⁻¹ * ∫ τ in Ioc t s, m_h τ) (𝓝[>] t) (𝓝 (m_h t))) :
    m_h t = -deriv (distributionFunc μ h) t :=
  levelWeight_eq_neg_hasDerivAt_distributionFunc_of_flat_null hslab hd.hasDerivAt hlebesgue

end DistributionFunction

/-! ### Section 2: Sharp BV Sobolev equality analysis and nonattainment by `W¹,¹` functions -/

section EqualityAnalysisAndNonattainment

/-- Strict superadditivity of `t ↦ t ^ p` (`p > 1`) on positive reals: if `1 < p`, `0 < A`, and
`0 < B`, then `A ^ p + B ^ p < (A + B) ^ p`. -/
theorem rpow_add_rpow_lt_add_rpow_of_pos {p A B : ℝ} (hp : 1 < p) (hA : 0 < A) (hB : 0 < B) :
    A ^ p + B ^ p < (A + B) ^ p := by
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hAB : 0 < A + B := add_pos hA hB
  have hA_pow : A ^ p < A * (A + B) ^ (p - 1) := by
    have h1 : A ^ (p - 1) < (A + B) ^ (p - 1) :=
      Real.rpow_lt_rpow hA.le (lt_add_of_pos_right A hB) hp1
    calc A ^ p = A ^ (1 + (p - 1)) := by ring_nf
      _ = A ^ (1 : ℝ) * A ^ (p - 1) := Real.rpow_add hA 1 (p - 1)
      _ = A * A ^ (p - 1) := by rw [Real.rpow_one]
      _ < A * (A + B) ^ (p - 1) := mul_lt_mul_of_pos_left h1 hA
  have hB_pow : B ^ p < B * (A + B) ^ (p - 1) := by
    have h2 : B ^ (p - 1) < (A + B) ^ (p - 1) :=
      Real.rpow_lt_rpow hB.le (lt_add_of_pos_left B hA) hp1
    calc B ^ p = B ^ (1 + (p - 1)) := by ring_nf
      _ = B ^ (1 : ℝ) * B ^ (p - 1) := Real.rpow_add hB 1 (p - 1)
      _ = B * B ^ (p - 1) := by rw [Real.rpow_one]
      _ < B * (A + B) ^ (p - 1) := mul_lt_mul_of_pos_left h2 hB
  calc A ^ p + B ^ p
      < A * (A + B) ^ (p - 1) + B * (A + B) ^ (p - 1) := add_lt_add hA_pow hB_pow
    _ = (A + B) ^ (1 : ℝ) * (A + B) ^ (p - 1) := by rw [Real.rpow_one, add_mul]
    _ = (A + B) ^ (1 + (p - 1)) := (Real.rpow_add hAB 1 (p - 1)).symm
    _ = (A + B) ^ p := by ring_nf

/-- For `1 < p`, `0 < A`, and `0 < B`, `(A ^ p + B ^ p) ^ (1 / p) < A + B`. -/
theorem rpow_add_rpow_inv_lt_add_of_pos {p A B : ℝ} (hp : 1 < p) (hA : 0 < A) (hB : 0 < B) :
    (A ^ p + B ^ p) ^ (1 / p) < A + B := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hlt := Real.rpow_lt_rpow
    (add_nonneg (Real.rpow_nonneg hA.le p) (Real.rpow_nonneg hB.le p))
    (rpow_add_rpow_lt_add_rpow_of_pos hp hA hB) (inv_pos.mpr hp0)
  rw [one_div]
  rwa [Real.rpow_rpow_inv (add_pos hA hB).le hp0.ne'] at hlt

/-- For `1 < p`, `0 ≤ A`, and `0 ≤ B`, `(A ^ p + B ^ p) ^ (1 / p) ≤ A + B`. -/
theorem rpow_add_rpow_inv_le_add {p A B : ℝ} (hp : 1 < p) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A ^ p + B ^ p) ^ (1 / p) ≤ A + B := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  rcases hA.eq_or_lt with rfl | hA_pos
  · simp [one_div, Real.zero_rpow hp0.ne', Real.rpow_rpow_inv hB hp0.ne']
  · rcases hB.eq_or_lt with rfl | hB_pos
    · simp [one_div, Real.zero_rpow hp0.ne', Real.rpow_rpow_inv hA_pos.le hp0.ne']
    · exact (rpow_add_rpow_inv_lt_add_of_pos hp hA_pos hB_pos).le

/-- **Strict concavity equality characterization for `ℓ^p` vs `ℓ^1` (`p > 1`)**: for `1 < p`,
`0 ≤ A`, and `0 ≤ B`, `(A ^ p + B ^ p) ^ (1 / p) = A + B` if and only if `A = 0 ∨ B = 0`. -/
theorem rpow_add_rpow_inv_eq_add_iff {p A B : ℝ} (hp : 1 < p) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A ^ p + B ^ p) ^ (1 / p) = A + B ↔ A = 0 ∨ B = 0 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  refine ⟨fun heq ↦ ?_, ?_⟩
  · by_contra! hpos
    exact (rpow_add_rpow_inv_lt_add_of_pos hp (hA.lt_of_ne' hpos.1) (hB.lt_of_ne' hpos.2)).ne heq
  · rintro (rfl | rfl)
    · simp [one_div, Real.zero_rpow hp0.ne', Real.rpow_rpow_inv hB hp0.ne']
    · simp [one_div, Real.zero_rpow hp0.ne', Real.rpow_rpow_inv hA hp0.ne']

/-- **Absence of sign cancellation in sharp BV Sobolev equality**: suppose `1 < p`, `0 < C`,
`0 ≤ norm_pos`, `0 ≤ norm_neg`, `0 ≤ var_pos`, `0 ≤ var_neg`, the Sobolev bounds
`norm_pos ≤ C * var_pos` and `norm_neg ≤ C * var_neg` hold for the positive and negative parts,
`norm_u = (norm_pos ^ p + norm_neg ^ p) ^ (1 / p)`, and `var_pos + var_neg ≤ var_u`.
If equality `norm_u = C * var_u` holds, then `norm_pos = 0 ∨ norm_neg = 0` (so at least one of the
positive or negative parts vanishes). -/
theorem single_sign_of_sobolev_equality {p C norm_u norm_pos norm_neg var_u var_pos var_neg : ℝ}
    (hp : 1 < p) (hC : 0 < C) (hnp : 0 ≤ norm_pos) (hnn : 0 ≤ norm_neg)
    (hsob_pos : norm_pos ≤ C * var_pos) (hsob_neg : norm_neg ≤ C * var_neg)
    (hnorm_decomp : norm_u = (norm_pos ^ p + norm_neg ^ p) ^ (1 / p))
    (hvar_decomp : var_pos + var_neg ≤ var_u)
    (heq : norm_u = C * var_u) :
    norm_pos = 0 ∨ norm_neg = 0 := by
  refine (rpow_add_rpow_inv_eq_add_iff hp hnp hnn).mp (le_antisymm
    (rpow_add_rpow_inv_le_add hp hnp hnn) ?_)
  calc norm_pos + norm_neg
      ≤ C * var_pos + C * var_neg := add_le_add hsob_pos hsob_neg
    _ = C * (var_pos + var_neg) := (mul_add C var_pos var_neg).symm
    _ ≤ C * var_u := mul_le_mul_of_nonneg_left hvar_decomp hC.le
    _ = (norm_pos ^ p + norm_neg ^ p) ^ (1 / p) := heq.symm.trans hnorm_decomp

/-- **Superlevel constancy implies vanishing of intermediate values**: if `Measurable w`,
`0 < c`, `μ (superlevelSet w 0) ≠ ⊤`, and `μ {x | c ≤ w x} = μ (superlevelSet w 0)`, then
`μ {x | 0 < w x ∧ w x < c} = 0`. -/
theorem measure_between_eq_zero_of_superlevel_const {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ} {c : ℝ} (hw : Measurable w) (hc : 0 < c)
    (hfin : μ (superlevelSet w 0) ≠ ⊤) (hconst : μ {x | c ≤ w x} = μ (superlevelSet w 0)) :
    μ {x | 0 < w x ∧ w x < c} = 0 := by
  have hsub : {x | c ≤ w x} ⊆ superlevelSet w 0 := fun x hx ↦ hc.trans_le hx
  have hm : MeasurableSet {x | c ≤ w x} := hw measurableSet_Ici
  have hdiff : {x | 0 < w x ∧ w x < c} = superlevelSet w 0 \ {x | c ≤ w x} := by
    ext x; simp [superlevelSet]
  rw [hdiff, measure_sdiff hsub hm.nullMeasurableSet (hconst.symm ▸ hfin), hconst, tsub_self]

/-- **Step-function characterization from superlevel constancy**: if `Measurable w`, `0 ≤ w x` a.e.,
`0 < c`, `μ (superlevelSet w 0) ≠ ⊤`, `μ {x | c ≤ w x} = μ (superlevelSet w 0)`, and
`μ (superlevelSet w c) = 0`, then `w =ᵐ[μ] (superlevelSet w 0).indicator (fun _ ↦ c)`. -/
theorem ae_eq_indicator_of_superlevel_step {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ} {c : ℝ} (hw : Measurable w) (hc : 0 < c)
    (hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x) (hfin : μ (superlevelSet w 0) ≠ ⊤)
    (hconst : μ {x | c ≤ w x} = μ (superlevelSet w 0))
    (htop : μ (superlevelSet w c) = 0) :
    w =ᵐ[μ] (superlevelSet w 0).indicator (fun _ ↦ c) := by
  have hmid : ∀ᵐ x ∂μ, ¬(0 < w x ∧ w x < c) := by
    rw [ae_iff]
    simpa only [Classical.not_not] using
      measure_between_eq_zero_of_superlevel_const hw hc hfin hconst
  have hgt : ∀ᵐ x ∂μ, ¬(c < w x) := by
    rw [ae_iff]
    simpa only [Classical.not_not, superlevelSet] using htop
  filter_upwards [hw_nonneg, hmid, hgt] with x hx0 hxmid hxgt
  by_cases hxpos : x ∈ superlevelSet w 0
  · rw [indicator_of_mem hxpos]
    linarith [not_and.mp hxmid hxpos]
  · rw [indicator_of_notMem hxpos]
    rw [mem_superlevelSet_iff, not_lt] at hxpos
    linarith

/-- **Mutual exclusion between absolutely continuous and purely singular measures**: if a measure
`ν₁` is absolutely continuous with respect to `μ` (`ν₁ ≪ μ`), `ν₂` is mutually singular with
respect to `μ` (`ν₂ ⟂ₘ μ`), and `ν₁ = ν₂`, then `ν₁ = 0`. -/
theorem eq_zero_of_ac_and_mutuallySingular_eq {α : Type*} [MeasurableSpace α]
    {μ ν₁ ν₂ : Measure α} (hac : ν₁ ≪ μ) (hperp : ν₂ ⟂ₘ μ) (heq : ν₁ = ν₂) :
    ν₁ = 0 := by
  subst heq
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hac hperp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Nonattainment of purely singular Caccioppoli/ball extremizers by `W¹,¹` functions**: if
`HasWeakGradientOn u g U` holds on a measurable set `U` and the variation measure
`gradientVariationMeasure g U` coincides with a purely singular measure `ν_sing`
(`ν_sing ⟂ₘ volume`, such as `|c| • |D 1_{B(a, r)}|` supported on `Metric.sphere a r`), then
`gradientVariationMeasure g U = 0`, `ν_sing = 0`, and `g =ᵐ[volume.restrict U] 0`. -/
theorem HasWeakGradientOn.eq_zero_of_gradientVariationMeasure_eq_mutuallySingular
    {u : E → ℝ} {g : E → E} {U : Set E} {ν_sing : Measure E}
    (h : HasWeakGradientOn u g U) (hU : MeasurableSet U) (hperp : ν_sing ⟂ₘ volume)
    (heq : gradientVariationMeasure g U = ν_sing) :
    gradientVariationMeasure g U = 0 ∧ ν_sing = 0 ∧ g =ᵐ[volume.restrict U] 0 := by
  have hzero : gradientVariationMeasure g U = 0 :=
    eq_zero_of_ac_and_mutuallySingular_eq (absolutelyContinuous_gradientVariationMeasure g U)
      hperp heq
  have hν0 : ν_sing = 0 := heq.symm.trans hzero
  have hlint : ∫⁻ x in U, ‖g x‖ₑ ∂volume = 0 := by
    rw [← gradientVariationMeasure_apply_self g hU, hzero, Measure.coe_zero, Pi.zero_apply]
  have hae : ∀ᵐ x ∂(volume.restrict U), ‖g x‖ₑ = 0 :=
    (lintegral_eq_zero_iff' h.integrableOn.aestronglyMeasurable.enorm).mp hlint
  refine ⟨hzero, hν0, ?_⟩
  filter_upwards [hae] with x hx
  exact enorm_eq_zero.mp hx

/-- **Vanishing of scalar multiple `c = 0` when a `W¹,¹` function matches `c • 1_A` with positive
singular perimeter**: if `HasWeakGradientOn u g U`, `P_A ≠ 0`, and the total variation
`ν_sing U` equals `ENNReal.ofReal |c| * P_A` while `gradientVariationMeasure g U = ν_sing` and
`ν_sing ⟂ₘ volume`, then `c = 0`. -/
theorem HasWeakGradientOn.eq_zero_const_of_singular_perimeter_eq
    {u : E → ℝ} {g : E → E} {U : Set E} {ν_sing : Measure E} {c : ℝ} {P_A : ℝ≥0∞}
    (h : HasWeakGradientOn u g U) (hU : MeasurableSet U) (hperp : ν_sing ⟂ₘ volume)
    (heq : gradientVariationMeasure g U = ν_sing) (hP : P_A ≠ 0)
    (hmass : ν_sing U = ENNReal.ofReal |c| * P_A) :
    c = 0 := by
  rcases h.eq_zero_of_gradientVariationMeasure_eq_mutuallySingular hU hperp heq with ⟨_, hν0, _⟩
  rw [hν0, Measure.coe_zero, Pi.zero_apply, eq_comm, mul_eq_zero] at hmass
  rcases hmass with hc0 | hP0
  · exact abs_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hc0) (abs_nonneg c))
  · exact False.elim (hP hP0)

end EqualityAnalysisAndNonattainment

/-! ### Section 3: Explicit radial ball near-extremizers and asymptotic sharp Sobolev quotient -/

section RadialBallNearExtremizers

/-- The explicit 1D piecewise-linear radial cutoff profile
`radialCutoffProfile r ε t = max 0 (min 1 ((r + ε - t) / ε))`, equal to `1` for `t ≤ r`, affine
decreasing with slope `-ε⁻¹` on `[r, r + ε]`, and `0` for `t ≥ r + ε`. -/
def radialCutoffProfile (r ε t : ℝ) : ℝ :=
  max 0 (min 1 ((r + ε - t) / ε))

/-- Nonnegativity `0 ≤ radialCutoffProfile r ε t`. -/
theorem radialCutoffProfile_nonneg (r ε t : ℝ) : 0 ≤ radialCutoffProfile r ε t :=
  le_max_left 0 _

/-- Upper bound `radialCutoffProfile r ε t ≤ 1`. -/
theorem radialCutoffProfile_le_one (r ε t : ℝ) : radialCutoffProfile r ε t ≤ 1 :=
  max_le zero_le_one (min_le_left 1 _)

/-- On `(-∞, r]`, `radialCutoffProfile r ε t = 1` for `0 < ε`. -/
theorem radialCutoffProfile_eq_one_of_le {r ε t : ℝ} (hε : 0 < ε) (ht : t ≤ r) :
    radialCutoffProfile r ε t = 1 := by
  have h1 : 1 ≤ (r + ε - t) / ε := by
    rw [le_div_iff₀ hε]; linarith
  simp [radialCutoffProfile, min_eq_left h1]

/-- On `[r + ε, ∞)`, `radialCutoffProfile r ε t = 0` for `0 < ε`. -/
theorem radialCutoffProfile_eq_zero_of_le {r ε t : ℝ} (hε : 0 < ε) (ht : r + ε ≤ t) :
    radialCutoffProfile r ε t = 0 := by
  have h0 : (r + ε - t) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [radialCutoffProfile, min_eq_right (h0.trans zero_le_one), max_eq_left h0]

/-- On `[r, r + ε]`, `radialCutoffProfile r ε t = (r + ε - t) / ε` for `0 < ε`. -/
theorem radialCutoffProfile_of_mem_Icc {r ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc r (r + ε)) :
    radialCutoffProfile r ε t = (r + ε - t) / ε := by
  have h0 : 0 ≤ (r + ε - t) / ε := div_nonneg (by linarith [ht.2]) hε.le
  have h1 : (r + ε - t) / ε ≤ 1 := (div_le_one hε).mpr (by linarith [ht.1])
  rw [radialCutoffProfile, min_eq_right h1, max_eq_right h0]

/-- `t ↦ radialCutoffProfile r ε t` is antitone for `0 < ε`. -/
theorem radialCutoffProfile_antitone {r ε : ℝ} (hε : 0 < ε) :
    Antitone (radialCutoffProfile r ε) := by
  intro t₁ t₂ ht
  unfold radialCutoffProfile
  gcongr

/-- Pointwise Lipschitz bound for `radialCutoffProfile r ε`:
`|radialCutoffProfile r ε t₁ - radialCutoffProfile r ε t₂| ≤ ε⁻¹ * |t₁ - t₂|` for `0 < ε`. -/
theorem abs_radialCutoffProfile_sub_le {r ε t₁ t₂ : ℝ} (hε : 0 < ε) :
    |radialCutoffProfile r ε t₁ - radialCutoffProfile r ε t₂| ≤ ε⁻¹ * |t₁ - t₂| := by
  have hmax : ∀ a b : ℝ, |max 0 a - max 0 b| ≤ |a - b| := fun a b ↦ by
    cases le_total 0 a <;> cases le_total 0 b <;>
      simp only [max_eq_left, max_eq_right, *] <;>
      rw [abs_le] <;> constructor <;> linarith [le_abs_self (a - b), neg_abs_le (a - b)]
  have hmin : ∀ a b : ℝ, |min 1 a - min 1 b| ≤ |a - b| := fun a b ↦ by
    cases le_total 1 a <;> cases le_total 1 b <;>
      simp only [min_eq_left, min_eq_right, *] <;>
      rw [abs_le] <;> constructor <;> linarith [le_abs_self (a - b), neg_abs_le (a - b)]
  calc |radialCutoffProfile r ε t₁ - radialCutoffProfile r ε t₂|
      ≤ |min 1 ((r + ε - t₁) / ε) - min 1 ((r + ε - t₂) / ε)| := hmax _ _
    _ ≤ |(r + ε - t₁) / ε - (r + ε - t₂) / ε| := hmin _ _
    _ = |-(t₁ - t₂) / ε| := by ring_nf
    _ = ε⁻¹ * |t₁ - t₂| := by
        rw [abs_div, abs_neg, abs_of_pos hε, div_eq_inv_mul]

/-- On the open transition interval `Ioo r (r + ε)`, `radialCutoffProfile r ε` has derivative
`-ε⁻¹`. -/
theorem hasDerivAt_radialCutoffProfile_of_mem_Ioo {r ε t : ℝ} (hε : 0 < ε)
    (ht : t ∈ Ioo r (r + ε)) :
    HasDerivAt (radialCutoffProfile r ε) (-ε⁻¹) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds ht.1 ht.2), self_mem_nhdsWithin] with s hs hne
  have hst : s - t ≠ 0 := sub_ne_zero.mpr hne
  rw [slope_def_field, radialCutoffProfile_of_mem_Icc hε ⟨hs.1.le, hs.2.le⟩,
    radialCutoffProfile_of_mem_Icc hε ⟨ht.1.le, ht.2.le⟩]
  field_simp [hε.ne', hst]
  ring

variable {E : Type*} [PseudoMetricSpace E]

/-- The **radial ball near-extremizer** `radialBallNearExtremizer a r ε x`, equal to `1` on
`Metric.closedBall a r`, affine decreasing in `dist x a` on the spherical shell
`Metric.ball a (r + ε) \ Metric.closedBall a r`, and `0` outside `Metric.ball a (r + ε)`. -/
def radialBallNearExtremizer (a : E) (r ε : ℝ) (x : E) : ℝ :=
  radialCutoffProfile r ε (dist x a)

/-- Nonnegativity `0 ≤ radialBallNearExtremizer a r ε x`. -/
theorem radialBallNearExtremizer_nonneg (a : E) (r ε : ℝ) (x : E) :
    0 ≤ radialBallNearExtremizer a r ε x :=
  radialCutoffProfile_nonneg r ε (dist x a)

/-- Upper bound `radialBallNearExtremizer a r ε x ≤ 1`. -/
theorem radialBallNearExtremizer_le_one (a : E) (r ε : ℝ) (x : E) :
    radialBallNearExtremizer a r ε x ≤ 1 :=
  radialCutoffProfile_le_one r ε (dist x a)

/-- On `Metric.closedBall a r`, `radialBallNearExtremizer a r ε x = 1` for `0 < ε`. -/
theorem radialBallNearExtremizer_eq_one_of_mem_closedBall {a : E} {r ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : x ∈ Metric.closedBall a r) :
    radialBallNearExtremizer a r ε x = 1 :=
  radialCutoffProfile_eq_one_of_le hε (Metric.mem_closedBall.mp hx)

/-- Outside `Metric.ball a (r + ε)`, `radialBallNearExtremizer a r ε x = 0` for `0 < ε`. -/
theorem radialBallNearExtremizer_eq_zero_of_notMem_ball {a : E} {r ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : x ∉ Metric.ball a (r + ε)) :
    radialBallNearExtremizer a r ε x = 0 :=
  radialCutoffProfile_eq_zero_of_le hε (not_lt.mp (mt Metric.mem_ball.mpr hx))

/-- Lower indicator bound `(Metric.closedBall a r).indicator 1 x ≤ radialBallNearExtremizer a r ε x`
for `0 < ε`. -/
theorem indicator_closedBall_le_radialBallNearExtremizer {a : E} {r ε : ℝ} (hε : 0 < ε) (x : E) :
    (Metric.closedBall a r).indicator (fun _ ↦ (1 : ℝ)) x ≤ radialBallNearExtremizer a r ε x := by
  by_cases hx : x ∈ Metric.closedBall a r
  · rw [indicator_of_mem hx, radialBallNearExtremizer_eq_one_of_mem_closedBall hε hx]
  · rw [indicator_of_notMem hx]; exact radialBallNearExtremizer_nonneg a r ε x

/-- Upper indicator bound `radialBallNearExtremizer a r ε x ≤ (Metric.ball a (r + ε)).indicator 1 x`
for `0 < ε`. -/
theorem radialBallNearExtremizer_le_indicator_ball {a : E} {r ε : ℝ} (hε : 0 < ε) (x : E) :
    radialBallNearExtremizer a r ε x ≤ (Metric.ball a (r + ε)).indicator (fun _ ↦ (1 : ℝ)) x := by
  by_cases hx : x ∈ Metric.ball a (r + ε)
  · rw [indicator_of_mem hx]; exact radialBallNearExtremizer_le_one a r ε x
  · rw [indicator_of_notMem hx, radialBallNearExtremizer_eq_zero_of_notMem_ball hε hx]

/-- Pointwise Lipschitz bound for `radialBallNearExtremizer a r ε`:
`|radialBallNearExtremizer a r ε x - radialBallNearExtremizer a r ε y| ≤ ε⁻¹ * dist x y`. -/
theorem abs_radialBallNearExtremizer_sub_le {a : E} {r ε : ℝ} (hε : 0 < ε) (x y : E) :
    |radialBallNearExtremizer a r ε x - radialBallNearExtremizer a r ε y| ≤ ε⁻¹ * dist x y :=
  (abs_radialCutoffProfile_sub_le hε).trans
    (mul_le_mul_of_nonneg_left (abs_dist_sub_le x y a) (inv_nonneg.mpr hε.le))

/-- `radialBallNearExtremizer a r ε` is `LipschitzWith (ENNReal.ofReal ε⁻¹).toNNReal` for
`0 < ε`. -/
theorem lipschitzWith_radialBallNearExtremizer {a : E} {r ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (ENNReal.ofReal ε⁻¹).toNNReal (radialBallNearExtremizer a r ε) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  change dist _ _ ≤ (ENNReal.ofReal ε⁻¹).toReal * dist x y
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hε.le), Real.dist_eq]
  exact abs_radialBallNearExtremizer_sub_le hε x y

/-- Pointwise convergence `radialBallNearExtremizer a r ε x → (Metric.ball a r).indicator 1 x` as
`ε → 0⁺` for every `x ∉ Metric.sphere a r`. -/
theorem tendsto_radialBallNearExtremizer_nhdsWithin_Ioi {a : E} {r : ℝ} {x : E}
    (hx : x ∉ Metric.sphere a r) :
    Tendsto (fun ε ↦ radialBallNearExtremizer a r ε x) (𝓝[>] 0)
      (𝓝 ((Metric.ball a r).indicator (fun _ ↦ (1 : ℝ)) x)) := by
  rcases lt_trichotomy (dist x a) r with hlt | heq | hgt
  · have hmem : x ∈ Metric.ball a r := hlt
    have hclosed : x ∈ Metric.closedBall a r := hlt.le
    rw [indicator_of_mem hmem]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (radialBallNearExtremizer_eq_one_of_mem_closedBall hε hclosed).symm
  · exact False.elim (hx heq)
  · have hnot : x ∉ Metric.ball a r := not_lt.mpr hgt.le
    rw [indicator_of_notMem hnot]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hgt)] with ε hε
    refine (radialBallNearExtremizer_eq_zero_of_notMem_ball hε.1 ?_).symm
    rw [Metric.mem_ball, not_lt]
    linarith [hε.2]

/-! ### Asymptotic sharp Sobolev quotient convergence as `ε ↓ 0` -/

/-- Right-hand limit of the normalized spherical-shell volume difference:
`ε⁻¹ * (ω_n * ((r + ε) ^ n - r ^ n)) → n * ω_n * r ^ (n - 1)` as `ε → 0⁺`. -/
theorem tendsto_shell_gradient_energy (ω_n r : ℝ) (n : ℕ) :
    Tendsto (fun ε : ℝ ↦ ε⁻¹ * (ω_n * ((r + ε) ^ n - r ^ n))) (𝓝[>] 0)
      (𝓝 ((n : ℝ) * ω_n * r ^ (n - 1))) := by
  have hd : Tendsto (fun ε : ℝ ↦ ε⁻¹ * ((r + ε) ^ n - r ^ n)) (𝓝[>] 0)
      (𝓝 ((n : ℝ) * r ^ (n - 1))) := by
    simpa [smul_eq_mul] using (hasDerivAt_pow n r).tendsto_slope_zero_right
  have hmul := hd.const_mul ω_n
  have heq_lim : ω_n * ((n : ℝ) * r ^ (n - 1)) = (n : ℝ) * ω_n * r ^ (n - 1) := by ring
  rw [heq_lim] at hmul
  refine hmul.congr fun ε ↦ by ring

/-- Continuity limit of the upper ball `L^{n/(n-1)}` norm bound as `ε → 0⁺`: for `0 < ω_n` and
`0 < r`, `(ω_n * (r + ε) ^ n) ^ (((n : ℝ) - 1) / n) → (ω_n * r ^ n) ^ (((n : ℝ) - 1) / n)`. -/
theorem tendsto_ball_lpNorm_upper {ω_n r : ℝ} (n : ℕ) (hω : 0 < ω_n) (hr : 0 < r) :
    Tendsto (fun ε : ℝ ↦ (ω_n * (r + ε) ^ n) ^ (((n : ℝ) - 1) / (n : ℝ))) (𝓝[>] 0)
      (𝓝 ((ω_n * r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)))) := by
  have hcont : ContinuousAt (fun ε : ℝ ↦ (ω_n * (r + ε) ^ n) ^ (((n : ℝ) - 1) / (n : ℝ))) 0 := by
    refine ContinuousAt.rpow ?_ continuousAt_const (Or.inl ?_)
    · exact continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow n)
    · positivity
  simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- Exact algebraic simplification of the ball Sobolev ratio: for `0 < ω_n`, `0 < r`, and `1 ≤ n`,
`((n : ℝ) * ω_n * r ^ (n - 1)) / ((ω_n * r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ))) =
  (n : ℝ) * ω_n ^ (1 / (n : ℝ))`. -/
theorem ball_sobolev_ratio_eq_sharp_constant {ω_n r : ℝ} {n : ℕ} (hω : 0 < ω_n) (hr : 0 < r)
    (hn : 1 ≤ n) :
    ((n : ℝ) * ω_n * r ^ (n - 1)) / ((ω_n * r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ))) =
      (n : ℝ) * ω_n ^ (1 / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.one_pos.trans_le hn)
  have hr_pow : (r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) = r ^ (n - 1) := by
    rw [← Real.rpow_natCast r n, ← Real.rpow_mul hr.le, mul_div_cancel₀ _ hn_pos.ne',
      ← Nat.cast_one, ← Nat.cast_sub hn, Real.rpow_natCast]
  have hsub : (1 : ℝ) - ((n : ℝ) - 1) / (n : ℝ) = 1 / (n : ℝ) := by
    field_simp
    ring
  have hω_pow : ω_n / ω_n ^ (((n : ℝ) - 1) / (n : ℝ)) = ω_n ^ (1 / (n : ℝ)) := by
    rw [← hsub, Real.rpow_sub hω, Real.rpow_one]
  rw [Real.mul_rpow hω.le (pow_nonneg hr.le n), hr_pow,
    mul_div_mul_right ((n : ℝ) * ω_n) (ω_n ^ (((n : ℝ) - 1) / (n : ℝ)))
      (pow_ne_zero (n - 1) hr.ne'),
    mul_div_assoc, hω_pow]

/-- **Sharp asymptotic Sobolev quotient convergence for radial ball near-extremizers**: if for
`ε > 0`, `G ε` is the gradient `L¹` energy converging to `n * ω_n * r ^ (n - 1)` (such as
`ε⁻¹ * ω_n * ((r + ε) ^ n - r ^ n)`) and `N ε` is the `L^{n/(n-1)}` norm sandwiched between
`(ω_n * r ^ n) ^ ((n - 1) / n)` and `(ω_n * (r + ε) ^ n) ^ ((n - 1) / n)`, then the Sobolev
quotient `G ε / N ε` converges as `ε → 0⁺` to the **sharp BV Sobolev constant
`n * ω_n ^ (1 / n)`**. -/
theorem tendsto_sobolev_quotient_sharp_constant {ω_n r : ℝ} {n : ℕ} (hω : 0 < ω_n) (hr : 0 < r)
    (hn : 1 ≤ n) {G N : ℝ → ℝ}
    (hG_nonneg : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ G ε)
    (hG : Tendsto G (𝓝[>] 0) (𝓝 ((n : ℝ) * ω_n * r ^ (n - 1))))
    (hN_low : ∀ᶠ ε in 𝓝[>] 0, (ω_n * r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ N ε)
    (hN_up : ∀ᶠ ε in 𝓝[>] 0, N ε ≤ (ω_n * (r + ε) ^ n) ^ (((n : ℝ) - 1) / (n : ℝ))) :
    Tendsto (fun ε ↦ G ε / N ε) (𝓝[>] 0) (𝓝 ((n : ℝ) * ω_n ^ (1 / (n : ℝ)))) := by
  set L := (ω_n * r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ))
  have hL_pos : 0 < L := Real.rpow_pos_of_pos (mul_pos hω (pow_pos hr n)) _
  have h_lim_low : Tendsto (fun ε ↦ G ε / (ω_n * (r + ε) ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)))
      (𝓝[>] 0) (𝓝 ((n : ℝ) * ω_n ^ (1 / (n : ℝ)))) := by
    rw [← ball_sobolev_ratio_eq_sharp_constant hω hr hn]
    exact hG.div (tendsto_ball_lpNorm_upper n hω hr) hL_pos.ne'
  have h_lim_up : Tendsto (fun ε ↦ G ε / L) (𝓝[>] 0)
      (𝓝 ((n : ℝ) * ω_n ^ (1 / (n : ℝ)))) := by
    rw [← ball_sobolev_ratio_eq_sharp_constant hω hr hn]
    exact hG.div_const L
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lim_low h_lim_up ?_ ?_
  · filter_upwards [hG_nonneg, hN_low, hN_up] with ε hG0 hNl hNu
    exact div_le_div_of_nonneg_left hG0 (hL_pos.trans_le hNl) hNu
  · filter_upwards [hG_nonneg, hN_low] with ε hG0 hNl
    exact div_le_div_of_nonneg_left hG0 hL_pos hNl

end RadialBallNearExtremizers

end TauCeti
