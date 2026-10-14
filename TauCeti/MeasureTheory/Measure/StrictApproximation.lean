/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.PerimeterTransport
public import TauCeti.MeasureTheory.Measure.RadonVariationMeasure
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.RadonVariationMeasure

/-!
# Partition of Unity, Strict BV Convergence, Smooth Approximation, and BV Ball Closedness

This file develops the partition-of-unity cutoff calculus, finite convex-combination and discrete
translation-convolution contraction of `distributionalVariation`, strict convergence in `BV(U)`
(`IsStrictBVTendstoOn`: `L¹(U)` convergence coupled with convergence of total variation
`|Du_n|(U) → |Du|(U)`), smooth strict approximation (`HasSmoothStrictApproximationOn`), strict
perimeter convergence of sets (`IsStrictPerimeterTendstoOn`), weak-star convergence of
distributional derivatives `Du_n ⇀ Du`, and `L¹(U)`-closedness of `BV(U)` norm balls:

1. **Partition-of-unity cutoff calculus and convex/convolution variation contraction**:
   `TauCeti.distributionalVariation_finsetSum_le`,
   `TauCeti.distributionalVariation_sum_mul_le`,
   `TauCeti.distributionalVariation_convex_sum_le`,
   `TauCeti.distributionalVariation_top_convex_sum_translate_le`,
   `TauCeti.IsPartitionOfUnityOn`, `TauCeti.IsPartitionOfUnityOn.sum_mul_eq`,
   `TauCeti.IsPartitionOfUnityOn.sum_product_rule_eq`,
   `TauCeti.HasWeakGradientOn.finsetSum`, and
   `TauCeti.IsPartitionOfUnityOn.hasWeakGradientOn_of_parts`.
2. **Strict convergence in `BV` (`IsStrictBVTendstoOn`) and set perimeter approximation**:
   `TauCeti.IsStrictBVTendstoOn`, `TauCeti.HasSmoothStrictApproximationOn`,
   `TauCeti.IsStrictPerimeterTendstoOn`, `TauCeti.isStrictBVTendstoOn_const`,
   `TauCeti.hasSmoothStrictApproximationOn_of_contDiff`,
   `TauCeti.IsStrictBVTendstoOn.tendsto_eLpNorm`,
   `TauCeti.IsStrictBVTendstoOn.tendsto_bvNorm`,
   `TauCeti.tendsto_integral_mul_divergence_of_tendsto_eLpNorm`,
   `TauCeti.IsStrictBVTendstoOn.tendsto_integral_mul_divergence`,
   `TauCeti.IsStrictPerimeterTendstoOn.compl`,
   `TauCeti.IsStrictPerimeterTendstoOn.tendsto_volume_inter`, and
   `TauCeti.isStrictPerimeterTendstoOn_iff_isStrictBVTendstoOn_indicator`.
3. **Weak-star limit of derivative measures and `L¹`-closedness of `BV` balls**:
   `TauCeti.integral_mul_divergence_eq_neg_of_tendsto_derivativeMeasure`,
   `TauCeti.hasDerivativeMeasureOn_of_tendsto`,
   `TauCeti.distributionalVariation_le_liminf_of_tendsto_eLpNorm`,
   `TauCeti.distributionalVariation_le_of_tendsto_eLpNorm`,
   `TauCeti.eLpNorm_add_distributionalVariation_le_of_tendsto_eLpNorm`,
   `TauCeti.relativePerimeter_le_liminf_of_tendsto_symmDiff`, and
   `TauCeti.relativePerimeter_le_of_tendsto_symmDiff`.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Set TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Topology Distributions symmDiff

namespace TauCeti

/-- Pointwise extended norm of the difference of two characteristic functions:
`‖S.indicator 1 x - T.indicator 1 x‖ₑ = (S ∆ T).indicator 1 x`. -/
theorem enorm_indicator_sub_indicator_one {α : Type*} (S T : Set α) (x : α) :
    ‖S.indicator (fun _ ↦ (1 : ℝ)) x - T.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ =
      (S ∆ T).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp [symmDiff, hxS, hxT]
/-- If `eLpNorm (u_seq n - u) 1 μ → 0`, then `eLpNorm (u_seq n) 1 μ → eLpNorm u 1 μ`. -/
theorem tendsto_eLpNorm_of_tendsto_eLpNorm_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u_seq : ℕ → α → ℝ} {u : α → ℝ}
    (h : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (u_seq n) 1 μ) atTop (𝓝 (eLpNorm u 1 μ)) := by
  have h_low : ∀ n, eLpNorm u 1 μ - eLpNorm (u_seq n - u) 1 μ ≤ eLpNorm (u_seq n) 1 μ := by
    intro n
    rw [tsub_le_iff_right]
    have heq : u = u_seq n - (u_seq n - u) := by ext x; simp
    conv_lhs => rw [heq]
    exact eLpNorm_sub_le le_rfl
  have h_up : ∀ n, eLpNorm (u_seq n) 1 μ ≤ eLpNorm (u_seq n - u) 1 μ + eLpNorm u 1 μ := by
    intro n
    have heq : u_seq n = (u_seq n - u) + u := by ext x; simp
    conv_lhs => rw [heq]
    exact eLpNorm_add_le le_rfl
  have h_lim_low : Tendsto (fun n ↦ eLpNorm u 1 μ - eLpNorm (u_seq n - u) 1 μ) atTop
      (𝓝 (eLpNorm u 1 μ)) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inr ENNReal.zero_ne_top)
  have h_lim_up : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 μ + eLpNorm u 1 μ) atTop
      (𝓝 (eLpNorm u 1 μ)) := by
    simpa using h.add tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_lim_low h_lim_up h_low h_up
/-- If `eLpNorm f 1 μ < ⊤`, then `f` is `μ`-integrable. -/
theorem integrable_of_eLpNorm_one_lt_top {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    {μ : Measure α} (h : eLpNorm f 1 μ < ⊤) : Integrable f μ := by
  have hmeas : AEStronglyMeasurable f μ := by
    by_contra hm; simp [eLpNorm, hm] at h
  exact ⟨hmeas, hasFiniteIntegral_iff_enorm.mpr
    (by simpa [eLpNorm_one_eq_lintegral_enorm hmeas] using h)⟩

/-! ### Section 1: Partition-of-unity cutoff calculus and convex/convolution contraction -/

section PartitionOfUnityAndContraction

/-- A finite family of scalar cutoff functions `η : ι → E → ℝ` indexed by `s : Finset ι` forms a
**partition of unity on `U : Set E`** (`IsPartitionOfUnityOn s η U`) if `0 ≤ η i x` for all
`i ∈ s` and `x ∈ U`, and `∑ i ∈ s, η i x = 1` for all `x ∈ U`. -/
def IsPartitionOfUnityOn {E ι : Type*} (s : Finset ι) (η : ι → E → ℝ) (U : Set E) : Prop :=
  (∀ i ∈ s, ∀ x ∈ U, 0 ≤ η i x) ∧ ∀ x ∈ U, ∑ i ∈ s, η i x = 1

namespace IsPartitionOfUnityOn

variable {E ι : Type*} {s : Finset ι} {η : ι → E → ℝ} {U V : Set E}

/-- Nonnegativity `0 ≤ η i x` of each partition-of-unity weight on `U`. -/
theorem nonneg (h : IsPartitionOfUnityOn s η U) {i : ι} (hi : i ∈ s) {x : E} (hx : x ∈ U) :
    0 ≤ η i x := h.1 i hi x hx
/-- Normalization `∑ i ∈ s, η i x = 1` on `U`. -/
theorem sum_eq_one (h : IsPartitionOfUnityOn s η U) {x : E} (hx : x ∈ U) :
    ∑ i ∈ s, η i x = 1 := h.2 x hx
/-- Each partition-of-unity weight satisfies `η i x ≤ 1` on `U`. -/
theorem le_one (h : IsPartitionOfUnityOn s η U) {i : ι} (hi : i ∈ s) {x : E} (hx : x ∈ U) :
    η i x ≤ 1 := by
  rw [← h.sum_eq_one hx]
  exact Finset.single_le_sum (fun j hj ↦ h.nonneg hj hx) hi
/-- Restriction of `IsPartitionOfUnityOn` to a subset `V ⊆ U`. -/
theorem mono (h : IsPartitionOfUnityOn s η U) (hVU : V ⊆ U) : IsPartitionOfUnityOn s η V :=
  ⟨fun i hi x hx ↦ h.1 i hi x (hVU hx), fun x hx ↦ h.2 x (hVU hx)⟩
/-- Pointwise scalar reconstruction `∑ i ∈ s, η i x * u x = u x` for `x ∈ U`. -/
theorem sum_mul_eq (h : IsPartitionOfUnityOn s η U) (u : E → ℝ) {x : E} (hx : x ∈ U) :
    ∑ i ∈ s, η i x * u x = u x := by
  rw [← Finset.sum_mul, h.sum_eq_one hx, one_mul]
/-- Pointwise vector reconstruction `∑ i ∈ s, η i x • v x = v x` for `x ∈ U`. -/
theorem sum_smul_eq {F : Type*} [AddCommMonoid F] [Module ℝ F] (h : IsPartitionOfUnityOn s η U)
    (v : E → F) {x : E} (hx : x ∈ U) :
    ∑ i ∈ s, η i x • v x = v x := by
  rw [← Finset.sum_smul, h.sum_eq_one hx, one_smul]
/-- **Partition-of-unity product-rule cancellation**: if `IsPartitionOfUnityOn s η U` and the
cutoff gradients satisfy `∑ i ∈ s, g_η i x = 0` for all `x ∈ U`, then for every scalar function
`u : E → ℝ`, vector field `g : E → F`, and `x ∈ U`,
`∑ i ∈ s, (η i x • g x + u x • g_η i x) = g x`. -/
theorem sum_product_rule_eq {F : Type*} [AddCommGroup F] [Module ℝ F]
    (h : IsPartitionOfUnityOn s η U) {g_η : ι → E → F}
    (hgrad : ∀ x ∈ U, ∑ i ∈ s, g_η i x = 0) (u : E → ℝ) (g : E → F) {x : E} (hx : x ∈ U) :
    ∑ i ∈ s, (η i x • g x + u x • g_η i x) = g x := by
  rw [Finset.sum_add_distrib, h.sum_smul_eq g hx, ← Finset.smul_sum, hgrad x hx, smul_zero,
    add_zero]

end IsPartitionOfUnityOn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section ConvexVariationContraction

variable {μ : Measure E} {Ω : Opens E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Finite sums of locally integrable functions on `Ω` are locally integrable on `Ω`. -/
theorem locallyIntegrableOn_finsetSum {ι : Type*} {s : Finset ι} {u : ι → E → ℝ}
    (hu : ∀ i ∈ s, LocallyIntegrableOn (u i) Ω μ) :
    LocallyIntegrableOn (fun x ↦ ∑ i ∈ s, u i x) Ω μ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun _ _ ↦ ⟨univ, univ_mem, integrableOn_zero⟩
  | @insert a s has ih =>
    have h_ins : (fun x ↦ ∑ i ∈ insert a s, u i x) = u a + fun x ↦ ∑ i ∈ s, u i x := by
      ext x; simp [Finset.sum_insert has]
    rw [h_ins]
    exact (hu a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi))
/-- **Finite subadditivity of variational total variation**: for any finite family `u : ι → E → ℝ`
of locally integrable functions on `Ω`,
`distributionalVariation μ Ω (fun x ↦ ∑ i ∈ s, u i x) ≤
  ∑ i ∈ s, distributionalVariation μ Ω (u i)`. -/
theorem distributionalVariation_finsetSum_le {ι : Type*} {s : Finset ι}
    {u : ι → E → ℝ} (hu : ∀ i ∈ s, LocallyIntegrableOn (u i) Ω μ) :
    distributionalVariation μ Ω (fun x ↦ ∑ i ∈ s, u i x) ≤
      ∑ i ∈ s, distributionalVariation μ Ω (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have ha : LocallyIntegrableOn (u a) Ω μ := hu a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, LocallyIntegrableOn (u i) Ω μ :=
      fun i hi ↦ hu i (Finset.mem_insert_of_mem hi)
    have h_ins : (fun x ↦ ∑ i ∈ insert a s, u i x) = u a + fun x ↦ ∑ i ∈ s, u i x := by
      ext x; simp [Finset.sum_insert has]
    rw [h_ins, Finset.sum_insert has]
    exact (distributionalVariation_add_le ha (locallyIntegrableOn_finsetSum hs)).trans
      (add_le_add_right (ih hs) _)
/-- **Nonnegative linear-combination contraction of `distributionalVariation`**: for nonnegative
weights `w : ι → ℝ` (`∀ i ∈ s, 0 ≤ w i`) and locally integrable functions `u i` on `Ω`,
`distributionalVariation μ Ω (fun x ↦ ∑ i ∈ s, w i * u i x) ≤
  ∑ i ∈ s, ENNReal.ofReal (w i) * distributionalVariation μ Ω (u i)`. -/
theorem distributionalVariation_sum_mul_le {ι : Type*} {s : Finset ι}
    {w : ι → ℝ} {u : ι → E → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hu : ∀ i ∈ s, LocallyIntegrableOn (u i) Ω μ) :
    distributionalVariation μ Ω (fun x ↦ ∑ i ∈ s, w i * u i x) ≤
      ∑ i ∈ s, ENNReal.ofReal (w i) * distributionalVariation μ Ω (u i) := by
  have hwu : ∀ i ∈ s, LocallyIntegrableOn (fun x ↦ w i * u i x) Ω μ :=
    fun i hi ↦ (hu i hi).smul (w i)
  refine (distributionalVariation_finsetSum_le hwu).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  have hsmul : (fun x ↦ w i * u i x) = w i • u i := rfl
  rw [hsmul, distributionalVariation_smul, abs_of_nonneg (hw i hi)]
/-- **Convex-combination contraction of `distributionalVariation`**: if `∀ i ∈ s, 0 ≤ w i`,
`∑ i ∈ s, w i = 1`, and `∀ i ∈ s, distributionalVariation μ Ω (u i) ≤ M`, then
`distributionalVariation μ Ω (fun x ↦ ∑ i ∈ s, w i * u i x) ≤ M`. -/
theorem distributionalVariation_convex_sum_le {ι : Type*} {s : Finset ι}
    {w : ι → ℝ} {u : ι → E → ℝ} {M : ℝ≥0∞} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1) (hu : ∀ i ∈ s, LocallyIntegrableOn (u i) Ω μ)
    (hM : ∀ i ∈ s, distributionalVariation μ Ω (u i) ≤ M) :
    distributionalVariation μ Ω (fun x ↦ ∑ i ∈ s, w i * u i x) ≤ M := by
  calc distributionalVariation μ Ω (fun x ↦ ∑ i ∈ s, w i * u i x)
      ≤ ∑ i ∈ s, ENNReal.ofReal (w i) * distributionalVariation μ Ω (u i) :=
        distributionalVariation_sum_mul_le hw hu
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (w i) * M :=
        Finset.sum_le_sum fun i hi ↦ mul_le_mul_right (hM i hi) _
    _ = (∑ i ∈ s, ENNReal.ofReal (w i)) * M := (Finset.sum_mul _ _ _).symm
    _ = ENNReal.ofReal (∑ i ∈ s, w i) * M := by rw [ENNReal.ofReal_sum_of_nonneg hw]
    _ = 1 * M := by rw [hsum, ENNReal.ofReal_one]
    _ = M := one_mul M
/-- **Discrete convolution / translation-average contraction of total variation**: for any
right-invariant measure `μ`, translations `y : ι → E`, and convex weights `w : ι → ℝ`
(`∀ i ∈ s, 0 ≤ w i`, `∑ i ∈ s, w i = 1`),
`distributionalVariation μ ⊤ (fun x ↦ ∑ i ∈ s, w i * u (x - y i)) ≤
  distributionalVariation μ ⊤ u`. -/
theorem distributionalVariation_top_convex_sum_translate_le [μ.IsAddRightInvariant]
    {ι : Type*} {s : Finset ι} {w : ι → ℝ} {y : ι → E} {u : E → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hu : ∀ i ∈ s, LocallyIntegrableOn (fun x ↦ u (x - y i)) ⊤ μ) :
    distributionalVariation μ ⊤ (fun x ↦ ∑ i ∈ s, w i * u (x - y i)) ≤
      distributionalVariation μ ⊤ u := by
  refine distributionalVariation_convex_sum_le hw hsum hu fun i _ ↦ ?_
  rw [distributionalVariation_top_comp_sub]

end ConvexVariationContraction

section WeakGradientPartitionGluing

/-- The zero function has zero weak gradient on any set `U`. -/
theorem HasWeakGradientOn.zero (U : Set E) : HasWeakGradientOn (0 : E → ℝ) (0 : E → E) U :=
  ⟨integrableOn_zero, fun _ _ ↦ ⟨by simp [IntegrableOn], by simp⟩⟩
/-- Equality on a measurable set `U` preserves `HasWeakGradientOn`. -/
theorem HasWeakGradientOn.congr_on {u₁ u₂ : E → ℝ} {g₁ g₂ : E → E} {U : Set E}
    (h : HasWeakGradientOn u₁ g₁ U) (hU : MeasurableSet U)
    (hu : EqOn u₁ u₂ U) (hg : EqOn g₁ g₂ U) :
    HasWeakGradientOn u₂ g₂ U := by
  refine ⟨h.1.congr_fun hg hU, fun φ hφ ↦ ?_⟩
  have hmul : EqOn (fun x ↦ u₁ x * divergence φ x) (fun x ↦ u₂ x * divergence φ x) U :=
    fun x hx ↦ by dsimp; rw [hu hx]
  have hinner : EqOn (fun x ↦ ⟪g₁ x, φ x⟫_ℝ) (fun x ↦ ⟪g₂ x, φ x⟫_ℝ) U :=
    fun x hx ↦ by dsimp; rw [hg hx]
  refine ⟨(h.integrableOn_mul_divergence hφ).congr_fun hmul hU, ?_⟩
  rw [← setIntegral_congr_fun hU hmul, h.integral_mul_divergence hφ,
    setIntegral_congr_fun hU hinner]
/-- Addition of functions with weak gradients on `U`. -/
theorem HasWeakGradientOn.add {u₁ u₂ : E → ℝ} {g₁ g₂ : E → E} {U : Set E}
    (h₁ : HasWeakGradientOn u₁ g₁ U) (h₂ : HasWeakGradientOn u₂ g₂ U) :
    HasWeakGradientOn (u₁ + u₂) (g₁ + g₂) U := by
  refine ⟨h₁.1.add h₂.1, fun φ hφ ↦ ?_⟩
  have hi₁ := h₁.integrableOn_mul_divergence hφ
  have hi₂ := h₂.integrableOn_mul_divergence hφ
  have hmul_eq : (fun x ↦ (u₁ + u₂) x * divergence φ x) =
      (fun x ↦ u₁ x * divergence φ x) + fun x ↦ u₂ x * divergence φ x := by
    ext x; simp [add_mul]
  refine ⟨by rw [hmul_eq]; exact hi₁.add hi₂, ?_⟩
  obtain ⟨C, hC⟩ := hφ.hasCompactSupport.exists_bound_of_continuous hφ.continuous
  have hint_inner : ∀ {g : E → E}, IntegrableOn g U volume →
      IntegrableOn (fun x ↦ ⟪g x, φ x⟫_ℝ) U volume := fun {g} hg ↦ by
    refine Integrable.mono' (hg.norm.const_mul (max C 0))
      (continuous_inner.comp_aestronglyMeasurable
        (hg.aestronglyMeasurable.prodMk hφ.continuous.aestronglyMeasurable)) ?_
    filter_upwards with x
    calc ‖⟪g x, φ x⟫_ℝ‖ ≤ ‖g x‖ * ‖φ x‖ := norm_inner_le_norm (g x) (φ x)
      _ ≤ ‖g x‖ * max C 0 :=
        mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left C 0)) (norm_nonneg _)
      _ = max C 0 * ‖g x‖ := mul_comm _ _
  have hL : ∫ x in U, (u₁ + u₂) x * divergence φ x =
      (∫ x in U, u₁ x * divergence φ x) + ∫ x in U, u₂ x * divergence φ x := by
    simp_rw [Pi.add_apply, add_mul]
    exact integral_add hi₁ hi₂
  have hR : ∫ x in U, ⟪(g₁ + g₂) x, φ x⟫_ℝ =
      (∫ x in U, ⟪g₁ x, φ x⟫_ℝ) + ∫ x in U, ⟪g₂ x, φ x⟫_ℝ := by
    simp_rw [Pi.add_apply, inner_add_left]
    exact integral_add (hint_inner h₁.1) (hint_inner h₂.1)
  rw [hL, h₁.integral_mul_divergence hφ, h₂.integral_mul_divergence hφ, hR, neg_add]
/-- Finite sum of functions with weak gradients on `U`. -/
theorem HasWeakGradientOn.finsetSum {ι : Type*} {s : Finset ι}
    {u : ι → E → ℝ} {g : ι → E → E} {U : Set E}
    (h : ∀ i ∈ s, HasWeakGradientOn (u i) (g i) U) :
    HasWeakGradientOn (fun x ↦ ∑ i ∈ s, u i x) (fun x ↦ ∑ i ∈ s, g i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasWeakGradientOn.zero U
  | @insert a s has ih =>
    have h_u : (fun x ↦ ∑ i ∈ insert a s, u i x) = u a + fun x ↦ ∑ i ∈ s, u i x := by
      ext x; simp [Finset.sum_insert has]
    have h_g : (fun x ↦ ∑ i ∈ insert a s, g i x) = g a + fun x ↦ ∑ i ∈ s, g i x := by
      ext x; simp [Finset.sum_insert has]
    rw [h_u, h_g]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
/-- **Partition-of-unity gluing for weak gradients**: if `IsPartitionOfUnityOn s η U` on a
measurable set `U`, the cutoff gradients satisfy `∑ i ∈ s, g_η i x = 0` on `U`, and each localized
piece `x ↦ η i x * u x` has weak gradient `x ↦ η i x • g x + u x • g_η i x` on `U`, then `u` has
weak gradient `g` on `U`. -/
theorem IsPartitionOfUnityOn.hasWeakGradientOn_of_parts {ι : Type*}
    {s : Finset ι} {η : ι → E → ℝ} {g_η : ι → E → E} {u : E → ℝ} {g : E → E} {U : Set E}
    (h : IsPartitionOfUnityOn s η U) (hU : MeasurableSet U)
    (hgrad : ∀ x ∈ U, ∑ i ∈ s, g_η i x = 0)
    (hparts : ∀ i ∈ s,
      HasWeakGradientOn (fun x ↦ η i x * u x) (fun x ↦ η i x • g x + u x • g_η i x) U) :
    HasWeakGradientOn u g U :=
  (HasWeakGradientOn.finsetSum hparts).congr_on hU
    (fun _ hx ↦ h.sum_mul_eq u hx) (fun _ hx ↦ h.sum_product_rule_eq hgrad u g hx)

end WeakGradientPartitionGluing

end PartitionOfUnityAndContraction

/-! ### Section 2: Strict convergence in `BV` (`IsStrictBVTendstoOn`) and set approximation -/

section StrictBVAndSetApproximation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Strict convergence in `BV(U)`** (`IsStrictBVTendstoOn u_seq u U`): `u_seq n` converges to `u`
in `L¹(U)` (`eLpNorm (u_seq n - u) 1 (volume.restrict U) → 0`) and the variational total variations
converge (`distributionalVariation volume U (u_seq n) → distributionalVariation volume U u`). -/
def IsStrictBVTendstoOn (u_seq : ℕ → E → ℝ) (u : E → ℝ) (U : Opens E) : Prop :=
  Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict (U : Set E))) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ distributionalVariation volume U (u_seq n)) atTop
      (𝓝 (distributionalVariation volume U u))
/-- Predicate asserting that `u : E → ℝ` admits a **smooth (`C^∞`) strict approximation** on
`U : Opens E` (`HasSmoothStrictApproximationOn u U`). -/
def HasSmoothStrictApproximationOn (u : E → ℝ) (U : Opens E) : Prop :=
  ∃ u_seq : ℕ → E → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n)) ∧ IsStrictBVTendstoOn u_seq u U
/-- **Strict perimeter convergence of sets on `U`** (`IsStrictPerimeterTendstoOn A_seq A U`):
`volume ((A_seq n ∆ A) ∩ U) → 0` and
`relativePerimeter volume U (A_seq n) → relativePerimeter volume U A`. -/
def IsStrictPerimeterTendstoOn (A_seq : ℕ → Set E) (A : Set E) (U : Opens E) : Prop :=
  Tendsto (fun n ↦ volume ((A_seq n ∆ A) ∩ (U : Set E))) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ relativePerimeter volume U (A_seq n)) atTop
      (𝓝 (relativePerimeter volume U A))
/-- The constant sequence `fun _ ↦ u` converges strictly in `BV(U)` to `u`. -/
theorem isStrictBVTendstoOn_const (u : E → ℝ) (U : Opens E) :
    IsStrictBVTendstoOn (fun _ ↦ u) u U :=
  ⟨by simp [sub_self], tendsto_const_nhds⟩
/-- Every smooth function `u : E → ℝ` (`ContDiff ℝ ⊤ u`) trivially admits a smooth strict
approximation on `U`. -/
theorem hasSmoothStrictApproximationOn_of_contDiff {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (U : Opens E) : HasSmoothStrictApproximationOn u U :=
  ⟨fun _ ↦ u, fun _ ↦ hu, isStrictBVTendstoOn_const u U⟩
/-- If `u : E → ℝ` is integrable on `U` with respect to `μ` and `φ : E → E` satisfies
`IsSmoothCompactlySupportedOn U φ`, then `x ↦ u x * divergence φ x` is integrable on `U`. -/
theorem IsSmoothCompactlySupportedOn.integrableOn_mul_divergence_of_integrableOn
    {U : Set E} {φ : E → E} {μ : Measure E} (hφ : IsSmoothCompactlySupportedOn U φ)
    {u : E → ℝ} (hu : IntegrableOn u U μ) :
    IntegrableOn (fun x ↦ u x * divergence φ x) U μ := by
  obtain ⟨C, hC⟩ := hφ.hasCompactSupport_divergence.exists_bound_of_continuous
    (continuous_divergence_of_contDiff_one hφ.contDiff_one)
  refine Integrable.mono' (hu.norm.mul_const (max C 0))
    (hu.aestronglyMeasurable.mul
      (continuous_divergence_of_contDiff_one hφ.contDiff_one).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left C 0)) (abs_nonneg _)
/-- **Weak-star convergence of distributional derivatives under `L¹(U)` difference convergence**:
if `eLpNorm (u_seq n - u) 1 (volume.restrict U) → 0` and `u_seq n * divergence φ` and
`u * divergence φ` are integrable on `U`, then
`∫ x in U, u_seq n x * divergence φ x → ∫ x in U, u x * divergence φ x`. -/
theorem tendsto_integral_mul_divergence_of_tendsto_eLpNorm_of_integrableOn {U : Set E}
    {u_seq : ℕ → E → ℝ} {u : E → ℝ} {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ)
    (hu_seq_int : ∀ᶠ n in atTop, IntegrableOn (fun x ↦ u_seq n x * divergence φ x) U volume)
    (hu_int : IntegrableOn (fun x ↦ u x * divergence φ x) U volume)
    (hL1 : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x in U, u_seq n x * divergence φ x) atTop
      (𝓝 (∫ x in U, u x * divergence φ x)) := by
  obtain ⟨C, hC⟩ := hφ.hasCompactSupport_divergence.exists_bound_of_continuous
    (continuous_divergence_of_contDiff_one hφ.contDiff_one)
  set M := max C 0
  have hM_nonneg : 0 ≤ M := le_max_right C 0
  have hev_int : ∀ᶠ n in atTop, IntegrableOn (u_seq n - u) U volume := by
    filter_upwards [hL1.eventually (Iio_mem_nhds ENNReal.zero_lt_top)] with n hn
    exact integrable_of_eLpNorm_one_lt_top hn
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htoReal : Tendsto (fun n ↦ M * (eLpNorm (u_seq n - u) 1 (volume.restrict U)).toReal)
      atTop (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1).const_mul M
  filter_upwards [hu_seq_int, hev_int, (Metric.tendsto_nhds.mp htoReal) ε hε] with
    n hn_seq hn_sub hn_bound
  have hsub_eq :
      (∫ x in U, u_seq n x * divergence φ x) - ∫ x in U, u x * divergence φ x =
        ∫ x in U, (u_seq n x - u x) * divergence φ x := by
    rw [← integral_sub hn_seq hu_int]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [Real.dist_eq, hsub_eq]
  have hnorm_le : |∫ x in U, (u_seq n x - u x) * divergence φ x| ≤
      M * (eLpNorm (u_seq n - u) 1 (volume.restrict U)).toReal := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hle : ∀ x, ‖(u_seq n x - u x) * divergence φ x‖ ≤ M * ‖(u_seq n - u) x‖ := fun x ↦ by
      rw [norm_mul, mul_comm, Pi.sub_apply]
      exact mul_le_mul_of_nonneg_right ((hC x).trans (le_max_left C 0)) (norm_nonneg _)
    calc ∫ x in U, ‖(u_seq n x - u x) * divergence φ x‖
        ≤ ∫ x in U, M * ‖(u_seq n - u) x‖ :=
          integral_mono (hφ.integrableOn_mul_divergence_of_integrableOn hn_sub).norm
            (hn_sub.norm.const_mul M) hle
      _ = M * ∫ x in U, ‖(u_seq n - u) x‖ := integral_const_mul M _
      _ = M * (eLpNorm (u_seq n - u) 1 (volume.restrict U)).toReal := by
          rw [eLpNorm_one_eq_lintegral_enorm hn_sub.aestronglyMeasurable,
            integral_norm_eq_lintegral_enorm hn_sub.aestronglyMeasurable]
  rw [dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hM_nonneg ENNReal.toReal_nonneg)] at hn_bound
  exact hnorm_le.trans_lt hn_bound
/-- **Weak-star convergence of distributional derivatives under `L¹(U)` convergence**:
if `eLpNorm (u_seq n - u) 1 (volume.restrict U) → 0` and `u` is integrable on `U`, then for every
smooth compactly supported test vector field `φ` on `U` (`IsSmoothCompactlySupportedOn U φ`),
`∫ x in U, u_seq n x * divergence φ x → ∫ x in U, u x * divergence φ x`. -/
theorem tendsto_integral_mul_divergence_of_tendsto_eLpNorm {U : Set E}
    {u_seq : ℕ → E → ℝ} {u : E → ℝ} (hu : IntegrableOn u U volume)
    (hL1 : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict U)) atTop (𝓝 0))
    {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ) :
    Tendsto (fun n ↦ ∫ x in U, u_seq n x * divergence φ x) atTop
      (𝓝 (∫ x in U, u x * divergence φ x)) := by
  have hev_seq : ∀ᶠ n in atTop, IntegrableOn (fun x ↦ u_seq n x * divergence φ x) U volume := by
    filter_upwards [hL1.eventually (Iio_mem_nhds ENNReal.zero_lt_top)] with n hn
    have hn_sub : IntegrableOn (u_seq n - u) U volume := integrable_of_eLpNorm_one_lt_top hn
    have heq : u_seq n = (u_seq n - u) + u := by ext x; simp
    rw [heq]
    exact hφ.integrableOn_mul_divergence_of_integrableOn (hn_sub.add hu)
  exact tendsto_integral_mul_divergence_of_tendsto_eLpNorm_of_integrableOn hφ hev_seq
    (hφ.integrableOn_mul_divergence_of_integrableOn hu) hL1

namespace IsStrictBVTendstoOn

variable {u_seq : ℕ → E → ℝ} {u : E → ℝ} {U : Opens E}

/-- `L¹(U)` convergence component of `IsStrictBVTendstoOn`. -/
theorem tendsto_eLpNorm_sub (h : IsStrictBVTendstoOn u_seq u U) :
    Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict (U : Set E))) atTop (𝓝 0) := h.1
/-- Total variation convergence component of `IsStrictBVTendstoOn`. -/
theorem tendsto_distributionalVariation (h : IsStrictBVTendstoOn u_seq u U) :
    Tendsto (fun n ↦ distributionalVariation volume U (u_seq n)) atTop
      (𝓝 (distributionalVariation volume U u)) := h.2
/-- Negation preserves `IsStrictBVTendstoOn`. -/
theorem neg (h : IsStrictBVTendstoOn u_seq u U) :
    IsStrictBVTendstoOn (fun n ↦ -u_seq n) (-u) U := by
  refine ⟨?_, ?_⟩
  · have hsub : ∀ n, -u_seq n - -u = -(u_seq n - u) := fun n ↦ by ext x; simp; ring
    simp_rw [hsub, eLpNorm_neg]; exact h.1
  · simp_rw [distributionalVariation_neg]; exact h.2
/-- Scalar multiplication by `c : ℝ` preserves `IsStrictBVTendstoOn`. -/
theorem smul (h : IsStrictBVTendstoOn u_seq u U) (c : ℝ) :
    IsStrictBVTendstoOn (fun n ↦ c • u_seq n) (c • u) U := by
  refine ⟨?_, ?_⟩
  · have hsub : ∀ n, c • u_seq n - c • u = c • (u_seq n - u) := fun n ↦ (smul_sub c _ _).symm
    simp_rw [hsub, eLpNorm_const_smul]
    simpa using ENNReal.Tendsto.const_mul h.1 (Or.inr enorm_ne_top)
  · simp_rw [distributionalVariation_smul]
    exact ENNReal.Tendsto.const_mul h.2 (Or.inr ENNReal.ofReal_ne_top)
/-- Adding a constant `c : ℝ` preserves `IsStrictBVTendstoOn`. -/
theorem add_const (h : IsStrictBVTendstoOn u_seq u U) (c : ℝ) :
    IsStrictBVTendstoOn (fun n x ↦ u_seq n x + c) (fun x ↦ u x + c) U := by
  refine ⟨?_, ?_⟩
  · have hsub : ∀ n, ((fun x ↦ u_seq n x + c) - fun x ↦ u x + c) = u_seq n - u :=
      fun n ↦ by ext x; simp
    simp_rw [hsub]; exact h.1
  · simp_rw [distributionalVariation_add_const]; exact h.2
/-- Under `IsStrictBVTendstoOn u_seq u U`, `eLpNorm (u_seq n) 1 (volume.restrict U)` converges to
`eLpNorm u 1 (volume.restrict U)`. -/
theorem tendsto_eLpNorm (h : IsStrictBVTendstoOn u_seq u U) :
    Tendsto (fun n ↦ eLpNorm (u_seq n) 1 (volume.restrict (U : Set E))) atTop
      (𝓝 (eLpNorm u 1 (volume.restrict (U : Set E)))) :=
  tendsto_eLpNorm_of_tendsto_eLpNorm_sub h.1
/-- **Full `BV(U)` norm convergence**: under `IsStrictBVTendstoOn u_seq u U`, the full `BV(U)` norm
`eLpNorm (u_seq n) 1 (volume.restrict U) + distributionalVariation volume U (u_seq n)` converges to
`eLpNorm u 1 (volume.restrict U) + distributionalVariation volume U u`. -/
theorem tendsto_bvNorm (h : IsStrictBVTendstoOn u_seq u U) :
    Tendsto (fun n ↦ eLpNorm (u_seq n) 1 (volume.restrict (U : Set E)) +
        distributionalVariation volume U (u_seq n)) atTop
      (𝓝 (eLpNorm u 1 (volume.restrict (U : Set E)) + distributionalVariation volume U u)) :=
  h.tendsto_eLpNorm.add h.2
/-- **Weak-star convergence of distributional derivatives under `IsStrictBVTendstoOn`**:
for every smooth compactly supported test vector field `φ` on `U`,
`∫ x in U, u_seq n x * divergence φ x → ∫ x in U, u x * divergence φ x`. -/
theorem tendsto_integral_mul_divergence (h : IsStrictBVTendstoOn u_seq u U)
    (hu : IntegrableOn u U volume) {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ) :
    Tendsto (fun n ↦ ∫ x in (U : Set E), u_seq n x * divergence φ x) atTop
      (𝓝 (∫ x in (U : Set E), u x * divergence φ x)) :=
  tendsto_integral_mul_divergence_of_tendsto_eLpNorm hu h.1 hφ

end IsStrictBVTendstoOn

/-- The constant set sequence `fun _ ↦ A` converges strictly in perimeter on `U` to `A`. -/
theorem isStrictPerimeterTendstoOn_const (A : Set E) (U : Opens E) :
    IsStrictPerimeterTendstoOn (fun _ ↦ A) A U :=
  ⟨by simp, tendsto_const_nhds⟩

namespace IsStrictPerimeterTendstoOn

variable {A_seq : ℕ → Set E} {A : Set E} {U : Opens E}

/-- Symmetric-difference volume convergence component of `IsStrictPerimeterTendstoOn`. -/
theorem tendsto_symmDiff (h : IsStrictPerimeterTendstoOn A_seq A U) :
    Tendsto (fun n ↦ volume ((A_seq n ∆ A) ∩ (U : Set E))) atTop (𝓝 0) := h.1
/-- Relative perimeter convergence component of `IsStrictPerimeterTendstoOn`. -/
theorem tendsto_relativePerimeter (h : IsStrictPerimeterTendstoOn A_seq A U) :
    Tendsto (fun n ↦ relativePerimeter volume U (A_seq n)) atTop
      (𝓝 (relativePerimeter volume U A)) := h.2
/-- **Complement symmetry of `IsStrictPerimeterTendstoOn`**: if `A_seq n → A` strictly in perimeter
on `U`, then `(A_seq n)ᶜ → Aᶜ` strictly in perimeter on `U`. -/
theorem compl (h : IsStrictPerimeterTendstoOn A_seq A U) :
    IsStrictPerimeterTendstoOn (fun n ↦ (A_seq n)ᶜ) Aᶜ U := by
  refine ⟨?_, ?_⟩
  · have hsymm : ∀ n, (A_seq n)ᶜ ∆ Aᶜ = A_seq n ∆ A := fun n ↦ by
      ext x; simp [symmDiff, and_comm, or_comm]
    simp_rw [hsymm]; exact h.1
  · simp_rw [relativePerimeter_compl]; exact h.2
/-- **Volume continuity under `IsStrictPerimeterTendstoOn`**: if
`IsStrictPerimeterTendstoOn A_seq A U`, then `volume (A_seq n ∩ U) → volume (A ∩ U)`. -/
theorem tendsto_volume_inter (h : IsStrictPerimeterTendstoOn A_seq A U) :
    Tendsto (fun n ↦ volume (A_seq n ∩ (U : Set E))) atTop (𝓝 (volume (A ∩ (U : Set E)))) := by
  have h_low : ∀ n, volume (A ∩ (U : Set E)) - volume ((A_seq n ∆ A) ∩ (U : Set E)) ≤
      volume (A_seq n ∩ (U : Set E)) := by
    intro n
    rw [tsub_le_iff_right, add_comm]
    have hsub : A ∩ (U : Set E) ⊆ ((A_seq n ∆ A) ∩ (U : Set E)) ∪ (A_seq n ∩ (U : Set E)) := by
      intro x ⟨hxA, hxU⟩
      by_cases hxAn : x ∈ A_seq n
      · exact Or.inr ⟨hxAn, hxU⟩
      · exact Or.inl ⟨Or.inr ⟨hxA, hxAn⟩, hxU⟩
    exact (measure_mono hsub).trans (measure_union_le _ _)
  have h_up : ∀ n, volume (A_seq n ∩ (U : Set E)) ≤
      volume ((A_seq n ∆ A) ∩ (U : Set E)) + volume (A ∩ (U : Set E)) := by
    intro n
    have hsub : A_seq n ∩ (U : Set E) ⊆ ((A_seq n ∆ A) ∩ (U : Set E)) ∪ (A ∩ (U : Set E)) := by
      intro x ⟨hxAn, hxU⟩
      by_cases hxA : x ∈ A
      · exact Or.inr ⟨hxA, hxU⟩
      · exact Or.inl ⟨Or.inl ⟨hxAn, hxA⟩, hxU⟩
    exact (measure_mono hsub).trans (measure_union_le _ _)
  have h_lim_low : Tendsto (fun n ↦ volume (A ∩ (U : Set E)) - volume ((A_seq n ∆ A) ∩ (U : Set E)))
      atTop (𝓝 (volume (A ∩ (U : Set E)))) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h.1 (Or.inr ENNReal.zero_ne_top)
  have h_lim_up : Tendsto (fun n ↦ volume ((A_seq n ∆ A) ∩ (U : Set E)) + volume (A ∩ (U : Set E)))
      atTop (𝓝 (volume (A ∩ (U : Set E)))) := by
    simpa using h.1.add tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_lim_low h_lim_up h_low h_up

end IsStrictPerimeterTendstoOn

/-- The `L¹(U)` distance between characteristic functions of measurable sets `S` and `T` equals
`volume ((S ∆ T) ∩ U)`. -/
theorem eLpNorm_indicator_sub_indicator_eq_volume_symmDiff {S T : Set E} {U : Set E}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    eLpNorm (S.indicator (fun _ ↦ (1 : ℝ)) - T.indicator (fun _ ↦ (1 : ℝ))) 1
        (volume.restrict U) = volume ((S ∆ T) ∩ U) := by
  have hmeas : AEStronglyMeasurable
      (S.indicator (fun _ ↦ (1 : ℝ)) - T.indicator (fun _ ↦ (1 : ℝ))) (volume.restrict U) :=
    ((stronglyMeasurable_const.indicator hS).sub
      (stronglyMeasurable_const.indicator hT)).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hmeas]
  simp_rw [Pi.sub_apply, enorm_indicator_sub_indicator_one]
  rw [lintegral_indicator (hS.symmDiff hT), setLIntegral_one,
    Measure.restrict_apply (hS.symmDiff hT)]
/-- **Bridge between strict set perimeter convergence and strict `BV` convergence of indicators**:
for measurable sets `A_seq n` and `A`, `IsStrictPerimeterTendstoOn A_seq A U` holds if and only if
`IsStrictBVTendstoOn (fun n ↦ (A_seq n).indicator 1) (A.indicator 1) U` holds. -/
theorem isStrictPerimeterTendstoOn_iff_isStrictBVTendstoOn_indicator
    {A_seq : ℕ → Set E} {A : Set E} {U : Opens E}
    (hA_seq : ∀ n, MeasurableSet (A_seq n)) (hA : MeasurableSet A) :
    IsStrictPerimeterTendstoOn A_seq A U ↔
      IsStrictBVTendstoOn (fun n ↦ (A_seq n).indicator (fun _ ↦ (1 : ℝ)))
        (A.indicator (fun _ ↦ (1 : ℝ))) U := by
  unfold IsStrictPerimeterTendstoOn IsStrictBVTendstoOn relativePerimeter
  rw [and_congr_left_iff]
  intro _
  refine tendsto_congr fun n ↦ ?_
  exact (eLpNorm_indicator_sub_indicator_eq_volume_symmDiff (hA_seq n) hA).symm

end StrictBVAndSetApproximation

/-! ### Section 3: Weak-star limit of derivative measures and `L¹`-closedness of `BV` balls -/

section WeakStarLimitAndBVClosedness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Weak-star limit of derivative measures**: if
`HasDerivativeMeasureOn (u_seq n) U (σ_seq n) (ν_seq n)` holds for each `n`,
`eLpNorm (u_seq n - u) 1 (volume.restrict U) → 0`, and for an admissible test vector field `φ` on
`U` (`IsSmoothCompactlySupportedOn U φ`),
`∫ x in U, ⟪σ_seq n x, φ x⟫_ℝ ∂(ν_seq n) → ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν`, then `u` satisfies the
distributional integration-by-parts identity
`∫ x in U, u x * divergence φ x = - ∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν`. -/
theorem integral_mul_divergence_eq_neg_of_tendsto_derivativeMeasure {U : Set E}
    {u_seq : ℕ → E → ℝ} {u : E → ℝ} {σ_seq : ℕ → E → E} {ν_seq : ℕ → Measure E}
    {σ : E → E} {ν : Measure E}
    (h_seq : ∀ n, HasDerivativeMeasureOn (u_seq n) U (σ_seq n) (ν_seq n))
    (hu : IntegrableOn u U volume)
    (hL1 : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict U)) atTop (𝓝 0))
    {φ : E → E} (hφ : IsSmoothCompactlySupportedOn U φ)
    (hpair : Tendsto (fun n ↦ ∫ x in U, ⟪σ_seq n x, φ x⟫_ℝ ∂(ν_seq n)) atTop
      (𝓝 (∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν))) :
    ∫ x in U, u x * divergence φ x = -∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν := by
  have hLHS := tendsto_integral_mul_divergence_of_tendsto_eLpNorm hu hL1 hφ
  have hRHS : Tendsto (fun n ↦ ∫ x in U, u_seq n x * divergence φ x) atTop
      (𝓝 (-∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν)) := by
    simp_rw [(h_seq _).integral_mul_divergence hφ]
    exact hpair.neg
  exact tendsto_nhds_unique hLHS hRHS
/-- **Stability of `HasDerivativeMeasureOn` under `L¹(U)` and weak-star derivative convergence**:
if `HasDerivativeMeasureOn (u_seq n) U (σ_seq n) (ν_seq n)` holds for each `n`, `u_seq n → u` in
`L¹(U)`, and the derivative pairings converge to `∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν` for every admissible
test vector field `φ` on `U`, then `HasDerivativeMeasureOn u U σ ν`. -/
theorem hasDerivativeMeasureOn_of_tendsto {U : Set E}
    {u_seq : ℕ → E → ℝ} {u : E → ℝ} {σ_seq : ℕ → E → E} {ν_seq : ℕ → Measure E}
    {σ : E → E} {ν : Measure E}
    (h_seq : ∀ n, HasDerivativeMeasureOn (u_seq n) U (σ_seq n) (ν_seq n))
    (hu : IntegrableOn u U volume)
    (hL1 : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict U)) atTop (𝓝 0))
    (hσ_meas : AEStronglyMeasurable σ (ν.restrict U))
    (hσ_norm : ∀ᵐ x ∂(ν.restrict U), ‖σ x‖ ≤ 1)
    (hpair : ∀ ⦃φ : E → E⦄, IsSmoothCompactlySupportedOn U φ →
      Tendsto (fun n ↦ ∫ x in U, ⟪σ_seq n x, φ x⟫_ℝ ∂(ν_seq n)) atTop
        (𝓝 (∫ x in U, ⟪σ x, φ x⟫_ℝ ∂ν))) :
    HasDerivativeMeasureOn u U σ ν :=
  ⟨hσ_meas, hσ_norm, fun _ hφ ↦ ⟨hφ.integrableOn_mul_divergence_of_integrableOn hu,
    integral_mul_divergence_eq_neg_of_tendsto_derivativeMeasure h_seq hu hL1 hφ (hpair hφ)⟩⟩
/-- **Sequential `L¹(U)` lower semicontinuity of `distributionalVariation`**:
if `eLpNorm (u_seq n - u) 1 (volume.restrict U) → 0`, then
`distributionalVariation volume U u ≤
  liminf (fun n ↦ distributionalVariation volume U (u_seq n)) atTop`. -/
theorem distributionalVariation_le_liminf_of_tendsto_eLpNorm {U : Opens E}
    {u_seq : ℕ → E → ℝ} {u : E → ℝ} (hu : IntegrableOn u U volume)
    (hL1 : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict (U : Set E))) atTop (𝓝 0)) :
    distributionalVariation volume U u ≤
      liminf (fun n ↦ distributionalVariation volume U (u_seq n)) atTop :=
  distributionalVariation_le_liminf fun φ ↦
    tendsto_integral_mul_divergence_of_tendsto_eLpNorm hu hL1
      (IsSmoothCompactlySupportedOn.of_testFunction φ)
/-- **Transfer of uniform variation bounds under `L¹(U)` convergence**:
if `eLpNorm (u_seq n - u) 1 (volume.restrict U) → 0` and
`∀ n, distributionalVariation volume U (u_seq n) ≤ M`, then
`distributionalVariation volume U u ≤ M`. -/
theorem distributionalVariation_le_of_tendsto_eLpNorm {U : Opens E}
    {u_seq : ℕ → E → ℝ} {u : E → ℝ} {M : ℝ≥0∞} (hu : IntegrableOn u U volume)
    (hL1 : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict (U : Set E))) atTop (𝓝 0))
    (hM : ∀ n, distributionalVariation volume U (u_seq n) ≤ M) :
    distributionalVariation volume U u ≤ M := by
  refine iSup₂_le fun φ hφ ↦ ?_
  have hlim : Tendsto
      (fun n ↦ ENNReal.ofReal (∫ x in (U : Set E), u_seq n x * divergence (φ : E → E) x)) atTop
      (𝓝 (ENNReal.ofReal (∫ x in (U : Set E), u x * divergence (φ : E → E) x))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_integral_mul_divergence_of_tendsto_eLpNorm hu hL1
        (IsSmoothCompactlySupportedOn.of_testFunction φ))
  exact le_of_tendsto hlim (Eventually.of_forall fun n ↦
    (le_distributionalVariation φ hφ (u_seq n)).trans (hM n))
/-- **`L¹(U)`-closedness of `BV(U)` norm balls**: if
`eLpNorm (u_seq n - u) 1 (volume.restrict U) → 0` and
`∀ n, eLpNorm (u_seq n) 1 (volume.restrict U) + distributionalVariation volume U (u_seq n) ≤ M`,
then `eLpNorm u 1 (volume.restrict U) + distributionalVariation volume U u ≤ M`. -/
theorem eLpNorm_add_distributionalVariation_le_of_tendsto_eLpNorm {U : Opens E}
    {u_seq : ℕ → E → ℝ} {u : E → ℝ} {M : ℝ≥0∞} (hu : IntegrableOn u U volume)
    (hL1 : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict (U : Set E))) atTop (𝓝 0))
    (hM : ∀ n,
      eLpNorm (u_seq n) 1 (volume.restrict (U : Set E)) +
        distributionalVariation volume U (u_seq n) ≤ M) :
    eLpNorm u 1 (volume.restrict (U : Set E)) + distributionalVariation volume U u ≤ M := by
  unfold distributionalVariation
  rw [ENNReal.add_iSup]
  refine iSup_le fun φ ↦ ?_
  have hlim₁ := tendsto_eLpNorm_of_tendsto_eLpNorm_sub hL1
  by_cases hφ : ∀ x, ‖φ x‖ ≤ 1
  · rw [ciSup_pos hφ]
    have hlim₂ : Tendsto
        (fun n ↦ ENNReal.ofReal (∫ x in (U : Set E), u_seq n x * divergence (φ : E → E) x)) atTop
        (𝓝 (ENNReal.ofReal (∫ x in (U : Set E), u x * divergence (φ : E → E) x))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_integral_mul_divergence_of_tendsto_eLpNorm hu hL1
          (IsSmoothCompactlySupportedOn.of_testFunction φ))
    exact le_of_tendsto (hlim₁.add hlim₂) (Eventually.of_forall fun n ↦
      (add_le_add_right (le_distributionalVariation φ hφ (u_seq n)) _).trans (hM n))
  · simp only [hφ, iSup_neg, not_false_eq_true, bot_eq_zero, add_zero]
    exact le_of_tendsto hlim₁ (Eventually.of_forall fun n ↦ le_self_add.trans (hM n))
/-- If `eLpNorm (u_seq n - u) 1 (volume.restrict U) → 0`, `u` is integrable on `U`, and
`distributionalVariation volume U (u_seq n) ≤ M < ⊤` for all `n`, then `IsBVOn volume U u`. -/
theorem isBVOn_of_tendsto_eLpNorm {U : Opens E} {u_seq : ℕ → E → ℝ} {u : E → ℝ} {M : ℝ≥0∞}
    (hu : IntegrableOn u U volume)
    (hL1 : Tendsto (fun n ↦ eLpNorm (u_seq n - u) 1 (volume.restrict (U : Set E))) atTop (𝓝 0))
    (hM : ∀ n, distributionalVariation volume U (u_seq n) ≤ M) (hM_lt : M < ⊤) :
    IsBVOn volume U u :=
  ⟨hu, (distributionalVariation_le_of_tendsto_eLpNorm hu hL1 hM).trans_lt hM_lt⟩
/-- **Sequential lower semicontinuity of relative perimeter under symmetric-difference
convergence**: if `volume ((A_seq n ∆ A) ∩ U) → 0` for measurable sets `A_seq n` and `A`, then
`relativePerimeter volume U A ≤ liminf (fun n ↦ relativePerimeter volume U (A_seq n)) atTop`. -/
theorem relativePerimeter_le_liminf_of_tendsto_symmDiff {U : Opens E}
    {A_seq : ℕ → Set E} {A : Set E}
    (hA_seq : ∀ n, MeasurableSet (A_seq n)) (hA : MeasurableSet A)
    (hL1 : Tendsto (fun n ↦ volume ((A_seq n ∆ A) ∩ (U : Set E))) atTop (𝓝 0)) :
    relativePerimeter volume U A ≤
      liminf (fun n ↦ relativePerimeter volume U (A_seq n)) atTop := by
  refine relativePerimeter_le_liminf fun φ ↦ ?_
  have hint : ∀ {S : Set E}, MeasurableSet S →
      IntegrableOn (fun x ↦ S.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x) U volume :=
    fun {S} hS ↦ by
      have heq : (fun x ↦ S.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x) =
          S.indicator (divergence (φ : E → E)) := by ext x; by_cases hx : x ∈ S <;> simp [hx]
      rw [heq]; exact (integrableOn_divergence_testFunction φ).indicator hS
  have hL1_ind : Tendsto (fun n ↦ eLpNorm
      ((A_seq n).indicator (fun _ ↦ (1 : ℝ)) - A.indicator (fun _ ↦ (1 : ℝ))) 1
      (volume.restrict (U : Set E))) atTop (𝓝 0) := by
    refine (tendsto_congr fun n ↦ ?_).mp hL1
    exact (eLpNorm_indicator_sub_indicator_eq_volume_symmDiff (hA_seq n) hA).symm
  exact tendsto_integral_mul_divergence_of_tendsto_eLpNorm_of_integrableOn
    (IsSmoothCompactlySupportedOn.of_testFunction φ) (Eventually.of_forall fun n ↦ hint (hA_seq n))
    (hint hA) hL1_ind
/-- **Transfer of uniform relative perimeter bounds under symmetric-difference convergence**:
if `volume ((A_seq n ∆ A) ∩ U) → 0` for measurable sets `A_seq n` and `A`, and
`∀ n, relativePerimeter volume U (A_seq n) ≤ M`, then `relativePerimeter volume U A ≤ M`. -/
theorem relativePerimeter_le_of_tendsto_symmDiff {U : Opens E}
    {A_seq : ℕ → Set E} {A : Set E} {M : ℝ≥0∞}
    (hA_seq : ∀ n, MeasurableSet (A_seq n)) (hA : MeasurableSet A)
    (hL1 : Tendsto (fun n ↦ volume ((A_seq n ∆ A) ∩ (U : Set E))) atTop (𝓝 0))
    (hM : ∀ n, relativePerimeter volume U (A_seq n) ≤ M) :
    relativePerimeter volume U A ≤ M := by
  refine (relativePerimeter_le_liminf_of_tendsto_symmDiff hA_seq hA hL1).trans ?_
  exact liminf_le_of_frequently_le' (Eventually.of_forall hM).frequently

end WeakStarLimitAndBVClosedness

end TauCeti
