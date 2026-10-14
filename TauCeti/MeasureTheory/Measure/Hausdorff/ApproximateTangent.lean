/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.MeasureTheory.Measure.Hausdorff.LipschitzAreaCoarea
import all TauCeti.MeasureTheory.Measure.Hausdorff.LipschitzAreaCoarea

/-!
# Hausdorff Density Ratios, Approximate Tangent Subspaces, and Tangential Area Formula

This file develops `d`-dimensional Hausdorff ball density ratios, density-one and density-zero
points, approximate tangent subspaces (`HasApproxTangentSubspaceAt`), tangential Fréchet
derivatives (`tangentialFDeriv`) along subspaces and `C¹` graphs, and the tangential area formula
under Hausdorff-null modifications and countable rectifiable decompositions:

1. **Hausdorff density ratios, density-one points, and approximate tangent subspaces**:
   `TauCeti.hausdorffBallRatio`, `TauCeti.HasHausdorffDensityAt`,
   `TauCeti.HasHausdorffDensityOneAt`, `TauCeti.HasHausdorffDensityZeroAt`,
   `TauCeti.HasHausdorffDensityAt.unique`, `TauCeti.hasHausdorffDensityAt_congr_symmDiff_zero`,
   `TauCeti.hasHausdorffDensityAt_iff_of_symmDiff_subset_densityZero`,
   `TauCeti.HasApproxTangentSubspaceAt`, `TauCeti.HasApproxTangentSubspaceAt.congr_symmDiff_zero`,
   `TauCeti.HasApproxTangentSubspaceAt.localize_ball`, and
   `TauCeti.hasApproxTangentSubspaceAt_vadd_submodule_iff`.
2. **Tangential differentiation, chart independence, and `C¹` graph tangent subspaces**:
   `TauCeti.tangentialFDeriv`, `TauCeti.norm_tangentialFDeriv_le_of_lipschitzWith`,
   `TauCeti.enorm_tangentialFDeriv_le_of_lipschitzWith`, `TauCeti.tangentialFDeriv_comp`,
   `TauCeti.fderiv_comp_chart_eq_tangentialFDeriv`, `TauCeti.tangentialFDeriv_congr_of_chart_range`,
   `TauCeti.graphMap`, `TauCeti.graphTangentSubspace`, `TauCeti.fderiv_graphMap`,
   `TauCeti.fderiv_comp_graphMap_apply`, `TauCeti.hasHausdorffDensityZeroAt_cone_graphMap`, and
   `TauCeti.hasApproxTangentSubspaceAt_graphMap_iff`.
3. **Null-modification invariance and countable rectifiable decomposition of the area formula**:
   `TauCeti.AreaFormulaHolds.congr_symmDiff_subset_null`,
   `TauCeti.AreaFormulaHolds.congr_symmDiff_hausdorffMeasure_zero`,
   `TauCeti.AreaFormulaHolds.of_rectifiable_decomposition`, and
   `TauCeti.AreaFormulaHolds.of_eq_null_union_iUnion`.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set
open scoped ENNReal NNReal Topology
open TauCeti.MeasureTheory

namespace TauCeti

/-! ### Section 1: Hausdorff density ratios and approximate tangent subspaces -/

section HausdorffDensityAndApproxTangent

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The `d`-dimensional Hausdorff ball ratio of a set `M ⊆ E` around `x : E` at radius `r : ℝ`,
normalized by `ω * ENNReal.ofReal r ^ d`. -/
def hausdorffBallRatio (d : ℝ) (ω : ℝ≥0∞) (M : Set E) (x : E) (r : ℝ) : ℝ≥0∞ :=
  μH[d] (M ∩ Metric.ball x r) / (ω * ENNReal.ofReal r ^ d)

/-- A set `M ⊆ E` has `d`-dimensional Hausdorff density `θ` (with normalization factor `ω`) at
`x : E` if `hausdorffBallRatio d ω M x r → θ` as `r → 0⁺`. -/
def HasHausdorffDensityAt (d : ℝ) (ω : ℝ≥0∞) (M : Set E) (x : E) (θ : ℝ≥0∞) : Prop :=
  Tendsto (hausdorffBallRatio d ω M x) (𝓝[>] 0) (𝓝 θ)

/-- A set `M ⊆ E` has `d`-dimensional Hausdorff density `1` at `x : E`. -/
def HasHausdorffDensityOneAt (d : ℝ) (ω : ℝ≥0∞) (M : Set E) (x : E) : Prop :=
  HasHausdorffDensityAt d ω M x 1

/-- A set `M ⊆ E` has `d`-dimensional Hausdorff density `0` at `x : E`. -/
def HasHausdorffDensityZeroAt (d : ℝ) (ω : ℝ≥0∞) (M : Set E) (x : E) : Prop :=
  HasHausdorffDensityAt d ω M x 0

/-- Uniqueness of the Hausdorff density limit at `x`. -/
theorem HasHausdorffDensityAt.unique {d : ℝ} {ω : ℝ≥0∞} {M : Set E} {x : E} {θ₁ θ₂ : ℝ≥0∞}
    (h₁ : HasHausdorffDensityAt d ω M x θ₁) (h₂ : HasHausdorffDensityAt d ω M x θ₂) :
    θ₁ = θ₂ := by
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique h₁ h₂

@[simp]
theorem hausdorffBallRatio_empty (d : ℝ) (ω : ℝ≥0∞) (x : E) (r : ℝ) :
    hausdorffBallRatio d ω (∅ : Set E) x r = 0 := by simp [hausdorffBallRatio]

/-- For `r ≤ 0`, `hausdorffBallRatio d ω M x r = 0` since `Metric.ball x r = ∅`. -/
theorem hausdorffBallRatio_of_le_zero (d : ℝ) (ω : ℝ≥0∞) (M : Set E) (x : E) {r : ℝ} (hr : r ≤ 0) :
    hausdorffBallRatio d ω M x r = 0 := by
  rw [hausdorffBallRatio, Metric.ball_eq_empty.mpr hr, inter_empty, measure_empty, ENNReal.zero_div]

/-- Monotonicity of `hausdorffBallRatio` in the set argument. -/
theorem hausdorffBallRatio_mono_set {d : ℝ} {ω : ℝ≥0∞} {M₁ M₂ : Set E} (h : M₁ ⊆ M₂)
    (x : E) (r : ℝ) :
    hausdorffBallRatio d ω M₁ x r ≤ hausdorffBallRatio d ω M₂ x r :=
  ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ h)) _

/-- Subadditivity of `hausdorffBallRatio` under binary union. -/
theorem hausdorffBallRatio_union_le (d : ℝ) (ω : ℝ≥0∞) (M₁ M₂ : Set E) (x : E) (r : ℝ) :
    hausdorffBallRatio d ω (M₁ ∪ M₂) x r ≤
      hausdorffBallRatio d ω M₁ x r + hausdorffBallRatio d ω M₂ x r := by
  unfold hausdorffBallRatio
  rw [union_inter_distrib_right, ← ENNReal.add_div]
  exact ENNReal.div_le_div_right (measure_union_le _ _) _

/-- Monotonicity of `HasHausdorffDensityZeroAt` under set inclusion. -/
theorem HasHausdorffDensityZeroAt.mono {d : ℝ} {ω : ℝ≥0∞} {M₁ M₂ : Set E} (h : M₁ ⊆ M₂)
    {x : E} (h₂ : HasHausdorffDensityZeroAt d ω M₂ x) :
    HasHausdorffDensityZeroAt d ω M₁ x :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h₂
    (fun _ ↦ bot_le) (fun r ↦ hausdorffBallRatio_mono_set h x r)

/-- The union of two sets of Hausdorff density zero at `x` has Hausdorff density zero at `x`. -/
theorem HasHausdorffDensityZeroAt.union {d : ℝ} {ω : ℝ≥0∞} {M₁ M₂ : Set E} {x : E}
    (h₁ : HasHausdorffDensityZeroAt d ω M₁ x) (h₂ : HasHausdorffDensityZeroAt d ω M₂ x) :
    HasHausdorffDensityZeroAt d ω (M₁ ∪ M₂) x := by
  have hsum : Tendsto (fun r ↦ hausdorffBallRatio d ω M₁ x r + hausdorffBallRatio d ω M₂ x r)
      (𝓝[>] 0) (𝓝 0) := by simpa using h₁.add h₂
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ bot_le) (hausdorffBallRatio_union_le d ω M₁ M₂ x)

/-- Any `Hᵈ`-null set has `Hᵈ`-density zero at every point. -/
theorem hasHausdorffDensityZeroAt_of_measure_zero {d : ℝ} {ω : ℝ≥0∞} {M : Set E}
    (hM : μH[d] M = 0) (x : E) :
    HasHausdorffDensityZeroAt d ω M x := by
  have hzero : hausdorffBallRatio d ω M x = fun _ ↦ 0 := by
    ext r; rw [hausdorffBallRatio, measure_mono_null inter_subset_left hM, ENNReal.zero_div]
  simp [HasHausdorffDensityZeroAt, HasHausdorffDensityAt, hzero]

/-- The empty set has Hausdorff density `0` at every point. -/
theorem hasHausdorffDensityZeroAt_empty (d : ℝ) (ω : ℝ≥0∞) (x : E) :
    HasHausdorffDensityZeroAt d ω (∅ : Set E) x :=
  hasHausdorffDensityZeroAt_of_measure_zero measure_empty x

/-- For `0 < d`, every singleton `{x}` has `d`-dimensional Hausdorff measure zero. -/
theorem hausdorffMeasure_singleton_of_pos (x : E) {d : ℝ} (hd : 0 < d) :
    μH[d] ({x} : Set E) = 0 := by
  rcases hausdorffMeasure_zero_or_top hd ({x} : Set E) with h0 | htop
  · exact h0
  · rw [hausdorffMeasure_zero_singleton] at htop; exact absurd htop ENNReal.one_ne_top

/-- For `0 < d`, every singleton `{y}` has `Hᵈ`-density zero at every point `x`. -/
theorem hasHausdorffDensityZeroAt_singleton {d : ℝ} (hd : 0 < d) (ω : ℝ≥0∞) (y x : E) :
    HasHausdorffDensityZeroAt d ω ({y} : Set E) x :=
  hasHausdorffDensityZeroAt_of_measure_zero (hausdorffMeasure_singleton_of_pos y hd) x

/-- For `r ≤ R`, intersecting `M` with `Metric.ball x R` leaves `hausdorffBallRatio` unchanged. -/
theorem hausdorffBallRatio_inter_ball_eq (d : ℝ) (ω : ℝ≥0∞) (M : Set E) (x : E) {r R : ℝ}
    (hrR : r ≤ R) :
    hausdorffBallRatio d ω (M ∩ Metric.ball x R) x r = hausdorffBallRatio d ω M x r := by
  unfold hausdorffBallRatio
  rw [inter_assoc, inter_eq_self_of_subset_right (Metric.ball_subset_ball hrR)]

/-- Localization of `HasHausdorffDensityAt` to any neighborhood `U ∈ 𝓝 x`. -/
theorem hasHausdorffDensityAt_inter_of_mem_nhds {d : ℝ} {ω : ℝ≥0∞} {M U : Set E} {x : E}
    (hU : U ∈ 𝓝 x) {θ : ℝ≥0∞} :
    HasHausdorffDensityAt d ω (M ∩ U) x θ ↔ HasHausdorffDensityAt d ω M x θ := by
  rcases Metric.mem_nhds_iff.mp hU with ⟨R, hR, hball⟩
  refine tendsto_congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hsub : Metric.ball x r ⊆ U := (Metric.ball_subset_ball hr.2.le).trans hball
  unfold hausdorffBallRatio
  rw [inter_assoc, inter_eq_self_of_subset_right hsub]

/-- Localization of `HasHausdorffDensityAt` to `M ∩ Metric.ball x R` for any `R > 0`. -/
theorem hasHausdorffDensityAt_inter_ball_iff {d : ℝ} {ω : ℝ≥0∞} {M : Set E} {x : E} {R : ℝ}
    (hR : 0 < R) {θ : ℝ≥0∞} :
    HasHausdorffDensityAt d ω (M ∩ Metric.ball x R) x θ ↔ HasHausdorffDensityAt d ω M x θ :=
  hasHausdorffDensityAt_inter_of_mem_nhds (Metric.ball_mem_nhds x hR)

/-- If `M ∩ Metric.ball x δ ⊆ {x}` for some `δ > 0` and `0 < d`, then `M` has `Hᵈ`-density zero at
`x`. -/
theorem hasHausdorffDensityZeroAt_of_inter_ball_subset_singleton {d : ℝ} (hd : 0 < d) (ω : ℝ≥0∞)
    {M : Set E} {x : E} {δ : ℝ} (hδ : 0 < δ) (hsub : M ∩ Metric.ball x δ ⊆ {x}) :
    HasHausdorffDensityZeroAt d ω M x := by
  rw [HasHausdorffDensityZeroAt, ← hasHausdorffDensityAt_inter_ball_iff hδ]
  exact (hasHausdorffDensityZeroAt_singleton hd ω x x).mono hsub

/-- If `x ∉ closure M`, then `M` has `Hᵈ`-density zero at `x`. -/
theorem hasHausdorffDensityZeroAt_of_notMem_closure {d : ℝ} {ω : ℝ≥0∞} {M : Set E} {x : E}
    (hx : x ∉ closure M) :
    HasHausdorffDensityZeroAt d ω M x := by
  have hcompl : M ∩ (closure M)ᶜ = ∅ :=
    disjoint_iff_inter_eq_empty.mp (disjoint_compl_right.mono_left subset_closure)
  rw [HasHausdorffDensityZeroAt,
    ← hasHausdorffDensityAt_inter_of_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hx), hcompl]
  exact hasHausdorffDensityZeroAt_empty d ω x

/-- **Invariance of `hausdorffBallRatio` under `Hᵈ`-null modifications**: if
`μH[d] (M ∆ M') = 0`, then `hausdorffBallRatio d ω M x r = hausdorffBallRatio d ω M' x r`. -/
theorem hausdorffBallRatio_congr_symmDiff_zero {d : ℝ} (ω : ℝ≥0∞) {M M' : Set E}
    (hnull : μH[d] (symmDiff M M') = 0) (x : E) (r : ℝ) :
    hausdorffBallRatio d ω M x r = hausdorffBallRatio d ω M' x r := by
  unfold hausdorffBallRatio
  congr 1
  refine measure_congr (ae_eq_set.mpr ⟨?_, ?_⟩)
  · exact measure_mono_null (fun y hy ↦ Or.inl ⟨hy.1.1, fun hy' ↦ hy.2 ⟨hy', hy.1.2⟩⟩) hnull
  · exact measure_mono_null (fun y hy ↦ Or.inr ⟨hy.1.1, fun hy' ↦ hy.2 ⟨hy', hy.1.2⟩⟩) hnull

/-- **Invariance of `HasHausdorffDensityAt` under `Hᵈ`-null modifications**: if
`μH[d] (M ∆ M') = 0`, then `HasHausdorffDensityAt d ω M x θ ↔ HasHausdorffDensityAt d ω M' x θ`. -/
theorem hasHausdorffDensityAt_congr_symmDiff_zero {d : ℝ} {ω : ℝ≥0∞} {M M' : Set E}
    (hnull : μH[d] (symmDiff M M') = 0) {x : E} {θ : ℝ≥0∞} :
    HasHausdorffDensityAt d ω M x θ ↔ HasHausdorffDensityAt d ω M' x θ := by
  have hfun : hausdorffBallRatio d ω M x = hausdorffBallRatio d ω M' x :=
    funext (hausdorffBallRatio_congr_symmDiff_zero ω hnull x)
  simp only [HasHausdorffDensityAt, hfun]

/-- If `M ∆ M' ⊆ N` where `N` has `Hᵈ`-density zero at `x`, then `HasHausdorffDensityAt d ω M x θ`
implies `HasHausdorffDensityAt d ω M' x θ`. -/
theorem HasHausdorffDensityAt.of_symmDiff_subset_densityZero {d : ℝ} {ω : ℝ≥0∞}
    {M M' N : Set E} {x : E} {θ : ℝ≥0∞} (hM : HasHausdorffDensityAt d ω M x θ)
    (hN : HasHausdorffDensityZeroAt d ω N x) (hsub : symmDiff M M' ⊆ N) :
    HasHausdorffDensityAt d ω M' x θ := by
  classical
  have hM'_le : ∀ r, hausdorffBallRatio d ω M' x r ≤
      hausdorffBallRatio d ω M x r + hausdorffBallRatio d ω N x r := fun r ↦
    (hausdorffBallRatio_mono_set
      (fun y hy ↦ if hyM : y ∈ M then Or.inl hyM else Or.inr (hsub (Or.inr ⟨hy, hyM⟩))) x r).trans
      (hausdorffBallRatio_union_le d ω M N x r)
  have hM_le : ∀ r, hausdorffBallRatio d ω M x r - hausdorffBallRatio d ω N x r ≤
      hausdorffBallRatio d ω M' x r := fun r ↦ tsub_le_iff_right.mpr <|
    (hausdorffBallRatio_mono_set
      (fun y hy ↦ if hyM' : y ∈ M' then Or.inl hyM' else Or.inr (hsub (Or.inl ⟨hy, hyM'⟩)))
      x r).trans (hausdorffBallRatio_union_le d ω M' N x r)
  have h_upper : Tendsto (fun r ↦ hausdorffBallRatio d ω M x r + hausdorffBallRatio d ω N x r)
      (𝓝[>] 0) (𝓝 θ) := by simpa using hM.add hN
  have h_lower : Tendsto (fun r ↦ hausdorffBallRatio d ω M x r - hausdorffBallRatio d ω N x r)
      (𝓝[>] 0) (𝓝 θ) := by simpa using ENNReal.Tendsto.sub hM hN (Or.inr ENNReal.zero_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_lower h_upper hM_le hM'_le

/-- **Density-zero symmetric difference stability**: if `HasHausdorffDensityZeroAt d ω N x` and
`M ∆ M' ⊆ N`, then `HasHausdorffDensityAt d ω M x θ ↔ HasHausdorffDensityAt d ω M' x θ`. -/
theorem hasHausdorffDensityAt_iff_of_symmDiff_subset_densityZero {d : ℝ} {ω : ℝ≥0∞}
    {M M' N : Set E} {x : E} {θ : ℝ≥0∞}
    (hN : HasHausdorffDensityZeroAt d ω N x) (hsub : symmDiff M M' ⊆ N) :
    HasHausdorffDensityAt d ω M x θ ↔ HasHausdorffDensityAt d ω M' x θ :=
  ⟨fun h ↦ h.of_symmDiff_subset_densityZero hN hsub,
   fun h ↦ h.of_symmDiff_subset_densityZero hN (by rwa [symmDiff_comm])⟩

end HausdorffDensityAndApproxTangent

section ApproxTangentSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A set `M ⊆ E` has approximate tangent subspace `T : Submodule ℝ E` at `x : E` (with dimension
`d` and normalization `ω`) if `M` has `Hᵈ`-density `1` at `x` and for every `ε > 0`, the exterior of
the `ε`-cone around `x + T` in `M`, `{y ∈ M | ε * dist y x ≤ Metric.infDist (y - x) T}`, has
`Hᵈ`-density `0` at `x`. -/
def HasApproxTangentSubspaceAt (d : ℝ) (ω : ℝ≥0∞) (M : Set E) (T : Submodule ℝ E) (x : E) : Prop :=
  HasHausdorffDensityOneAt d ω M x ∧
    ∀ ε : ℝ, 0 < ε →
      HasHausdorffDensityZeroAt d ω {y ∈ M | ε * dist y x ≤ Metric.infDist (y - x) T} x

/-- If `HasApproxTangentSubspaceAt d ω M T x`, then `M` has `Hᵈ`-density `1` at `x`. -/
theorem HasApproxTangentSubspaceAt.hasHausdorffDensityOneAt {d : ℝ} {ω : ℝ≥0∞} {M : Set E}
    {T : Submodule ℝ E} {x : E} (h : HasApproxTangentSubspaceAt d ω M T x) :
    HasHausdorffDensityOneAt d ω M x := h.1

/-- If `HasApproxTangentSubspaceAt d ω M T x`, then for every `ε > 0` the exterior of the `ε`-cone
around `x + T` in `M` has `Hᵈ`-density `0` at `x`. -/
theorem HasApproxTangentSubspaceAt.cone_densityZero {d : ℝ} {ω : ℝ≥0∞} {M : Set E}
    {T : Submodule ℝ E} {x : E} (h : HasApproxTangentSubspaceAt d ω M T x) {ε : ℝ} (hε : 0 < ε) :
    HasHausdorffDensityZeroAt d ω {y ∈ M | ε * dist y x ≤ Metric.infDist (y - x) T} x := h.2 ε hε

/-- **Invariance of `HasApproxTangentSubspaceAt` under difference-null modifications**: if
`HasHausdorffDensityZeroAt d ω N x` and `M ∆ M' ⊆ N`, then
`HasApproxTangentSubspaceAt d ω M T x ↔ HasApproxTangentSubspaceAt d ω M' T x`. -/
theorem HasApproxTangentSubspaceAt.congr_symmDiff_densityZero {d : ℝ} {ω : ℝ≥0∞}
    {M M' N : Set E} {T : Submodule ℝ E} {x : E}
    (hN : HasHausdorffDensityZeroAt d ω N x) (hsub : symmDiff M M' ⊆ N) :
    HasApproxTangentSubspaceAt d ω M T x ↔ HasApproxTangentSubspaceAt d ω M' T x := by
  refine and_congr (hasHausdorffDensityAt_iff_of_symmDiff_subset_densityZero hN hsub)
    (forall₂_congr fun ε _ ↦ hasHausdorffDensityAt_iff_of_symmDiff_subset_densityZero hN ?_)
  rintro y (⟨⟨hyM, hcone⟩, hyM'⟩ | ⟨⟨hyM', hcone⟩, hyM⟩)
  · exact hsub (Or.inl ⟨hyM, fun h ↦ hyM' ⟨h, hcone⟩⟩)
  · exact hsub (Or.inr ⟨hyM', fun h ↦ hyM ⟨h, hcone⟩⟩)

/-- **Invariance of `HasApproxTangentSubspaceAt` under `Hᵈ`-null modifications**: if
`μH[d] (M ∆ M') = 0`, then
`HasApproxTangentSubspaceAt d ω M T x ↔ HasApproxTangentSubspaceAt d ω M' T x`. -/
theorem HasApproxTangentSubspaceAt.congr_symmDiff_zero {d : ℝ} {ω : ℝ≥0∞} {M M' : Set E}
    {T : Submodule ℝ E} {x : E} (hnull : μH[d] (symmDiff M M') = 0) :
    HasApproxTangentSubspaceAt d ω M T x ↔ HasApproxTangentSubspaceAt d ω M' T x :=
  HasApproxTangentSubspaceAt.congr_symmDiff_densityZero
    (hasHausdorffDensityZeroAt_of_measure_zero hnull x) Subset.rfl

/-- Localization of `HasApproxTangentSubspaceAt` to any neighborhood `U ∈ 𝓝 x`. -/
theorem HasApproxTangentSubspaceAt.localize_nhds {d : ℝ} {ω : ℝ≥0∞} {M U : Set E}
    {T : Submodule ℝ E} {x : E} (hU : U ∈ 𝓝 x) :
    HasApproxTangentSubspaceAt d ω (M ∩ U) T x ↔ HasApproxTangentSubspaceAt d ω M T x := by
  refine and_congr (hasHausdorffDensityAt_inter_of_mem_nhds hU) (forall₂_congr fun ε _ ↦ ?_)
  have hset : {y ∈ M ∩ U | ε * dist y x ≤ Metric.infDist (y - x) T} =
      {y ∈ M | ε * dist y x ≤ Metric.infDist (y - x) T} ∩ U :=
    Set.ext fun y ↦ ⟨fun ⟨⟨hyM, hyU⟩, hc⟩ ↦ ⟨⟨hyM, hc⟩, hyU⟩,
      fun ⟨⟨hyM, hc⟩, hyU⟩ ↦ ⟨⟨hyM, hyU⟩, hc⟩⟩
  rw [hset, HasHausdorffDensityZeroAt, hasHausdorffDensityAt_inter_of_mem_nhds hU,
    ← HasHausdorffDensityZeroAt]

/-- Localization of `HasApproxTangentSubspaceAt` to `M ∩ Metric.ball x R` for any `R > 0`. -/
theorem HasApproxTangentSubspaceAt.localize_ball {d : ℝ} {ω : ℝ≥0∞} {M : Set E}
    {T : Submodule ℝ E} {x : E} {R : ℝ} (hR : 0 < R) :
    HasApproxTangentSubspaceAt d ω (M ∩ Metric.ball x R) T x ↔
      HasApproxTangentSubspaceAt d ω M T x :=
  HasApproxTangentSubspaceAt.localize_nhds (Metric.ball_mem_nhds x hR)

omit [MeasurableSpace E] [BorelSpace E] in
/-- For any point `y ∈ x +ᵥ (T : Set E)` in the affine subspace `x + T`, `infDist (y - x) T = 0`. -/
theorem infDist_sub_eq_zero_of_mem_vadd_submodule {T : Submodule ℝ E} {x y : E}
    (hy : y ∈ x +ᵥ (T : Set E)) : Metric.infDist (y - x) (T : Set E) = 0 := by
  rcases hy with ⟨v, hv, rfl⟩
  dsimp only; rw [vadd_eq_add, add_sub_cancel_left]; exact Metric.infDist_zero_of_mem hv

omit [MeasurableSpace E] [BorelSpace E] in
/-- For any `ε > 0`, the exterior of the `ε`-cone of `x +ᵥ (T : Set E)` around `T` at `x` is
contained in `{x}`. -/
theorem cone_vadd_submodule_subset_singleton (T : Submodule ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) :
    {y ∈ x +ᵥ (T : Set E) | ε * dist y x ≤ Metric.infDist (y - x) T} ⊆ {x} := by
  rintro y ⟨hyT, hle⟩
  rw [mem_singleton_iff]
  by_contra hne
  rw [infDist_sub_eq_zero_of_mem_vadd_submodule hyT] at hle
  exact absurd (le_antisymm hle (mul_nonneg hε.le dist_nonneg))
    (mul_ne_zero hε.ne' (dist_ne_zero.mpr hne))

/-- For `0 < d` and `0 < ε`, the exterior of the `ε`-cone of `x +ᵥ (T : Set E)` around `T` at `x`
has `Hᵈ`-density zero at `x`. -/
theorem hasHausdorffDensityZeroAt_cone_vadd_submodule {d : ℝ} (hd : 0 < d) (ω : ℝ≥0∞)
    (T : Submodule ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) :
    HasHausdorffDensityZeroAt d ω
      {y ∈ x +ᵥ (T : Set E) | ε * dist y x ≤ Metric.infDist (y - x) T} x :=
  (hasHausdorffDensityZeroAt_singleton hd ω x x).mono (cone_vadd_submodule_subset_singleton T x hε)

/-- For `0 < d`, an affine subspace `x +ᵥ (T : Set E)` has approximate tangent subspace `T` at `x`
if and only if it has `Hᵈ`-density `1` at `x`. -/
theorem hasApproxTangentSubspaceAt_vadd_submodule_iff {d : ℝ} (hd : 0 < d) (ω : ℝ≥0∞)
    (T : Submodule ℝ E) (x : E) :
    HasApproxTangentSubspaceAt d ω (x +ᵥ (T : Set E)) T x ↔
      HasHausdorffDensityOneAt d ω (x +ᵥ (T : Set E)) x :=
  ⟨HasApproxTangentSubspaceAt.hasHausdorffDensityOneAt,
   fun h ↦ ⟨h, fun _ hε ↦ hasHausdorffDensityZeroAt_cone_vadd_submodule hd ω T x hε⟩⟩

end ApproxTangentSubspace

/-! ### Section 2: Tangential differentiation, chart independence, and `C¹` graph tangent spaces -/

section TangentialFDerivAndGraphs

variable {E F G H V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The tangential Fréchet derivative of `f : E → F` along a subspace `T : Submodule ℝ E` at
`x : E`, defined as the restriction `(fderiv ℝ f x).comp T.subtypeL : T →L[ℝ] F`. -/
def tangentialFDeriv (T : Submodule ℝ E) (f : E → F) (x : E) : T →L[ℝ] F :=
  (fderiv ℝ f x).comp T.subtypeL

@[simp]
theorem tangentialFDeriv_apply (T : Submodule ℝ E) (f : E → F) (x : E) (v : T) :
    tangentialFDeriv T f x v = fderiv ℝ f x v := rfl

/-- Operator norm bound `‖tangentialFDeriv T f x‖ ≤ ‖fderiv ℝ f x‖`. -/
theorem norm_tangentialFDeriv_le (T : Submodule ℝ E) (f : E → F) (x : E) :
    ‖tangentialFDeriv T f x‖ ≤ ‖fderiv ℝ f x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ (fderiv ℝ f x).le_opNorm (v : E)

/-- Extended operator norm bound `‖tangentialFDeriv T f x‖ₑ ≤ ‖fderiv ℝ f x‖ₑ`. -/
theorem enorm_tangentialFDeriv_le (T : Submodule ℝ E) (f : E → F) (x : E) :
    ‖tangentialFDeriv T f x‖ₑ ≤ ‖fderiv ℝ f x‖ₑ := by
  simp only [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (norm_tangentialFDeriv_le T f x)

@[simp]
theorem tangentialFDeriv_id (T : Submodule ℝ E) (x : E) :
    tangentialFDeriv T (id : E → E) x = T.subtypeL := by ext v; simp [tangentialFDeriv]

@[simp]
theorem tangentialFDeriv_const (T : Submodule ℝ E) (c : F) (x : E) :
    tangentialFDeriv T (fun _ : E ↦ c) x = 0 := by ext v; simp [tangentialFDeriv]

theorem tangentialFDeriv_add (T : Submodule ℝ E) {f g : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    tangentialFDeriv T (f + g) x = tangentialFDeriv T f x + tangentialFDeriv T g x := by
  unfold tangentialFDeriv; rw [fderiv_add hf hg, ContinuousLinearMap.add_comp]

theorem tangentialFDeriv_smul (T : Submodule ℝ E) (c : ℝ) {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    tangentialFDeriv T (c • f) x = c • tangentialFDeriv T f x := by
  unfold tangentialFDeriv; rw [fderiv_const_smul hf c, ContinuousLinearMap.smul_comp]

/-- **Tangential chain rule (ambient codomain)**: for `f : E → F` differentiable at `x` and
`g : F → G` differentiable at `f x`,
`tangentialFDeriv T (g ∘ f) x = (fderiv ℝ g (f x)).comp (tangentialFDeriv T f x)`. -/
theorem tangentialFDeriv_comp_right (T : Submodule ℝ E) {f : E → F} {g : F → G} {x : E}
    (hg : DifferentiableAt ℝ g (f x)) (hf : DifferentiableAt ℝ f x) :
    tangentialFDeriv T (g ∘ f) x = (fderiv ℝ g (f x)).comp (tangentialFDeriv T f x) := by
  ext v; simp [tangentialFDeriv, fderiv_comp x hg hf]

/-- **Tangential chain rule (subspace-to-subspace)**: if `f : E → F` is differentiable at `x`,
`g : F → G` is differentiable at `f x`, and `tangentialFDeriv T f x` maps `T` into `S`, then
`tangentialFDeriv T (g ∘ f) x v = tangentialFDeriv S g (f x) ⟨tangentialFDeriv T f x v, hTS v⟩`. -/
theorem tangentialFDeriv_comp (T : Submodule ℝ E) (S : Submodule ℝ F) {f : E → F} {g : F → G}
    {x : E} (hg : DifferentiableAt ℝ g (f x)) (hf : DifferentiableAt ℝ f x)
    (hTS : ∀ v : T, tangentialFDeriv T f x v ∈ S) (v : T) :
    tangentialFDeriv T (g ∘ f) x v =
      tangentialFDeriv S g (f x) ⟨tangentialFDeriv T f x v, hTS v⟩ := by
  simp [tangentialFDeriv_comp_right T hg hf]

/-- **Lipschitz tangential derivative norm bound**: if `LipschitzWith K f`, then
`‖tangentialFDeriv T f x‖ ≤ K`. -/
theorem norm_tangentialFDeriv_le_of_lipschitzWith (T : Submodule ℝ E) {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : E) : ‖tangentialFDeriv T f x‖ ≤ K :=
  (norm_tangentialFDeriv_le T f x).trans (norm_fderiv_le_of_lipschitz ℝ hf)

/-- **Lipschitz tangential derivative extended norm bound**: if `LipschitzWith K f`, then
`‖tangentialFDeriv T f x‖ₑ ≤ K`. -/
theorem enorm_tangentialFDeriv_le_of_lipschitzWith (T : Submodule ℝ E) {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : E) : ‖tangentialFDeriv T f x‖ₑ ≤ K := by
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (norm_tangentialFDeriv_le_of_lipschitzWith T hf x)

/-- **Chart parametrization compatibility**: if `Φ : H → E` is differentiable at `u` with
`∀ v, fderiv ℝ Φ u v ∈ T` and `f : E → F` is differentiable at `Φ u`, then
`fderiv ℝ (f ∘ Φ) u v = tangentialFDeriv T f (Φ u) ⟨fderiv ℝ Φ u v, hΦT v⟩`. -/
theorem fderiv_comp_chart_eq_tangentialFDeriv (T : Submodule ℝ E) {Φ : H → E} {f : E → F}
    {u : H} (hf : DifferentiableAt ℝ f (Φ u)) (hΦ : DifferentiableAt ℝ Φ u)
    (hΦT : ∀ v : H, fderiv ℝ Φ u v ∈ T) (v : H) :
    fderiv ℝ (f ∘ Φ) u v = tangentialFDeriv T f (Φ u) ⟨fderiv ℝ Φ u v, hΦT v⟩ := by
  rw [fderiv_comp u hf hΦ, ContinuousLinearMap.comp_apply, tangentialFDeriv_apply]

/-- **Chart independence and extension invariance of `tangentialFDeriv`**: if `Φ : H → E` is
differentiable at `u` with `LinearMap.range (fderiv ℝ Φ u).toLinearMap = T`, and `f₁, f₂ : E → F`
are differentiable at `Φ u` and satisfy `f₁ ∘ Φ =ᶠ[𝓝 u] f₂ ∘ Φ`, then
`tangentialFDeriv T f₁ (Φ u) = tangentialFDeriv T f₂ (Φ u)`. -/
theorem tangentialFDeriv_congr_of_chart_range (T : Submodule ℝ E) {Φ : H → E} {f₁ f₂ : E → F}
    {u : H} (hΦ : DifferentiableAt ℝ Φ u) (hrange : LinearMap.range (fderiv ℝ Φ u).toLinearMap = T)
    (hf₁ : DifferentiableAt ℝ f₁ (Φ u)) (hf₂ : DifferentiableAt ℝ f₂ (Φ u))
    (heq : f₁ ∘ Φ =ᶠ[𝓝 u] f₂ ∘ Φ) :
    tangentialFDeriv T f₁ (Φ u) = tangentialFDeriv T f₂ (Φ u) := by
  ext ⟨w, hw⟩
  rw [← hrange, LinearMap.mem_range, ContinuousLinearMap.coe_coe] at hw
  rcases hw with ⟨v, rfl⟩
  have hΦT : ∀ z : H, fderiv ℝ Φ u z ∈ T := fun z ↦ by
    rw [← hrange]; exact LinearMap.mem_range_self _ z
  rw [← fderiv_comp_chart_eq_tangentialFDeriv T hf₁ hΦ hΦT v,
    ← fderiv_comp_chart_eq_tangentialFDeriv T hf₂ hΦ hΦT v, heq.fderiv_eq]

/-- The graph map `u ↦ (u, g u)` of a function `g : H → V`. -/
def graphMap (g : H → V) (u : H) : H × V := (u, g u)

omit [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℝ V] in
@[simp]
theorem graphMap_apply (g : H → V) (u : H) : graphMap g u = (u, g u) := rfl

/-- The continuous linear parametrization `v ↦ (v, fderiv ℝ g u v)` of the tangent space to the
graph of `g : H → V` at `(u, g u)`. -/
def graphTangentLinearMap (g : H → V) (u : H) : H →L[ℝ] H × V :=
  (ContinuousLinearMap.id ℝ H).prod (fderiv ℝ g u)

@[simp]
theorem graphTangentLinearMap_apply (g : H → V) (u v : H) :
    graphTangentLinearMap g u v = (v, fderiv ℝ g u v) := rfl

/-- The classical tangent subspace to the graph of `g : H → V` at `(u, g u)`, defined as the range
of `graphTangentLinearMap g u : H →L[ℝ] H × V`. -/
def graphTangentSubspace (g : H → V) (u : H) : Submodule ℝ (H × V) :=
  LinearMap.range (graphTangentLinearMap g u).toLinearMap

/-- First-coordinate projection is a left inverse to `graphTangentLinearMap g u`. -/
@[simp]
theorem fst_comp_graphTangentLinearMap (g : H → V) (u : H) :
    (ContinuousLinearMap.fst ℝ H V).comp (graphTangentLinearMap g u) =
      ContinuousLinearMap.id ℝ H := by ext v; rfl

/-- `graphTangentLinearMap g u` is always injective. -/
theorem graphTangentLinearMap_injective (g : H → V) (u : H) :
    Function.Injective (graphTangentLinearMap g u) :=
  Function.LeftInverse.injective (g := ContinuousLinearMap.fst ℝ H V) fun _ ↦ rfl

/-- If `g : H → V` is differentiable at `u`, then `graphMap g` has Fréchet derivative
`graphTangentLinearMap g u` at `u`. -/
theorem hasFDerivAt_graphMap {g : H → V} {u : H} (hg : DifferentiableAt ℝ g u) :
    HasFDerivAt (graphMap g) (graphTangentLinearMap g u) u :=
  (hasFDerivAt_id u).prodMk hg.hasFDerivAt

/-- If `g : H → V` is differentiable at `u`, then `graphMap g` is differentiable at `u`. -/
theorem differentiableAt_graphMap {g : H → V} {u : H} (hg : DifferentiableAt ℝ g u) :
    DifferentiableAt ℝ (graphMap g) u := (hasFDerivAt_graphMap hg).differentiableAt

/-- Fréchet derivative of `graphMap g` at `u` when `g` is differentiable at `u`. -/
theorem fderiv_graphMap {g : H → V} {u : H} (hg : DifferentiableAt ℝ g u) :
    fderiv ℝ (graphMap g) u = graphTangentLinearMap g u := (hasFDerivAt_graphMap hg).fderiv

/-- Characterization of membership in `graphTangentSubspace g u`:
`(v, w) ∈ graphTangentSubspace g u` if and only if `w = fderiv ℝ g u v`. -/
theorem mem_graphTangentSubspace_iff (g : H → V) (u : H) (p : H × V) :
    p ∈ graphTangentSubspace g u ↔ p.2 = fderiv ℝ g u p.1 := by
  simp only [graphTangentSubspace, LinearMap.mem_range, ContinuousLinearMap.coe_coe,
    graphTangentLinearMap, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    Prod.ext_iff]
  exact ⟨fun ⟨_, rfl, h2⟩ ↦ h2.symm, fun h ↦ ⟨p.1, rfl, h.symm⟩⟩

/-- For `g : H → V` differentiable at `u` and `f : H × V → F` differentiable at `graphMap g u`,
the derivative of `f ∘ graphMap g` at `u` factors through
`tangentialFDeriv (graphTangentSubspace g u) f (graphMap g u)`. -/
theorem fderiv_comp_graphMap_apply {g : H → V} {f : H × V → F} {u : H}
    (hf : DifferentiableAt ℝ f (graphMap g u)) (hg : DifferentiableAt ℝ g u) (v : H) :
    fderiv ℝ (f ∘ graphMap g) u v =
      tangentialFDeriv (graphTangentSubspace g u) f (graphMap g u)
        ⟨graphTangentLinearMap g u v, LinearMap.mem_range_self _ v⟩ := by
  have hmem : ∀ z : H, fderiv ℝ (graphMap g) u z ∈ graphTangentSubspace g u := fun z ↦ by
    rw [fderiv_graphMap hg]; exact LinearMap.mem_range_self _ z
  simpa [fderiv_graphMap hg] using fderiv_comp_chart_eq_tangentialFDeriv
    (graphTangentSubspace g u) hf (differentiableAt_graphMap hg) hmem v

/-- If two differentiable functions `f₁, f₂ : H × V → F` agree on the graph `range (graphMap g)`,
then their tangential derivatives along `graphTangentSubspace g u` at `graphMap g u` coincide. -/
theorem tangentialFDeriv_graphTangentSubspace_congr_of_eqOn_graph {g : H → V}
    {f₁ f₂ : H × V → F} {u : H} (hg : DifferentiableAt ℝ g u)
    (hf₁ : DifferentiableAt ℝ f₁ (graphMap g u)) (hf₂ : DifferentiableAt ℝ f₂ (graphMap g u))
    (heq : EqOn f₁ f₂ (range (graphMap g))) :
    tangentialFDeriv (graphTangentSubspace g u) f₁ (graphMap g u) =
      tangentialFDeriv (graphTangentSubspace g u) f₂ (graphMap g u) := by
  refine tangentialFDeriv_congr_of_chart_range (graphTangentSubspace g u)
    (differentiableAt_graphMap hg) (by rw [fderiv_graphMap hg, graphTangentSubspace]) hf₁ hf₂
    (Eventually.of_forall fun x ↦ heq (mem_range_self x))

/-- Upper bound for the distance from `graphMap g x - graphMap g u` to `graphTangentSubspace g u`
by the first-order Taylor remainder `‖g x - g u - fderiv ℝ g u (x - u)‖`. -/
theorem infDist_graphMap_sub_le (g : H → V) (u x : H) :
    Metric.infDist (graphMap g x - graphMap g u) (graphTangentSubspace g u) ≤
      ‖g x - g u - fderiv ℝ g u (x - u)‖ := by
  have hz : (x - u, fderiv ℝ g u (x - u)) ∈ (graphTangentSubspace g u : Set (H × V)) := by
    rw [SetLike.mem_coe, mem_graphTangentSubspace_iff]
  refine (Metric.infDist_le_dist_of_mem hz).trans ?_
  rw [dist_eq_norm]
  have hsub : graphMap g x - graphMap g u - (x - u, fderiv ℝ g u (x - u)) =
      (0, g x - g u - fderiv ℝ g u (x - u)) := by ext <;> simp [graphMap]
  rw [hsub, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]

/-- If `g : H → V` is differentiable at `u`, then for every `ε > 0` there is `δ > 0` such that the
exterior of the `ε`-cone of `range (graphMap g)` around `graphTangentSubspace g u` at `graphMap g u`
intersects `Metric.ball (graphMap g u) δ` only inside `{graphMap g u}`. -/
theorem graphMap_cone_subset_singleton_eventually {g : H → V} {u : H}
    (hg : DifferentiableAt ℝ g u) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, {y ∈ range (graphMap g) | ε * dist y (graphMap g u) ≤
        Metric.infDist (y - graphMap g u) (graphTangentSubspace g u)} ∩
      Metric.ball (graphMap g u) δ ⊆ {graphMap g u} := by
  rcases Metric.mem_nhds_iff.mp (hg.hasFDerivAt.isLittleO.bound (half_pos hε)) with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, fun y ⟨⟨⟨x, hxy⟩, hcone⟩, hyball⟩ ↦ ?_⟩
  subst hxy; rw [mem_singleton_iff]; by_contra hne
  have hxball : x ∈ Metric.ball u δ := by
    rw [Metric.mem_ball] at hyball ⊢; exact (le_max_left _ _).trans_lt hyball
  have hdist_le : ‖x - u‖ ≤ dist (graphMap g x) (graphMap g u) := by
    simp only [graphMap, dist_eq_norm]; exact le_max_left _ _
  have h1 : ε * dist (graphMap g x) (graphMap g u) ≤
      (ε / 2) * dist (graphMap g x) (graphMap g u) :=
    (hcone.trans (infDist_graphMap_sub_le g u x)).trans
      ((hball hxball).trans (mul_le_mul_of_nonneg_left hdist_le (half_pos hε).le))
  linarith [mul_lt_mul_of_pos_right (half_lt_self hε) (dist_pos.mpr hne)]

/-- **Cone condition for differentiable graphs**: if `g : H → V` is differentiable at `u` and
`0 < d`, then for every `ε > 0`, the exterior of the `ε`-cone of `range (graphMap g)` around
`graphTangentSubspace g u` at `graphMap g u` has `Hᵈ`-density zero at `graphMap g u`. -/
theorem hasHausdorffDensityZeroAt_cone_graphMap [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopologyEither H V]
    {d : ℝ} (hd : 0 < d) (ω : ℝ≥0∞) {g : H → V} {u : H} (hg : DifferentiableAt ℝ g u)
    {ε : ℝ} (hε : 0 < ε) :
    HasHausdorffDensityZeroAt d ω
      {y ∈ range (graphMap g) |
        ε * dist y (graphMap g u) ≤
          Metric.infDist (y - graphMap g u) (graphTangentSubspace g u)}
      (graphMap g u) := by
  rcases graphMap_cone_subset_singleton_eventually hg hε with ⟨δ, hδ, hsub⟩
  exact hasHausdorffDensityZeroAt_of_inter_ball_subset_singleton hd ω hδ hsub

/-- **Agreement of approximate tangent subspaces with classical tangent spaces on differentiable
graphs**: for `0 < d` and `g : H → V` differentiable at `u`, the graph `range (graphMap g)` has
approximate tangent subspace `graphTangentSubspace g u` at `graphMap g u` if and only if it has
`Hᵈ`-density `1` at `graphMap g u`. -/
theorem hasApproxTangentSubspaceAt_graphMap_iff [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopologyEither H V]
    {d : ℝ} (hd : 0 < d) (ω : ℝ≥0∞) {g : H → V} {u : H} (hg : DifferentiableAt ℝ g u) :
    HasApproxTangentSubspaceAt d ω (range (graphMap g)) (graphTangentSubspace g u) (graphMap g u) ↔
      HasHausdorffDensityOneAt d ω (range (graphMap g)) (graphMap g u) :=
  ⟨HasApproxTangentSubspaceAt.hasHausdorffDensityOneAt,
   fun h ↦ ⟨h, fun _ hε ↦ hasHausdorffDensityZeroAt_cone_graphMap hd ω hg hε⟩⟩

end TangentialFDerivAndGraphs

/-! ### Section 3: Tangential area formula on countably rectifiable sets and null-set invariance -/

section RectifiableAreaFormula

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Outside `f '' (M ∆ A)`, the fibers of `M` and `A` over `y` coincide. -/
theorem inter_preimage_singleton_eq_of_notMem_image_symmDiff {f : X → Y} {M A : Set X} {y : Y}
    (hy : y ∉ f '' symmDiff M A) : M ∩ f ⁻¹' {y} = A ∩ f ⁻¹' {y} := by
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
  refine ⟨fun ⟨hxM, hfx⟩ ↦ ⟨?_, hfx⟩, fun ⟨hxA, hfx⟩ ↦ ⟨?_, hfx⟩⟩
  · by_contra hxA; exact hy ⟨x, Or.inl ⟨hxM, hxA⟩, hfx⟩
  · by_contra hxM; exact hy ⟨x, Or.inr ⟨hxA, hxM⟩, hfx⟩

omit [MeasurableSpace Y] in
/-- Outside `f '' (M ∆ A)`, `weightedFiberSum f M g y = weightedFiberSum f A g y`. -/
theorem weightedFiberSum_eq_of_notMem_image_symmDiff {f : X → Y} {M A : Set X} (g : X → ℝ≥0∞)
    {y : Y} (hy : y ∉ f '' symmDiff M A) :
    weightedFiberSum f M g y = weightedFiberSum f A g y := by
  unfold weightedFiberSum; rw [inter_preimage_singleton_eq_of_notMem_image_symmDiff hy]

/-- If `M ∆ A ⊆ N` and `μY (f '' N) = 0`, then
`weightedFiberSum f M g =ᵐ[μY] weightedFiberSum f A g`. -/
theorem weightedFiberSum_ae_eq_of_symmDiff_subset_null {μY : Measure Y} {f : X → Y}
    {M A N : Set X} (hsub : symmDiff M A ⊆ N) (hN : μY (f '' N) = 0) (g : X → ℝ≥0∞) :
    weightedFiberSum f M g =ᵐ[μY] weightedFiberSum f A g := by
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun y hy ↦ ?_) (measure_mono_null (image_mono hsub) hN)
  by_contra hnot; exact hy (weightedFiberSum_eq_of_notMem_image_symmDiff g hnot)

/-- If `M ∆ A ⊆ N` and `μY (f '' N) = 0`, then the Lebesgue integrals of `weightedFiberSum f M g`
and `weightedFiberSum f A g` with respect to `μY` are equal. -/
theorem lintegral_weightedFiberSum_congr_of_symmDiff_subset_null {μY : Measure Y} {f : X → Y}
    {M A N : Set X} (hsub : symmDiff M A ⊆ N) (hN : μY (f '' N) = 0) (g : X → ℝ≥0∞) :
    ∫⁻ y, weightedFiberSum f M g y ∂μY = ∫⁻ y, weightedFiberSum f A g y ∂μY :=
  lintegral_congr_ae (weightedFiberSum_ae_eq_of_symmDiff_subset_null hsub hN g)

omit [MeasurableSpace Y] in
/-- If `M ∆ A ⊆ N` and `μX N = 0`, then `∫⁻ x in M, h x ∂μX = ∫⁻ x in A, h x ∂μX`. -/
theorem setLIntegral_congr_of_symmDiff_subset_null {μX : Measure X} {M A N : Set X}
    (hsub : symmDiff M A ⊆ N) (hN : μX N = 0) (h : X → ℝ≥0∞) :
    ∫⁻ x in M, h x ∂μX = ∫⁻ x in A, h x ∂μX := by
  have hae : M =ᵐ[μX] A :=
    ae_eq_set.mpr ⟨measure_mono_null (fun x hx ↦ hsub (Or.inl hx)) hN,
      measure_mono_null (fun x hx ↦ hsub (Or.inr hx)) hN⟩
  rw [Measure.restrict_congr_set hae]

/-- **Null-modification invariance of `AreaFormulaHolds`**: if `AreaFormulaHolds μX μY f J A` holds
and `M ∆ A ⊆ N` where `μX N = 0` and `μY (f '' N) = 0`, then `AreaFormulaHolds μX μY f J M`
holds. -/
theorem AreaFormulaHolds.congr_symmDiff_subset_null {μX : Measure X} {μY : Measure Y}
    {f : X → Y} {J : X → ℝ≥0∞} {A M N : Set X} (h : AreaFormulaHolds μX μY f J A)
    (hsub : symmDiff M A ⊆ N) (hNX : μX N = 0) (hNY : μY (f '' N) = 0) :
    AreaFormulaHolds μX μY f J M := fun g hg ↦ by
  rw [setLIntegral_congr_of_symmDiff_subset_null hsub hNX, h hg,
    lintegral_weightedFiberSum_congr_of_symmDiff_subset_null hsub hNY]

variable [EMetricSpace X] [BorelSpace X] [EMetricSpace Y] [BorelSpace Y]

/-- Any `LipschitzOnWith K` map preserves `d`-dimensional Hausdorff measure zero (`0 ≤ d`). -/
theorem _root_.LipschitzOnWith.hausdorffMeasure_image_eq_zero {K : ℝ≥0} {f : X → Y} {N : Set X}
    (hf : LipschitzOnWith K f N) {d : ℝ} (hd : 0 ≤ d) (hN : μH[d] N = 0) : μH[d] (f '' N) = 0 :=
  nonpos_iff_eq_zero.mp ((hf.hausdorffMeasure_image_le hd).trans (by simp [hN]))

/-- Any `LipschitzWith K` map preserves `d`-dimensional Hausdorff measure zero (`0 ≤ d`). -/
theorem _root_.LipschitzWith.hausdorffMeasure_image_eq_zero {K : ℝ≥0} {f : X → Y}
    (hf : LipschitzWith K f) {d : ℝ} (hd : 0 ≤ d) {N : Set X} (hN : μH[d] N = 0) :
    μH[d] (f '' N) = 0 := hf.lipschitzOnWith.hausdorffMeasure_image_eq_zero hd hN

/-- **Hausdorff-null modification invariance of `AreaFormulaHolds` for Lipschitz maps**: if
`AreaFormulaHolds μH[d] μH[d] f J A` holds, `0 ≤ d`, `LipschitzOnWith K f N`, `M ∆ A ⊆ N`, and
`μH[d] N = 0`, then `AreaFormulaHolds μH[d] μH[d] f J M` holds. -/
theorem AreaFormulaHolds.congr_symmDiff_subset_hausdorffMeasure_zero {d : ℝ} (hd : 0 ≤ d)
    {K : ℝ≥0} {f : X → Y} {J : X → ℝ≥0∞} {A M N : Set X} (h : AreaFormulaHolds μH[d] μH[d] f J A)
    (hf : LipschitzOnWith K f N) (hsub : symmDiff M A ⊆ N) (hN : μH[d] N = 0) :
    AreaFormulaHolds μH[d] μH[d] f J M :=
  h.congr_symmDiff_subset_null hsub hN (hf.hausdorffMeasure_image_eq_zero hd hN)

/-- **Hausdorff-null symmetric difference invariance of `AreaFormulaHolds`**: if
`AreaFormulaHolds μH[d] μH[d] f J A` holds, `0 ≤ d`, `LipschitzWith K f`, and
`μH[d] (M ∆ A) = 0`, then `AreaFormulaHolds μH[d] μH[d] f J M` holds. -/
theorem AreaFormulaHolds.congr_symmDiff_hausdorffMeasure_zero {d : ℝ} (hd : 0 ≤ d) {K : ℝ≥0}
    {f : X → Y} {J : X → ℝ≥0∞} {A M : Set X} (h : AreaFormulaHolds μH[d] μH[d] f J A)
    (hf : LipschitzWith K f) (hnull : μH[d] (symmDiff M A) = 0) :
    AreaFormulaHolds μH[d] μH[d] f J M :=
  h.congr_symmDiff_subset_hausdorffMeasure_zero hd hf.lipschitzOnWith Subset.rfl hnull

/-- **Rectifiable decomposition theorem for the tangential area formula**: if `A : ι → Set X` is a
countable pairwise disjoint family of measurable sets on each of which
`AreaFormulaHolds μH[d] μH[d] f J (A i)` holds with a.e.-measurable fiber sums, and
`M ∆ (⋃ i, A i) ⊆ N` with `μH[d] N = 0` and `LipschitzOnWith K f N` (`0 ≤ d`), then
`AreaFormulaHolds μH[d] μH[d] f J M` holds on all of `M`. -/
theorem AreaFormulaHolds.of_rectifiable_decomposition {ι : Type*} [Countable ι] {d : ℝ}
    (hd : 0 ≤ d) {K : ℝ≥0} {f : X → Y} {J : X → ℝ≥0∞} {A : ι → Set X} {M N : Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (h : ∀ i, AreaFormulaHolds μH[d] μH[d] f J (A i))
    (hmeas : ∀ i ⦃g : X → ℝ≥0∞⦄, Measurable g →
      AEMeasurable (weightedFiberSum f (A i) g) (μH[d] : Measure Y))
    (hf : LipschitzOnWith K f N) (hsub : symmDiff M (⋃ i, A i) ⊆ N) (hN : μH[d] N = 0) :
    AreaFormulaHolds μH[d] μH[d] f J M :=
  (AreaFormulaHolds.iUnion_disjoint hA hdisj h hmeas).congr_symmDiff_subset_hausdorffMeasure_zero
    hd hf hsub hN

/-- **Tangential area formula on `N ∪ ⋃ i, A i`**: if `A : ι → Set X` are pairwise disjoint
measurable sets satisfying `AreaFormulaHolds μH[d] μH[d] f J (A i)` with a.e.-measurable fiber
sums, `μH[d] N = 0`, `0 ≤ d`, and `LipschitzWith K f`, then
`AreaFormulaHolds μH[d] μH[d] f J (N ∪ ⋃ i, A i)` holds. -/
theorem AreaFormulaHolds.of_eq_null_union_iUnion {ι : Type*} [Countable ι] {d : ℝ} (hd : 0 ≤ d)
    {K : ℝ≥0} {f : X → Y} {J : X → ℝ≥0∞} {A : ι → Set X} {N : Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (h : ∀ i, AreaFormulaHolds μH[d] μH[d] f J (A i))
    (hmeas : ∀ i ⦃g : X → ℝ≥0∞⦄, Measurable g →
      AEMeasurable (weightedFiberSum f (A i) g) (μH[d] : Measure Y))
    (hf : LipschitzWith K f) (hN : μH[d] N = 0) :
    AreaFormulaHolds μH[d] μH[d] f J (N ∪ ⋃ i, A i) := by
  refine AreaFormulaHolds.of_rectifiable_decomposition hd hA hdisj h hmeas hf.lipschitzOnWith
    (fun x hx ↦ ?_) hN
  rcases hx with ⟨hxN | hxU, hxnotU⟩ | ⟨hxU, hxnot⟩
  exacts [hxN, False.elim (hxnotU hxU), False.elim (hxnot (Or.inr hxU))]

/-- **Multiplicity form of the tangential area formula on `N ∪ ⋃ i, A i`**:
`∫⁻ x in N ∪ ⋃ i, A i, J x ∂μH[d] = ∫⁻ y, fiberMultiplicity f (N ∪ ⋃ i, A i) y ∂μH[d]`. -/
theorem lintegral_jacobian_of_eq_null_union_iUnion {ι : Type*} [Countable ι] {d : ℝ} (hd : 0 ≤ d)
    {K : ℝ≥0} {f : X → Y} {J : X → ℝ≥0∞} {A : ι → Set X} {N : Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (h : ∀ i, AreaFormulaHolds μH[d] μH[d] f J (A i))
    (hmeas : ∀ i ⦃g : X → ℝ≥0∞⦄, Measurable g →
      AEMeasurable (weightedFiberSum f (A i) g) (μH[d] : Measure Y))
    (hf : LipschitzWith K f) (hN : μH[d] N = 0) :
    ∫⁻ x in N ∪ ⋃ i, A i, J x ∂μH[d] =
      ∫⁻ y, fiberMultiplicity f (N ∪ ⋃ i, A i) y ∂μH[d] :=
  (AreaFormulaHolds.of_eq_null_union_iUnion hd hA hdisj h hmeas hf hN).lintegral_jacobian

/-- **Injective specialization of the tangential area formula on `N ∪ ⋃ i, A i`**: when `f` is
injective on `M = N ∪ ⋃ i, A i` and `f '' M` is measurable,
`∫⁻ x in M, J x ∂μH[d] = μH[d] (f '' M)`. -/
theorem lintegral_jacobian_eq_measure_image_of_eq_null_union_iUnion {ι : Type*} [Countable ι]
    {d : ℝ} (hd : 0 ≤ d) {K : ℝ≥0} {f : X → Y} {J : X → ℝ≥0∞} {A : ι → Set X} {N : Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (h : ∀ i, AreaFormulaHolds μH[d] μH[d] f J (A i))
    (hmeas : ∀ i ⦃g : X → ℝ≥0∞⦄, Measurable g →
      AEMeasurable (weightedFiberSum f (A i) g) (μH[d] : Measure Y))
    (hf : LipschitzWith K f) (hN : μH[d] N = 0)
    (hinj : Set.InjOn f (N ∪ ⋃ i, A i)) (himg : MeasurableSet (f '' (N ∪ ⋃ i, A i))) :
    ∫⁻ x in N ∪ ⋃ i, A i, J x ∂μH[d] = μH[d] (f '' (N ∪ ⋃ i, A i)) :=
  (AreaFormulaHolds.of_eq_null_union_iUnion hd hA hdisj h hmeas hf hN)
    |>.lintegral_jacobian_eq_measure_image_of_injOn hinj himg

end RectifiableAreaFormula

end TauCeti
