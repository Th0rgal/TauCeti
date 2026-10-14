/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.EssentialConvexity
public import TauCeti.MeasureTheory.Measure.IsoperimetricDomains
import all TauCeti.MeasureTheory.Measure.BallPerimeter
import all TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
import all TauCeti.MeasureTheory.Measure.EssentialBoundary
import all TauCeti.MeasureTheory.Measure.EssentialConvexity
import all TauCeti.MeasureTheory.Measure.IsoperimetricDomains
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerProperties
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
import all TauCeti.MeasureTheory.Measure.Perimeter

/-!
# Cylindrical Tube Estimates, Compact Convex Representatives, and Measurable Ball Rigidity

This file develops cylindrical tube integration formulas in orthogonal slice coordinates, the
quantitative endpoint-to-midpoint `OrdConnected` slice bridge, boundedness of finite-volume convex
sets with nonempty interior, existence of compact convex body representatives preserving volume and
Caccioppoli perimeter, Steiner perimeter equality forcing, and measurable ball rigidity:

1. **Cylindrical tubes and endpoint-to-midpoint interval slice propagation**:
   `orthogonalSliceLinearIsometryEquiv`, `orthogonalSliceMeasurableEquiv`,
   `measurePreserving_orthogonalSlice`, `cylinderTube`, `cylinderSliceSet`, `mem_cylinderTube_iff`,
   `measurableSet_cylinderTube`, `volume_cylinderTube`, `lineSection_cylinderTube`,
   `volume_inter_cylinderTube`, `volume_cylinderTube_diff`,
   `Set.OrdConnected.Icc_subset_of_nonempty_inter_Icc`,
   `IsAEOrdConnected.volume_Icc_diff_eq_zero_of_volume_inter_Icc_pos`,
   `IsAEOrdConnected.volume_inter_eq_of_subset_Icc`,
   `volume_cylinderTube_diff_eq_zero_of_ae_inter_Icc_pos`, and
   `volume_inter_cylinderTube_eq_of_ae_inter_Icc_pos`.
2. **Boundedness of finite-volume convex sets & compact convex body representatives**:
   `Convex.ball_combo_subset_of_ball_subset`, `Convex.ball_midpoint_subset_of_ball_subset`,
   `Convex.measure_ball_mul_le_of_not_isBounded`,
   `Convex.isBounded_of_interior_nonempty_of_measure_lt_top`,
   `Convex.isBounded_of_interior_nonempty_of_volume_lt_top`,
   `Convex.isBounded_of_volume_pos_of_volume_lt_top`,
   `Convex.isCompact_closure_of_volume_pos_of_volume_lt_top`,
   `Convex.closure_isCompact_and_perimeter_eq`, and
   `IsEssentiallyConvex.exists_isCompact_convex_witness`.
3. **Steiner perimeter equality forcing & measurable essentially-convex ball rigidity**:
   `isoperimetricLHS`, `perimeter_eq_of_isoperimetricBound_eq`,
   `forall_perimeter_steinerSymmetrization_eq_of_isoperimetricBound_eq`,
   `IsEssentiallyConvex.exists_isCompact_convex_isoperimetric_witness`,
   `volume_symmDiff_ball_eq_zero_of_eq_closedBall`,
   `isEssentiallyConvex_and_isoperimetric_eq_of_symmDiff_ball_eq_zero`, and
   `IsEssentiallyConvex.perimeter_eq_isoperimetricBound_iff_exists_ball`.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set Submodule
open TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal symmDiff InnerProductSpace Topology

namespace TauCeti

/-!
### Section 1: Cylindrical tubes and endpoint-to-midpoint interval slice propagation
-/

section CylinderTubeAndSliceBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal slice linear isometry equivalence `WithLp 2 ((ℝ ∙ e)ᗮ × ℝ) ≃ₗᵢ[ℝ] E` mapping
`(y, t)` to `(y : E) + t • e` for a unit vector `e` (`‖e‖ = 1`). -/
def orthogonalSliceLinearIsometryEquiv (e : E) (he : ‖e‖ = 1) :
    WithLp 2 ((ℝ ∙ e)ᗮ × ℝ) ≃ₗᵢ[ℝ] E :=
  orthogonalHyperplaneProdEquiv he

@[simp]
theorem orthogonalSliceLinearIsometryEquiv_apply (e : E) (he : ‖e‖ = 1)
    (p : WithLp 2 ((ℝ ∙ e)ᗮ × ℝ)) :
    orthogonalSliceLinearIsometryEquiv e he p = (p.fst : E) + p.snd • e := by
  rfl

@[simp]
theorem orthogonalSliceLinearIsometryEquiv_symm_apply (e : E) (he : ‖e‖ = 1) (x : E) :
    (orthogonalSliceLinearIsometryEquiv e he).symm x =
      WithLp.toLp 2 ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x, ⟪x, e⟫_ℝ) := by
  rfl

variable [MeasurableSpace E] [BorelSpace E]

/-- Orthogonal slice measurable equivalence `((ℝ ∙ e)ᗮ × ℝ) ≃ᵐ E` mapping `(y, t)` to
`(y : E) + t • e` for a unit vector `e` (`‖e‖ = 1`). -/
def orthogonalSliceMeasurableEquiv (e : E) (he : ‖e‖ = 1) : ((ℝ ∙ e)ᗮ × ℝ) ≃ᵐ E :=
  orthogonalHyperplaneProdMeasurableEquiv he

@[simp]
theorem orthogonalSliceMeasurableEquiv_apply (e : E) (he : ‖e‖ = 1) (p : (ℝ ∙ e)ᗮ × ℝ) :
    orthogonalSliceMeasurableEquiv e he p = (p.1 : E) + p.2 • e := by
  rfl

@[simp]
theorem orthogonalSliceMeasurableEquiv_symm_apply (e : E) (he : ‖e‖ = 1) (x : E) :
    (orthogonalSliceMeasurableEquiv e he).symm x =
      ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x, ⟪x, e⟫_ℝ) := by
  rfl

/-- **Cylindrical tube** in unit direction `e` (`‖e‖ = 1`) over a base set `B ⊆ (ℝ ∙ e)ᗮ` and a 1D
fiber set `I ⊆ ℝ`, defined as the image of `B ×ˢ I` under `orthogonalSliceMeasurableEquiv e he`. -/
def cylinderTube (e : E) (he : ‖e‖ = 1) (B : Set (ℝ ∙ e)ᗮ) (I : Set ℝ) : Set E :=
  orthogonalSliceMeasurableEquiv e he '' (B ×ˢ I)

/-- Alias for `cylinderTube e he B I`. -/
abbrev cylinderSliceSet (e : E) (he : ‖e‖ = 1) (B : Set (ℝ ∙ e)ᗮ) (I : Set ℝ) : Set E :=
  cylinderTube e he B I

/-- `cylinderTube e he B I` is the preimage of `B ×ˢ I` under
`(orthogonalSliceMeasurableEquiv e he).symm`. -/
theorem cylinderTube_eq_symm_preimage (e : E) (he : ‖e‖ = 1) (B : Set (ℝ ∙ e)ᗮ) (I : Set ℝ) :
    cylinderTube e he B I = (orthogonalSliceMeasurableEquiv e he).symm ⁻¹' (B ×ˢ I) :=
  (orthogonalSliceMeasurableEquiv e he).toEquiv.image_eq_preimage_symm (B ×ˢ I)

/-- Explicit set-builder description of `cylinderTube e he B I`. -/
theorem cylinderTube_eq_setOf (e : E) (he : ‖e‖ = 1) (B : Set (ℝ ∙ e)ᗮ) (I : Set ℝ) :
    cylinderTube e he B I =
      {x : E | (ℝ ∙ e)ᗮ.orthogonalProjectionOnto x ∈ B ∧ ⟪x, e⟫_ℝ ∈ I} := by
  ext x; simp [cylinderTube_eq_symm_preimage]

/-- Membership characterization for `cylinderTube e he B I`. -/
@[simp]
theorem mem_cylinderTube_iff {e : E} (he : ‖e‖ = 1) {B : Set (ℝ ∙ e)ᗮ} {I : Set ℝ} {x : E} :
    x ∈ cylinderTube e he B I ↔ (ℝ ∙ e)ᗮ.orthogonalProjectionOnto x ∈ B ∧ ⟪x, e⟫_ℝ ∈ I := by
  simp [cylinderTube_eq_setOf]

/-- Membership of `(y : E) + t • e` in `cylinderTube e he B I` (`y : (ℝ ∙ e)ᗮ`). -/
theorem mem_cylinderTube_add_smul_iff {e : E} (he : ‖e‖ = 1) {B : Set (ℝ ∙ e)ᗮ} {I : Set ℝ}
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    (y : E) + t • e ∈ cylinderTube e he B I ↔ y ∈ B ∧ t ∈ I := by
  rw [mem_cylinderTube_iff he, orthogonalProjectionOnto_coe_add_smul,
    inner_coe_orthogonal_add_smul_self he]

@[simp]
theorem cylinderTube_empty_left (e : E) (he : ‖e‖ = 1) (I : Set ℝ) :
    cylinderTube e he ∅ I = ∅ := by simp [cylinderTube]

@[simp]
theorem cylinderTube_empty_right (e : E) (he : ‖e‖ = 1) (B : Set (ℝ ∙ e)ᗮ) :
    cylinderTube e he B ∅ = ∅ := by simp [cylinderTube]

@[simp]
theorem cylinderTube_univ (e : E) (he : ‖e‖ = 1) :
    cylinderTube e he Set.univ Set.univ = Set.univ := by
  rw [cylinderTube_eq_symm_preimage, Set.univ_prod_univ, Set.preimage_univ]

theorem cylinderTube_mono {e : E} (he : ‖e‖ = 1) {B₁ B₂ : Set (ℝ ∙ e)ᗮ} {I₁ I₂ : Set ℝ}
    (hB : B₁ ⊆ B₂) (hI : I₁ ⊆ I₂) :
    cylinderTube e he B₁ I₁ ⊆ cylinderTube e he B₂ I₂ :=
  Set.image_mono (Set.prod_mono hB hI)

theorem cylinderTube_inter (e : E) (he : ‖e‖ = 1) (B₁ B₂ : Set (ℝ ∙ e)ᗮ) (I₁ I₂ : Set ℝ) :
    cylinderTube e he (B₁ ∩ B₂) (I₁ ∩ I₂) =
      cylinderTube e he B₁ I₁ ∩ cylinderTube e he B₂ I₂ := by
  rw [cylinderTube_eq_symm_preimage, cylinderTube_eq_symm_preimage, cylinderTube_eq_symm_preimage,
    ← Set.prod_inter_prod, Set.preimage_inter]

/-- For `y ∈ B`, the 1D slice `lineSection e (cylinderTube e he B I) y` is `I`. -/
theorem lineSection_cylinderTube_of_mem (e : E) (he : ‖e‖ = 1) {B : Set (ℝ ∙ e)ᗮ} (I : Set ℝ)
    {y : (ℝ ∙ e)ᗮ} (hy : y ∈ B) :
    lineSection e (cylinderTube e he B I) y = I := by
  ext t; simp [lineSection, mem_cylinderTube_add_smul_iff he, hy]

/-- For `y ∉ B`, the 1D slice `lineSection e (cylinderTube e he B I) y` is `∅`. -/
theorem lineSection_cylinderTube_of_notMem (e : E) (he : ‖e‖ = 1) {B : Set (ℝ ∙ e)ᗮ} (I : Set ℝ)
    {y : (ℝ ∙ e)ᗮ} (hy : y ∉ B) :
    lineSection e (cylinderTube e he B I) y = ∅ := by
  ext t; simp [lineSection, mem_cylinderTube_add_smul_iff he, hy]

open Classical in
/-- Complete slice formula for `cylinderTube e he B I`. -/
theorem lineSection_cylinderTube (e : E) (he : ‖e‖ = 1) (B : Set (ℝ ∙ e)ᗮ) (I : Set ℝ)
    (y : (ℝ ∙ e)ᗮ) :
    lineSection e (cylinderTube e he B I) y = if y ∈ B then I else ∅ := by
  split_ifs with hy
  · exact lineSection_cylinderTube_of_mem e he I hy
  · exact lineSection_cylinderTube_of_notMem e he I hy

/-- For `y ∈ B`, `lineSection e (A ∩ cylinderTube e he B I) y = lineSection e A y ∩ I`. -/
theorem lineSection_inter_cylinderTube_of_mem (e : E) (he : ‖e‖ = 1) (A : Set E)
    {B : Set (ℝ ∙ e)ᗮ} (I : Set ℝ) {y : (ℝ ∙ e)ᗮ} (hy : y ∈ B) :
    lineSection e (A ∩ cylinderTube e he B I) y = lineSection e A y ∩ I := by
  rw [lineSection_inter, lineSection_cylinderTube_of_mem e he I hy]

/-- For `y ∉ B`, `lineSection e (A ∩ cylinderTube e he B I) y = ∅`. -/
theorem lineSection_inter_cylinderTube_of_notMem (e : E) (he : ‖e‖ = 1) (A : Set E)
    {B : Set (ℝ ∙ e)ᗮ} (I : Set ℝ) {y : (ℝ ∙ e)ᗮ} (hy : y ∉ B) :
    lineSection e (A ∩ cylinderTube e he B I) y = ∅ := by
  rw [lineSection_inter, lineSection_cylinderTube_of_notMem e he I hy, Set.inter_empty]

/-- `cylinderTube e he B I` is measurable whenever `B` and `I` are measurable. -/
theorem measurableSet_cylinderTube (e : E) (he : ‖e‖ = 1) {B : Set (ℝ ∙ e)ᗮ} {I : Set ℝ}
    (hB : MeasurableSet B) (hI : MeasurableSet I) :
    MeasurableSet (cylinderTube e he B I) := by
  rw [cylinderTube_eq_symm_preimage]
  exact (orthogonalSliceMeasurableEquiv e he).symm.measurable (hB.prod hI)

variable [FiniteDimensional ℝ E]

/-- `orthogonalSliceMeasurableEquiv e he` preserves Lebesgue measure. -/
theorem measurePreserving_orthogonalSlice (e : E) (he : ‖e‖ = 1) :
    MeasurePreserving (orthogonalSliceMeasurableEquiv e he)
      ((volume : Measure (ℝ ∙ e)ᗮ).prod (volume : Measure ℝ)) (volume : Measure E) :=
  measurePreserving_orthogonalHyperplaneProd he

/-- `(orthogonalSliceMeasurableEquiv e he).symm` preserves Lebesgue measure. -/
theorem measurePreserving_orthogonalSlice_symm (e : E) (he : ‖e‖ = 1) :
    MeasurePreserving (orthogonalSliceMeasurableEquiv e he).symm
      (volume : Measure E) ((volume : Measure (ℝ ∙ e)ᗮ).prod (volume : Measure ℝ)) :=
  (measurePreserving_orthogonalSlice e he).symm (orthogonalSliceMeasurableEquiv e he)

/-- `cylinderTube e he B I` is null-measurable whenever `B` and `I` are null-measurable. -/
theorem nullMeasurableSet_cylinderTube (e : E) (he : ‖e‖ = 1) {B : Set (ℝ ∙ e)ᗮ} {I : Set ℝ}
    (hB : NullMeasurableSet B volume) (hI : NullMeasurableSet I volume) :
    NullMeasurableSet (cylinderTube e he B I) volume := by
  rw [cylinderTube_eq_symm_preimage]
  exact (hB.prod hI).preimage (measurePreserving_orthogonalSlice_symm e he).quasiMeasurePreserving

/-- **Exact product-volume formula for a cylindrical tube**:
`volume (cylinderTube e he B I) = volume B * volume I`. -/
@[simp]
theorem volume_cylinderTube (e : E) (he : ‖e‖ = 1) (B : Set (ℝ ∙ e)ᗮ) (I : Set ℝ) :
    volume (cylinderTube e he B I) = volume B * volume I := by
  rw [cylinderTube_eq_symm_preimage,
    (measurePreserving_orthogonalSlice_symm e he).measure_preimage_emb
      (orthogonalSliceMeasurableEquiv e he).symm.measurableEmbedding (B ×ˢ I),
    Measure.prod_prod]

/-- **Fubini–Tonelli slice integral for `volume (A ∩ cylinderTube e he B I)`**. -/
theorem volume_inter_cylinderTube (e : E) (he : ‖e‖ = 1) {A : Set E} {B : Set (ℝ ∙ e)ᗮ}
    {I : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) (hI : MeasurableSet I) :
    volume (A ∩ cylinderTube e he B I) =
      ∫⁻ y in B, volume (lineSection e A y ∩ I) ∂volume := by
  rw [volume_eq_lintegral_lineSection he (hA.inter (measurableSet_cylinderTube e he hB hI)),
    ← lintegral_indicator hB]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : y ∈ B
  · simp [Set.indicator_of_mem hy, lineSection_inter_cylinderTube_of_mem e he A I hy]
  · simp [Set.indicator_of_notMem hy, lineSection_inter_cylinderTube_of_notMem e he A I hy]

/-- **Fubini–Tonelli slice integral for `volume (cylinderTube e he B I \ A)`**. -/
theorem volume_cylinderTube_diff (e : E) (he : ‖e‖ = 1) {A : Set E} {B : Set (ℝ ∙ e)ᗮ}
    {I : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) (hI : MeasurableSet I) :
    volume (cylinderTube e he B I \ A) =
      ∫⁻ y in B, volume (I \ lineSection e A y) ∂volume := by
  rw [volume_eq_lintegral_lineSection he ((measurableSet_cylinderTube e he hB hI).diff hA),
    ← lintegral_indicator hB]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : y ∈ B
  · simp [Set.indicator_of_mem hy, lineSection_sdiff, lineSection_cylinderTube_of_mem e he I hy]
  · simp [Set.indicator_of_notMem hy, lineSection_sdiff,
      lineSection_cylinderTube_of_notMem e he I hy]

/-- **Endpoint-to-midpoint `OrdConnected` interval bridge**: if `I : Set ℝ` is order-connected and
meets both `Set.Icc a₁ b₁` and `Set.Icc a₂ b₂`, then `Set.Icc b₁ a₂ ⊆ I`. -/
theorem _root_.Set.OrdConnected.Icc_subset_of_nonempty_inter_Icc {I : Set ℝ} (hI : I.OrdConnected)
    {a₁ b₁ a₂ b₂ : ℝ} (h₁ : (I ∩ Set.Icc a₁ b₁).Nonempty) (h₂ : (I ∩ Set.Icc a₂ b₂).Nonempty) :
    Set.Icc b₁ a₂ ⊆ I := by
  rcases h₁ with ⟨t₁, ht₁I, -, ht₁b₁⟩; rcases h₂ with ⟨t₂, ht₂I, ha₂t₂, -⟩
  exact fun t ⟨hb₁t, hta₂⟩ ↦ hI.out ht₁I ht₂I ⟨ht₁b₁.trans hb₁t, hta₂.trans ha₂t₂⟩

/-- **Measure-theoretic 1D interval-slice bridge**: if `IsAEOrdConnected S`,
`0 < volume (S ∩ Set.Icc a₁ b₁)`, and `0 < volume (S ∩ Set.Icc a₂ b₂)`, then almost every point of
`Set.Icc b₁ a₂` belongs to `S`, i.e. `volume (Set.Icc b₁ a₂ \ S) = 0`. -/
theorem IsAEOrdConnected.volume_Icc_diff_eq_zero_of_volume_inter_Icc_pos {S : Set ℝ}
    (hS : IsAEOrdConnected S) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : 0 < volume (S ∩ Set.Icc a₁ b₁))
    (h₂ : 0 < volume (S ∩ Set.Icc a₂ b₂)) :
    volume (Set.Icc b₁ a₂ \ S) = 0 := by
  rcases hS with ⟨I, hI_ord, hSI⟩
  have hI₁ : 0 < volume (I ∩ Set.Icc a₁ b₁) := by
    rwa [← measure_congr (hSI.inter EventuallyEq.rfl)]
  have hI₂ : 0 < volume (I ∩ Set.Icc a₂ b₂) := by
    rwa [← measure_congr (hSI.inter EventuallyEq.rfl)]
  have hsub : Set.Icc b₁ a₂ ⊆ I :=
    hI_ord.Icc_subset_of_nonempty_inter_Icc
      (nonempty_of_measure_ne_zero hI₁.ne') (nonempty_of_measure_ne_zero hI₂.ne')
  exact measure_mono_null (Set.sdiff_subset_sdiff_left hsub) (ae_eq_set.1 hSI).2

/-- If `IsAEOrdConnected S` meets `Set.Icc a₁ b₁` and `Set.Icc a₂ b₂` in positive measure, then for
every subset `J ⊆ Set.Icc b₁ a₂`, `volume (J \ S) = 0`. -/
theorem IsAEOrdConnected.volume_diff_eq_zero_of_subset_Icc {S J : Set ℝ}
    (hS : IsAEOrdConnected S) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : 0 < volume (S ∩ Set.Icc a₁ b₁))
    (h₂ : 0 < volume (S ∩ Set.Icc a₂ b₂)) (hJ : J ⊆ Set.Icc b₁ a₂) :
    volume (J \ S) = 0 :=
  measure_mono_null (Set.sdiff_subset_sdiff_left hJ)
    (hS.volume_Icc_diff_eq_zero_of_volume_inter_Icc_pos h₁ h₂)

/-- If `IsAEOrdConnected S` meets `Set.Icc a₁ b₁` and `Set.Icc a₂ b₂` in positive measure, then for
every subset `J ⊆ Set.Icc b₁ a₂`, `volume (S ∩ J) = volume J`. -/
theorem IsAEOrdConnected.volume_inter_eq_of_subset_Icc {S J : Set ℝ}
    (hS : IsAEOrdConnected S) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : 0 < volume (S ∩ Set.Icc a₁ b₁))
    (h₂ : 0 < volume (S ∩ Set.Icc a₂ b₂)) (hJ : J ⊆ Set.Icc b₁ a₂) :
    volume (S ∩ J) = volume J := by
  have hdiff : volume (J \ S) = 0 := hS.volume_diff_eq_zero_of_subset_Icc h₁ h₂ hJ
  have hae : (S ∩ J : Set ℝ) =ᵐ[volume] J := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null (fun _ ⟨⟨_, hxJ⟩, hx⟩ ↦ False.elim (hx hxJ)) measure_empty, ?_⟩
    have heq : J \ (S ∩ J) = J \ S := by ext t; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
    rw [heq, hdiff]
  exact measure_congr hae

/-- **Quantitative cylindrical tube full-density theorem (null-difference form)**: if for
`volume`-a.e. `y ∈ B`, the slice `lineSection e A y` is `IsAEOrdConnected` and intersects both
`Set.Icc a₁ b₁` and `Set.Icc a₂ b₂` in positive 1D measure, then for every measurable subset
`J ⊆ Set.Icc b₁ a₂`, `volume (cylinderTube e he B J \ A) = 0`. -/
theorem volume_cylinderTube_diff_eq_zero_of_ae_inter_Icc_pos (e : E) (he : ‖e‖ = 1) {A : Set E}
    {B : Set (ℝ ∙ e)ᗮ} {J : Set ℝ} {a₁ b₁ a₂ b₂ : ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hJ : MeasurableSet J) (hJ_sub : J ⊆ Set.Icc b₁ a₂)
    (hslice : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ B →
      IsAEOrdConnected (lineSection e A y) ∧
        0 < volume (lineSection e A y ∩ Set.Icc a₁ b₁) ∧
        0 < volume (lineSection e A y ∩ Set.Icc a₂ b₂)) :
    volume (cylinderTube e he B J \ A) = 0 := by
  have hmeas_diff : MeasurableSet (cylinderTube e he B J \ A) :=
    (measurableSet_cylinderTube e he hB hJ).diff hA
  rw [volume_eq_lintegral_lineSection he hmeas_diff,
    (lintegral_eq_zero_iff (measurable_volume_lineSection hmeas_diff))]
  filter_upwards [hslice] with y hy
  by_cases hyB : y ∈ B
  · obtain ⟨hord, h₁, h₂⟩ := hy hyB
    rw [Pi.zero_apply, lineSection_sdiff, lineSection_cylinderTube_of_mem e he J hyB]
    exact hord.volume_diff_eq_zero_of_subset_Icc h₁ h₂ hJ_sub
  · rw [Pi.zero_apply, lineSection_sdiff, lineSection_cylinderTube_of_notMem e he J hyB,
      Set.empty_sdiff, measure_empty]

/-- **Quantitative cylindrical tube full-density theorem (intersection-volume form)**: under the
hypotheses of `volume_cylinderTube_diff_eq_zero_of_ae_inter_Icc_pos`,
`volume (A ∩ cylinderTube e he B J) = volume B * volume J = volume (cylinderTube e he B J)`. -/
theorem volume_inter_cylinderTube_eq_of_ae_inter_Icc_pos (e : E) (he : ‖e‖ = 1) {A : Set E}
    {B : Set (ℝ ∙ e)ᗮ} {J : Set ℝ} {a₁ b₁ a₂ b₂ : ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hJ : MeasurableSet J) (hJ_sub : J ⊆ Set.Icc b₁ a₂)
    (hslice : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ B →
      IsAEOrdConnected (lineSection e A y) ∧
        0 < volume (lineSection e A y ∩ Set.Icc a₁ b₁) ∧
        0 < volume (lineSection e A y ∩ Set.Icc a₂ b₂)) :
    volume (A ∩ cylinderTube e he B J) = volume B * volume J ∧
      volume (A ∩ cylinderTube e he B J) = volume (cylinderTube e he B J) := by
  have hdiff := volume_cylinderTube_diff_eq_zero_of_ae_inter_Icc_pos e he hA hB hJ hJ_sub hslice
  have hae : (A ∩ cylinderTube e he B J : Set E) =ᵐ[volume] cylinderTube e he B J := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null (fun _ ⟨⟨_, hxT⟩, hx⟩ ↦ False.elim (hx hxT)) measure_empty, ?_⟩
    have heq : cylinderTube e he B J \ (A ∩ cylinderTube e he B J) =
        cylinderTube e he B J \ A := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [heq, hdiff]
  have hvol : volume (A ∩ cylinderTube e he B J) = volume (cylinderTube e he B J) :=
    measure_congr hae
  exact ⟨hvol.trans (volume_cylinderTube e he B J), hvol⟩

/-- If `essentialInterior volume A` is closed under line segments, then it is convex. -/
theorem convex_essentialInterior_of_segment_subset {A : Set E}
    (hseg : ∀ x₁ ∈ essentialInterior volume A, ∀ x₂ ∈ essentialInterior volume A,
      segment ℝ x₁ x₂ ⊆ essentialInterior volume A) :
    Convex ℝ (essentialInterior volume A) :=
  convex_iff_segment_subset.2 hseg

/-- If `A` is null-measurable and `essentialInterior volume A` is closed under line segments, then
`IsEssentiallyConvex A`. -/
theorem isEssentiallyConvex_of_segment_subset_essentialInterior {A : Set E}
    (hA : NullMeasurableSet A volume)
    (hseg : ∀ x₁ ∈ essentialInterior volume A, ∀ x₂ ∈ essentialInterior volume A,
      segment ℝ x₁ x₂ ⊆ essentialInterior volume A) :
    IsEssentiallyConvex A :=
  IsEssentiallyConvex.of_convex_essentialInterior hA
    (convex_essentialInterior_of_segment_subset hseg)

end CylinderTubeAndSliceBridge

/-! ### Section 2: Boundedness of finite-volume convex sets and compact convex witnesses -/

section ConvexBoundednessAndCompactWitness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Convex ball-to-point interpolation inclusion**: if `Convex ℝ C`, `Metric.ball x₀ r ⊆ C`,
and `x ∈ C`, then for every `θ ∈ [0, 1)`, the scaled open ball
`Metric.ball ((1 - θ) • x₀ + θ • x) ((1 - θ) * r)` is contained in `C`. -/
theorem _root_.Convex.ball_combo_subset_of_ball_subset {C : Set E} (hC : Convex ℝ C) {x₀ x : E}
    {r θ : ℝ} (hball : Metric.ball x₀ r ⊆ C) (hx : x ∈ C) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) :
    Metric.ball ((1 - θ) • x₀ + θ • x) ((1 - θ) * r) ⊆ C := by
  intro z hz; have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  let y : E := x₀ + (1 - θ)⁻¹ • (z - ((1 - θ) • x₀ + θ • x))
  have hy_ball : y ∈ Metric.ball x₀ r := by
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    have hy_sub : y - x₀ = (1 - θ)⁻¹ • (z - ((1 - θ) • x₀ + θ • x)) := add_sub_cancel_left _ _
    rw [hy_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h1θ, inv_mul_lt_iff₀ h1θ]
    exact hz
  have hcomb : (1 - θ) • y + θ • x = z := by
    dsimp only [y]; rw [smul_add, smul_inv_smul₀ h1θ.ne']; abel
  rw [← hcomb]; exact hC (hball hy_ball) hx h1θ.le hθ₀ (sub_add_cancel 1 θ)

/-- **Midpoint ball inclusion**: if `Convex ℝ C`, `Metric.ball x₀ r ⊆ C`, and `x ∈ C`, then
`Metric.ball ((1 / 2 : ℝ) • (x₀ + x)) (r / 2) ⊆ C`. -/
theorem _root_.Convex.ball_midpoint_subset_of_ball_subset {C : Set E} (hC : Convex ℝ C) {x₀ x : E}
    {r : ℝ} (hball : Metric.ball x₀ r ⊆ C) (hx : x ∈ C) :
    Metric.ball ((1 / 2 : ℝ) • (x₀ + x)) (r / 2) ⊆ C := by
  have h := hC.ball_combo_subset_of_ball_subset hball hx (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hcenter : (1 - (1 / 2 : ℝ)) • x₀ + (1 / 2 : ℝ) • x = (1 / 2 : ℝ) • (x₀ + x) := by
    rw [smul_add]; norm_num
  have hrad : (1 - (1 / 2 : ℝ)) * r = r / 2 := by ring
  rwa [hcenter, hrad] at h

omit [NormedSpace ℝ E] in
/-- If `C : Set E` is not bounded (`¬ Bornology.IsBounded C`), then for every `x₀ : E` and `R : ℝ`
there exists `x ∈ C` with `R < dist x x₀`. -/
theorem exists_dist_gt_of_not_isBounded {C : Set E} (hunb : ¬ Bornology.IsBounded C) (x₀ : E)
    (R : ℝ) : ∃ x ∈ C, R < dist x x₀ := by
  by_contra! hle
  exact hunb (Metric.isBounded_closedBall.subset fun x hx ↦ Metric.mem_closedBall.2 (hle x hx))

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- If a convex set `C` contains `Metric.ball x₀ r` (`r > 0`) and is unbounded, then for every
`N : ℕ`, `C` contains `N` pairwise disjoint open balls of radius `r / 2`, so
`(N : ℝ≥0∞) * μ (Metric.ball x₀ (r / 2)) ≤ μ C`. -/
theorem _root_.Convex.measure_ball_mul_le_of_not_isBounded {C : Set E} (hC : Convex ℝ C) {x₀ : E}
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball x₀ r ⊆ C) (hunb : ¬ Bornology.IsBounded C)
    (N : ℕ) : (N : ℝ≥0∞) * μ (Metric.ball x₀ (r / 2)) ≤ μ C := by
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · simp
  · have hN_real : (0 : ℝ) < 2 * (N : ℝ) := by positivity
    obtain ⟨x, hxC, hx_dist⟩ := exists_dist_gt_of_not_isBounded hunb x₀ (2 * (N : ℝ) * r)
    let θ : Fin N → ℝ := fun k ↦ (k.1 : ℝ) / (2 * (N : ℝ))
    let c : Fin N → E := fun k ↦ (1 - θ k) • x₀ + θ k • x
    have hθ_nonneg (k : Fin N) : 0 ≤ θ k := div_nonneg (Nat.cast_nonneg k.1) hN_real.le
    have hθ_le_half (k : Fin N) : θ k ≤ 1 / 2 := by
      dsimp only [θ]; rw [div_le_iff₀ hN_real]
      have hk : (k.1 : ℝ) ≤ (N : ℝ) := Nat.cast_le.2 k.2.le; linarith
    have hsub (k : Fin N) : Metric.ball (c k) (r / 2) ⊆ C := by
      refine (Metric.ball_subset_ball ?_).trans
        (hC.ball_combo_subset_of_ball_subset hball hxC (hθ_nonneg k)
          ((hθ_le_half k).trans_lt (by norm_num)))
      nlinarith [hθ_le_half k]
    have hdisj : Pairwise fun i j : Fin N ↦
        Disjoint (Metric.ball (c i) (r / 2)) (Metric.ball (c j) (r / 2)) := by
      intro i j hij; refine Metric.ball_disjoint_ball ?_
      have hdiff : c i - c j = (θ i - θ j) • (x - x₀) := by
        dsimp only [c]; rw [sub_smul, sub_smul, one_smul, sub_smul, smul_sub, smul_sub]; abel
      have hdist_eq : dist (c i) (c j) = |θ i - θ j| * dist x x₀ := by
        rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
      have hij_abs : 1 ≤ |(i.1 : ℝ) - (j.1 : ℝ)| := by
        have hij_int : (1 : ℤ) ≤ |(i.1 : ℤ) - (j.1 : ℤ)| :=
          Int.one_le_abs (sub_ne_zero.2 (Nat.cast_injective.ne (Fin.val_ne_of_ne hij)))
        exact_mod_cast hij_int
      have hθ_abs : 1 / (2 * (N : ℝ)) ≤ |θ i - θ j| := by
        dsimp only [θ]; rw [← sub_div, abs_div, abs_of_pos hN_real]
        exact div_le_div_of_nonneg_right hij_abs hN_real.le
      have hr_le : r ≤ (1 / (2 * (N : ℝ))) * dist x x₀ := by
        rw [one_div, le_inv_mul_iff₀ hN_real]; exact hx_dist.le
      linarith [mul_le_mul_of_nonneg_right hθ_abs (dist_nonneg (x := x) (y := x₀))]
    calc (N : ℝ≥0∞) * μ (Metric.ball x₀ (r / 2))
        = ∑ k ∈ (Finset.univ : Finset (Fin N)), μ (Metric.ball (c k) (r / 2)) := by
          have hball_eq (k : Fin N) :
              μ (Metric.ball (c k) (r / 2)) = μ (Metric.ball x₀ (r / 2)) := by
            rw [Measure.addHaar_ball_center μ (c k) (r / 2),
              Measure.addHaar_ball_center μ x₀ (r / 2)]
          simp [hball_eq]
      _ = μ (⋃ k ∈ (Finset.univ : Finset (Fin N)), Metric.ball (c k) (r / 2)) := by
          rw [measure_biUnion_finset (fun i _ j _ hij ↦ hdisj hij)
            (fun _ _ ↦ measurableSet_ball)]
      _ ≤ μ C := measure_mono (Set.iUnion₂_subset fun k _ ↦ hsub k)

variable [FiniteDimensional ℝ E]

/-- **Every finite-Haar-measure convex set with nonempty interior is bounded**. -/
theorem _root_.Convex.isBounded_of_interior_nonempty_of_measure_lt_top {C : Set E}
    (hC : Convex ℝ C) (hint : (interior C).Nonempty) (hfin : μ C < ⊤) :
    Bornology.IsBounded C := by
  rcases hint with ⟨x₀, hx₀⟩
  rcases Metric.isOpen_iff.1 isOpen_interior x₀ hx₀ with ⟨r, hr, hball_int⟩
  have hball : Metric.ball x₀ r ⊆ C := hball_int.trans interior_subset
  by_contra hunb
  set b : ℝ≥0∞ := μ (Metric.ball x₀ (r / 2))
  have hb_pos : 0 < b := measure_ball_pos μ x₀ (half_pos hr)
  have hb_top : b ≠ ⊤ := measure_ball_lt_top.ne
  have hdiv_lt : μ C / b < ⊤ := ENNReal.div_lt_top hfin.ne hb_pos.ne'
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hdiv_lt.ne
  have hle : (N : ℝ≥0∞) * b ≤ μ C := hC.measure_ball_mul_le_of_not_isBounded hr hball hunb N
  have hlt : μ C < (N : ℝ≥0∞) * b := (ENNReal.div_lt_iff (Or.inl hb_pos.ne') (Or.inl hb_top)).1 hN
  exact hlt.not_ge hle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Every finite-volume convex set in `V` with nonempty interior is bounded. -/
theorem _root_.Convex.isBounded_of_interior_nonempty_of_volume_lt_top {C : Set V}
    (hC : Convex ℝ C) (hint : (interior C).Nonempty) (hfin : volume C < ⊤) :
    Bornology.IsBounded C :=
  hC.isBounded_of_interior_nonempty_of_measure_lt_top hint hfin

/-- **Every convex set in `V` with `0 < volume C` and `volume C < ⊤` is bounded**. -/
theorem _root_.Convex.isBounded_of_volume_pos_of_volume_lt_top {C : Set V} (hC : Convex ℝ C)
    (hpos : 0 < volume C) (hfin : volume C < ⊤) :
    Bornology.IsBounded C :=
  hC.isBounded_of_measure_pos_of_measure_lt_top hpos hfin

/-- **Every convex set in `V` with `0 < volume C` and `volume C < ⊤` has compact closure**. -/
theorem _root_.Convex.isCompact_closure_of_volume_pos_of_volume_lt_top {C : Set V}
    (hC : Convex ℝ C) (hpos : 0 < volume C) (hfin : volume C < ⊤) :
    IsCompact (closure C) :=
  (hC.isCompact_closure_of_measure_pos_of_measure_lt_top hpos hfin).1

/-- **Compact convex body closure properties** for a convex set `C ⊆ V` with
`0 < volume C` and `volume C < ⊤`: `closure C` is a compact convex body with nonempty interior
whose symmetric difference with `C` has volume `0`, and which has the same volume and Caccioppoli
perimeter as `C`. -/
theorem _root_.Convex.closure_isCompact_and_perimeter_eq {C : Set V} (hC : Convex ℝ C)
    (hpos : 0 < volume C) (hfin : volume C < ⊤) :
    IsCompact (closure C) ∧ Convex ℝ (closure C) ∧ (interior (closure C)).Nonempty ∧
      volume (symmDiff (closure C) C) = 0 ∧ volume (closure C) = volume C ∧
      perimeter volume (closure C) = perimeter volume C := by
  obtain ⟨hcomp, hconv, hint, _, hae, hvol⟩ :=
    hC.isCompact_closure_of_measure_pos_of_measure_lt_top hpos hfin
  have hsymm : volume (symmDiff (closure C) C) = 0 := by
    rw [Set.symmDiff_def, measure_union_null_iff]
    exact ⟨(ae_eq_set.1 hae).1, (ae_eq_set.1 hae).2⟩
  exact ⟨hcomp, hconv, hint, hsymm, hvol, hC.perimeter_closure volume⟩

/-- **Compact convex body representative of an essentially convex set**: for every set `A : Set V`
with `IsEssentiallyConvex A`, `0 < volume A`, and `volume A < ⊤`, there exists a compact convex
body `K ⊆ V` (`K = closure C`) such that:
1. `IsCompact K`, `Convex ℝ K`, and `(interior K).Nonempty`,
2. `volume (symmDiff A K) = 0` (`A =ᵐ[volume] K`),
3. `volume K = volume A`, and
4. `perimeter volume K = perimeter volume A`. -/
theorem IsEssentiallyConvex.exists_isCompact_convex_witness {A : Set V}
    (hA : IsEssentiallyConvex A) (hpos : 0 < volume A) (hfin : volume A < ⊤) :
    ∃ K : Set V, IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      volume (symmDiff A K) = 0 ∧ volume K = volume A ∧
      perimeter volume K = perimeter volume A := by
  obtain ⟨K, hK_comp, hK_conv, hK_int, hAK, hvol, hper, _, _⟩ :=
    hA.exists_isCompact_convex_ae_eq hpos hfin
  have hsymm : volume (symmDiff A K) = 0 := by
    rw [Set.symmDiff_def, measure_union_null_iff]
    exact ⟨(ae_eq_set.1 hAK).1, (ae_eq_set.1 hAK).2⟩
  exact ⟨K, hK_comp, hK_conv, hK_int, hsymm, hvol, hper⟩

end ConvexBoundednessAndCompactWitness

/-! ### Section 3: Steiner perimeter equality forcing and measurable ball rigidity -/

section SteinerEqualityAndBallRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Alias for the sharp Euclidean isoperimetric lower-bound functional `isoperimetricBound s`. -/
abbrev isoperimetricLHS (_μ : Measure E := by volume_tac) (s : Set E) : ℝ≥0∞ :=
  isoperimetricBound s

/-- `volume (symmDiff A B) = 0 ↔ A =ᵐ[volume] B`. -/
theorem volume_symmDiff_eq_zero_iff_ae_eq {A B : Set E} :
    volume (symmDiff A B) = 0 ↔ A =ᵐ[volume] B := by
  rw [Set.symmDiff_def, measure_union_null_iff, ae_eq_set]

/-- If `volume (symmDiff A B) = 0`, then `A =ᵐ[volume] B`. -/
theorem ae_eq_of_volume_symmDiff_eq_zero {A B : Set E} (h : volume (symmDiff A B) = 0) :
    A =ᵐ[volume] B := volume_symmDiff_eq_zero_iff_ae_eq.1 h

/-- If `A =ᵐ[volume] B`, then `volume (symmDiff A B) = 0`. -/
theorem volume_symmDiff_eq_zero_of_ae_eq {A B : Set E} (h : A =ᵐ[volume] B) :
    volume (symmDiff A B) = 0 := volume_symmDiff_eq_zero_iff_ae_eq.2 h

/-- Null-modification invariance of `volume` under `volume (symmDiff A B) = 0`. -/
theorem volume_eq_of_symmDiff_eq_zero {A B : Set E} (h : volume (symmDiff A B) = 0) :
    volume A = volume B := measure_congr (ae_eq_of_volume_symmDiff_eq_zero h)

/-- Null-modification invariance of `perimeter volume` under `volume (symmDiff A B) = 0`. -/
theorem perimeter_eq_of_symmDiff_eq_zero {A B : Set E} (h : volume (symmDiff A B) = 0) :
    perimeter volume A = perimeter volume B :=
  perimeter_congr_ae (ae_eq_of_volume_symmDiff_eq_zero h)

/-- Null-modification invariance of `isoperimetricBound` under `volume (symmDiff A B) = 0`. -/
theorem isoperimetricBound_eq_of_symmDiff_eq_zero {A B : Set E} (h : volume (symmDiff A B) = 0) :
    isoperimetricBound A = isoperimetricBound B :=
  isoperimetricBound_congr_ae (ae_eq_of_volume_symmDiff_eq_zero h)

/-- Null-modification invariance of `isoperimetricDeficit` under `volume (symmDiff A B) = 0`. -/
theorem isoperimetricDeficit_eq_of_symmDiff_eq_zero {A B : Set E} (h : volume (symmDiff A B) = 0) :
    isoperimetricDeficit A = isoperimetricDeficit B :=
  isoperimetricDeficit_congr_ae (ae_eq_of_volume_symmDiff_eq_zero h)

/-- **Abstract symmetral perimeter equality forcing lemma**: if `S` preserves the volume of `A`
(`volume S = volume A`), does not increase perimeter (`perimeter volume S ≤ perimeter volume A`),
and satisfies the Euclidean isoperimetric inequality (`isoperimetricBound S ≤ perimeter volume S`),
and `A` attains isoperimetric equality (`perimeter volume A = isoperimetricBound A`), then
`perimeter volume S = perimeter volume A` and `perimeter volume S = isoperimetricBound S`. -/
theorem perimeter_eq_of_isoperimetricBound_eq {A S : Set E} (hvol : volume S = volume A)
    (hper_le : perimeter volume S ≤ perimeter volume A)
    (hiso : isoperimetricBound S ≤ perimeter volume S)
    (heq : perimeter volume A = isoperimetricBound A) :
    perimeter volume S = perimeter volume A ∧ perimeter volume S = isoperimetricBound S := by
  have hb : isoperimetricBound S = isoperimetricBound A := by simp [isoperimetricBound, hvol]
  have hper_eq : perimeter volume S = perimeter volume A :=
    le_antisymm hper_le (by rw [heq, ← hb]; exact hiso)
  exact ⟨hper_eq, by rw [hper_eq, heq, hb]⟩

/-- **Universal-direction Steiner perimeter equality forcing**: if `A` is null-measurable and
attains `perimeter volume A = isoperimetricBound A`, and for every unit vector `e` (`‖e‖ = 1`)
`perimeter volume (steinerSymmetrization e A) ≤ perimeter volume A` and
`isoperimetricBound (steinerSymmetrization e A) ≤ perimeter volume (steinerSymmetrization e A)`,
then `perimeter volume (steinerSymmetrization e A) = perimeter volume A` for all unit `e`. -/
theorem forall_perimeter_steinerSymmetrization_eq_of_isoperimetricBound_eq {A : Set E}
    (hA : NullMeasurableSet A volume)
    (hrec : ∀ e : E, ‖e‖ = 1 → perimeter volume (steinerSymmetrization e A) ≤ perimeter volume A)
    (hiso : ∀ e : E, ‖e‖ = 1 → isoperimetricBound (steinerSymmetrization e A) ≤
      perimeter volume (steinerSymmetrization e A))
    (heq : perimeter volume A = isoperimetricBound A) :
    ∀ e : E, ‖e‖ = 1 → perimeter volume (steinerSymmetrization e A) = perimeter volume A :=
  fun e he ↦ perimeter_steinerSymmetrization_eq_of_isoperimetricBound_eq he hA
    (hrec e he) (hiso e he) heq

/-- If `volume (symmDiff A K) = 0`, then `A` attains isoperimetric equality if and only if `K`
attains isoperimetric equality. -/
theorem perimeter_eq_isoperimetricBound_iff_of_symmDiff_eq_zero {A K : Set E}
    (hAK : volume (symmDiff A K) = 0) :
    perimeter volume A = isoperimetricBound A ↔ perimeter volume K = isoperimetricBound K := by
  rw [perimeter_eq_of_symmDiff_eq_zero hAK, isoperimetricBound_eq_of_symmDiff_eq_zero hAK]

/-- **Compact convex witness for an essentially convex isoperimetric minimizer**: if
`IsEssentiallyConvex A`, `0 < volume A`, `volume A < ⊤`, and
`perimeter volume A = isoperimetricBound A`, then there exists a compact convex body `K ⊆ E` with
nonempty interior such that `volume (symmDiff A K) = 0`, `volume K = volume A`,
`perimeter volume K = perimeter volume A`, and `perimeter volume K = isoperimetricBound K`. -/
theorem IsEssentiallyConvex.exists_isCompact_convex_isoperimetric_witness {A : Set E}
    (hA : IsEssentiallyConvex A) (hpos : 0 < volume A) (hfin : volume A < ⊤)
    (heq : perimeter volume A = isoperimetricBound A) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      volume (symmDiff A K) = 0 ∧ volume K = volume A ∧ perimeter volume K = perimeter volume A ∧
      perimeter volume K = isoperimetricBound K := by
  obtain ⟨K, hK_comp, hK_conv, hK_int, hAK, hvol, hper⟩ :=
    hA.exists_isCompact_convex_witness hpos hfin
  exact ⟨K, hK_comp, hK_conv, hK_int, hAK, hvol, hper,
    (perimeter_eq_isoperimetricBound_iff_of_symmDiff_eq_zero hAK).1 heq⟩

/-- Every open ball `Metric.ball c r` in `E` is essentially convex. -/
theorem isEssentiallyConvex_ball (c : E) (r : ℝ) : IsEssentiallyConvex (Metric.ball c r) :=
  (convex_ball c r).isEssentiallyConvex

/-- Every closed ball `Metric.closedBall c r` in `E` is essentially convex. -/
theorem isEssentiallyConvex_closedBall (c : E) (r : ℝ) :
    IsEssentiallyConvex (Metric.closedBall c r) := (convex_closedBall c r).isEssentiallyConvex

variable [Nontrivial E]

/-- On a nontrivial finite-dimensional inner product space `E`,
`volume (symmDiff (Metric.closedBall c r) (Metric.ball c r)) = 0`. -/
theorem volume_symmDiff_closedBall_ball (c : E) (r : ℝ) :
    volume (symmDiff (Metric.closedBall c r) (Metric.ball c r)) = 0 :=
  volume_symmDiff_eq_zero_of_ae_eq (closedBall_ae_eq_ball c r)

/-- **Closed-ball-to-open-ball null-difference transfer**: if `volume (symmDiff A K) = 0` and
`K = Metric.closedBall c r`, then `volume (symmDiff A (Metric.ball c r)) = 0` and
`A =ᵐ[volume] Metric.ball c r`. -/
theorem volume_symmDiff_ball_eq_zero_of_eq_closedBall {A K : Set E} {c : E} {r : ℝ}
    (hAK : volume (symmDiff A K) = 0) (hK : K = Metric.closedBall c r) :
    volume (symmDiff A (Metric.ball c r)) = 0 ∧ (A =ᵐ[volume] Metric.ball c r) := by
  subst hK
  have hsymm : volume (symmDiff A (Metric.ball c r)) = 0 :=
    measure_mono_null (symmDiff_triangle A (Metric.closedBall c r) (Metric.ball c r))
      (measure_union_null hAK (volume_symmDiff_closedBall_ball c r))
  exact ⟨hsymm, ae_eq_of_volume_symmDiff_eq_zero hsymm⟩

/-- **Regular open upgrade from closed-ball witness**: if `IsRegularOpen A`,
`volume (symmDiff A K) = 0`, and `K = Metric.closedBall c r`, then `A = Metric.ball c r`. -/
theorem eq_ball_of_isRegularOpen_of_symmDiff_closedBall_eq_zero {A K : Set E} {c : E} {r : ℝ}
    (hA_reg : IsRegularOpen A) (hAK : volume (symmDiff A K) = 0)
    (hK : K = Metric.closedBall c r) :
    A = Metric.ball c r :=
  eq_ball_of_isRegularOpen_of_ae_eq_ball hA_reg
    (volume_symmDiff_ball_eq_zero_of_eq_closedBall hAK hK).2

/-- **Converse measurable ball isoperimetric equality theorem**: if
`volume (symmDiff A (Metric.ball c r)) = 0` with `0 < r`, then `IsEssentiallyConvex A`,
`volume A = volume (Metric.ball c r)`, `perimeter volume A = perimeter volume (Metric.ball c r)`,
`perimeter volume A = isoperimetricBound A`, and `isoperimetricDeficit A = 0`. -/
theorem isEssentiallyConvex_and_isoperimetric_eq_of_symmDiff_ball_eq_zero {A : Set E} {c : E}
    {r : ℝ} (hr : 0 < r) (hA : volume (symmDiff A (Metric.ball c r)) = 0) :
    IsEssentiallyConvex A ∧
      volume A = volume (Metric.ball c r) ∧
      perimeter volume A = perimeter volume (Metric.ball c r) ∧
      perimeter volume A = isoperimetricBound A ∧
      isoperimetricDeficit A = 0 := by
  have hae : A =ᵐ[volume] Metric.ball c r := ae_eq_of_volume_symmDiff_eq_zero hA
  have hconv : IsEssentiallyConvex A := (isEssentiallyConvex_ball c r).mono_ae hae.symm
  have hvol : volume A = volume (Metric.ball c r) := volume_eq_of_symmDiff_eq_zero hA
  have hper : perimeter volume A = perimeter volume (Metric.ball c r) :=
    perimeter_eq_of_symmDiff_eq_zero hA
  have hiso : perimeter volume A = isoperimetricBound A :=
    (perimeter_eq_isoperimetricBound_iff_of_symmDiff_eq_zero hA).2
      (perimeter_ball_eq_isoperimetricBound c hr)
  exact ⟨hconv, hvol, hper, hiso, isoperimetricDeficit_eq_zero_of_perimeter_eq hiso⟩

/-- **Converse measurable ball isoperimetric equality theorem (`=ᵐ[volume]` form)**. -/
theorem isEssentiallyConvex_and_isoperimetric_eq_of_ae_eq_ball {A : Set E} {c : E} {r : ℝ}
    (hr : 0 < r) (hA : A =ᵐ[volume] Metric.ball c r) :
    IsEssentiallyConvex A ∧
      volume A = volume (Metric.ball c r) ∧
      perimeter volume A = perimeter volume (Metric.ball c r) ∧
      perimeter volume A = isoperimetricBound A ∧
      isoperimetricDeficit A = 0 :=
  isEssentiallyConvex_and_isoperimetric_eq_of_symmDiff_ball_eq_zero hr
    (volume_symmDiff_eq_zero_of_ae_eq hA)

/-- **Measurable essentially-convex ball rigidity equivalence**: if `A : Set E` is essentially
convex with `0 < volume A` and `volume A < ⊤`, and every compact convex body `K` with nonempty
interior attaining `perimeter volume K = isoperimetricBound K` is a closed ball of positive radius,
then `perimeter volume A = isoperimetricBound A` if and only if there exist `c : E` and `r > 0`
such that `volume (symmDiff A (Metric.ball c r)) = 0` (`A =ᵐ[volume] Metric.ball c r`). -/
theorem IsEssentiallyConvex.perimeter_eq_isoperimetricBound_iff_exists_ball {A : Set E}
    (hA : IsEssentiallyConvex A) (hpos : 0 < volume A) (hfin : volume A < ⊤)
    (h_rig : ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      perimeter volume K = isoperimetricBound K →
      ∃ c : E, ∃ r > 0, K = Metric.closedBall c r) :
    perimeter volume A = isoperimetricBound A ↔
      ∃ c : E, ∃ r > 0, volume (symmDiff A (Metric.ball c r)) = 0 := by
  constructor
  · intro heq
    obtain ⟨K, hK_comp, hK_conv, hK_int, hAK, -, -, hK_eq⟩ :=
      hA.exists_isCompact_convex_isoperimetric_witness hpos hfin heq
    obtain ⟨c, r, hr, hK_ball⟩ := h_rig K hK_comp hK_conv hK_int hK_eq
    exact ⟨c, r, hr, (volume_symmDiff_ball_eq_zero_of_eq_closedBall hAK hK_ball).1⟩
  · rintro ⟨c, r, hr, hball⟩
    exact (isEssentiallyConvex_and_isoperimetric_eq_of_symmDiff_ball_eq_zero hr hball).2.2.2.1

/-- `=ᵐ[volume]` form of `IsEssentiallyConvex.perimeter_eq_isoperimetricBound_iff_exists_ball`. -/
theorem IsEssentiallyConvex.perimeter_eq_isoperimetricBound_iff_exists_ae_eq_ball {A : Set E}
    (hA : IsEssentiallyConvex A) (hpos : 0 < volume A) (hfin : volume A < ⊤)
    (h_rig : ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      perimeter volume K = isoperimetricBound K →
      ∃ c : E, ∃ r > 0, K = Metric.closedBall c r) :
    perimeter volume A = isoperimetricBound A ↔
      ∃ c : E, ∃ r > 0, A =ᵐ[volume] Metric.ball c r := by
  rw [hA.perimeter_eq_isoperimetricBound_iff_exists_ball hpos hfin h_rig]
  simp_rw [volume_symmDiff_eq_zero_iff_ae_eq]

end SteinerEqualityAndBallRigidity

end TauCeti
