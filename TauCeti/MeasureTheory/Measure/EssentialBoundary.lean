/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Measure-Theoretic Density, Essential Interior, Essential Exterior, and Essential Boundary

This file defines measure-theoretic density of sets at a point in a pseudo-metric measure space,
together with the essential interior, essential exterior, and essential boundary (also known as
the measure-theoretic boundary). We establish their basic properties, exact invariance under
`μ`-almost everywhere (`=ᵐ[μ]`) modifications, complement symmetry for null-measurable sets,
comparisons with the topological interior, closure, and frontier, the Lebesgue density theorem on
Besicovitch covering spaces and finite-dimensional real normed spaces, and concrete comparisons on
punctured balls and balls perturbed by null dense sets.

## Main definitions

* `TauCeti.MeasureTheory.HasMeasureDensityAt`: `HasMeasureDensityAt μ s x d` states that the ball
  density ratio `μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r)` tends to `d : ℝ≥0∞` as
  `r → 0⁺` (`𝓝[>] 0`).
* `TauCeti.MeasureTheory.essentialInterior`: the set of points `x` where `s` has measure-theoretic
  density `1` (`HasMeasureDensityAt μ s x 1`).
* `TauCeti.MeasureTheory.essentialExterior`: the set of points `x` where `s` has measure-theoretic
  density `0` (`HasMeasureDensityAt μ s x 0`).
* `TauCeti.MeasureTheory.essentialBoundary`: the complement
  `(essentialInterior μ s ∪ essentialExterior μ s)ᶜ`, consisting of points where `s` has neither
  density `1` nor density `0`.

## Main results

* `TauCeti.MeasureTheory.hasMeasureDensityAt_congr_ae`, `essentialInterior_congr_ae`,
  `essentialExterior_congr_ae`, and `essentialBoundary_congr_ae`: exact invariance under `=ᵐ[μ]`
  null modifications.
* `TauCeti.MeasureTheory.hasMeasureDensityAt_iff_tendsto_ball` and
  `hasMeasureDensityAt_iff_tendsto_ball_of_isAddHaarMeasure`: equivalence between closed-ball and
  open-ball density ratios when spheres of small positive radius are `μ`-null.
* `TauCeti.MeasureTheory.essentialInterior_compl`, `essentialExterior_compl`, and
  `essentialBoundary_compl`: complement symmetry for null-measurable sets.
* `TauCeti.MeasureTheory.interior_subset_essentialInterior`,
  `compl_closure_subset_essentialExterior`, `essentialInterior_subset_closure`, and
  `essentialBoundary_subset_frontier`: inclusions relating measure-theoretic and topological
  interior, closure, and boundary.
* `TauCeti.MeasureTheory.ae_hasMeasureDensityAt_one`, `ae_hasMeasureDensityAt_zero`,
  `essentialInterior_ae_eq`, `essentialExterior_ae_eq`, and `measure_essentialBoundary_eq_zero`:
  Lebesgue density theorem and vanishing measure of the essential boundary of any null-measurable
  set.
* `TauCeti.MeasureTheory.essentialBoundary_punctured_ball_ssubset_frontier` and
  `essentialBoundary_ball_union_ssubset_frontier_of_null_of_dense`: explicit examples showing that
  the essential boundary is invariant under removing the center of a ball or adding a null dense
  set, whereas the topological frontier strictly enlarges.
-/

public section

noncomputable section

open MeasureTheory Measure Set Filter Metric
open scoped ENNReal NNReal Topology

namespace TauCeti.MeasureTheory

/-!
### Definitions and basic properties of measure-theoretic density
-/

section Definitions

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- A set `s : Set X` has measure-theoretic density `d : ℝ≥0∞` at `x : X` with respect to a
measure `μ` if `μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) → d` as `r → 0⁺`. -/
def HasMeasureDensityAt (μ : Measure X) (s : Set X) (x : X) (d : ℝ≥0∞) : Prop :=
  Tendsto (fun r : ℝ ↦ μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 d)

/-- The **essential interior** (or measure-theoretic interior) of `s : Set X` with respect to `μ`
is the set of points where `s` has measure-theoretic density `1`. -/
def essentialInterior (μ : Measure X) (s : Set X) : Set X := {x : X | HasMeasureDensityAt μ s x 1}

/-- The **essential exterior** (or measure-theoretic exterior) of `s : Set X` with respect to `μ`
is the set of points where `s` has measure-theoretic density `0`. -/
def essentialExterior (μ : Measure X) (s : Set X) : Set X := {x : X | HasMeasureDensityAt μ s x 0}

/-- The **essential boundary** (or measure-theoretic boundary) of `s : Set X` with respect to `μ`
is the complement of the union of the essential interior and the essential exterior. -/
def essentialBoundary (μ : Measure X) (s : Set X) : Set X :=
  (essentialInterior μ s ∪ essentialExterior μ s)ᶜ

theorem hasMeasureDensityAt_iff {μ : Measure X} {s : Set X} {x : X} {d : ℝ≥0∞} :
    HasMeasureDensityAt μ s x d ↔
      Tendsto (fun r : ℝ ↦ μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 d) := by rfl

@[simp] theorem mem_essentialInterior_iff {μ : Measure X} {s : Set X} {x : X} :
    x ∈ essentialInterior μ s ↔ HasMeasureDensityAt μ s x 1 := by rfl

@[simp] theorem mem_essentialExterior_iff {μ : Measure X} {s : Set X} {x : X} :
    x ∈ essentialExterior μ s ↔ HasMeasureDensityAt μ s x 0 := by rfl

theorem essentialBoundary_def (μ : Measure X) (s : Set X) :
    essentialBoundary μ s = (essentialInterior μ s ∪ essentialExterior μ s)ᶜ := by rfl

theorem essentialBoundary_eq_compl_inter_compl (μ : Measure X) (s : Set X) :
    essentialBoundary μ s = (essentialInterior μ s)ᶜ ∩ (essentialExterior μ s)ᶜ :=
  compl_union _ _

@[simp] theorem mem_essentialBoundary_iff {μ : Measure X} {s : Set X} {x : X} :
    x ∈ essentialBoundary μ s ↔ ¬HasMeasureDensityAt μ s x 1 ∧ ¬HasMeasureDensityAt μ s x 0 := by
  rw [essentialBoundary_eq_compl_inter_compl, mem_inter_iff, mem_compl_iff, mem_compl_iff,
    mem_essentialInterior_iff, mem_essentialExterior_iff]

theorem notMem_essentialBoundary_iff {μ : Measure X} {s : Set X} {x : X} :
    x ∉ essentialBoundary μ s ↔ x ∈ essentialInterior μ s ∨ x ∈ essentialExterior μ s := by
  rw [essentialBoundary_def, notMem_compl_iff, mem_union]

theorem disjoint_essentialBoundary_essentialInterior (μ : Measure X) (s : Set X) :
    Disjoint (essentialBoundary μ s) (essentialInterior μ s) :=
  disjoint_compl_left.mono_right subset_union_left

theorem disjoint_essentialBoundary_essentialExterior (μ : Measure X) (s : Set X) :
    Disjoint (essentialBoundary μ s) (essentialExterior μ s) :=
  disjoint_compl_left.mono_right subset_union_right

theorem essentialInterior_union_essentialExterior_union_essentialBoundary
    (μ : Measure X) (s : Set X) :
    essentialInterior μ s ∪ essentialExterior μ s ∪ essentialBoundary μ s = Set.univ :=
  union_compl_self _

namespace HasMeasureDensityAt

/-- Measure-theoretic density at a point is unique. -/
theorem unique {μ : Measure X} {s : Set X} {x : X} {d₁ d₂ : ℝ≥0∞}
    (h₁ : HasMeasureDensityAt μ s x d₁) (h₂ : HasMeasureDensityAt μ s x d₂) : d₁ = d₂ :=
  tendsto_nhds_unique h₁ h₂

/-- Any measure-theoretic density value `d` satisfies `d ≤ 1`. -/
theorem le_one {μ : Measure X} {s : Set X} {x : X} {d : ℝ≥0∞}
    (h : HasMeasureDensityAt μ s x d) : d ≤ 1 :=
  le_of_tendsto' h fun _ ↦
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)

/-- Measure-theoretic density is monotone with respect to set inclusion. -/
theorem le_of_subset {μ : Measure X} {s t : Set X} {x : X} {d₁ d₂ : ℝ≥0∞}
    (h₁ : HasMeasureDensityAt μ s x d₁) (h₂ : HasMeasureDensityAt μ t x d₂) (hst : s ⊆ t) :
    d₁ ≤ d₂ :=
  le_of_tendsto_of_tendsto' h₁ h₂ fun _ ↦
    ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ hst)) _

/-- If `s ⊆ t` and `s` has measure-theoretic density `1` at `x`, then `t` also has
measure-theoretic density `1` at `x`. -/
theorem mono_one {μ : Measure X} {s t : Set X} {x : X}
    (hs : HasMeasureDensityAt μ s x 1) (hst : s ⊆ t) : HasMeasureDensityAt μ t x 1 := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hs tendsto_const_nhds (fun _ ↦ ?_) (fun _ ↦ ?_)
  · exact ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ hst)) _
  · exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)

/-- If `s ⊆ t` and `t` has measure-theoretic density `0` at `x`, then `s` also has
measure-theoretic density `0` at `x`. -/
theorem mono_zero {μ : Measure X} {s t : Set X} {x : X}
    (ht : HasMeasureDensityAt μ t x 0) (hst : s ⊆ t) : HasMeasureDensityAt μ s x 0 :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ _root_.zero_le) fun _ ↦
      ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ hst)) _

end HasMeasureDensityAt

/-- The essential interior and essential exterior of any set are disjoint. -/
theorem disjoint_essentialInterior_essentialExterior (μ : Measure X) (s : Set X) :
    Disjoint (essentialInterior μ s) (essentialExterior μ s) :=
  disjoint_left.mpr fun _ hx₁ hx₀ ↦ one_ne_zero (hx₁.unique hx₀)

theorem essentialInterior_mono {μ : Measure X} {s t : Set X} (hst : s ⊆ t) :
    essentialInterior μ s ⊆ essentialInterior μ t := fun _ hx ↦ hx.mono_one hst

theorem essentialExterior_anti {μ : Measure X} {s t : Set X} (hst : s ⊆ t) :
    essentialExterior μ t ⊆ essentialExterior μ s := fun _ hx ↦ hx.mono_zero hst

theorem hasMeasureDensityAt_empty (μ : Measure X) (x : X) :
    HasMeasureDensityAt μ ∅ x 0 := by simp [HasMeasureDensityAt]

@[simp] theorem essentialExterior_empty (μ : Measure X) : essentialExterior μ ∅ = Set.univ :=
  eq_univ_of_forall (hasMeasureDensityAt_empty μ)

@[simp] theorem essentialInterior_empty (μ : Measure X) : essentialInterior μ ∅ = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ one_ne_zero (hx.unique (hasMeasureDensityAt_empty μ x))

@[simp] theorem essentialBoundary_empty (μ : Measure X) : essentialBoundary μ ∅ = ∅ := by
  simp [essentialBoundary]

/-- Equivalently, `HasMeasureDensityAt` can be tested using open balls `Metric.ball x r` whenever
spheres of small positive radius around `x` have `μ`-measure zero. -/
theorem hasMeasureDensityAt_iff_tendsto_ball {μ : Measure X} {s : Set X} {x : X} {d : ℝ≥0∞}
    (hsphere : ∀ᶠ r in 𝓝[>] 0, μ (Metric.sphere x r) = 0) :
    HasMeasureDensityAt μ s x d ↔
      Tendsto (fun r : ℝ ↦ μ (s ∩ Metric.ball x r) / μ (Metric.ball x r)) (𝓝[>] 0) (𝓝 d) := by
  refine tendsto_congr' ?_
  filter_upwards [hsphere] with r hr
  have hs_sph : μ (s ∩ Metric.sphere x r) = 0 := measure_mono_null inter_subset_right hr
  have hcb : μ (s ∩ Metric.closedBall x r) = μ (s ∩ Metric.ball x r) := by
    rw [← Metric.ball_union_sphere, inter_union_distrib_left]
    exact le_antisymm ((measure_union_le _ _).trans (by simp [hs_sph]))
      (measure_mono subset_union_left)
  have hb : μ (Metric.closedBall x r) = μ (Metric.ball x r) := by
    rw [← Metric.ball_union_sphere]
    exact le_antisymm ((measure_union_le _ _).trans (by simp [hr]))
      (measure_mono subset_union_left)
  rw [hcb, hb]

end Definitions

/-!
### Exact `=ᵐ[μ]` null-modification invariance
-/

section CongruenceAE

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X}

namespace HasMeasureDensityAt

/-- Measure-theoretic density is invariant under `=ᵐ[μ]` modifications of the set. -/
theorem congr_ae {s t : Set X} {x : X} {d : ℝ≥0∞}
    (h : HasMeasureDensityAt μ s x d) (hst : s =ᵐ[μ] t) : HasMeasureDensityAt μ t x d :=
  h.congr fun _ ↦ by rw [measure_congr (hst.inter EventuallyEq.rfl)]

end HasMeasureDensityAt

theorem hasMeasureDensityAt_congr_ae {s t : Set X} {x : X} {d : ℝ≥0∞} (hst : s =ᵐ[μ] t) :
    HasMeasureDensityAt μ s x d ↔ HasMeasureDensityAt μ t x d :=
  ⟨fun h ↦ h.congr_ae hst, fun h ↦ h.congr_ae hst.symm⟩

/-- The essential interior is invariant under `=ᵐ[μ]` modifications. -/
theorem essentialInterior_congr_ae {s t : Set X} (hst : s =ᵐ[μ] t) :
    essentialInterior μ s = essentialInterior μ t := by
  ext x; exact hasMeasureDensityAt_congr_ae hst

/-- The essential exterior is invariant under `=ᵐ[μ]` modifications. -/
theorem essentialExterior_congr_ae {s t : Set X} (hst : s =ᵐ[μ] t) :
    essentialExterior μ s = essentialExterior μ t := by
  ext x; exact hasMeasureDensityAt_congr_ae hst

/-- The essential boundary is invariant under `=ᵐ[μ]` modifications. -/
theorem essentialBoundary_congr_ae {s t : Set X} (hst : s =ᵐ[μ] t) :
    essentialBoundary μ s = essentialBoundary μ t := by
  rw [essentialBoundary, essentialBoundary, essentialInterior_congr_ae hst,
    essentialExterior_congr_ae hst]

theorem hasMeasureDensityAt_of_measure_eq_zero {s : Set X} (hs : μ s = 0) (x : X) :
    HasMeasureDensityAt μ s x 0 :=
  (hasMeasureDensityAt_empty μ x).congr_ae (ae_eq_empty.mpr hs).symm

theorem essentialExterior_of_measure_eq_zero {s : Set X} (hs : μ s = 0) :
    essentialExterior μ s = Set.univ := by
  rw [essentialExterior_congr_ae (ae_eq_empty.mpr hs), essentialExterior_empty]

theorem essentialInterior_of_measure_eq_zero {s : Set X} (hs : μ s = 0) :
    essentialInterior μ s = ∅ := by
  rw [essentialInterior_congr_ae (ae_eq_empty.mpr hs), essentialInterior_empty]

theorem essentialBoundary_of_measure_eq_zero {s : Set X} (hs : μ s = 0) :
    essentialBoundary μ s = ∅ := by
  rw [essentialBoundary_congr_ae (ae_eq_empty.mpr hs), essentialBoundary_empty]

theorem essentialInterior_diff_null (s : Set X) {N : Set X} (hN : μ N = 0) :
    essentialInterior μ (s \ N) = essentialInterior μ s :=
  essentialInterior_congr_ae (sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right hN))

theorem essentialExterior_diff_null (s : Set X) {N : Set X} (hN : μ N = 0) :
    essentialExterior μ (s \ N) = essentialExterior μ s :=
  essentialExterior_congr_ae (sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right hN))

theorem essentialBoundary_diff_null (s : Set X) {N : Set X} (hN : μ N = 0) :
    essentialBoundary μ (s \ N) = essentialBoundary μ s :=
  essentialBoundary_congr_ae (sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right hN))

theorem essentialInterior_union_null (s : Set X) {N : Set X} (hN : μ N = 0) :
    essentialInterior μ (s ∪ N) = essentialInterior μ s :=
  essentialInterior_congr_ae (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hN))

theorem essentialExterior_union_null (s : Set X) {N : Set X} (hN : μ N = 0) :
    essentialExterior μ (s ∪ N) = essentialExterior μ s :=
  essentialExterior_congr_ae (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hN))

theorem essentialBoundary_union_null (s : Set X) {N : Set X} (hN : μ N = 0) :
    essentialBoundary μ (s ∪ N) = essentialBoundary μ s :=
  essentialBoundary_congr_ae (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hN))

end CongruenceAE

/-!
### Locally finite open-positive measures, complement symmetry, and topological comparisons
-/

section LocallyFiniteOpenPos

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X}

theorem eventually_measure_closedBall_ne_zero [IsOpenPosMeasure μ] (x : X) :
    ∀ᶠ r in 𝓝[>] 0, μ (Metric.closedBall x r) ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  exact ne_of_gt ((isOpen_ball.measure_pos μ (nonempty_ball.mpr hr)).trans_le
    (measure_mono ball_subset_closedBall))

theorem eventually_measure_closedBall_lt_top [IsLocallyFiniteMeasure μ] (x : X) :
    ∀ᶠ r in 𝓝[>] 0, μ (Metric.closedBall x r) < ⊤ := by
  rcases (μ.finiteAt_nhds x).exists_mem_basis Metric.nhds_basis_closedBall with ⟨R, hR, hlt⟩
  filter_upwards [Ioc_mem_nhdsGT hR] with r hr
  exact (measure_mono (closedBall_subset_closedBall hr.2)).trans_lt hlt

theorem eventually_measure_closedBall_ne_top [IsLocallyFiniteMeasure μ] (x : X) :
    ∀ᶠ r in 𝓝[>] 0, μ (Metric.closedBall x r) ≠ ⊤ := by
  filter_upwards [eventually_measure_closedBall_lt_top (μ := μ) x] with r hr using hr.ne

theorem hasMeasureDensityAt_univ [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] (x : X) :
    HasMeasureDensityAt μ Set.univ x 1 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_measure_closedBall_ne_zero (μ := μ) x,
    eventually_measure_closedBall_ne_top (μ := μ) x] with r h0 htop
  rw [univ_inter, ENNReal.div_self h0 htop]

@[simp] theorem essentialInterior_univ [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] :
    essentialInterior μ Set.univ = Set.univ :=
  eq_univ_of_forall hasMeasureDensityAt_univ

@[simp] theorem essentialExterior_univ [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] :
    essentialExterior μ Set.univ = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ one_ne_zero ((hasMeasureDensityAt_univ x).unique hx)

@[simp] theorem essentialBoundary_univ [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ] :
    essentialBoundary μ Set.univ = ∅ := by simp [essentialBoundary]

/-- For a null-measurable set `s`, the ball density ratios of `s` and `sᶜ` sum to `1` for all
sufficiently small `r > 0`. -/
theorem eventually_measure_inter_div_add_compl [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    {s : Set X} (hs : NullMeasurableSet s μ) (x : X) :
    ∀ᶠ r in 𝓝[>] 0,
      μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) +
        μ (sᶜ ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) = 1 := by
  filter_upwards [eventually_measure_closedBall_ne_zero (μ := μ) x,
    eventually_measure_closedBall_ne_top (μ := μ) x] with r h0 htop
  rw [← ENNReal.add_div, inter_comm s, ← sdiff_eq_compl_inter, measure_inter_add_sdiff₀ _ hs,
    ENNReal.div_self h0 htop]

/-- If `s` is null-measurable and has density `d` at `x`, then `sᶜ` has density `1 - d` at `x`. -/
theorem HasMeasureDensityAt.compl [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    {s : Set X} (hs : NullMeasurableSet s μ) {x : X} {d : ℝ≥0∞}
    (h : HasMeasureDensityAt μ s x d) : HasMeasureDensityAt μ sᶜ x (1 - d) := by
  have hsub : Tendsto
      (fun r : ℝ ↦ 1 - μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 (1 - d)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
  refine hsub.congr' ?_
  filter_upwards [eventually_measure_inter_div_add_compl hs x] with r hr
  rw [← hr, add_comm, ENNReal.add_sub_cancel_right]
  exact ne_of_lt (lt_of_le_of_lt
    (ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right))
    ENNReal.one_lt_top)

theorem hasMeasureDensityAt_compl_zero_iff [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    {s : Set X} (hs : NullMeasurableSet s μ) {x : X} :
    HasMeasureDensityAt μ sᶜ x 0 ↔ HasMeasureDensityAt μ s x 1 :=
  ⟨fun h ↦ by simpa using (h.compl hs.compl).congr_ae (by rw [compl_compl]),
    fun h ↦ by simpa using h.compl hs⟩

theorem hasMeasureDensityAt_compl_one_iff [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    {s : Set X} (hs : NullMeasurableSet s μ) {x : X} :
    HasMeasureDensityAt μ sᶜ x 1 ↔ HasMeasureDensityAt μ s x 0 := by
  rw [← hasMeasureDensityAt_compl_zero_iff hs.compl, compl_compl]

/-- For a null-measurable set `s`, `essentialInterior μ sᶜ = essentialExterior μ s`. -/
theorem essentialInterior_compl [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    {s : Set X} (hs : NullMeasurableSet s μ) :
    essentialInterior μ sᶜ = essentialExterior μ s := by
  ext x; exact hasMeasureDensityAt_compl_one_iff hs

/-- For a null-measurable set `s`, `essentialExterior μ sᶜ = essentialInterior μ s`. -/
theorem essentialExterior_compl [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    {s : Set X} (hs : NullMeasurableSet s μ) :
    essentialExterior μ sᶜ = essentialInterior μ s := by
  ext x; exact hasMeasureDensityAt_compl_zero_iff hs

/-- For a null-measurable set `s`, `essentialBoundary μ sᶜ = essentialBoundary μ s`. -/
theorem essentialBoundary_compl [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    {s : Set X} (hs : NullMeasurableSet s μ) :
    essentialBoundary μ sᶜ = essentialBoundary μ s := by
  rw [essentialBoundary, essentialBoundary, essentialInterior_compl hs, essentialExterior_compl hs,
    union_comm]

/-- Every point of the topological interior of `s` belongs to the essential interior of `s`. -/
theorem interior_subset_essentialInterior [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    (s : Set X) : interior s ⊆ essentialInterior μ s := by
  intro x hx
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hx) with
    ⟨R, hR, hsub⟩
  refine (hasMeasureDensityAt_univ (μ := μ) x).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hR] with r hr
  rw [univ_inter, inter_eq_right.mpr ((closedBall_subset_closedBall hr.2).trans hsub)]

/-- Every point outside the topological closure of `s` belongs to the essential exterior of `s`. -/
theorem compl_closure_subset_essentialExterior (s : Set X) :
    (closure s)ᶜ ⊆ essentialExterior μ s := by
  intro x hx
  rw [← interior_compl] at hx
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hx) with
    ⟨R, hR, hsub⟩
  refine (hasMeasureDensityAt_empty μ x).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hR] with r hr
  have hemp : s ∩ Metric.closedBall x r = ∅ :=
    disjoint_iff_inter_eq_empty.mp (disjoint_compl_right.mono_right
      ((closedBall_subset_closedBall hr.2).trans hsub))
  rw [hemp, empty_inter]

/-- The essential interior of `s` is contained in the topological closure of `s`. -/
theorem essentialInterior_subset_closure (s : Set X) :
    essentialInterior μ s ⊆ closure s := by
  rw [← compl_subset_compl]
  exact (compl_closure_subset_essentialExterior s).trans
    (disjoint_essentialInterior_essentialExterior μ s).subset_compl_left

/-- The essential exterior of `s` is contained in the complement of `interior s`. -/
theorem essentialExterior_subset_compl_interior [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    (s : Set X) : essentialExterior μ s ⊆ (interior s)ᶜ := by
  rw [subset_compl_comm]
  exact (interior_subset_essentialInterior s).trans
    (disjoint_essentialInterior_essentialExterior μ s).subset_compl_right

/-- The essential boundary of `s` is always contained in the topological frontier of `s`. -/
theorem essentialBoundary_subset_frontier [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    (s : Set X) : essentialBoundary μ s ⊆ frontier s := by
  intro x hx
  rw [mem_essentialBoundary_iff] at hx
  exact ⟨of_not_not fun hcl ↦ hx.2 (compl_closure_subset_essentialExterior s hcl),
    fun hint ↦ hx.1 (interior_subset_essentialInterior s hint)⟩

/-!
### Set operations on essential interior, exterior, and boundary
-/

/-- If `s` and `t` both have density `0` at `x`, then `s ∪ t` has density `0` at `x`. -/
theorem HasMeasureDensityAt.union_zero {s t : Set X} {x : X}
    (hs : HasMeasureDensityAt μ s x 0) (ht : HasMeasureDensityAt μ t x 0) :
    HasMeasureDensityAt μ (s ∪ t) x 0 := by
  have hsum : Tendsto
      (fun r : ℝ ↦ μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) +
        μ (t ∩ Metric.closedBall x r) / μ (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by simpa using hs.add ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ _root_.zero_le) fun _ ↦ ?_
  rw [← ENNReal.add_div, union_inter_distrib_right]
  exact ENNReal.div_le_div_right (measure_union_le _ _) _

/-- The essential exterior of `s ∪ t` equals the intersection of the essential exteriors. -/
theorem essentialExterior_union (s t : Set X) :
    essentialExterior μ (s ∪ t) = essentialExterior μ s ∩ essentialExterior μ t :=
  Subset.antisymm
    (subset_inter (essentialExterior_anti subset_union_left)
      (essentialExterior_anti subset_union_right))
    (fun _ ⟨hs, ht⟩ ↦ hs.union_zero ht)

theorem essentialInterior_union_subset (s t : Set X) :
    essentialInterior μ s ∪ essentialInterior μ t ⊆ essentialInterior μ (s ∪ t) :=
  union_subset (essentialInterior_mono subset_union_left)
    (essentialInterior_mono subset_union_right)

theorem essentialExterior_inter_subset (s t : Set X) :
    essentialExterior μ s ∪ essentialExterior μ t ⊆ essentialExterior μ (s ∩ t) :=
  union_subset (essentialExterior_anti inter_subset_left)
    (essentialExterior_anti inter_subset_right)

/-- If `s` and `t` both have measure-theoretic density `1` at `x` and `t` is null-measurable, then
`s ∩ t` has measure-theoretic density `1` at `x`. -/
theorem HasMeasureDensityAt.inter_one [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    {s t : Set X} (ht_meas : NullMeasurableSet t μ) {x : X}
    (hs : HasMeasureDensityAt μ s x 1) (ht : HasMeasureDensityAt μ t x 1) :
    HasMeasureDensityAt μ (s ∩ t) x 1 := by
  have htc : HasMeasureDensityAt μ tᶜ x 0 := (hasMeasureDensityAt_compl_zero_iff ht_meas).mpr ht
  have hdiff : Tendsto
      (fun r : ℝ ↦ μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) -
        μ (tᶜ ∩ Metric.closedBall x r) / μ (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub hs htc (Or.inr ENNReal.zero_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hdiff tendsto_const_nhds (fun r ↦ ?_)
    (fun _ ↦ ?_)
  · refine tsub_le_iff_right.mpr ?_
    rw [← ENNReal.add_div]
    refine ENNReal.div_le_div_right ?_ _
    have hsub : s ∩ Metric.closedBall x r ⊆
        ((s ∩ t) ∩ Metric.closedBall x r) ∪ (tᶜ ∩ Metric.closedBall x r) := fun y ⟨hys, hyB⟩ ↦
      (em (y ∈ t)).elim (fun hyt ↦ Or.inl ⟨⟨hys, hyt⟩, hyB⟩) (fun hyt ↦ Or.inr ⟨hyt, hyB⟩)
    exact (measure_mono hsub).trans (measure_union_le _ _)
  · exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)

/-- When `t` is null-measurable, `essentialInterior μ (s ∩ t)` is the intersection of the essential
interiors. -/
theorem essentialInterior_inter [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    (s : Set X) {t : Set X} (ht : NullMeasurableSet t μ) :
    essentialInterior μ (s ∩ t) = essentialInterior μ s ∩ essentialInterior μ t :=
  Subset.antisymm
    (subset_inter (essentialInterior_mono inter_subset_left)
      (essentialInterior_mono inter_subset_right))
    (fun _ ⟨hxs, hxt⟩ ↦ hxs.inter_one ht hxt)

/-- The essential boundary of a union is contained in the union of the essential boundaries. -/
theorem essentialBoundary_union_subset (s t : Set X) :
    essentialBoundary μ (s ∪ t) ⊆ essentialBoundary μ s ∪ essentialBoundary μ t := by
  intro x hx
  rw [mem_essentialBoundary_iff] at hx
  rw [mem_union]
  by_contra! h
  rcases notMem_essentialBoundary_iff.mp h.1 with hxs1 | hxs0
  · exact hx.1 (essentialInterior_union_subset s t (Or.inl hxs1))
  · rcases notMem_essentialBoundary_iff.mp h.2 with hxt1 | hxt0
    · exact hx.1 (essentialInterior_union_subset s t (Or.inr hxt1))
    · exact hx.2 (by rw [← mem_essentialExterior_iff, essentialExterior_union]; exact ⟨hxs0, hxt0⟩)

/-- When `t` is null-measurable, the essential boundary of `s ∩ t` is contained in the union of the
essential boundaries of `s` and `t`. -/
theorem essentialBoundary_inter_subset [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    (s : Set X) {t : Set X} (ht : NullMeasurableSet t μ) :
    essentialBoundary μ (s ∩ t) ⊆ essentialBoundary μ s ∪ essentialBoundary μ t := by
  intro x hx
  rw [mem_essentialBoundary_iff] at hx
  rw [mem_union]
  by_contra! h
  rcases notMem_essentialBoundary_iff.mp h.1 with hxs1 | hxs0
  · rcases notMem_essentialBoundary_iff.mp h.2 with hxt1 | hxt0
    · have h1 : x ∈ essentialInterior μ (s ∩ t) := by
        rw [essentialInterior_inter s ht]; exact ⟨hxs1, hxt1⟩
      exact hx.1 h1
    · exact hx.2 (essentialExterior_inter_subset s t (Or.inr hxt0))
  · exact hx.2 (essentialExterior_inter_subset s t (Or.inl hxs0))

/-- When `t` is null-measurable, the essential boundary of `s \ t` is contained in the union of the
essential boundaries of `s` and `t`. -/
theorem essentialBoundary_diff_subset [IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    (s : Set X) {t : Set X} (ht : NullMeasurableSet t μ) :
    essentialBoundary μ (s \ t) ⊆ essentialBoundary μ s ∪ essentialBoundary μ t := by
  rw [sdiff_eq, ← essentialBoundary_compl ht]
  exact essentialBoundary_inter_subset s ht.compl

end LocallyFiniteOpenPos

/-!
### Lebesgue density theorem on Besicovitch spaces and finite-dimensional normed spaces
-/

section LebesgueDensity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X] {μ : Measure X} [IsLocallyFiniteMeasure μ]

/-- **Lebesgue density theorem** (indicator form): for any null-measurable set `s`, at `μ`-almost
every `x`, `s` has measure-theoretic density `s.indicator 1 x` at `x`. -/
theorem ae_hasMeasureDensityAt_indicator {s : Set X} (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, HasMeasureDensityAt μ s x (s.indicator 1 x) := by
  let t := toMeasurable μ s
  have hst : s =ᵐ[μ] t := hs.toMeasurable_ae_eq.symm
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet μ
    (measurableSet_toMeasurable μ s), hst.mem_iff] with x hx hxt
  have hind : t.indicator (1 : X → ℝ≥0∞) x = s.indicator 1 x := by
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem (hxt.mp hxs), indicator_of_mem hxs]
    · rw [indicator_of_notMem (fun h ↦ hxs (hxt.mpr h)), indicator_of_notMem hxs]
  rw [hind] at hx
  exact HasMeasureDensityAt.congr_ae hx hst.symm

/-- **Lebesgue density theorem** (interior points): for any set `s`, `μ`-almost every point of `s`
belongs to `essentialInterior μ s`. -/
theorem ae_restrict_hasMeasureDensityAt_one (s : Set X) :
    ∀ᵐ x ∂μ.restrict s, HasMeasureDensityAt μ s x 1 :=
  Besicovitch.ae_tendsto_measure_inter_div μ s

/-- For a null-measurable set `s`, `μ`-almost every `x ∈ s` has measure-theoretic density `1`. -/
theorem ae_hasMeasureDensityAt_one {s : Set X} (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, x ∈ s → HasMeasureDensityAt μ s x 1 := by
  filter_upwards [ae_hasMeasureDensityAt_indicator hs] with x hx hxs
  rwa [indicator_of_mem hxs, Pi.one_apply] at hx

/-- For a null-measurable set `s`, `μ`-almost every `x ∉ s` has measure-theoretic density `0`. -/
theorem ae_hasMeasureDensityAt_zero {s : Set X} (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, x ∉ s → HasMeasureDensityAt μ s x 0 := by
  filter_upwards [ae_hasMeasureDensityAt_indicator hs] with x hx hxs
  rwa [indicator_of_notMem hxs] at hx

/-- For a null-measurable set `s`, `essentialBoundary μ s` has `μ`-measure zero. -/
theorem measure_essentialBoundary_eq_zero {s : Set X} (hs : NullMeasurableSet s μ) :
    μ (essentialBoundary μ s) = 0 := by
  refine measure_mono_null (fun x hx ↦ hx) (ae_iff.mp ?_)
  filter_upwards [ae_hasMeasureDensityAt_one hs, ae_hasMeasureDensityAt_zero hs] with x hx1 hx0
  exact (em (x ∈ s)).elim (fun hxs ↦ Or.inl (hx1 hxs)) (fun hxs ↦ Or.inr (hx0 hxs))

/-- For a null-measurable set `s`, `essentialInterior μ s =ᵐ[μ] s`. -/
theorem essentialInterior_ae_eq {s : Set X} (hs : NullMeasurableSet s μ) :
    essentialInterior μ s =ᵐ[μ] s := by
  filter_upwards [ae_hasMeasureDensityAt_one hs, ae_hasMeasureDensityAt_zero hs] with x hx1 hx0
  simp only [eq_iff_iff, mem_essentialInterior_iff]
  exact ⟨fun h1 ↦ by_contra fun hxs ↦ one_ne_zero (h1.unique (hx0 hxs)), hx1⟩

/-- For a null-measurable set `s`, `essentialExterior μ s =ᵐ[μ] sᶜ`. -/
theorem essentialExterior_ae_eq {s : Set X} (hs : NullMeasurableSet s μ) :
    essentialExterior μ s =ᵐ[μ] sᶜ := by
  filter_upwards [ae_hasMeasureDensityAt_one hs, ae_hasMeasureDensityAt_zero hs] with x hx1 hx0
  simp only [eq_iff_iff, mem_essentialExterior_iff, mem_compl_iff]
  exact ⟨fun h0 hxs ↦ one_ne_zero ((hx1 hxs).unique h0), hx0⟩

/-- For a null-measurable set `s`, `essentialInterior μ s` is null-measurable. -/
theorem nullMeasurableSet_essentialInterior {s : Set X} (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (essentialInterior μ s) μ :=
  hs.congr (essentialInterior_ae_eq hs).symm

/-- For a null-measurable set `s`, `essentialExterior μ s` is null-measurable. -/
theorem nullMeasurableSet_essentialExterior {s : Set X} (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (essentialExterior μ s) μ :=
  hs.compl.congr (essentialExterior_ae_eq hs).symm

/-- For a null-measurable set `s`, `essentialBoundary μ s` is null-measurable. -/
theorem nullMeasurableSet_essentialBoundary {s : Set X} (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (essentialBoundary μ s) μ :=
  NullMeasurableSet.of_null (measure_essentialBoundary_eq_zero hs)

end LebesgueDensity

/-!
### Balls, punctured balls, and null-dense perturbations in finite-dimensional normed spaces
-/

section NormedSpaceExamples

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- On a finite-dimensional real normed space with an additive Haar measure `μ`, measure-theoretic
density can be computed using open balls `Metric.ball x r`. -/
theorem hasMeasureDensityAt_iff_tendsto_ball_of_isAddHaarMeasure {s : Set E} {x : E} {d : ℝ≥0∞} :
    HasMeasureDensityAt μ s x d ↔
      Tendsto (fun r : ℝ ↦ μ (s ∩ Metric.ball x r) / μ (Metric.ball x r)) (𝓝[>] 0) (𝓝 d) := by
  refine hasMeasureDensityAt_iff_tendsto_ball ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  exact addHaar_sphere_of_ne_zero μ x hr.ne'

omit [BorelSpace E] in
/-- The open ball `Metric.ball c r` is contained in its essential interior. -/
theorem ball_subset_essentialInterior_ball (c : E) (r : ℝ) :
    Metric.ball c r ⊆ essentialInterior μ (Metric.ball c r) := by
  simpa [isOpen_ball.interior_eq] using interior_subset_essentialInterior (μ := μ) (Metric.ball c r)

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The complement of `Metric.closedBall c r` (`r ≠ 0`) is contained in the essential exterior of
`Metric.ball c r`. -/
theorem compl_closedBall_subset_essentialExterior_ball (c : E) {r : ℝ} (hr : r ≠ 0) :
    (Metric.closedBall c r)ᶜ ⊆ essentialExterior μ (Metric.ball c r) := by
  simpa [closure_ball c hr] using compl_closure_subset_essentialExterior (μ := μ) (Metric.ball c r)

omit [BorelSpace E] in
/-- The essential boundary of `Metric.ball c r` (`r ≠ 0`) is contained in `Metric.sphere c r`. -/
theorem essentialBoundary_ball_subset_sphere (c : E) {r : ℝ} (hr : r ≠ 0) :
    essentialBoundary μ (Metric.ball c r) ⊆ Metric.sphere c r := by
  simpa [frontier_ball c hr] using essentialBoundary_subset_frontier (μ := μ) (Metric.ball c r)

/-- On a nontrivial finite-dimensional real normed space, `Metric.closedBall c r` and
`Metric.ball c r` are `=ᵐ[μ]`-equal. -/
theorem closedBall_ae_eq_ball [Nontrivial E] (c : E) (r : ℝ) :
    Metric.closedBall c r =ᵐ[μ] Metric.ball c r := by
  rw [← Metric.ball_union_sphere]
  exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr (addHaar_sphere μ c r))

theorem essentialInterior_closedBall_eq_ball [Nontrivial E] (c : E) (r : ℝ) :
    essentialInterior μ (Metric.closedBall c r) = essentialInterior μ (Metric.ball c r) :=
  essentialInterior_congr_ae (closedBall_ae_eq_ball c r)

theorem essentialExterior_closedBall_eq_ball [Nontrivial E] (c : E) (r : ℝ) :
    essentialExterior μ (Metric.closedBall c r) = essentialExterior μ (Metric.ball c r) :=
  essentialExterior_congr_ae (closedBall_ae_eq_ball c r)

theorem essentialBoundary_closedBall_eq_ball [Nontrivial E] (c : E) (r : ℝ) :
    essentialBoundary μ (Metric.closedBall c r) = essentialBoundary μ (Metric.ball c r) :=
  essentialBoundary_congr_ae (closedBall_ae_eq_ball c r)

/-- Removing the center `c` from `Metric.ball c r` in a nontrivial normed space yields an
`=ᵐ[μ]`-equivalent set. -/
theorem punctured_ball_ae_eq_ball [Nontrivial E] (c : E) (r : ℝ) :
    (Metric.ball c r \ {c} : Set E) =ᵐ[μ] Metric.ball c r :=
  sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right (measure_singleton c))

/-- The essential interior of `Metric.ball c r \ {c}` equals that of `Metric.ball c r`. -/
theorem essentialInterior_punctured_ball [Nontrivial E] (c : E) (r : ℝ) :
    essentialInterior μ (Metric.ball c r \ {c}) = essentialInterior μ (Metric.ball c r) :=
  essentialInterior_diff_null (Metric.ball c r) (measure_singleton c)

/-- The essential exterior of `Metric.ball c r \ {c}` equals that of `Metric.ball c r`. -/
theorem essentialExterior_punctured_ball [Nontrivial E] (c : E) (r : ℝ) :
    essentialExterior μ (Metric.ball c r \ {c}) = essentialExterior μ (Metric.ball c r) :=
  essentialExterior_diff_null (Metric.ball c r) (measure_singleton c)

/-- The essential boundary of `Metric.ball c r \ {c}` equals that of `Metric.ball c r`. -/
theorem essentialBoundary_punctured_ball [Nontrivial E] (c : E) (r : ℝ) :
    essentialBoundary μ (Metric.ball c r \ {c}) = essentialBoundary μ (Metric.ball c r) :=
  essentialBoundary_diff_null (Metric.ball c r) (measure_singleton c)

/-- The puncture `c` belongs to the essential interior of `Metric.ball c r \ {c}` for `r > 0`. -/
theorem center_mem_essentialInterior_punctured_ball [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    c ∈ essentialInterior μ (Metric.ball c r \ {c}) := by
  rw [essentialInterior_punctured_ball]
  exact ball_subset_essentialInterior_ball c r (mem_ball_self hr)

/-- The puncture `c` does not belong to `essentialBoundary μ (Metric.ball c r \ {c})` (`r > 0`). -/
theorem center_notMem_essentialBoundary_punctured_ball [Nontrivial E] (c : E) {r : ℝ}
    (hr : 0 < r) : c ∉ essentialBoundary μ (Metric.ball c r \ {c}) :=
  disjoint_right.mp (disjoint_essentialBoundary_essentialInterior μ _)
    (center_mem_essentialInterior_punctured_ball c hr)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- In a nontrivial real normed space, `c ∈ frontier (Metric.ball c r \ {c})` for `r > 0`. -/
theorem center_mem_frontier_punctured_ball [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    c ∈ frontier (Metric.ball c r \ {c}) := by
  refine ⟨Metric.mem_closure_iff.mpr fun ε hε ↦ ?_, fun hc ↦ (interior_subset hc).2 rfl⟩
  let δ : ℝ := min (ε / 2) (r / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) (half_pos hr)
  obtain ⟨v, hv⟩ := exists_norm_eq E hδ.le
  have hvc : c + v ≠ c := by
    intro h
    have hv0 : v = 0 := by simpa using congrArg (fun y ↦ y - c) h
    rw [hv0, norm_zero] at hv
    exact hδ.ne hv
  refine ⟨c + v, ⟨?_, hvc⟩, ?_⟩
  · rw [mem_ball, dist_self_add_left, hv]
    exact (min_le_right _ _).trans_lt (half_lt_self hr)
  · rw [dist_self_add_right, hv]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)

/-- For `r > 0` in a nontrivial finite-dimensional real normed space, the essential boundary of the
punctured ball `Metric.ball c r \ {c}` is a **strict** subset of its topological frontier. -/
theorem essentialBoundary_punctured_ball_ssubset_frontier [Nontrivial E] (c : E) {r : ℝ}
    (hr : 0 < r) :
    essentialBoundary μ (Metric.ball c r \ {c}) ⊂ frontier (Metric.ball c r \ {c}) :=
  ssubset_of_subset_not_subset (essentialBoundary_subset_frontier _) fun hsub ↦
    center_notMem_essentialBoundary_punctured_ball (μ := μ) c hr
      (hsub (center_mem_frontier_punctured_ball c hr))

theorem essentialBoundary_punctured_ball_ne_frontier [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    essentialBoundary μ (Metric.ball c r \ {c}) ≠ frontier (Metric.ball c r \ {c}) :=
  (essentialBoundary_punctured_ball_ssubset_frontier c hr).ne

omit [BorelSpace E] in
/-- For any `μ`-null set `D` and `r ≠ 0`, `essentialBoundary μ (Metric.ball c r ∪ D)` is contained
in `Metric.sphere c r`. -/
theorem essentialBoundary_ball_union_subset_sphere (c : E) {r : ℝ} (hr : r ≠ 0) {D : Set E}
    (hD : μ D = 0) :
    essentialBoundary μ (Metric.ball c r ∪ D) ⊆ Metric.sphere c r := by
  rw [essentialBoundary_union_null _ hD]
  exact essentialBoundary_ball_subset_sphere c hr

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If `D` is `μ`-null and dense in `E`, then every point outside `Metric.closedBall c r` belongs
to the topological frontier of `Metric.ball c r ∪ D`. -/
theorem compl_closedBall_subset_frontier_ball_union_of_null_of_dense (c : E) (r : ℝ) {D : Set E}
    (hD : μ D = 0) (hDense : Dense D) :
    (Metric.closedBall c r)ᶜ ⊆ frontier (Metric.ball c r ∪ D) := by
  intro x hx
  have hcl : x ∈ closure (Metric.ball c r ∪ D) :=
    closure_mono subset_union_right (hDense.closure_eq.symm ▸ mem_univ x)
  refine ⟨hcl, fun hint ↦ ?_⟩
  let U : Set E := interior (Metric.ball c r ∪ D) ∩ (Metric.closedBall c r)ᶜ
  have hU_open : IsOpen U := isOpen_interior.inter isClosed_closedBall.isOpen_compl
  have hU_nonempty : U.Nonempty := ⟨x, hint, hx⟩
  have hU_sub : U ⊆ D := fun y ⟨hy_int, hy_compl⟩ ↦
    (interior_subset hy_int).elim (fun hb ↦ False.elim (hy_compl (ball_subset_closedBall hb))) id
  exact hU_open.measure_ne_zero μ hU_nonempty (measure_mono_null hU_sub hD)

omit [BorelSpace E] in
/-- If `D` is `μ`-null and dense in a nontrivial normed space `E` and `r > 0`, then the essential
boundary of `Metric.ball c r ∪ D` is a **strict** subset of its topological frontier. -/
theorem essentialBoundary_ball_union_ssubset_frontier_of_null_of_dense [Nontrivial E] (c : E)
    {r : ℝ} (hr : 0 < r) {D : Set E} (hD : μ D = 0) (hDense : Dense D) :
    essentialBoundary μ (Metric.ball c r ∪ D) ⊂ frontier (Metric.ball c r ∪ D) := by
  refine ssubset_of_subset_not_subset (essentialBoundary_subset_frontier _) fun hsub ↦ ?_
  obtain ⟨v, hv⟩ := exists_norm_eq E (by positivity : 0 ≤ 2 * r)
  have hxc : c + v ∈ (Metric.closedBall c r)ᶜ := by
    rw [mem_compl_iff, mem_closedBall, dist_self_add_left, hv, not_le]
    linarith
  have hfront : c + v ∈ frontier (Metric.ball c r ∪ D) :=
    compl_closedBall_subset_frontier_ball_union_of_null_of_dense (μ := μ) c r hD hDense hxc
  have hsph : c + v ∈ Metric.sphere c r :=
    essentialBoundary_ball_union_subset_sphere (μ := μ) c hr.ne' hD (hsub hfront)
  rw [mem_sphere, dist_self_add_left, hv] at hsph
  linarith

end NormedSpaceExamples

end TauCeti.MeasureTheory
