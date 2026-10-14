/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.MeasureTheory.Measure.BallPerimeter
public import TauCeti.MeasureTheory.Measure.EssentialBoundary
public import TauCeti.MeasureTheory.Measure.Lebesgue.SteinerProperties
import all TauCeti.MeasureTheory.Measure.EssentialBoundary
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterSlicing
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerProperties

/-!
# Oriented Half-Spaces, Hyperplanes, Slabs, Gauss–Green Boundary Integrals, and Relative Perimeter
This file develops the geometry, measure-theoretic boundary structure, Gauss–Green divergence
formulas, and exact Caccioppoli relative perimeters of oriented affine half-spaces, hyperplanes,
and slabs in finite-dimensional real inner product spaces `E`:
1. **Affine half-spaces, hyperplanes, slabs, topology, volume, and essential boundary**:
   `halfSpaceLT`, `halfSpaceLE`, `halfSpaceGT`, `halfSpaceGE`, `hyperplane`, `slab`,
   `volume_hyperplane`, `halfSpaceLT_ae_eq_halfSpaceLE`, measure density `1 / 2` along
   `hyperplane e a`, and `essentialInterior`/`essentialExterior`/`essentialBoundary`.
2. **Hyperplane parametrization and Gauss–Green divergence theorem on half-spaces and slabs**:
   `hyperplanePoint`, `norm_hyperplanePoint_sub_sq`, `integral_inner_mem_divergence`, and
   Gauss–Green boundary integral formulas on half-spaces and slabs.
3. **Exact relative perimeter of half-spaces and slabs in open sets and balls**:
   `hyperplaneSlice`, `relativePerimeter_halfSpaceLT_eq_volume_hyperplaneSlice`,
   `relativePerimeter_slab_eq_add_volume_hyperplaneSlice`, and the De Giorgi blow-up formula
   `relativePerimeter_halfSpaceLT_ball_inner`.
4. **Steiner symmetrization of half-spaces and slabs & slice characterization of convexity**:
   `steinerSymmetrization_halfSpaceLT`, `steinerSymmetrization_slab`, and
   `convex_iff_forall_ordConnected_steinerFiber`.
-/

public section

noncomputable section

open Filter Function MeasureTheory Pointwise Set Submodule TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Distributions Topology
open TauCeti.MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Section 1: Affine half-spaces, hyperplanes, slabs, topology, and essential boundary -/
/-- The open lower affine half-space `{x : E | ⟪x, e⟫_ℝ < a}`. -/
def halfSpaceLT (e : E) (a : ℝ) : Set E := {x : E | ⟪x, e⟫_ℝ < a}
/-- The closed lower affine half-space `{x : E | ⟪x, e⟫_ℝ ≤ a}`. -/
def halfSpaceLE (e : E) (a : ℝ) : Set E := {x : E | ⟪x, e⟫_ℝ ≤ a}
/-- The open upper affine half-space `{x : E | a < ⟪x, e⟫_ℝ}`. -/
def halfSpaceGT (e : E) (a : ℝ) : Set E := {x : E | a < ⟪x, e⟫_ℝ}
/-- The closed upper affine half-space `{x : E | a ≤ ⟪x, e⟫_ℝ}`. -/
def halfSpaceGE (e : E) (a : ℝ) : Set E := {x : E | a ≤ ⟪x, e⟫_ℝ}
/-- The affine hyperplane `{x : E | ⟪x, e⟫_ℝ = a}`. -/
def hyperplane (e : E) (a : ℝ) : Set E := {x : E | ⟪x, e⟫_ℝ = a}
/-- The closed affine slab `{x : E | a ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ b}`. -/
def slab (e : E) (a b : ℝ) : Set E := {x : E | a ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ b}
@[simp] theorem mem_halfSpaceLT {e x : E} {a : ℝ} : x ∈ halfSpaceLT e a ↔ ⟪x, e⟫_ℝ < a := by rfl
@[simp] theorem mem_halfSpaceLE {e x : E} {a : ℝ} : x ∈ halfSpaceLE e a ↔ ⟪x, e⟫_ℝ ≤ a := by rfl
@[simp] theorem mem_halfSpaceGT {e x : E} {a : ℝ} : x ∈ halfSpaceGT e a ↔ a < ⟪x, e⟫_ℝ := by rfl
@[simp] theorem mem_halfSpaceGE {e x : E} {a : ℝ} : x ∈ halfSpaceGE e a ↔ a ≤ ⟪x, e⟫_ℝ := by rfl
@[simp] theorem mem_hyperplane {e x : E} {a : ℝ} : x ∈ hyperplane e a ↔ ⟪x, e⟫_ℝ = a := by rfl
@[simp] theorem mem_slab {e x : E} {a b : ℝ} :
    x ∈ slab e a b ↔ a ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ b := by rfl
@[simp] theorem compl_halfSpaceLT (e : E) (a : ℝ) : (halfSpaceLT e a)ᶜ = halfSpaceGE e a :=
  Set.ext fun _ ↦ by simp [halfSpaceLT, halfSpaceGE]
@[simp] theorem compl_halfSpaceLE (e : E) (a : ℝ) : (halfSpaceLE e a)ᶜ = halfSpaceGT e a :=
  Set.ext fun _ ↦ by simp [halfSpaceLE, halfSpaceGT]
@[simp] theorem compl_halfSpaceGT (e : E) (a : ℝ) : (halfSpaceGT e a)ᶜ = halfSpaceLE e a :=
  Set.ext fun _ ↦ by simp [halfSpaceGT, halfSpaceLE]
@[simp] theorem compl_halfSpaceGE (e : E) (a : ℝ) : (halfSpaceGE e a)ᶜ = halfSpaceLT e a :=
  Set.ext fun _ ↦ by simp [halfSpaceGE, halfSpaceLT]
@[simp] theorem halfSpaceLT_neg (e : E) (a : ℝ) : halfSpaceLT (-e) (-a) = halfSpaceGT e a :=
  Set.ext fun _ ↦ by simp [halfSpaceLT, halfSpaceGT, inner_neg_right]
@[simp] theorem halfSpaceLE_neg (e : E) (a : ℝ) : halfSpaceLE (-e) (-a) = halfSpaceGE e a :=
  Set.ext fun _ ↦ by simp [halfSpaceLE, halfSpaceGE, inner_neg_right]
theorem halfSpaceLT_subset_halfSpaceLE (e : E) (a : ℝ) : halfSpaceLT e a ⊆ halfSpaceLE e a :=
  fun _ hx ↦ mem_halfSpaceLE.mpr (le_of_lt hx)
theorem slab_eq_sdiff (e : E) (a b : ℝ) : slab e a b = halfSpaceLE e b \ halfSpaceLT e a :=
  Set.ext fun _ ↦ by simp [slab, halfSpaceLE, halfSpaceLT, and_comm]
theorem halfSpaceLE_diff_halfSpaceLT (e : E) (a : ℝ) :
    halfSpaceLE e a \ halfSpaceLT e a = hyperplane e a :=
  Set.ext fun _ ↦ by simp [halfSpaceLE, halfSpaceLT, hyperplane, le_antisymm_iff, and_comm]
theorem halfSpaceLT_union_hyperplane (e : E) (a : ℝ) :
    halfSpaceLT e a ∪ hyperplane e a = halfSpaceLE e a := by
  rw [← halfSpaceLE_diff_halfSpaceLT, union_sdiff_self,
    union_eq_self_of_subset_left (halfSpaceLT_subset_halfSpaceLE e a)]
theorem isOpen_halfSpaceLT (e : E) (a : ℝ) : IsOpen (halfSpaceLT e a) :=
  isOpen_lt (continuous_id.inner continuous_const) continuous_const
theorem isClosed_halfSpaceLE (e : E) (a : ℝ) : IsClosed (halfSpaceLE e a) :=
  isClosed_le (continuous_id.inner continuous_const) continuous_const
theorem isOpen_halfSpaceGT (e : E) (a : ℝ) : IsOpen (halfSpaceGT e a) :=
  isOpen_lt continuous_const (continuous_id.inner continuous_const)
theorem isClosed_halfSpaceGE (e : E) (a : ℝ) : IsClosed (halfSpaceGE e a) :=
  isClosed_le continuous_const (continuous_id.inner continuous_const)
theorem isClosed_hyperplane (e : E) (a : ℝ) : IsClosed (hyperplane e a) :=
  isClosed_eq (continuous_id.inner continuous_const) continuous_const
theorem isClosed_slab (e : E) (a b : ℝ) : IsClosed (slab e a b) :=
  (isClosed_halfSpaceGE e a).inter (isClosed_halfSpaceLE e b)
theorem convex_halfSpaceLT (e : E) (a : ℝ) : Convex ℝ (halfSpaceLT e a) :=
  convex_halfSpace_lt ((innerSL ℝ).flip e).isLinear a
theorem convex_halfSpaceLE (e : E) (a : ℝ) : Convex ℝ (halfSpaceLE e a) :=
  convex_halfSpace_le ((innerSL ℝ).flip e).isLinear a
theorem convex_hyperplane (e : E) (a : ℝ) : Convex ℝ (hyperplane e a) :=
  _root_.convex_hyperplane ((innerSL ℝ).flip e).isLinear a
theorem convex_slab (e : E) (a b : ℝ) : Convex ℝ (slab e a b) :=
  (convex_halfSpace_ge ((innerSL ℝ).flip e).isLinear a).inter (convex_halfSpaceLE e b)
/-- For `e ≠ 0`, the closure of `halfSpaceLT e a` is `halfSpaceLE e a`. -/
theorem closure_halfSpaceLT {e : E} (he : e ≠ 0) (a : ℝ) :
    closure (halfSpaceLT e a) = halfSpaceLE e a := by
  refine Subset.antisymm
    ((isClosed_halfSpaceLE e a).closure_subset_iff.mpr (halfSpaceLT_subset_halfSpaceLE e a))
    fun x hx ↦ ?_
  have he2 : 0 < ‖e‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr he)
  have htend : Tendsto (fun n : ℕ ↦ x - (1 / (n + 1 : ℝ)) • e) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.sub
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const e)
  refine mem_closure_of_tendsto htend (Eventually.of_forall fun n ↦ ?_)
  change ⟪x - (1 / (n + 1 : ℝ)) • e, e⟫_ℝ < a
  rw [inner_sub_left, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  linarith [mem_halfSpaceLE.mp hx, mul_pos (by positivity : 0 < 1 / (n + 1 : ℝ)) he2]
/-- For `e ≠ 0`, the topological frontier of `halfSpaceLT e a` is `hyperplane e a`. -/
theorem frontier_halfSpaceLT {e : E} (he : e ≠ 0) (a : ℝ) :
    frontier (halfSpaceLT e a) = hyperplane e a := by
  rw [frontier, closure_halfSpaceLT he, (isOpen_halfSpaceLT e a).interior_eq,
    halfSpaceLE_diff_halfSpaceLT]

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

theorem measurableSet_halfSpaceLT (e : E) (a : ℝ) : MeasurableSet (halfSpaceLT e a) :=
  (isOpen_halfSpaceLT e a).measurableSet
theorem measurableSet_halfSpaceLE (e : E) (a : ℝ) : MeasurableSet (halfSpaceLE e a) :=
  (isClosed_halfSpaceLE e a).measurableSet
theorem measurableSet_hyperplane (e : E) (a : ℝ) : MeasurableSet (hyperplane e a) :=
  (isClosed_hyperplane e a).measurableSet
theorem measurableSet_slab (e : E) (a b : ℝ) : MeasurableSet (slab e a b) :=
  (isClosed_slab e a b).measurableSet
@[simp] theorem orthogonalHyperplaneProdMeasurableEquiv_preimage_hyperplane {e : E} (he : ‖e‖ = 1)
    (a : ℝ) :
    (orthogonalHyperplaneProdMeasurableEquiv he) ⁻¹' hyperplane e a = Set.univ ×ˢ {a} := by
  ext ⟨y, t⟩; simp [hyperplane, inner_coe_add_smul_self he]

variable [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The dimension of `orthogonalHyperplane e` (`e ≠ 0`) is `Module.finrank ℝ E - 1`. -/
theorem finrank_orthogonalHyperplane {e : E} (he : e ≠ 0) :
    Module.finrank ℝ (orthogonalHyperplane e) = Module.finrank ℝ E - 1 := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
  change Module.finrank ℝ (ℝ ∙ e) + Module.finrank ℝ (orthogonalHyperplane e) =
    Module.finrank ℝ E at h1
  rw [finrank_span_singleton he] at h1; omega
/-- Every affine hyperplane `hyperplane e a` with `e ≠ 0` has Lebesgue measure zero. -/
@[simp] theorem volume_hyperplane {e : E} (he : e ≠ 0) (a : ℝ) : volume (hyperplane e a) = 0 := by
  have h1 : ∀ {u : E} (hu : ‖u‖ = 1) (b : ℝ), volume (hyperplane u b) = 0 := fun hu b ↦ by
    rw [← (measurePreserving_orthogonalHyperplaneProdMeasurableEquiv hu).measure_preimage
      (measurableSet_hyperplane _ b).nullMeasurableSet,
      orthogonalHyperplaneProdMeasurableEquiv_preimage_hyperplane, Measure.prod_prod,
      Real.volume_singleton, mul_zero]
  have hnorm : ‖‖e‖⁻¹ • e‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr he)]
  have heq : hyperplane e a = hyperplane (‖e‖⁻¹ • e) (‖e‖⁻¹ * a) :=
    Set.ext fun _ ↦ by simp [hyperplane, inner_smul_right, inv_ne_zero (norm_ne_zero_iff.mpr he)]
  rw [heq, h1 hnorm]
/-- For `e ≠ 0`, `halfSpaceLT e a` and `halfSpaceLE e a` are `volume`-almost everywhere equal. -/
theorem halfSpaceLT_ae_eq_halfSpaceLE {e : E} (he : e ≠ 0) (a : ℝ) :
    halfSpaceLT e a =ᵐ[volume] halfSpaceLE e a := by
  rw [← halfSpaceLT_union_hyperplane]
  exact (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr (volume_hyperplane he a))).symm
/-- For `e ≠ 0`, `halfSpaceGT e a` and `halfSpaceGE e a` are `volume`-almost everywhere equal. -/
theorem halfSpaceGT_ae_eq_halfSpaceGE {e : E} (he : e ≠ 0) (a : ℝ) :
    halfSpaceGT e a =ᵐ[volume] halfSpaceGE e a := by
  rw [← halfSpaceLT_neg, ← halfSpaceLE_neg]
  exact halfSpaceLT_ae_eq_halfSpaceLE (neg_ne_zero.mpr he) (-a)
/-- Any closed ball centered on `hyperplane e a` (`e ≠ 0`) is bisected by `halfSpaceLT e a`. -/
theorem volume_halfSpaceLT_inter_closedBall_of_mem_hyperplane {e x : E} (he : e ≠ 0) {a : ℝ}
    (hx : x ∈ hyperplane e a) (r : ℝ) :
    2 * volume (halfSpaceLT e a ∩ Metric.closedBall x r) = volume (Metric.closedBall x r) := by
  let Lneg : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have hmp : ∀ s : Set E, volume ((fun z : E ↦ (2 : ℝ) • x - z) ⁻¹' s) = volume s := fun s ↦ by
    rw [show (fun z : E ↦ (2 : ℝ) • x - z) = (fun z ↦ (2 : ℝ) • x + z) ∘ Lneg by
      ext z; simp [Lneg, sub_eq_add_neg], preimage_comp,
      Lneg.measurePreserving.measure_preimage_emb
        Lneg.toHomeomorph.toMeasurableEquiv.measurableEmbedding, measure_preimage_add]
  have hpre : (fun z : E ↦ (2 : ℝ) • x - z) ⁻¹' (halfSpaceLT e a ∩ Metric.closedBall x r) =
      halfSpaceGT e a ∩ Metric.closedBall x r := by
    ext z
    simp only [mem_preimage, mem_inter_iff, mem_halfSpaceLT, mem_halfSpaceGT,
      Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖(2 : ℝ) • x - z - x‖ = ‖z - x‖ := by
      rw [two_smul, add_sub_right_comm, add_sub_cancel_right, norm_sub_rev]
    have hinner : ⟪(2 : ℝ) • x - z, e⟫_ℝ < a ↔ a < ⟪z, e⟫_ℝ := by
      rw [inner_sub_left, inner_smul_left, RCLike.conj_to_real, mem_hyperplane.mp hx]
      constructor <;> intro h <;> linarith
    rw [hnorm, hinner]
  have heq1 : volume (halfSpaceLT e a ∩ Metric.closedBall x r) =
      volume (halfSpaceGT e a ∩ Metric.closedBall x r) := by rw [← hpre, hmp]
  have heq2 : volume (halfSpaceLT e a ∩ Metric.closedBall x r) =
      volume (halfSpaceLE e a ∩ Metric.closedBall x r) :=
    measure_congr ((halfSpaceLT_ae_eq_halfSpaceLE he a).inter (EventuallyEq.refl _ _))
  have hpart := measure_inter_add_sdiff (μ := volume) (Metric.closedBall x r)
    (measurableSet_halfSpaceLE e a)
  have hsdiff : Metric.closedBall x r \ halfSpaceLE e a =
      halfSpaceGT e a ∩ Metric.closedBall x r := by
    rw [Set.sdiff_eq, compl_halfSpaceLE, inter_comm]
  rw [inter_comm (Metric.closedBall x r), hsdiff, ← heq1, ← heq2, ← two_mul] at hpart
  exact hpart
/-- At every point `x ∈ hyperplane e a` (`e ≠ 0`), `halfSpaceLT e a` has measure density `1 / 2`. -/
theorem hasMeasureDensityAt_halfSpaceLT_of_mem_hyperplane {e x : E} (he : e ≠ 0) {a : ℝ}
    (hx : x ∈ hyperplane e a) :
    HasMeasureDensityAt volume (halfSpaceLT e a) x (1 / 2) := by
  rw [hasMeasureDensityAt_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hv := volume_halfSpaceLT_inter_closedBall_of_mem_hyperplane he hx r
  have hv_pos : volume (halfSpaceLT e a ∩ Metric.closedBall x r) ≠ 0 :=
    fun h0 ↦ (Metric.measure_closedBall_pos volume x hr).ne' (by rw [← hv, h0, mul_zero])
  have hv_top : volume (halfSpaceLT e a ∩ Metric.closedBall x r) ≠ ⊤ :=
    fun htop' ↦ measure_closedBall_lt_top.ne (by rw [← hv, htop', ENNReal.mul_top two_ne_zero])
  rw [← hv, ← ENNReal.mul_div_mul_right 1 2 hv_pos hv_top, one_mul]
/-- The essential boundary of `halfSpaceLT e a` (`e ≠ 0`) is `hyperplane e a`. -/
@[simp] theorem essentialBoundary_halfSpaceLT {e : E} (he : e ≠ 0) (a : ℝ) :
    essentialBoundary volume (halfSpaceLT e a) = hyperplane e a := by
  refine Subset.antisymm ?_ fun x hx ↦ ?_
  · rw [← frontier_halfSpaceLT he]; exact essentialBoundary_subset_frontier (halfSpaceLT e a)
  · have hd := hasMeasureDensityAt_halfSpaceLT_of_mem_hyperplane he hx
    rw [essentialBoundary_eq_compl_inter_compl]
    exact ⟨fun h1 ↦ by have := hd.unique h1; norm_num at this,
      fun h0 ↦ by have := hd.unique h0; norm_num at this⟩
@[simp] theorem essentialBoundary_halfSpaceLE {e : E} (he : e ≠ 0) (a : ℝ) :
    essentialBoundary volume (halfSpaceLE e a) = hyperplane e a := by
  rw [← essentialBoundary_congr_ae (halfSpaceLT_ae_eq_halfSpaceLE he a),
    essentialBoundary_halfSpaceLT he]
/-- The essential interior of `halfSpaceLT e a` (`e ≠ 0`) is `halfSpaceLT e a`. -/
@[simp] theorem essentialInterior_halfSpaceLT {e : E} (he : e ≠ 0) (a : ℝ) :
    essentialInterior volume (halfSpaceLT e a) = halfSpaceLT e a := by
  refine Subset.antisymm (fun x hx ↦ ?_) fun x hx ↦
    interior_subset_essentialInterior (halfSpaceLT e a)
      (by rwa [(isOpen_halfSpaceLT e a).interior_eq])
  have hle : x ∈ halfSpaceLE e a := by
    rw [← closure_halfSpaceLT he]; exact essentialInterior_subset_closure (halfSpaceLT e a) hx
  by_contra hlt
  have hhyp : x ∈ essentialBoundary volume (halfSpaceLT e a) := by
    rw [essentialBoundary_halfSpaceLT he, ← halfSpaceLE_diff_halfSpaceLT]; exact ⟨hle, hlt⟩
  exact disjoint_left.mp
    (disjoint_essentialBoundary_essentialInterior volume (halfSpaceLT e a)) hhyp hx
@[simp] theorem essentialInterior_halfSpaceLE {e : E} (he : e ≠ 0) (a : ℝ) :
    essentialInterior volume (halfSpaceLE e a) = halfSpaceLT e a := by
  rw [← essentialInterior_congr_ae (halfSpaceLT_ae_eq_halfSpaceLE he a),
    essentialInterior_halfSpaceLT he]
/-- The essential exterior of `halfSpaceLT e a` (`e ≠ 0`) is `halfSpaceGT e a`. -/
@[simp] theorem essentialExterior_halfSpaceLT {e : E} (he : e ≠ 0) (a : ℝ) :
    essentialExterior volume (halfSpaceLT e a) = halfSpaceGT e a := by
  rw [← essentialInterior_compl (measurableSet_halfSpaceLT e a).nullMeasurableSet,
    compl_halfSpaceLT, ← halfSpaceLE_neg, essentialInterior_halfSpaceLE (neg_ne_zero.mpr he),
    halfSpaceLT_neg]
@[simp] theorem essentialExterior_halfSpaceLE {e : E} (he : e ≠ 0) (a : ℝ) :
    essentialExterior volume (halfSpaceLE e a) = halfSpaceGT e a := by
  rw [← essentialExterior_congr_ae (halfSpaceLT_ae_eq_halfSpaceLE he a),
    essentialExterior_halfSpaceLT he]

end Measurable

/-! ### Section 2: Hyperplane parametrization and Gauss–Green theorem on half-spaces and slabs -/
/-- Affine parametrization `hyperplanePoint e a y = (y : E) + a • e` of `hyperplane e a`. -/
def hyperplanePoint (e : E) (a : ℝ) (y : orthogonalHyperplane e) : E := (y : E) + a • e
theorem continuous_hyperplanePoint (e : E) (a : ℝ) : Continuous (hyperplanePoint e a) :=
  (orthogonalHyperplane e).subtypeL.continuous.add continuous_const
@[simp]
theorem inner_hyperplanePoint_self {e : E} (he : ‖e‖ = 1) (a : ℝ) (y : orthogonalHyperplane e) :
    ⟪hyperplanePoint e a y, e⟫_ℝ = a :=
  inner_coe_add_smul_self he y a
@[simp]
theorem orthogonalProjectionOnto_hyperplanePoint (e : E) (a : ℝ) (y : orthogonalHyperplane e) :
    (orthogonalHyperplane e).orthogonalProjectionOnto (hyperplanePoint e a y) = y :=
  orthogonalProjectionOnto_orthogonalHyperplane_add_smul e y a
/-- Pythagorean decomposition of `‖hyperplanePoint e a y - c‖ ^ 2` relative to any point `c : E`. -/
theorem norm_hyperplanePoint_sub_sq {e : E} (he : ‖e‖ = 1) (a : ℝ)
    (y : orthogonalHyperplane e) (c : E) :
    ‖hyperplanePoint e a y - c‖ ^ 2 =
      ‖y - (orthogonalHyperplane e).orthogonalProjectionOnto c‖ ^ 2 + (a - ⟪c, e⟫_ℝ) ^ 2 := by
  have hc := (orthogonalProjection_orthogonalHyperplane_add_inner_smul he c).symm
  have hsub : hyperplanePoint e a y - c =
      ((y - (orthogonalHyperplane e).orthogonalProjectionOnto c : orthogonalHyperplane e) : E) +
        (a - ⟪c, e⟫_ℝ) • e := by
    dsimp only [hyperplanePoint]; conv_lhs => rw [hc]
    rw [Submodule.coe_sub, sub_smul]; abel
  rw [hsub, norm_coe_add_smul_sq he]
/-- Tangential restriction of `φ : 𝓓(Ω, E)` to the hyperplane slice at height `t : ℝ`. -/
def hyperplaneTestFunction (e : E) {Ω : Opens E} (φ : 𝓓(Ω, E)) (t : ℝ) :
    𝓓((⊤ : Opens (orthogonalHyperplane e)), orthogonalHyperplane e) where
  toFun y := (orthogonalHyperplane e).orthogonalProjectionOnto ((φ : E → E) ((y : E) + t • e))
  contDiff' := (orthogonalHyperplane e).orthogonalProjectionOnto.contDiff.comp
    (φ.contDiff.comp ((orthogonalHyperplane e).subtypeL.contDiff.add contDiff_const))
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact
    (φ.hasCompactSupport.isCompact.image
      (orthogonalHyperplane e).orthogonalProjectionOnto.continuous) fun y hy ↦
      ⟨(y : E) + t • e, subset_tsupport _ fun h0 ↦ hy (by simp [h0]),
        orthogonalProjectionOnto_orthogonalHyperplane_add_smul e y t⟩
  tsupport_subset' := subset_univ _
/-- Normal 1D fiber test function `t ↦ ⟪φ ((y : E) + t • e), e⟫_ℝ`. -/
def normalFiberTestFunction {Ω : Opens E} (φ : 𝓓(Ω, E)) {e : E} (he : ‖e‖ = 1)
    (y : orthogonalHyperplane e) : 𝓓((⊤ : Opens ℝ), ℝ) :=
  steinerFiberTestFunction
    ⟨innerTestFunction e φ, (innerTestFunction e φ).contDiff,
      (innerTestFunction e φ).hasCompactSupport, subset_univ _⟩ he y
@[simp] theorem normalFiberTestFunction_apply {Ω : Opens E} (φ : 𝓓(Ω, E)) {e : E} (he : ‖e‖ = 1)
    (y : orthogonalHyperplane e) (t : ℝ) :
    normalFiberTestFunction φ he y t = ⟪(φ : E → E) ((y : E) + t • e), e⟫_ℝ :=
  (real_inner_comm e ((φ : E → E) ((y : E) + t • e))).symm
/-- Tangential divergence of `hyperplaneTestFunction e φ t` equals `div (φ - ⟪e, φ ·⟫_ℝ • e)`. -/
theorem divergence_hyperplaneTestFunction [FiniteDimensional ℝ E] {e : E} (he : ‖e‖ = 1)
    {Ω : Opens E} (φ : 𝓓(Ω, E)) (y : orthogonalHyperplane e) (t : ℝ) :
    divergence (hyperplaneTestFunction e φ t : orthogonalHyperplane e → orthogonalHyperplane e) y =
      divergence ((φ - constSmulTestFunction (innerTestFunction e φ) e : 𝓓(Ω, E)) : E → E)
        ((y : E) + t • e) := by
  let H := orthogonalHyperplane e
  let x : E := (y : E) + t • e
  have hdφ : ∀ z, DifferentiableAt ℝ (φ : E → E) z := φ.contDiff.differentiable (by simp)
  have h1 : fderiv ℝ (hyperplaneTestFunction e φ t : H → H) y =
      H.orthogonalProjectionOnto.comp ((fderiv ℝ (φ : E → E) x).comp H.subtypeL) := by
    have hd1 : HasFDerivAt (fun y' : H ↦ (y' : E) + t • e) H.subtypeL y := by
      simpa using H.subtypeL.hasFDerivAt.add_const (t • e)
    exact (H.orthogonalProjectionOnto.hasFDerivAt.comp y ((hdφ x).hasFDerivAt.comp y hd1)).fderiv
  have htr1 : divergence (hyperplaneTestFunction e φ t : H → H) y =
      (LinearMap.trace ℝ E) (H.starProjection.comp (fderiv ℝ (φ : E → E) x)).toLinearMap := by
    rw [divergence, h1]
    exact LinearMap.trace_comp_comm' H.subtypeL.toLinearMap
      (H.orthogonalProjectionOnto.comp (fderiv ℝ (φ : E → E) x)).toLinearMap
  have hstar : H.starProjection ∘ (φ : E → E) =
      ((φ - constSmulTestFunction (innerTestFunction e φ) e : 𝓓(Ω, E)) : E → E) := by
    ext z; change H.starProjection (φ z) = φ z - ⟪e, φ z⟫_ℝ • e
    rw [starProjection_orthogonalHyperplane_apply he, real_inner_comm]
  rw [htr1, ← (H.starProjection.hasFDerivAt.comp x (hdφ x).hasFDerivAt).fderiv, hstar, divergence]

section GaussGreen

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Master Fubini–Divergence reduction for `{x : E | ⟪x, e⟫_ℝ ∈ I}`** (`‖e‖ = 1`). -/
theorem integral_inner_mem_divergence {e : E} (he : ‖e‖ = 1) {I : Set ℝ} (hI : MeasurableSet I)
    {Ω : Opens E} (φ : 𝓓(Ω, E)) :
    ∫ x in {x : E | ⟪x, e⟫_ℝ ∈ I}, divergence (φ : E → E) x =
      ∫ y : orthogonalHyperplane e,
        ∫ t in I, divergence (normalFiberTestFunction φ he y : ℝ → ℝ) t := by
  let H := orthogonalHyperplane e
  let φN : 𝓓(Ω, E) := constSmulTestFunction (innerTestFunction e φ) e
  let φT : 𝓓(Ω, E) := φ - φN
  have hpre : (orthogonalHyperplaneProdMeasurableEquiv he) ⁻¹' {x : E | ⟪x, e⟫_ℝ ∈ I} =
      Set.univ ×ˢ I := by
    ext ⟨y, t⟩; simp [orthogonalHyperplaneProdMeasurableEquiv_apply, inner_coe_add_smul_self he]
  have hdiv_add : ∀ x, divergence (φ : E → E) x =
      divergence (φT : E → E) x + divergence (φN : E → E) x := fun x ↦ by
    have hdT : DifferentiableAt ℝ (φT : E → E) x := φT.contDiff.differentiable (by simp) x
    have hdN : DifferentiableAt ℝ (φN : E → E) x := φN.contDiff.differentiable (by simp) x
    rw [show (φ : E → E) = (φT : E → E) + (φN : E → E) by ext z; simp [φT], divergence,
      (hdT.hasFDerivAt.add hdN.hasFDerivAt).fderiv, ContinuousLinearMap.toLinearMap_add, map_add]
    rfl
  simp_rw [hdiv_add]
  rw [integral_add (integrable_divergence_testFunction φT).integrableOn
    (integrable_divergence_testFunction φN).integrableOn]
  have hint_prod (ψ : 𝓓(Ω, E)) :
      Integrable (fun p : H × ℝ ↦ divergence (ψ : E → E)
        (orthogonalHyperplaneProdMeasurableEquiv he p))
        ((volume : Measure H).prod (volume.restrict I)) :=
    ((measurePreserving_orthogonalHyperplaneProdMeasurableEquiv he).integrable_comp_emb
      (orthogonalHyperplaneProdMeasurableEquiv he).measurableEmbedding).mpr
      (integrable_divergence_testFunction ψ) |>.mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hmp_prod (ψ : 𝓓(Ω, E)) :
      ∫ x in {x : E | ⟪x, e⟫_ℝ ∈ I}, divergence (ψ : E → E) x =
        ∫ p : H × ℝ, divergence (ψ : E → E) (orthogonalHyperplaneProdMeasurableEquiv he p)
          ∂(volume : Measure H).prod (volume.restrict I) := by
    rw [← (measurePreserving_orthogonalHyperplaneProdMeasurableEquiv he).setIntegral_preimage_emb
      (orthogonalHyperplaneProdMeasurableEquiv he).measurableEmbedding
      (divergence (ψ : E → E)) {x : E | ⟪x, e⟫_ℝ ∈ I},
      hpre, ← Measure.prod_restrict, Measure.restrict_univ]
  have hT0 : ∫ x in {x : E | ⟪x, e⟫_ℝ ∈ I}, divergence (φT : E → E) x = 0 := by
    rw [hmp_prod φT, integral_prod_symm _ (hint_prod φT)]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
    dsimp only
    have hcongr : (fun y : H ↦ divergence (φT : E → E)
        (orthogonalHyperplaneProdMeasurableEquiv he (y, t))) =
        divergence (hyperplaneTestFunction e φ t : H → H) :=
      funext fun y ↦ (divergence_hyperplaneTestFunction he φ y t).symm
    rw [hcongr]
    have h0 := integral_divergence_testFunction_eq_zero (μ := volume) (hyperplaneTestFunction e φ t)
    rwa [Opens.coe_top, setIntegral_univ] at h0
  have hN : ∫ x in {x : E | ⟪x, e⟫_ℝ ∈ I}, divergence (φN : E → E) x =
      ∫ y : H, ∫ t in I, divergence (normalFiberTestFunction φ he y : ℝ → ℝ) t := by
    rw [hmp_prod φN, integral_prod _ (hint_prod φN)]
    refine integral_congr_ae (Eventually.of_forall fun y ↦
      setIntegral_congr_fun hI fun t _ ↦ ?_)
    change divergence (φN : E → E) ((y : E) + t • e) =
      divergence (normalFiberTestFunction φ he y : ℝ → ℝ) t
    dsimp only [φN, normalFiberTestFunction]
    rw [divergence_constSmulTestFunction, divergence_steinerFiberTestFunction]; rfl
  rw [hT0, zero_add, hN]
/-- **Gauss–Green divergence theorem on `halfSpaceLT e a`** (`‖e‖ = 1`). -/
theorem integral_halfSpaceLT_divergence {e : E} (he : ‖e‖ = 1) (a : ℝ) {Ω : Opens E}
    (φ : 𝓓(Ω, E)) :
    ∫ x in halfSpaceLT e a, divergence (φ : E → E) x =
      ∫ y : orthogonalHyperplane e, ⟪(φ : E → E) (hyperplanePoint e a y), e⟫_ℝ := by
  change ∫ x in {x : E | ⟪x, e⟫_ℝ ∈ Iio a}, divergence (φ : E → E) x = _
  rw [integral_inner_mem_divergence he measurableSet_Iio φ]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only; rw [integral_Iio_divergence_testFunction, normalFiberTestFunction_apply]; rfl
/-- **Gauss–Green divergence theorem on `halfSpaceLE e a`** (`‖e‖ = 1`). -/
theorem integral_halfSpaceLE_divergence {e : E} (he : ‖e‖ = 1) (a : ℝ) {Ω : Opens E}
    (φ : 𝓓(Ω, E)) :
    ∫ x in halfSpaceLE e a, divergence (φ : E → E) x =
      ∫ y : orthogonalHyperplane e, ⟪(φ : E → E) (hyperplanePoint e a y), e⟫_ℝ := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  rw [← setIntegral_congr_set (halfSpaceLT_ae_eq_halfSpaceLE he0 a),
    integral_halfSpaceLT_divergence he]
/-- **Gauss–Green divergence theorem on `halfSpaceGT e a`** (`‖e‖ = 1`). -/
theorem integral_halfSpaceGT_divergence {e : E} (he : ‖e‖ = 1) (a : ℝ) {Ω : Opens E}
    (φ : 𝓓(Ω, E)) :
    ∫ x in halfSpaceGT e a, divergence (φ : E → E) x =
      -∫ y : orthogonalHyperplane e, ⟪(φ : E → E) (hyperplanePoint e a y), e⟫_ℝ := by
  change ∫ x in {x : E | ⟪x, e⟫_ℝ ∈ Ioi a}, divergence (φ : E → E) x = _
  rw [integral_inner_mem_divergence he measurableSet_Ioi φ, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only; rw [integral_Ioi_divergence_testFunction, normalFiberTestFunction_apply]; rfl
/-- **Gauss–Green divergence theorem on `slab e a b`** (`‖e‖ = 1`, `a ≤ b`). -/
theorem integral_slab_divergence {e : E} (he : ‖e‖ = 1) {a b : ℝ} (hab : a ≤ b) {Ω : Opens E}
    (φ : 𝓓(Ω, E)) :
    ∫ x in slab e a b, divergence (φ : E → E) x =
      ∫ y : orthogonalHyperplane e,
        (⟪(φ : E → E) (hyperplanePoint e b y), e⟫_ℝ -
          ⟪(φ : E → E) (hyperplanePoint e a y), e⟫_ℝ) := by
  change ∫ x in {x : E | ⟪x, e⟫_ℝ ∈ Icc a b}, divergence (φ : E → E) x = _
  rw [integral_inner_mem_divergence he measurableSet_Icc φ]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [integral_Icc_divergence_testFunction _ hab, normalFiberTestFunction_apply,
    normalFiberTestFunction_apply]; rfl

end GaussGreen

/-! ### Section 3: Exact relative perimeter of half-spaces and slabs in open sets and balls -/
/-- The slice `{y : orthogonalHyperplane e | hyperplanePoint e a y ∈ s}` along `hyperplane e a`. -/
def hyperplaneSlice (e : E) (a : ℝ) (s : Set E) : Set (orthogonalHyperplane e) :=
  {y : orthogonalHyperplane e | hyperplanePoint e a y ∈ s}
@[simp] theorem mem_hyperplaneSlice {e : E} {a : ℝ} {s : Set E} {y : orthogonalHyperplane e} :
    y ∈ hyperplaneSlice e a s ↔ hyperplanePoint e a y ∈ s := by rfl
theorem isOpen_hyperplaneSlice (e : E) (a : ℝ) {s : Set E} (hs : IsOpen s) :
    IsOpen (hyperplaneSlice e a s) :=
  hs.preimage (continuous_hyperplanePoint e a)
/-- Slice of `Metric.ball c r` by `hyperplane e a` when `|a - ⟪c, e⟫_ℝ| < r`. -/
theorem hyperplaneSlice_ball_of_abs_lt {e : E} (he : ‖e‖ = 1) (c : E) {a r : ℝ}
    (har : |a - ⟪c, e⟫_ℝ| < r) :
    hyperplaneSlice e a (Metric.ball c r) =
      Metric.ball ((orthogonalHyperplane e).orthogonalProjectionOnto c)
        (Real.sqrt (r ^ 2 - (a - ⟪c, e⟫_ℝ) ^ 2)) := by
  have hr : 0 < r := (abs_nonneg _).trans_lt har
  have hsub_pos : 0 < r ^ 2 - (a - ⟪c, e⟫_ℝ) ^ 2 := by
    rw [sub_pos, ← sq_abs]; exact sq_lt_sq.mpr (by rwa [abs_abs, abs_of_pos hr])
  ext y; simp only [mem_hyperplaneSlice, Metric.mem_ball, dist_eq_norm]
  rw [← sq_lt_sq₀ (norm_nonneg _) hr.le,
    ← sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_pos.mpr hsub_pos).le,
    Real.sq_sqrt hsub_pos.le, norm_hyperplanePoint_sub_sq he a y c, lt_sub_iff_add_lt]
/-- When `r ≤ |a - ⟪c, e⟫_ℝ|`, the slice of `Metric.ball c r` by `hyperplane e a` is empty. -/
theorem hyperplaneSlice_ball_of_le_abs {e : E} (he : ‖e‖ = 1) (c : E) {a r : ℝ}
    (har : r ≤ |a - ⟪c, e⟫_ℝ|) :
    hyperplaneSlice e a (Metric.ball c r) = ∅ := by
  ext y
  simp only [mem_hyperplaneSlice, Metric.mem_ball, dist_eq_norm, mem_empty_iff_false, iff_false,
    not_lt]
  rcases le_or_gt r 0 with hr0 | hr0
  · exact hr0.trans (norm_nonneg _)
  · rw [← sq_le_sq₀ hr0.le (norm_nonneg _), norm_hyperplanePoint_sub_sq he a y c]
    have hsq : r ^ 2 ≤ (a - ⟪c, e⟫_ℝ) ^ 2 := by
      rw [← sq_abs (a - ⟪c, e⟫_ℝ)]; exact sq_le_sq.mpr (by rwa [abs_of_pos hr0, abs_abs])
    linarith [sq_nonneg ‖y - (orthogonalHyperplane e).orthogonalProjectionOnto c‖]
/-- Slice of `Metric.ball c r` by the hyperplane through `c` (`a = ⟪c, e⟫_ℝ`). -/
@[simp] theorem hyperplaneSlice_ball_inner {e : E} (he : ‖e‖ = 1) (c : E) (r : ℝ) :
    hyperplaneSlice e ⟪c, e⟫_ℝ (Metric.ball c r) =
      Metric.ball ((orthogonalHyperplane e).orthogonalProjectionOnto c) r := by
  rcases lt_or_ge 0 r with hr | hr
  · rw [hyperplaneSlice_ball_of_abs_lt he c (by simpa using hr)]; simp [Real.sqrt_sq hr.le]
  · rw [hyperplaneSlice_ball_of_le_abs he c (by simpa using hr), Metric.ball_eq_empty.mpr hr]

section RelativePerimeter

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gauss–Green upper bound on the relative perimeter of `halfSpaceLT e a` in an open set `Ω`. -/
theorem relativePerimeter_halfSpaceLT_le_volume_hyperplaneSlice {e : E} (he : ‖e‖ = 1)
    (Ω : Opens E) (a : ℝ) :
    relativePerimeter volume Ω (halfSpaceLT e a) ≤ volume (hyperplaneSlice e a Ω) := by
  rw [relativePerimeter_eq_iSup_of_measurableSet (measurableSet_halfSpaceLT e a)]
  refine iSup₂_le fun φ hφ ↦ ?_
  have hsupp : Function.support (fun y : orthogonalHyperplane e ↦
      ⟪(φ : E → E) (hyperplanePoint e a y), e⟫_ℝ) ⊆ hyperplaneSlice e a Ω :=
    fun y hy ↦ by_contra fun hyΩ ↦ hy (by simp [φ.zero_on_compl hyΩ])
  have hint_eq : ∫ x in halfSpaceLT e a ∩ (Ω : Set E), divergence (φ : E → E) x =
      ∫ y in hyperplaneSlice e a Ω, ⟪(φ : E → E) (hyperplanePoint e a y), e⟫_ℝ := by
    have h1 : ∫ x in halfSpaceLT e a ∩ (Ω : Set E), divergence (φ : E → E) x =
        ∫ x in halfSpaceLT e a, divergence (φ : E → E) x :=
      (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
        (measurableSet_halfSpaceLT e a).nullMeasurableSet inter_subset_left
        (Eventually.of_forall fun x ⟨hx_lt, hxΩ⟩ ↦
          divergence_testFunction_eq_zero_of_notMem φ (fun h ↦ hxΩ ⟨hx_lt, h⟩))).symm
    rw [h1, integral_halfSpaceLT_divergence he a φ,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
        Function.notMem_support.mp (hy ∘ (hsupp ·))]
  rw [hint_eq]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ y in hyperplaneSlice e a Ω, ‖⟪(φ : E → E) (hyperplanePoint e a y), e⟫_ℝ‖ₑ
      ≤ ∫⁻ _ in hyperplaneSlice e a Ω, 1 := lintegral_mono fun y ↦ by
        rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
        exact (abs_real_inner_le_norm _ _).trans (by rw [he, mul_one]; exact hφ _)
    _ = volume (hyperplaneSlice e a Ω) := by simp
/-- Any compact `K ⊆ hyperplaneSlice e a Ω` has `volume K` bounded by `directionalPerimeter`. -/
theorem volume_compact_le_directionalPerimeter_halfSpaceLT {e : E} (he : ‖e‖ = 1)
    (Ω : Opens E) (a : ℝ) {K : Set (orthogonalHyperplane e)}
    (hK_sub : K ⊆ hyperplaneSlice e a Ω) (hK : IsCompact K) :
    volume K ≤ directionalPerimeter volume Ω e (halfSpaceLT e a) := by
  let KE : Set E := hyperplanePoint e a '' K
  have hKE_compact : IsCompact KE := hK.image (continuous_hyperplanePoint e a)
  rcases hKE_compact.exists_cthickening_subset_open Ω.isOpen (image_subset_iff.mpr hK_sub) with
    ⟨δ, hδ, hδ_sub⟩
  rcases exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (Metric.isOpen_thickening (δ := δ) (E := KE)) hKE_compact.isClosed
    (Metric.self_subset_thickening hδ KE) with ⟨ψ_raw, hψ_diff, hψ_range, hψ_supp, hψ_one⟩
  have htsupp_sub : tsupport ψ_raw ⊆ Metric.cthickening δ KE := by
    rw [tsupport, hψ_supp]; exact Metric.closure_thickening_subset_cthickening δ KE
  have hψ_compact : HasCompactSupport ψ_raw :=
    HasCompactSupport.of_support_subset_isCompact hKE_compact.cthickening
      (subset_tsupport ψ_raw |>.trans htsupp_sub)
  let ψ : 𝓓(Ω, ℝ) := ⟨ψ_raw, hψ_diff, hψ_compact, htsupp_sub.trans hδ_sub⟩
  have hψ_nonneg : ∀ x, 0 ≤ ψ x := fun x ↦ (hψ_range (mem_range_self x)).1
  have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ_nonneg x)]; exact (hψ_range (mem_range_self x)).2
  let φ : 𝓓(Ω, E) := constSmulTestFunction ψ e
  have hdiv : ∫ x in (Ω : Set E),
      (halfSpaceLT e a).indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ (ψ : E → ℝ) x e =
      ∫ y : orthogonalHyperplane e, ψ (hyperplanePoint e a y) := by
    have h2 : (fun x ↦ (halfSpaceLT e a).indicator (fun _ ↦ (1 : ℝ)) x *
        divergence (φ : E → E) x) =
        (halfSpaceLT e a).indicator (divergence (φ : E → E)) := by
      ext x; by_cases hx : x ∈ halfSpaceLT e a <;> simp [hx]
    have h1 : (fun x ↦ (halfSpaceLT e a).indicator (fun _ ↦ (1 : ℝ)) x *
        fderiv ℝ (ψ : E → ℝ) x e) =
        fun x ↦ (halfSpaceLT e a).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x := by
      ext x; dsimp only [φ]; rw [divergence_constSmulTestFunction]
    simp_rw [h1]
    rw [setIntegral_mul_divergence_eq_integral, h2,
      integral_indicator (measurableSet_halfSpaceLT e a), integral_halfSpaceLT_divergence he a φ]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    change ⟪ψ (hyperplanePoint e a y) • e, e⟫_ℝ = ψ (hyperplanePoint e a y)
    rw [inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  have hK_le : (volume K).toReal ≤ ∫ y : orthogonalHyperplane e, ψ (hyperplanePoint e a y) := by
    have hint : Integrable (fun y : orthogonalHyperplane e ↦ ψ (hyperplanePoint e a y)) := by
      have hc : HasCompactSupport (fun y : orthogonalHyperplane e ↦ ψ (hyperplanePoint e a y)) :=
        HasCompactSupport.of_support_subset_isCompact
          (ψ.hasCompactSupport.isCompact.image
            (orthogonalHyperplane e).orthogonalProjectionOnto.continuous) fun y hy ↦
          ⟨hyperplanePoint e a y, subset_tsupport _ hy,
            orthogonalProjectionOnto_orthogonalHyperplane_add_smul e y a⟩
      exact (ψ.continuous.comp (continuous_hyperplanePoint e a)).integrable_of_hasCompactSupport hc
    calc (volume K).toReal = ∫ _ in K, (1 : ℝ) := by simp [Measure.real]
      _ ≤ ∫ y in K, ψ (hyperplanePoint e a y) :=
          setIntegral_mono_on (integrableOn_const hK.measure_lt_top.ne) hint.integrableOn
            hK.isClosed.measurableSet fun y hy ↦
            ((hψ_one (hyperplanePoint e a y)).mp (mem_image_of_mem _ hy)).ge
      _ ≤ ∫ y : orthogonalHyperplane e, ψ (hyperplanePoint e a y) :=
          setIntegral_le_integral hint (Eventually.of_forall fun y ↦ hψ_nonneg _)
  rw [← ENNReal.ofReal_toReal hK.measure_lt_top.ne]
  refine (ENNReal.ofReal_le_ofReal hK_le).trans ?_
  rw [← hdiv]
  exact le_directionalVariation ψ hψ_norm e ((halfSpaceLT e a).indicator fun _ ↦ (1 : ℝ))
/-- **Exact directional perimeter of `halfSpaceLT e a` in an open set `Ω`** (`‖e‖ = 1`). -/
@[simp] theorem directionalPerimeter_halfSpaceLT_eq_volume_hyperplaneSlice {e : E} (he : ‖e‖ = 1)
    (Ω : Opens E) (a : ℝ) :
    directionalPerimeter volume Ω e (halfSpaceLT e a) = volume (hyperplaneSlice e a Ω) := by
  refine le_antisymm
    ((directionalPerimeter_le_relativePerimeter he.le (halfSpaceLT e a)).trans
      (relativePerimeter_halfSpaceLT_le_volume_hyperplaneSlice he Ω a)) ?_
  rw [(isOpen_hyperplaneSlice e a Ω.isOpen).measure_eq_iSup_isCompact volume]
  exact iSup₂_le fun K hK_sub ↦ iSup_le fun hK ↦
    volume_compact_le_directionalPerimeter_halfSpaceLT he Ω a hK_sub hK
/-- **Exact relative perimeter of `halfSpaceLT e a` in an open set `Ω`** (`‖e‖ = 1`). -/
@[simp] theorem relativePerimeter_halfSpaceLT_eq_volume_hyperplaneSlice {e : E} (he : ‖e‖ = 1)
    (Ω : Opens E) (a : ℝ) :
    relativePerimeter volume Ω (halfSpaceLT e a) = volume (hyperplaneSlice e a Ω) := by
  refine le_antisymm (relativePerimeter_halfSpaceLT_le_volume_hyperplaneSlice he Ω a) ?_
  rw [← directionalPerimeter_halfSpaceLT_eq_volume_hyperplaneSlice he Ω a]
  exact directionalPerimeter_le_relativePerimeter he.le (halfSpaceLT e a)
@[simp] theorem relativePerimeter_halfSpaceLE_eq_volume_hyperplaneSlice {e : E} (he : ‖e‖ = 1)
    (Ω : Opens E) (a : ℝ) :
    relativePerimeter volume Ω (halfSpaceLE e a) = volume (hyperplaneSlice e a Ω) := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  rw [← relativePerimeter_congr_ae (ae_restrict_of_ae (halfSpaceLT_ae_eq_halfSpaceLE he0 a)),
    relativePerimeter_halfSpaceLT_eq_volume_hyperplaneSlice he]
@[simp] theorem relativePerimeter_halfSpaceGE_eq_volume_hyperplaneSlice {e : E} (he : ‖e‖ = 1)
    (Ω : Opens E) (a : ℝ) :
    relativePerimeter volume Ω (halfSpaceGE e a) = volume (hyperplaneSlice e a Ω) := by
  rw [← compl_halfSpaceLT, relativePerimeter_compl,
    relativePerimeter_halfSpaceLT_eq_volume_hyperplaneSlice he]
@[simp] theorem relativePerimeter_halfSpaceGT_eq_volume_hyperplaneSlice {e : E} (he : ‖e‖ = 1)
    (Ω : Opens E) (a : ℝ) :
    relativePerimeter volume Ω (halfSpaceGT e a) = volume (hyperplaneSlice e a Ω) := by
  rw [← compl_halfSpaceLE, relativePerimeter_compl,
    relativePerimeter_halfSpaceLE_eq_volume_hyperplaneSlice he]
/-- Upper bound on the relative perimeter of `slab e a b` in `Ω` (`‖e‖ = 1`, `a ≤ b`). -/
theorem relativePerimeter_slab_le_add_volume_hyperplaneSlice {e : E} (he : ‖e‖ = 1)
    (Ω : Opens E) {a b : ℝ} (hab : a ≤ b) :
    relativePerimeter volume Ω (slab e a b) ≤
      volume (hyperplaneSlice e a Ω) + volume (hyperplaneSlice e b Ω) := by
  have hsub : halfSpaceLT e a ⊆ halfSpaceLE e b := fun x hx ↦ (mem_halfSpaceLT.mp hx).le.trans hab
  rw [slab_eq_sdiff, add_comm,
    ← relativePerimeter_halfSpaceLE_eq_volume_hyperplaneSlice he Ω b,
    ← relativePerimeter_halfSpaceLT_eq_volume_hyperplaneSlice he Ω a]
  exact relativePerimeter_diff_le_of_subset (measurableSet_halfSpaceLE e b).nullMeasurableSet
    (measurableSet_halfSpaceLT e a).nullMeasurableSet hsub
/-- **Exact relative perimeter of a non-degenerate closed slab `slab e a b` (`a < b`) in `Ω`**. -/
theorem relativePerimeter_slab_eq_add_volume_hyperplaneSlice {e : E} (he : ‖e‖ = 1)
    (Ω : Opens E) {a b : ℝ} (hab : a < b) :
    relativePerimeter volume Ω (slab e a b) =
      volume (hyperplaneSlice e a Ω) + volume (hyperplaneSlice e b Ω) := by
  refine le_antisymm (relativePerimeter_slab_le_add_volume_hyperplaneSlice he Ω hab.le) ?_
  let m : ℝ := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  let U₁ : Opens E := Ω ⊓ ⟨halfSpaceLT e m, isOpen_halfSpaceLT e m⟩
  let U₂ : Opens E := Ω ⊓ ⟨halfSpaceGT e m, isOpen_halfSpaceGT e m⟩
  have hdisj : Disjoint (U₁ : Set E) (U₂ : Set E) := Set.disjoint_left.mpr
    fun _ hx1 hx2 ↦ (lt_trans (mem_halfSpaceLT.mp hx1.2) (mem_halfSpaceGT.mp hx2.2)).false
  have h1 : relativePerimeter volume U₁ (slab e a b) = volume (hyperplaneSlice e a Ω) := by
    have hinter : slab e a b ∩ (U₁ : Set E) = halfSpaceGE e a ∩ (U₁ : Set E) :=
      Set.ext fun x ↦ ⟨fun ⟨⟨ha, _⟩, hU⟩ ↦ ⟨ha, hU⟩,
        fun ⟨ha, hΩ, hxm⟩ ↦ ⟨⟨ha, (hxm.trans hmb).le⟩, hΩ, hxm⟩⟩
    have hslice : hyperplaneSlice e a U₁ = hyperplaneSlice e a Ω := by
      ext y; change hyperplanePoint e a y ∈ Ω ∧ ⟪hyperplanePoint e a y, e⟫_ℝ < m ↔ _
      rw [inner_hyperplanePoint_self he]; exact and_iff_left ham
    rw [relativePerimeter_eq_of_inter_ae_eq (EventuallyEq.of_eq hinter),
      relativePerimeter_halfSpaceGE_eq_volume_hyperplaneSlice he, hslice]
  have h2 : relativePerimeter volume U₂ (slab e a b) = volume (hyperplaneSlice e b Ω) := by
    have hinter : slab e a b ∩ (U₂ : Set E) = halfSpaceLE e b ∩ (U₂ : Set E) :=
      Set.ext fun x ↦ ⟨fun ⟨⟨_, hb⟩, hU⟩ ↦ ⟨hb, hU⟩,
        fun ⟨hb, hΩ, hmx⟩ ↦ ⟨⟨(ham.trans hmx).le, hb⟩, hΩ, hmx⟩⟩
    have hslice : hyperplaneSlice e b U₂ = hyperplaneSlice e b Ω := by
      ext y; change hyperplanePoint e b y ∈ Ω ∧ m < ⟪hyperplanePoint e b y, e⟫_ℝ ↔ _
      rw [inner_hyperplanePoint_self he]; exact and_iff_left hmb
    rw [relativePerimeter_eq_of_inter_ae_eq (EventuallyEq.of_eq hinter),
      relativePerimeter_halfSpaceLE_eq_volume_hyperplaneSlice he, hslice]
  rw [← h1, ← h2]
  exact (relativePerimeter_add_le_sup_of_disjoint hdisj (slab e a b)).trans
    (relativePerimeter_mono (sup_le inf_le_left inf_le_left) (slab e a b))
/-- **Exact relative perimeter of `halfSpaceLT e a` in `Metric.ball c r`**. -/
theorem relativePerimeter_halfSpaceLT_ball_of_abs_lt {e : E} (he : ‖e‖ = 1) (c : E) {a r : ℝ}
    (har : |a - ⟪c, e⟫_ℝ| < r) :
    relativePerimeter volume ⟨Metric.ball c r, Metric.isOpen_ball⟩ (halfSpaceLT e a) =
      volume (Metric.ball (0 : orthogonalHyperplane e)
        (Real.sqrt (r ^ 2 - (a - ⟪c, e⟫_ℝ) ^ 2))) := by
  rw [relativePerimeter_halfSpaceLT_eq_volume_hyperplaneSlice he]
  change volume (hyperplaneSlice e a (Metric.ball c r)) = _
  rw [hyperplaneSlice_ball_of_abs_lt he c har]
  have hpre : (fun y ↦ -(orthogonalHyperplane e).orthogonalProjectionOnto c + y) ⁻¹'
      Metric.ball (0 : orthogonalHyperplane e) (Real.sqrt (r ^ 2 - (a - ⟪c, e⟫_ℝ) ^ 2)) =
      Metric.ball ((orthogonalHyperplane e).orthogonalProjectionOnto c)
        (Real.sqrt (r ^ 2 - (a - ⟪c, e⟫_ℝ) ^ 2)) := by
    ext y; simp [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm]
  rw [← hpre, measure_preimage_add]
/-- **De Giorgi blow-up formula for a half-space through the center of `Metric.ball c r`**. -/
theorem relativePerimeter_halfSpaceLT_ball_inner {e : E} (he : ‖e‖ = 1) (c : E) (r : ℝ) :
    relativePerimeter volume ⟨Metric.ball c r, Metric.isOpen_ball⟩ (halfSpaceLT e ⟪c, e⟫_ℝ) =
      volume (Metric.ball (0 : orthogonalHyperplane e) r) := by
  rcases lt_or_ge 0 r with hr | hr
  · rw [relativePerimeter_halfSpaceLT_ball_of_abs_lt he c (by simpa using hr)]
    simp [Real.sqrt_sq hr.le]
  · rw [relativePerimeter_halfSpaceLT_eq_volume_hyperplaneSlice he]
    change volume (hyperplaneSlice e ⟪c, e⟫_ℝ (Metric.ball c r)) = _
    rw [hyperplaneSlice_ball_inner he c r]; simp [Metric.ball_eq_empty.mpr hr]
/-- **De Giorgi blow-up formula in terms of the unit `(n - 1)`-ball `ω_{n-1}`**. -/
theorem relativePerimeter_halfSpaceLT_ball_inner_eq_unitBall {e : E} (he : ‖e‖ = 1)
    (hdim : 1 < Module.finrank ℝ E) (c : E) {r : ℝ} (hr : 0 ≤ r) :
    relativePerimeter volume ⟨Metric.ball c r, Metric.isOpen_ball⟩ (halfSpaceLT e ⟪c, e⟫_ℝ) =
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
        volume (Metric.ball (0 : orthogonalHyperplane e) 1) := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  have hfin := finrank_orthogonalHyperplane he0
  have hpos : 0 < Module.finrank ℝ (orthogonalHyperplane e) := by omega
  have : Nontrivial (orthogonalHyperplane e) := Module.nontrivial_of_finrank_pos hpos
  rw [relativePerimeter_halfSpaceLT_ball_inner he c r, Measure.addHaar_ball _ _ hr, hfin]
/-- Every half-space `halfSpaceLT e a` (`‖e‖ = 1`) has locally finite perimeter on `E`. -/
theorem hasLocallyFinitePerimeterIn_halfSpaceLT {e : E} (he : ‖e‖ = 1) (a : ℝ) (Ω : Opens E) :
    HasLocallyFinitePerimeterIn volume Ω (halfSpaceLT e a) := by
  refine ⟨(measurableSet_halfSpaceLT e a).nullMeasurableSet, fun U hU _ ↦ ?_⟩
  rw [relativePerimeter_halfSpaceLT_eq_volume_hyperplaneSlice he]
  have hsub : hyperplaneSlice e a U ⊆
      (orthogonalHyperplane e).orthogonalProjectionOnto '' closure (U : Set E) :=
    fun y hy ↦ ⟨hyperplanePoint e a y, subset_closure hy,
      orthogonalProjectionOnto_hyperplanePoint e a y⟩
  exact (measure_mono hsub).trans_lt
    (hU.image (orthogonalHyperplane e).orthogonalProjectionOnto.continuous).measure_lt_top
/-- Global perimeter of `halfSpaceLT e a` (`‖e‖ = 1`) equals `volume (Set.univ : Set H)`. -/
theorem perimeter_halfSpaceLT {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    perimeter volume (halfSpaceLT e a) = volume (Set.univ : Set (orthogonalHyperplane e)) :=
  relativePerimeter_halfSpaceLT_eq_volume_hyperplaneSlice he ⊤ a
/-- When `1 < Module.finrank ℝ E`, `halfSpaceLT e a` (`‖e‖ = 1`) has global perimeter `⊤`. -/
theorem perimeter_halfSpaceLT_eq_top {e : E} (he : ‖e‖ = 1)
    (hdim : 1 < Module.finrank ℝ E) (a : ℝ) :
    perimeter volume (halfSpaceLT e a) = ⊤ := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  have hfin := finrank_orthogonalHyperplane he0
  have hpos : 0 < Module.finrank ℝ (orthogonalHyperplane e) := by omega
  have : Nontrivial (orthogonalHyperplane e) := Module.nontrivial_of_finrank_pos hpos
  rw [perimeter_halfSpaceLT he a, measure_univ_of_isAddLeftInvariant]

end RelativePerimeter

/-! ### Section 4: Steiner symmetrization of half-spaces/slabs & slice convexity characterization -/
@[simp]
theorem steinerFiber_halfSpaceLT {e : E} (he : ‖e‖ = 1) (a : ℝ) (y : orthogonalHyperplane e) :
    steinerFiber e (halfSpaceLT e a) y = Set.Iio a := by
  ext t; simp [mem_steinerFiber_iff, inner_coe_add_smul_self he]
@[simp] theorem steinerFiber_slab {e : E} (he : ‖e‖ = 1) (a b : ℝ) (y : orthogonalHyperplane e) :
    steinerFiber e (slab e a b) y = Set.Icc a b := by
  ext t; simp [mem_steinerFiber_iff, inner_coe_add_smul_self he]
@[simp]
theorem steinerFiber_hyperplane {e : E} (he : ‖e‖ = 1) (a : ℝ) (y : orthogonalHyperplane e) :
    steinerFiber e (hyperplane e a) y = {a} := by
  ext t; simp [mem_steinerFiber_iff, inner_coe_add_smul_self he]
/-- Steiner symmetrization of `hyperplane e a` in direction `e` (`‖e‖ = 1`) is `∅`. -/
@[simp] theorem steinerSymmetrization_hyperplane {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    steinerSymmetrization e (hyperplane e a) = ∅ := by
  ext x; simp [mem_steinerSymmetrization_iff, steinerFiber_hyperplane he,
    symmetricInterval_of_volume_eq_zero (Real.volume_singleton)]
/-- Steiner symmetrization of `halfSpaceLT e a` in direction `e` (`‖e‖ = 1`) is `Set.univ`. -/
@[simp] theorem steinerSymmetrization_halfSpaceLT {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    steinerSymmetrization e (halfSpaceLT e a) = Set.univ := by
  ext x; simp [mem_steinerSymmetrization_iff, steinerFiber_halfSpaceLT he,
    symmetricInterval_of_volume_eq_top Real.volume_Iio]
/-- Steiner symmetrization of `slab e a b` (`a < b`, `‖e‖ = 1`) is the centered slab. -/
theorem steinerSymmetrization_slab {e : E} (he : ‖e‖ = 1) {a b : ℝ} (hab : a < b) :
    steinerSymmetrization e (slab e a b) = slab e (-(b - a) / 2) ((b - a) / 2) := by
  have hvol0 : volume (Icc a b) ≠ 0 := by
    rw [Real.volume_Icc]; exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hvol_top : volume (Icc a b) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  ext x
  rw [mem_steinerSymmetrization_iff, steinerFiber_slab he,
    symmetricInterval_of_volume_ne_zero_of_ne_top hvol0 hvol_top, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_pos.mpr hab).le, mem_Icc, mem_slab]
/-- Convexity of `s` from `OrdConnected` 1D directional slices `steinerFiber e s y`. -/
theorem convex_of_forall_ordConnected_steinerFiber {s : Set E}
    (hs : ∀ e : E, ‖e‖ = 1 → ∀ y : orthogonalHyperplane e, (steinerFiber e s y).OrdConnected) :
    Convex ℝ s := by
  intro x₀ hx₀ x₁ hx₁ a b ha hb hab
  rcases eq_or_ne x₀ x₁ with rfl | hne
  · rw [← add_smul, hab, one_smul]; exact hx₀
  · set d : ℝ := ‖x₁ - x₀‖
    have hd : 0 < d := norm_sub_pos_iff.mpr hne.symm
    let e : E := d⁻¹ • (x₁ - x₀)
    have he : ‖e‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd, inv_mul_cancel₀ hd.ne']
    let y : orthogonalHyperplane e := (orthogonalHyperplane e).orthogonalProjectionOnto x₀
    let t₀ : ℝ := ⟪x₀, e⟫_ℝ
    have hx₀_eq : (y : E) + t₀ • e = x₀ :=
      orthogonalProjection_orthogonalHyperplane_add_inner_smul he x₀
    have hde : d • e = x₁ - x₀ := smul_inv_smul₀ hd.ne' (x₁ - x₀)
    have ht₀_mem : t₀ ∈ steinerFiber e s y := by rwa [mem_steinerFiber_iff, hx₀_eq]
    have ht₁_mem : t₀ + d ∈ steinerFiber e s y := by
      rw [mem_steinerFiber_iff, add_smul, ← add_assoc, hx₀_eq, hde, add_sub_cancel]; exact hx₁
    have hcomb_mem : t₀ + b * d ∈ steinerFiber e s y :=
      (hs e he y).out ht₀_mem ht₁_mem ⟨by linarith [mul_nonneg hb hd.le], by nlinarith⟩
    rw [mem_steinerFiber_iff, add_smul, ← add_assoc, hx₀_eq, mul_smul, hde] at hcomb_mem
    have hcomb_eq : x₀ + b • (x₁ - x₀) = a • x₀ + b • x₁ := by
      rw [show a = 1 - b by linarith, sub_smul, one_smul, smul_sub]; abel
    rwa [← hcomb_eq]
/-- **Directional slice characterization of convexity** via `OrdConnected` 1D fibers. -/
theorem convex_iff_forall_ordConnected_steinerFiber {s : Set E} :
    Convex ℝ s ↔
      ∀ e : E, ‖e‖ = 1 → ∀ y : orthogonalHyperplane e, (steinerFiber e s y).OrdConnected :=
  ⟨fun hs e _ y ↦ hs.ordConnected_steinerFiber e y, convex_of_forall_ordConnected_steinerFiber⟩

end TauCeti
