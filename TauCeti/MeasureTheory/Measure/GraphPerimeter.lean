/-
Copyright (c) 2026 General Intelligence, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module
public import TauCeti.MeasureTheory.Measure.HalfSpacePerimeter
public import TauCeti.MeasureTheory.Measure.Hausdorff.CurveMultiplicity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.PerimeterSlicing
import all TauCeti.MeasureTheory.Measure.IntervalPerimeter
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
import all TauCeti.MeasureTheory.Measure.HalfSpacePerimeter
/-!
# Graph Surface Area, Subgraph Gauss–Green Formula, and BV Boundary Trace
Develops `graphSurfaceArea`, `graphUnitNormal`, subgraph Gauss–Green, and BV trace/gluing bounds.
-/

public section
noncomputable section
open Filter Function MeasureTheory Pointwise Set Submodule TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Distributions Topology
open TauCeti.MeasureTheory
namespace TauCeti
local notation "H⊥" => orthogonalHyperplane
local notation "pt⊥" => hyperplanePoint
local notation "equiv⊥" => orthogonalHyperplaneProdMeasurableEquiv
local notation "mp⊥" => measurePreserving_orthogonalHyperplaneProdMeasurableEquiv
local notation "slice⊥" => hyperplaneSlice
local notation "hsLT" => halfSpaceLT
local notation "hsGT" => halfSpaceGT
section GraphJacobian
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
@[simp] theorem gradient_const (a : ℝ) (y : H) : gradient (fun _ : H ↦ a) y = 0 :=
    (by simp [gradient])
/-- The classical **graph surface Jacobian** `√(1 + ‖gradient f y‖ ^ 2)` of `f : H → ℝ` at `y`. -/
def graphJacobian (f : H → ℝ) (y : H) : ℝ := Real.sqrt (1 + ‖gradient f y‖ ^ 2)
theorem graphJacobian_eq_sqrt_one_add_norm_fderiv_sq (f : H → ℝ) (y : H) : graphJacobian f y =
    Real.sqrt (1 + ‖fderiv ℝ f y‖ ^ 2) := (by simp [graphJacobian, gradient])
@[simp] theorem sq_graphJacobian (f : H → ℝ) (y : H) : (graphJacobian f y) ^ 2 = 1 + ‖gradient f y‖
    ^ 2 := Real.sq_sqrt (by positivity)
theorem one_le_graphJacobian (f : H → ℝ) (y : H) : 1 ≤ graphJacobian f y :=
    (by simp [graphJacobian])
theorem graphJacobian_pos (f : H → ℝ) (y : H) : 0 < graphJacobian f y := zero_lt_one.trans_le
    (one_le_graphJacobian f y)
theorem graphJacobian_nonneg (f : H → ℝ) (y : H) : 0 ≤ graphJacobian f y := (graphJacobian_pos f
    y).le
theorem graphJacobian_le_one_add_norm_gradient (f : H → ℝ) (y : H) : graphJacobian f y ≤ 1 +
    ‖gradient f y‖ := by
  rw [graphJacobian, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + ‖gradient f y‖)]; exact
    Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (gradient f y)])
theorem graphJacobian_le_of_lipschitzWith {f : H → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (y : H) :
    graphJacobian f y ≤ Real.sqrt (1 + (K : ℝ) ^ 2) := by
  rw [graphJacobian_eq_sqrt_one_add_norm_fderiv_sq]; exact Real.sqrt_le_sqrt (add_le_add_right
    ((sq_le_sq₀ (norm_nonneg _) K.coe_nonneg).mpr (norm_fderiv_le_of_lipschitz ℝ hf)) 1)
@[simp] theorem graphJacobian_const (a : ℝ) (y : H) : graphJacobian (fun _ : H ↦ a) y = 1 :=
    (by simp [graphJacobian])
@[simp] theorem graphJacobian_neg (f : H → ℝ) (y : H) : graphJacobian (-f) y = graphJacobian f y :=
    (by simp [graphJacobian_eq_sqrt_one_add_norm_fderiv_sq, fderiv_neg])
@[simp] theorem graphJacobian_add_const (f : H → ℝ) (c : ℝ) (y : H) : graphJacobian (fun z ↦ f z +
    c) y = graphJacobian f y := (by simp [graphJacobian_eq_sqrt_one_add_norm_fderiv_sq])
section NormalVector
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Affine parametrization `graphPoint e f y = (y : E) + f y • e` of the graph of `f` along `e`. -/
def graphPoint (e : E) (f : H⊥ e → ℝ) (y : H⊥ e) : E := (y : E) + f y • e
@[simp] theorem graphPoint_const (e : E) (a : ℝ) (y : H⊥ e) : graphPoint e (fun _ ↦ a) y = pt⊥ e a y
    := (by rfl)
@[simp] theorem inner_graphPoint_self {e : E} (he : ‖e‖ = 1) (f : H⊥ e → ℝ) (y : H⊥ e) : ⟪graphPoint
    e f y, e⟫_ℝ = f y := inner_coe_add_smul_self he y (f y)
@[simp] theorem orthogonalProjectionOnto_graphPoint (e : E) (f : H⊥ e → ℝ) (y : H⊥ e) : (H⊥
    e).orthogonalProjectionOnto (graphPoint e f y) = y :=
    orthogonalProjectionOnto_orthogonalHyperplane_add_smul e y (f y)
theorem continuous_graphPoint (e : E) {f : H⊥ e → ℝ} (hf : Continuous f) : Continuous (graphPoint e
    f) := (H⊥ e).subtypeL.continuous.add (hf.smul continuous_const)
theorem inner_coe_orthogonalHyperplane_add_smul {e : E} (he : ‖e‖ = 1) (w : E) (v : H⊥ e) (t : ℝ) :
    ⟪w, (v : E) + t • e⟫_ℝ = ⟪(H⊥ e).orthogonalProjectionOnto w, v⟫_ℝ + t * ⟪w, e⟫_ℝ := by
  (conv_lhs => rw [← orthogonalProjection_orthogonalHyperplane_add_inner_smul he w]); simp only
    [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    coe_inner_orthogonalHyperplane_eq_zero, inner_coe_orthogonalHyperplane_eq_zero,
    real_inner_self_eq_norm_sq, he, Submodule.coe_inner]; ring
variable [FiniteDimensional ℝ E]
/-- Unnormalized outward normal `((-gradient f y : H⊥ e) : E) + e`. -/
def graphNormalVec (e : E) (f : H⊥ e → ℝ) (y : H⊥ e) : E := ((-gradient f y : H⊥ e) : E) + e
/-- Normalized outward unit normal `(graphJacobian f y)⁻¹ • graphNormalVec e f y`. -/
def graphUnitNormal (e : E) (f : H⊥ e → ℝ) (y : H⊥ e) : E := (graphJacobian f y)⁻¹ • graphNormalVec
    e f y
@[simp] theorem graphNormalVec_const (e : E) (a : ℝ) (y : H⊥ e) : graphNormalVec e (fun _ ↦ a) y = e
    := (by simp [graphNormalVec])
@[simp] theorem graphUnitNormal_const (e : E) (a : ℝ) (y : H⊥ e) : graphUnitNormal e (fun _ ↦ a) y =
    e := (by simp [graphUnitNormal])
theorem graphNormalVec_eq_smul_graphUnitNormal (e : E) (f : H⊥ e → ℝ) (y : H⊥ e) : graphNormalVec e
    f y = graphJacobian f y • graphUnitNormal e f y :=
    (by rw [graphUnitNormal, smul_smul, mul_inv_cancel₀ (graphJacobian_pos f y).ne', one_smul])
theorem inner_graphNormalVec {e : E} (he : ‖e‖ = 1) (w : E) (f : H⊥ e → ℝ) (y : H⊥ e) : ⟪w,
    graphNormalVec e f y⟫_ℝ = -⟪(H⊥ e).orthogonalProjectionOnto w, gradient f y⟫_ℝ + ⟪w, e⟫_ℝ := by
  have h1 : graphNormalVec e f y = ((-gradient f y : H⊥ e) : E) + (1 : ℝ) • e :=
    (by simp [graphNormalVec]); rw [h1, inner_coe_orthogonalHyperplane_add_smul he, inner_neg_right,
    one_mul]
theorem norm_graphNormalVec_sq {e : E} (he : ‖e‖ = 1) (f : H⊥ e → ℝ) (y : H⊥ e) : ‖graphNormalVec e
    f y‖ ^ 2 = 1 + ‖gradient f y‖ ^ 2 := by
  have h1 : graphNormalVec e f y = ((-gradient f y : H⊥ e) : E) + (1 : ℝ) • e :=
    (by simp [graphNormalVec]); rw [h1, norm_coe_add_smul_sq he, norm_neg, one_pow, add_comm]
@[simp] theorem norm_graphNormalVec {e : E} (he : ‖e‖ = 1) (f : H⊥ e → ℝ) (y : H⊥ e) :
    ‖graphNormalVec e f y‖ = graphJacobian f y :=
    (by rw [graphJacobian, ← norm_graphNormalVec_sq he, Real.sqrt_sq (norm_nonneg _)])
@[simp] theorem norm_graphUnitNormal {e : E} (he : ‖e‖ = 1) (f : H⊥ e → ℝ) (y : H⊥ e) :
    ‖graphUnitNormal e f y‖ = 1 := by
  rw [graphUnitNormal, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (graphJacobian_nonneg f y)),
    norm_graphNormalVec he, inv_mul_cancel₀ (graphJacobian_pos f y).ne']
theorem inner_graphUnitNormal_self {e : E} (he : ‖e‖ = 1) (f : H⊥ e → ℝ) (y : H⊥ e) :
    ⟪graphUnitNormal e f y, graphUnitNormal e f y⟫_ℝ = 1 :=
    (by rw [real_inner_self_eq_norm_sq, norm_graphUnitNormal he, one_pow])
@[simp] theorem inner_graphNormalVec_self_dir {e : E} (he : ‖e‖ = 1) (f : H⊥ e → ℝ) (y : H⊥ e) :
    ⟪graphNormalVec e f y, e⟫_ℝ = 1 := by
  have h1 : graphNormalVec e f y = ((-gradient f y : H⊥ e) : E) + (1 : ℝ) • e :=
    (by simp [graphNormalVec]); rw [h1, inner_coe_add_smul_self he]
theorem inner_graphUnitNormal_self_dir {e : E} (he : ‖e‖ = 1) (f : H⊥ e → ℝ) (y : H⊥ e) :
    ⟪graphUnitNormal e f y, e⟫_ℝ = (graphJacobian f y)⁻¹ := by
  rw [graphUnitNormal, inner_smul_left, RCLike.conj_to_real, inner_graphNormalVec_self_dir he,
    mul_one]
theorem inner_tangent_graphNormalVec_eq_zero {e : E} (he : ‖e‖ = 1) (f : H⊥ e → ℝ) (y v : H⊥ e) :
    ⟪(v : E) + (fderiv ℝ f y v) • e, graphNormalVec e f y⟫_ℝ = 0 := by
  rw [inner_graphNormalVec he, orthogonalProjectionOnto_orthogonalHyperplane_add_smul,
    inner_coe_add_smul_self he, real_inner_comm (gradient f y) v]; dsimp only [gradient]; rw
    [InnerProductSpace.toDual_symm_apply, neg_add_cancel]
theorem inner_tangent_graphUnitNormal_eq_zero {e : E} (he : ‖e‖ = 1) (f : H⊥ e → ℝ) (y v : H⊥ e) :
    ⟪(v : E) + (fderiv ℝ f y v) • e, graphUnitNormal e f y⟫_ℝ = 0 :=
    (by rw [graphUnitNormal, inner_smul_right, inner_tangent_graphNormalVec_eq_zero he, mul_zero])
end NormalVector
variable [MeasurableSpace H]
/-- The **graph surface measure** `μ.withDensity (fun y ↦ ENNReal.ofReal (graphJacobian f y))`. -/
def graphSurfaceMeasure (μ : Measure H) (f : H → ℝ) : Measure H := μ.withDensity (fun y ↦
    ENNReal.ofReal (graphJacobian f y))
/-- The **graph surface area** `∫⁻ y in s, ENNReal.ofReal (graphJacobian f y) ∂μ` of `s : Set H`. -/
def graphSurfaceArea (μ : Measure H) (f : H → ℝ) (s : Set H) : ℝ≥0∞ := ∫⁻ y in s, ENNReal.ofReal
    (graphJacobian f y) ∂μ
theorem graphSurfaceMeasure_apply (μ : Measure H) (f : H → ℝ) {s : Set H} (hs : MeasurableSet s) :
    graphSurfaceMeasure μ f s = graphSurfaceArea μ f s := withDensity_apply _ hs
@[simp] theorem graphSurfaceArea_empty (μ : Measure H) (f : H → ℝ) : graphSurfaceArea μ f ∅ = 0 :=
    (by simp [graphSurfaceArea])
@[simp] theorem graphSurfaceArea_const (μ : Measure H) (a : ℝ) (s : Set H) : graphSurfaceArea μ (fun
    _ : H ↦ a) s = μ s := (by simp [graphSurfaceArea])
theorem measure_le_graphSurfaceArea (μ : Measure H) (f : H → ℝ) (s : Set H) : μ s ≤ graphSurfaceArea
    μ f s := by
  rw [← Measure.restrict_apply_univ, ← lintegral_one]; exact lintegral_mono fun y ↦
    ENNReal.one_le_ofReal.mpr (one_le_graphJacobian f y)
theorem graphSurfaceArea_le_of_lipschitzWith (μ : Measure H) {f : H → ℝ} {K : ℝ≥0} (hf :
    LipschitzWith K f) (s : Set H) : graphSurfaceArea μ f s ≤ ENNReal.ofReal (Real.sqrt (1 + (K : ℝ)
    ^ 2)) * μ s := (lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal
    (graphJacobian_le_of_lipschitzWith hf y)).trans (setLIntegral_const _ _).le
theorem isLocallyFiniteMeasure_graphSurfaceMeasure_of_lipschitzWith [OpensMeasurableSpace H] (μ :
    Measure H) [IsLocallyFiniteMeasure μ] {f : H → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsLocallyFiniteMeasure (graphSurfaceMeasure μ f) := by
  refine ⟨fun x ↦ ?_⟩; rcases (μ.finiteAt_nhds x).exists_mem_basis (nhds_basis_opens x) with ⟨U,
    ⟨hxU, hUopen⟩, hUfin⟩; refine ⟨U, hUopen.mem_nhds hxU, ?_⟩; rw [graphSurfaceMeasure_apply μ f
    hUopen.measurableSet]; exact (graphSurfaceArea_le_of_lipschitzWith μ hf U).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUfin)
@[simp] theorem gradient_real_eq_deriv (f : ℝ → ℝ) (t : ℝ) : gradient f t = deriv f t := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := ℝ) (x := 1) (y := fderiv ℝ f t); rwa
    [real_inner_comm, RCLike.inner_apply, RCLike.conj_to_real, mul_one] at h
theorem graphJacobian_real (f : ℝ → ℝ) (t : ℝ) : graphJacobian f t = Real.sqrt (1 + (deriv f t) ^ 2)
    := (by rw [graphJacobian, gradient_real_eq_deriv, Real.norm_eq_abs, sq_abs])
theorem graphSurfaceArea_real_Icc_eq_eVariationOn_planarGraph {f : ℝ → ℝ} {a b : ℝ} (hf :
    AbsolutelyContinuousOnInterval f a b) : graphSurfaceArea volume f (Icc a b) = eVariationOn
    (planarGraph f) (Icc a b) := by
  rw [hf.eVariationOn_planarGraph_eq_lintegral, graphSurfaceArea]; simp_rw [graphJacobian_real]
theorem graphSurfaceArea_real_Icc_eq_euclideanHausdorffMeasure_planarGraph {f : ℝ → ℝ} {a b : ℝ} (hf
    : AbsolutelyContinuousOnInterval f a b) : graphSurfaceArea volume f (Icc a b) = μHE[1]
    (planarGraph f '' Icc a b) := by
  rw [euclideanHausdorffMeasure_planarGraph_eq_lintegral hf, graphSurfaceArea]; simp_rw
    [graphJacobian_real]
theorem graphSurfaceArea_real_Icc_eq_eVariationOn_of_contDiffOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) : graphSurfaceArea volume f (Icc a b) = eVariationOn
    (planarGraph f) (Icc a b) := by
  exact graphSurfaceArea_real_Icc_eq_eVariationOn_planarGraph (uIcc_of_le hab ▸
    hf).absolutelyContinuousOnInterval
end GraphJacobian
local notation "pt_G" => graphPoint
local notation "ν_G" => graphNormalVec
local notation "n_G" => graphUnitNormal
section ProductMeasure
variable {H : Type*}
/-- The open **subgraph** `{p : H × ℝ | p.2 < f p.1}` of `f : H → ℝ`. -/
def subgraph (f : H → ℝ) : Set (H × ℝ) := {p : H × ℝ | p.2 < f p.1}
/-- The **graph** `{p : H × ℝ | p.2 = f p.1}` of `f : H → ℝ`. -/
def graphSet (f : H → ℝ) : Set (H × ℝ) := {p : H × ℝ | p.2 = f p.1}
@[simp] theorem mem_subgraph {f : H → ℝ} {p : H × ℝ} : p ∈ subgraph f ↔ p.2 < f p.1 := Iff.rfl
@[simp] theorem mem_graphSet {f : H → ℝ} {p : H × ℝ} : p ∈ graphSet f ↔ p.2 = f p.1 := Iff.rfl
variable [MeasurableSpace H] {μ : Measure H} {f : H → ℝ}
theorem measurableSet_subgraph (hf : Measurable f) : MeasurableSet (subgraph f) := measurableSet_lt
    measurable_snd (hf.comp measurable_fst)
theorem measurableSet_graphSet (hf : Measurable f) : MeasurableSet (graphSet f) :=
    measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
theorem measure_prod_graphSet (hf : Measurable f) : (μ.prod (volume : Measure ℝ)) (graphSet f) = 0
    := by
  rw [Measure.prod_apply (measurableSet_graphSet hf), lintegral_eq_zero_iff
    (measurable_measure_prodMk_left (measurableSet_graphSet hf))]; refine Eventually.of_forall fun y
    ↦ ?_; have hpre : Prod.mk y ⁻¹' graphSet f = {f y} := Set.ext fun _ ↦ (by simp [graphSet]); simp
    [hpre]
end ProductMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The open subgraph along `e : E`. -/
def subgraphOn (e : E) (f : H⊥ e → ℝ) : Set E := {x : E | ⟪x, e⟫_ℝ < f ((H⊥
    e).orthogonalProjectionOnto x)}
/-- The closed subgraph along `e : E`. -/
def subgraphLEOn (e : E) (f : H⊥ e → ℝ) : Set E := {x : E | ⟪x, e⟫_ℝ ≤ f ((H⊥
    e).orthogonalProjectionOnto x)}
/-- The open epigraph along `e : E`. -/
def epigraphOn (e : E) (f : H⊥ e → ℝ) : Set E := {x : E | f ((H⊥ e).orthogonalProjectionOnto x) <
    ⟪x, e⟫_ℝ}
/-- The closed epigraph along `e : E`. -/
def epigraphGEOn (e : E) (f : H⊥ e → ℝ) : Set E := {x : E | f ((H⊥ e).orthogonalProjectionOnto x) ≤
    ⟪x, e⟫_ℝ}
/-- The graph hypersurface along `e : E`. -/
def graphOn (e : E) (f : H⊥ e → ℝ) : Set E := {x : E | ⟪x, e⟫_ℝ = f ((H⊥ e).orthogonalProjectionOnto
    x)}
/-- The slice `{y : H⊥ e | pt_G e f y ∈ s}` of `s : Set E` along `f`. -/
def graphSlice (e : E) (f : H⊥ e → ℝ) (s : Set E) : Set (H⊥ e) := {y : H⊥ e | pt_G e f y ∈ s}
local notation "sub_G" => subgraphOn
local notation "subLE_G" => subgraphLEOn
@[simp] theorem subgraphOn_const (e : E) (a : ℝ) : sub_G e (fun _ ↦ a) = hsLT e a := (by rfl)
@[simp] theorem subgraphLEOn_const (e : E) (a : ℝ) : subLE_G e (fun _ ↦ a) = halfSpaceLE e a :=
    (by rfl)
@[simp] theorem epigraphOn_const (e : E) (a : ℝ) : epigraphOn e (fun _ ↦ a) = hsGT e a := (by rfl)
@[simp] theorem epigraphGEOn_const (e : E) (a : ℝ) : epigraphGEOn e (fun _ ↦ a) = halfSpaceGE e a :=
    (by rfl)
@[simp] theorem graphOn_const (e : E) (a : ℝ) : graphOn e (fun _ ↦ a) = hyperplane e a := (by rfl)
@[simp] theorem graphSlice_const (e : E) (a : ℝ) (s : Set E) : graphSlice e (fun _ ↦ a) s = slice⊥ e
    a s := (by rfl)
@[simp] theorem compl_subgraphOn (e : E) (f : H⊥ e → ℝ) : (sub_G e f)ᶜ = epigraphGEOn e f := Set.ext
    fun _ ↦ (by simp [subgraphOn, epigraphGEOn])
@[simp] theorem compl_subgraphLEOn (e : E) (f : H⊥ e → ℝ) : (subLE_G e f)ᶜ = epigraphOn e f :=
    Set.ext fun _ ↦ (by simp [subgraphLEOn, epigraphOn])
variable {e x : E} {f : H⊥ e → ℝ}
@[simp] theorem mem_subgraphOn : x ∈ sub_G e f ↔ ⟪x, e⟫_ℝ < f ((H⊥ e).orthogonalProjectionOnto x) :=
    Iff.rfl
@[simp] theorem mem_subgraphLEOn : x ∈ subLE_G e f ↔ ⟪x, e⟫_ℝ ≤ f ((H⊥ e).orthogonalProjectionOnto
    x) := Iff.rfl
@[simp] theorem mem_epigraphOn : x ∈ epigraphOn e f ↔ f ((H⊥ e).orthogonalProjectionOnto x) < ⟪x,
    e⟫_ℝ := Iff.rfl
@[simp] theorem mem_epigraphGEOn : x ∈ epigraphGEOn e f ↔ f ((H⊥ e).orthogonalProjectionOnto x) ≤
    ⟪x, e⟫_ℝ := Iff.rfl
theorem subgraphOn_subset_subgraphLEOn (e : E) (f : H⊥ e → ℝ) : sub_G e f ⊆ subLE_G e f := fun _ hx
    ↦ mem_subgraphLEOn.mpr (le_of_lt (mem_subgraphOn.mp hx))
theorem subgraphLEOn_diff_subgraphOn (e : E) (f : H⊥ e → ℝ) : subLE_G e f \ sub_G e f = graphOn e f
    := Set.ext fun _ ↦ (by simp [subgraphLEOn, subgraphOn, graphOn, le_antisymm_iff])
theorem subgraphOn_union_graphOn (e : E) (f : H⊥ e → ℝ) : sub_G e f ∪ graphOn e f = subLE_G e f :=
    (by ext; simp [subgraphOn, graphOn, subgraphLEOn, le_iff_lt_or_eq])
variable (e) in theorem isOpen_subgraphOn (hf : Continuous f) : IsOpen (sub_G e f) := isOpen_lt
    (continuous_id.inner continuous_const) (hf.comp (H⊥ e).orthogonalProjectionOnto.continuous)
variable (e) in theorem isClosed_subgraphLEOn (hf : Continuous f) : IsClosed (subLE_G e f) :=
    isClosed_le (continuous_id.inner continuous_const) (hf.comp (H⊥
    e).orthogonalProjectionOnto.continuous)
variable (e) in theorem isOpen_epigraphOn (hf : Continuous f) : IsOpen (epigraphOn e f) := isOpen_lt
    (hf.comp (H⊥ e).orthogonalProjectionOnto.continuous) (continuous_id.inner continuous_const)
variable (e) in theorem isClosed_epigraphGEOn (hf : Continuous f) : IsClosed (epigraphGEOn e f) :=
    isClosed_le (hf.comp (H⊥ e).orthogonalProjectionOnto.continuous) (continuous_id.inner
    continuous_const)
variable (e) in theorem isClosed_graphOn (hf : Continuous f) : IsClosed (graphOn e f) := isClosed_eq
    (continuous_id.inner continuous_const) (hf.comp (H⊥ e).orthogonalProjectionOnto.continuous)
variable (e) in theorem isOpen_graphSlice (hf : Continuous f) {s : Set E} (hs : IsOpen s) : IsOpen
    (graphSlice e f s) := hs.preimage (continuous_graphPoint e hf)
theorem closure_subgraphOn (he : e ≠ 0) (hf : Continuous f) : closure (sub_G e f) = subLE_G e f :=
    by
  have hlim (x : E) := tendsto_const_nhds (x := x).sub ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜
    := ℝ)).smul_const e); refine Subset.antisymm ((isClosed_subgraphLEOn e
    hf).closure_subset_iff.mpr (subgraphOn_subset_subgraphLEOn e f)) fun x hx ↦
    mem_closure_of_tendsto (by simpa only [zero_smul, sub_zero] using hlim x) (Eventually.of_forall
    fun n ↦ ?_); rw [mem_subgraphOn, map_sub,
    orthogonalProjectionOnto_orthogonalHyperplane_smul_self, sub_zero, inner_sub_left,
    inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]; linarith [hx.out, mul_pos
    (by positivity : 0 < 1 / (n + 1 : ℝ)) (sq_pos_of_pos (norm_pos_iff.mpr he))]
theorem closure_epigraphOn (he : e ≠ 0) (hf : Continuous f) : closure (epigraphOn e f) =
    epigraphGEOn e f := by
  have hlim (x : E) := tendsto_const_nhds (x := x).add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜
    := ℝ)).smul_const e); refine Subset.antisymm ((isClosed_epigraphGEOn e
    hf).closure_subset_iff.mpr fun _ hx ↦ mem_epigraphGEOn.mpr (le_of_lt (mem_epigraphOn.mp hx)))
    fun x hx ↦ mem_closure_of_tendsto (by simpa only [zero_smul, add_zero] using hlim x)
    (Eventually.of_forall fun n ↦ ?_); rw [mem_epigraphOn, map_add,
    orthogonalProjectionOnto_orthogonalHyperplane_smul_self, add_zero, inner_add_left,
    inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]; linarith [hx.out, mul_pos
    (by positivity : 0 < 1 / (n + 1 : ℝ)) (sq_pos_of_pos (norm_pos_iff.mpr he))]
theorem interior_subgraphLEOn (he : e ≠ 0) (hf : Continuous f) : interior (subLE_G e f) = sub_G e f
    := (by simp [interior_eq_compl_closure_compl, closure_epigraphOn he hf, ← compl_subgraphOn])
theorem interior_closure_subgraphOn (he : e ≠ 0) (hf : Continuous f) : interior (closure (sub_G e
    f)) = sub_G e f := (by rw [closure_subgraphOn he hf, interior_subgraphLEOn he hf])
theorem frontier_subgraphOn (he : e ≠ 0) (hf : Continuous f) : frontier (sub_G e f) = graphOn e f :=
    by
  rw [frontier, closure_subgraphOn he hf, (isOpen_subgraphOn e hf).interior_eq,
    subgraphLEOn_diff_subgraphOn]
variable (e) in theorem exists_testFunction_eq_one_on_graphPoint [FiniteDimensional ℝ E] (U : Opens
    E) (hf : Continuous f) {K : Set (H⊥ e)} (hK_sub : K ⊆ graphSlice e f U) (hK : IsCompact K) : ∃ ψ
    : 𝓓(U, ℝ), (∀ x, 0 ≤ ψ x) ∧ (∀ x, ‖ψ x‖ ≤ 1) ∧ ∀ y ∈ K, ψ (pt_G e f y) = 1 := by
  let KE : Set E := pt_G e f '' K; have hKE_compact : IsCompact KE := hK.image
    (continuous_graphPoint e hf); rcases hKE_compact.exists_cthickening_subset_open U.isOpen
    (image_subset_iff.mpr hK_sub) with ⟨δ, hδ, hδ_sub⟩; rcases exists_contDiff_support_eq_eq_one_iff
    (n := ⊤) (Metric.isOpen_thickening (δ := δ) (E := KE)) hKE_compact.isClosed
    (Metric.self_subset_thickening hδ KE) with ⟨ψ_raw, hψ_diff, hψ_range, hψ_supp, hψ_one⟩; have
    htsupp_sub : tsupport ψ_raw ⊆ Metric.cthickening δ KE :=
    (by rw [tsupport, hψ_supp]; exact Metric.closure_thickening_subset_cthickening δ KE); let ψ :
    𝓓(U, ℝ) := ⟨ψ_raw, hψ_diff, HasCompactSupport.of_support_subset_isCompact
    hKE_compact.cthickening (subset_tsupport ψ_raw |>.trans htsupp_sub), htsupp_sub.trans hδ_sub⟩;
    have hψ_nonneg : ∀ x, 0 ≤ ψ x := fun x ↦ (hψ_range (mem_range_self x)).1; refine ⟨ψ, hψ_nonneg,
    fun x ↦ ?_, fun y hy ↦ (hψ_one (pt_G e f y)).mp (mem_image_of_mem _ hy)⟩; rw [Real.norm_eq_abs,
    abs_of_nonneg (hψ_nonneg x)]; exact (hψ_range (mem_range_self x)).2
theorem hasCompactSupport_divergence {ψ : E → E} (hc : HasCompactSupport ψ) : HasCompactSupport
    (divergence ψ) := HasCompactSupport.of_support_subset_isCompact hc.isCompact fun x hx ↦
    by_contra fun hnx ↦ hx
    (by simp [divergence, (notMem_tsupport_iff_eventuallyEq.mp hnx).fderiv_eq])
variable [MeasurableSpace E] [BorelSpace E]
variable (e) in theorem measurableSet_subgraphOn (hf : Measurable f) : MeasurableSet (sub_G e f) :=
    measurableSet_lt (continuous_id.inner continuous_const).measurable (hf.comp (H⊥
    e).orthogonalProjectionOnto.continuous.measurable)
variable (e) in theorem measurableSet_subgraphLEOn (hf : Measurable f) : MeasurableSet (subLE_G e f)
    := measurableSet_le (continuous_id.inner continuous_const).measurable (hf.comp (H⊥
    e).orthogonalProjectionOnto.continuous.measurable)
variable (e) in theorem measurableSet_epigraphOn (hf : Measurable f) : MeasurableSet (epigraphOn e
    f) := measurableSet_lt (hf.comp (H⊥ e).orthogonalProjectionOnto.continuous.measurable)
    (continuous_id.inner continuous_const).measurable
variable (e) in theorem measurableSet_graphOn (hf : Measurable f) : MeasurableSet (graphOn e f) :=
    measurableSet_eq_fun (continuous_id.inner continuous_const).measurable (hf.comp (H⊥
    e).orthogonalProjectionOnto.continuous.measurable)
@[simp] theorem equiv_preimage_subgraphOn (he : ‖e‖ = 1) (f : H⊥ e → ℝ) : (equiv⊥ he) ⁻¹' sub_G e f
    = subgraph f := by
  ext ⟨y, t⟩; simp [subgraphOn, subgraph, orthogonalHyperplaneProdMeasurableEquiv_apply,
    inner_coe_add_smul_self he, orthogonalProjectionOnto_orthogonalHyperplane_add_smul]
@[simp] theorem equiv_preimage_graphOn (he : ‖e‖ = 1) (f : H⊥ e → ℝ) : (equiv⊥ he) ⁻¹' graphOn e f =
    graphSet f := by
  ext ⟨y, t⟩; simp [graphOn, graphSet, orthogonalHyperplaneProdMeasurableEquiv_apply,
    inner_coe_add_smul_self he, orthogonalProjectionOnto_orthogonalHyperplane_add_smul]
variable [FiniteDimensional ℝ E]
theorem volume_graphOn (he : ‖e‖ = 1) (hf : Measurable f) : volume (graphOn e f) = 0 := by
  rw [← (mp⊥ he).measure_preimage (measurableSet_graphOn e hf).nullMeasurableSet,
    equiv_preimage_graphOn, measure_prod_graphSet hf]
theorem subgraphOn_ae_eq_subgraphLEOn (he : ‖e‖ = 1) (hf : Measurable f) : sub_G e f =ᵐ[volume]
    subLE_G e f := by
  rw [← subgraphOn_union_graphOn]; exact (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr
    (volume_graphOn he hf))).symm
theorem epigraphOn_ae_eq_epigraphGEOn (he : ‖e‖ = 1) (hf : Measurable f) : epigraphOn e f =ᵐ[volume]
    epigraphGEOn e f := (by simpa using (subgraphOn_ae_eq_subgraphLEOn he hf).symm.compl)
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in theorem
    hasCompactSupport_graphComp {α : Type*} [Zero α] {g : E → α} (hg : HasCompactSupport g) (k : H⊥
    e → ℝ) {h : H⊥ e → ℝ} (hh : ∀ y : H⊥ e, g ((y : E) + k y • e) = 0 → h y = 0) : HasCompactSupport
    h := HasCompactSupport.of_support_subset_isCompact (hg.isCompact.image (H⊥
    e).orthogonalProjectionOnto.continuous) fun y hy ↦ ⟨(y : E) + k y • e, subset_tsupport g fun h0
    ↦ hy (hh y h0), orthogonalProjectionOnto_orthogonalHyperplane_add_smul e y (k y)⟩
theorem setIntegral_subgraphOn_eq (he : ‖e‖ = 1) (hf : Measurable f) {G : E → ℝ} (hG : Integrable G
    volume) : ∫ x in sub_G e f, G x = ∫ y, ∫ t in Iio (f y), G ((y : E) + t • e) := by
  have hint : Integrable ((subgraph f).indicator fun p ↦ G (equiv⊥ he p)) (volume.prod volume) :=
    (((mp⊥ he).integrable_comp_emb (equiv⊥ he).measurableEmbedding).mpr hG).indicator
    (measurableSet_subgraph hf); rw [← (mp⊥ he).setIntegral_preimage_emb (equiv⊥
    he).measurableEmbedding G (sub_G e f), equiv_preimage_subgraphOn he f, ← integral_indicator
    (measurableSet_subgraph hf), integral_prod _ hint]; refine integral_congr_ae
    (Eventually.of_forall fun y ↦ ?_); have h1 : (fun t : ℝ ↦ (subgraph f).indicator (fun p ↦ G
    (equiv⊥ he p)) (y, t)) = (Iio (f y)).indicator (fun t : ℝ ↦ G ((y : E) + t • e)) := (by
    ext t; by_cases ht : t < f y <;> simp [subgraph, ht,
      orthogonalHyperplaneProdMeasurableEquiv_apply]); dsimp only; rw [h1, integral_indicator
        measurableSet_Iio]
theorem integral_subgraphOn_fderiv (he : ‖e‖ = 1) (hf : Measurable f) {U : Opens E} (ψ : 𝓓(U, ℝ)) :
    ∫ x in sub_G e f, fderiv ℝ (ψ : E → ℝ) x e = ∫ y, ψ (pt_G e f y) := by
  let ψ_top : 𝓓((⊤ : Opens E), ℝ) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_univ _⟩; have h1 :
    (fun x : E ↦ fderiv ℝ (ψ : E → ℝ) x e) = divergence (constSmulTestFunction ψ e : E → E) :=
    funext fun x ↦ (divergence_constSmulTestFunction ψ e x).symm; rw [setIntegral_subgraphOn_eq he
    hf (h1 ▸ integrable_divergence_testFunction _)]; refine integral_congr_ae (Eventually.of_forall
    fun y ↦ ?_); have h2 : (fun t : ℝ ↦ fderiv ℝ (ψ : E → ℝ) ((y : E) + t • e) e) = divergence
    (steinerFiberTestFunction ψ_top he y : ℝ → ℝ) := funext fun t ↦
    (divergence_steinerFiberTestFunction ψ_top he y t).symm; dsimp only; rw [h2,
    integral_Iio_divergence_testFunction]; rfl
theorem indicator_mul_eq {α : Type*} (s : Set α) (u g : α → ℝ) : (fun x ↦ s.indicator u x * g x) =
    s.indicator (fun x ↦ u x * g x) := (by ext x; by_cases hx : x ∈ s <;> simp [hx])
theorem setIntegral_indicator_subgraphOn_fderiv (he : ‖e‖ = 1) (U : Opens E) (hf : Measurable f) (ψ
    : 𝓓(U, ℝ)) : ∫ x in (U : Set E), (sub_G e f).indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ (ψ : E →
    ℝ) x e = ∫ y, ψ (pt_G e f y) := by
  simp_rw [indicator_mul_eq, one_mul]; rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx
    ↦ by simp [fderiv_testFunction_eq_zero_of_notMem ψ e hx], integral_indicator
    (measurableSet_subgraphOn e hf), integral_subgraphOn_fderiv he hf ψ]
theorem directionalPerimeter_subgraphOn_le_volume_graphSlice (he : ‖e‖ = 1) (U : Opens E) (hf :
    Measurable f) : directionalPerimeter volume U e (sub_G e f) ≤ volume (graphSlice e f U) := by
  refine iSup₂_le fun ψ hψ ↦ ?_; rw [setIntegral_indicator_subgraphOn_fderiv he U hf ψ, ←
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := graphSlice e f U) (f := fun y ↦ ψ (pt_G e
    f y)) fun y hy ↦ ψ.zero_on_compl hy]; refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
    ?_; rw [← Real.enorm_eq_ofReal_abs]; refine (enorm_integral_le_lintegral_enorm _).trans
    ((lintegral_mono fun y ↦
    by rw [Real.enorm_eq_ofReal_abs, ← Real.norm_eq_abs, ENNReal.ofReal_le_one]; exact hψ _).trans
    (by simp))
@[simp] theorem directionalPerimeter_subgraphOn_eq_volume_graphSlice (he : ‖e‖ = 1) (U : Opens E)
    (hf : Continuous f) : directionalPerimeter volume U e (sub_G e f) = volume (graphSlice e f U) :=
    by
  refine le_antisymm (directionalPerimeter_subgraphOn_le_volume_graphSlice he U hf.measurable) ?_;
    rw [(isOpen_graphSlice e hf U.isOpen).measure_eq_iSup_isCompact volume]; refine iSup₂_le fun K
    hK_sub ↦ iSup_le fun hK ↦ ?_; rcases exists_testFunction_eq_one_on_graphPoint e U hf hK_sub hK
    with ⟨ψ, hψ_nonneg, hψ_norm, hψ_one⟩; have hint : Integrable _ volume := (ψ.continuous.comp
    (continuous_graphPoint e hf)).integrable_of_hasCompactSupport (hasCompactSupport_graphComp
    ψ.hasCompactSupport f fun _ ↦ id); have hK_le : (volume K).toReal ≤ ∫ y, ψ (pt_G e f y) := (by
    rw [show (volume K).toReal = ∫ _ in K, (1 : ℝ) by simp [Measure.real]]; exact
      (setIntegral_mono_on (integrableOn_const hK.measure_lt_top.ne) hint.integrableOn
      hK.isClosed.measurableSet fun y hy ↦ (hψ_one y hy).ge).trans (setIntegral_le_integral hint
      (Eventually.of_forall fun _ ↦ hψ_nonneg _))); rw [← ENNReal.ofReal_toReal
        hK.measure_lt_top.ne]; refine (ENNReal.ofReal_le_ofReal hK_le).trans ?_; rw [←
        setIntegral_indicator_subgraphOn_fderiv he U hf.measurable ψ]; exact le_directionalVariation
        ψ hψ_norm e ((sub_G e f).indicator fun _ ↦ (1 : ℝ))
theorem volume_graphSlice_le_relativePerimeter_subgraphOn (he : ‖e‖ = 1) (U : Opens E) (hf :
    Continuous f) : volume (graphSlice e f U) ≤ relativePerimeter volume U (sub_G e f) := by
  rw [← directionalPerimeter_subgraphOn_eq_volume_graphSlice he U hf]; exact
    directionalPerimeter_le_relativePerimeter he.le (sub_G e f)
theorem integral_fderiv_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] {g : H → ℝ} (hg : ContDiff ℝ 1 g) (hc
    : HasCompactSupport g) (v : H) : ∫ y : H, fderiv ℝ g y v = 0 := by
  have hg' := (hg.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := v)); have hc' :
    HasCompactSupport fun y : H ↦ fderiv ℝ g y v := HasCompactSupport.of_support_subset_isCompact
    hc.isCompact fun y hy ↦ by_contra fun hny ↦ hy
    (by simp [(notMem_tsupport_iff_eventuallyEq.mp hny).fderiv_eq]); simpa using
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure H)) (f := fun _ : H
    ↦ (1 : ℝ)) (g := g) (v := v) (by simp) (by simpa using hg'.integrable_of_hasCompactSupport hc')
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc) (fun _ _ ↦
    differentiableAt_const 1) (fun y _ ↦ hg.differentiable one_ne_zero y)
theorem integral_Iio_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (a : ℝ) : ∫
    t in Iio a, deriv g t = g a := by
  have hc' : HasCompactSupport (deriv g) := HasCompactSupport.of_support_subset_isCompact
    hc.isCompact fun t ht ↦ by_contra fun hnt ↦ ht
    (by simp [(notMem_tsupport_iff_eventuallyEq.mp hnt).deriv_eq]); obtain ⟨m, hm⟩ := (hc.union
    hc').bddBelow; let L := min a (m - 1); have hLa : L ≤ a := min_le_left _ _; have hLm : L < m :=
    (min_le_right _ _).trans_lt (sub_one_lt m); have hgL : g L = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hLm.not_ge (hm (Or.inl h)); have h_eq : ∫ t in Iio a,
    deriv g t = ∫ t in Ioc L a, deriv g t := (by
    rw [← integral_Iic_eq_integral_Iio, ← integral_Icc_eq_integral_Ioc]; refine
      setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Iic.nullMeasurableSet
      Icc_subset_Iic_self (Eventually.of_forall fun t ⟨ht_le, ht_not⟩ ↦ ?_); have htL : t < L :=
      not_le.1 fun h ↦ ht_not ⟨h, ht_le⟩; exact image_eq_zero_of_notMem_tsupport fun h ↦ (htL.trans
      hLm).not_ge (hm (Or.inr h))); rw [h_eq, ← intervalIntegral.integral_of_le hLa,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ (hg.differentiable one_ne_zero
        t).hasDerivAt) ((hg.continuous_deriv le_rfl).intervalIntegrable L a), hgL, sub_zero]
omit [MeasurableSpace E] [BorelSpace E] in theorem continuous_divergence {ψ : E → E} (hψ : ContDiff
    ℝ 1 ψ) : Continuous (divergence ψ) := (((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM
    ℝ)).continuous_of_finiteDimensional).comp (hψ.continuous_fderiv one_ne_zero)
theorem integral_divergence_eq_zero {ψ : E → E} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) : ∫
    x : E, divergence ψ x = 0 := by
  let b := stdOrthonormalBasis ℝ E; have hg (i : Fin (Module.finrank ℝ E)) := contDiff_const (c :=
    (b i : E)).inner ℝ hψ; have hcs (i : Fin (Module.finrank ℝ E)) : HasCompactSupport (fun z : E ↦
    ⟪b i, ψ z⟫_ℝ) := HasCompactSupport.of_support_subset_isCompact hc.isCompact fun z hz ↦
    subset_tsupport ψ fun h0 ↦ hz (by simp [h0]); have hdiv_eq : (fun x : E ↦ divergence ψ x) = fun
    x : E ↦ ∑ i, fderiv ℝ (fun z : E ↦ ⟪b i, ψ z⟫_ℝ) x (b i) := (by
    ext x; rw [divergence_eq_sum_orthonormalBasis b]; refine Finset.sum_congr rfl fun i _ ↦ ?_; erw
      [((innerSL ℝ (b i)).hasFDerivAt.comp x (hψ.differentiable one_ne_zero x).hasFDerivAt).fderiv];
      rfl); have hint_i (i : Fin (Module.finrank ℝ E)) : Integrable _ volume := (((hg
        i).continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := (b i :
        E)))).integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact (hcs
        i).isCompact fun x hx ↦ by_contra fun hnx ↦ hx
        (by simp [(notMem_tsupport_iff_eventuallyEq.mp hnx).fderiv_eq])); rw [hdiv_eq,
        integral_finsetSum _ fun i _ ↦ hint_i i]; exact Finset.sum_eq_zero fun i _ ↦
        integral_fderiv_eq_zero (hg i) (hcs i) _
omit [MeasurableSpace E] [BorelSpace E] in theorem trace_eq_sum_orthogonalHyperplane (he : ‖e‖ = 1)
    (A : E →L[ℝ] E) : LinearMap.trace ℝ E A.toLinearMap = (∑ i, ⟪((stdOrthonormalBasis ℝ (H⊥ e) i :
    H⊥ e) : E), A (stdOrthonormalBasis ℝ (H⊥ e) i)⟫_ℝ) + ⟪e, A e⟫_ℝ := by
  let H := H⊥ e; let b := stdOrthonormalBasis ℝ H; have hsplit : A = H.starProjection.comp A +
    ((innerSL ℝ e).comp A).smulRight e := (by
    ext z; change A z = H.starProjection (A z) + ⟪e, A z⟫_ℝ • e; rw
      [starProjection_orthogonalHyperplane_apply he, real_inner_comm e (A z), sub_add_cancel]); have
        htr1 : LinearMap.trace ℝ E (H.starProjection.comp A).toLinearMap = ∑ i, ⟪(b i : E), A (b
        i)⟫_ℝ := (by
    have hcomp : (H.starProjection.comp A).toLinearMap = H.subtypeL.toLinearMap.comp
      (H.orthogonalProjectionOnto.comp A).toLinearMap := rfl; rw [hcomp, LinearMap.trace_comp_comm',
      LinearMap.trace_eq_sum_inner _ b]; refine Finset.sum_congr rfl fun i _ ↦ (by simp [H]));
        (conv_lhs => rw [hsplit]); rw [ContinuousLinearMap.toLinearMap_add, map_add, htr1]; simp [H,
        b]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in theorem fderiv_inner_shear {ψ : E
    → E} {y : H⊥ e} (s : ℝ) (v : H⊥ e) (w : E) (hf : DifferentiableAt ℝ f y) (hψ : DifferentiableAt
    ℝ ψ ((y : E) + (s + f y) • e)) : fderiv ℝ (fun y' : H⊥ e ↦ ⟪w, ψ ((y' : E) + (s + f y') • e)⟫_ℝ)
    y v = ⟪w, fderiv ℝ ψ ((y : E) + (s + f y) • e) v⟫_ℝ + fderiv ℝ f y v * ⟪w, fderiv ℝ ψ ((y : E) +
    (s + f y) • e) e⟫_ℝ := by
  let H := H⊥ e; erw [((innerSL ℝ w).hasFDerivAt.comp y (hψ.hasFDerivAt.comp y
    (H.subtypeL.hasFDerivAt.add ((hf.hasFDerivAt.const_add s).smul_const e)))).fderiv]; change ⟪w,
    (fderiv ℝ ψ ((y : E) + (s + f y) • e)) ((v : E) + (fderiv ℝ f y v) • e)⟫_ℝ = _; rw [map_add,
    map_smul, inner_add_right, inner_smul_right]
omit [MeasurableSpace E] [BorelSpace E] in theorem divergence_shear_eq (he : ‖e‖ = 1) {ψ : E → E} {y
    : H⊥ e} (s : ℝ) (hf : DifferentiableAt ℝ f y) (hψ : DifferentiableAt ℝ ψ ((y : E) + (s + f y) •
    e)) : divergence ψ ((y : E) + (s + f y) • e) = (∑ i, fderiv ℝ (fun y' : H⊥ e ↦
    ⟪((stdOrthonormalBasis ℝ (H⊥ e) i : H⊥ e) : E), ψ ((y' : E) + (s + f y') • e)⟫_ℝ) y
    (stdOrthonormalBasis ℝ (H⊥ e) i)) + deriv (fun s' : ℝ ↦ ⟪ψ ((y : E) + (s' + f y) • e), ν_G e f
    y⟫_ℝ) s := by
  let H := H⊥ e; let b := stdOrthonormalBasis ℝ H; let x : E := (y : E) + (s + f y) • e; have
    hsum_grad : (∑ i, fderiv ℝ f y (b i) * ⟪(b i : E), fderiv ℝ ψ x e⟫_ℝ) =
    ⟪H.orthogonalProjectionOnto (fderiv ℝ ψ x e), gradient f y⟫_ℝ := (by
    have h1 : ∀ i, fderiv ℝ f y (b i) = ⟪gradient f y, b i⟫_ℝ := fun _ ↦
      (InnerProductSpace.toDual_symm_apply).symm; have h2 (i : Fin (Module.finrank ℝ H)) : ⟪(b i :
      E), fderiv ℝ ψ x e⟫_ℝ = ⟪b i, H.orthogonalProjectionOnto (fderiv ℝ ψ x e)⟫_ℝ :=
      (by simp [H, real_inner_comm]); simp_rw [h1, h2]; exact (b.sum_inner_mul_inner (gradient f y)
      (H.orthogonalProjectionOnto (fderiv ℝ ψ x e))).trans (real_inner_comm _ _)); have hline :
        HasDerivAt (fun s' : ℝ ↦ (y : E) + (s' + f y) • e) e s :=
        (by simpa using (((hasDerivAt_id s).add_const (f y)).smul_const e).const_add (y : E)); have
        hterm2 : deriv (fun s' : ℝ ↦ ⟪ψ ((y : E) + (s' + f y) • e), ν_G e f y⟫_ℝ) s =
        -⟪H.orthogonalProjectionOnto (fderiv ℝ ψ x e), gradient f y⟫_ℝ + ⟪e, fderiv ℝ ψ x e⟫_ℝ :=
        (by
    erw [((hψ.hasFDerivAt.comp_hasDerivAt s hline).inner ℝ (hasDerivAt_const s (ν_G e f y))).deriv];
      rw [inner_zero_right, zero_add, inner_graphNormalVec he, real_inner_comm (fderiv ℝ ψ x e) e]);
        rw [divergence, trace_eq_sum_orthogonalHyperplane he (fderiv ℝ ψ x), Finset.sum_congr rfl
        fun i _ ↦ fderiv_inner_shear s (b i) (b i) hf hψ, Finset.sum_add_distrib, hsum_grad,
        hterm2]; ring
theorem integral_subgraphOn_divergence_of_contDiff (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) {ψ : E → E}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) : ∫ x in sub_G e f, divergence ψ x = ∫ y, ⟪ψ
    (pt_G e f y), ν_G e f y⟫_ℝ := by
  let H := H⊥ e; let b := stdOrthonormalBasis ℝ H; have hdiv_cont := continuous_divergence hψ; have
    hdiv_supp := hasCompactSupport_divergence hc
  let Φ : H × ℝ ≃ₜ E := Homeomorph.trans ⟨⟨fun p ↦ (p.1, p.2 + f p.1), fun p ↦ (p.1, p.2 - f p.1),
    fun ⟨_, _⟩ ↦ by simp, fun ⟨_, _⟩ ↦ by simp⟩, continuous_fst.prodMk (continuous_snd.add
    (hf.continuous.comp continuous_fst)), continuous_fst.prodMk (continuous_snd.sub
    (hf.continuous.comp continuous_fst))⟩ ((WithLp.prodContinuousLinearEquiv 2 ℝ H
    ℝ).symm.toHomeomorph.trans (orthogonalHyperplaneProdEquiv he).toHomeomorph)
  rw [setIntegral_subgraphOn_eq he hf.continuous.measurable
    (hdiv_cont.integrable_of_hasCompactSupport hdiv_supp)]; have hfiber (y : H) : ∫ t in Iio (f y),
    divergence ψ ((y : E) + t • e) = ∫ s in Iio (0 : ℝ), divergence ψ ((y : E) + (s + f y) • e) :=
    (by
    have hpre : (fun s : ℝ ↦ s + f y) ⁻¹' Iio (f y) = Iio (0 : ℝ) := Set.ext fun _ ↦ (by simp); rw
      [← (measurePreserving_add_right volume (f y)).setIntegral_preimage_emb (Homeomorph.addRight (f
      y)).measurableEmbedding (fun t : ℝ ↦ divergence ψ ((y : E) + t • e)) (Iio (f y)), hpre]);
        simp_rw [hfiber]; let T (i : Fin (Module.finrank ℝ H)) (p : H × ℝ) : ℝ := fderiv ℝ (fun y' :
        H ↦ ⟪(b i : E), ψ ((y' : E) + (p.2 + f y') • e)⟫_ℝ) p.1 (b i); let N (p : H × ℝ) : ℝ :=
        deriv (fun s' : ℝ ↦ ⟪ψ ((p.1 : E) + (s' + f p.1) • e), ν_G e f p.1⟫_ℝ) p.2; have hT_eq (i :
        Fin (Module.finrank ℝ H)) : T i = fun p : H × ℝ ↦ ⟪(b i : E), fderiv ℝ ψ (Φ p) (b i)⟫_ℝ +
        fderiv ℝ f p.1 (b i) * ⟪(b i : E), fderiv ℝ ψ (Φ p) e⟫_ℝ := funext fun ⟨y, s⟩ ↦
        fderiv_inner_shear s (b i) (b i) (hf.differentiable one_ne_zero y) (hψ.differentiable
        one_ne_zero (Φ (y, s))); have hT_cont (i : Fin (Module.finrank ℝ H)) : Continuous (T i) :=
        (by
    rw [hT_eq i]; have hf' : Continuous fun p : H × ℝ ↦ fderiv ℝ f p.1 (b i) :=
      ((hf.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_const; have hψ'
      (v : E) := ((hψ.continuous_fderiv one_ne_zero).comp Φ.continuous).clm_apply (continuous_const
      (y := v)); exact ((continuous_const (y := (b i : E))).inner (hψ' (b i))).add (hf'.mul
      ((continuous_const (y := (b i : E))).inner (hψ' e)))); have hT_supp (i : Fin (Module.finrank ℝ
        H)) : HasCompactSupport (T i) := HasCompactSupport.of_support_subset_isCompact
        (hc.isCompact.image Φ.symm.continuous) fun p hp ↦ ⟨Φ p, by_contra fun hnp ↦ hp
        (by simp [hT_eq, (notMem_tsupport_iff_eventuallyEq.mp hnp).fderiv_eq]), Φ.symm_apply_apply
        p⟩; have hT_int (i : Fin (Module.finrank ℝ H)) : Integrable (T i) (volume.prod
        (volume.restrict (Iio (0 : ℝ)))) := ((hT_cont i).integrable_of_hasCompactSupport (hT_supp
        i)).mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self); have hdiv_int :
        Integrable _ (volume.prod (volume.restrict (Iio (0 : ℝ)))) := ((hdiv_cont.comp
        Φ.continuous).integrable_of_hasCompactSupport (hdiv_supp.comp_homeomorph Φ)).mono_measure
        (Measure.prod_mono le_rfl Measure.restrict_le_self); have hdecomp (p : H × ℝ) : divergence ψ
        (Φ p) = (∑ i, T i p) + N p := divergence_shear_eq he p.2 (hf.differentiable one_ne_zero p.1)
        (hψ.differentiable one_ne_zero (Φ p)); have hN_int : Integrable N (volume.prod
        (volume.restrict (Iio (0 : ℝ)))) := (hdiv_int.sub (integrable_finsetSum _ fun i _ ↦ hT_int
        i)).congr (Eventually.of_forall fun p ↦ by dsimp; linarith [hdecomp p]); have hprod_eq : (∫
        y : H, ∫ s in Iio (0 : ℝ), divergence ψ ((y : E) + (s + f y) • e)) = (∑ i, ∫ s in Iio (0 :
        ℝ), ∫ y : H, T i (y, s)) + ∫ y : H, ∫ s in Iio (0 : ℝ), N (y, s) := (by
    change (∫ y : H, ∫ s in Iio (0 : ℝ), divergence ψ (Φ (y, s))) = _; rw [← integral_prod (fun p :
      H × ℝ ↦ divergence ψ (Φ p)) hdiv_int]; simp_rw [hdecomp]; rw [integral_add
      (integrable_finsetSum _ fun i _ ↦ hT_int i) hN_int, integral_finsetSum _ fun i _ ↦ hT_int i,
      integral_prod N hN_int]
    exact congrArg (· + _) (Finset.sum_congr rfl fun i _ ↦ integral_prod_symm (T i) (hT_int i)));
      have hT_zero : (∑ i, ∫ s in Iio (0 : ℝ), ∫ y : H, T i (y, s)) = 0 := Finset.sum_eq_zero fun i
      _ ↦ integral_eq_zero_of_ae (Eventually.of_forall fun s ↦ integral_fderiv_eq_zero
      (contDiff_const.inner ℝ (hψ.comp (H.subtypeL.contDiff.add ((contDiff_const.add hf).smul
      contDiff_const)))) (hasCompactSupport_graphComp hc (fun y' ↦ s + f y') fun _ h0 ↦
      by simp [h0]) (b i)); rw [hprod_eq, hT_zero, zero_add]; refine integral_congr_ae
      (Eventually.of_forall fun y ↦ ?_); have hg_diff : ContDiff ℝ 1 (fun s' : ℝ ↦ ⟪ψ ((y : E) + (s'
      + f y) • e), ν_G e f y⟫_ℝ) := (hψ.comp (contDiff_const.add ((contDiff_id.add
      contDiff_const).smul contDiff_const))).inner ℝ contDiff_const; have hg_supp :
      HasCompactSupport (fun s' : ℝ ↦ ⟪ψ ((y : E) + (s' + f y) • e), ν_G e f y⟫_ℝ) :=
      HasCompactSupport.of_support_subset_isCompact (hc.isCompact.image ((continuous_id.inner
      (continuous_const (y := e))).sub (continuous_const (y := f y)))) fun s' hs' ↦ ⟨(y : E) + (s' +
      f y) • e, subset_tsupport ψ fun h0 ↦ hs' (by simp [h0]),
      (by simp [inner_coe_add_smul_self he])⟩; simpa [N, graphPoint] using integral_Iio_deriv
      hg_diff hg_supp 0
theorem integral_subgraphOn_divergence (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) {U : Opens E} (φ : 𝓓(U,
    E)) : ∫ x in sub_G e f, divergence (φ : E → E) x = ∫ y, ⟪φ (pt_G e f y), ν_G e f y⟫_ℝ :=
    integral_subgraphOn_divergence_of_contDiff he hf (φ.contDiff.of_le (by simp))
    φ.hasCompactSupport
theorem integral_subgraphOn_divergence_unitNormal (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) {U : Opens E}
    (φ : 𝓓(U, E)) : ∫ x in sub_G e f, divergence (φ : E → E) x = ∫ y, ⟪φ (pt_G e f y), n_G e f y⟫_ℝ
    * graphJacobian f y := by
  rw [integral_subgraphOn_divergence he hf φ]; refine integral_congr_ae (Eventually.of_forall fun y
    ↦ ?_); dsimp only; rw [graphNormalVec_eq_smul_graphUnitNormal, inner_smul_right, mul_comm]
theorem integral_epigraphOn_divergence_of_contDiff (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) {ψ : E → E}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) : ∫ x in epigraphOn e f, divergence ψ x = -∫ y,
    ⟪ψ (pt_G e f y), ν_G e f y⟫_ℝ := by
  have hsum := integral_add_compl (s := subLE_G e f) (measurableSet_subgraphLEOn e
    hf.continuous.measurable) ((continuous_divergence hψ).integrable_of_hasCompactSupport
    (hasCompactSupport_divergence hc) (μ := volume)); have hle : ∫ x in subLE_G e f, divergence ψ x
    = ∫ y, ⟪ψ (pt_G e f y), ν_G e f y⟫_ℝ := (by
    rw [← setIntegral_congr_set (subgraphOn_ae_eq_subgraphLEOn he hf.continuous.measurable),
      integral_subgraphOn_divergence_of_contDiff he hf hψ hc]); rw [compl_subgraphLEOn, hle,
        integral_divergence_eq_zero hψ hc] at hsum; linarith
theorem integral_epigraphOn_divergence (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) {U : Opens E} (φ : 𝓓(U,
    E)) : ∫ x in epigraphOn e f, divergence (φ : E → E) x = -∫ y, ⟪φ (pt_G e f y), ν_G e f y⟫_ℝ :=
    integral_epigraphOn_divergence_of_contDiff he hf (φ.contDiff.of_le (by simp))
    φ.hasCompactSupport
theorem relativePerimeter_subgraphOn_le_graphSurfaceArea (he : ‖e‖ = 1) (U : Opens E) (hf : ContDiff
    ℝ 1 f) : relativePerimeter volume U (sub_G e f) ≤ graphSurfaceArea volume f (graphSlice e f U)
    := by
  rw [relativePerimeter_eq_iSup_of_measurableSet (measurableSet_subgraphOn e
    hf.continuous.measurable)]; refine iSup₂_le fun φ hφ ↦ ?_; have hint_eq : ∫ x in sub_G e f ∩ (U
    : Set E), divergence (φ : E → E) x = ∫ y in graphSlice e f U, ⟪φ (pt_G e f y), ν_G e f y⟫_ℝ :=
    (by
    rw [← setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (measurableSet_subgraphOn e
      hf.continuous.measurable).nullMeasurableSet inter_subset_left (Eventually.of_forall fun x
      ⟨hx_lt, hxU⟩ ↦ divergence_testFunction_eq_zero_of_notMem φ (fun h ↦ hxU ⟨hx_lt, h⟩)),
      integral_subgraphOn_divergence he hf φ, setIntegral_eq_integral_of_forall_compl_eq_zero fun y
      hy ↦ by simp [φ.zero_on_compl hy]]); rw [hint_eq]; refine (ENNReal.ofReal_le_ofReal
        (le_abs_self _)).trans ?_; rw [← Real.enorm_eq_ofReal_abs]; refine
        (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y ↦ ?_); rw
        [Real.enorm_eq_ofReal_abs]; refine ENNReal.ofReal_le_ofReal ((abs_real_inner_le_norm _
        _).trans ?_); rw [norm_graphNormalVec he]; simpa using mul_le_mul_of_nonneg_right (hφ _)
        (graphJacobian_nonneg f y)
theorem relativePerimeter_subgraphLEOn_le_graphSurfaceArea (he : ‖e‖ = 1) (U : Opens E) (hf :
    ContDiff ℝ 1 f) : relativePerimeter volume U (subLE_G e f) ≤ graphSurfaceArea volume f
    (graphSlice e f U) := by
  rw [← relativePerimeter_congr_ae (ae_restrict_of_ae (subgraphOn_ae_eq_subgraphLEOn he
    hf.continuous.measurable))]; exact relativePerimeter_subgraphOn_le_graphSurfaceArea he U hf
theorem relativePerimeter_epigraphOn_le_graphSurfaceArea (he : ‖e‖ = 1) (U : Opens E) (hf : ContDiff
    ℝ 1 f) : relativePerimeter volume U (epigraphOn e f) ≤ graphSurfaceArea volume f (graphSlice e f
    U) := by
  simpa [← compl_subgraphLEOn] using relativePerimeter_subgraphLEOn_le_graphSurfaceArea he U hf
variable {u u₁ u₂ : E → ℝ} {U : Opens E}
omit [MeasurableSpace E] [BorelSpace E] in theorem divergence_smul_eq_add_inner_gradient {Φ : E → E}
    {x : E} (hu : DifferentiableAt ℝ u x) (hΦ : DifferentiableAt ℝ Φ x) : divergence (fun z ↦ u z •
    Φ z) x = u x * divergence Φ x + ⟪gradient u x, Φ x⟫_ℝ :=
    (by rw [divergence_smul hu hΦ, ← InnerProductSpace.toDual_symm_apply]; rfl)
theorem integrable_inner_gradient (hu : ContDiff ℝ 1 u) (Φ : 𝓓(U, E)) : Integrable (fun x ↦
    ⟪gradient u x, Φ x⟫_ℝ) volume := by
  have hgrad : Continuous (gradient u) := (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (hu.continuous_fderiv one_ne_zero); exact (hgrad.inner
    Φ.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact
    Φ.hasCompactSupport.isCompact fun x hx ↦ subset_tsupport Φ fun h0 ↦ hx (by simp [h0]))
theorem integral_mul_divergence_add {s : Set E} (hu : ContDiff ℝ 1 u) (Φ : 𝓓(U, E)) : (∫ x in s, u x
    * divergence (Φ : E → E) x) + ∫ x in s, ⟪gradient u x, Φ x⟫_ℝ = ∫ x in s, divergence (u • (Φ : E
    → E)) x := by
  have h1 : Integrable (fun x ↦ u x * divergence (Φ : E → E) x) volume := (hu.continuous.mul
    (continuous_divergence_testFunction Φ)).integrable_of_hasCompactSupport
    ((hasCompactSupport_divergence_testFunction Φ).smul_left (f := u)); have hdiv : divergence (u •
    (Φ : E → E)) = fun x ↦ u x * divergence (Φ : E → E) x + ⟪gradient u x, Φ x⟫_ℝ := funext fun x ↦
    divergence_smul_eq_add_inner_gradient (hu.differentiable one_ne_zero x)
    (Φ.contDiff.differentiable (by simp) x); rw [hdiv, integral_add h1.integrableOn
    (integrable_inner_gradient hu Φ).integrableOn]
theorem setIntegral_inter_inner_gradient {s : Set E} (hs : MeasurableSet s) (u : E → ℝ) (Φ : 𝓓(U,
    E)) : ∫ x in (U : Set E) ∩ s, ⟪gradient u x, Φ x⟫_ℝ = ∫ x in s, ⟪gradient u x, Φ x⟫_ℝ :=
    (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs.nullMeasurableSet inter_subset_right
    (Eventually.of_forall fun x ⟨hxs, hxU⟩ ↦ by simp [Φ.zero_on_compl (fun h ↦ hxU ⟨h, hxs⟩)])).symm
theorem ofReal_abs_integral_gradient_le {s : Set E} (u : E → ℝ) (Φ : 𝓓(U, E)) (hΦ : ∀ x, ‖Φ x‖ ≤ 1)
    : ENNReal.ofReal |∫ x in s, ⟪gradient u x, Φ x⟫_ℝ| ≤ ∫⁻ x in s, ‖gradient u x‖ₑ := by
  rw [← Real.enorm_eq_ofReal_abs]; refine (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_mono fun x ↦ ?_); rw [enorm_le_iff_norm_le, Real.norm_eq_abs]; exact
    (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hΦ x))
variable (U) in theorem ofReal_abs_integral_slice_le (he : ‖e‖ = 1) (a : ℝ) (w : E → ℝ) (Φ : 𝓓(U,
    E)) (hΦ : ∀ x, ‖Φ x‖ ≤ 1) : ENNReal.ofReal |∫ y in slice⊥ e a U, w (pt⊥ e a y) * ⟪Φ (pt⊥ e a y),
    e⟫_ℝ| ≤ ∫⁻ y in slice⊥ e a U, ‖w (pt⊥ e a y)‖ₑ := by
  rw [← Real.enorm_eq_ofReal_abs]; refine (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_mono fun y ↦ ?_); rw [enorm_mul]; refine mul_le_of_le_one_right (by positivity) ?_;
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]; exact (abs_real_inner_le_norm _ _).trans
    (by rw [he, mul_one]; exact hΦ _)
theorem integral_subgraphOn_mul_divergence_eq (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) (hu : ContDiff ℝ
    1 u) (Φ : 𝓓(U, E)) : ∫ x in sub_G e f, u x * divergence (Φ : E → E) x = -(∫ x in sub_G e f,
    ⟪gradient u x, Φ x⟫_ℝ) + ∫ y, u (pt_G e f y) * ⟪Φ (pt_G e f y), ν_G e f y⟫_ℝ := by
  have hgg := integral_subgraphOn_divergence_of_contDiff he hf (hu.smul (Φ.contDiff.of_le
    (by simp))) (Φ.hasCompactSupport.smul_left (f := u)); simp_rw [show ∀ z, (u • (Φ : E → E)) z = u
    z • Φ z from fun _ ↦ rfl, inner_smul_left, RCLike.conj_to_real] at hgg; linarith
    [integral_mul_divergence_add (s := sub_G e f) hu Φ, hgg]
theorem integral_epigraphOn_mul_divergence_eq (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) (hu : ContDiff ℝ
    1 u) (Φ : 𝓓(U, E)) : ∫ x in epigraphOn e f, u x * divergence (Φ : E → E) x = -(∫ x in epigraphOn
    e f, ⟪gradient u x, Φ x⟫_ℝ) - ∫ y, u (pt_G e f y) * ⟪Φ (pt_G e f y), ν_G e f y⟫_ℝ := by
  have hgg := integral_epigraphOn_divergence_of_contDiff he hf (hu.smul (Φ.contDiff.of_le
    (by simp))) (Φ.hasCompactSupport.smul_left (f := u)); simp_rw [show ∀ z, (u • (Φ : E → E)) z = u
    z • Φ z from fun _ ↦ rfl, inner_smul_left, RCLike.conj_to_real] at hgg; linarith
    [integral_mul_divergence_add (s := epigraphOn e f) hu Φ, hgg]
theorem integral_halfSpaceLT_mul_divergence_eq (he : ‖e‖ = 1) (a : ℝ) (hu : ContDiff ℝ 1 u) (Φ :
    𝓓(U, E)) : ∫ x in hsLT e a, u x * divergence (Φ : E → E) x = -(∫ x in hsLT e a, ⟪gradient u x, Φ
    x⟫_ℝ) + ∫ y, u (pt⊥ e a y) * ⟪Φ (pt⊥ e a y), e⟫_ℝ :=
    (by simpa using integral_subgraphOn_mul_divergence_eq he (f := fun _ ↦ a) contDiff_const hu Φ)
theorem integral_halfSpaceGT_mul_divergence_eq (he : ‖e‖ = 1) (a : ℝ) (hu : ContDiff ℝ 1 u) (Φ :
    𝓓(U, E)) : ∫ x in hsGT e a, u x * divergence (Φ : E → E) x = -(∫ x in hsGT e a, ⟪gradient u x, Φ
    x⟫_ℝ) - ∫ y, u (pt⊥ e a y) * ⟪Φ (pt⊥ e a y), e⟫_ℝ :=
    (by simpa using integral_epigraphOn_mul_divergence_eq he (f := fun _ ↦ a) contDiff_const hu Φ)
theorem integral_indicator_halfSpaceLT_mul_divergence_eq (he : ‖e‖ = 1) (a : ℝ) (hu : ContDiff ℝ 1
    u) (Φ : 𝓓(U, E)) : ∫ x in (U : Set E), (hsLT e a).indicator u x * divergence (Φ : E → E) x = -(∫
    x in (U : Set E) ∩ hsLT e a, ⟪gradient u x, Φ x⟫_ℝ) + ∫ y in slice⊥ e a U, u (pt⊥ e a y) * ⟪Φ
    (pt⊥ e a y), e⟫_ℝ := by
  rw [setIntegral_mul_divergence_eq_integral, indicator_mul_eq, integral_indicator
    (measurableSet_halfSpaceLT e a), integral_halfSpaceLT_mul_divergence_eq he a hu Φ,
    setIntegral_inter_inner_gradient (measurableSet_halfSpaceLT e a) u Φ,
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := slice⊥ e a U) fun y hy ↦
    by simp [Φ.zero_on_compl hy]]
theorem integral_indicator_halfSpaceGT_mul_divergence_eq (he : ‖e‖ = 1) (a : ℝ) (hu : ContDiff ℝ 1
    u) (Φ : 𝓓(U, E)) : ∫ x in (U : Set E), (hsGT e a).indicator u x * divergence (Φ : E → E) x = -(∫
    x in (U : Set E) ∩ hsGT e a, ⟪gradient u x, Φ x⟫_ℝ) - ∫ y in slice⊥ e a U, u (pt⊥ e a y) * ⟪Φ
    (pt⊥ e a y), e⟫_ℝ := by
  rw [setIntegral_mul_divergence_eq_integral, indicator_mul_eq, integral_indicator
    (isOpen_halfSpaceGT e a).measurableSet, integral_halfSpaceGT_mul_divergence_eq he a hu Φ,
    setIntegral_inter_inner_gradient (isOpen_halfSpaceGT e a).measurableSet u Φ,
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := slice⊥ e a U) fun y hy ↦
    by simp [Φ.zero_on_compl hy]]
variable (U) in theorem distributionalVariation_indicator_halfSpaceLT_mul_le (he : ‖e‖ = 1) (a : ℝ)
    (hu : ContDiff ℝ 1 u) : distributionalVariation volume U ((hsLT e a).indicator u) ≤ (∫⁻ x in (U
    : Set E) ∩ hsLT e a, ‖gradient u x‖ₑ) + ∫⁻ y in slice⊥ e a U, ‖u (pt⊥ e a y)‖ₑ := by
  refine iSup₂_le fun Φ hΦ ↦ ?_; rw [integral_indicator_halfSpaceLT_mul_divergence_eq he a hu Φ];
    set I₁ := ∫ x in (U : Set E) ∩ hsLT e a, ⟪gradient u x, Φ x⟫_ℝ; set I₂ := ∫ y in slice⊥ e a U, u
    (pt⊥ e a y) * ⟪Φ (pt⊥ e a y), e⟫_ℝ; refine (ENNReal.ofReal_le_ofReal (show -I₁ + I₂ ≤ |I₁| +
    |I₂| by linarith [neg_abs_le I₁, le_abs_self I₂])).trans ?_; rw [ENNReal.ofReal_add (abs_nonneg
    I₁) (abs_nonneg I₂)]; exact add_le_add (ofReal_abs_integral_gradient_le u Φ hΦ)
    (ofReal_abs_integral_slice_le U he a u Φ hΦ)
variable (U) in theorem enorm_integral_trace_mul_le_distributionalVariation_add_lintegral_gradient
    (he : ‖e‖ = 1) (a : ℝ) (hu : ContDiff ℝ 1 u) (ψ : 𝓓(U, ℝ)) (hψ : ∀ x, ‖ψ x‖ ≤ 1) : ‖∫ y in
    slice⊥ e a U, u (pt⊥ e a y) * ψ (pt⊥ e a y)‖ₑ ≤ distributionalVariation volume U ((hsLT e
    a).indicator u) + ∫⁻ x in (U : Set E) ∩ hsLT e a, ‖gradient u x‖ₑ := by
  let Φ : 𝓓(U, E) := constSmulTestFunction ψ e; have hΦ_norm : ∀ x, ‖Φ x‖ ≤ 1 := fun x ↦
    (by rw [constSmulTestFunction_apply, norm_smul, he, mul_one]; exact hψ x); set I_var := ∫ x in
    (U : Set E), (hsLT e a).indicator u x * divergence (Φ : E → E) x; set I_grad := ∫ x in (U : Set
    E) ∩ hsLT e a, ⟪gradient u x, Φ x⟫_ℝ; have hpair :=
    integral_indicator_halfSpaceLT_mul_divergence_eq he a hu Φ; change I_var = -I_grad + _ at hpair;
    simp_rw [Φ, constSmulTestFunction_apply, inner_smul_left, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq, he, one_pow, mul_one] at hpair; have hle : |∫ y in slice⊥ e a U, u
    (pt⊥ e a y) * ψ (pt⊥ e a y)| ≤ |I_var| + |I_grad| := (by
    rw [show (∫ y in slice⊥ e a U, u (pt⊥ e a y) * ψ (pt⊥ e a y)) = I_var + I_grad
      by linarith [hpair]]; exact abs_add_le _ _); rw [Real.enorm_eq_ofReal_abs]; refine
        (ENNReal.ofReal_le_ofReal hle).trans ?_; rw [ENNReal.ofReal_add (abs_nonneg I_var)
        (abs_nonneg I_grad)]; exact add_le_add (abs_le_distributionalVariation Φ hΦ_norm _)
        (ofReal_abs_integral_gradient_le u Φ hΦ_norm)
variable (U) in theorem setLIntegral_trace_compact_le_distributionalVariation_add_lintegral_gradient
    (he : ‖e‖ = 1) (a : ℝ) (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u (pt⊥ e a y)) {K : Set (H⊥ e)}
    (hK_sub : K ⊆ slice⊥ e a U) (hK : IsCompact K) : ∫⁻ y in K, ‖u (pt⊥ e a y)‖ₑ ≤
    distributionalVariation volume U ((hsLT e a).indicator u) + ∫⁻ x in (U : Set E) ∩ hsLT e a,
    ‖gradient u x‖ₑ := by
  rcases exists_testFunction_eq_one_on_graphPoint e U (f := fun _ ↦ a) continuous_const hK_sub hK
    with ⟨ψ, hψ_nonneg, hψ_norm, hψ_one⟩; have hint_bdry : IntegrableOn (fun y ↦ u (pt⊥ e a y) * ψ
    (pt⊥ e a y)) (slice⊥ e a U) volume := ((hu.continuous.comp (continuous_hyperplanePoint e a)).mul
    (ψ.continuous.comp (continuous_hyperplanePoint e a))).integrable_of_hasCompactSupport
    (hasCompactSupport_graphComp ψ.hasCompactSupport (fun _ ↦ a) fun _ h0 ↦
    by simp [hyperplanePoint, h0]) |>.integrableOn (s := slice⊥ e a U); have hint_K : IntegrableOn
    (fun y ↦ u (pt⊥ e a y)) K volume := (hu.continuous.comp (continuous_hyperplanePoint e
    a)).continuousOn.integrableOn_compact hK; have hK_le : ∫ y in K, u (pt⊥ e a y) ≤ ∫ y in slice⊥ e
    a U, u (pt⊥ e a y) * ψ (pt⊥ e a y) := (by
    rw [setIntegral_congr_fun (g := fun y ↦ u (pt⊥ e a y) * ψ (pt⊥ e a y)) hK.isClosed.measurableSet
      fun y hy ↦ by simp [show ψ (pt⊥ e a y) = 1 from hψ_one y hy]]; exact setIntegral_mono_set
      hint_bdry (Eventually.of_forall fun y ↦ mul_nonneg (hu0 y) (hψ_nonneg _))
        hK_sub.eventuallyLE); have hlint_K : (∫⁻ y in K, ‖u (pt⊥ e a y)‖ₑ) = ENNReal.ofReal (∫ y in
        K, u (pt⊥ e a y)) := (by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint_K]; exact congrArg ENNReal.ofReal
      (setIntegral_congr_fun hK.isClosed.measurableSet fun y _ ↦ Real.norm_of_nonneg (hu0 y))); rw
        [hlint_K]; refine (ENNReal.ofReal_le_ofReal (hK_le.trans (le_abs_self _))).trans ?_; rw [←
        Real.enorm_eq_ofReal_abs]; exact
        enorm_integral_trace_mul_le_distributionalVariation_add_lintegral_gradient U he a hu ψ
        hψ_norm
theorem piecewise_halfSpaceLT_ae_eq_add_indicator (he : e ≠ 0) (a : ℝ) [DecidablePred (· ∈ hsLT e
    a)] (u₁ u₂ : E → ℝ) : (hsLT e a).piecewise u₁ u₂ =ᵐ[volume] fun x ↦ (hsLT e a).indicator u₁ x +
    (hsGT e a).indicator u₂ x := by
  filter_upwards [compl_mem_ae_iff.mpr (volume_hyperplane he a)] with x hx; rcases lt_trichotomy ⟪x,
    e⟫_ℝ a with hlt | heq | hgt
  · simp [mem_halfSpaceLT.mpr hlt, show x ∉ hsGT e a from not_lt.mpr hlt.le]
  · exact False.elim (hx heq)
  · simp [show x ∉ hsLT e a from not_lt.mpr hgt.le, mem_halfSpaceGT.mpr hgt]
theorem integral_piecewise_halfSpaceLT_mul_divergence_eq (he : ‖e‖ = 1) (a : ℝ) [DecidablePred (· ∈
    hsLT e a)] (hu₁ : ContDiff ℝ 1 u₁) (hu₂ : ContDiff ℝ 1 u₂) (Φ : 𝓓(U, E)) : ∫ x in (U : Set E),
    (hsLT e a).piecewise u₁ u₂ x * divergence (Φ : E → E) x = -(∫ x in (U : Set E) ∩ hsLT e a,
    ⟪gradient u₁ x, Φ x⟫_ℝ) - (∫ x in (U : Set E) ∩ hsGT e a, ⟪gradient u₂ x, Φ x⟫_ℝ) + ∫ y in
    slice⊥ e a U, (u₁ (pt⊥ e a y) - u₂ (pt⊥ e a y)) * ⟪Φ (pt⊥ e a y), e⟫_ℝ := by
  have he0 : e ≠ 0 := (by intro h; simp [h] at he); have hae : (fun x ↦ (hsLT e a).piecewise u₁ u₂ x
    * divergence (Φ : E → E) x) =ᵐ[volume] fun x ↦ (hsLT e a).indicator u₁ x * divergence (Φ : E →
    E) x + (hsGT e a).indicator u₂ x * divergence (Φ : E → E) x := (by
    filter_upwards [piecewise_halfSpaceLT_ae_eq_add_indicator he0 a u₁ u₂] with x hx; rw [hx,
      add_mul]); have hint (w : E → ℝ) (hw : ContDiff ℝ 1 w) (s : Set E) (hs : MeasurableSet s) :
        IntegrableOn (fun x ↦ s.indicator w x * divergence (Φ : E → E) x) (U : Set E) volume := (by
    rw [indicator_mul_eq]; exact ((hw.continuous.mul (continuous_divergence_testFunction
      Φ)).integrable_of_hasCompactSupport ((hasCompactSupport_divergence_testFunction Φ).smul_left
      (f := w))).indicator hs |>.integrableOn); rw [setIntegral_congr_ae U.isOpen.measurableSet
        (hae.mono fun _ hx _ ↦ hx), integral_add (hint u₁ hu₁ _ (measurableSet_halfSpaceLT e a))
        (hint u₂ hu₂ _ (isOpen_halfSpaceGT e a).measurableSet),
        integral_indicator_halfSpaceLT_mul_divergence_eq he a hu₁ Φ,
        integral_indicator_halfSpaceGT_mul_divergence_eq he a hu₂ Φ]; have hbdry_int (w : E → ℝ) (hw
        : ContDiff ℝ 1 w) : IntegrableOn (fun y ↦ w (pt⊥ e a y) * ⟪Φ (pt⊥ e a y), e⟫_ℝ) (slice⊥ e a
        U) volume := ((hw.continuous.comp (continuous_hyperplanePoint e a)).mul ((Φ.continuous.comp
        (continuous_hyperplanePoint e a)).inner (continuous_const (y :=
        e)))).integrable_of_hasCompactSupport (hasCompactSupport_graphComp Φ.hasCompactSupport (fun
        _ ↦ a) fun _ h0 ↦ by simp [hyperplanePoint, h0]) |>.integrableOn (s := slice⊥ e a U); have
        hsub_bdry := integral_sub (hbdry_int u₁ hu₁) (hbdry_int u₂ hu₂); simp_rw [←
        sub_mul] at hsub_bdry; linarith [hsub_bdry]
variable (U) in theorem distributionalVariation_piecewise_halfSpaceLT_le (he : ‖e‖ = 1) (a : ℝ)
    [DecidablePred (· ∈ hsLT e a)] (hu₁ : ContDiff ℝ 1 u₁) (hu₂ : ContDiff ℝ 1 u₂) :
    distributionalVariation volume U ((hsLT e a).piecewise u₁ u₂) ≤ (∫⁻ x in (U : Set E) ∩ hsLT e a,
    ‖gradient u₁ x‖ₑ) + (∫⁻ x in (U : Set E) ∩ hsGT e a, ‖gradient u₂ x‖ₑ) + ∫⁻ y in slice⊥ e a U,
    ‖u₁ (pt⊥ e a y) - u₂ (pt⊥ e a y)‖ₑ := by
  refine iSup₂_le fun Φ hΦ ↦ ?_; rw [integral_piecewise_halfSpaceLT_mul_divergence_eq he a hu₁ hu₂
    Φ]; set I₁ := ∫ x in (U : Set E) ∩ hsLT e a, ⟪gradient u₁ x, Φ x⟫_ℝ; set I₂ := ∫ x in (U : Set
    E) ∩ hsGT e a, ⟪gradient u₂ x, Φ x⟫_ℝ; set I₃ := ∫ y in slice⊥ e a U, (u₁ (pt⊥ e a y) - u₂ (pt⊥
    e a y)) * ⟪Φ (pt⊥ e a y), e⟫_ℝ; refine (ENNReal.ofReal_le_ofReal (show -I₁ - I₂ + I₃ ≤ |I₁| +
    |I₂| + |I₃| by linarith [neg_abs_le I₁, neg_abs_le I₂, le_abs_self I₃])).trans ?_; rw
    [ENNReal.ofReal_add (add_nonneg (abs_nonneg I₁) (abs_nonneg I₂)) (abs_nonneg I₃),
    ENNReal.ofReal_add (abs_nonneg I₁) (abs_nonneg I₂)]; exact add_le_add (add_le_add
    (ofReal_abs_integral_gradient_le u₁ Φ hΦ) (ofReal_abs_integral_gradient_le u₂ Φ hΦ))
    (ofReal_abs_integral_slice_le U he a (fun x ↦ u₁ x - u₂ x) Φ hΦ)
variable (U) in theorem distributionalVariation_piecewise_halfSpaceLT_le_of_eq_on_hyperplane (he :
    ‖e‖ = 1) (a : ℝ) [DecidablePred (· ∈ hsLT e a)] (hu₁ : ContDiff ℝ 1 u₁) (hu₂ : ContDiff ℝ 1 u₂)
    (heq : ∀ y ∈ slice⊥ e a U, u₁ (pt⊥ e a y) = u₂ (pt⊥ e a y)) : distributionalVariation volume U
    ((hsLT e a).piecewise u₁ u₂) ≤ (∫⁻ x in (U : Set E) ∩ hsLT e a, ‖gradient u₁ x‖ₑ) + ∫⁻ x in (U :
    Set E) ∩ hsGT e a, ‖gradient u₂ x‖ₑ := by
  have h0 : (∫⁻ y in slice⊥ e a U, ‖u₁ (pt⊥ e a y) - u₂ (pt⊥ e a y)‖ₑ) = 0 := (by
    rw [setLIntegral_congr_fun (g := fun _ ↦ 0) (isOpen_hyperplaneSlice e a U.isOpen).measurableSet
      fun y hy ↦ by simp [heq y hy], lintegral_zero]); simpa [h0] using
        distributionalVariation_piecewise_halfSpaceLT_le U he a hu₁ hu₂
end TauCeti
