/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
import all TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
import all TauCeti.MeasureTheory.Measure.HalfSpacePerimeter
import all TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski
import all TauCeti.MeasureTheory.Measure.Lebesgue.PrekopaLeindler
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
import all TauCeti.MeasureTheory.Measure.MinkowskiContent

/-!
# Degenerate Parallel-Volume Derivatives, Difference-Body Isodiametry, and Ball Rigidity

This file completes Milestone I2 (`Isoperimetry/README.md` lines 170–181):
1. **Lower-dimensional compact sets in hyperplanes and higher-codimension subspaces**:
   `volume K = 0`, `perimeter volume K = 0`, outer-parallel right derivative `2 * H^{n-1}(K)` at
   `r = 0` (`> H^{n-1}(K) > perimeter volume K = 0` in codimension `1`, and `= 0` in codimension
   `≥ 2`).
2. **Closed convex hull `closedConvexHull` and difference body `differenceBody` isodiametry**:
   diameter preservation, `differenceBody s ⊆ Metric.closedBall 0 (Metric.diam s / 2)`, and the
   Brunn–Minkowski volume chain `volume s ≤ volume (closedConvexHull s) ≤ volume (differenceBody s)
   ≤ volume (Metric.closedBall 0 (Metric.diam s / 2))`.
3. **Isodiametric ball rigidity, closed convex body equality, and converse with diameter bound**:
   `s =ᵐ[volume] closedConvexHull s`, `differenceBody s = Metric.closedBall 0 (Metric.diam s / 2)`,
   exact/a.e. ball rigidity under `-K = {a} + K` (unconditional on `ℝ`), and the converse under
   `Metric.diam s ≤ 2 * r` together with the single-point null-modification counterexample.
-/

public section
noncomputable section
open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set Submodule
open scoped ENNReal NNReal InnerProductSpace Topology
open TauCeti.MeasureTheory

namespace TauCeti

/-! ### Section 1: Lower-dimensional compact sets in hyperplanes & higher-codimension subspaces -/
section LowerDimensionalParallelVolume
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-- Linear isometry equivalences commute with `outerParallel`. -/
theorem outerParallel_image_linearIsometryEquiv (L : F ≃ₗᵢ[ℝ] E) (s : Set F) (r : ℝ) :
    outerParallel (L '' s) r = L '' outerParallel s r := by
  ext y; simp only [outerParallel, Set.mem_add, Set.mem_smul_set, Metric.mem_closedBall,
    dist_zero_right, Set.mem_image]; constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨x + r • L.symm z, ⟨x, hx, r • L.symm z, ⟨L.symm z, ?_, rfl⟩, rfl⟩, ?_⟩
    · simpa [L.symm.norm_map] using hz
    · simp [map_add, map_smul]
  · rintro ⟨w, ⟨x, hx, _, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    refine ⟨L x, ⟨x, hx, rfl⟩, r • L z, ⟨L z, ?_, rfl⟩, by simp [map_add, map_smul]⟩
    simpa [L.norm_map] using hz
/-- Translations `(c + ·) '' s = {c} + s` commute with `outerParallel`. -/
theorem outerParallel_singleton_add (c : E) (s : Set E) (r : ℝ) :
    outerParallel ({c} + s) r = {c} + outerParallel s r := add_assoc _ _ _
/-- `hyperplanePoint e a` is an isometry from `orthogonalHyperplane e` into `E`. -/
theorem isometry_hyperplanePoint (e : E) (a : ℝ) : Isometry (hyperplanePoint e a) :=
  (isometry_add_right (a • e)).comp (orthogonalHyperplane e).subtypeₗᵢ.isometry
/-- For `‖e‖ = 1`, the range of `hyperplanePoint e a` is `hyperplane e a`. -/
@[simp] theorem range_hyperplanePoint {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    Set.range (hyperplanePoint e a) = hyperplane e a := by
  ext x; simp only [Set.mem_range, mem_hyperplane]
  refine ⟨by rintro ⟨y, rfl⟩; exact inner_hyperplanePoint_self he a y, fun hx ↦ ?_⟩
  refine ⟨(orthogonalHyperplane e).orthogonalProjectionOnto x, ?_⟩
  simpa [hyperplanePoint, hx] using orthogonalProjection_orthogonalHyperplane_add_inner_smul he x
/-- Any `K ⊆ hyperplane e a` (`‖e‖ = 1`) is the image of its `hyperplanePoint e a`-preimage. -/
theorem image_preimage_hyperplanePoint_of_subset {e : E} (he : ‖e‖ = 1) {a : ℝ} {K : Set E}
    (hK : K ⊆ hyperplane e a) : hyperplanePoint e a '' (hyperplanePoint e a ⁻¹' K) = K := by
  rw [Set.image_preimage_eq_iff, range_hyperplanePoint he a]; exact hK
/-- For `‖e‖ = 1`, `hyperplanePoint e a ⁻¹' K` is the orthogonal projection image of `K`. -/
theorem preimage_hyperplanePoint_eq_image_orthogonalProjection {e : E} (he : ‖e‖ = 1) {a : ℝ}
    {K : Set E} (hK : K ⊆ hyperplane e a) :
    hyperplanePoint e a ⁻¹' K = (orthogonalHyperplane e).orthogonalProjectionOnto '' K := by
  ext y; simp only [Set.mem_preimage, Set.mem_image]
  refine ⟨fun hy ↦ ⟨hyperplanePoint e a y, hy, orthogonalProjectionOnto_hyperplanePoint e a y⟩, ?_⟩
  rintro ⟨x, hx, rfl⟩; have hxe : ⟪x, e⟫_ℝ = a := mem_hyperplane.1 (hK hx)
  have hpt : hyperplanePoint e a ((orthogonalHyperplane e).orthogonalProjectionOnto x) = x := by
    simpa [hyperplanePoint, hxe] using
      orthogonalProjection_orthogonalHyperplane_add_inner_smul he x
  rwa [hpt]
/-- Decomposing `hyperplanePoint e a '' K₀` via `orthogonalHyperplaneProdEquiv he`. -/
theorem hyperplanePoint_image_eq_singleton_add {e : E} (he : ‖e‖ = 1) (a : ℝ)
    (K₀ : Set (orthogonalHyperplane e)) :
    hyperplanePoint e a '' K₀ =
      {a • e} + orthogonalHyperplaneProdEquiv he '' (WithLp.toLp 2 '' (K₀ ×ˢ {(0 : ℝ)})) := by
  ext x; simp only [hyperplanePoint, Set.singleton_add, Set.mem_image, Set.mem_prod,
    Set.mem_singleton_iff]
  refine ⟨by rintro ⟨y, hy, rfl⟩; exact ⟨(y : E), ⟨WithLp.toLp 2 (y, 0),
    ⟨(y, 0), ⟨hy, rfl⟩, rfl⟩, by simp⟩, add_comm (a • e) _⟩, ?_⟩
  rintro ⟨_, ⟨_, ⟨⟨y, t⟩, ⟨hy, rfl⟩, rfl⟩, rfl⟩, rfl⟩; exact ⟨y, hy, by simp [add_comm]⟩
/-- Representation of `outerParallel (hyperplanePoint e a '' K₀) r`. -/
theorem outerParallel_hyperplanePoint_image {e : E} (he : ‖e‖ = 1) (a : ℝ)
    (K₀ : Set (orthogonalHyperplane e)) (r : ℝ) :
    outerParallel (hyperplanePoint e a '' K₀) r = {a • e} + orthogonalHyperplaneProdEquiv he ''
        outerParallel (WithLp.toLp 2 '' (K₀ ×ˢ {(0 : ℝ)})) r := by
  rw [hyperplanePoint_image_eq_singleton_add he a K₀, outerParallel_singleton_add,
    outerParallel_image_linearIsometryEquiv]
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
omit [MeasurableSpace E] [BorelSpace E] in
/-- If `K ⊆ E` is compact, then `hyperplanePoint e a ⁻¹' K` is compact. -/
theorem isCompact_preimage_hyperplanePoint (e : E) (a : ℝ) {K : Set E} (hK : IsCompact K) :
    IsCompact (hyperplanePoint e a ⁻¹' K) :=
  (isometry_hyperplanePoint e a).isClosedEmbedding.isCompact_preimage hK
/-- Any subset `s ⊆ hyperplane e a` (`e ≠ 0`) has ambient Lebesgue volume `0`. -/
theorem volume_eq_zero_of_subset_hyperplane {e : E} (he : e ≠ 0) {a : ℝ} {s : Set E}
    (hs : s ⊆ hyperplane e a) : volume s = 0 := measure_mono_null hs (volume_hyperplane he a)
/-- Any subset `s ⊆ hyperplane e a` (`e ≠ 0`) has ambient Caccioppoli perimeter `0`. -/
theorem perimeter_eq_zero_of_subset_hyperplane {e : E} (he : e ≠ 0) {a : ℝ} {s : Set E}
    (hs : s ⊆ hyperplane e a) : perimeter volume s = 0 :=
  perimeter_eq_zero_of_measure_zero (volume_eq_zero_of_subset_hyperplane he hs)
/-- Any hyperplane image `hyperplanePoint e a '' K₀` (`‖e‖ = 1`) has ambient volume `0`. -/
@[simp] theorem volume_hyperplanePoint_image_eq_zero {e : E} (he : ‖e‖ = 1) (a : ℝ)
    (K₀ : Set (orthogonalHyperplane e)) : volume (hyperplanePoint e a '' K₀) = 0 := by
  refine volume_eq_zero_of_subset_hyperplane (a := a)
    (norm_ne_zero_iff.mp (by rw [he]; exact one_ne_zero)) ?_
  rw [← range_hyperplanePoint he a]; exact Set.image_subset_range _ _
/-- Any hyperplane image `hyperplanePoint e a '' K₀` (`‖e‖ = 1`) has ambient perimeter `0`. -/
@[simp] theorem perimeter_hyperplanePoint_image_eq_zero {e : E} (he : ‖e‖ = 1) (a : ℝ)
    (K₀ : Set (orthogonalHyperplane e)) : perimeter volume (hyperplanePoint e a '' K₀) = 0 :=
  perimeter_eq_zero_of_measure_zero (volume_hyperplanePoint_image_eq_zero he a K₀)
/-- On `orthogonalHyperplane e` (`e ≠ 0`), `μHE[Module.finrank ℝ E - 1]` coincides with `volume`. -/
theorem euclideanHausdorffMeasure_orthogonalHyperplane_eq_volume {e : E} (he : e ≠ 0) :
    (μHE[Module.finrank ℝ E - 1] : Measure (orthogonalHyperplane e)) = volume := by
  rw [← finrank_orthogonalHyperplane he, InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
/-- For `e ≠ 0`, `μHE[Module.finrank ℝ E - 1] (hyperplanePoint e a '' K₀) = volume K₀`. -/
@[simp] theorem euclideanHausdorffMeasure_hyperplanePoint_image {e : E} (he : e ≠ 0) (a : ℝ)
    (K₀ : Set (orthogonalHyperplane e)) :
    μHE[Module.finrank ℝ E - 1] (hyperplanePoint e a '' K₀) = volume K₀ := by
  rw [(isometry_hyperplanePoint e a).euclideanHausdorffMeasure_image,
    euclideanHausdorffMeasure_orthogonalHyperplane_eq_volume he]
/-- For `‖e‖ = 1` and `K ⊆ hyperplane e a`, `volume (hyperplanePoint e a ⁻¹' K) = H^{n-1}(K)`. -/
theorem volume_preimage_hyperplanePoint_of_subset {e : E} (he : ‖e‖ = 1) {a : ℝ} {K : Set E}
    (hK : K ⊆ hyperplane e a) :
    volume (hyperplanePoint e a ⁻¹' K) = μHE[Module.finrank ℝ E - 1] K := by
  have he0 : e ≠ 0 := norm_ne_zero_iff.mp (by rw [he]; exact one_ne_zero)
  rw [← euclideanHausdorffMeasure_hyperplanePoint_image he0 a (hyperplanePoint e a ⁻¹' K),
    image_preimage_hyperplanePoint_of_subset he hK]
/-- Volume of `outerParallel (hyperplanePoint e a '' K₀) r` via `WithLp 2` product measure. -/
theorem volume_outerParallel_hyperplanePoint_image {e : E} (he : ‖e‖ = 1) (a : ℝ)
    (K₀ : Set (orthogonalHyperplane e)) (r : ℝ) :
    volume (outerParallel (hyperplanePoint e a '' K₀) r) = (Measure.map (WithLp.toLp 2)
        ((volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ)))
        (outerParallel (WithLp.toLp 2 '' (K₀ ×ˢ {(0 : ℝ)})) r) := by
  rw [outerParallel_hyperplanePoint_image he a K₀, Set.singleton_add, image_add_left,
    measure_preimage_add]
  have himg := Equiv.image_eq_preimage_symm (orthogonalHyperplaneProdEquiv he).toEquiv
    (outerParallel (WithLp.toLp 2 '' (K₀ ×ˢ {(0 : ℝ)})) r)
  have h1 : volume (orthogonalHyperplaneProdEquiv he ''
      outerParallel (WithLp.toLp 2 '' (K₀ ×ˢ {(0 : ℝ)})) r) =
      volume (outerParallel (WithLp.toLp 2 '' (K₀ ×ˢ {(0 : ℝ)})) r) :=
    himg ▸ (orthogonalHyperplaneProdEquiv he).symm.measurePreserving.measure_preimage_emb
      (orthogonalHyperplaneProdEquiv he).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding _
  have h2 : (Measure.map (WithLp.toLp 2)
      ((volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ))) = volume :=
    (WithLp.volume_preserving_toLp (orthogonalHyperplane e) ℝ).map_eq
  rw [h1, h2]
/-- Two-sided Fubini volume bounds for `outerParallel (hyperplanePoint e a '' K₀) r` (`r > 0`). -/
theorem volume_outerParallel_hyperplanePoint_image_div_bounds {e : E} (he : ‖e‖ = 1) (a : ℝ)
    (K₀ : Set (orthogonalHyperplane e)) {r : ℝ} (hr : 0 < r) :
    2 * volume K₀ ≤
        volume (outerParallel (hyperplanePoint e a '' K₀) r) / ENNReal.ofReal r ∧
      volume (outerParallel (hyperplanePoint e a '' K₀) r) / ENNReal.ofReal r ≤
        2 * volume (outerParallel K₀ r) := by
  rw [volume_outerParallel_hyperplanePoint_image he a K₀ r]; refine ⟨?_, ?_⟩
  · rw [← measure_prod_Icc_div volume K₀ hr,
      ← map_toLp_prod_image (volume.prod (volume : Measure ℝ)) (K₀ ×ˢ Icc (-r) r)]
    exact ENNReal.div_le_div_right (measure_mono (toLp_prod_Icc_subset_outerParallel K₀ hr.le)) _
  · rw [← measure_prod_Icc_div volume (outerParallel K₀ r) hr,
      ← map_toLp_prod_image (volume.prod (volume : Measure ℝ)) (outerParallel K₀ r ×ˢ Icc (-r) r)]
    exact ENNReal.div_le_div_right
      (measure_mono (outerParallel_toLp_prod_singleton_subset K₀ hr.le)) _
/-- **Outer-parallel difference quotient limit for `hyperplanePoint e a '' K₀`**. -/
theorem tendsto_outerParallel_hyperplanePoint_image_div {e : E} (he : ‖e‖ = 1) (a : ℝ)
    {K₀ : Set (orthogonalHyperplane e)} (hK₀ : IsCompact K₀) :
    Tendsto (fun r : ℝ ↦
      volume (outerParallel (hyperplanePoint e a '' K₀) r) / ENNReal.ofReal r)
      (𝓝[>] 0) (𝓝 (2 * volume K₀)) := by
  simpa [volume_outerParallel_hyperplanePoint_image he a K₀] using
    tendsto_outerParallel_toLp_prod_singleton_div hK₀
/-- Lower Minkowski content of `hyperplanePoint e a '' K₀` equals `2 * volume K₀`. -/
theorem lowerMinkowskiContent_hyperplanePoint_image {e : E} (he : ‖e‖ = 1) (a : ℝ)
    {K₀ : Set (orthogonalHyperplane e)} (hK₀ : IsCompact K₀) :
    lowerMinkowskiContent volume (hyperplanePoint e a '' K₀) = 2 * volume K₀ := by
  simpa [lowerMinkowskiContent, volume_hyperplanePoint_image_eq_zero he a K₀] using
    (tendsto_outerParallel_hyperplanePoint_image_div he a hK₀).liminf_eq
/-- Upper Minkowski content of `hyperplanePoint e a '' K₀` equals `2 * volume K₀`. -/
theorem upperMinkowskiContent_hyperplanePoint_image {e : E} (he : ‖e‖ = 1) (a : ℝ)
    {K₀ : Set (orthogonalHyperplane e)} (hK₀ : IsCompact K₀) :
    upperMinkowskiContent volume (hyperplanePoint e a '' K₀) = 2 * volume K₀ := by
  simpa [upperMinkowskiContent, volume_hyperplanePoint_image_eq_zero he a K₀] using
    (tendsto_outerParallel_hyperplanePoint_image_div he a hK₀).limsup_eq
/-- **Outer-parallel right derivative for `hyperplanePoint e a '' K₀`**. -/
theorem hasDerivWithinAt_outerParallel_hyperplanePoint_image {e : E} (he : ‖e‖ = 1) (a : ℝ)
    {K₀ : Set (orthogonalHyperplane e)} (hK₀ : IsCompact K₀) :
    HasDerivWithinAt (fun r : ℝ ↦ (volume (outerParallel (hyperplanePoint e a '' K₀) r)).toReal)
      (2 * (volume K₀).toReal) (Ici 0) 0 := by
  simpa [volume_outerParallel_hyperplanePoint_image he a K₀] using
    hasDerivWithinAt_outerParallel_toLp_prod_singleton hK₀
/-- **Hyperplane outer-parallel difference quotient limit (`2 * μHE[finrank ℝ E - 1] K`)**. -/
theorem tendsto_outerParallel_of_subset_hyperplane_div {e : E} (he : ‖e‖ = 1) {a : ℝ}
    {K : Set E} (hK : IsCompact K) (hK_sub : K ⊆ hyperplane e a) :
    Tendsto (fun r : ℝ ↦ volume (outerParallel K r) / ENNReal.ofReal r)
      (𝓝[>] 0) (𝓝 (2 * μHE[Module.finrank ℝ E - 1] K)) := by
  have himg := image_preimage_hyperplanePoint_of_subset he hK_sub
  rw [← volume_preimage_hyperplanePoint_of_subset he hK_sub]
  conv in outerParallel K _ => rw [← himg]
  exact tendsto_outerParallel_hyperplanePoint_image_div he a
    (isCompact_preimage_hyperplanePoint e a hK)
/-- Lower Minkowski content of compact `K ⊆ hyperplane e a` equals `2 * H^{n-1}(K)`. -/
theorem lowerMinkowskiContent_of_subset_hyperplane {e : E} (he : ‖e‖ = 1) {a : ℝ}
    {K : Set E} (hK : IsCompact K) (hK_sub : K ⊆ hyperplane e a) :
    lowerMinkowskiContent volume K = 2 * μHE[Module.finrank ℝ E - 1] K := by
  have h0 := volume_eq_zero_of_subset_hyperplane
    (norm_ne_zero_iff.mp (by rw [he]; exact one_ne_zero)) hK_sub
  simpa [lowerMinkowskiContent, h0] using
    (tendsto_outerParallel_of_subset_hyperplane_div he hK hK_sub).liminf_eq
/-- Upper Minkowski content of compact `K ⊆ hyperplane e a` equals `2 * H^{n-1}(K)`. -/
theorem upperMinkowskiContent_of_subset_hyperplane {e : E} (he : ‖e‖ = 1) {a : ℝ}
    {K : Set E} (hK : IsCompact K) (hK_sub : K ⊆ hyperplane e a) :
    upperMinkowskiContent volume K = 2 * μHE[Module.finrank ℝ E - 1] K := by
  have h0 := volume_eq_zero_of_subset_hyperplane
    (norm_ne_zero_iff.mp (by rw [he]; exact one_ne_zero)) hK_sub
  simpa [upperMinkowskiContent, h0] using
    (tendsto_outerParallel_of_subset_hyperplane_div he hK hK_sub).limsup_eq
/-- **Hyperplane outer-parallel right derivative formula (`2 * H^{n-1}(K)`)**. -/
theorem hasDerivWithinAt_outerParallel_of_subset_hyperplane {e : E} (he : ‖e‖ = 1) {a : ℝ}
    {K : Set E} (hK : IsCompact K) (hK_sub : K ⊆ hyperplane e a) :
    HasDerivWithinAt (fun r : ℝ ↦ (volume (outerParallel K r)).toReal)
      (2 * (μHE[Module.finrank ℝ E - 1] K).toReal) (Ici 0) 0 := by
  have himg := image_preimage_hyperplanePoint_of_subset he hK_sub
  rw [← volume_preimage_hyperplanePoint_of_subset he hK_sub]
  conv in outerParallel K _ => rw [← himg]
  exact hasDerivWithinAt_outerParallel_hyperplanePoint_image he a
    (isCompact_preimage_hyperplanePoint e a hK)
/-- **Codimension-1 strict gap between outer-parallel derivative, `H^{n-1}`, and perimeter**. -/
theorem outerParallelDeriv_gt_perimeter_and_hausdorffMeasure_of_codim_one {e : E} (he : ‖e‖ = 1)
    {a : ℝ} {K : Set E} (hK : IsCompact K) (hK_sub : K ⊆ hyperplane e a)
    (hK_pos : 0 < μHE[Module.finrank ℝ E - 1] K) :
    volume K = 0 ∧ perimeter volume K = 0 ∧
      HasDerivWithinAt (fun r : ℝ ↦ (volume (outerParallel K r)).toReal)
        (2 * (μHE[Module.finrank ℝ E - 1] K).toReal) (Ici 0) 0 ∧
      (perimeter volume K).toReal < (μHE[Module.finrank ℝ E - 1] K).toReal ∧
      (μHE[Module.finrank ℝ E - 1] K).toReal < 2 * (μHE[Module.finrank ℝ E - 1] K).toReal := by
  have he0 : e ≠ 0 := norm_ne_zero_iff.mp (by rw [he]; exact one_ne_zero)
  have hper : perimeter volume K = 0 := perimeter_eq_zero_of_subset_hyperplane he0 hK_sub
  have hfin : μHE[Module.finrank ℝ E - 1] K ≠ ⊤ := by
    rw [← volume_preimage_hyperplanePoint_of_subset he hK_sub]
    exact (isCompact_preimage_hyperplanePoint e a hK).measure_lt_top.ne
  have hpos_real : 0 < (μHE[Module.finrank ℝ E - 1] K).toReal := ENNReal.toReal_pos hK_pos.ne' hfin
  refine ⟨volume_eq_zero_of_subset_hyperplane he0 hK_sub, hper,
    hasDerivWithinAt_outerParallel_of_subset_hyperplane he hK hK_sub, by simp [hper, hpos_real],
    by linarith⟩
/-- **Higher-codimension (`≥ 2`) vanishing of `(n-1)`-measure and outer-parallel derivative**. -/
theorem hasDerivWithinAt_outerParallel_of_subset_hyperplane_of_hausdorffMeasure_eq_zero
    {e : E} (he : ‖e‖ = 1) {a : ℝ} {K : Set E} (hK : IsCompact K) (hK_sub : K ⊆ hyperplane e a)
    (hK_zero : μHE[Module.finrank ℝ E - 1] K = 0) :
    lowerMinkowskiContent volume K = 0 ∧ upperMinkowskiContent volume K = 0 ∧
      HasDerivWithinAt (fun r : ℝ ↦ (volume (outerParallel K r)).toReal) 0 (Ici 0) 0 := by
  refine ⟨by simp [lowerMinkowskiContent_of_subset_hyperplane he hK hK_sub, hK_zero],
    by simp [upperMinkowskiContent_of_subset_hyperplane he hK hK_sub, hK_zero], ?_⟩
  simpa [hK_zero] using hasDerivWithinAt_outerParallel_of_subset_hyperplane he hK hK_sub
/-- **Subspaces of codimension `≥ 2`**: `volume K = 0`, `perimeter = 0`, and `H^{n-1}(K) = 0`. -/
theorem hasDerivWithinAt_outerParallel_of_subset_submodule_codim_ge_two
    {s : Submodule ℝ E} (hcodim : Module.finrank ℝ s + 2 ≤ Module.finrank ℝ E)
    {K : Set E} (hK : IsCompact K) (hK_sub : K ⊆ (s : Set E)) :
    volume K = 0 ∧ perimeter volume K = 0 ∧ μHE[Module.finrank ℝ E - 1] K = 0 ∧
      lowerMinkowskiContent volume K = 0 ∧ upperMinkowskiContent volume K = 0 ∧
      HasDerivWithinAt (fun r : ℝ ↦ (volume (outerParallel K r)).toReal) 0 (Ici 0) 0 := by
  have hortho_dim : 2 ≤ Module.finrank ℝ (sᗮ : Submodule ℝ E) := by
    have hsum := s.finrank_add_finrank_orthogonal; omega
  have hnt : Nontrivial sᗮ :=
    Module.nontrivial_of_finrank_pos (Nat.lt_of_lt_of_le zero_lt_two hortho_dim)
  obtain ⟨v, hv⟩ := exists_ne (0 : sᗮ); set u : sᗮ := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv; have he : ‖(u : E)‖ = 1 := hu
  have he0 : (u : E) ≠ 0 := norm_ne_zero_iff.mp (by rw [he]; exact one_ne_zero)
  have hK_hyp : K ⊆ hyperplane (u : E) 0 := fun x hx ↦ by
    rw [mem_hyperplane, real_inner_comm]
    exact (Submodule.mem_orthogonal' s u.1).1 u.2 x (hK_sub hx)
  have hKs_compact : IsCompact ((Subtype.val : s → E) ⁻¹' K) :=
    isometry_subtype_coe.isClosedEmbedding.isCompact_preimage hK
  have hK_img : (Subtype.val : s → E) '' ((Subtype.val : s → E) ⁻¹' K) = K :=
    Set.image_preimage_eq_of_subset (by simpa using hK_sub)
  have hKs_fin : μHE[Module.finrank ℝ s] K ≠ ⊤ := by
    rw [← hK_img, isometry_subtype_coe.euclideanHausdorffMeasure_image,
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    exact hKs_compact.measure_lt_top.ne
  have hlt : Module.finrank ℝ s < Module.finrank ℝ E - 1 := by omega
  have hK_zero : μHE[Module.finrank ℝ E - 1] K = 0 :=
    (MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top hlt K).resolve_right hKs_fin
  obtain ⟨hlow, hupp, hderiv⟩ :=
    hasDerivWithinAt_outerParallel_of_subset_hyperplane_of_hausdorffMeasure_eq_zero
      he hK hK_hyp hK_zero
  exact ⟨volume_eq_zero_of_subset_hyperplane he0 hK_hyp,
    perimeter_eq_zero_of_subset_hyperplane he0 hK_hyp, hK_zero, hlow, hupp, hderiv⟩
end LowerDimensionalParallelVolume

/-! ### Section 2: Closed convex hull & difference-body `(1/2) • (K - K)` isodiametric inequality -/
section DifferenceBodyIsodiametry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The **closed convex hull** `closure (convexHull ℝ s)` of a subset `s ⊆ E`. -/
def closedConvexHull (s : Set E) : Set E := closure (convexHull ℝ s)
/-- The **normalized difference body** `(1 / 2 : ℝ) • (closedConvexHull s - closedConvexHull s)`. -/
def differenceBody (s : Set E) : Set E := (1 / 2 : ℝ) • (closedConvexHull s - closedConvexHull s)
theorem subset_convexHull_closedConvexHull (s : Set E) : convexHull ℝ s ⊆ closedConvexHull s :=
  subset_closure
theorem subset_closedConvexHull (s : Set E) : s ⊆ closedConvexHull s :=
  (subset_convexHull ℝ s).trans subset_closure
theorem closure_subset_closedConvexHull (s : Set E) : closure s ⊆ closedConvexHull s :=
  closure_mono (subset_convexHull ℝ s)
theorem isClosed_closedConvexHull (s : Set E) : IsClosed (closedConvexHull s) := isClosed_closure
theorem convex_closedConvexHull (s : Set E) : Convex ℝ (closedConvexHull s) :=
  (convex_convexHull ℝ s).closure
theorem closedConvexHull_mono {s t : Set E} (hst : s ⊆ t) :
    closedConvexHull s ⊆ closedConvexHull t := closure_mono (convexHull_mono hst)
theorem closedConvexHull_eq_self {s : Set E} (hs_conv : Convex ℝ s) (hs_closed : IsClosed s) :
    closedConvexHull s = s := by rw [closedConvexHull, hs_conv.convexHull_eq, hs_closed.closure_eq]
@[simp] theorem closedConvexHull_empty : closedConvexHull (∅ : Set E) = ∅ := by
  simp [closedConvexHull]
@[simp] theorem closedConvexHull_closure (s : Set E) :
    closedConvexHull (closure s) = closedConvexHull s := Subset.antisymm (closure_minimal
    (convexHull_min (closure_subset_closedConvexHull s) (convex_closedConvexHull s))
    (isClosed_closedConvexHull s)) (closedConvexHull_mono subset_closure)
@[simp] theorem closedConvexHull_closedConvexHull (s : Set E) :
    closedConvexHull (closedConvexHull s) = closedConvexHull s :=
  closedConvexHull_eq_self (convex_closedConvexHull s) (isClosed_closedConvexHull s)
theorem closedConvexHull_nonempty {s : Set E} (hs : s.Nonempty) :
    (closedConvexHull s).Nonempty := hs.mono (subset_closedConvexHull s)
@[simp] theorem ediam_closedConvexHull (s : Set E) :
    Metric.ediam (closedConvexHull s) = Metric.ediam s := by
  rw [closedConvexHull, Metric.ediam_closure, convexHull_ediam]
@[simp] theorem diam_closedConvexHull (s : Set E) :
    Metric.diam (closedConvexHull s) = Metric.diam s := by
  rw [closedConvexHull, Metric.diam_closure, convexHull_diam]
@[simp] theorem isBounded_closedConvexHull_iff {s : Set E} :
    Bornology.IsBounded (closedConvexHull s) ↔ Bornology.IsBounded s := by
  rw [closedConvexHull, isBounded_closure_iff, isBounded_convexHull]
theorem isBounded_closedConvexHull {s : Set E} (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (closedConvexHull s) := isBounded_closedConvexHull_iff.2 hs
theorem isCompact_closedConvexHull [ProperSpace E] {s : Set E} (hs : Bornology.IsBounded s) :
    IsCompact (closedConvexHull s) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_closedConvexHull s)
    (isBounded_closedConvexHull hs)
/-- `differenceBody s` as midpoint Minkowski sum of `closedConvexHull s` and its negation. -/
theorem differenceBody_eq_smul_add_smul_neg (s : Set E) :
    differenceBody s = (1 / 2 : ℝ) • closedConvexHull s + (1 / 2 : ℝ) • (-closedConvexHull s) := by
  rw [differenceBody, sub_eq_add_neg, smul_add]
theorem convex_differenceBody (s : Set E) : Convex ℝ (differenceBody s) :=
  ((convex_closedConvexHull s).sub (convex_closedConvexHull s)).smul (1 / 2 : ℝ)
theorem neg_mem_differenceBody (s : Set E) {z : E} (hz : z ∈ differenceBody s) :
    -z ∈ differenceBody s := by
  rcases hz with ⟨w, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  exact ⟨y - x, ⟨y, hy, x, hx, rfl⟩, by simp [smul_sub]⟩
@[simp] theorem preimage_neg_differenceBody (s : Set E) :
    Neg.neg ⁻¹' differenceBody s = differenceBody s := by
  ext z; exact ⟨fun hz ↦ by simpa using neg_mem_differenceBody s hz, neg_mem_differenceBody s⟩
theorem zero_mem_differenceBody {s : Set E} (hs : s.Nonempty) : (0 : E) ∈ differenceBody s := by
  obtain ⟨x, hx⟩ := closedConvexHull_nonempty hs
  exact ⟨0, ⟨x, hx, x, hx, sub_self x⟩, smul_zero _⟩
theorem differenceBody_nonempty {s : Set E} (hs : s.Nonempty) : (differenceBody s).Nonempty :=
  ⟨0, zero_mem_differenceBody hs⟩
theorem isBounded_differenceBody {s : Set E} (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (differenceBody s) :=
  ((isBounded_closedConvexHull hs).sub (isBounded_closedConvexHull hs)).smul₀ (1 / 2 : ℝ)
theorem isCompact_differenceBody [ProperSpace E] {s : Set E} (hs : Bornology.IsBounded s) :
    IsCompact (differenceBody s) := by
  rw [differenceBody, sub_eq_add_neg]
  exact ((isCompact_closedConvexHull hs).add (isCompact_closedConvexHull hs).neg).smul (1 / 2 : ℝ)
theorem isClosed_differenceBody [ProperSpace E] {s : Set E} (hs : Bornology.IsBounded s) :
    IsClosed (differenceBody s) := (isCompact_differenceBody hs).isClosed
/-- Every element of `differenceBody s` has norm at most `Metric.diam s / 2`. -/
theorem norm_le_diam_div_two_of_mem_differenceBody {s : Set E} (hs : Bornology.IsBounded s)
    {z : E} (hz : z ∈ differenceBody s) : ‖z‖ ≤ Metric.diam s / 2 := by
  rcases hz with ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  have hxy : dist x y ≤ Metric.diam s :=
    (Metric.dist_le_diam_of_mem (isBounded_closedConvexHull hs) hx hy).trans_eq
      (diam_closedConvexHull s)
  rw [norm_smul, Real.norm_of_nonneg (by positivity), ← dist_eq_norm]; linarith
/-- **Difference-body ball inclusion**: `differenceBody s ⊆ Metric.closedBall 0 (diam s / 2)`. -/
theorem differenceBody_subset_closedBall {s : Set E} (hs : Bornology.IsBounded s) :
    differenceBody s ⊆ Metric.closedBall (0 : E) (Metric.diam s / 2) := fun z hz ↦ by
  simpa [Metric.mem_closedBall, dist_zero_right] using
    norm_le_diam_div_two_of_mem_differenceBody hs hz
/-- **Diameter preservation of `differenceBody`**: `ediam (differenceBody s) = ediam s`. -/
@[simp] theorem ediam_differenceBody (s : Set E) :
    Metric.ediam (differenceBody s) = Metric.ediam s := by
  refine le_antisymm (Metric.ediam_le fun u hu v hv ↦ ?_) (Metric.ediam_le fun x hx y hy ↦ ?_)
  · rcases hu with ⟨_, ⟨x₁, hx₁, y₁, hy₁, rfl⟩, rfl⟩
    rcases hv with ⟨_, ⟨x₂, hx₂, y₂, hy₂, rfl⟩, rfl⟩; dsimp only
    have hsub : (1 / 2 : ℝ) • (x₁ - y₁) - (1 / 2 : ℝ) • (x₂ - y₂) =
        (1 / 2 : ℝ) • (x₁ - x₂) + (1 / 2 : ℝ) • (y₂ - y₁) := by
      rw [← smul_sub, ← smul_add]; congr 1; abel
    have hnorm : dist ((1 / 2 : ℝ) • (x₁ - y₁)) ((1 / 2 : ℝ) • (x₂ - y₂)) ≤
        (1 / 2 : ℝ) * dist x₁ x₂ + (1 / 2 : ℝ) * dist y₂ y₁ := by
      rw [dist_eq_norm, hsub]; refine (norm_add_le _ _).trans ?_
      simp [norm_smul, dist_eq_norm]
    rw [edist_dist]; refine (ENNReal.ofReal_le_ofReal hnorm).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ← edist_dist, ← edist_dist]
    have hd₁ : edist x₁ x₂ ≤ Metric.ediam s :=
      ediam_closedConvexHull s ▸ Metric.edist_le_ediam_of_mem hx₁ hx₂
    have hd₂ : edist y₂ y₁ ≤ Metric.ediam s :=
      ediam_closedConvexHull s ▸ Metric.edist_le_ediam_of_mem hy₂ hy₁
    calc
      ENNReal.ofReal (1 / 2) * edist x₁ x₂ + ENNReal.ofReal (1 / 2) * edist y₂ y₁ ≤
          ENNReal.ofReal (1 / 2) * Metric.ediam s + ENNReal.ofReal (1 / 2) * Metric.ediam s := by
        gcongr
      _ = Metric.ediam s := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
          ENNReal.ofReal_one, one_mul]
  · have hz : (1 / 2 : ℝ) • (x - y) ∈ differenceBody s :=
      ⟨x - y, ⟨x, subset_closedConvexHull s hx, y, subset_closedConvexHull s hy, rfl⟩, rfl⟩
    have hnz : -((1 / 2 : ℝ) • (x - y)) ∈ differenceBody s := neg_mem_differenceBody s hz
    have hdist : edist x y = edist ((1 / 2 : ℝ) • (x - y)) (-((1 / 2 : ℝ) • (x - y))) := by
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ,
        smul_smul, mul_one_div_cancel two_ne_zero, one_smul]
    rw [hdist]; exact Metric.edist_le_ediam_of_mem hz hnz
/-- **Diameter preservation of `differenceBody`**: `Metric.diam (differenceBody s) = diam s`. -/
@[simp] theorem diam_differenceBody (s : Set E) :
    Metric.diam (differenceBody s) = Metric.diam s := by
  simp only [Metric.diam, ediam_differenceBody]
/-- Helper identity `a ^ (1 / 2) * a ^ (1 / 2) = a` in `ℝ≥0∞`. -/
theorem ennreal_rpow_half_mul_self (a : ℝ≥0∞) : a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := by
  rcases eq_or_ne a 0 with rfl | ha0; · simp
  rcases eq_or_ne a ⊤ with rfl | hatop; · simp
  rw [← ENNReal.rpow_add _ _ ha0 hatop, add_halves, ENNReal.rpow_one]
variable [MeasureSpace E]
/-- For every set `s ⊆ E`, `volume s ≤ volume (closedConvexHull s)`. -/
theorem volume_le_volume_closedConvexHull (s : Set E) : volume s ≤ volume (closedConvexHull s) :=
  measure_mono (subset_closedConvexHull s)
variable [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
/-- Multiplicative Brunn–Minkowski gives `volume K ≤ volume ((1 / 2 : ℝ) • (K - K))`. -/
theorem volume_le_volume_half_smul_sub {K : Set E} (hK : MeasurableSet K) :
    volume K ≤ volume ((1 / 2 : ℝ) • (K - K)) := by
  have hBM := volume_smul_add_smul_ge_geom_mean (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hK hK.neg
  rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, measure_neg, ennreal_rpow_half_mul_self,
    ← smul_add, ← sub_eq_add_neg] at hBM
/-- **Brunn–Minkowski difference-body volume inequality**. -/
theorem volume_closedConvexHull_le_volume_differenceBody (s : Set E) :
    volume (closedConvexHull s) ≤ volume (differenceBody s) :=
  volume_le_volume_half_smul_sub (isClosed_closedConvexHull s).measurableSet
/-- For every set `s ⊆ E`, `volume s ≤ volume (differenceBody s)`. -/
theorem volume_le_volume_differenceBody (s : Set E) : volume s ≤ volume (differenceBody s) :=
  (volume_le_volume_closedConvexHull s).trans (volume_closedConvexHull_le_volume_differenceBody s)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
/-- Volume of `differenceBody s` is at most `volume (Metric.closedBall 0 (Metric.diam s / 2))`. -/
theorem volume_differenceBody_le_volume_closedBall_diam_div_two {s : Set F}
    (hs : Bornology.IsBounded s) :
    volume (differenceBody s) ≤ volume (Metric.closedBall (0 : F) (Metric.diam s / 2)) :=
  measure_mono (differenceBody_subset_closedBall hs)
/-- **Difference-body isodiametric inequality chain**. -/
theorem isodiametric_differenceBody_chain {s : Set F} (hs : Bornology.IsBounded s) :
    volume s ≤ volume (closedConvexHull s) ∧
      volume (closedConvexHull s) ≤ volume (differenceBody s) ∧
      volume (differenceBody s) ≤ volume (Metric.closedBall (0 : F) (Metric.diam s / 2)) :=
  ⟨volume_le_volume_closedConvexHull s,
    volume_closedConvexHull_le_volume_differenceBody s,
    volume_differenceBody_le_volume_closedBall_diam_div_two hs⟩
/-- **The Euclidean Isodiametric Inequality via the Brunn–Minkowski difference body**. -/
theorem isodiametric_inequality_via_differenceBody {s : Set F} (hs : Bornology.IsBounded s) :
    volume s ≤ volume (Metric.closedBall (0 : F) (Metric.diam s / 2)) :=
  (volume_le_volume_differenceBody s).trans
    (volume_differenceBody_le_volume_closedBall_diam_div_two hs)
/-- **Open-ball Isodiametric Inequality via the Brunn–Minkowski difference body**. -/
theorem isodiametric_inequality_ball_via_differenceBody [Nontrivial F] {s : Set F}
    (hs : Bornology.IsBounded s) :
    volume s ≤ volume (Metric.ball (0 : F) (Metric.diam s / 2)) := by
  rw [← Measure.addHaar_closedBall_eq_addHaar_ball]
  exact isodiametric_inequality_via_differenceBody hs
end DifferenceBodyIsodiametry

/-! ### Section 3: Isodiametric ball rigidity, closed convex body equality, and converse -/
section IsodiametricRigidityAndConverse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- If `s ⊆ t` with `NullMeasurableSet s μ`, `μ t ≠ ⊤`, and `μ s = μ t`, then `s =ᵐ[μ] t`. -/
theorem ae_eq_of_subset_of_measure_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hst : s ⊆ t) (hs : NullMeasurableSet s μ) (ht_top : μ t ≠ ⊤)
    (heq : μ s = μ t) : s =ᵐ[μ] t := by
  rw [ae_eq_set]
  refine ⟨measure_mono_null (Set.sdiff_eq_empty.2 hst).subset measure_empty, ?_⟩
  rw [measure_sdiff hst hs (heq ▸ ht_top), heq, tsub_self]
/-- **Full-measure closed subset of a closed ball is the closed ball**. -/
theorem eq_closedBall_of_isClosed_of_subset_closedBall_of_volume_eq {c : E} {r : ℝ} (hr : 0 ≤ r)
    {K : Set E} (hK_ne : K.Nonempty) (hK_closed : IsClosed K)
    (hK_sub : K ⊆ Metric.closedBall c r) (hvol : volume K = volume (Metric.closedBall c r)) :
    K = Metric.closedBall c r := by
  rcases eq_or_lt_of_le hr with rfl | hr_pos
  · obtain ⟨x, hx⟩ := hK_ne; have hxc : x = c := by simpa using hK_sub hx
    exact Subset.antisymm hK_sub (by simp [← hxc, hx])
  · refine Subset.antisymm hK_sub ?_
    have hdiff_cb : volume (Metric.closedBall c r \ K) = 0 := by
      rw [measure_sdiff hK_sub hK_closed.nullMeasurableSet
        (hvol ▸ (ProperSpace.isCompact_closedBall c r).measure_lt_top.ne), hvol, tsub_self]
    have hdiff_b : volume (Metric.ball c r \ K) = 0 :=
      measure_mono_null (Set.sdiff_subset_sdiff_left Metric.ball_subset_closedBall) hdiff_cb
    have hball_sub : Metric.ball c r ⊆ K := by
      simpa [hK_closed.closure_eq] using
        isOpen_ball.subset_closure_of_measure_diff_eq_zero hdiff_b
    rw [← closure_ball c hr_pos.ne', ← hK_closed.closure_eq]; exact closure_mono hball_sub
/-- **Equality in the difference-body chain under isodiametric equality**. -/
theorem volume_closedConvexHull_and_differenceBody_eq_of_isodiametric_eq {s : Set E}
    (hs : Bornology.IsBounded s)
    (heq : volume s = volume (Metric.closedBall (0 : E) (Metric.diam s / 2))) :
    volume (closure s) = volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) ∧
      volume (closedConvexHull s) = volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) ∧
      volume (differenceBody s) = volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) := by
  obtain ⟨h1, h2, h3⟩ := isodiametric_differenceBody_chain hs
  have hcl_cch : volume (closure s) ≤ volume (closedConvexHull s) :=
    measure_mono (closure_subset_closedConvexHull s)
  exact ⟨le_antisymm (hcl_cch.trans (h2.trans h3)) (heq ▸ measure_mono subset_closure),
    le_antisymm (h2.trans h3) (heq ▸ h1), le_antisymm h3 (heq ▸ h1.trans h2)⟩
/-- **Almost-everywhere convexity under isodiametric equality**. -/
theorem ae_eq_closedConvexHull_of_isodiametric_eq {s : Set E} (hs : Bornology.IsBounded s)
    (hs_meas : NullMeasurableSet s volume)
    (heq : volume s = volume (Metric.closedBall (0 : E) (Metric.diam s / 2))) :
    (s =ᵐ[volume] closure s) ∧ (s =ᵐ[volume] closedConvexHull s) := by
  obtain ⟨hcl, hcch, _⟩ := volume_closedConvexHull_and_differenceBody_eq_of_isodiametric_eq hs heq
  have htop : volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : E) (Metric.diam s / 2)).measure_lt_top.ne
  exact ⟨ae_eq_of_subset_of_measure_eq subset_closure hs_meas (hcl ▸ htop) (heq.trans hcl.symm),
    ae_eq_of_subset_of_measure_eq (subset_closedConvexHull s) hs_meas (hcch ▸ htop)
      (heq.trans hcch.symm)⟩
/-- **Exact point-set ball rigidity of `differenceBody s` under isodiametric equality**. -/
theorem differenceBody_eq_closedBall_of_isodiametric_eq {s : Set E} (hs_ne : s.Nonempty)
    (hs : Bornology.IsBounded s)
    (heq : volume s = volume (Metric.closedBall (0 : E) (Metric.diam s / 2))) :
    differenceBody s = Metric.closedBall (0 : E) (Metric.diam s / 2) :=
  eq_closedBall_of_isClosed_of_subset_closedBall_of_volume_eq
    (div_nonneg Metric.diam_nonneg zero_le_two) (differenceBody_nonempty hs_ne)
    (isClosed_differenceBody hs) (differenceBody_subset_closedBall hs)
    (volume_closedConvexHull_and_differenceBody_eq_of_isodiametric_eq hs heq).2.2
/-- **Iterated Steiner symmetrization a.e.-rigidity under isodiametric equality**. -/
theorem steinerSymmetrizationBasis_closure_ae_eq_closedBall_of_isodiametric_eq {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) {s : Set E} (hs : Bornology.IsBounded s)
    (heq : volume s = volume (Metric.closedBall (0 : E) (Metric.diam s / 2))) :
    steinerSymmetrizationBasis b (closure s) =ᵐ[volume]
      Metric.closedBall (0 : E) (Metric.diam s / 2) := by
  have hcl := (volume_closedConvexHull_and_differenceBody_eq_of_isodiametric_eq hs heq).1
  have hsub : steinerSymmetrizationBasis b (closure s) ⊆
      Metric.closedBall (0 : E) (Metric.diam s / 2) := by
    simpa [Metric.diam_closure] using
      steinerSymmetrizationBasis_subset_closedBall_diam_div_two b hs.closure
  have hvol : volume (steinerSymmetrizationBasis b (closure s)) =
      volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) := by
    rw [volume_steinerSymmetrizationBasis b isClosed_closure.measurableSet, hcl]
  exact ae_eq_of_subset_of_measure_eq hsub
    (measurableSet_steinerSymmetrizationBasis b isClosed_closure.measurableSet).nullMeasurableSet
    (ProperSpace.isCompact_closedBall (0 : E) (Metric.diam s / 2)).measure_lt_top.ne hvol
/-- **Isodiametric ball rigidity for sets contained in a closed ball of radius `diam s / 2`**. -/
theorem closure_and_closedConvexHull_eq_closedBall_of_subset_closedBall {c : E} {s : Set E}
    (hs_ne : s.Nonempty) (hs_sub : s ⊆ Metric.closedBall c (Metric.diam s / 2))
    (heq : volume s = volume (Metric.closedBall (0 : E) (Metric.diam s / 2))) :
    closure s = Metric.closedBall c (Metric.diam s / 2) ∧
      closedConvexHull s = Metric.closedBall c (Metric.diam s / 2) := by
  have hs_bdd : Bornology.IsBounded s := Metric.isBounded_closedBall.subset hs_sub
  obtain ⟨hcl, hcch, _⟩ :=
    volume_closedConvexHull_and_differenceBody_eq_of_isodiametric_eq hs_bdd heq
  have hvol_c : volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) =
      volume (Metric.closedBall c (Metric.diam s / 2)) :=
    (Measure.addHaar_closedBall_center volume c (Metric.diam s / 2)).symm
  have hr : 0 ≤ Metric.diam s / 2 := div_nonneg Metric.diam_nonneg zero_le_two
  have hcch_sub : closedConvexHull s ⊆ Metric.closedBall c (Metric.diam s / 2) :=
    closure_minimal (convexHull_min hs_sub (convex_closedBall c _)) Metric.isClosed_closedBall
  exact ⟨eq_closedBall_of_isClosed_of_subset_closedBall_of_volume_eq hr hs_ne.closure
      isClosed_closure (closure_minimal hs_sub Metric.isClosed_closedBall) (hcl.trans hvol_c),
    eq_closedBall_of_isClosed_of_subset_closedBall_of_volume_eq hr (closedConvexHull_nonempty hs_ne)
      (isClosed_closedConvexHull s) hcch_sub (hcch.trans hvol_c)⟩
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Any bounded `s ⊆ E` centrally symmetric into `closedConvexHull s` lies in `closedBall c`. -/
theorem subset_closedBall_diam_div_two_of_symm_center {c : E} {s : Set E}
    (hs : Bornology.IsBounded s) (hs_symm : ∀ x ∈ s, (2 : ℝ) • c - x ∈ closedConvexHull s) :
    s ⊆ Metric.closedBall c (Metric.diam s / 2) := by
  intro x hx; rw [Metric.mem_closedBall, le_div_iff₀ zero_lt_two]
  have hdist : dist x ((2 : ℝ) • c - x) ≤ Metric.diam (closedConvexHull s) :=
    Metric.dist_le_diam_of_mem (isBounded_closedConvexHull hs)
      (subset_closedConvexHull s hx) (hs_symm x hx)
  have htwo : dist x ((2 : ℝ) • c - x) = dist x c * 2 := by
    rw [dist_eq_norm, dist_eq_norm, show x - ((2 : ℝ) • c - x) = (2 : ℝ) • (x - c) by
      rw [two_smul, two_smul]; abel, norm_smul, Real.norm_ofNat, mul_comm]
  rwa [htwo, diam_closedConvexHull] at hdist
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `-K = {a} + K` (`K := closedConvexHull s`), `K` is a translate of `differenceBody s`. -/
theorem subset_closedBall_and_closedConvexHull_eq_translate_differenceBody_of_neg_eq_add
    {a : E} {s : Set E} (hs : Bornology.IsBounded s)
    (hneg : -closedConvexHull s = {a} + closedConvexHull s) :
    s ⊆ Metric.closedBall (-((1 / 2 : ℝ) • a)) (Metric.diam s / 2) ∧
      closedConvexHull s = {-((1 / 2 : ℝ) • a)} + differenceBody s := by
  set c : E := -((1 / 2 : ℝ) • a)
  have h2c : (2 : ℝ) • c = -a := by dsimp [c]; rw [smul_neg, smul_smul]; norm_num
  have hsymm : ∀ x ∈ closedConvexHull s, (2 : ℝ) • c - x ∈ closedConvexHull s := by
    intro x hx; have hnx : -x ∈ -closedConvexHull s := Set.neg_mem_neg.2 hx
    rw [hneg, Set.singleton_add] at hnx; rcases hnx with ⟨y, hy, hyx⟩
    have hx' : x = -(a + y) := by rw [← neg_eq_iff_eq_neg]; exact hyx.symm
    have hyeq : y = (2 : ℝ) • c - x := by rw [h2c, hx']; abel
    rwa [← hyeq]
  refine ⟨subset_closedBall_diam_div_two_of_symm_center hs
    (fun x hx ↦ hsymm x (subset_closedConvexHull s hx)), ?_⟩
  ext x; simp only [Set.singleton_add, Set.mem_image, differenceBody, Set.mem_smul_set, Set.mem_sub]
  constructor
  · intro hx
    refine ⟨x - c, ⟨x - (2 : ℝ) • c + x, ⟨x, hx, (2 : ℝ) • c - x, hsymm x hx, by abel⟩, ?_⟩,
      add_sub_cancel c x⟩
    rw [two_smul, show x - (c + c) + x = (2 : ℝ) • (x - c) by rw [two_smul]; abel,
      smul_smul, one_div_mul_cancel two_ne_zero, one_smul]
  · rintro ⟨_, ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩, rfl⟩
    have hv' : (2 : ℝ) • c - v ∈ closedConvexHull s := hsymm v hv
    have hmid : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • ((2 : ℝ) • c - v) ∈ closedConvexHull s :=
      convex_closedConvexHull s hu hv' (by positivity) (by positivity) (by ring)
    have heq_pt : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • ((2 : ℝ) • c - v) =
        c + (1 / 2 : ℝ) • (u - v) := by
      rw [smul_sub, smul_sub, smul_smul, one_div_mul_cancel two_ne_zero, one_smul]; abel
    rwa [← heq_pt]
/-- **Isodiametric ball rigidity under Brunn–Minkowski translate equality (`-K = {a} + K`)**. -/
theorem closedConvexHull_eq_closedBall_and_ae_eq_ball_of_neg_eq_add [Nontrivial E]
    {a : E} {s : Set E} (hs_ne : s.Nonempty) (hs : Bornology.IsBounded s)
    (hs_meas : NullMeasurableSet s volume) (hneg : -closedConvexHull s = {a} + closedConvexHull s)
    (heq : volume s = volume (Metric.ball (0 : E) (Metric.diam s / 2))) :
    closedConvexHull s = Metric.closedBall (-((1 / 2 : ℝ) • a)) (Metric.diam s / 2) ∧
      closure s = Metric.closedBall (-((1 / 2 : ℝ) • a)) (Metric.diam s / 2) ∧
      (s =ᵐ[volume] Metric.ball (-((1 / 2 : ℝ) • a)) (Metric.diam s / 2)) := by
  have heq_cb : volume s = volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) := by
    rwa [Measure.addHaar_closedBall_eq_addHaar_ball]
  have hsub := (subset_closedBall_and_closedConvexHull_eq_translate_differenceBody_of_neg_eq_add
    hs hneg).1
  obtain ⟨hcl, hcch⟩ :=
    closure_and_closedConvexHull_eq_closedBall_of_subset_closedBall hs_ne hsub heq_cb
  have hae_cch := (ae_eq_closedConvexHull_of_isodiametric_eq hs hs_meas heq_cb).2
  rw [hcch] at hae_cch
  exact ⟨hcch, hcl, hae_cch.trans (closedBall_ae_eq_ball _ _)⟩
/-- **Closed convex body isodiametric rigidity** (`K = Metric.closedBall c (Metric.diam K / 2)`). -/
theorem eq_closedBall_of_isClosed_of_convex_of_neg_eq_add {a : E} {K : Set E}
    (hK_ne : K.Nonempty) (hK_bdd : Bornology.IsBounded K) (hK_closed : IsClosed K)
    (hK_conv : Convex ℝ K) (hneg : -K = {a} + K)
    (heq : volume K = volume (Metric.closedBall (0 : E) (Metric.diam K / 2))) :
    K = Metric.closedBall (-((1 / 2 : ℝ) • a)) (Metric.diam K / 2) := by
  have hcch : closedConvexHull K = K := closedConvexHull_eq_self hK_conv hK_closed
  have hsub := (subset_closedBall_and_closedConvexHull_eq_translate_differenceBody_of_neg_eq_add
    hK_bdd (hcch.symm ▸ hneg)).1
  simpa [hcch] using
    (closure_and_closedConvexHull_eq_closedBall_of_subset_closedBall hK_ne hsub heq).2
/-- **Unconditional 1D isodiametric ball rigidity on `ℝ`**. -/
theorem closedConvexHull_eq_closedBall_and_ae_eq_ball_of_isodiametric_eq_real
    {s : Set ℝ} (hs_ne : s.Nonempty) (hs : Bornology.IsBounded s)
    (hs_meas : NullMeasurableSet s volume)
    (heq : volume s = volume (Metric.closedBall (0 : ℝ) (Metric.diam s / 2))) :
    ∃ c : ℝ, closedConvexHull s = Metric.closedBall c (Metric.diam s / 2) ∧
      closure s = Metric.closedBall c (Metric.diam s / 2) ∧
      (s =ᵐ[volume] Metric.ball c (Metric.diam s / 2)) := by
  set u := sInf (closedConvexHull s); set v := sSup (closedConvexHull s)
  have hK_Icc : closedConvexHull s = Icc u v :=
    (convex_closedConvexHull s).eq_Icc_of_isCompact (closedConvexHull_nonempty hs_ne)
      (isCompact_closedConvexHull hs)
  set a : ℝ := -(u + v)
  have hneg : -closedConvexHull s = {a} + closedConvexHull s := by
    rw [hK_Icc]; ext x; simp only [Set.mem_neg, Set.singleton_add, Set.mem_image, Set.mem_Icc]
    refine ⟨fun ⟨h1, h2⟩ ↦ ⟨x - a, ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩, by ring⟩, ?_⟩
    rintro ⟨y, ⟨h1, h2⟩, hyx⟩; dsimp [a] at hyx; exact ⟨by linarith, by linarith⟩
  have heq_ball : volume s = volume (Metric.ball (0 : ℝ) (Metric.diam s / 2)) := by
    rwa [← Measure.addHaar_closedBall_eq_addHaar_ball]
  exact ⟨-((1 / 2 : ℝ) * a),
    closedConvexHull_eq_closedBall_and_ae_eq_ball_of_neg_eq_add hs_ne hs hs_meas hneg heq_ball⟩
/-- If `volume (ball c r \ s) = 0`, `closedBall c r ⊆ closure s` and `2 * r ≤ Metric.diam s`. -/
theorem closedBall_subset_closure_and_two_mul_le_diam_of_measure_ball_diff_eq_zero
    [Nontrivial E] {c : E} {r : ℝ} (hr : 0 < r) {s : Set E}
    (hdiff : volume (Metric.ball c r \ s) = 0) :
    Metric.closedBall c r ⊆ closure s ∧ (Bornology.IsBounded s → 2 * r ≤ Metric.diam s) := by
  have hcb_sub : Metric.closedBall c r ⊆ closure s := by
    rw [← closure_ball c hr.ne']
    exact closure_minimal (isOpen_ball.subset_closure_of_measure_diff_eq_zero hdiff)
      isClosed_closure
  refine ⟨hcb_sub, fun hs ↦ ?_⟩
  rw [← Metric.diam_closedBall_eq c hr.le, ← Metric.diam_closure (s := s)]
  exact Metric.diam_mono hcb_sub hs.closure
/-- **Converse of isodiametric rigidity under diameter bound `Metric.diam s ≤ 2 * r`**. -/
theorem diam_eq_two_mul_radius_and_isodiametric_eq_of_ae_eq_ball_of_diam_le
    [Nontrivial E] {c : E} {r : ℝ} (hr : 0 < r) {s : Set E} (hs : Bornology.IsBounded s)
    (hae : s =ᵐ[volume] Metric.ball c r) (hdiam : Metric.diam s ≤ 2 * r) :
    Metric.diam s = 2 * r ∧
      volume s = volume (Metric.ball (0 : E) (Metric.diam s / 2)) ∧
      volume s = volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) := by
  have hdiam_eq : Metric.diam s = 2 * r := le_antisymm hdiam
    ((closedBall_subset_closure_and_two_mul_le_diam_of_measure_ball_diff_eq_zero hr
      (ae_eq_set.1 hae.symm).1).2 hs)
  have hrad : Metric.diam s / 2 = r := by rw [hdiam_eq, mul_div_cancel_left₀ r two_ne_zero]
  have hvol_b : volume s = volume (Metric.ball (0 : E) (Metric.diam s / 2)) := by
    rw [measure_congr hae, hrad, Measure.addHaar_ball_center]
  exact ⟨hdiam_eq, hvol_b, hvol_b.trans (Measure.addHaar_closedBall_eq_addHaar_ball _ _ _).symm⟩
/-- **Null-modification diameter counterexample to the unrestricted converse**. -/
theorem ae_eq_ball_union_singleton_diam_gt_and_volume_lt {c e : E} (he : ‖e‖ = 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    let s : Set E := Metric.ball c r ∪ {c + R • e}
    (s =ᵐ[volume] Metric.ball c r) ∧ Bornology.IsBounded s ∧
      r + R ≤ Metric.diam s ∧ 2 * r < Metric.diam s ∧
      volume s < volume (Metric.ball (0 : E) (Metric.diam s / 2)) := by
  have : Nontrivial E := ⟨⟨e, 0, norm_ne_zero_iff.mp (by rw [he]; exact one_ne_zero)⟩⟩; intro s
  have hae : s =ᵐ[volume] Metric.ball c r :=
    union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 (measure_singleton (c + R • e)))
  have hbdd : Bornology.IsBounded s := Metric.isBounded_ball.union Bornology.isBounded_singleton
  have hpt₁ : c - r • e ∈ closure s := by
    have hmem : c - r • e ∈ Metric.closedBall c r := by
      simp [Metric.mem_closedBall, norm_smul, he, abs_of_pos hr]
    rw [← closure_ball c hr.ne'] at hmem; exact closure_mono Set.subset_union_left hmem
  have hpt₂ : c + R • e ∈ closure s := subset_closure (Set.mem_union_right _ (Set.mem_singleton _))
  have hd_ge : r + R ≤ Metric.diam s := by
    rw [← Metric.diam_closure]
    have hdist : dist (c + R • e) (c - r • e) = r + R := by
      rw [dist_eq_norm, show c + R • e - (c - r • e) = (r + R) • e by rw [add_smul]; abel,
        norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)]
    rw [← hdist]; exact Metric.dist_le_diam_of_mem hbdd.closure hpt₂ hpt₁
  have hd_gt : 2 * r < Metric.diam s := by linarith
  refine ⟨hae, hbdd, hd_ge, hd_gt, ?_⟩
  rw [measure_congr hae, Measure.addHaar_ball_center volume c r]
  have hsub : Metric.closedBall (0 : E) r ⊆ Metric.ball (0 : E) (Metric.diam s / 2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hmid_pos : 0 < (r + Metric.diam s / 2) / 2 := by linarith
  have hopen_ne :
      (Metric.ball (0 : E) (Metric.diam s / 2) \ Metric.closedBall (0 : E) r).Nonempty :=
    ⟨((r + Metric.diam s / 2) / 2) • e, by
      simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right, norm_smul,
        he, mul_one, Real.norm_of_nonneg hmid_pos.le, not_le]
      constructor <;> linarith⟩
  have hpos_diff : 0 < volume (Metric.ball (0 : E) (Metric.diam s / 2) \
      Metric.closedBall (0 : E) r) :=
    (isOpen_ball.sdiff Metric.isClosed_closedBall).measure_pos volume hopen_ne
  rw [← Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : E) r]
  have htop : volume (Metric.closedBall (0 : E) r) ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : E) r).measure_lt_top.ne
  rw [measure_sdiff hsub Metric.isClosed_closedBall.nullMeasurableSet htop, tsub_pos_iff_lt]
    at hpos_diff
  exact hpos_diff
/-- Existence form of the null-modification diameter counterexample to the unrestricted converse. -/
theorem exists_ae_eq_ball_diam_gt_and_volume_lt [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    ∃ s : Set E, Bornology.IsBounded s ∧ (s =ᵐ[volume] Metric.ball c r) ∧
      2 * r < Metric.diam s ∧
      volume s < volume (Metric.ball (0 : E) (Metric.diam s / 2)) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E); have he : ‖‖v‖⁻¹ • v‖ = 1 := norm_smul_inv_norm hv
  have h := ae_eq_ball_union_singleton_diam_gt_and_volume_lt (c := c) he hr (lt_add_one r)
  exact ⟨Metric.ball c r ∪ {c + (r + 1) • (‖v‖⁻¹ • v)}, h.2.1, h.1, h.2.2.2.1, h.2.2.2.2⟩
end IsodiametricRigidityAndConverse
end TauCeti
