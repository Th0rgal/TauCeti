/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
public import TauCeti.Analysis.Fourier.RectifiableArea
public import TauCeti.MeasureTheory.Measure.FrontierIsoperimetry
public import TauCeti.MeasureTheory.Measure.MinkowskiContent

import all TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import all TauCeti.Analysis.Fourier.RectifiableArea
import all TauCeti.MeasureTheory.Measure.FrontierIsoperimetry
import all TauCeti.MeasureTheory.Measure.MinkowskiContent

/-!
# Planar Jordan Curve Isoperimetric Inequality, Circle Rigidity, and Frontier Corollaries

This file completes Milestone I6 (`Isoperimetry/README.md` and `Isoperimetry/Suggested.lean`):
1. **Exact `n`-th power Minkowski-content and topological-frontier isoperimetric theorems**:
   `TauCeti.isoperimetricBound_pow_finrank`, `TauCeti.isoperimetric_lowerMinkowskiContent`,
   `TauCeti.isoperimetric_frontier_of_measurableSet`, and `TauCeti.isoperimetric_frontier`.
2. **Unconditional topology, regular-openness, and measure of `filledHull C \ C`** for any Jordan
   curve `C ⊆ ℂ`: `TauCeti.not_isPreconnected_compl_of_isJordanCurve`,
   `TauCeti.isClosed_filledHull`, `TauCeti.isOpen_filledHull_diff`, `TauCeti.interior_filledHull`,
   `TauCeti.nonempty_filledHull_diff`, `TauCeti.closure_filledHull_diff`,
   `TauCeti.frontier_filledHull_diff`, `TauCeti.isRegularOpen_filledHull_diff`, and area/length
   positivity and finiteness.
3. **Circle formulas, parameterized simple closed curve equivalence, and Jordan isoperimetry**:
   `TauCeti.isJordanCurve_and_hausdorffMeasure_lt_top_iff`, `TauCeti.jordan_isoperimetric`,
   `TauCeti.jordan_isoperimetric_eq_iff`, `TauCeti.simple_closed_rectifiable_isoperimetric`,
   `TauCeti.simple_closed_rectifiable_isoperimetric_eq_iff`, their signed-area specializations, and
   `TauCeti.cantorCircleCurveComplex_isoperimetric_package`.
-/

public section

open Filter Function MeasureTheory MeasureTheory.Measure Metric OnePoint Pointwise Set
  TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology
open TauCeti.MeasureTheory

namespace TauCeti

/-! ### Section 1: `n`-th power Minkowski-content and topological-frontier theorems -/

section PowerAndFrontierIsoperimetry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **Exact `n`-th power identity for `isoperimetricBound`**. -/
theorem isoperimetricBound_pow_finrank [Nontrivial E] (s : Set E) :
    isoperimetricBound s ^ Module.finrank ℝ E =
      (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * volume (Metric.ball (0 : E) 1) *
        volume s ^ (Module.finrank ℝ E - 1) := by
  set n := Module.finrank ℝ E
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
  rw [isoperimetricBound, mul_pow, mul_pow,
    ← ENNReal.rpow_natCast (volume (Metric.ball (0 : E) 1) ^ _), ← ENNReal.rpow_mul,
    one_div_mul_cancel hn_pos.ne', ENNReal.rpow_one, ← ENNReal.rpow_natCast (volume s ^ _),
    ← ENNReal.rpow_mul, div_mul_cancel₀ _ hn_pos.ne', ← Nat.cast_one, ← Nat.cast_sub hn1,
    ENNReal.rpow_natCast]
/-- Equivalence between `isoperimetricBound s ≤ X` and its `n`-th power form. -/
theorem isoperimetricBound_le_iff_pow_finrank_le [Nontrivial E] {s : Set E} {X : ℝ≥0∞} :
    isoperimetricBound s ≤ X ↔
      (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * volume (Metric.ball (0 : E) 1) *
        volume s ^ (Module.finrank ℝ E - 1) ≤ X ^ Module.finrank ℝ E := by
  rw [← isoperimetricBound_pow_finrank]
  set n := Module.finrank ℝ E
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨fun h ↦ pow_le_pow_left' h n, fun h ↦ ?_⟩
  have h1 := ENNReal.rpow_le_rpow h (by positivity : 0 ≤ 1 / (n : ℝ))
  rwa [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hn_pos.ne',
    ENNReal.rpow_one, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    mul_one_div_cancel hn_pos.ne', ENNReal.rpow_one] at h1
/-- Equivalence between `isoperimetricBound s = X` and its `n`-th power form. -/
theorem isoperimetricBound_eq_iff_pow_finrank_eq [Nontrivial E] {s : Set E} {X : ℝ≥0∞} :
    isoperimetricBound s = X ↔
      (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * volume (Metric.ball (0 : E) 1) *
        volume s ^ (Module.finrank ℝ E - 1) = X ^ Module.finrank ℝ E := by
  rw [← isoperimetricBound_pow_finrank]
  set n := Module.finrank ℝ E
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
  have h1 := congrArg (fun x : ℝ≥0∞ ↦ x ^ (1 / (n : ℝ))) h
  rwa [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hn_pos.ne',
    ENNReal.rpow_one, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    mul_one_div_cancel hn_pos.ne', ENNReal.rpow_one] at h1
/-- **Unconditional `n`-th power lower Minkowski-content isoperimetric inequality**. -/
theorem isoperimetric_lowerMinkowskiContent {n : ℕ} (hn : 2 ≤ n)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume) (hvol : volume E < ⊤) :
    (n : ℝ≥0∞) ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        volume E ^ (n - 1) ≤ (lowerMinkowskiContent volume E) ^ n := by
  have : NeZero n := ⟨by omega⟩; rcases E.eq_empty_or_nonempty with rfl | hne
  · have hn1 : n - 1 ≠ 0 := by omega
    simp [zero_pow hn1]
  · simpa [finrank_euclideanSpace_fin] using lowerMinkowskiContent_pow_finrank_ge hne hE hvol.ne
/-- Specialization of `TauCeti.isoperimetric_lowerMinkowskiContent` to Borel-measurable sets. -/
theorem isoperimetric_lowerMinkowskiContent_of_measurableSet {n : ℕ} (hn : 2 ≤ n)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : MeasurableSet E) (hvol : volume E < ⊤) :
    (n : ℝ≥0∞) ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        volume E ^ (n - 1) ≤ (lowerMinkowskiContent volume E) ^ n :=
  isoperimetric_lowerMinkowskiContent hn hE.nullMeasurableSet hvol
/-- Normalized Euclidean Hausdorff `(n - 1)`-measure topological-frontier isoperimetric bound. -/
theorem isoperimetricBound_le_euclideanHausdorffMeasure_frontier [Nontrivial E] (s : Set E)
    (hiso : volume (frontier s) = 0 → NullMeasurableSet s volume →
      isoperimetricBound (interior s) ≤ perimeter volume (interior s))
    (hperim : volume (frontier s) = 0 → NullMeasurableSet s volume →
      perimeter volume s ≤ μHE[Module.finrank ℝ E - 1] (frontier s)) :
    isoperimetricBound s ≤ μHE[Module.finrank ℝ E - 1] (frontier s) := by
  by_cases htop : μHE[Module.finrank ℝ E - 1] (frontier s) = ⊤
  · rw [htop]; exact le_top
  · have hfront : TauCeti.euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) < ⊤ :=
      (TauCeti.MeasureTheory.euclideanHausdorffMeasure_lt_top_iff _ _).mp (lt_top_iff_ne_top.2 htop)
    obtain ⟨h0, hmeas, _, _, hbound_i, _, hperim_i, _⟩ :=
      isoperimetricBound_and_perimeter_interior_of_hausdorffMeasure_frontier_lt_top hfront
    calc isoperimetricBound s = isoperimetricBound (interior s) := hbound_i.symm
      _ ≤ perimeter volume (interior s) := hiso h0 hmeas
      _ = perimeter volume s := hperim_i
      _ ≤ μHE[Module.finrank ℝ E - 1] (frontier s) := hperim h0 hmeas
/-- Direct `n`-th power deduction of the topological-frontier isoperimetric inequality from `i. -/
theorem isoperimetric_frontier_of_isoperimetricBound_le {n : ℕ} (hn : 2 ≤ n)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hle : isoperimetricBound E ≤ μHE[n - 1] (frontier E)) :
    (n : ℝ≥0∞) ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        volume E ^ (n - 1) ≤ (μHE[n - 1] (frontier E)) ^ n := by
  have : NeZero n := ⟨by omega⟩
  have hpow := pow_le_pow_left' hle (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
  rwa [isoperimetricBound_pow_finrank, finrank_euclideanSpace_fin] at hpow
/-- **Borel-measurable `n`-th power topological-frontier isoperimetric theorem**. -/
theorem isoperimetric_frontier_of_measurableSet {n : ℕ} (hn : 2 ≤ n)
    (E : Set (EuclideanSpace ℝ (Fin n))) (_hE : MeasurableSet E) (hvol : volume E < ⊤)
    (hiso : volume (frontier E) = 0 → NullMeasurableSet E volume → volume (interior E) < ⊤ →
      isoperimetricBound (interior E) ≤ perimeter volume (interior E))
    (hperim : volume (frontier E) = 0 → NullMeasurableSet E volume → volume E < ⊤ →
      perimeter volume E ≤ μHE[n - 1] (frontier E)) :
    (n : ℝ≥0∞) ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        volume E ^ (n - 1) ≤ (μHE[n - 1] (frontier E)) ^ n := by
  have : NeZero n := ⟨by omega⟩
  refine isoperimetric_frontier_of_isoperimetricBound_le hn E ?_
  simpa [finrank_euclideanSpace_fin] using
    isoperimetricBound_le_euclideanHausdorffMeasure_frontier E
      (fun h0 hmeas ↦ hiso h0 hmeas ((measure_mono interior_subset).trans_lt hvol))
      (fun h0 hmeas ↦ by simpa [finrank_euclideanSpace_fin] using hperim h0 hmeas hvol)
/-- **Topological-frontier isoperimetric theorem without measurability hypotheses**. -/
theorem isoperimetric_frontier {n : ℕ} (hn : 2 ≤ n)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hvol : volume E < ⊤)
    (hiso : volume (frontier E) = 0 → NullMeasurableSet E volume → volume (interior E) < ⊤ →
      isoperimetricBound (interior E) ≤ perimeter volume (interior E))
    (hperim : volume (frontier E) = 0 → NullMeasurableSet E volume → volume E < ⊤ →
      perimeter volume E ≤ μHE[n - 1] (frontier E)) :
    (n : ℝ≥0∞) ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        volume E ^ (n - 1) ≤ (μHE[n - 1] (frontier E)) ^ n := by
  have : NeZero n := ⟨by omega⟩
  refine isoperimetric_frontier_of_isoperimetricBound_le hn E ?_
  simpa [finrank_euclideanSpace_fin] using
    isoperimetricBound_le_euclideanHausdorffMeasure_frontier E
      (fun h0 hmeas ↦ hiso h0 hmeas ((measure_mono interior_subset).trans_lt hvol))
      (fun h0 hmeas ↦ by simpa [finrank_euclideanSpace_fin] using hperim h0 hmeas hvol)

end PowerAndFrontierIsoperimetry

/-! ### Section 2: Unconditional topology, regular-openness, and measure of `filledHull C \ C` -/

section JordanInsideTopology

/-- **A Jordan curve in `ℂ` disconnects the plane**. -/
theorem not_isPreconnected_compl_of_isJordanCurve {C : Set ℂ} (hC : IsJordanCurve C) :
    ¬ IsPreconnected Cᶜ := by
  intro hconn
  obtain ⟨e⟩ := isJordanCurve_iff.mp hC
  let eS2 : OnePoint ℂ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
  let f : sphere (0 : ℂ) 1 → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun u ↦ eS2 ((jordanParam e (Circle.homeomorphSphere.symm u) : ℂ) : OnePoint ℂ)
  have hf_cont : Continuous f := eS2.continuous.comp (OnePoint.continuous_coe.comp
    ((continuous_jordanParam e).comp Circle.homeomorphSphere.symm.continuous))
  have hf_inj : Function.Injective f := eS2.injective.comp (OnePoint.coe_injective.comp
    ((jordanParam_injective e).comp Circle.homeomorphSphere.symm.injective))
  have hrange_C : range (jordanParam e ∘ Circle.homeomorphSphere.symm) = C := by
    rw [Circle.homeomorphSphere.symm.surjective.range_comp, range_jordanParam]
  have hrange_f : range f = eS2 '' (((↑) : ℂ → OnePoint ℂ) '' C) := by
    change range (eS2 ∘ ((↑) : ℂ → OnePoint ℂ) ∘ (jordanParam e ∘ Circle.homeomorphSphere.symm)) = _
    rw [range_comp, range_comp, hrange_C]
  have hinfty : (∞ : OnePoint ℂ) ∈ closure (((↑) : ℂ → OnePoint ℂ) '' Cᶜ) := by
    have huniv : closure (((↑) : ℂ → OnePoint ℂ) '' C) ∪
        closure (((↑) : ℂ → OnePoint ℂ) '' Cᶜ) = univ := by
      rw [← closure_union, ← image_union, union_compl_self, image_univ,
        OnePoint.denseRange_coe.closure_eq]
    have hcl : closure (((↑) : ℂ → OnePoint ℂ) '' C) = ((↑) : ℂ → OnePoint ℂ) '' C :=
      (hC.isCompact.image OnePoint.continuous_coe).isClosed.closure_eq
    have hmem : (∞ : OnePoint ℂ) ∈ ((↑) : ℂ → OnePoint ℂ) '' C ∪
        closure (((↑) : ℂ → OnePoint ℂ) '' Cᶜ) := by rw [← hcl, huniv]; exact mem_univ _
    exact hmem.resolve_left OnePoint.infty_notMem_image_coe
  have hpre_onePoint : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' C)ᶜ := by
    rw [OnePoint.compl_image_coe]
    exact (hconn.image _ OnePoint.continuous_coe.continuousOn).subset_closure
      subset_union_left (union_subset subset_closure (singleton_subset_iff.2 hinfty))
  have hpre_range : IsPreconnected (range f)ᶜ := by
    rw [hrange_f, ← Homeomorph.image_compl]
    exact hpre_onePoint.image _ eS2.continuous.continuousOn
  have hclosed : IsClosed (range f) := by simpa using (isCompact_univ.image hf_cont).isClosed
  have := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2))
    (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  have := hclosed.isOpen_compl.locallyPathConnectedSpace
  have := isPreconnected_iff_preconnectedSpace.1 hpre_range
  have hcard := natCard_zerothHomotopy_sphere_compl_range_eq_two
    (by simp [Complex.finrank_real_complex] :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = Module.finrank ℝ ℂ + 1) hf_cont hf_inj
  have hle : Nat.card (ZerothHomotopy ↥(range f)ᶜ) ≤ 1 := by
    rw [← Nat.card_congr connectedComponentsEquivZerothHomotopy]
    simpa using Nat.card_le_card_of_injective
      (f := fun _ : ConnectedComponents ↥(range f)ᶜ ↦ ()) (fun _ _ _ ↦ Subsingleton.elim _ _)
  omega
/-- Every Jordan curve `C ⊆ ℂ` has a point outside its filled hull. -/
theorem exists_notMem_filledHull {C : Set ℂ} (hC : IsJordanCurve C) :
    ∃ y : ℂ, y ∉ filledHull C := by
  by_contra! hcon
  exact NormedSpace.unbounded_univ ℝ ℂ
    ((isBounded_filledHull.mpr hC.isCompact.isBounded).subset fun z _ ↦ hcon z)
/-- The exterior `(filledHull C)ᶜ` of a Jordan curve `C ⊆ ℂ` is the single unbounded connected. -/
theorem compl_filledHull_eq_connectedComponentIn {C : Set ℂ} (hC : IsJordanCurve C)
    {y : ℂ} (hy : y ∉ filledHull C) : (filledHull C)ᶜ = connectedComponentIn Cᶜ y := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two
  have hy' : ¬Bornology.IsBounded (connectedComponentIn Cᶜ y) := by rwa [mem_filledHull_iff] at hy
  ext z; simp only [mem_compl_iff, mem_filledHull_iff]
  refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
  · have hzC : z ∈ Cᶜ := fun hzC ↦ hz (mem_filledHull_iff.mp (subset_filledHull hzC))
    rw [← connectedComponentIn_compl_eq_of_unbounded_component hrank hC.isCompact.isBounded hz hy']
    exact mem_connectedComponentIn hzC
  · rwa [← connectedComponentIn_eq hz]
/-- The exterior `(filledHull C)ᶜ` of a Jordan curve `C ⊆ ℂ` is open. -/
theorem isOpen_compl_filledHull {C : Set ℂ} (hC : IsJordanCurve C) : IsOpen (filledHull C)ᶜ := by
  obtain ⟨y, hy⟩ := exists_notMem_filledHull hC
  rw [compl_filledHull_eq_connectedComponentIn hC hy]
  exact hC.isClosed.isOpen_compl.connectedComponentIn
/-- **The filled hull of a Jordan curve `C ⊆ ℂ` is closed.** -/
theorem isClosed_filledHull {C : Set ℂ} (hC : IsJordanCurve C) : IsClosed (filledHull C) :=
  isOpen_compl_iff.mp (isOpen_compl_filledHull hC)
/-- **The filled hull of a Jordan curve `C ⊆ ℂ` is compact.** -/
theorem isCompact_filledHull {C : Set ℂ} (hC : IsJordanCurve C) : IsCompact (filledHull C) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_filledHull hC)
    (isBounded_filledHull.mpr hC.isCompact.isBounded)
/-- **The Jordan inside `filledHull C \ C` is open.** -/
theorem isOpen_filledHull_diff {C : Set ℂ} (hC : IsJordanCurve C) : IsOpen (filledHull C \ C) := by
  have heq : filledHull C \ C = Cᶜ ∩ ((filledHull C)ᶜ)ᶜ := by ext z; simp [and_comm]
  rw [heq, compl_compl]
  exact isOpen_iff_mem_nhds.mpr fun x ⟨hxC, hxH⟩ ↦ Filter.mem_of_superset
      (hC.isClosed.isOpen_compl.connectedComponentIn.mem_nhds (mem_connectedComponentIn hxC))
      fun z hz ↦ ⟨connectedComponentIn_subset Cᶜ x hz,
        mem_filledHull_iff.mpr
          (by rw [← connectedComponentIn_eq hz]; exact mem_filledHull_iff.mp hxH)⟩
/-- **The Jordan inside `filledHull C \ C` is bounded.** -/
theorem isBounded_filledHull_diff {C : Set ℂ} (hC : IsJordanCurve C) :
    Bornology.IsBounded (filledHull C \ C) :=
  (isBounded_filledHull.mpr hC.isCompact.isBounded).subset sdiff_subset
/-- The Jordan inside `filledHull C \ C` is Borel-measurable. -/
theorem measurableSet_filledHull_diff {C : Set ℂ} (hC : IsJordanCurve C) :
    MeasurableSet (filledHull C \ C) := (isOpen_filledHull_diff hC).measurableSet
/-- The Jordan inside `filledHull C \ C` is Lebesgue null-measurable. -/
theorem nullMeasurableSet_filledHull_diff {C : Set ℂ} (hC : IsJordanCurve C) :
    NullMeasurableSet (filledHull C \ C) volume :=
  (measurableSet_filledHull_diff hC).nullMeasurableSet
/-- **The interior of `filledHull C` is `filledHull C \ C`.** -/
theorem interior_filledHull {C : Set ℂ} (hC : IsJordanCurve C) :
    interior (filledHull C) = filledHull C \ C := by
  refine Subset.antisymm (fun z hz ↦ ⟨interior_subset hz, ?_⟩)
    (interior_maximal sdiff_subset (isOpen_filledHull_diff hC))
  exact disjoint_left.mp
    (hC.disjoint_of_isOpen_of_subset_filledHull isOpen_interior interior_subset) hz
/-- **Unconditional nonemptiness of the Jordan inside `filledHull C \ C`.** -/
theorem nonempty_filledHull_diff {C : Set ℂ} (hC : IsJordanCurve C) :
    (filledHull C \ C).Nonempty := by
  by_contra! hemp
  obtain ⟨y, hy⟩ := exists_notMem_filledHull hC
  have hsub : Cᶜ ⊆ (filledHull C)ᶜ := fun z hzC hzH ↦ hemp.subset ⟨hzH, hzC⟩
  have heq : Cᶜ = connectedComponentIn Cᶜ y :=
    Subset.antisymm (hsub.trans (compl_filledHull_eq_connectedComponentIn hC hy).subset)
      (connectedComponentIn_subset Cᶜ y)
  exact not_isPreconnected_compl_of_isJordanCurve hC (heq ▸ isPreconnected_connectedComponentIn)
/-- **The closure of the Jordan inside `filledHull C \ C` is `filledHull C`.** -/
theorem closure_filledHull_diff {C : Set ℂ} (hC : IsJordanCurve C) :
    closure (filledHull C \ C) = filledHull C := by
  refine Subset.antisymm (closure_minimal sdiff_subset (isClosed_filledHull hC)) fun z hz ↦ ?_
  by_cases hzC : z ∈ C
  · obtain ⟨x, hxH, hxC⟩ := nonempty_filledHull_diff hC
    obtain ⟨y, hy⟩ := exists_notMem_filledHull hC
    have hyC : y ∉ C := fun hyC ↦ hy (subset_filledHull hyC)
    have hxH' := mem_filledHull_iff.mp hxH
    have hxy : y ∉ connectedComponentIn Cᶜ x := fun h ↦
      hy (mem_filledHull_iff.mpr (by rw [← connectedComponentIn_eq h]; exact hxH'))
    have hsub : connectedComponentIn Cᶜ x ⊆ filledHull C \ C := fun w hw ↦
      ⟨mem_filledHull_iff.mpr (by rw [← connectedComponentIn_eq hw]; exact hxH'),
        connectedComponentIn_subset Cᶜ x hw⟩
    exact closure_mono hsub (hC.subset_closure_connectedComponentIn hxC hyC hxy hzC)
  · exact subset_closure ⟨hz, hzC⟩
/-- **The frontier of the Jordan inside `filledHull C \ C` is `C`.** -/
theorem frontier_filledHull_diff {C : Set ℂ} (hC : IsJordanCurve C) :
    frontier (filledHull C \ C) = C := by
  rw [frontier, closure_filledHull_diff hC, (isOpen_filledHull_diff hC).interior_eq]
  ext z; simp only [Set.mem_sdiff, not_and, not_not]
  exact ⟨fun ⟨hzH, h⟩ ↦ h hzH, fun hzC ↦ ⟨subset_filledHull hzC, fun _ ↦ hzC⟩⟩
/-- **The Jordan inside `filledHull C \ C` is a regular open set**. -/
theorem isRegularOpen_filledHull_diff {C : Set ℂ} (hC : IsJordanCurve C) :
    IsRegularOpen (filledHull C \ C) :=
  ⟨isOpen_filledHull_diff hC, by rw [closure_filledHull_diff hC, interior_filledHull hC]⟩
/-- **Area positivity of the Jordan inside**: `0 < volume (filledHull C \ C)`. -/
theorem volume_filledHull_diff_pos {C : Set ℂ} (hC : IsJordanCurve C) :
    0 < volume (filledHull C \ C) :=
  (isOpen_filledHull_diff hC).measure_pos volume (nonempty_filledHull_diff hC)
/-- **Area finiteness of the Jordan inside**: `volume (filledHull C \ C) < ⊤`. -/
theorem volume_filledHull_diff_lt_top {C : Set ℂ} (hC : IsJordanCurve C) :
    volume (filledHull C \ C) < ⊤ := (isBounded_filledHull_diff hC).measure_lt_top
/-- Real-valued area positivity of the Jordan inside: `0 < (volume (filledHull C \ C)).toReal`. -/
theorem toReal_volume_filledHull_diff_pos {C : Set ℂ} (hC : IsJordanCurve C) :
    0 < (volume (filledHull C \ C)).toReal :=
  ENNReal.toReal_pos (volume_filledHull_diff_pos hC).ne' (volume_filledHull_diff_lt_top hC).ne
/-- **Length positivity of any Jordan curve**: `0 < μHE[1] C`. -/
theorem hausdorffMeasure_one_pos_of_isJordanCurve {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {C : Set X} (hC : IsJordanCurve C) : 0 < μHE[1] C := by
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hC.not_subsingleton
  exact (edist_pos.mpr hab).trans_le
    (hC.isConnected.isPreconnected.edist_le_euclideanHausdorffMeasure ha hb)
/-- Real-valued length positivity of a rectifiable Jordan curve: `0 < (μHE[1] C).toReal`. -/
theorem toReal_hausdorffMeasure_one_pos_of_isJordanCurve {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {C : Set X} (hC : IsJordanCurve C) (hrect : μHE[1] C < ⊤) :
    0 < (μHE[1] C).toReal :=
  ENNReal.toReal_pos (hausdorffMeasure_one_pos_of_isJordanCurve hC).ne' hrect.ne

end JordanInsideTopology

/-! ### Section 3: Planar circle formulas and parameterized simple closed curve equivalence -/

section CircleAndParameterizedEquivalence

/-- Canonical linear isometry equivalence `ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def complexToEuclidean : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr
/-- The Jordan inside of a circle `Metric.sphere c r` (`0 ≤ r`) is `Metric.ball c r`. -/
theorem filledHull_sphere_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) {r : ℝ} (hr : 0 ≤ r) :
    filledHull (Metric.sphere c r) \ Metric.sphere c r = Metric.ball c r := by
  rw [filledHull_sphere c hr, closedBall_sdiff_sphere]
/-- Exact enclosed area of a circle `Metric.sphere (c : ℂ) r` (`0 ≤ r`). -/
theorem volume_filledHull_sphere_diff (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (filledHull (Metric.sphere c r) \ Metric.sphere c r) =
      ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [filledHull_sphere_diff c hr, Complex.volume_ball, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (sq_nonneg r), mul_comm]
/-- Real enclosed area of a circle `Metric.sphere (c : ℂ) r` (`0 ≤ r`). -/
theorem toReal_volume_filledHull_sphere_diff (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (filledHull (Metric.sphere c r) \ Metric.sphere c r)).toReal = Real.pi * r ^ 2 := by
  rw [volume_filledHull_sphere_diff c hr, ENNReal.toReal_ofReal (by positivity)]
/-- **One-dimensional Euclidean Hausdorff measure of a complex circle** (`0 ≤ r`). -/
theorem euclideanHausdorffMeasure_sphere_complex (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    μHE[1] (Metric.sphere c r) = ENNReal.ofReal (2 * Real.pi * r) := by
  rw [← complexToEuclidean.isometry.euclideanHausdorffMeasure_image (Metric.sphere c r)]
  change μHE[1] (complexToEuclidean.toIsometryEquiv '' Metric.sphere c r) = _
  rw [complexToEuclidean.toIsometryEquiv.image_sphere c r,
    euclideanHausdorffMeasure_sphere_two (complexToEuclidean.toIsometryEquiv c) hr]
/-- Real Hausdorff 1-measure of a complex circle (`0 ≤ r`). -/
theorem toReal_euclideanHausdorffMeasure_sphere_complex (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (μHE[1] (Metric.sphere c r)).toReal = 2 * Real.pi * r := by
  rw [euclideanHausdorffMeasure_sphere_complex c hr, ENNReal.toReal_ofReal (by positivity)]
/-- Exact squared `isoperimetricBound` in `ℂ`. -/
theorem isoperimetricBound_sq_complex (s : Set ℂ) :
    isoperimetricBound s ^ 2 = ENNReal.ofReal (4 * Real.pi) * volume s := by
  have h := isoperimetricBound_pow_finrank s
  rw [Complex.finrank_real_complex] at h
  rw [h, Complex.volume_ball]
  have h4 : ((2 : ℕ) : ℝ≥0∞) ^ 2 * (ENNReal.ofReal 1 ^ 2 * ↑NNReal.pi) =
      ENNReal.ofReal (4 * Real.pi) := by
    rw [ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ENNReal.ofReal_mul (by positivity)]
    norm_num
  rw [h4]; simp
/-- Exact perimeter of the Jordan inside of a circle `Metric.sphere (c : ℂ) r` (`0 < r`). -/
theorem perimeter_filledHull_sphere_diff_eq_hausdorffMeasure (c : ℂ) {r : ℝ} (hr : 0 < r) :
    perimeter volume (filledHull (Metric.sphere c r) \ Metric.sphere c r) =
      μHE[1] (Metric.sphere c r) := by
  rw [filledHull_sphere_diff c hr.le, perimeter_ball c hr, Complex.finrank_real_complex,
    Complex.volume_ball, euclideanHausdorffMeasure_sphere_complex c hr.le]
  have hr0 : 0 ≤ r := hr.le
  rw [← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (sq_nonneg r), ← ENNReal.ofReal_mul (by positivity)]
  congr 1; push_cast; field_simp
/-- **Unconditional `ℝ≥0∞` Jordan isoperimetric equality for a complex circle** (`0 ≤ r`). -/
theorem jordan_isoperimetric_sphere_ennreal (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (4 * Real.pi) * volume (filledHull (Metric.sphere c r) \ Metric.sphere c r) =
      (μHE[1] (Metric.sphere c r)) ^ 2 := by
  rw [volume_filledHull_sphere_diff c hr, euclideanHausdorffMeasure_sphere_complex c hr,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  congr 1; ring
/-- **Unconditional real Jordan isoperimetric equality for a complex circle** (`0 ≤ r`). -/
theorem jordan_isoperimetric_sphere_eq (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    4 * Real.pi * (volume (filledHull (Metric.sphere c r) \ Metric.sphere c r)).toReal =
      (μHE[1] (Metric.sphere c r)).toReal ^ 2 := by
  rw [toReal_volume_filledHull_sphere_diff c hr,
    toReal_euclideanHausdorffMeasure_sphere_complex c hr]
  ring
/-- For a closed curve `γ a = γ b` (`a < b`), the image on `Icc a b` equals that on `Ico a b`. -/
theorem image_Icc_eq_image_Ico_of_closed {X : Type*} {γ : ℝ → X} {a b : ℝ} (hab : a < b)
    (hclosed : γ a = γ b) : γ '' Icc a b = γ '' Ico a b := by
  rw [← Ico_insert_right hab.le, image_insert_eq, ← hclosed,
    insert_eq_of_mem (mem_image_of_mem γ (left_mem_Ico.mpr hab))]
/-- **The trace `γ '' Icc a b` of a continuous simple closed curve on `[a, b]`**. -/
theorem isJordanCurve_image_Icc {X : Type*} [TopologicalSpace X] [T2Space X] {γ : ℝ → X}
    {a b : ℝ} (hab : a < b) (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) : IsJordanCurve (γ '' Icc a b) := by
  let p : ℝ := b - a
  have hp : 0 < p := sub_pos.mpr hab
  have : Fact (0 < p) := ⟨hp⟩
  have hap : a + p = b := add_sub_cancel a b
  let δ : ℝ → X := fun t ↦ γ (a + t)
  have hδ_closed : δ 0 = δ p := by simp [δ, hap, hclosed]
  have hδ_cont : ContinuousOn δ (Icc 0 p) := hγ.comp (continuousOn_const.add continuousOn_id)
    fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcont_lift : Continuous (AddCircle.liftIco p 0 δ) :=
    AddCircle.liftIco_zero_continuous hδ_closed hδ_cont
  have hinj_lift : Function.Injective (AddCircle.liftIco p 0 δ) := by
    intro q₁ q₂ hq
    obtain ⟨s, hs, rfl⟩ := AddCircle.eq_coe_Ico q₁
    obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico q₂
    rw [AddCircle.liftIco_zero_coe_apply hs, AddCircle.liftIco_zero_coe_apply ht] at hq
    have hs' : a + s ∈ Ico a b := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have ht' : a + t ∈ Ico a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact congrArg ((↑) : ℝ → AddCircle p) (add_left_cancel (hinj hs' ht' hq))
  have huniv : IsJordanCurve (univ : Set (AddCircle p)) := isJordanCurve_iff.mpr
    ⟨(Homeomorph.Set.univ (AddCircle p)).trans (AddCircle.homeomorphCircle hp.ne')⟩
  have himg := huniv.image hcont_lift.continuousOn hinj_lift.injOn
  have hrange : AddCircle.liftIco p 0 δ '' univ = γ '' Icc a b := by
    rw [image_univ, image_Icc_eq_image_Ico_of_closed hab hclosed]
    ext x; simp only [mem_range, mem_image, mem_Ico]
    refine ⟨?_, fun ⟨t, ht, htx⟩ ↦ ⟨(t - a : ℝ), ?_⟩⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico q
      exact ⟨a + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        (AddCircle.liftIco_zero_coe_apply (f := δ) ht).symm⟩
    · have ht0 : t - a ∈ Ico 0 p := ⟨sub_nonneg.mpr ht.1, sub_lt_sub_right ht.2 a⟩
      rw [AddCircle.liftIco_zero_coe_apply ht0]; simpa [δ] using htx
  rwa [hrange] at himg
/-- **Every Jordan curve `C` admits a continuous simple closed parameterization on `[0, 1]`**. -/
theorem exists_simple_closed_param_of_isJordanCurve {X : Type*} [TopologicalSpace X]
    {C : Set X} (hC : IsJordanCurve C) :
    ∃ γ : ℝ → X, Continuous γ ∧ γ 0 = γ 1 ∧ InjOn γ (Ico 0 1) ∧ γ '' Icc 0 1 = C := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp hC
  let φ : ℝ → Circle := fun t ↦ AddCircle.homeomorphCircle one_ne_zero (t : AddCircle (1 : ℝ))
  refine ⟨fun t ↦ jordanParam e (φ t), ?_, ?_, ?_, ?_⟩
  · exact (continuous_jordanParam e).comp
      ((AddCircle.homeomorphCircle one_ne_zero).continuous.comp continuous_quotient_mk')
  · simp [φ, AddCircle.coe_period]
  · intro s hs t ht hst
    have hq : (s : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) :=
      (AddCircle.homeomorphCircle one_ne_zero).injective (jordanParam_injective e hst)
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
      (by simpa using hs) (by simpa using ht)).mp hq
  · rw [image_Icc_eq_image_Ico_of_closed zero_lt_one (by simp [φ, AddCircle.coe_period])]
    have hsurj : ((↑) : ℝ → AddCircle (1 : ℝ)) '' Ico 0 1 = univ := by
      ext q; simp only [mem_image, mem_Ico, mem_univ, iff_true]
      obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico q; exact ⟨t, ht, rfl⟩
    change (jordanParam e ∘ AddCircle.homeomorphCircle one_ne_zero ∘
      ((↑) : ℝ → AddCircle (1 : ℝ))) '' Ico 0 1 = C
    rw [image_comp, image_comp, hsurj, image_univ,
      (AddCircle.homeomorphCircle one_ne_zero).surjective.range_eq, image_univ, range_jordanParam]
/-- **Equivalence between rectifiable Jordan curves and simple closed rectifiable curves**. -/
theorem isJordanCurve_and_hausdorffMeasure_lt_top_iff {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {C : Set X} :
    (IsJordanCurve C ∧ μHE[1] C < ⊤) ↔
      ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ γ 0 = γ 1 ∧ InjOn γ (Ico 0 1) ∧
        BoundedVariationOn γ (Icc 0 1) ∧ γ '' Icc 0 1 = C := by
  refine ⟨fun ⟨hC, hrect⟩ ↦ ?_, ?_⟩
  · obtain ⟨γ, hcont, hclosed, hinj, himg⟩ := exists_simple_closed_param_of_isJordanCurve hC
    exact ⟨γ, hcont.continuousOn, hclosed, hinj,
      (boundedVariationOn_iff_euclideanHausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico
        hcont.continuousOn hinj).mpr (himg.symm ▸ hrect), himg⟩
  · rintro ⟨γ, hcont, hclosed, hinj, hbv, rfl⟩
    exact ⟨isJordanCurve_image_Icc zero_lt_one hcont hclosed hinj,
      (boundedVariationOn_iff_euclideanHausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico
        hcont hinj).mp hbv⟩
/-- **Unconditional equality attainment for every continuous rectifiable simple parametrizatio. -/
theorem simple_closed_rectifiable_sphere_eq {γ : ℝ → ℂ} {a b : ℝ} (_hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) (_hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (htrace : γ '' Icc a b = Metric.sphere c r) :
    BoundedVariationOn γ (Icc a b) ∧
      4 * Real.pi * (volume (filledHull (γ '' Icc a b) \ γ '' Icc a b)).toReal =
        (eVariationOn γ (Icc a b)).toReal ^ 2 := by
  have hlen : μHE[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) :=
    euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ hinj
  have hfin : μHE[1] (γ '' Icc a b) < ⊤ := by
    rw [htrace, euclideanHausdorffMeasure_sphere_complex c hr]; exact ENNReal.ofReal_lt_top
  refine ⟨(boundedVariationOn_iff_euclideanHausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico
    hγ hinj).mpr hfin, ?_⟩
  rw [← hlen, htrace, jordan_isoperimetric_sphere_eq c hr]

end CircleAndParameterizedEquivalence

/-! ### Section 4: Planar Jordan isoperimetric inequality, circle rigidity, and compatibility -/

section PlanarJordanIsoperimetry

/-- **Planar Jordan curve isoperimetric inequality in `ℝ≥0∞`** (via the finite-perimeter speci. -/
theorem jordan_isoperimetric_ennreal {C : Set ℂ} (_hC : IsJordanCurve C)
    (hiso : isoperimetricBound (filledHull C \ C) ≤ perimeter volume (filledHull C \ C))
    (hperim : perimeter volume (filledHull C \ C) ≤ μHE[1] C) :
    ENNReal.ofReal (4 * Real.pi) * volume (filledHull C \ C) ≤ (μHE[1] C) ^ 2 := by
  rw [← isoperimetricBound_sq_complex]; exact pow_le_pow_left' (hiso.trans hperim) 2
/-- **Geometric planar Jordan curve isoperimetric inequality**. -/
theorem jordan_isoperimetric {C : Set ℂ} (hC : IsJordanCurve C) (hrect : μHE[1] C < ⊤)
    (hiso : isoperimetricBound (filledHull C \ C) ≤ perimeter volume (filledHull C \ C))
    (hperim : perimeter volume (filledHull C \ C) ≤ μHE[1] C) :
    4 * Real.pi * (volume (filledHull C \ C)).toReal ≤ (μHE[1] C).toReal ^ 2 := by
  have hle := jordan_isoperimetric_ennreal hC hiso hperim
  have htop_r : (μHE[1] C) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hrect.ne
  have htop_l : ENNReal.ofReal (4 * Real.pi) * volume (filledHull C \ C) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_filledHull_diff_lt_top hC).ne
  have hreal := (ENNReal.toReal_le_toReal htop_l htop_r).mpr hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow] at hreal
/-- **Geometric planar Jordan curve circle rigidity**. -/
theorem jordan_isoperimetric_eq_iff {C : Set ℂ} (hC : IsJordanCurve C) (hrect : μHE[1] C < ⊤)
    (hiso : isoperimetricBound (filledHull C \ C) ≤ perimeter volume (filledHull C \ C))
    (hperim : perimeter volume (filledHull C \ C) ≤ μHE[1] C)
    (hrig : isoperimetricBound (filledHull C \ C) = perimeter volume (filledHull C \ C) →
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ (filledHull C \ C =ᵐ[volume] Metric.ball c r)) :
    4 * Real.pi * (volume (filledHull C \ C)).toReal = (μHE[1] C).toReal ^ 2 ↔
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ C = Metric.sphere c r := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · have htop_r : (μHE[1] C) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hrect.ne
    have htop_l : ENNReal.ofReal (4 * Real.pi) * volume (filledHull C \ C) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_filledHull_diff_lt_top hC).ne
    have heq_enn : isoperimetricBound (filledHull C \ C) ^ 2 = (μHE[1] C) ^ 2 := by
      rw [isoperimetricBound_sq_complex, ← ENNReal.toReal_eq_toReal_iff' htop_l htop_r,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow]
      exact heq
    have hbound_eq : isoperimetricBound (filledHull C \ C) = μHE[1] C := by
      rw [isoperimetricBound_eq_iff_pow_finrank_eq, ← isoperimetricBound_pow_finrank,
        Complex.finrank_real_complex]
      exact heq_enn
    obtain ⟨c, r, hr, hae⟩ := hrig (le_antisymm hiso (hperim.trans_eq hbound_eq.symm))
    obtain ⟨hfr_eq, _⟩ := frontier_eq_sphere_of_isRegularOpen_of_ae_eq_ball
      (isRegularOpen_filledHull_diff hC) hr.ne' hae
    exact ⟨c, r, hr, (frontier_filledHull_diff hC).symm.trans hfr_eq⟩
  · rintro ⟨c, r, hr, rfl⟩; exact jordan_isoperimetric_sphere_eq c hr.le
/-- **Parameterized simple closed rectifiable curve isoperimetric inequality**. -/
theorem simple_closed_rectifiable_isoperimetric {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hrect : BoundedVariationOn γ (Icc a b))
    (hiso : isoperimetricBound (filledHull (γ '' Icc a b) \ γ '' Icc a b) ≤
      perimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b))
    (hperim : perimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b) ≤ μHE[1] (γ '' Icc a b)) :
    4 * Real.pi * (volume (filledHull (γ '' Icc a b) \ γ '' Icc a b)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 := by
  have hC : IsJordanCurve (γ '' Icc a b) := isJordanCurve_image_Icc hab hγ hclosed hinj
  have hlen : μHE[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) :=
    euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ hinj
  have hfin : μHE[1] (γ '' Icc a b) < ⊤ :=
    (boundedVariationOn_iff_euclideanHausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico
      hγ hinj).mp hrect
  rw [← hlen]; exact jordan_isoperimetric hC hfin hiso hperim
/-- **Parameterized simple closed rectifiable curve circle rigidity**. -/
theorem simple_closed_rectifiable_isoperimetric_eq_iff {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hrect : BoundedVariationOn γ (Icc a b))
    (hiso : isoperimetricBound (filledHull (γ '' Icc a b) \ γ '' Icc a b) ≤
      perimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b))
    (hperim : perimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b) ≤ μHE[1] (γ '' Icc a b))
    (hrig : isoperimetricBound (filledHull (γ '' Icc a b) \ γ '' Icc a b) =
        perimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b) → ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
        (filledHull (γ '' Icc a b) \ γ '' Icc a b =ᵐ[volume] Metric.ball c r)) :
    4 * Real.pi * (volume (filledHull (γ '' Icc a b) \ γ '' Icc a b)).toReal =
        (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc a b = Metric.sphere c r := by
  have hC : IsJordanCurve (γ '' Icc a b) := isJordanCurve_image_Icc hab hγ hclosed hinj
  have hlen : μHE[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) :=
    euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ hinj
  have hfin : μHE[1] (γ '' Icc a b) < ⊤ :=
    (boundedVariationOn_iff_euclideanHausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico
      hγ hinj).mp hrect
  rw [← hlen]; exact jordan_isoperimetric_eq_iff hC hfin hiso hperim hrig

/-! ### Compatibility Bridge 2: AC / arclength signed-area specialization via Milestone I3 -/
/-- Total variation is invariant under post-composition with an isometry. -/
theorem eVariationOn_comp_isometry {α E F : Type*} [LinearOrder α] [EMetricSpace E]
    [EMetricSpace F] {Φ : E → F} (hΦ : Isometry Φ) (γ : α → E) (s : Set α) :
    eVariationOn (Φ ∘ γ) s = eVariationOn γ s := by
  simp only [eVariationOn, Function.comp_apply, hΦ.edist_eq]
/-- Bounded variation is preserved under post-composition with an isometry. -/
theorem boundedVariationOn_comp_isometry {α E F : Type*} [LinearOrder α] [EMetricSpace E]
    [EMetricSpace F] {Φ : E → F} (hΦ : Isometry Φ) {γ : α → E} {s : Set α}
    (hγ : BoundedVariationOn γ s) : BoundedVariationOn (Φ ∘ γ) s := by
  rwa [BoundedVariationOn, eVariationOn_comp_isometry hΦ]
/-- Geometric signed area of a rectifiable curve `γ. -/
noncomputable def rectifiableSignedAreaComplex (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  rectifiableSignedArea (complexToEuclidean ∘ γ) a b
/-- **Unconditional complex rectifiable curve isoperimetric inequality**. -/
theorem four_mul_pi_mul_abs_rectifiableSignedAreaComplex_le {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) :
    4 * Real.pi * |rectifiableSignedAreaComplex γ a b| ≤ (eVariationOn γ (Icc a b)).toReal ^ 2 := by
  have hvar : eVariationOn (complexToEuclidean ∘ γ) (Icc a b) = eVariationOn γ (Icc a b) :=
    eVariationOn_comp_isometry complexToEuclidean.isometry γ (Icc a b)
  rw [rectifiableSignedAreaComplex, ← hvar]
  exact four_mul_pi_mul_abs_rectifiableSignedArea_le hab
    (boundedVariationOn_comp_isometry complexToEuclidean.isometry hγ)
    (complexToEuclidean.continuous.comp_continuousOn hc) (congrArg complexToEuclidean hclosed)
/-- **Unconditional complex simple closed rectifiable curve Hausdorff-length inequality**. -/
theorem four_mul_pi_mul_abs_rectifiableSignedAreaComplex_le_hausdorff {γ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    4 * Real.pi * |rectifiableSignedAreaComplex γ a b| ≤ (μHE[1] (γ '' Icc a b)).toReal ^ 2 := by
  rw [euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hc hinj]
  exact four_mul_pi_mul_abs_rectifiableSignedAreaComplex_le hab hγ hc hclosed
/-- **Unconditional complex circle-trace rigidity for `rectifiableSignedAreaComplex`**. -/
theorem exists_sphere_trace_of_rectifiableSignedAreaComplex_eq_of_injOn_Ico {γ : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (heq : 4 * Real.pi * |rectifiableSignedAreaComplex γ a b| =
      (eVariationOn γ (Icc a b)).toReal ^ 2) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc a b = Metric.sphere c r := by
  have hvar : eVariationOn (complexToEuclidean ∘ γ) (Icc a b) = eVariationOn γ (Icc a b) :=
    eVariationOn_comp_isometry complexToEuclidean.isometry γ (Icc a b)
  have hinjE : InjOn (complexToEuclidean ∘ γ) (Ico a b) :=
    complexToEuclidean.injective.injOn.comp hinj (mapsTo_univ _ _)
  obtain ⟨cE, htraceE⟩ := exists_sphere_trace_of_rectifiableSignedArea_eq_of_injOn_Ico hab.le
    (boundedVariationOn_comp_isometry complexToEuclidean.isometry hγ)
    (complexToEuclidean.continuous.comp_continuousOn hc)
    (congrArg complexToEuclidean hclosed) hinjE (by rwa [hvar])
  have hC : IsJordanCurve (γ '' Icc a b) := isJordanCurve_image_Icc hab hc hclosed hinj
  have hlen : μHE[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) :=
    euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hc hinj
  have hfin : μHE[1] (γ '' Icc a b) < ⊤ :=
    (boundedVariationOn_iff_euclideanHausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico
      hc hinj).mp hγ
  have hL_pos : 0 < (eVariationOn γ (Icc a b)).toReal := by
    rw [← hlen]; exact toReal_hausdorffMeasure_one_pos_of_isJordanCurve hC hfin
  refine ⟨complexToEuclidean.symm cE, (eVariationOn γ (Icc a b)).toReal / (2 * Real.pi),
    div_pos hL_pos Real.two_pi_pos, ?_⟩
  rw [hvar] at htraceE
  have himg := congrArg (Set.image complexToEuclidean.symm) htraceE
  rw [Set.image_comp, ← Set.image_comp, LinearIsometryEquiv.symm_comp_self, Set.image_id] at himg
  exact himg.trans (complexToEuclidean.symm.toIsometryEquiv.image_sphere cE _)
/-- **Signed-area specialization of `simple_closed_rectifiable_isoperimetric`**. -/
theorem simple_closed_rectifiable_isoperimetric_of_signedArea {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b)
    (_hinj : InjOn γ (Ico a b)) (hrect : BoundedVariationOn γ (Icc a b))
    (harea : (volume (filledHull (γ '' Icc a b) \ γ '' Icc a b)).toReal ≤
      |rectifiableSignedAreaComplex γ a b|) :
    4 * Real.pi * (volume (filledHull (γ '' Icc a b) \ γ '' Icc a b)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 :=
  (mul_le_mul_of_nonneg_left harea (by positivity)).trans
    (four_mul_pi_mul_abs_rectifiableSignedAreaComplex_le hab.le hrect hγ hclosed)
/-- **Compatibility specialization of `simple_closed_rectifiable_isoperimetric_eq_iff` via Mil. -/
theorem simple_closed_rectifiable_isoperimetric_eq_iff_of_signedArea {γ : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hrect : BoundedVariationOn γ (Icc a b))
    (harea : (volume (filledHull (γ '' Icc a b) \ γ '' Icc a b)).toReal ≤
      |rectifiableSignedAreaComplex γ a b|) :
    4 * Real.pi * (volume (filledHull (γ '' Icc a b) \ γ '' Icc a b)).toReal =
        (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc a b = Metric.sphere c r := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · have harea_eq : 4 * Real.pi * |rectifiableSignedAreaComplex γ a b| =
        (eVariationOn γ (Icc a b)).toReal ^ 2 :=
      le_antisymm (four_mul_pi_mul_abs_rectifiableSignedAreaComplex_le hab.le hrect hγ hclosed)
        (heq ▸ mul_le_mul_of_nonneg_left harea (by positivity))
    exact exists_sphere_trace_of_rectifiableSignedAreaComplex_eq_of_injOn_Ico
      hab hrect hγ hclosed hinj harea_eq
  · rintro ⟨c, r, hr, htrace⟩
    exact (simple_closed_rectifiable_sphere_eq hab hγ hclosed hinj hr.le htrace).2
/-- **Compatibility specialization of `jordan_isoperimetric` via Milestone I3**. -/
theorem jordan_isoperimetric_of_signedArea {C : Set ℂ} (hC : IsJordanCurve C) (hrect : μHE[1] C < ⊤)
    (harea : ∀ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) → γ 0 = γ 1 → InjOn γ (Ico 0 1) →
      BoundedVariationOn γ (Icc 0 1) → γ '' Icc 0 1 = C →
        (volume (filledHull C \ C)).toReal ≤ |rectifiableSignedAreaComplex γ 0 1|) :
    4 * Real.pi * (volume (filledHull C \ C)).toReal ≤ (μHE[1] C).toReal ^ 2 := by
  obtain ⟨γ, hcont, hclosed, hinj, hbv, himg⟩ :=
    (isJordanCurve_and_hausdorffMeasure_lt_top_iff (C := C)).mp ⟨hC, hrect⟩
  have hlen : μHE[1] C = eVariationOn γ (Icc 0 1) := by
    rw [← himg, euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hcont hinj]
  rw [hlen, ← himg]
  exact simple_closed_rectifiable_isoperimetric_of_signedArea zero_lt_one hcont hclosed hinj hbv
    (by simpa [himg] using harea γ hcont hclosed hinj hbv himg)
/-- **Compatibility specialization of `jordan_isoperimetric_eq_iff` via Milestone I3**. -/
theorem jordan_isoperimetric_eq_iff_of_signedArea {C : Set ℂ} (hC : IsJordanCurve C)
    (hrect : μHE[1] C < ⊤)
    (harea : ∀ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) → γ 0 = γ 1 → InjOn γ (Ico 0 1) →
      BoundedVariationOn γ (Icc 0 1) → γ '' Icc 0 1 = C →
        (volume (filledHull C \ C)).toReal ≤ |rectifiableSignedAreaComplex γ 0 1|) :
    4 * Real.pi * (volume (filledHull C \ C)).toReal = (μHE[1] C).toReal ^ 2 ↔
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ C = Metric.sphere c r := by
  obtain ⟨γ, hcont, hclosed, hinj, hbv, himg⟩ :=
    (isJordanCurve_and_hausdorffMeasure_lt_top_iff (C := C)).mp ⟨hC, hrect⟩
  have hlen : μHE[1] C = eVariationOn γ (Icc 0 1) := by
    rw [← himg, euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hcont hinj]
  rw [hlen, ← himg]
  exact simple_closed_rectifiable_isoperimetric_eq_iff_of_signedArea zero_lt_one hcont hclosed
    hinj hbv (by simpa [himg] using harea γ hcont hclosed hinj hbv himg)

/-! ### Unconditional non-AC Cantor circle verification in `ℂ` -/
/-- Complex Cantor-reparametrized circle `cantorCircleCurveComplex c r : ℝ → ℂ` on `[0, 1]`. -/
noncomputable def cantorCircleCurveComplex (c : ℂ) (r : ℝ) : ℝ → ℂ :=
  complexToEuclidean.symm ∘ cantorCircleCurve (complexToEuclidean c) r
/-- **Unconditional verification of the non-AC Cantor circle in `ℂ`**. -/
theorem cantorCircleCurveComplex_isoperimetric_package (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (cantorCircleCurveComplex c r) (Icc 0 1) ∧
      cantorCircleCurveComplex c r 0 = cantorCircleCurveComplex c r 1 ∧
      InjOn (cantorCircleCurveComplex c r) (Ico 0 1) ∧
      BoundedVariationOn (cantorCircleCurveComplex c r) (Icc 0 1) ∧
      ¬ AbsolutelyContinuousOnInterval (cantorCircleCurveComplex c r) 0 1 ∧
      cantorCircleCurveComplex c r '' Icc 0 1 = Metric.sphere c r ∧
      IsJordanCurve (cantorCircleCurveComplex c r '' Icc 0 1) ∧ 4 * Real.pi *
          (volume (filledHull (cantorCircleCurveComplex c r '' Icc 0 1) \
            cantorCircleCurveComplex c r '' Icc 0 1)).toReal =
        (eVariationOn (cantorCircleCurveComplex c r) (Icc 0 1)).toReal ^ 2 := by
  have hcont : ContinuousOn (cantorCircleCurveComplex c r) (Icc 0 1) :=
    complexToEuclidean.symm.continuous.comp_continuousOn
      (continuousOn_cantorCircleCurve (complexToEuclidean c) r)
  have hclosed : cantorCircleCurveComplex c r 0 = cantorCircleCurveComplex c r 1 :=
    congrArg complexToEuclidean.symm (cantorCircleCurve_one (complexToEuclidean c) r).symm
  have hinj : InjOn (cantorCircleCurveComplex c r) (Ico 0 1) :=
    complexToEuclidean.symm.injective.injOn.comp
      (injOn_cantorCircleCurve_Ico (complexToEuclidean c) hr.ne') (mapsTo_univ _ _)
  have htrace : cantorCircleCurveComplex c r '' Icc 0 1 = Metric.sphere c r := by
    rw [cantorCircleCurveComplex, Set.image_comp, image_cantorCircleCurve_Icc _ hr.le]
    exact (complexToEuclidean.symm.toIsometryEquiv.image_sphere _ r).trans (by simp)
  obtain ⟨hbv, heq⟩ :=
    simple_closed_rectifiable_sphere_eq zero_lt_one hcont hclosed hinj hr.le htrace
  have hnot_ac : ¬ AbsolutelyContinuousOnInterval (cantorCircleCurveComplex c r) 0 1 := by
    intro hac
    have hacE :
        AbsolutelyContinuousOnInterval (cantorCircleCurve (complexToEuclidean c) r) 0 1 := by
      have h := complexToEuclidean.lipschitzWith.comp_absolutelyContinuousOnInterval hac
      have heq_fn : (complexToEuclidean ∘ cantorCircleCurveComplex c r) =
          cantorCircleCurve (complexToEuclidean c) r := by ext t; simp [cantorCircleCurveComplex]
      rwa [heq_fn] at h
    exact not_absolutelyContinuousOnInterval_cantorCircleCurve (complexToEuclidean c) hr.ne' hacE
  exact ⟨hcont, hclosed, hinj, hbv, hnot_ac, htrace,
    isJordanCurve_image_Icc zero_lt_one hcont hclosed hinj, heq⟩

end PlanarJordanIsoperimetry

end TauCeti
