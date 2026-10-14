/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.OneDimIsoperimetry
public import TauCeti.MeasureTheory.Measure.ReducedBoundary
public import TauCeti.MeasureTheory.Measure.IsoperimetricDomains

import all TauCeti.MeasureTheory.Measure.OneDimIsoperimetry
import all TauCeti.MeasureTheory.Measure.ReducedBoundary
import all TauCeti.MeasureTheory.Measure.IsoperimetricDomains

/-!
# Topological-Frontier Isoperimetric Corollary, Counterexamples, and Ellipsoid/Ellipse Strictness

This file develops the topological-frontier isoperimetric corollary and its sharp-constant equality
consequences, the two frontier sensitivity counterexamples, the unconditional one-dimensional
topological-frontier inequality and interval/ball rigidity on `ℝ`, and the unconditional
isoperimetric inequality and strict non-spherical/non-circular rigidity for `n`-dimensional
axis-aligned ellipsoids and planar ellipses.

## Main Definitions and Results

* `TauCeti.euclideanHausdorffMeasure`, `TauCeti.frontierIsoperimetricDeficit`
* `TauCeti.isoperimetricBound_le_hausdorffMeasure_frontier`,
  `TauCeti.ae_eq_ball_of_isoperimetricBound_eq_hausdorffMeasure_frontier`,
  `TauCeti.eq_ball_and_frontier_eq_sphere_of_isRegularOpen_of_frontier_eq`
* `TauCeti.not_isoperimetricBound_eq_hausdorffMeasure_frontier_ball_union_dense`,
  `TauCeti.punctured_ball_frontier_isoperimetric_counterexample`
* `TauCeti.isoperimetricBound_le_hausdorffMeasure_frontier_real`,
  `TauCeti.ae_eq_ball_of_isoperimetricBound_eq_hausdorffMeasure_frontier_real`
* `TauCeti.euclideanEllipsoid`, `TauCeti.planarEllipse`,
  `TauCeti.isoperimetricBound_euclideanEllipsoid_lt_perimeter`,
  `TauCeti.isoperimetricBound_planarEllipse_lt_perimeter`,
  `TauCeti.isoperimetricBound_planarEllipse_eq_perimeter_iff`
-/

public section
open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set TopologicalSpace
  TestFunction
open scoped ENNReal NNReal InnerProductSpace Topology Distributions
open TauCeti.MeasureTheory
namespace TauCeti

/-! ### Section 1: Topological-frontier corollary, sharp equality consequences, counterexamples -/

section FrontierCorollary
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The `d`-dimensional Hausdorff measure `μH[(d : ℝ)]` on `E`. -/
noncomputable abbrev euclideanHausdorffMeasure (d : ℕ) : Measure E := μH[(d : ℝ)]
/-- **Topological-frontier isoperimetric deficit** of `s ⊆ E`: `frontierIsoperimetricDeficit s =
(H^{n-1}(frontier s)).toReal - (isoperimetricBound s).toReal`. -/
noncomputable def frontierIsoperimetricDeficit (s : Set E) : ℝ :=
  (euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s)).toReal -
    (isoperimetricBound s).toReal
/-- When `euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) < ⊤` (`[Nontrivial E]`),
`frontier s` is Lebesgue-null, `s` is `NullMeasurableSet` without prior measurability assumptions,
`interior s =ᵐ[volume] s`, and both `isoperimetricBound` and `perimeter` agree on `interior s`. -/
theorem isoperimetricBound_and_perimeter_interior_of_hausdorffMeasure_frontier_lt_top [Nontrivial E]
    {s : Set E} (hfront : euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) < ⊤) :
    volume (frontier s) = 0 ∧ NullMeasurableSet s volume ∧ (interior s =ᵐ[volume] s) ∧ (closure s
    =ᵐ[volume] s) ∧ isoperimetricBound (interior s) = isoperimetricBound s ∧ isoperimetricBound
    (closure s) = isoperimetricBound s ∧ perimeter volume (interior s) = perimeter volume s ∧
    perimeter volume (closure s) = perimeter volume s := by
  obtain ⟨h0, hmeas, hi, hc, _, _⟩ :=
    nullMeasurableSet_and_interior_ae_eq_of_hausdorffMeasure_frontier_lt_top (μ := volume) hfront
  obtain ⟨hpi, hpc⟩ := perimeter_interior_and_closure_of_null_frontier h0
  exact ⟨h0, hmeas, hi, hc, isoperimetricBound_congr_ae hi, isoperimetricBound_congr_ae hc,
    hpi, hpc⟩
/-- **Extended topological-frontier isoperimetric corollary** (`isoperimetricBound s ≤
H^{n-1}(frontier s)`), requiring **no separate measurability hypothesis on `s`**. -/
theorem isoperimetricBound_le_hausdorffMeasure_frontier [Nontrivial E] (s : Set E) (hiso : volume
    (frontier s) = 0 → NullMeasurableSet s volume → isoperimetricBound (interior s) ≤ perimeter
    volume (interior s)) (hperim : volume (frontier s) = 0 → NullMeasurableSet s volume → perimeter
    volume s ≤ euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s)) : isoperimetricBound
    s ≤ euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) := by
  by_cases htop : euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨h0, hmeas, _, _, hbound_i, _, hperim_i, _⟩ :=
      isoperimetricBound_and_perimeter_interior_of_hausdorffMeasure_frontier_lt_top
        (lt_top_iff_ne_top.2 htop)
    calc isoperimetricBound s = isoperimetricBound (interior s) := hbound_i.symm
      _ ≤ perimeter volume (interior s) := hiso h0 hmeas
      _ = perimeter volume s := hperim_i
      _ ≤ euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) := hperim h0 hmeas
/-- **Finite-volume topological-frontier isoperimetric corollary** (no measurability needed). -/
theorem isoperimetricBound_le_hausdorffMeasure_frontier_of_volume_lt_top [Nontrivial E] {s : Set E}
    (hvol : volume s < ⊤) (hiso : volume (frontier s) = 0 → NullMeasurableSet s volume → volume
    (interior s) < ⊤ → isoperimetricBound (interior s) ≤ perimeter volume (interior s)) (hperim :
    volume (frontier s) = 0 → NullMeasurableSet s volume → volume s < ⊤ → perimeter volume s ≤
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s)) : isoperimetricBound s ≤
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) :=
  isoperimetricBound_le_hausdorffMeasure_frontier s
    (fun h0 hmeas ↦ hiso h0 hmeas ((measure_mono interior_subset).trans_lt hvol))
    (fun h0 hmeas ↦ hperim h0 hmeas hvol)
/-- **Bounded-set topological-frontier isoperimetric corollary** (without measurability of `s`). -/
theorem isoperimetricBound_le_hausdorffMeasure_frontier_of_isBounded [Nontrivial E] {s : Set E}
    (hbdd : Bornology.IsBounded s) (hiso : volume (frontier s) = 0 → NullMeasurableSet s volume →
    volume (interior s) < ⊤ → isoperimetricBound (interior s) ≤ perimeter volume (interior s))
    (hperim : volume (frontier s) = 0 → NullMeasurableSet s volume → volume s < ⊤ → perimeter volume
    s ≤ euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s)) : isoperimetricBound s ≤
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) :=
  isoperimetricBound_le_hausdorffMeasure_frontier_of_volume_lt_top hbdd.measure_lt_top hiso hperim
/-- Nonnegativity of `frontierIsoperimetricDeficit s` when `H^{n-1}(frontier s) < ⊤`. -/
theorem frontierIsoperimetricDeficit_nonneg {s : Set E} (hfront : euclideanHausdorffMeasure
    (Module.finrank ℝ E - 1) (frontier s) < ⊤) (hle : isoperimetricBound s ≤
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s)) : 0 ≤
    frontierIsoperimetricDeficit s :=
  sub_nonneg.2 ((ENNReal.toReal_le_toReal (hle.trans_lt hfront).ne hfront.ne).2 hle)
/-- **Sharp-constant topological-frontier equality consequences**: equality `isoperimetricBound s =
H^{n-1}(frontier s)` (`0 < volume s < ⊤`, `H^{n-1}(frontier s) < ⊤`) forces `volume (frontier s) =
0`, `NullMeasurableSet s volume`, `perimeter volume s = H^{n-1}(frontier s)`, `isoperimetricBound s
= perimeter volume s`, zero deficits, and `s =ᵐ[volume] Metric.ball c r`. -/
theorem ae_eq_ball_of_isoperimetricBound_eq_hausdorffMeasure_frontier [Nontrivial E] {s : Set E}
    (hpos : 0 < volume s) (hvol : volume s < ⊤) (hfront : euclideanHausdorffMeasure (Module.finrank
    ℝ E - 1) (frontier s) < ⊤) (hiso : volume (frontier s) = 0 → NullMeasurableSet s volume →
    isoperimetricBound (interior s) ≤ perimeter volume (interior s)) (hperim : volume (frontier s) =
    0 → NullMeasurableSet s volume → perimeter volume s ≤ euclideanHausdorffMeasure (Module.finrank
    ℝ E - 1) (frontier s)) (hrig : NullMeasurableSet s volume → 0 < volume s → volume s < ⊤ →
    isoperimetricBound s = perimeter volume s → ∃ c : E, ∃ r : ℝ, 0 < r ∧ (s =ᵐ[volume] Metric.ball
    c r)) (heq : isoperimetricBound s = euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier
    s)) : volume (frontier s) = 0 ∧ NullMeasurableSet s volume ∧ perimeter volume s =
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) ∧ isoperimetricBound s =
    perimeter volume s ∧ frontierIsoperimetricDeficit s = 0 ∧ isoperimetricDeficit s = 0 ∧ ∃ c : E,
    ∃ r : ℝ, 0 < r ∧ (s =ᵐ[volume] Metric.ball c r) := by
  obtain ⟨h0, hmeas, _, _, hbound_i, _, hperim_i, _⟩ :=
    isoperimetricBound_and_perimeter_interior_of_hausdorffMeasure_frontier_lt_top hfront
  have hle_p : isoperimetricBound s ≤ perimeter volume s := by
    rw [← hbound_i, ← hperim_i]; exact hiso h0 hmeas
  have hbp : isoperimetricBound s = perimeter volume s :=
    le_antisymm hle_p ((hperim h0 hmeas).trans_eq heq.symm)
  exact ⟨h0, hmeas, hbp.symm.trans heq, hbp, by simp [frontierIsoperimetricDeficit, heq],
    isoperimetricDeficit_eq_zero_of_perimeter_eq hbp.symm, hrig hmeas hpos hvol hbp⟩
theorem closure_interior_eq_closedBall_of_null_frontier_of_ae_eq_ball {s : Set E} {c : E} {r : ℝ}
    (hr : 0 < r) (h0 : volume (frontier s) = 0) (hae : s =ᵐ[volume] Metric.ball c r) : closure
    (interior s) = Metric.closedBall c r ∧ interior (closure (interior s)) = Metric.ball c r := by
  have hi_ball : interior s =ᵐ[volume] Metric.ball c r :=
    (interior_ae_eq_of_null_frontier h0).trans hae
  have hcl : closure (interior s) = Metric.closedBall c r :=
    (isOpen_interior.closure_eq_of_ae_eq Metric.isOpen_ball hi_ball).trans (closure_ball c hr.ne')
  exact ⟨hcl, by rw [hcl, interior_closedBall c hr.ne']⟩
/-- **Exact point-set ball rigidity for regular open sets under sharp frontier equality**: if
`IsRegularOpen s`, `0 < volume s < ⊤`, `H^{n-1}(frontier s) < ⊤`, and `isoperimetricBound s =
H^{n-1}(frontier s)`, then literally `s = Metric.ball c r` and `frontier s = Metric.sphere c r`. -/
theorem eq_ball_and_frontier_eq_sphere_of_isRegularOpen_of_frontier_eq [Nontrivial E] {s : Set E}
    (hreg : IsRegularOpen s) (hpos : 0 < volume s) (hvol : volume s < ⊤) (hfront :
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s) < ⊤) (hiso : volume (frontier s)
    = 0 → NullMeasurableSet s volume → isoperimetricBound (interior s) ≤ perimeter volume (interior
    s)) (hperim : volume (frontier s) = 0 → NullMeasurableSet s volume → perimeter volume s ≤
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s)) (hrig : NullMeasurableSet s
    volume → 0 < volume s → volume s < ⊤ → isoperimetricBound s = perimeter volume s → ∃ c : E, ∃ r
    : ℝ, 0 < r ∧ (s =ᵐ[volume] Metric.ball c r)) (heq : isoperimetricBound s =
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier s)) : ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =
    Metric.ball c r ∧ frontier s = Metric.sphere c r ∧ closure s = Metric.closedBall c r := by
  obtain ⟨_, _, _, _, _, _, c, r, hr, hae⟩ :=
    ae_eq_ball_of_isoperimetricBound_eq_hausdorffMeasure_frontier hpos hvol hfront hiso hperim
      hrig heq
  obtain ⟨hfr_eq, hcl_eq⟩ := frontier_eq_sphere_of_isRegularOpen_of_ae_eq_ball hreg hr.ne' hae
  exact ⟨c, r, hr, eq_ball_of_isRegularOpen_of_ae_eq_ball hreg hae, hfr_eq, hcl_eq⟩
theorem hausdorffMeasure_frontier_ball_union_eq_top_of_null_of_dense [Nontrivial E] (c : E) {r : ℝ}
    (hr : 0 < r) {D : Set E} (hD_null : volume D = 0) (hD_dense : Dense D) :
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier (Metric.ball c r ∪ D)) = ⊤ := by
  by_contra hne
  have h0 : volume (frontier (Metric.ball c r ∪ D)) = 0 :=
    measure_frontier_eq_zero_of_hausdorffMeasure_sub_one_ne_top hne
  rw [volume_frontier_ball_union_eq_top_of_null_of_dense c hr hD_null hD_dense] at h0
  exact ENNReal.top_ne_zero h0
/-- **Failure of the converse of topological-frontier equality under null modifications**: for `s =
Metric.ball c r ∪ D` (`0 < r`, `volume D = 0`, `Dense D`), `s =ᵐ[volume] Metric.ball c r` and
`perimeter volume s = isoperimetricBound s < ⊤`, yet `H^{n-1}(frontier s) = ⊤`. -/
theorem not_isoperimetricBound_eq_hausdorffMeasure_frontier_ball_union_dense [Nontrivial E] (c : E)
    {r : ℝ} (hr : 0 < r) {D : Set E} (hD_null : volume D = 0) (hD_dense : Dense D) : (Metric.ball c
    r ∪ D =ᵐ[volume] Metric.ball c r) ∧ perimeter volume (Metric.ball c r ∪ D) = isoperimetricBound
    (Metric.ball c r ∪ D) ∧ isoperimetricBound (Metric.ball c r ∪ D) < ⊤ ∧ euclideanHausdorffMeasure
    (Module.finrank ℝ E - 1) (frontier (Metric.ball c r ∪ D)) = ⊤ ∧ isoperimetricBound (Metric.ball
    c r ∪ D) ≠ euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier (Metric.ball c r ∪ D))
    := by
  have hae : Metric.ball c r ∪ D =ᵐ[volume] Metric.ball c r :=
    ball_union_null_ae_eq_ball c r hD_null
  have hbound : isoperimetricBound (Metric.ball c r ∪ D) = isoperimetricBound (Metric.ball c r) :=
    isoperimetricBound_congr_ae hae
  have hperim : perimeter volume (Metric.ball c r ∪ D) =
      isoperimetricBound (Metric.ball c r ∪ D) := by
    rw [perimeter_ball_union_null c r hD_null, hbound, perimeter_ball_eq_isoperimetricBound c hr]
  have hlt_top : isoperimetricBound (Metric.ball c r ∪ D) < ⊤ := by
    rw [hbound]; exact isoperimetricBound_lt_top_of_volume_lt_top measure_ball_lt_top
  have htop := hausdorffMeasure_frontier_ball_union_eq_top_of_null_of_dense c hr hD_null hD_dense
  exact ⟨hae, hperim, hlt_top, htop, by rw [htop]; exact hlt_top.ne⟩
/-- Specialization of `not_isoperimetricBound_eq_hausdorffMeasure_frontier_ball_union_dense` to any
**countable dense set `D ⊆ E`**. -/
theorem not_isoperimetricBound_eq_hausdorffMeasure_frontier_ball_union_countable_dense [Nontrivial
    E] (c : E) {r : ℝ} (hr : 0 < r) {D : Set E} (hD_count : D.Countable) (hD_dense : Dense D) :
    (Metric.ball c r ∪ D =ᵐ[volume] Metric.ball c r) ∧ perimeter volume (Metric.ball c r ∪ D) =
    isoperimetricBound (Metric.ball c r ∪ D) ∧ isoperimetricBound (Metric.ball c r ∪ D) < ⊤ ∧
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier (Metric.ball c r ∪ D)) = ⊤ ∧
    isoperimetricBound (Metric.ball c r ∪ D) ≠ euclideanHausdorffMeasure (Module.finrank ℝ E - 1)
    (frontier (Metric.ball c r ∪ D)) :=
  not_isoperimetricBound_eq_hausdorffMeasure_frontier_ball_union_dense c hr
    (hD_count.measure_zero volume) hD_dense
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem closure_punctured_ball [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) : closure (Metric.ball c
    r \ {c}) = Metric.closedBall c r := by
  refine Subset.antisymm (closure_minimal (sdiff_subset.trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall) ?_
  rw [← closure_ball c hr.ne']; refine closure_minimal (fun x hx ↦ ?_) isClosed_closure
  by_cases hxc : x = c
  · rw [hxc]; exact interior_subset (center_mem_interior_closure_punctured_ball c hr)
  · exact subset_closure ⟨hx, hxc⟩
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem frontier_punctured_ball [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) : frontier (Metric.ball
    c r \ {c}) = Metric.sphere c r ∪ {c} := by
  have hopen : IsOpen (Metric.ball c r \ {c}) := Metric.isOpen_ball.sdiff isClosed_singleton
  rw [frontier, closure_punctured_ball c hr, hopen.interior_eq]; ext x
  simp only [Set.mem_sdiff, mem_closedBall, mem_ball, mem_singleton_iff, not_and, not_not,
    mem_union, mem_sphere]
  exact ⟨fun ⟨hle, h⟩ ↦ (lt_or_eq_of_le hle).imp_left h |>.symm,
    by rintro (rfl | rfl); exacts [⟨le_rfl, fun hlt ↦ (lt_irrefl _ hlt).elim⟩,
      ⟨by simpa using hr.le, fun _ ↦ rfl⟩]⟩
theorem hausdorffMeasure_frontier_punctured_ball (hn : 2 ≤ Module.finrank ℝ E) (c : E) {r : ℝ} (hr :
    0 < r) : euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (frontier (Metric.ball c r \ {c})) =
    euclideanHausdorffMeasure (Module.finrank ℝ E - 1) (Metric.sphere c r) := by
  have hpos : 0 < Module.finrank ℝ E := by omega
  have : Nontrivial E := Module.finrank_pos_iff.1 hpos
  have hd : (0 : ℝ) < (Module.finrank ℝ E - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < Module.finrank ℝ E - 1)
  have : NullSingletonClass (euclideanHausdorffMeasure (Module.finrank ℝ E - 1) : Measure E) :=
    Measure.nullSingletonClass_hausdorff E hd
  rw [frontier_punctured_ball c hr]
  exact le_antisymm ((measure_union_le _ _).trans (by simp [measure_singleton c]))
    (measure_mono subset_union_left)
/-- **Failure of literal ball equality without `IsRegularOpen` for punctured balls (`n ≥ 2`)**: in
dimension `2 ≤ Module.finrank ℝ E`, `s = Metric.ball c r \ {c}` (`0 < r`) has the same volume,
`isoperimetricBound`, `perimeter`, and `H^{n-1}(frontier s)` as `Metric.ball c r`, yet `¬
IsRegularOpen s`, `∀ x R, s ≠ Metric.ball x R`, and `∀ x R, s ≠ Metric.closedBall x R`. -/
theorem punctured_ball_frontier_isoperimetric_counterexample (hn : 2 ≤ Module.finrank ℝ E) (c : E)
    {r : ℝ} (hr : 0 < r) : (Metric.ball c r \ {c} =ᵐ[volume] Metric.ball c r) ∧ perimeter volume
    (Metric.ball c r \ {c}) = isoperimetricBound (Metric.ball c r \ {c}) ∧ euclideanHausdorffMeasure
    (Module.finrank ℝ E - 1) (frontier (Metric.ball c r \ {c})) = euclideanHausdorffMeasure
    (Module.finrank ℝ E - 1) (frontier (Metric.ball c r)) ∧ ¬ IsRegularOpen (Metric.ball c r \ {c})
    ∧ (∀ x : E, ∀ R : ℝ, Metric.ball c r \ {c} ≠ Metric.ball x R) ∧ (∀ x : E, ∀ R : ℝ, Metric.ball c
    r \ {c} ≠ Metric.closedBall x R) := by
  have hpos : 0 < Module.finrank ℝ E := by omega
  have : Nontrivial E := Module.finrank_pos_iff.1 hpos
  obtain ⟨hperim, _, hae, hne_ball, hne_cball⟩ := punctured_ball_isoperimetric_rigidity c hr
  rw [frontier_ball c hr.ne', hausdorffMeasure_frontier_punctured_ball hn c hr]
  exact ⟨hae, hperim, rfl, not_isRegularOpen_punctured_ball c hr, hne_ball, hne_cball⟩
end FrontierCorollary

/-! ### Section 2: Unconditional 1D topological-frontier inequality & interval rigidity on `ℝ` -/

section OneDimFrontier
theorem _root_.IsPreconnected.exists_mem_frontier {X : Type*} [TopologicalSpace X] {v s : Set X} (hv
    : IsPreconnected v) {x y : X} (hx : x ∈ v ∩ interior s) (hy : y ∈ v ∩ (closure s)ᶜ) : ∃ p ∈ v ∩
    frontier s, p ≠ x := by
  by_contra! h
  have hsub : v ⊆ interior s ∪ (closure s)ᶜ := fun p hp ↦ by
    by_cases hp_int : p ∈ interior s
    · exact Or.inl hp_int
    · exact Or.inr fun hp_cl ↦ hp_int ((h p ⟨hp, hp_cl, hp_int⟩).symm ▸ hx.2)
  obtain ⟨z, _, hz_int, hz_compl⟩ :=
    hv (interior s) (closure s)ᶜ isOpen_interior isClosed_closure.isOpen_compl hsub ⟨x, hx⟩ ⟨y, hy⟩
  exact hz_compl (interior_subset.trans subset_closure hz_int)
theorem two_le_hausdorffMeasure_zero_of_pair {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {A : Set X} {p₁ p₂ : X} (hne : p₁ ≠ p₂) (hp₁ : p₁ ∈ A) (hp₂ : p₂ ∈ A) : 2 ≤ μH[0]
    A := by
  have hsub : ({p₁} ∪ {p₂} : Set X) ⊆ A :=
    union_subset (singleton_subset_iff.2 hp₁) (singleton_subset_iff.2 hp₂)
  calc (2 : ℝ≥0∞) = μH[0] ({p₁} : Set X) + μH[0] ({p₂} : Set X) := by
        rw [hausdorffMeasure_zero_singleton, hausdorffMeasure_zero_singleton]; norm_num
    _ = μH[0] ({p₁} ∪ {p₂} : Set X) :=
        (measure_union (disjoint_singleton.2 hne) (measurableSet_singleton p₂)).symm
    _ ≤ μH[0] A := measure_mono hsub
theorem three_le_hausdorffMeasure_zero_of_triple {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {A : Set X} {p₁ p₂ p₃ : X} (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) (hp₁ :
    p₁ ∈ A) (hp₂ : p₂ ∈ A) (hp₃ : p₃ ∈ A) : 3 ≤ μH[0] A := by
  have hsub : ({p₁, p₂} ∪ {p₃} : Set X) ⊆ A :=
    union_subset (pair_subset hp₁ hp₂) (singleton_subset_iff.2 hp₃)
  have hdisj : Disjoint ({p₁, p₂} : Set X) {p₃} := by simp [h13.symm, h23.symm]
  calc (3 : ℝ≥0∞) = 2 + 1 := by norm_num
    _ ≤ μH[0] ({p₁, p₂} : Set X) + μH[0] ({p₃} : Set X) :=
        add_le_add (two_le_hausdorffMeasure_zero_of_pair h12 (mem_insert _ _)
          (mem_insert_of_mem _ (mem_singleton _))) (by rw [hausdorffMeasure_zero_singleton])
    _ = μH[0] ({p₁, p₂} ∪ {p₃} : Set X) := (measure_union hdisj (measurableSet_singleton p₃)).symm
    _ ≤ μH[0] A := measure_mono hsub
theorem eq_or_eq_of_hausdorffMeasure_zero_le_two {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {A : Set X} (hA : μH[0] A ≤ 2) {p₁ p₂ p₃ : X} (h12 : p₁ ≠ p₂) (hp₁ : p₁ ∈ A) (hp₂
    : p₂ ∈ A) (hp₃ : p₃ ∈ A) : p₃ = p₁ ∨ p₃ = p₂ := by
  by_contra! h
  exact absurd ((three_le_hausdorffMeasure_zero_of_triple h12 h.1.symm h.2.symm hp₁ hp₂ hp₃).trans
    hA) (by norm_num)
theorem exists_lt_and_gt_mem_frontier_real {s : Set ℝ} (htop : volume (closure s) < ⊤) {x₀ : ℝ} (hx₀
    : x₀ ∈ interior s) : (∃ p₁ < x₀, p₁ ∈ frontier s) ∧ (∃ p₂ > x₀, p₂ ∈ frontier s) := by
  have hy_ex : ∃ y ≤ x₀, y ∈ (closure s)ᶜ := by
    by_contra! h
    have hvol := measure_mono (μ := volume)
      (fun y hy ↦ of_not_not (h y hy) : Set.Iic x₀ ⊆ closure s)
    rw [Real.volume_Iic] at hvol; exact htop.not_ge hvol
  have hz_ex : ∃ z ≥ x₀, z ∈ (closure s)ᶜ := by
    by_contra! h
    have hvol := measure_mono (μ := volume)
      (fun z hz ↦ of_not_not (h z hz) : Set.Ici x₀ ⊆ closure s)
    rw [Real.volume_Ici] at hvol; exact htop.not_ge hvol
  obtain ⟨⟨y, hyx, hy⟩, ⟨z, hxz, hz⟩⟩ := hy_ex, hz_ex
  obtain ⟨p₁, ⟨hp₁_Icc, hp₁_fr⟩, hp₁_ne⟩ := isPreconnected_Icc.exists_mem_frontier
    (x := x₀) (y := y) ⟨⟨hyx, le_rfl⟩, hx₀⟩ ⟨⟨le_rfl, hyx⟩, hy⟩
  obtain ⟨p₂, ⟨hp₂_Icc, hp₂_fr⟩, hp₂_ne⟩ := isPreconnected_Icc.exists_mem_frontier
    (x := x₀) (y := z) ⟨⟨le_rfl, hxz⟩, hx₀⟩ ⟨⟨hxz, le_rfl⟩, hz⟩
  exact ⟨⟨p₁, lt_of_le_of_ne hp₁_Icc.2 hp₁_ne, hp₁_fr⟩,
    ⟨p₂, lt_of_le_of_ne hp₂_Icc.1 hp₂_ne.symm, hp₂_fr⟩⟩
@[simp] theorem isoperimetricBound_real (s : Set ℝ) : isoperimetricBound s = 2 := by
  simp [isoperimetricBound, Module.finrank_self, Real.volume_ball]
/-- **Unconditional 1D topological-frontier lower bound** (`2 ≤ μH[0] (frontier s)`). -/
theorem two_le_hausdorffMeasure_zero_frontier_real {s : Set ℝ} (h0 : 0 < volume s) (htop : volume s
    < ⊤) : 2 ≤ μH[0] (frontier s) := by
  by_cases hf : μH[(Module.finrank ℝ ℝ - 1 : ℕ)] (frontier s) = ⊤
  · simp [Module.finrank_self] at hf; simp [hf]
  · obtain ⟨_, _, _, _, hint_eq, hcl_eq⟩ :=
      nullMeasurableSet_and_interior_ae_eq_of_hausdorffMeasure_frontier_lt_top (μ := volume)
        (lt_top_iff_ne_top.2 hf)
    obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero (hint_eq.symm ▸ h0).ne'
    obtain ⟨⟨p₁, hp₁x, hp₁_fr⟩, ⟨p₂, hxp₂, hp₂_fr⟩⟩ :=
      exists_lt_and_gt_mem_frontier_real (hcl_eq.symm ▸ htop) hx₀
    exact two_le_hausdorffMeasure_zero_of_pair (hp₁x.trans hxp₂).ne hp₁_fr hp₂_fr
/-- **Unconditional 1D topological-frontier isoperimetric inequality** on `ℝ`: for any `s : Set ℝ`
(`0 < volume s < ⊤`), `isoperimetricBound s ≤ H^0(frontier s)`. -/
theorem isoperimetricBound_le_hausdorffMeasure_frontier_real {s : Set ℝ} (h0 : 0 < volume s) (htop :
    volume s < ⊤) : isoperimetricBound s ≤ euclideanHausdorffMeasure (Module.finrank ℝ ℝ - 1)
    (frontier s) := by
  simpa [isoperimetricBound_real, euclideanHausdorffMeasure, Module.finrank_self] using
    two_le_hausdorffMeasure_zero_frontier_real h0 htop
/-- **Unconditional 1D topological-frontier equality rigidity**: if `0 < volume s < ⊤` and `μH[0]
(frontier s) ≤ 2` on `ℝ`, then `frontier s = {a, b}` and `interior s = Set.Ioo a b`. -/
theorem interior_and_frontier_eq_of_hausdorffMeasure_zero_frontier_le_two {s : Set ℝ} (h0 : 0 <
    volume s) (htop : volume s < ⊤) (hfr : μH[0] (frontier s) ≤ 2) : ∃ a b : ℝ, a < b ∧ frontier s =
    {a, b} ∧ interior s = Set.Ioo a b ∧ s =ᵐ[volume] Set.Ioo a b ∧ perimeter volume s = 2 := by
  have hlt_top : μH[(Module.finrank ℝ ℝ - 1 : ℕ)] (frontier s) < ⊤ := by
    simpa [Module.finrank_self] using hfr.trans_lt (by norm_num)
  obtain ⟨hnull, _, hi_ae, _, hint_eq, hcl_eq⟩ :=
    nullMeasurableSet_and_interior_ae_eq_of_hausdorffMeasure_frontier_lt_top (μ := volume) hlt_top
  have hcl_lt : volume (closure s) < ⊤ := hcl_eq.symm ▸ htop
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero (hint_eq.symm ▸ h0).ne'
  obtain ⟨⟨a, hax, ha_fr⟩, ⟨b, hxb, hb_fr⟩⟩ := exists_lt_and_gt_mem_frontier_real hcl_lt hx₀
  have hab : a < b := hax.trans hxb
  have hfr_eq : frontier s = {a, b} := Subset.antisymm
    (fun p hp ↦ eq_or_eq_of_hausdorffMeasure_zero_le_two hfr hab.ne ha_fr hb_fr hp)
    (pair_subset ha_fr hb_fr)
  have hint_sub : interior s ⊆ Set.Ioo a b := fun x hx ↦ by
    obtain ⟨⟨p₁, hp₁x, hp₁_fr⟩, ⟨p₂, hxp₂, hp₂_fr⟩⟩ := exists_lt_and_gt_mem_frontier_real hcl_lt hx
    rcases eq_or_eq_of_hausdorffMeasure_zero_le_two hfr hab.ne ha_fr hb_fr hp₁_fr with rfl | rfl <;>
    rcases eq_or_eq_of_hausdorffMeasure_zero_le_two hfr hab.ne ha_fr hb_fr hp₂_fr with rfl | rfl
    · exact absurd (hp₁x.trans hxp₂) (lt_irrefl _)
    · exact ⟨hp₁x, hxp₂⟩
    · exact absurd ((hp₁x.trans hxp₂).trans hab) (lt_irrefl _)
    · exact absurd (hp₁x.trans hxp₂) (lt_irrefl _)
  have hIoo_sub : Set.Ioo a b ⊆ interior s := fun x hx ↦ by
    by_contra hx_not
    have hx_compl : x ∈ (closure s)ᶜ := fun hx_cl ↦ by
      have hx_fr : x ∈ frontier s := ⟨hx_cl, hx_not⟩
      rw [hfr_eq, mem_insert_iff, mem_singleton_iff] at hx_fr
      rcases hx_fr with rfl | rfl <;> [exact hx.1.false; exact hx.2.false]
    obtain ⟨p, ⟨hp_Ioo, hp_fr⟩, _⟩ := isPreconnected_Ioo.exists_mem_frontier
      (x := x₀) (y := x) ⟨⟨hax, hxb⟩, hx₀⟩ ⟨hx, hx_compl⟩
    rw [hfr_eq, mem_insert_iff, mem_singleton_iff] at hp_fr
    rcases hp_fr with rfl | rfl <;> [exact hp_Ioo.1.false; exact hp_Ioo.2.false]
  have hint_Ioo : interior s = Set.Ioo a b := Subset.antisymm hint_sub hIoo_sub
  refine ⟨a, b, hab, hfr_eq, hint_Ioo, hi_ae.symm.trans (by rw [hint_Ioo]), ?_⟩
  rw [← (perimeter_interior_and_closure_of_null_frontier hnull).1, hint_Ioo, perimeter_Ioo hab]
/-- **Unconditional 1D sharp-constant frontier equality rigidity** on `ℝ`: if `0 < volume s < ⊤` and
`isoperimetricBound s = H^0(frontier s)`, then `s =ᵐ[volume] Metric.ball c r`, `interior s =
Metric.ball c r`, and `frontier s = Metric.sphere c r` for some `c : ℝ` and `r > 0`. -/
theorem ae_eq_ball_of_isoperimetricBound_eq_hausdorffMeasure_frontier_real {s : Set ℝ} (h0 : 0 <
    volume s) (htop : volume s < ⊤) (heq : isoperimetricBound s = euclideanHausdorffMeasure
    (Module.finrank ℝ ℝ - 1) (frontier s)) : ∃ c r : ℝ, 0 < r ∧ (s =ᵐ[volume] Metric.ball c r) ∧
    interior s = Metric.ball c r ∧ frontier s = Metric.sphere c r ∧ perimeter volume s = 2 := by
  have hfr : μH[0] (frontier s) ≤ 2 := by
    simpa [isoperimetricBound_real, euclideanHausdorffMeasure, Module.finrank_self] using
      heq.symm.le
  obtain ⟨a, b, hab, hfr_eq, hint_eq, hae, hperim⟩ :=
    interior_and_frontier_eq_of_hausdorffMeasure_zero_frontier_le_two h0 htop hfr
  have hball : Metric.ball ((a + b) / 2) ((b - a) / 2) = Set.Ioo a b := by
    rw [Real.ball_eq_Ioo]; congr 1 <;> ring
  refine ⟨(a + b) / 2, (b - a) / 2, by linarith, by rwa [hball], by rw [hint_eq, hball], ?_, hperim⟩
  rw [hfr_eq, ← frontier_Ioo hab, ← hball, frontier_ball ((a + b) / 2) (by linarith)]
end OneDimFrontier

/-! ### Section 3: Linear image perimeter bounds and `n`-dimensional axis-aligned ellipsoids -/

section Ellipsoids
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem divergence_continuousLinearMap (L : E →L[ℝ] E) (x : E) : divergence L x = LinearMap.trace ℝ
    E L.toLinearMap := by rw [divergence, L.fderiv]
@[simp] theorem divergence_conj_continuousLinearEquiv (e : E ≃L[ℝ] E) (φ : E → E) (y : E) :
    divergence (fun z ↦ e (φ (e.symm z))) y = divergence φ (e.symm y) := by
  unfold divergence
  have h1 : (fun z ↦ e (φ (e.symm z))) = (e : E → E) ∘ (φ ∘ e.symm) := rfl
  rw [h1, e.comp_fderiv, e.symm.comp_right_fderiv]
  exact LinearMap.trace_conj' (fderiv ℝ φ (e.symm y)).toLinearMap e.toLinearEquiv
@[simp] theorem divergence_conj_symm_continuousLinearEquiv (e : E ≃L[ℝ] E) (ψ : E → E) (x : E) :
    divergence (fun z ↦ e.symm (ψ (e z))) x = divergence ψ (e x) :=
  divergence_conj_continuousLinearEquiv e.symm ψ x
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem integral_comp_continuousLinearEquiv (e : E ≃L[ℝ] E) (g : E → ℝ) : ∫ y, g y ∂(volume :
    Measure E) = |LinearMap.det e.toLinearMap| * ∫ x, g (e x) ∂(volume : Measure E) := by
  have hdet : LinearMap.det e.toLinearMap ≠ 0 := e.toLinearEquiv.isUnit_det'.ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E) hdet
  have hint := (e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map
    (μ := (volume : Measure E)) g).symm
  change ∫ x, g (e x) ∂(volume : Measure E) =
    ∫ y, g y ∂(Measure.map (⇑e.toLinearMap) volume) at hint
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,
    abs_inv] at hint
  rw [hint, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hdet), one_mul]
/-- **Upper bound on perimeter under `e : E ≃L[ℝ] E`**: `perimeter volume (e '' s) ≤ |det e| * max 1
‖e⁻¹‖ * perimeter volume s`. -/
theorem perimeter_image_continuousLinearEquiv_le (e : E ≃L[ℝ] E) (s : Set E) : perimeter volume (e
    '' s) ≤ ENNReal.ofReal (|LinearMap.det e.toLinearMap| * max 1 ‖e.symm.toContinuousLinearMap‖) *
    perimeter volume s := by
  set M : ℝ := max 1 ‖e.symm.toContinuousLinearMap‖
  have hM0 : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  rw [perimeter, relativePerimeter, distributionalVariation]; refine iSup₂_le fun ψ hψ ↦ ?_
  let φ₀ : 𝓓((⊤ : Opens E), E) :=
    { toFun := ψ ∘ e, contDiff' := ψ.contDiff.comp e.contDiff
      hasCompactSupport' := ψ.hasCompactSupport.comp_homeomorph e.toHomeomorph
      tsupport_subset' := subset_univ _ }
  let φ : 𝓓((⊤ : Opens E), E) :=
    TestFunction.postcompCLM (𝕜 := ℝ) (M⁻¹ • e.symm.toContinuousLinearMap) φ₀
  have hφ_norm : ∀ x, ‖φ x‖ ≤ 1 := fun x ↦ by
    change ‖M⁻¹ • e.symm (ψ (e x))‖ ≤ 1; rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hM0.le)]
    calc M⁻¹ * ‖e.symm (ψ (e x))‖
        ≤ M⁻¹ * (‖e.symm.toContinuousLinearMap‖ * ‖ψ (e x)‖) :=
          mul_le_mul_of_nonneg_left (e.symm.toContinuousLinearMap.le_opNorm _) (inv_nonneg.2 hM0.le)
      _ ≤ M⁻¹ * (M * 1) := mul_le_mul_of_nonneg_left
          (mul_le_mul (le_max_right 1 _) (hψ (e x)) (norm_nonneg _) hM0.le) (inv_nonneg.2 hM0.le)
      _ = 1 := by rw [mul_one, inv_mul_cancel₀ hM0.ne']
  have hint : ∫ y in ((⊤ : Opens E) : Set E),
      (e '' s).indicator (fun _ ↦ (1 : ℝ)) y * divergence (ψ : E → E) y ∂volume =
      (|LinearMap.det e.toLinearMap| * M) * ∫ x in ((⊤ : Opens E) : Set E),
        s.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂volume := by
    rw [setIntegral_mul_divergence_eq_integral, setIntegral_mul_divergence_eq_integral,
      integral_comp_continuousLinearEquiv e]
    have hfun : (fun x ↦ (e '' s).indicator (fun _ ↦ (1 : ℝ)) (e x) *
        divergence (ψ : E → E) (e x)) =
        fun x ↦ M * (s.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x) := by
      ext x
      have hdiv : divergence (φ : E → E) x = M⁻¹ * divergence (ψ : E → E) (e x) := by
        rw [show (φ : E → E) = M⁻¹ • fun z ↦ e.symm (ψ (e z)) from rfl,
          divergence_const_smul, divergence_conj_symm_continuousLinearEquiv]
      by_cases hx : x ∈ s <;>
        simp [hx, e.injective.mem_set_image, hdiv, ← mul_assoc, mul_inv_cancel₀ hM0.ne']
    rw [hfun, integral_const_mul, mul_assoc]
  rw [hint, ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hM0.le)]
  exact mul_le_mul_of_nonneg_left
    (le_distributionalVariation (μ := volume) φ hφ_norm (s.indicator fun _ ↦ (1 : ℝ)))
    (by positivity)
theorem perimeter_image_continuousLinearEquiv_lt_top (e : E ≃L[ℝ] E) {s : Set E} (hs : perimeter
    volume s < ⊤) : perimeter volume (e '' s) < ⊤ :=
  (perimeter_image_continuousLinearEquiv_le e s).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs)
theorem perimeter_preimage_ball_ge_of_gt (e : E ≃L[ℝ] E) (htr : 0 ≤ LinearMap.trace ℝ E
    e.symm.toLinearMap) {R : ℝ} (hR : 1 < R) : ENNReal.ofReal (LinearMap.trace ℝ E
    e.symm.toLinearMap / R) * volume (e.symm ⁻¹' Metric.ball (0 : E) 1) ≤ perimeter volume (e.symm
    ⁻¹' Metric.ball (0 : E) 1) := by
  have hRpos : 0 < R := zero_lt_one.trans hR
  let R' : ℝ := (1 + R) / 2
  let χ : ContDiffBump (0 : E) := ⟨1, R', zero_lt_one, by dsimp [R']; linarith⟩
  let φ : 𝓓((⊤ : Opens E), E) :=
    { toFun := fun x ↦ R⁻¹ • (χ (e.symm x) • e.symm x)
      contDiff' := contDiff_const.smul ((χ.contDiff.comp e.symm.contDiff).smul e.symm.contDiff)
      hasCompactSupport' :=
        ((χ.hasCompactSupport.comp_homeomorph e.symm.toHomeomorph).smul_right).smul_left
      tsupport_subset' := subset_univ _ }
  have hφ_norm : ∀ x, ‖φ x‖ ≤ 1 := fun x ↦ by
    change ‖R⁻¹ • (χ (e.symm x) • e.symm x)‖ ≤ 1
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hRpos.le),
      Real.norm_of_nonneg χ.nonneg]
    by_cases hx : e.symm x ∈ Metric.ball 0 R'
    · have hLx : ‖e.symm x‖ ≤ R := (mem_ball_zero_iff.1 hx).le.trans (by dsimp [R']; linarith)
      calc R⁻¹ * (χ (e.symm x) * ‖e.symm x‖) ≤ R⁻¹ * (1 * R) := by gcongr; exact χ.le_one
        _ = 1 := by rw [one_mul, inv_mul_cancel₀ hRpos.ne']
    · simp [Function.notMem_support.1 (by rwa [χ.support_eq] : e.symm x ∉ support χ)]
  set s : Set E := e.symm ⁻¹' Metric.ball (0 : E) 1
  have hs_open : IsOpen s := Metric.isOpen_ball.preimage e.symm.continuous
  have hdiv_s : ∀ x ∈ s, divergence (φ : E → E) x =
      LinearMap.trace ℝ E e.symm.toLinearMap / R := fun x hx ↦ by
    have hev : (φ : E → E) =ᶠ[𝓝 x] fun y ↦ R⁻¹ • e.symm y := by
      filter_upwards [hs_open.mem_nhds hx] with y hy
      change R⁻¹ • (χ (e.symm y) • e.symm y) = R⁻¹ • e.symm y
      rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_smul]
    rw [divergence, hev.fderiv_eq, ← divergence,
      show (fun y ↦ R⁻¹ • e.symm y) = R⁻¹ • (e.symm.toContinuousLinearMap : E → E) from rfl,
      divergence_const_smul, divergence_continuousLinearMap, div_eq_inv_mul]; rfl
  have hint : ∫ x in ((⊤ : Opens E) : Set E),
      s.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂volume =
      (volume s).toReal * (LinearMap.trace ℝ E e.symm.toLinearMap / R) := by
    rw [show (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x) =
      s.indicator (fun x ↦ divergence (φ : E → E) x) by ext x; by_cases hx : x ∈ s <;> simp [hx]]
    rw [setIntegral_indicator hs_open.measurableSet, Opens.coe_top, univ_inter,
      setIntegral_congr_fun hs_open.measurableSet hdiv_s, setIntegral_const,
      Measure.real, smul_eq_mul]
  have hs_img : s = e '' Metric.ball (0 : E) 1 := (e.toEquiv.image_eq_preimage_symm _).symm
  have hvol_lt_top : volume s < ⊤ := by
    rw [hs_img, Measure.addHaar_image_continuousLinearEquiv]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  have hle := le_distributionalVariation (μ := volume) φ hφ_norm (s.indicator fun _ ↦ (1 : ℝ))
  rwa [hint, mul_comm, ENNReal.ofReal_mul (div_nonneg htr hRpos.le),
    ENNReal.ofReal_toReal hvol_lt_top.ne] at hle
/-- **Sharp trace lower bound on the perimeter of `e.symm ⁻¹' Metric.ball 0 1`**. -/
theorem perimeter_preimage_ball_ge (e : E ≃L[ℝ] E) (htr : 0 ≤ LinearMap.trace ℝ E
    e.symm.toLinearMap) : ENNReal.ofReal (LinearMap.trace ℝ E e.symm.toLinearMap) * volume (e.symm
    ⁻¹' Metric.ball (0 : E) 1) ≤ perimeter volume (e.symm ⁻¹' Metric.ball (0 : E) 1) := by
  set s : Set E := e.symm ⁻¹' Metric.ball (0 : E) 1
  set tr : ℝ := LinearMap.trace ℝ E e.symm.toLinearMap
  have hs_img : s = e '' Metric.ball (0 : E) 1 := (e.toEquiv.image_eq_preimage_symm _).symm
  have hvol_lt_top : volume s < ⊤ := by
    rw [hs_img, Measure.addHaar_image_continuousLinearEquiv]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  have hlim : Tendsto (fun k : ℕ ↦ ENNReal.ofReal (tr / (1 + 1 / (k + 1 : ℝ))) * volume s)
      atTop (𝓝 (ENNReal.ofReal (tr / 1) * volume s)) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hvol_lt_top.ne)
    refine (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.div ?_ one_ne_zero)
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [div_one] at hlim
  exact le_of_tendsto' hlim fun k ↦
    perimeter_preimage_ball_ge_of_gt e htr (lt_add_of_pos_right 1 (by positivity))
/-- Coordinate diagonal continuous linear map `x ↦ (i ↦ w i * x i)` on `ℝ^n`. -/
noncomputable def diagLinearMap {n : ℕ} (w : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) :=
  ((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Matrix.toLin' (Matrix.diagonal w)).toContinuousLinearMap).comp
    (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
@[simp] theorem diagLinearMap_apply {n : ℕ} (w : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin
    n) : diagLinearMap w x i = w i * x i := by
  simp [diagLinearMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
theorem diagLinearMap_comp {n : ℕ} (u v : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) : diagLinearMap
    u (diagLinearMap v x) = diagLinearMap (fun i ↦ u i * v i) x := by ext i; simp [mul_assoc]
@[simp] theorem diagLinearMap_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : diagLinearMap (fun _ ↦ (1
    : ℝ)) x = x := by ext i; simp
/-- Coordinate diagonal continuous linear equivalence on `ℝ^n` when `∀ i, w i ≠ 0`. -/
noncomputable def diagLinearEquiv {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) : EuclideanSpace ℝ
    (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearEquiv.equivOfInverse (diagLinearMap w) (diagLinearMap fun i ↦ (w i)⁻¹)
    (fun x ↦ by rw [diagLinearMap_comp]; simp [inv_mul_cancel₀ (hw _)])
    (fun x ↦ by rw [diagLinearMap_comp]; simp [mul_inv_cancel₀ (hw _)])
theorem det_diagLinearMap {n : ℕ} (w : Fin n → ℝ) : LinearMap.det (diagLinearMap w).toLinearMap = ∏
    i, w i := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv
  have hconj : (diagLinearMap w).toLinearMap =
      e.symm.toLinearMap ∘ₗ Matrix.toLin' (Matrix.diagonal w) ∘ₗ e.symm.symm.toLinearMap := rfl
  rw [hconj, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_diagonal]
theorem trace_diagLinearMap {n : ℕ} (w : Fin n → ℝ) : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
    (diagLinearMap w).toLinearMap = ∑ i, w i := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
/-- The open axis-aligned `n`-dimensional ellipsoid `{x ∈ ℝ^n | ∑ i, (x i / w i)² < 1}`. -/
def euclideanEllipsoid {n : ℕ} (w : Fin n → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x : EuclideanSpace ℝ (Fin n) | ∑ i : Fin n, (x i / w i) ^ 2 < 1}
theorem euclideanEllipsoid_eq_preimage_ball {n : ℕ} (w : Fin n → ℝ) : euclideanEllipsoid w =
    diagLinearMap (fun i ↦ (w i)⁻¹) ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  ext x; simp only [euclideanEllipsoid, mem_ofPred_eq, mem_preimage, mem_ball_zero_iff]
  rw [← sq_lt_one_iff₀ (norm_nonneg _), PiLp.norm_sq_eq_of_L2]
  have hsum : (∑ i : Fin n, ‖(diagLinearMap (fun j ↦ (w j)⁻¹) x).ofLp i‖ ^ 2) =
      ∑ i : Fin n, (x i / w i) ^ 2 := Finset.sum_congr rfl fun i _ ↦ by
    change ‖diagLinearMap (fun j ↦ (w j)⁻¹) x i‖ ^ 2 = (x i / w i) ^ 2
    rw [diagLinearMap_apply, Real.norm_eq_abs, sq_abs, div_eq_inv_mul]
  rw [hsum]
theorem isOpen_euclideanEllipsoid {n : ℕ} (w : Fin n → ℝ) : IsOpen (euclideanEllipsoid w) := by
  rw [euclideanEllipsoid_eq_preimage_ball]
  exact Metric.isOpen_ball.preimage (diagLinearMap _).continuous
theorem measurableSet_euclideanEllipsoid {n : ℕ} (w : Fin n → ℝ) : MeasurableSet (euclideanEllipsoid
    w) := (isOpen_euclideanEllipsoid w).measurableSet
theorem euclideanEllipsoid_eq_image_ball {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, w i ≠ 0) :
    euclideanEllipsoid w = (diagLinearEquiv w hw) '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  (euclideanEllipsoid_eq_preimage_ball w).trans
    ((diagLinearEquiv w hw).toEquiv.image_eq_preimage_symm _).symm
theorem euclideanEllipsoid_const {n : ℕ} {r : ℝ} (hr : 0 < r) : euclideanEllipsoid (fun _ : Fin n ↦
    r) = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
  ext x; simp only [euclideanEllipsoid, mem_ofPred_eq, mem_ball_zero_iff]
  rw [← div_lt_one hr, ← sq_lt_one_iff₀ (div_nonneg (norm_nonneg x) hr.le), div_pow,
    PiLp.norm_sq_eq_of_L2]
  have hsum : (∑ i : Fin n, ‖x.ofLp i‖ ^ 2) / r ^ 2 = ∑ i : Fin n, (x i / r) ^ 2 := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ ↦ ?_
    change ‖x i‖ ^ 2 / r ^ 2 = (x i / r) ^ 2; rw [Real.norm_eq_abs, sq_abs, div_pow]
  rw [hsum]
/-- **Exact volume of an `n`-dimensional ellipsoid** (`∀ i, 0 < w i`): `volume (euclideanEllipsoid
w) = (∏ i, w i) * volume (Metric.ball 0 1)`. -/
theorem volume_euclideanEllipsoid {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) : volume
    (euclideanEllipsoid w) = ENNReal.ofReal (∏ i, w i) * volume (Metric.ball (0 : EuclideanSpace ℝ
    (Fin n)) 1) := by
  rw [euclideanEllipsoid_eq_image_ball (fun i ↦ (hw i).ne'),
    Measure.addHaar_image_continuousLinearEquiv]
  change ENNReal.ofReal |LinearMap.det (diagLinearMap w).toLinearMap| * _ = _
  rw [det_diagLinearMap, abs_of_nonneg (Finset.prod_nonneg fun i _ ↦ (hw i).le)]
theorem perimeter_euclideanEllipsoid_lt_top {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, w i ≠ 0) : perimeter
    volume (euclideanEllipsoid w) < ⊤ := by
  rw [euclideanEllipsoid_eq_image_ball hw]
  exact perimeter_image_continuousLinearEquiv_lt_top (diagLinearEquiv w hw)
    (perimeter_ball_lt_top 0 1)
theorem hasFinitePerimeter_euclideanEllipsoid {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, w i ≠ 0) :
    HasFinitePerimeter volume (euclideanEllipsoid w) :=
  ⟨(measurableSet_euclideanEllipsoid w).nullMeasurableSet, perimeter_euclideanEllipsoid_lt_top hw⟩
theorem sum_inv_mul_prod_eq_sum_prod_erase {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, w i ≠ 0) : (∑ i : Fin
    n, (w i)⁻¹) * (∏ j : Fin n, w j) = ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, w j := by
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ i), ← mul_assoc,
    inv_mul_cancel₀ (hw i), one_mul]
/-- **Codimension-1 semi-axis product lower bound on ellipsoid perimeter**: `ENNReal.ofReal (∑ i, ∏
j ≠ i, w j) * volume (Metric.ball 0 1) ≤ perimeter volume (euclideanEllipsoid w)`. -/
theorem perimeter_euclideanEllipsoid_ge {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) : ENNReal.ofReal
    (∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, w j) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin
    n)) 1) ≤ perimeter volume (euclideanEllipsoid w) := by
  have hne : ∀ i, w i ≠ 0 := fun i ↦ (hw i).ne'
  have htr : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (diagLinearEquiv w hne).symm.toLinearMap = ∑ i, (w i)⁻¹ :=
    trace_diagLinearMap fun i ↦ (w i)⁻¹
  have hle := perimeter_preimage_ball_ge (diagLinearEquiv w hne)
    (htr ▸ Finset.sum_nonneg fun i _ ↦ inv_nonneg.2 (hw i).le)
  change ENNReal.ofReal (LinearMap.trace ℝ _ (diagLinearEquiv w hne).symm.toLinearMap) *
      volume (diagLinearMap (fun i ↦ (w i)⁻¹) ⁻¹' Metric.ball 0 1) ≤
    perimeter volume (diagLinearMap (fun i ↦ (w i)⁻¹) ⁻¹' Metric.ball 0 1) at hle
  rwa [htr, ← euclideanEllipsoid_eq_preimage_ball, volume_euclideanEllipsoid hw, ← mul_assoc,
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ ↦ inv_nonneg.2 (hw i).le),
    sum_inv_mul_prod_eq_sum_prod_erase hne] at hle
/-- **Explicit formula for `isoperimetricBound (euclideanEllipsoid w)`** (`1 ≤ n`, `∀ i, 0 < w i`):
`isoperimetricBound (euclideanEllipsoid w) = n * (∏ i, w i)^((n - 1) / n) * volume (Metric.ball 0
1)`. -/
theorem isoperimetricBound_euclideanEllipsoid {n : ℕ} (hn : 1 ≤ n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w
    i) : isoperimetricBound (euclideanEllipsoid w) = ENNReal.ofReal ((n : ℝ) * (∏ i, w i) ^ (((n :
    ℝ) - 1) / (n : ℝ))) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.finrank_pos_iff.1 (by omega : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
  rw [isoperimetricBound_of_volume_eq (Finset.prod_nonneg fun i _ ↦ (hw i).le)
    (volume_euclideanEllipsoid hw), hfin]
theorem finrank_mul_prod_rpow_le_and_eq_iff {n : ℕ} (hn : 1 ≤ n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    : ((n : ℝ) * (∏ i, w i) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, w
    j) ∧ ((n : ℝ) * (∏ i, w i) ^ (((n : ℝ) - 1) / (n : ℝ)) = ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i,
    w j ↔ ∀ i j : Fin n, w i = w j) := by
  obtain ⟨hle, heq⟩ := geom_mean_face_le_and_eq_iff (by omega : 0 < n) hw
  exact ⟨by linarith, ⟨fun h ↦ heq.1 (by linarith), fun h ↦ by linarith [heq.2 h]⟩⟩
/-- **Unconditional Euclidean isoperimetric inequality for all axis-aligned ellipsoids**. -/
theorem isoperimetricBound_euclideanEllipsoid_le_perimeter {n : ℕ} (hn : 1 ≤ n) {w : Fin n → ℝ} (hw
    : ∀ i, 0 < w i) : isoperimetricBound (euclideanEllipsoid w) ≤ perimeter volume
    (euclideanEllipsoid w) := by
  rw [isoperimetricBound_euclideanEllipsoid hn hw]
  exact (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (finrank_mul_prod_rpow_le_and_eq_iff hn hw).1)
    (by positivity)).trans (perimeter_euclideanEllipsoid_ge hw)
/-- **Strict Euclidean isoperimetric inequality for every non-spherical ellipsoid** (`1 ≤ n`, `∀ i,
0 < w i`, `∃ i j, w i ≠ w j`): `isoperimetricBound (euclideanEllipsoid w) < perimeter volume
(euclideanEllipsoid w)`. -/
theorem isoperimetricBound_euclideanEllipsoid_lt_perimeter {n : ℕ} (hn : 1 ≤ n) {w : Fin n → ℝ} (hw
    : ∀ i, 0 < w i) (hne : ∃ i j, w i ≠ w j) : isoperimetricBound (euclideanEllipsoid w) < perimeter
    volume (euclideanEllipsoid w) := by
  obtain ⟨hle, heq_iff⟩ := finrank_mul_prod_rpow_le_and_eq_iff hn hw
  have hne_val : (n : ℝ) * (∏ i, w i) ^ (((n : ℝ) - 1) / (n : ℝ)) ≠
      ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, w j := by
    intro heq; obtain ⟨i, j, hij⟩ := hne; exact hij (heq_iff.1 heq i j)
  have hlt : (n : ℝ) * (∏ i, w i) ^ (((n : ℝ) - 1) / (n : ℝ)) <
      ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, w j := lt_of_le_of_ne hle hne_val
  have hsum_pos : 0 < ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, w j :=
    (mul_pos (Nat.cast_pos.2 (by omega))
      (Real.rpow_pos_of_pos (Finset.prod_pos fun i _ ↦ hw i) _)).trans hlt
  have hball_pos : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ zero_lt_one).ne'
  rw [isoperimetricBound_euclideanEllipsoid hn hw, mul_comm]
  refine (ENNReal.mul_lt_mul_right hball_pos measure_ball_lt_top.ne
    ((ENNReal.ofReal_lt_ofReal_iff hsum_pos).2 hlt)).trans_le ?_
  rw [mul_comm]; exact perimeter_euclideanEllipsoid_ge hw
/-- **Strict positivity of the isoperimetric deficit of every non-spherical ellipsoid**. -/
theorem isoperimetricDeficit_euclideanEllipsoid_pos {n : ℕ} (hn : 1 ≤ n) {w : Fin n → ℝ} (hw : ∀ i,
    0 < w i) (hne : ∃ i j, w i ≠ w j) : 0 < isoperimetricDeficit (euclideanEllipsoid w) :=
  isoperimetricDeficit_pos_of_lt (perimeter_euclideanEllipsoid_lt_top fun i ↦ (hw i).ne')
    (isoperimetricBound_euclideanEllipsoid_lt_perimeter hn hw hne)
/-- **Ellipsoid isoperimetric equality rigidity (`1 ≤ n`)**: an axis-aligned ellipsoid with positive
semi-axes `w` achieves Euclidean isoperimetric equality if and only if all semi-axes are equal. -/
theorem isoperimetricBound_euclideanEllipsoid_eq_perimeter_iff {n : ℕ} (hn : 1 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) : isoperimetricBound (euclideanEllipsoid w) = perimeter volume
    (euclideanEllipsoid w) ↔ ∀ i j, w i = w j := by
  refine ⟨fun heq ↦ by by_contra! hne; exact
    (isoperimetricBound_euclideanEllipsoid_lt_perimeter hn hw hne).ne heq, fun hall ↦ ?_⟩
  let i₀ : Fin n := ⟨0, by omega⟩
  have hw_eq : w = fun _ ↦ w i₀ := funext fun i ↦ hall i i₀
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.finrank_pos_iff.1 (by rw [finrank_euclideanSpace_fin]; omega)
  rw [hw_eq, euclideanEllipsoid_const (hw i₀), perimeter_ball_eq_isoperimetricBound 0 (hw i₀)]

end Ellipsoids

/-! ### Section 4: Planar ellipses (`planarEllipse a b`) and strict inequality for `a ≠ b` -/

section PlanarEllipse

/-- The open planar elliptical disk `{x ∈ ℝ² | (x 0 / a)² + (x 1 / b)² < 1}`. -/
def planarEllipse (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x : EuclideanSpace ℝ (Fin 2) | (x 0 / a) ^ 2 + (x 1 / b) ^ 2 < 1}
theorem planarEllipse_eq_euclideanEllipsoid (a b : ℝ) : planarEllipse a b = euclideanEllipsoid ![a,
    b] := by ext x; simp [planarEllipse, euclideanEllipsoid, Fin.sum_univ_two]
theorem isOpen_planarEllipse (a b : ℝ) : IsOpen (planarEllipse a b) := by
  rw [planarEllipse_eq_euclideanEllipsoid]; exact isOpen_euclideanEllipsoid ![a, b]
theorem measurableSet_planarEllipse (a b : ℝ) : MeasurableSet (planarEllipse a b) :=
  (isOpen_planarEllipse a b).measurableSet
theorem planarEllipse_self {a : ℝ} (ha : 0 < a) : planarEllipse a a = Metric.ball (0 :
    EuclideanSpace ℝ (Fin 2)) a := by
  have hconst : (![a, a] : Fin 2 → ℝ) = fun _ ↦ a := by ext i; fin_cases i <;> rfl
  rw [planarEllipse_eq_euclideanEllipsoid, hconst, euclideanEllipsoid_const ha]
theorem perimeter_planarEllipse_self_eq_isoperimetricBound {a : ℝ} (ha : 0 < a) : perimeter volume
    (planarEllipse a a) = isoperimetricBound (planarEllipse a a) ∧ isoperimetricDeficit
    (planarEllipse a a) = 0 := by
  have : Nontrivial (EuclideanSpace ℝ (Fin 2)) :=
    Module.finrank_pos_iff.1 (by rw [finrank_euclideanSpace_fin]; omega)
  rw [planarEllipse_self ha]
  exact ⟨perimeter_ball_eq_isoperimetricBound 0 ha, isoperimetricDeficit_ball_eq_zero 0 ha⟩
/-- **Exact area of `planarEllipse a b`**: `volume (planarEllipse a b) = ENNReal.ofReal (a * b) *
volume (Metric.ball 0 1)`. -/
theorem volume_planarEllipse {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : volume (planarEllipse a b) =
    ENNReal.ofReal (a * b) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  have hab : ∀ i : Fin 2, 0 < (![a, b] : Fin 2 → ℝ) i := fun i ↦ by fin_cases i <;> assumption
  rw [planarEllipse_eq_euclideanEllipsoid, volume_euclideanEllipsoid hab, Fin.prod_univ_two]; rfl
theorem perimeter_planarEllipse_lt_top {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : perimeter volume
    (planarEllipse a b) < ⊤ := by
  rw [planarEllipse_eq_euclideanEllipsoid]
  exact perimeter_euclideanEllipsoid_lt_top fun i ↦ by fin_cases i <;> assumption
theorem hasFinitePerimeter_planarEllipse {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : HasFinitePerimeter
    volume (planarEllipse a b) :=
  ⟨(measurableSet_planarEllipse a b).nullMeasurableSet, perimeter_planarEllipse_lt_top ha hb⟩
/-- **Explicit formula for `isoperimetricBound (planarEllipse a b)`** (`0 < a`, `0 < b`). -/
theorem isoperimetricBound_planarEllipse {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : isoperimetricBound
    (planarEllipse a b) = ENNReal.ofReal (2 * Real.sqrt (a * b)) * volume (Metric.ball (0 :
    EuclideanSpace ℝ (Fin 2)) 1) := by
  have hab : ∀ i : Fin 2, 0 < (![a, b] : Fin 2 → ℝ) i := fun i ↦ by fin_cases i <;> assumption
  rw [planarEllipse_eq_euclideanEllipsoid, isoperimetricBound_euclideanEllipsoid (by omega) hab,
    Fin.prod_univ_two]
  congr 2; rw [show (((2 : ℕ) : ℝ) - 1) / ((2 : ℕ) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rfl
theorem isoperimetricBound_planarEllipse_eq_unitBall {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    isoperimetricBound (planarEllipse a b) = ENNReal.ofReal (Real.sqrt (a * b)) * perimeter volume
    (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin 2)) :=
    Module.finrank_pos_iff.1 (by rw [finrank_euclideanSpace_fin]; omega)
  rw [isoperimetricBound_planarEllipse ha hb, perimeter_ball_eq_unitBall 0 zero_lt_one,
    finrank_euclideanSpace_fin, ← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 2; ring
/-- **Arithmetic-mean lower bound on planar ellipse perimeter**. -/
theorem arith_mean_le_perimeter_planarEllipse {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : ENNReal.ofReal
    (a + b) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≤ perimeter volume
    (planarEllipse a b) := by
  have hab : ∀ i : Fin 2, 0 < (![a, b] : Fin 2 → ℝ) i := fun i ↦ by fin_cases i <;> assumption
  have hle := perimeter_euclideanEllipsoid_ge hab
  have h0 : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  have h1 : Finset.univ.erase (1 : Fin 2) = {0} := by decide
  rw [← planarEllipse_eq_euclideanEllipsoid, Fin.sum_univ_two, h0, h1, Finset.prod_singleton,
    Finset.prod_singleton] at hle
  rwa [show (![a, b] : Fin 2 → ℝ) 1 + (![a, b] : Fin 2 → ℝ) 0 = a + b from add_comm b a] at hle
theorem arith_mean_mul_perimeter_unitBall_le_perimeter_planarEllipse {a b : ℝ} (ha : 0 < a) (hb : 0
    < b) : ENNReal.ofReal ((a + b) / 2) * perimeter volume (Metric.ball (0 : EuclideanSpace ℝ (Fin
    2)) 1) ≤ perimeter volume (planarEllipse a b) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin 2)) :=
    Module.finrank_pos_iff.1 (by rw [finrank_euclideanSpace_fin]; omega)
  rw [perimeter_ball_eq_unitBall 0 zero_lt_one, finrank_euclideanSpace_fin, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  rw [show (a + b) / 2 * (((2 : ℕ) : ℝ) * 1 ^ (2 - 1)) = a + b by push_cast; ring]
  exact arith_mean_le_perimeter_planarEllipse ha hb
/-- **Unconditional planar isoperimetric inequality for all ellipses** (`0 < a`, `0 < b`). -/
theorem isoperimetricBound_planarEllipse_le_perimeter {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    isoperimetricBound (planarEllipse a b) ≤ perimeter volume (planarEllipse a b) := by
  have hab : ∀ i : Fin 2, 0 < (![a, b] : Fin 2 → ℝ) i := fun i ↦ by fin_cases i <;> assumption
  rw [planarEllipse_eq_euclideanEllipsoid]
  exact isoperimetricBound_euclideanEllipsoid_le_perimeter (by omega) hab
/-- **Strict planar isoperimetric inequality for every non-circular ellipse** (`a ≠ b`). -/
theorem isoperimetricBound_planarEllipse_lt_perimeter {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠
    b) : isoperimetricBound (planarEllipse a b) < perimeter volume (planarEllipse a b) := by
  have hab : ∀ i : Fin 2, 0 < (![a, b] : Fin 2 → ℝ) i := fun i ↦ by fin_cases i <;> assumption
  rw [planarEllipse_eq_euclideanEllipsoid]
  exact isoperimetricBound_euclideanEllipsoid_lt_perimeter (by omega) hab ⟨0, 1, hne⟩
/-- **Strict positivity of the isoperimetric deficit of every non-circular planar ellipse**. -/
theorem isoperimetricDeficit_planarEllipse_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) : 0
    < isoperimetricDeficit (planarEllipse a b) :=
  isoperimetricDeficit_pos_of_lt (perimeter_planarEllipse_lt_top ha.ne' hb.ne')
    (isoperimetricBound_planarEllipse_lt_perimeter ha hb hne)
/-- **Planar ellipse isoperimetric equality rigidity**: `planarEllipse a b` (`0 < a`, `0 < b`)
achieves planar isoperimetric equality if and only if `a = b`. -/
theorem isoperimetricBound_planarEllipse_eq_perimeter_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    isoperimetricBound (planarEllipse a b) = perimeter volume (planarEllipse a b) ↔ a = b := by
  refine ⟨fun heq ↦ ?_, fun h ↦ h ▸ (perimeter_planarEllipse_self_eq_isoperimetricBound ha).1.symm⟩
  by_contra hne; exact (isoperimetricBound_planarEllipse_lt_perimeter ha hb hne).ne heq
/-- **Planar ellipse deficit-zero characterization**: `isoperimetricDeficit (planarEllipse a b) = 0`
if and only if `a = b` (`0 < a`, `0 < b`). -/
theorem isoperimetricDeficit_planarEllipse_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    isoperimetricDeficit (planarEllipse a b) = 0 ↔ a = b := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ (perimeter_planarEllipse_self_eq_isoperimetricBound ha).2⟩
  by_contra hne; exact (isoperimetricDeficit_planarEllipse_pos ha hb hne).ne' h0
end PlanarEllipse
end TauCeti
