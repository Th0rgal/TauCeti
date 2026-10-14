/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MeanInequalities
public import TauCeti.MeasureTheory.Measure.BallPerimeter
public import TauCeti.MeasureTheory.Measure.BoxPerimeter
public import TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
public import TauCeti.MeasureTheory.Measure.ReducedBoundary
import all TauCeti.MeasureTheory.Measure.BallPerimeter
import all TauCeti.MeasureTheory.Measure.BoxPerimeter
import all TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
import all TauCeti.MeasureTheory.Measure.EssentialBoundary
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.PerimeterTransport

/-!
# Euclidean Isoperimetric Bound, Deficit, and Strict Domain Examples

This file defines the sharp Euclidean isoperimetric lower-bound functional `isoperimetricBound` and
the isoperimetric deficit `isoperimetricDeficit` in finite-dimensional real inner product spaces,
and establishes exact equality and strict inequality across benchmark geometric domains:

1. **Euclidean isoperimetric lower-bound and deficit functional**:
   `isoperimetricBound`, `isoperimetricDeficit`, invariance under a.e. equality, translation, and
   linear isometries, homogeneous scaling under dilations (`isoperimetricBound_smul`), exact
   equality for open and closed balls (`perimeter_ball_eq_isoperimetricBound`,
   `isoperimetricDeficit_ball_eq_zero`), and the punctured ball example
   (`perimeter_punctured_ball_eq_isoperimetricBound`, `punctured_ball_ne_ball`,
   `punctured_ball_ne_closedBall`).
2. **Strict inequality for concentric annuli**:
   `volume_annulus`, `isoperimetricBound_annulus`, `isoperimetricBound_annulus_lt_perimeter`, and
   `isoperimetricDeficit_annulus_pos`.
3. **Strict inequality for separated unions of two positive-radius balls**:
   strict subadditivity `rpow_add_lt_add_rpow` of `t ↦ t ^ α` for `0 < α < 1`, exact perimeter
   additivity `perimeter_ball_union_ball_of_disjoint_closedBall`, and strict inequality
   `isoperimetricBound_ball_union_ball_lt_perimeter_of_disjoint_closedBall` and
   `isoperimetricDeficit_ball_union_ball_pos_of_disjoint_closedBall`.
4. **Sharp box AM–GM inequality, cube rigidity, `ω_n < 2^n`, and strict inequality for boxes**:
   `two_mul_finrank_mul_volume_rpow_le_perimeter_euclideanOpenBox`, cube equality characterization
   `two_mul_finrank_mul_volume_rpow_eq_perimeter_euclideanOpenBox_iff`, strict unit-ball-in-cube
   volume bound `volume_unitBall_lt_two_pow` (`2 ≤ n`), and strict Euclidean isoperimetric
   inequality `isoperimetricBound_euclideanOpenBox_lt_perimeter` and
   `isoperimetricDeficit_euclideanOpenBox_pos` for every nondegenerate `n`-box (`2 ≤ n`) and
   planar rectangle (`n = 2`).
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology
open TauCeti.MeasureTheory

namespace TauCeti

/-! ### Section 1: Euclidean isoperimetric bound, deficit, balls, and punctured balls -/

section IsoperimetricFunctional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Sharp Euclidean isoperimetric lower-bound functional** on `E`:
`isoperimetricBound s = n * |B(0, 1)|^(1 / n) * |s|^((n - 1) / n)` (`n = Module.finrank ℝ E`). -/
def isoperimetricBound (s : Set E) : ℝ≥0∞ :=
  (Module.finrank ℝ E : ℝ≥0∞) *
    (volume (Metric.ball (0 : E) 1)) ^ (1 / (Module.finrank ℝ E : ℝ)) *
    (volume s) ^ (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ))

/-- **Euclidean isoperimetric deficit** of `s ⊆ E`:
`isoperimetricDeficit s = (perimeter volume s).toReal - (isoperimetricBound s).toReal`. -/
def isoperimetricDeficit (s : Set E) : ℝ :=
  (perimeter volume s).toReal - (isoperimetricBound s).toReal

/-- When `2 ≤ Module.finrank ℝ E` and `volume s = 0`, `isoperimetricBound s = 0`. -/
theorem isoperimetricBound_of_volume_eq_zero (hn : 2 ≤ Module.finrank ℝ E) {s : Set E}
    (hs : volume s = 0) : isoperimetricBound s = 0 := by
  have hexp : 0 < ((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ) := by
    have : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hn
    exact div_pos (by linarith) (by linarith)
  simp [isoperimetricBound, hs, ENNReal.zero_rpow_of_pos hexp]

@[simp] theorem isoperimetricBound_empty (hn : 2 ≤ Module.finrank ℝ E) :
    isoperimetricBound (∅ : Set E) = 0 :=
  isoperimetricBound_of_volume_eq_zero hn measure_empty

/-- `isoperimetricBound` is monotone with respect to set inclusion. -/
theorem isoperimetricBound_mono {s t : Set E} (hst : s ⊆ t) :
    isoperimetricBound s ≤ isoperimetricBound t := by
  by_cases hn : Module.finrank ℝ E = 0
  · simp [isoperimetricBound, hn]
  · have hn1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have hexp : 0 ≤ ((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ) :=
      div_nonneg (by linarith) (by linarith)
    unfold isoperimetricBound; gcongr

/-- **A.e.-invariance of `isoperimetricBound`**. -/
theorem isoperimetricBound_congr_ae {s t : Set E} (hst : s =ᵐ[volume] t) :
    isoperimetricBound s = isoperimetricBound t := by
  simp [isoperimetricBound, measure_congr hst]

/-- **A.e.-invariance of `isoperimetricDeficit`**. -/
theorem isoperimetricDeficit_congr_ae {s t : Set E} (hst : s =ᵐ[volume] t) :
    isoperimetricDeficit s = isoperimetricDeficit t := by
  simp [isoperimetricDeficit, perimeter_congr_ae hst, isoperimetricBound_congr_ae hst]

@[simp] theorem isoperimetricBound_preimage_add_left (c : E) (s : Set E) :
    isoperimetricBound ((fun x ↦ c + x) ⁻¹' s) = isoperimetricBound s := by
  simp [isoperimetricBound, measure_preimage_add]

@[simp] theorem isoperimetricBound_vadd (c : E) (s : Set E) :
    isoperimetricBound (c +ᵥ s) = isoperimetricBound s := by
  rw [← preimage_vadd_neg]; simp_rw [vadd_eq_add]; exact isoperimetricBound_preimage_add_left (-c) s

@[simp] theorem isoperimetricDeficit_vadd (c : E) (s : Set E) :
    isoperimetricDeficit (c +ᵥ s) = isoperimetricDeficit s := by
  rw [isoperimetricDeficit, isoperimetricDeficit, isoperimetricBound_vadd, ← preimage_vadd_neg]
  simp_rw [vadd_eq_add]; rw [perimeter_preimage_add_left]

@[simp] theorem isoperimetricBound_preimage_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    isoperimetricBound (L ⁻¹' s) = isoperimetricBound s := by
  have hvol : volume (L ⁻¹' s) = volume s :=
    L.measurePreserving.measure_preimage_emb L.toHomeomorph.toMeasurableEquiv.measurableEmbedding s
  simp [isoperimetricBound, hvol]

@[simp] theorem isoperimetricDeficit_preimage_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    isoperimetricDeficit (L ⁻¹' s) = isoperimetricDeficit s := by
  simp [isoperimetricDeficit, perimeter_preimage_linearIsometryEquiv]

/-- **Master evaluation formula for `isoperimetricBound`** whenever `volume s` is a nonnegative
multiple `ENNReal.ofReal v * volume (Metric.ball 0 1)` of unit-ball volume (`[Nontrivial E]`). -/
theorem isoperimetricBound_of_volume_eq [Nontrivial E] {s : Set E} {v : ℝ} (hv : 0 ≤ v)
    (hs : volume s = ENNReal.ofReal v * volume (Metric.ball (0 : E) 1)) :
    isoperimetricBound s =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) *
        v ^ (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ))) *
        volume (Metric.ball (0 : E) 1) := by
  set n : ℕ := Module.finrank ℝ E
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.2 Module.finrank_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Module.finrank_pos : 1 ≤ n)
  have hexp : 0 ≤ ((n : ℝ) - 1) / (n : ℝ) := div_nonneg (by linarith) hn_pos.le
  have hsum : 1 / (n : ℝ) + ((n : ℝ) - 1) / (n : ℝ) = 1 := by
    rw [← add_div, add_sub_cancel, div_self hn_pos.ne']
  set ω : ℝ≥0∞ := volume (Metric.ball (0 : E) 1)
  have hω_pow : ω ^ (1 / (n : ℝ)) * ω ^ (((n : ℝ) - 1) / (n : ℝ)) = ω := by
    rw [← ENNReal.rpow_add_of_nonneg (1 / (n : ℝ)) (((n : ℝ) - 1) / (n : ℝ))
      (by positivity) hexp, hsum, ENNReal.rpow_one]
  calc isoperimetricBound s
      = (n : ℝ≥0∞) * ω ^ (1 / (n : ℝ)) *
          (ENNReal.ofReal (v ^ (((n : ℝ) - 1) / (n : ℝ))) * ω ^ (((n : ℝ) - 1) / (n : ℝ))) := by
        rw [isoperimetricBound, hs, ENNReal.mul_rpow_of_nonneg _ _ hexp,
          ENNReal.ofReal_rpow_of_nonneg hv hexp]
    _ = ((n : ℝ≥0∞) * ENNReal.ofReal (v ^ (((n : ℝ) - 1) / (n : ℝ)))) *
          (ω ^ (1 / (n : ℝ)) * ω ^ (((n : ℝ) - 1) / (n : ℝ))) := by ring
    _ = ENNReal.ofReal ((n : ℝ) * v ^ (((n : ℝ) - 1) / (n : ℝ))) * ω := by
        rw [hω_pow, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

/-- **Homogeneous scaling of `isoperimetricBound` under dilations** (`r ≠ 0`):
`isoperimetricBound (r • s) = |r|^(n - 1) * isoperimetricBound s`. -/
theorem isoperimetricBound_smul [Nontrivial E] {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    isoperimetricBound (r • s) =
      ENNReal.ofReal (|r| ^ (Module.finrank ℝ E - 1)) * isoperimetricBound s := by
  set n : ℕ := Module.finrank ℝ E
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.2 Module.finrank_pos
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hexp : 0 ≤ ((n : ℝ) - 1) / (n : ℝ) :=
    div_nonneg (sub_nonneg.2 (by exact_mod_cast hn1)) hn_pos.le
  have hr_abs : 0 < |r| := abs_pos.2 hr
  have hrpow : (|r| ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) = |r| ^ (n - 1) := by
    rw [← Real.rpow_natCast |r| n, ← Real.rpow_mul hr_abs.le,
      mul_div_cancel₀ _ hn_pos.ne', ← Nat.cast_one, ← Nat.cast_sub hn1, Real.rpow_natCast]
  rw [isoperimetricBound, isoperimetricBound, Measure.addHaar_smul,
    ENNReal.mul_rpow_of_nonneg _ _ hexp,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hexp, abs_pow, hrpow]
  ring

theorem isoperimetricBound_lt_top_of_volume_lt_top {s : Set E} (hs : volume s < ⊤) :
    isoperimetricBound s < ⊤ := by
  unfold isoperimetricBound
  by_cases hn : Module.finrank ℝ E = 0
  · simp [hn]
  · have hn1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) measure_ball_lt_top.ne))
      (ENNReal.rpow_lt_top_of_nonneg (div_nonneg (by linarith) (by linarith)) hs.ne)

theorem toReal_isoperimetricBound (s : Set E) :
    (isoperimetricBound s).toReal =
      (Module.finrank ℝ E : ℝ) *
        (volume (Metric.ball (0 : E) 1)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) *
        (volume s).toReal ^ (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ)) := by
  simp [isoperimetricBound, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]

theorem isoperimetricDeficit_eq_zero_of_perimeter_eq {s : Set E}
    (h : perimeter volume s = isoperimetricBound s) :
    isoperimetricDeficit s = 0 := by simp [isoperimetricDeficit, h]

theorem isoperimetricDeficit_pos_of_lt {s : Set E} (hfin : perimeter volume s < ⊤)
    (hlt : isoperimetricBound s < perimeter volume s) :
    0 < isoperimetricDeficit s :=
  sub_pos.2 ((ENNReal.toReal_lt_toReal (hlt.trans hfin).ne hfin.ne).2 hlt)

/-- **Exact isoperimetric equality for open balls**: for `c : E` and `0 < r` (`[Nontrivial E]`),
`perimeter volume (Metric.ball c r) = isoperimetricBound (Metric.ball c r)`. -/
theorem perimeter_ball_eq_isoperimetricBound [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter volume (Metric.ball c r) = isoperimetricBound (Metric.ball c r) := by
  set n : ℕ := Module.finrank ℝ E
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.2 Module.finrank_pos
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hrpow : (r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) = r ^ (n - 1) := by
    rw [← Real.rpow_natCast r n, ← Real.rpow_mul hr.le,
      mul_div_cancel₀ _ hn_pos.ne', ← Nat.cast_one, ← Nat.cast_sub hn1, Real.rpow_natCast]
  rw [perimeter_ball_eq_unitBall c hr,
    isoperimetricBound_of_volume_eq (pow_nonneg hr.le n) (Measure.addHaar_ball volume c hr.le),
    hrpow]

/-- **Exact isoperimetric equality for closed balls** (`0 < r`, `[Nontrivial E]`). -/
theorem perimeter_closedBall_eq_isoperimetricBound [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter volume (Metric.closedBall c r) = isoperimetricBound (Metric.closedBall c r) := by
  rw [perimeter_closedBall_eq_ball, isoperimetricBound_congr_ae (closedBall_ae_eq_ball c r),
    perimeter_ball_eq_isoperimetricBound c hr]

@[simp] theorem isoperimetricDeficit_ball_eq_zero [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    isoperimetricDeficit (Metric.ball c r) = 0 :=
  isoperimetricDeficit_eq_zero_of_perimeter_eq (perimeter_ball_eq_isoperimetricBound c hr)

@[simp] theorem isoperimetricDeficit_closedBall_eq_zero [Nontrivial E] (c : E) {r : ℝ}
    (hr : 0 < r) : isoperimetricDeficit (Metric.closedBall c r) = 0 :=
  isoperimetricDeficit_eq_zero_of_perimeter_eq (perimeter_closedBall_eq_isoperimetricBound c hr)

/-- **Punctured ball `Metric.ball c r \ {c}`**: `isoperimetricBound` agrees with `ball c r`. -/
theorem isoperimetricBound_punctured_ball [Nontrivial E] (c : E) (r : ℝ) :
    isoperimetricBound (Metric.ball c r \ {c}) = isoperimetricBound (Metric.ball c r) :=
  isoperimetricBound_congr_ae (punctured_ball_ae_eq_ball c r)

/-- **Exact isoperimetric equality for a punctured ball `Metric.ball c r \ {c}`** (`0 < r`). -/
theorem perimeter_punctured_ball_eq_isoperimetricBound [Nontrivial E] (c : E) {r : ℝ}
    (hr : 0 < r) :
    perimeter volume (Metric.ball c r \ {c}) = isoperimetricBound (Metric.ball c r \ {c}) := by
  rw [perimeter_congr_ae (punctured_ball_ae_eq_ball c r), isoperimetricBound_punctured_ball,
    perimeter_ball_eq_isoperimetricBound c hr]

@[simp] theorem isoperimetricDeficit_punctured_ball_eq_zero [Nontrivial E] (c : E) {r : ℝ}
    (hr : 0 < r) : isoperimetricDeficit (Metric.ball c r \ {c}) = 0 :=
  isoperimetricDeficit_eq_zero_of_perimeter_eq (perimeter_punctured_ball_eq_isoperimetricBound c hr)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `0 < r` and `[Nontrivial E]`, `c ∈ interior (closure (Metric.ball c r \ {c}))`. -/
theorem center_mem_interior_closure_punctured_ball [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    c ∈ interior (closure (Metric.ball c r \ {c})) := by
  have hsub : Metric.ball c r ⊆ closure (Metric.ball c r \ {c}) := fun x hx ↦ by
    by_cases hxc : x = c
    · exact hxc ▸ (center_mem_frontier_punctured_ball c hr).1
    · exact subset_closure ⟨hx, hxc⟩
  exact Metric.isOpen_ball.subset_interior_iff.2 hsub (Metric.mem_ball_self hr)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A punctured ball `Metric.ball c r \ {c}` (`0 < r`, `[Nontrivial E]`) is not regular open. -/
theorem not_isRegularOpen_punctured_ball [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    ¬ IsRegularOpen (Metric.ball c r \ {c}) := fun hreg ↦
  (hreg.interior_closure ▸ center_mem_interior_closure_punctured_ball c hr).2 rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A punctured ball `Metric.ball c r \ {c}` (`0 < r`, `[Nontrivial E]`) is not closed. -/
theorem not_isClosed_punctured_ball [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (Metric.ball c r \ {c}) := fun hcl ↦
  (hcl.closure_eq ▸ (center_mem_frontier_punctured_ball c hr).1).2 rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Literal open-ball equality fails for a punctured ball** (`0 < r`, `[Nontrivial E]`). -/
theorem punctured_ball_ne_ball [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) (x : E) (R : ℝ) :
    Metric.ball c r \ {c} ≠ Metric.ball x R :=
  fun heq ↦ not_isRegularOpen_punctured_ball c hr (heq ▸ isRegularOpen_ball x R)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Literal closed-ball equality fails for a punctured ball** (`0 < r`, `[Nontrivial E]`). -/
theorem punctured_ball_ne_closedBall [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) (x : E) (R : ℝ) :
    Metric.ball c r \ {c} ≠ Metric.closedBall x R :=
  fun heq ↦ not_isClosed_punctured_ball c hr (heq ▸ Metric.isClosed_closedBall)

/-- **Complete punctured-ball isoperimetric rigidity package**: `Metric.ball c r \ {c}` (`0 < r`)
achieves exact equality `perimeter = isoperimetricBound` and `isoperimetricDeficit = 0`, satisfies
a.e. ball rigidity `Metric.ball c r \ {c} =ᵐ[volume] Metric.ball c r`, and is literally unequal to
every open ball and every closed ball. -/
theorem punctured_ball_isoperimetric_rigidity [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter volume (Metric.ball c r \ {c}) = isoperimetricBound (Metric.ball c r \ {c}) ∧
      isoperimetricDeficit (Metric.ball c r \ {c}) = 0 ∧
      (Metric.ball c r \ {c} : Set E) =ᵐ[volume] Metric.ball c r ∧
      (∀ x R, Metric.ball c r \ {c} ≠ Metric.ball x R) ∧
      (∀ x R, Metric.ball c r \ {c} ≠ Metric.closedBall x R) :=
  ⟨perimeter_punctured_ball_eq_isoperimetricBound c hr,
    isoperimetricDeficit_punctured_ball_eq_zero c hr,
    punctured_ball_ae_eq_ball c r,
    punctured_ball_ne_ball c hr,
    punctured_ball_ne_closedBall c hr⟩

/-! ### Section 2: Strict isoperimetric inequality for concentric annuli -/

/-- Exact volume of the concentric annulus `Metric.ball c R \ Metric.closedBall c r`
(`0 < r < R`). -/
theorem volume_annulus [Nontrivial E] (c : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    volume (Metric.ball c R \ Metric.closedBall c r) =
      ENNReal.ofReal (R ^ Module.finrank ℝ E - r ^ Module.finrank ℝ E) *
        volume (Metric.ball (0 : E) 1) := by
  have hR : 0 < R := hr.trans hrR
  rw [measure_sdiff (Metric.closedBall_subset_ball hrR)
      Metric.isClosed_closedBall.nullMeasurableSet measure_closedBall_lt_top.ne,
    Measure.addHaar_ball volume c hR.le, Measure.addHaar_closedBall volume c hr.le,
    ← ENNReal.sub_mul (fun _ _ ↦ measure_ball_lt_top.ne),
    ← ENNReal.ofReal_sub _ (pow_nonneg hr.le _)]

/-- Exact perimeter of the open concentric annulus `Metric.ball c R \ Metric.closedBall c r`
(`0 < r < R`) in terms of unit-ball volume. -/
theorem perimeter_ball_diff_closedBall_eq_unitBall [Nontrivial E] (c : E) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    perimeter volume (Metric.ball c R \ Metric.closedBall c r) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) *
        (R ^ (Module.finrank ℝ E - 1) + r ^ (Module.finrank ℝ E - 1))) *
        volume (Metric.ball (0 : E) 1) := by
  rw [perimeter_ball_diff_closedBall c hr hrR, ← perimeter_closedBall_diff_ball c hr hrR,
    perimeter_closedBall_diff_ball_eq_unitBall c hr hrR]

/-- **Isoperimetric lower bound of a concentric annulus `Metric.ball c R \ Metric.closedBall c r`**
(`0 < r < R`). -/
theorem isoperimetricBound_annulus [Nontrivial E] (c : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    isoperimetricBound (Metric.ball c R \ Metric.closedBall c r) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) *
        (R ^ Module.finrank ℝ E - r ^ Module.finrank ℝ E) ^
          (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ))) *
        volume (Metric.ball (0 : E) 1) := by
  have hsub : 0 ≤ R ^ Module.finrank ℝ E - r ^ Module.finrank ℝ E :=
    sub_nonneg.2 (pow_le_pow_left₀ hr.le hrR.le _)
  exact isoperimetricBound_of_volume_eq hsub (volume_annulus c hr hrR)

/-- **Strict Euclidean isoperimetric inequality for every concentric annulus**
`Metric.ball c R \ Metric.closedBall c r` (`0 < r < R`, `[Nontrivial E]`). -/
theorem isoperimetricBound_annulus_lt_perimeter [Nontrivial E] (c : E) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    isoperimetricBound (Metric.ball c R \ Metric.closedBall c r) <
      perimeter volume (Metric.ball c R \ Metric.closedBall c r) := by
  set n : ℕ := Module.finrank ℝ E
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.2 hn1
  have hR : 0 < R := hr.trans hrR
  have hexp : 0 ≤ ((n : ℝ) - 1) / (n : ℝ) :=
    div_nonneg (sub_nonneg.2 (by exact_mod_cast hn1)) hn_pos.le
  have hsub_nonneg : 0 ≤ R ^ n - r ^ n := sub_nonneg.2 (pow_le_pow_left₀ hr.le hrR.le n)
  have hsub_le : R ^ n - r ^ n ≤ R ^ n := sub_le_self _ (pow_nonneg hr.le n)
  have hrpow_le : (R ^ n - r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ R ^ (n - 1) := by
    calc (R ^ n - r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ))
        ≤ (R ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) :=
          Real.rpow_le_rpow hsub_nonneg hsub_le hexp
      _ = R ^ (n - 1) := by
          rw [← Real.rpow_natCast R n, ← Real.rpow_mul hR.le,
            mul_div_cancel₀ _ hn_pos.ne', ← Nat.cast_one, ← Nat.cast_sub hn1, Real.rpow_natCast]
  have hlt_real : (n : ℝ) * (R ^ n - r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) <
      (n : ℝ) * (R ^ (n - 1) + r ^ (n - 1)) :=
    mul_lt_mul_of_pos_left (by linarith [pow_pos hr (n - 1)]) hn_pos
  rw [isoperimetricBound_annulus c hr hrR, perimeter_ball_diff_closedBall_eq_unitBall c hr hrR,
    mul_comm _ (volume (Metric.ball (0 : E) 1)), mul_comm _ (volume (Metric.ball (0 : E) 1))]
  exact ENNReal.mul_lt_mul_right (Metric.measure_ball_pos volume (0 : E) zero_lt_one).ne'
    measure_ball_lt_top.ne ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt_real)

/-- **Strict positivity of the isoperimetric deficit of every concentric annulus** (`0 < r < R`). -/
theorem isoperimetricDeficit_annulus_pos [Nontrivial E] (c : E) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    0 < isoperimetricDeficit (Metric.ball c R \ Metric.closedBall c r) := by
  refine isoperimetricDeficit_pos_of_lt ?_ (isoperimetricBound_annulus_lt_perimeter c hr hrR)
  rw [perimeter_ball_diff_closedBall c hr hrR]
  exact ENNReal.add_lt_top.2 ⟨perimeter_closedBall_lt_top c R, perimeter_ball_lt_top c r⟩

/-! ### Section 3: Strict isoperimetric inequality for separated unions of two balls -/

/-- **Strict subadditivity of `t ↦ t ^ α` for `0 < α < 1`** on positive reals:
`(a + b) ^ α < a ^ α + b ^ α`. -/
theorem rpow_add_lt_add_rpow {a b α : ℝ} (ha : 0 < a) (hb : 0 < b) (_hα0 : 0 < α) (hα1 : α < 1) :
    (a + b) ^ α < a ^ α + b ^ α := by
  have hab : 0 < a + b := add_pos ha hb
  have h1 : a / (a + b) < (a / (a + b)) ^ α := by
    calc a / (a + b) = (a / (a + b)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (a / (a + b)) ^ α := Real.rpow_lt_rpow_of_exponent_gt (div_pos ha hab)
          ((div_lt_one hab).2 (lt_add_of_pos_right a hb)) hα1
  have h2 : b / (a + b) < (b / (a + b)) ^ α := by
    calc b / (a + b) = (b / (a + b)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (b / (a + b)) ^ α := Real.rpow_lt_rpow_of_exponent_gt (div_pos hb hab)
          ((div_lt_one hab).2 (lt_add_of_pos_left b ha)) hα1
  have hsum : 1 < (a / (a + b)) ^ α + (b / (a + b)) ^ α := by
    calc (1 : ℝ) = a / (a + b) + b / (a + b) := by rw [← add_div, div_self hab.ne']
      _ < (a / (a + b)) ^ α + (b / (a + b)) ^ α := add_lt_add h1 h2
  rw [Real.div_rpow ha.le hab.le, Real.div_rpow hb.le hab.le, ← add_div,
    lt_div_iff₀ (Real.rpow_pos_of_pos hab α), one_mul] at hsum
  exact hsum

/-- For `2 ≤ n` and `0 < r₁, r₂`,
`(r₁ ^ n + r₂ ^ n) ^ ((n - 1) / n) < r₁ ^ (n - 1) + r₂ ^ (n - 1)`. -/
theorem pow_add_pow_rpow_div_lt {n : ℕ} (hn : 2 ≤ n) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    (r₁ ^ n + r₂ ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) < r₁ ^ (n - 1) + r₂ ^ (n - 1) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hn1 : 1 ≤ n := by omega
  have hα0 : 0 < ((n : ℝ) - 1) / (n : ℝ) := div_pos (by linarith) hn_pos
  have hα1 : ((n : ℝ) - 1) / (n : ℝ) < 1 := (div_lt_one hn_pos).2 (by linarith)
  have hpow : ∀ {r : ℝ}, 0 < r → (r ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) = r ^ (n - 1) :=
    fun {r} hr ↦ by
      rw [← Real.rpow_natCast r n, ← Real.rpow_mul hr.le,
        mul_div_cancel₀ _ hn_pos.ne', ← Nat.cast_one, ← Nat.cast_sub hn1, Real.rpow_natCast]
  calc (r₁ ^ n + r₂ ^ n) ^ (((n : ℝ) - 1) / (n : ℝ))
      < (r₁ ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) + (r₂ ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) :=
        rpow_add_lt_add_rpow (pow_pos hr₁ n) (pow_pos hr₂ n) hα0 hα1
    _ = r₁ ^ (n - 1) + r₂ ^ (n - 1) := by rw [hpow hr₁, hpow hr₂]

/-- Volume of a disjoint union of two open balls `Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂`. -/
theorem volume_ball_union_ball_of_disjoint [Nontrivial E] (c₁ c₂ : E) {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hdisj : Disjoint (Metric.ball c₁ r₁) (Metric.ball c₂ r₂)) :
    volume (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) =
      ENNReal.ofReal (r₁ ^ Module.finrank ℝ E + r₂ ^ Module.finrank ℝ E) *
        volume (Metric.ball (0 : E) 1) := by
  rw [measure_union hdisj Metric.isOpen_ball.measurableSet,
    Measure.addHaar_ball volume c₁ hr₁, Measure.addHaar_ball volume c₂ hr₂, ← add_mul,
    ENNReal.ofReal_add (pow_nonneg hr₁ _) (pow_nonneg hr₂ _)]

/-- **Exact perimeter additivity for a separated union of two positive-radius balls**:
when `Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₂ r₂)` and `0 < r₁, r₂`,
`perimeter volume (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) =
perimeter volume (Metric.ball c₁ r₁) + perimeter volume (Metric.ball c₂ r₂)`. -/
theorem perimeter_ball_union_ball_of_disjoint_closedBall {c₁ c₂ : E} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdisj : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₂ r₂)) :
    perimeter volume (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) =
      perimeter volume (Metric.ball c₁ r₁) + perimeter volume (Metric.ball c₂ r₂) := by
  have hdisj_open : Disjoint (Metric.ball c₁ r₁) (Metric.ball c₂ r₂) :=
    hdisj.mono Metric.ball_subset_closedBall Metric.ball_subset_closedBall
  refine le_antisymm
    (perimeter_union_le_of_disjoint Metric.isOpen_ball.measurableSet.nullMeasurableSet
      Metric.isOpen_ball.measurableSet.nullMeasurableSet hdisj_open) ?_
  obtain ⟨U₁, U₂, hU₁, hU₂, hc₁, hc₂, hU_disj⟩ :=
    normal_separation Metric.isClosed_closedBall Metric.isClosed_closedBall hdisj
  let Ω₁ : Opens E := ⟨U₁, hU₁⟩
  let Ω₂ : Opens E := ⟨U₂, hU₂⟩
  have h1 : relativePerimeter volume Ω₁ (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) =
      perimeter volume (Metric.ball c₁ r₁) := by
    have hinter : (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) ∩ U₁ = Metric.ball c₁ r₁ ∩ U₁ := by
      have hd : Disjoint (Metric.ball c₂ r₂) U₁ :=
        hU_disj.symm.mono_left (Metric.ball_subset_closedBall.trans hc₂)
      rw [union_inter_distrib_right, hd.inter_eq, union_empty]
    rw [relativePerimeter_eq_of_inter_ae_eq (EventuallyEq.of_eq hinter),
      relativePerimeter_ball_eq_perimeter c₁ hr₁ hc₁]
  have h2 : relativePerimeter volume Ω₂ (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) =
      perimeter volume (Metric.ball c₂ r₂) := by
    have hinter : (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) ∩ U₂ = Metric.ball c₂ r₂ ∩ U₂ := by
      have hd : Disjoint (Metric.ball c₁ r₁) U₂ :=
        hU_disj.mono_left (Metric.ball_subset_closedBall.trans hc₁)
      rw [union_inter_distrib_right, hd.inter_eq, empty_union]
    rw [relativePerimeter_eq_of_inter_ae_eq (EventuallyEq.of_eq hinter),
      relativePerimeter_ball_eq_perimeter c₂ hr₂ hc₂]
  rw [← h1, ← h2]
  exact relativePerimeter_add_le_perimeter_of_disjoint hU_disj _

/-- Exact perimeter of a separated union of two balls in terms of unit-ball volume. -/
theorem perimeter_ball_union_ball_eq_unitBall [Nontrivial E] {c₁ c₂ : E} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdisj : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₂ r₂)) :
    perimeter volume (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) *
        (r₁ ^ (Module.finrank ℝ E - 1) + r₂ ^ (Module.finrank ℝ E - 1))) *
        volume (Metric.ball (0 : E) 1) := by
  rw [perimeter_ball_union_ball_of_disjoint_closedBall hr₁ hr₂ hdisj,
    perimeter_ball_eq_unitBall c₁ hr₁, perimeter_ball_eq_unitBall c₂ hr₂, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity), mul_add]

/-- Isoperimetric lower bound of a disjoint union of two balls. -/
theorem isoperimetricBound_ball_union_ball_of_disjoint [Nontrivial E] {c₁ c₂ : E} {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hdisj : Disjoint (Metric.ball c₁ r₁) (Metric.ball c₂ r₂)) :
    isoperimetricBound (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) *
        (r₁ ^ Module.finrank ℝ E + r₂ ^ Module.finrank ℝ E) ^
          (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ))) *
        volume (Metric.ball (0 : E) 1) :=
  isoperimetricBound_of_volume_eq (add_nonneg (pow_nonneg hr₁ _) (pow_nonneg hr₂ _))
    (volume_ball_union_ball_of_disjoint c₁ c₂ hr₁ hr₂ hdisj)

/-- **Strict Euclidean isoperimetric inequality for any separated union of two positive-radius
balls** (`2 ≤ Module.finrank ℝ E`, `0 < r₁, r₂`, disjoint closed balls). -/
theorem isoperimetricBound_ball_union_ball_lt_perimeter_of_disjoint_closedBall
    (hn : 2 ≤ Module.finrank ℝ E) {c₁ c₂ : E} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdisj : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₂ r₂)) :
    isoperimetricBound (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) <
      perimeter volume (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  have hdisj_open : Disjoint (Metric.ball c₁ r₁) (Metric.ball c₂ r₂) :=
    hdisj.mono Metric.ball_subset_closedBall Metric.ball_subset_closedBall
  have hn_pos : 0 < (Module.finrank ℝ E : ℝ) := Nat.cast_pos.2 (by omega)
  have hlt : (Module.finrank ℝ E : ℝ) *
      (r₁ ^ Module.finrank ℝ E + r₂ ^ Module.finrank ℝ E) ^
        (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ)) <
      (Module.finrank ℝ E : ℝ) *
        (r₁ ^ (Module.finrank ℝ E - 1) + r₂ ^ (Module.finrank ℝ E - 1)) :=
    mul_lt_mul_of_pos_left (pow_add_pow_rpow_div_lt hn hr₁ hr₂) hn_pos
  rw [isoperimetricBound_ball_union_ball_of_disjoint hr₁.le hr₂.le hdisj_open,
    perimeter_ball_union_ball_eq_unitBall hr₁ hr₂ hdisj,
    mul_comm _ (volume (Metric.ball (0 : E) 1)), mul_comm _ (volume (Metric.ball (0 : E) 1))]
  exact ENNReal.mul_lt_mul_right (Metric.measure_ball_pos volume (0 : E) zero_lt_one).ne'
    measure_ball_lt_top.ne ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt)

/-- **Strict positivity of the isoperimetric deficit of any separated union of two positive-radius
balls** (`2 ≤ Module.finrank ℝ E`). -/
theorem isoperimetricDeficit_ball_union_ball_pos_of_disjoint_closedBall
    (hn : 2 ≤ Module.finrank ℝ E) {c₁ c₂ : E} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdisj : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₂ r₂)) :
    0 < isoperimetricDeficit (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) := by
  refine isoperimetricDeficit_pos_of_lt ?_
    (isoperimetricBound_ball_union_ball_lt_perimeter_of_disjoint_closedBall hn hr₁ hr₂ hdisj)
  rw [perimeter_ball_union_ball_of_disjoint_closedBall hr₁ hr₂ hdisj]
  exact ENNReal.add_lt_top.2 ⟨perimeter_ball_lt_top c₁ r₁, perimeter_ball_lt_top c₂ r₂⟩

/-- **Strict Euclidean isoperimetric inequality for two balls with `r₁ + r₂ < dist c₁ c₂`**. -/
theorem isoperimetricBound_ball_union_ball_lt_perimeter_of_add_lt_dist
    (hn : 2 ≤ Module.finrank ℝ E) {c₁ c₂ : E} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdist : r₁ + r₂ < dist c₁ c₂) :
    isoperimetricBound (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) <
      perimeter volume (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) :=
  isoperimetricBound_ball_union_ball_lt_perimeter_of_disjoint_closedBall hn hr₁ hr₂
    (Metric.closedBall_disjoint_closedBall hdist)

theorem isoperimetricDeficit_ball_union_ball_pos_of_add_lt_dist
    (hn : 2 ≤ Module.finrank ℝ E) {c₁ c₂ : E} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdist : r₁ + r₂ < dist c₁ c₂) :
    0 < isoperimetricDeficit (Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂) :=
  isoperimetricDeficit_ball_union_ball_pos_of_disjoint_closedBall hn hr₁ hr₂
    (Metric.closedBall_disjoint_closedBall hdist)

end IsoperimetricFunctional

/-! ### Section 4: Box AM–GM inequality, cube rigidity, `ω_n < 2^n`, and strict box inequality -/

section Box

/-- For any positive reals `L : Fin n → ℝ` (`0 < L i`), the product of the `n` codimension-1
products `∏ j ≠ i, L j` equals `(∏ i, L i) ^ (n - 1)`. -/
theorem prod_prod_erase_eq_pow_pred {n : ℕ} {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) :
    (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, L j) = (∏ i : Fin n, L i) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · set V : ℝ := ∏ i : Fin n, L i
    have hV : 0 < V := Finset.prod_pos fun i _ ↦ hL i
    have hmul : V * ∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, L j = V * V ^ (n - 1) := by
      calc V * ∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, L j
          = ∏ i : Fin n, (L i * ∏ j ∈ Finset.univ.erase i, L j) := by
            rw [← Finset.prod_mul_distrib]
        _ = ∏ _ : Fin n, V :=
            Finset.prod_congr rfl fun i _ ↦ Finset.mul_prod_erase Finset.univ L (Finset.mem_univ i)
        _ = V ^ n := by simp [Finset.prod_const]
        _ = V * V ^ (n - 1) := by conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']
    exact mul_left_cancel₀ hV.ne' hmul

/-- Weighted AM–GM inequality and equality characterization for codimension-1 box face products. -/
theorem geom_mean_face_le_and_eq_iff {n : ℕ} (hn : 0 < n) {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) :
    2 * (n : ℝ) * (∏ i : Fin n, L i) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, L j ∧
    (2 * (n : ℝ) * (∏ i : Fin n, L i) ^ (((n : ℝ) - 1) / (n : ℝ)) =
      2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, L j ↔ ∀ i j : Fin n, L i = L j) := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  let F : Fin n → ℝ := fun i ↦ ∏ j ∈ Finset.univ.erase i, L j
  have hF_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ F i :=
    fun i _ ↦ Finset.prod_nonneg fun j _ ↦ (hL j).le
  let w : Fin n → ℝ := fun _ ↦ 1 / (n : ℝ)
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w i := fun _ _ ↦ by positivity
  have hw_ne : ∀ i : Fin n, w i ≠ 0 := fun _ ↦ one_div_ne_zero hn_ne
  have hw_sum : ∑ i ∈ (Finset.univ : Finset (Fin n)), w i = 1 := by
    simp [w, Finset.sum_const, mul_inv_cancel₀ hn_ne]
  have hV_pos : 0 < ∏ i : Fin n, L i := Finset.prod_pos fun i _ ↦ hL i
  have hlhs : ∏ i ∈ (Finset.univ : Finset (Fin n)), F i ^ w i =
      (∏ i : Fin n, L i) ^ (((n : ℝ) - 1) / (n : ℝ)) := by
    dsimp only [w]
    rw [Real.finsetProd_rpow Finset.univ F hF_nonneg (1 / (n : ℝ)),
      prod_prod_erase_eq_pow_pred hL, ← Real.rpow_natCast _ (n - 1),
      ← Real.rpow_mul hV_pos.le, Nat.cast_sub hn, Nat.cast_one, mul_one_div]
  have hrhs : ∑ i ∈ (Finset.univ : Finset (Fin n)), w i * F i =
      (1 / (n : ℝ)) * ∑ i : Fin n, F i := by dsimp only [w]; rw [← Finset.mul_sum]
  have hcancel : 2 * (n : ℝ) * (1 / (n : ℝ) * ∑ i : Fin n, F i) = 2 * ∑ i : Fin n, F i := by
    field_simp
  refine ⟨?_, ?_⟩
  · have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ w F hw_nonneg hw_sum hF_nonneg
    rw [hlhs, hrhs] at hamgm
    have hmul := mul_le_mul_of_nonneg_left hamgm (by positivity : 0 ≤ 2 * (n : ℝ))
    rwa [hcancel] at hmul
  · have hamgm_iff :=
      Real.geom_mean_eq_arith_mean_weighted_iff_of_nonneg' Finset.univ w F hw_nonneg hw_sum
        hF_nonneg
    have hscale : 2 * (n : ℝ) * (∏ i : Fin n, L i) ^ (((n : ℝ) - 1) / (n : ℝ)) =
        2 * ∑ i : Fin n, F i ↔ ∏ i : Fin n, F i ^ w i = ∑ i : Fin n, w i * F i := by
      rw [← hlhs, hrhs, ← hcancel, mul_right_inj' (by positivity : 2 * (n : ℝ) ≠ 0)]
    rw [hscale, hamgm_iff]
    have hLF : ∀ i : Fin n, L i * F i = ∏ k : Fin n, L k :=
      fun i ↦ Finset.mul_prod_erase Finset.univ L (Finset.mem_univ i)
    constructor
    · intro h i j
      have hFij : F i = F j :=
        (h i (Finset.mem_univ i) (hw_ne i)).trans (h j (Finset.mem_univ j) (hw_ne j)).symm
      have hF_pos : F j ≠ 0 := (Finset.prod_pos fun k _ ↦ hL k).ne'
      exact mul_right_cancel₀ hF_pos (by rw [← hFij, hLF i, ← hLF j, hFij])
    · intro h j _ _
      have hF_eq : ∀ i : Fin n, F i = F j := fun i ↦
        mul_left_cancel₀ (hL j).ne' (by rw [← h i j, hLF i, ← hLF j, h i j])
      calc F j = (∑ i : Fin n, w i) * F j := by rw [hw_sum, one_mul]
        _ = ∑ i : Fin n, w i * F j := Finset.sum_mul _ _ _
        _ = ∑ i : Fin n, w i * F i := Finset.sum_congr rfl fun i _ ↦ by rw [hF_eq i]

/-- **Sharp Box AM–GM Inequality**: for any nondegenerate open box `euclideanOpenBox a b` in
`EuclideanSpace ℝ (Fin n)` (`∀ i, a i < b i`),
`2 * n * (volume (euclideanOpenBox a b)).toReal ^ ((n - 1) / n) ≤
(perimeter volume (euclideanOpenBox a b)).toReal`. -/
theorem two_mul_finrank_mul_volume_rpow_le_perimeter_euclideanOpenBox {n : ℕ}
    {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    2 * (n : ℝ) * (volume (euclideanOpenBox a b)).toReal ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      (perimeter volume (euclideanOpenBox a b)).toReal := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [perimeter_euclideanOpenBox hab]
  · have hL : ∀ i, 0 < b i - a i := fun i ↦ sub_pos.2 (hab i)
    have hV : (volume (euclideanOpenBox a b)).toReal = ∏ i : Fin n, (b i - a i) := by
      rw [volume_euclideanOpenBox, ENNReal.toReal_prod]
      exact Finset.prod_congr rfl fun i _ ↦ ENNReal.toReal_ofReal (hL i).le
    have hP : (perimeter volume (euclideanOpenBox a b)).toReal =
        2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j) := by
      rw [perimeter_euclideanOpenBox hab, ENNReal.toReal_ofReal (mul_nonneg zero_le_two
        (Finset.sum_nonneg fun i _ ↦ Finset.prod_nonneg fun j _ ↦ (hL j).le))]
    rw [hV, hP]
    exact (geom_mean_face_le_and_eq_iff hn hL).1

/-- **Sharp Box AM–GM Inequality for closed boxes `euclideanBox a b`**. -/
theorem two_mul_finrank_mul_volume_rpow_le_perimeter_euclideanBox {n : ℕ}
    {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    2 * (n : ℝ) * (volume (euclideanBox a b)).toReal ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      (perimeter volume (euclideanBox a b)).toReal := by
  rw [← measure_congr (euclideanOpenBox_ae_eq_euclideanBox a b), ← perimeter_euclideanOpenBox_eq]
  exact two_mul_finrank_mul_volume_rpow_le_perimeter_euclideanOpenBox hab

/-- **Cube rigidity in the Box AM–GM Inequality**: for `∀ i, a i < b i`, equality
`2 * n * |B| ^ ((n - 1) / n) = P(B)` holds if and only if all side lengths are equal
(`∀ i j, b i - a i = b j - a j`). -/
theorem two_mul_finrank_mul_volume_rpow_eq_perimeter_euclideanOpenBox_iff {n : ℕ}
    {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    2 * (n : ℝ) * (volume (euclideanOpenBox a b)).toReal ^ (((n : ℝ) - 1) / (n : ℝ)) =
      (perimeter volume (euclideanOpenBox a b)).toReal ↔
      ∀ i j : Fin n, b i - a i = b j - a j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [perimeter_euclideanOpenBox hab]
  · have hL : ∀ i, 0 < b i - a i := fun i ↦ sub_pos.2 (hab i)
    have hV : (volume (euclideanOpenBox a b)).toReal = ∏ i : Fin n, (b i - a i) := by
      rw [volume_euclideanOpenBox, ENNReal.toReal_prod]
      exact Finset.prod_congr rfl fun i _ ↦ ENNReal.toReal_ofReal (hL i).le
    have hP : (perimeter volume (euclideanOpenBox a b)).toReal =
        2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j) := by
      rw [perimeter_euclideanOpenBox hab, ENNReal.toReal_ofReal (mul_nonneg zero_le_two
        (Finset.sum_nonneg fun i _ ↦ Finset.prod_nonneg fun j _ ↦ (hL j).le))]
    rw [hV, hP]
    exact (geom_mean_face_le_and_eq_iff hn hL).2

/-- The open unit ball `Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1` is contained in the open
unit cube `euclideanOpenBox (fun _ ↦ -1) (fun _ ↦ 1)`. -/
theorem ball_zero_one_subset_euclideanOpenBox (n : ℕ) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆
      euclideanOpenBox (fun _ : Fin n ↦ (-1 : ℝ)) (fun _ : Fin n ↦ (1 : ℝ)) := by
  intro x hx i
  rw [Metric.mem_ball, dist_zero_right] at hx
  exact abs_lt.1 ((PiLp.norm_apply_le x i).trans_lt hx)

/-- Volume of the open cube `(-1, 1)^n` in `EuclideanSpace ℝ (Fin n)` is `2^n`. -/
theorem volume_euclideanOpenBox_neg_one_one (n : ℕ) :
    volume (euclideanOpenBox (fun _ : Fin n ↦ (-1 : ℝ)) (fun _ : Fin n ↦ (1 : ℝ))) =
      ENNReal.ofReal ((2 : ℝ) ^ n) := by
  rw [volume_euclideanOpenBox]
  simp [sub_neg_eq_add, one_add_one_eq_two, Finset.prod_const, ENNReal.ofReal_pow]

/-- **Strict ball-inside-cube volume inequality (`ω_n < 2^n`) for `2 ≤ n`**:
`volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) < ENNReal.ofReal ((2 : ℝ) ^ n)`. -/
theorem volume_unitBall_lt_two_pow {n : ℕ} (hn : 2 ≤ n) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) < ENNReal.ofReal ((2 : ℝ) ^ n) := by
  let B : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 1
  let Q : Set (EuclideanSpace ℝ (Fin n)) :=
    euclideanOpenBox (fun _ : Fin n ↦ (-1 : ℝ)) (fun _ : Fin n ↦ (1 : ℝ))
  let U : Set (EuclideanSpace ℝ (Fin n)) :=
    Q \ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  have hU_open : IsOpen U := (isOpen_euclideanOpenBox _ _).sdiff Metric.isClosed_closedBall
  let x₀ : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ : Fin n ↦ (3 / 4 : ℝ))
  have hx₀_mem : x₀ ∈ U := by
    refine ⟨fun i ↦ by norm_num [x₀], ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, not_le]
    have hsq : ‖x₀‖ ^ 2 = (n : ℝ) * (9 / 16 : ℝ) := by
      rw [PiLp.norm_sq_eq_of_L2]
      have hcoord : ∀ i : Fin n, ‖x₀.ofLp i‖ ^ 2 = (9 / 16 : ℝ) := fun _ ↦ by
        change |(3 / 4 : ℝ)| ^ 2 = 9 / 16; norm_num
      simp_rw [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact (sq_lt_sq₀ zero_le_one (norm_nonneg x₀)).1 (by nlinarith)
  have hU_pos : 0 < volume U := hU_open.measure_pos volume ⟨x₀, hx₀_mem⟩
  have hdisj : Disjoint B U :=
    disjoint_sdiff_self_right.mono_left Metric.ball_subset_closedBall
  have hsub : B ∪ U ⊆ Q :=
    union_subset (ball_zero_one_subset_euclideanOpenBox n) sdiff_subset
  rw [← volume_euclideanOpenBox_neg_one_one n]
  calc volume B
      < volume B + volume U := ENNReal.lt_add_right measure_ball_lt_top.ne hU_pos.ne'
    _ = volume (B ∪ U) := (measure_union hdisj hU_open.measurableSet).symm
    _ ≤ volume Q := measure_mono hsub

/-- For `2 ≤ n`, `(volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / n) < 2`. -/
theorem toReal_volume_unitBall_rpow_inv_lt_two {n : ℕ} (hn : 2 ≤ n) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) < 2 := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hvol_pos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
  have hlt := (ENNReal.toReal_lt_toReal measure_ball_lt_top.ne ENNReal.ofReal_ne_top).2
    (volume_unitBall_lt_two_pow hn)
  rw [ENNReal.toReal_ofReal (by positivity)] at hlt
  calc (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ))
      < ((2 : ℝ) ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_lt_rpow hvol_pos.le hlt (by positivity)
    _ = 2 := by
        rw [← Real.rpow_natCast 2 n, ← Real.rpow_mul zero_le_two,
          mul_one_div_cancel hn_pos.ne', Real.rpow_one]

/-- **Strict Euclidean isoperimetric inequality for every nondegenerate open `n`-box (`2 ≤ n`)**:
`isoperimetricBound (euclideanOpenBox a b) < perimeter volume (euclideanOpenBox a b)`. -/
theorem isoperimetricBound_euclideanOpenBox_lt_perimeter {n : ℕ} (hn : 2 ≤ n)
    {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    isoperimetricBound (euclideanOpenBox a b) < perimeter volume (euclideanOpenBox a b) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hV_pos : 0 < (volume (euclideanOpenBox a b)).toReal := by
    rw [volume_euclideanOpenBox, ENNReal.toReal_prod]
    exact Finset.prod_pos fun i _ ↦
      ENNReal.toReal_pos (ENNReal.ofReal_ne_zero_iff.2 (sub_pos.2 (hab i))) ENNReal.ofReal_ne_top
  have hV_rpow_pos : 0 < (volume (euclideanOpenBox a b)).toReal ^ (((n : ℝ) - 1) / (n : ℝ)) :=
    Real.rpow_pos_of_pos hV_pos _
  have hbound_toReal : (isoperimetricBound (euclideanOpenBox a b)).toReal <
      2 * (n : ℝ) * (volume (euclideanOpenBox a b)).toReal ^ (((n : ℝ) - 1) / (n : ℝ)) := by
    rw [toReal_isoperimetricBound, hfin, mul_comm (2 : ℝ) (n : ℝ)]
    exact mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_left (toReal_volume_unitBall_rpow_inv_lt_two hn) hn_pos) hV_rpow_pos
  have hlt_perim : (isoperimetricBound (euclideanOpenBox a b)).toReal <
      (perimeter volume (euclideanOpenBox a b)).toReal :=
    hbound_toReal.trans_le (two_mul_finrank_mul_volume_rpow_le_perimeter_euclideanOpenBox hab)
  have hB_fin : isoperimetricBound (euclideanOpenBox a b) ≠ ⊤ := by
    refine (isoperimetricBound_lt_top_of_volume_lt_top ?_).ne
    rw [volume_euclideanOpenBox]
    exact ENNReal.prod_lt_top fun i _ ↦ ENNReal.ofReal_lt_top
  exact (ENNReal.toReal_lt_toReal hB_fin (perimeter_euclideanOpenBox_lt_top a b).ne).1 hlt_perim

/-- **Strict positivity of the isoperimetric deficit of every nondegenerate open `n`-box**
(`2 ≤ n`). -/
theorem isoperimetricDeficit_euclideanOpenBox_pos {n : ℕ} (hn : 2 ≤ n)
    {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    0 < isoperimetricDeficit (euclideanOpenBox a b) :=
  isoperimetricDeficit_pos_of_lt (perimeter_euclideanOpenBox_lt_top a b)
    (isoperimetricBound_euclideanOpenBox_lt_perimeter hn hab)

/-- **Strict Euclidean isoperimetric inequality for every nondegenerate closed `n`-box**
(`2 ≤ n`). -/
theorem isoperimetricBound_euclideanBox_lt_perimeter {n : ℕ} (hn : 2 ≤ n)
    {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    isoperimetricBound (euclideanBox a b) < perimeter volume (euclideanBox a b) := by
  rw [← isoperimetricBound_congr_ae (euclideanOpenBox_ae_eq_euclideanBox a b),
    ← perimeter_euclideanOpenBox_eq]
  exact isoperimetricBound_euclideanOpenBox_lt_perimeter hn hab

/-- **Strict positivity of the isoperimetric deficit of every nondegenerate closed `n`-box**
(`2 ≤ n`). -/
theorem isoperimetricDeficit_euclideanBox_pos {n : ℕ} (hn : 2 ≤ n)
    {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    0 < isoperimetricDeficit (euclideanBox a b) := by
  rw [← isoperimetricDeficit_congr_ae (euclideanOpenBox_ae_eq_euclideanBox a b)]
  exact isoperimetricDeficit_euclideanOpenBox_pos hn hab

/-- **Planar rectangle specialization (`n = 2`)**: every nondegenerate planar rectangle
`euclideanOpenBox a b` in `EuclideanSpace ℝ (Fin 2)` satisfies strict Euclidean isoperimetric
inequality `isoperimetricBound (euclideanOpenBox a b) < perimeter volume (euclideanOpenBox a b)`
and `0 < isoperimetricDeficit (euclideanOpenBox a b)`. -/
theorem isoperimetricBound_planarRectangle_lt_perimeter
    {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i) :
    isoperimetricBound (euclideanOpenBox a b) < perimeter volume (euclideanOpenBox a b) ∧
      0 < isoperimetricDeficit (euclideanOpenBox a b) :=
  ⟨isoperimetricBound_euclideanOpenBox_lt_perimeter le_rfl hab,
    isoperimetricDeficit_euclideanOpenBox_pos le_rfl hab⟩

end Box

end TauCeti
