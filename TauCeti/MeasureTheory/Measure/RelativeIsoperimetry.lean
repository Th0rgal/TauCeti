/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.EssentialBoundary
public import TauCeti.MeasureTheory.Measure.HalfSpacePerimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.SteinerProperties
public import TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
public import TauCeti.MeasureTheory.Measure.OneDimIsoperimetry
public import TauCeti.MeasureTheory.Measure.ReducedBoundary
import all TauCeti.MeasureTheory.Measure.EssentialBoundary
import all TauCeti.MeasureTheory.Measure.HalfSpacePerimeter
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerProperties
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
import all TauCeti.MeasureTheory.Measure.OneDimIsoperimetry
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.ReducedBoundary

/-!
# Relative Isoperimetric Functional, Ahlfors Density Bounds, and Iterated Steiner Symmetrization

This file develops the relative isoperimetric functional on subdomains, its De Giorgi blow-up
scaling and reduction to the unit ball, one-dimensional relative isoperimetric inequalities on
intervals, two-sided `(n - 1)`-Ahlfors density bounds and disjoint ball packing on the reduced
boundary, and iterated Steiner symmetrization along finite lists and sequences of directions:
1. **Relative isoperimetric functional and scale-invariant reduction to the unit ball**:
   `relativeVolumeMin`, `relativeIsoperimetricLHS`, `relativeVolumeMin_deGiorgiBlowUp_ball`, and
   `relativeIsoperimetric_ball_of_unitBall`.
2. **Two-sided `(n - 1)`-Ahlfors density bounds and disjoint ball packing on `reducedBoundary`**:
   `HasDeGiorgiBlowUp.tendsto_relativeVolumeMin_div_volume_ball`,
   `HasDeGiorgiNormal.tendsto_relativePerimeter_div_rpow`, `relativePerimeter_add_le_of_disjoint`,
   and `sum_relativePerimeter_openBall_le_of_pairwiseDisjoint`.
3. **Iterated Steiner symmetrization along finite lists and sequences of directions**:
   `iteratedSteinerSymmetrization`, `steinerSymmetrizationSeq`, `convex_steinerSymmetrization`,
   `convex_iteratedSteinerSymmetrization`, `volume_iteratedSteinerSymmetrization`,
   `iteratedSteinerSymmetrization_ball_ae_eq`, `volume_symmDiff_iteratedSteinerSymmetrization_le`,
   and `antitone_volume_symmDiff_steinerSymmetrizationSeq_ball`.
-/

public section

open Filter MeasureTheory Set TopologicalSpace TestFunction TauCeti.MeasureTheory
open scoped ENNReal NNReal InnerProductSpace Distributions Topology symmDiff

namespace TauCeti

/-! ### Section 1: Relative Isoperimetric Functional, Blow-Up Scaling, and 1D Interval Bounds -/

section RelativeVolumeMin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The **smaller relative volume** `min (volume (s ∩ U)) (volume (U \ s))` of `s ⊆ E` in `U`. -/
noncomputable def relativeVolumeMin (U s : Set E) : ℝ≥0∞ := min (volume (s ∩ U)) (volume (U \ s))
/-- The **relative isoperimetric left-hand side**
`min (volume (s ∩ U)) (volume (U \ s)) ^ ((finrank ℝ E - 1) / finrank ℝ E)`. -/
noncomputable def relativeIsoperimetricLHS (U s : Set E) : ℝ≥0∞ :=
  (relativeVolumeMin U s) ^ (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ))
@[simp] theorem relativeVolumeMin_empty (U : Set E) : relativeVolumeMin U ∅ = 0 := by
  simp [relativeVolumeMin]
@[simp] theorem relativeVolumeMin_empty_left (s : Set E) : relativeVolumeMin ∅ s = 0 := by
  simp [relativeVolumeMin]
@[simp] theorem relativeVolumeMin_univ (U : Set E) : relativeVolumeMin U Set.univ = 0 := by
  simp [relativeVolumeMin]
@[simp] theorem relativeVolumeMin_self (U : Set E) : relativeVolumeMin U U = 0 := by
  simp [relativeVolumeMin]
/-- Complement symmetry of `relativeVolumeMin`: `relativeVolumeMin U sᶜ = relativeVolumeMin U s`. -/
@[simp] theorem relativeVolumeMin_compl (U s : Set E) :
    relativeVolumeMin U sᶜ = relativeVolumeMin U s := by
  have h1 : sᶜ ∩ U = U \ s := by ext x; simp [and_comm]
  have h2 : U \ sᶜ = s ∩ U := by ext x; simp [and_comm]
  dsimp [relativeVolumeMin]; rw [h1, h2, min_comm]
/-- A.e. congruence of `relativeVolumeMin`. -/
theorem relativeVolumeMin_congr_ae {U s t : Set E} (hst : s =ᵐ[volume] t) :
    relativeVolumeMin U s = relativeVolumeMin U t := by
  have h1 : (s ∩ U : Set E) =ᵐ[volume] (t ∩ U : Set E) := hst.inter EventuallyEq.rfl
  have hc := hst.compl.inter (EventuallyEq.rfl : U =ᵐ[volume] U)
  have hs_eq : sᶜ ∩ U = U \ s := by ext x; simp [and_comm]
  have ht_eq : tᶜ ∩ U = U \ t := by ext x; simp [and_comm]
  rw [hs_eq, ht_eq] at hc; simp [relativeVolumeMin, measure_congr h1, measure_congr hc]
theorem relativeVolumeMin_congr_ae_restrict {U s t : Set E} (hU : NullMeasurableSet U volume)
    (hst : s =ᵐ[volume.restrict U] t) : relativeVolumeMin U s = relativeVolumeMin U t := by
  have h1 : volume (s ∩ U) = volume (t ∩ U) := by
    rw [← Measure.restrict_apply₀' hU, ← Measure.restrict_apply₀' hU, measure_congr hst]
  have hs_eq : U \ s = sᶜ ∩ U := by ext x; simp [and_comm]
  have ht_eq : U \ t = tᶜ ∩ U := by ext x; simp [and_comm]
  have h2 : volume (U \ s) = volume (U \ t) := by
    rw [hs_eq, ht_eq, ← Measure.restrict_apply₀' hU, ← Measure.restrict_apply₀' hU,
      measure_congr hst.compl]
  simp [relativeVolumeMin, h1, h2]
theorem relativeVolumeMin_le_volume_left (U s : Set E) :
    relativeVolumeMin U s ≤ volume (s ∩ U) := min_le_left _ _
theorem relativeVolumeMin_le_volume_right (U s : Set E) :
    relativeVolumeMin U s ≤ volume (U \ s) := min_le_right _ _
theorem relativeVolumeMin_le_volume (U s : Set E) : relativeVolumeMin U s ≤ volume U :=
  (relativeVolumeMin_le_volume_left U s).trans (measure_mono Set.inter_subset_right)
/-- For any null-measurable set `s`, `2 * relativeVolumeMin U s ≤ volume U`. -/
theorem two_mul_relativeVolumeMin_le_volume (U : Set E) {s : Set E}
    (hs : NullMeasurableSet s volume) : 2 * relativeVolumeMin U s ≤ volume U := by
  rw [two_mul, ← measure_inter_add_sdiff₀ U hs, Set.inter_comm]
  exact add_le_add (min_le_left _ _) (min_le_right _ _)
theorem two_mul_relativeVolumeMin_le_volume_of_measurableSet (U : Set E) {s : Set E}
    (hs : MeasurableSet s) : 2 * relativeVolumeMin U s ≤ volume U :=
  two_mul_relativeVolumeMin_le_volume U hs.nullMeasurableSet
@[simp] theorem relativeIsoperimetricLHS_compl (U s : Set E) :
    relativeIsoperimetricLHS U sᶜ = relativeIsoperimetricLHS U s := by
  simp [relativeIsoperimetricLHS]
theorem relativeIsoperimetricLHS_congr_ae {U s t : Set E} (hst : s =ᵐ[volume] t) :
    relativeIsoperimetricLHS U s = relativeIsoperimetricLHS U t := by
  simp [relativeIsoperimetricLHS, relativeVolumeMin_congr_ae hst]
theorem relativeIsoperimetricLHS_congr_ae_restrict {U s t : Set E}
    (hU : NullMeasurableSet U volume) (hst : s =ᵐ[volume.restrict U] t) :
    relativeIsoperimetricLHS U s = relativeIsoperimetricLHS U t := by
  simp [relativeIsoperimetricLHS, relativeVolumeMin_congr_ae_restrict hU hst]
@[simp] theorem relativeIsoperimetricLHS_empty (hdim : 1 < Module.finrank ℝ E) (U : Set E) :
    relativeIsoperimetricLHS U ∅ = 0 := by
  have hn : (1 : ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
  have hpos : 0 < ((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ) :=
    div_pos (by linarith) (by linarith)
  simp [relativeIsoperimetricLHS, ENNReal.zero_rpow_of_pos hpos]
@[simp] theorem relativeIsoperimetricLHS_univ (hdim : 1 < Module.finrank ℝ E) (U : Set E) :
    relativeIsoperimetricLHS U Set.univ = 0 := by
  rw [← compl_empty, relativeIsoperimetricLHS_compl, relativeIsoperimetricLHS_empty hdim]
/-- **Complement-volume scaling of `deGiorgiBlowUp` on balls** for `0 < r`. -/
theorem volume_ball_diff_deGiorgiBlowUp (s : Set E) (x : E) (R : ℝ) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball 0 R \ deGiorgiBlowUp s x r) =
      ENNReal.ofReal (r ^ (-(Module.finrank ℝ E : ℝ))) * volume (Metric.ball x (r * R) \ s) := by
  have h1 : Metric.ball (0 : E) R \ deGiorgiBlowUp s x r =
      deGiorgiBlowUp sᶜ x r ∩ Metric.ball 0 R := by ext z; simp [deGiorgiBlowUp_compl, and_comm]
  have h2 : sᶜ ∩ Metric.ball x (r * R) = Metric.ball x (r * R) \ s := by ext z; simp [and_comm]
  rw [h1, volume_deGiorgiBlowUp_inter_ball sᶜ x R hr, h2]
/-- **De Giorgi blow-up scaling of `relativeVolumeMin` on balls** for `0 < r`. -/
theorem relativeVolumeMin_deGiorgiBlowUp_ball (s : Set E) (x : E) (R : ℝ) {r : ℝ} (hr : 0 < r) :
    relativeVolumeMin (Metric.ball 0 R) (deGiorgiBlowUp s x r) =
      ENNReal.ofReal (r ^ (-(Module.finrank ℝ E : ℝ))) *
        relativeVolumeMin (Metric.ball x (r * R)) s := by
  dsimp [relativeVolumeMin]
  rw [volume_deGiorgiBlowUp_inter_ball s x R hr, volume_ball_diff_deGiorgiBlowUp s x R hr]
  exact ((monotone_id.const_mul' _).map_min).symm
/-- **De Giorgi blow-up scaling of `relativeIsoperimetricLHS` on balls** for `0 < r` and
`1 ≤ Module.finrank ℝ E`. -/
theorem relativeIsoperimetricLHS_deGiorgiBlowUp_ball_of_one_le_finrank
    (hdim : 1 ≤ Module.finrank ℝ E) (s : Set E) (x : E) (R : ℝ) {r : ℝ} (hr : 0 < r) :
    relativeIsoperimetricLHS (Metric.ball 0 R) (deGiorgiBlowUp s x r) =
      ENNReal.ofReal (r ^ (1 - (Module.finrank ℝ E : ℝ))) *
        relativeIsoperimetricLHS (Metric.ball x (r * R)) s := by
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hdim
  have hn0 : n ≠ 0 := by linarith
  have hp : 0 ≤ (n - 1) / n := div_nonneg (by linarith) (by linarith)
  have hrpow : (ENNReal.ofReal (r ^ (-n))) ^ ((n - 1) / n) = ENNReal.ofReal (r ^ (1 - n)) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _), ← Real.rpow_mul hr.le]
    congr 2; field_simp [hn0]; ring
  dsimp [relativeIsoperimetricLHS]
  rw [relativeVolumeMin_deGiorgiBlowUp_ball s x R hr, ENNReal.mul_rpow_of_nonneg _ _ hp, hrpow]
theorem relativeIsoperimetricLHS_deGiorgiBlowUp_ball [Nontrivial E] (s : Set E) (x : E) (R : ℝ)
    {r : ℝ} (hr : 0 < r) : relativeIsoperimetricLHS (Metric.ball 0 R) (deGiorgiBlowUp s x r) =
      ENNReal.ofReal (r ^ (1 - (Module.finrank ℝ E : ℝ))) *
        relativeIsoperimetricLHS (Metric.ball x (r * R)) s :=
  relativeIsoperimetricLHS_deGiorgiBlowUp_ball_of_one_le_finrank
    (Nat.succ_le_of_lt Module.finrank_pos) s x R hr
/-- **Scale- and translation-invariant reduction of the relative isoperimetric inequality on balls
to the unit ball**. -/
theorem relativeIsoperimetric_ball_of_unitBall_of_one_le_finrank
    (hdim : 1 ≤ Module.finrank ℝ E) {C : ℝ≥0∞} {s : Set E} (x : E) {r : ℝ} (hr : 0 < r)
    (hunit : relativeIsoperimetricLHS (Metric.ball (0 : E) 1) (deGiorgiBlowUp s x r) ≤
      C * relativePerimeter volume (openBall (0 : E) 1) (deGiorgiBlowUp s x r)) :
    relativeIsoperimetricLHS (Metric.ball x r) s ≤
      C * relativePerimeter volume (openBall x r) s := by
  have hLHS := relativeIsoperimetricLHS_deGiorgiBlowUp_ball_of_one_le_finrank hdim s x 1 hr
  have hRHS := relativePerimeter_deGiorgiBlowUp_ball s x 1 hr
  rw [mul_one] at hLHS hRHS; rw [hLHS, hRHS, ← mul_assoc, mul_comm C _, mul_assoc] at hunit
  exact (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.2 (Real.rpow_pos_of_pos hr _)) ENNReal.ofReal_ne_top).mp hunit
theorem relativeIsoperimetric_ball_of_unitBall [Nontrivial E] {C : ℝ≥0∞} {s : Set E} (x : E)
    {r : ℝ} (hr : 0 < r)
    (hunit : relativeIsoperimetricLHS (Metric.ball (0 : E) 1) (deGiorgiBlowUp s x r) ≤
      C * relativePerimeter volume (openBall (0 : E) 1) (deGiorgiBlowUp s x r)) :
    relativeIsoperimetricLHS (Metric.ball x r) s ≤
      C * relativePerimeter volume (openBall x r) s :=
  relativeIsoperimetric_ball_of_unitBall_of_one_le_finrank
    (Nat.succ_le_of_lt Module.finrank_pos) x hr hunit
theorem relativeIsoperimetric_forall_ball_of_unitBall [Nontrivial E] {C : ℝ≥0∞}
    (hunit : ∀ A : Set E, MeasurableSet A → relativeIsoperimetricLHS (Metric.ball (0 : E) 1) A ≤
      C * relativePerimeter volume (openBall (0 : E) 1) A)
    {s : Set E} (hs : MeasurableSet s) (x : E) {r : ℝ} (hr : 0 < r) :
    relativeIsoperimetricLHS (Metric.ball x r) s ≤
      C * relativePerimeter volume (openBall x r) s :=
  relativeIsoperimetric_ball_of_unitBall x hr
    (hunit (deGiorgiBlowUp s x r) (hs.preimage (by fun_prop)))

end RelativeVolumeMin

section OneDimRelativeBounds

/-- If `x₀ ∈ essentialExterior volume s`, `x₁ ∈ essentialInterior volume s`, and the closed
interval between `x₀` and `x₁` lies in `Ω : Opens ℝ`, then `1 ≤ relativePerimeter volume Ω s`. -/
theorem one_le_relativePerimeter_of_mem_essentialExterior_of_mem_essentialInterior
    {Ω : Opens ℝ} {s : Set ℝ} (hs : NullMeasurableSet s volume) {x₀ x₁ : ℝ}
    (hx₀ : x₀ ∈ essentialExterior volume s) (hx₁ : x₁ ∈ essentialInterior volume s)
    (hsub : Set.Icc (min x₀ x₁) (max x₀ x₁) ⊆ (Ω : Set ℝ)) :
    1 ≤ relativePerimeter volume Ω s := by
  have hu : LocallyIntegrableOn (s.indicator fun _ ↦ (1 : ℝ)) Ω volume :=
    (locallyIntegrableOn_top_indicator_one hs).mono_set (Set.subset_univ _)
  rcases le_total x₀ x₁ with hle | hle
  · have ht : Monotone ![x₀, x₁] := Fin.monotone_iff_le_succ.2 fun k ↦ by fin_cases k; exact hle
    have hsub' : Set.Icc (![x₀, x₁] 0) (![x₀, x₁] (Fin.last 1)) ⊆ (Ω : Set ℝ) := by
      simpa [min_eq_left hle, max_eq_right hle] using hsub
    simpa [relativePerimeter] using ofReal_sum_abs_sub_le_distributionalVariation
      (val := ![0, 1]) hu ht hsub' fun j ↦ by
        fin_cases j
        exacts [tendsto_bumpMollify_indicator_zero hx₀, tendsto_bumpMollify_indicator_one hs hx₁]
  · have ht : Monotone ![x₁, x₀] := Fin.monotone_iff_le_succ.2 fun k ↦ by fin_cases k; exact hle
    have hsub' : Set.Icc (![x₁, x₀] 0) (![x₁, x₀] (Fin.last 1)) ⊆ (Ω : Set ℝ) := by
      simpa [min_eq_right hle, max_eq_left hle] using hsub
    simpa [relativePerimeter] using ofReal_sum_abs_sub_le_distributionalVariation
      (val := ![1, 0]) hu ht hsub' fun j ↦ by
        fin_cases j
        exacts [tendsto_bumpMollify_indicator_one hs hx₁, tendsto_bumpMollify_indicator_zero hx₀]
/-- **Sharp 1D relative perimeter lower bound on `Set.Ioo a b`**: if
`0 < relativeVolumeMin (Set.Ioo a b) s`, then
`1 ≤ relativePerimeter volume ⟨Set.Ioo a b, isOpen_Ioo⟩ s`. -/
theorem one_le_relativePerimeter_Ioo_of_relativeVolumeMin_pos {a b : ℝ} {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (hpos : 0 < relativeVolumeMin (Set.Ioo a b) s) :
    1 ≤ relativePerimeter volume ⟨Set.Ioo a b, isOpen_Ioo⟩ s := by
  have h1 : 0 < volume (s ∩ Set.Ioo a b) := hpos.trans_le (relativeVolumeMin_le_volume_left _ _)
  have h2 : 0 < volume (Set.Ioo a b \ s) := hpos.trans_le (relativeVolumeMin_le_volume_right _ _)
  have hae1 : (essentialInterior volume s ∩ Set.Ioo a b : Set ℝ) =ᵐ[volume] s ∩ Set.Ioo a b :=
    EventuallyEqSet.inter (essentialInterior_ae_eq hs) EventuallyEq.rfl
  have h := EventuallyEqSet.inter (essentialExterior_ae_eq hs)
    (EventuallyEq.rfl : Set.Ioo a b =ᵐ[volume] Set.Ioo a b)
  have heq : sᶜ ∩ Set.Ioo a b = Set.Ioo a b \ s := by ext x; simp [and_comm]
  rw [heq] at h
  obtain ⟨x₁, hx₁_int, hx₁_Ioo⟩ := nonempty_of_measure_ne_zero (μ := volume)
    ((measure_congr hae1).trans_ne h1.ne')
  obtain ⟨x₀, hx₀_ext, hx₀_Ioo⟩ := nonempty_of_measure_ne_zero (μ := volume)
    ((measure_congr h).trans_ne h2.ne')
  exact one_le_relativePerimeter_of_mem_essentialExterior_of_mem_essentialInterior hs
    hx₀_ext hx₁_int (Set.ordConnected_Ioo.out (min_rec' (· ∈ Set.Ioo a b) hx₀_Ioo hx₁_Ioo)
      (max_rec' (· ∈ Set.Ioo a b) hx₀_Ioo hx₁_Ioo))
/-- **Exact 1D relative isoperimetric inequality on `Set.Ioo a b`**. -/
theorem relativeIsoperimetricLHS_Ioo_le_relativePerimeter {a b : ℝ} {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (hpos : 0 < relativeVolumeMin (Set.Ioo a b) s) :
    relativeIsoperimetricLHS (Set.Ioo a b) s ≤
      relativePerimeter volume ⟨Set.Ioo a b, isOpen_Ioo⟩ s := by
  simpa [relativeIsoperimetricLHS, Module.finrank_self] using
    one_le_relativePerimeter_Ioo_of_relativeVolumeMin_pos hs hpos
/-- **1D Poincaré-type relative volume bound on `Set.Ioo a b`**. -/
theorem relativeVolumeMin_Ioo_le_mul_relativePerimeter (a b : ℝ) {s : Set ℝ}
    (hs : NullMeasurableSet s volume) : relativeVolumeMin (Set.Ioo a b) s ≤
      ENNReal.ofReal ((b - a) / 2) * relativePerimeter volume ⟨Set.Ioo a b, isOpen_Ioo⟩ s := by
  rcases eq_zero_or_pos (relativeVolumeMin (Set.Ioo a b) s) with h0 | hpos; · simp [h0]
  have h2 := two_mul_relativeVolumeMin_le_volume (Set.Ioo a b) hs; rw [Real.volume_Ioo] at h2
  have hhalf : relativeVolumeMin (Set.Ioo a b) s ≤ ENNReal.ofReal ((b - a) / 2) := by
    rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_ofNat,
      ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_comm]
    exact h2
  exact (hhalf.trans_eq (mul_one _).symm).trans
    (by gcongr; exact one_le_relativePerimeter_Ioo_of_relativeVolumeMin_pos hs hpos)

end OneDimRelativeBounds

/-! ### Section 2: Two-Sided `(n-1)`-Ahlfors Density Bounds and Disjoint Ball Packing -/

section AhlforsDensityAndPacking

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem HasDeGiorgiBlowUp.tendsto_compl_density_one_half {s : Set E} {x ν : E}
    (h : HasDeGiorgiBlowUp s x ν) :
    Tendsto (fun r : ℝ ↦ volume (Metric.ball x r \ s) / volume (Metric.ball x r))
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  refine h.compl.tendsto_density_one_half.congr fun r ↦ ?_
  have h1 : sᶜ ∩ Metric.ball x r = Metric.ball x r \ s := by ext z; simp [and_comm]
  rw [h1]
/-- **Asymptotic relative-volume density `1 / 2` in `ℝ≥0∞`** at any point with a De Giorgi
blow-up. -/
theorem HasDeGiorgiBlowUp.tendsto_relativeVolumeMin_div_volume_ball_ennreal {s : Set E} {x ν : E}
    (h : HasDeGiorgiBlowUp s x ν) :
    Tendsto (fun r : ℝ ↦ relativeVolumeMin (Metric.ball x r) s / volume (Metric.ball x r))
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hmin := h.tendsto_density_one_half.min h.tendsto_compl_density_one_half
  rw [min_self] at hmin; refine hmin.congr fun r ↦ ?_
  have hmono : Monotone (fun a : ℝ≥0∞ ↦ a / volume (Metric.ball x r)) :=
    fun _ _ hab ↦ ENNReal.div_le_div_right hab _
  exact (hmono.map_min).symm
/-- **Asymptotic relative-volume density `1 / 2` in `ℝ`** at any point with a De Giorgi blow-up. -/
theorem HasDeGiorgiBlowUp.tendsto_relativeVolumeMin_div_volume_ball {s : Set E} {x ν : E}
    (h : HasDeGiorgiBlowUp s x ν) :
    Tendsto (fun r : ℝ ↦
      (relativeVolumeMin (Metric.ball x r) s).toReal / (volume (Metric.ball x r)).toReal)
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have henn := ENNReal.tendsto_toReal (by simp : (1 / 2 : ℝ≥0∞) ≠ ⊤)
    |>.comp h.tendsto_relativeVolumeMin_div_volume_ball_ennreal
  have hval : ((1 / 2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) := by norm_num
  rw [hval] at henn
  exact henn.congr' (by filter_upwards [self_mem_nhdsWithin] with r _; simp [ENNReal.toReal_div])
/-- **Two-sided volume-fraction bounds on small balls** around any point with a De Giorgi
blow-up. -/
theorem HasDeGiorgiBlowUp.eventually_relativeVolumeMin_ball_bounds {s : Set E} {x ν : E}
    (h : HasDeGiorgiBlowUp s x ν) : ∀ᶠ r in 𝓝[>] 0,
      (1 / 4 : ℝ≥0∞) * volume (Metric.ball x r) ≤ relativeVolumeMin (Metric.ball x r) s ∧
        relativeVolumeMin (Metric.ball x r) s ≤ volume (Metric.ball x r) := by
  have : Nontrivial E := ⟨⟨ν, 0, h.ne_zero⟩⟩
  have hlt1 : (1 / 4 : ℝ≥0∞) < 1 / 2 := by
    simpa using ENNReal.inv_lt_inv.mpr (by norm_num : (2 : ℝ≥0∞) < 4)
  have hlt2 : (1 / 2 : ℝ≥0∞) < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]; norm_num
  filter_upwards [self_mem_nhdsWithin,
    h.tendsto_relativeVolumeMin_div_volume_ball_ennreal.eventually (Icc_mem_nhds hlt1 hlt2)] with
    r (hr : 0 < r) ⟨h1, _⟩
  exact ⟨(ENNReal.le_div_iff_mul_le (Or.inl (Metric.measure_ball_pos volume x hr).ne')
    (Or.inl measure_ball_lt_top.ne)).mp h1, relativeVolumeMin_le_volume _ _⟩
theorem volume_ball_orthogonalHyperplane_eq_pow_mul_unitBall {e : E} (he : e ≠ 0) {r : ℝ}
    (hr : 0 < r) : volume (Metric.ball (0 : orthogonalHyperplane e) r) =
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
        volume (Metric.ball (0 : orthogonalHyperplane e) 1) := by
  have hfin := finrank_orthogonalHyperplane he
  rcases subsingleton_or_nontrivial (orthogonalHyperplane e) with hsub | hnt
  · have h0 : Module.finrank ℝ E - 1 = 0 := by rw [← hfin, Module.finrank_zero_of_subsingleton]
    have hball_r : Metric.ball (0 : orthogonalHyperplane e) r = Set.univ := by
      ext y; simp [Subsingleton.elim y 0, hr]
    have hball_1 : Metric.ball (0 : orthogonalHyperplane e) 1 = Set.univ := by
      ext y; simp [Subsingleton.elim y 0]
    simp [h0, hball_r, hball_1]
  · rw [Measure.addHaar_ball _ _ hr.le, hfin]
/-- **Asymptotic `(n - 1)`-dimensional perimeter density in `ℝ≥0∞`** at any point with a De Giorgi
outward unit normal `ν`. -/
theorem HasDeGiorgiNormal.tendsto_relativePerimeter_div_pow_ennreal {s : Set E} {x ν : E}
    (h : HasDeGiorgiNormal s x ν) :
    Tendsto (fun r : ℝ ↦ relativePerimeter volume (openBall x r) s /
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)))
      (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : orthogonalHyperplane ν) 1))) := by
  let ω := volume (Metric.ball (0 : orthogonalHyperplane ν) 1)
  have hω_pos : ω ≠ 0 := (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have hω_top : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hmul : Tendsto (fun r : ℝ ↦ (relativePerimeter volume (openBall x r) s /
      volume (Metric.ball (0 : orthogonalHyperplane ν) r)) * ω) (𝓝[>] 0) (𝓝 (1 * ω)) :=
    ENNReal.Tendsto.mul_const h.2 (Or.inr hω_top)
  rw [one_mul] at hmul; refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [volume_ball_orthogonalHyperplane_eq_pow_mul_unitBall h.1.ne_zero hr]
  have hc0 : ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (pow_pos hr _)
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top),
    mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hω_pos hω_top, mul_one, ← div_eq_mul_inv]
/-- **Asymptotic `(n - 1)`-dimensional perimeter density in `ℝ`** at any point with a De Giorgi
outward unit normal `ν`. -/
theorem HasDeGiorgiNormal.tendsto_relativePerimeter_div_rpow {s : Set E} {x ν : E}
    (h : HasDeGiorgiNormal s x ν) :
    Tendsto (fun r : ℝ ↦ (relativePerimeter volume (openBall x r) s).toReal /
      r ^ (Module.finrank ℝ E - 1))
      (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : orthogonalHyperplane ν) 1)).toReal) := by
  refine ((ENNReal.tendsto_toReal measure_ball_lt_top.ne).comp
    h.tendsto_relativePerimeter_div_pow_ennreal).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp [ENNReal.toReal_div, ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
/-- **Two-sided Ahlfors `(n - 1)`-regularity / perimeter density bounds** around any point `x`
with `HasDeGiorgiNormal s x ν`. -/
theorem HasDeGiorgiNormal.eventually_relativePerimeter_ball_bounds {s : Set E} {x ν : E}
    (h : HasDeGiorgiNormal s x ν) : ∀ᶠ r in 𝓝[>] 0,
      (1 / 2 : ℝ≥0∞) * volume (Metric.ball (0 : orthogonalHyperplane ν) r) ≤
        relativePerimeter volume (openBall x r) s ∧
      relativePerimeter volume (openBall x r) s ≤
        2 * volume (Metric.ball (0 : orthogonalHyperplane ν) r) := by
  have hlt1 : (1 / 2 : ℝ≥0∞) < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]; norm_num
  have hlt2 : (1 : ℝ≥0∞) < 2 := by norm_num
  filter_upwards [self_mem_nhdsWithin, h.2.eventually (Icc_mem_nhds hlt1 hlt2)] with
    r (hr : 0 < r) ⟨h1, h2⟩
  have hB0 : volume (Metric.ball (0 : orthogonalHyperplane ν) r) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 hr).ne'
  have hBtop : volume (Metric.ball (0 : orthogonalHyperplane ν) r) ≠ ⊤ := measure_ball_lt_top.ne
  exact ⟨(ENNReal.le_div_iff_mul_le (Or.inl hB0) (Or.inl hBtop)).mp h1,
    (ENNReal.div_le_iff_le_mul (Or.inl hB0) (Or.inl hBtop)).mp h2⟩
theorem eventually_relativePerimeter_ball_bounds_of_mem_reducedBoundary {s : Set E} {x : E}
    (hx : x ∈ reducedBoundary s) : ∀ᶠ r in 𝓝[>] 0,
      (1 / 2 : ℝ≥0∞) * volume (Metric.ball (0 : orthogonalHyperplane (deGiorgiNormal s x)) r) ≤
        relativePerimeter volume (openBall x r) s ∧
      relativePerimeter volume (openBall x r) s ≤
        2 * volume (Metric.ball (0 : orthogonalHyperplane (deGiorgiNormal s x)) r) :=
  (hasDeGiorgiNormal_deGiorgiNormal hx).eventually_relativePerimeter_ball_bounds

end AhlforsDensityAndPacking

section DisjointOpenPacking

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E} {Ω U V : Opens E}

/-- **Superadditivity of `distributionalVariation` on disjoint open subsets**: if `U ≤ Ω` and
`V ≤ Ω` are disjoint open sets, then
`distributionalVariation μ U u + distributionalVariation μ V u ≤ distributionalVariation μ Ω u`. -/
theorem distributionalVariation_add_le_of_disjoint (hU : U ≤ Ω) (hV : V ≤ Ω)
    (hdisj : Disjoint (U : Set E) (V : Set E)) (u : E → ℝ) :
    distributionalVariation μ U u + distributionalVariation μ V u ≤
      distributionalVariation μ Ω u := by
  conv_lhs => rw [distributionalVariation]
  rw [ENNReal.iSup_add]; refine iSup_le fun φ₁ ↦ ?_
  by_cases hφ₁ : ∀ x, ‖φ₁ x‖ ≤ 1
  · rw [ciSup_pos hφ₁, distributionalVariation, ENNReal.add_iSup]; refine iSup_le fun φ₂ ↦ ?_
    by_cases hφ₂ : ∀ x, ‖φ₂ x‖ ≤ 1
    · rw [ciSup_pos hφ₂]
      let φ₁' : 𝓓(U, E) := if 0 < ∫ x, u x * divergence (φ₁ : E → E) x ∂μ then φ₁ else 0
      let φ₂' : 𝓓(V, E) := if 0 < ∫ x, u x * divergence (φ₂ : E → E) x ∂μ then φ₂ else 0
      have hφ₁'_norm : ∀ x, ‖φ₁' x‖ ≤ 1 := fun x ↦ by
        dsimp [φ₁']; split_ifs; exacts [hφ₁ x, by simp]
      have hφ₂'_norm : ∀ x, ‖φ₂' x‖ ≤ 1 := fun x ↦ by
        dsimp [φ₂']; split_ifs; exacts [hφ₂ x, by simp]
      have hint₁ : Integrable (fun x ↦ u x * divergence (φ₁' : E → E) x) μ := by
        dsimp [φ₁']; split_ifs with h; exacts [not_imp_comm.mp integral_undef h.ne', by simp]
      have hint₂ : Integrable (fun x ↦ u x * divergence (φ₂' : E → E) x) μ := by
        dsimp [φ₂']; split_ifs with h; exacts [not_imp_comm.mp integral_undef h.ne', by simp]
      have hnn₁ : 0 ≤ ∫ x, u x * divergence (φ₁' : E → E) x ∂μ := by
        dsimp [φ₁']; split_ifs with h; exacts [h.le, by simp]
      have hnn₂ : 0 ≤ ∫ x, u x * divergence (φ₂' : E → E) x ∂μ := by
        dsimp [φ₂']; split_ifs with h; exacts [h.le, by simp]
      have heq₁ : ENNReal.ofReal (∫ x in (U : Set E), u x * divergence (φ₁ : E → E) x ∂μ) =
          ENNReal.ofReal (∫ x, u x * divergence (φ₁' : E → E) x ∂μ) := by
        rw [setIntegral_mul_divergence_eq_integral]; dsimp [φ₁']; split_ifs with h
        exacts [rfl, by simp [ENNReal.ofReal_eq_zero.2 (not_lt.mp h)]]
      have heq₂ : ENNReal.ofReal (∫ x in (V : Set E), u x * divergence (φ₂ : E → E) x ∂μ) =
          ENNReal.ofReal (∫ x, u x * divergence (φ₂' : E → E) x ∂μ) := by
        rw [setIntegral_mul_divergence_eq_integral]; dsimp [φ₂']; split_ifs with h
        exacts [rfl, by simp [ENNReal.ofReal_eq_zero.2 (not_lt.mp h)]]
      let ψ₁ : 𝓓(Ω, E) := TestFunction.monoCLM ℝ φ₁'
      let ψ₂ : 𝓓(Ω, E) := TestFunction.monoCLM ℝ φ₂'
      let ψ : 𝓓(Ω, E) := ψ₁ + ψ₂
      have hψ₁_coe : (ψ₁ : E → E) = (φ₁' : E → E) := by
        ext x; simp [ψ₁, TestFunction.monoCLM_apply, hU]
      have hψ₂_coe : (ψ₂ : E → E) = (φ₂' : E → E) := by
        ext x; simp [ψ₂, TestFunction.monoCLM_apply, hV]
      have hψ_coe : (ψ : E → E) = (φ₁' : E → E) + (φ₂' : E → E) := by
        ext x; simp [ψ, congrFun hψ₁_coe x, congrFun hψ₂_coe x]
      have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
        change ‖ψ₁ x + ψ₂ x‖ ≤ 1; rw [congrFun hψ₁_coe x, congrFun hψ₂_coe x]
        by_cases hxU : x ∈ (U : Set E)
        · have hxV : x ∉ tsupport (φ₂' : E → E) := fun h ↦ hdisj.le_bot ⟨hxU, φ₂'.tsupport_subset h⟩
          rw [image_eq_zero_of_notMem_tsupport hxV, add_zero]; exact hφ₁'_norm x
        · have hxU' : x ∉ tsupport (φ₁' : E → E) := fun h ↦ hxU (φ₁'.tsupport_subset h)
          rw [image_eq_zero_of_notMem_tsupport hxU', zero_add]; exact hφ₂'_norm x
      have hdiv : ∀ x, u x * divergence (ψ : E → E) x =
          u x * divergence (φ₁' : E → E) x + u x * divergence (φ₂' : E → E) x := fun x ↦ by
        rw [hψ_coe, divergence_add (φ₁'.contDiff.differentiable (by simp) x)
          (φ₂'.contDiff.differentiable (by simp) x), mul_add]
      rw [heq₁, heq₂, ← ENNReal.ofReal_add hnn₁ hnn₂, ← integral_add hint₁ hint₂]
      simp_rw [← hdiv]; rw [← setIntegral_mul_divergence_eq_integral]
      exact le_distributionalVariation ψ hψ_norm u
    · simp only [hφ₂, iSup_false, bot_eq_zero, add_zero]
      exact (le_distributionalVariation φ₁ hφ₁ u).trans (distributionalVariation_mono hU u)
  · simp only [hφ₁, iSup_false, bot_eq_zero, zero_add]
    exact distributionalVariation_mono hV u
theorem relativePerimeter_add_le_of_disjoint (hU : U ≤ Ω) (hV : V ≤ Ω)
    (hdisj : Disjoint (U : Set E) (V : Set E)) (s : Set E) :
    relativePerimeter μ U s + relativePerimeter μ V s ≤ relativePerimeter μ Ω s :=
  distributionalVariation_add_le_of_disjoint hU hV hdisj _
/-- **Finite-family superadditivity of `distributionalVariation`** across pairwise disjoint open
subsets `U i ≤ Ω`. -/
theorem sum_distributionalVariation_le_of_pairwiseDisjoint {ι : Type*}
    (I : Finset ι) (U : ι → Opens E) (hdisj : (I : Set ι).PairwiseDisjoint fun i ↦ (U i : Set E))
    (hsub : ∀ i ∈ I, U i ≤ Ω) (u : E → ℝ) :
    ∑ i ∈ I, distributionalVariation μ (U i) u ≤ distributionalVariation μ Ω u := by
  classical
  induction I using Finset.cons_induction generalizing Ω with
  | empty => simp
  | cons a s ha ih =>
    let W : Opens E := ⟨⋃ i ∈ s, (U i : Set E), isOpen_biUnion fun i _ ↦ (U i).isOpen⟩
    have hW_sub : W ≤ Ω := Set.iUnion₂_subset fun i hi ↦ hsub i (Finset.mem_cons_of_mem hi)
    have haW_disj : Disjoint (U a : Set E) (W : Set E) :=
      Set.disjoint_iUnion₂_right.mpr fun i hi ↦
        hdisj (Finset.mem_cons_self a s) (Finset.mem_cons_of_mem hi)
          (ne_of_mem_of_not_mem hi ha).symm
    have hih : ∑ i ∈ s, distributionalVariation μ (U i) u ≤ distributionalVariation μ W u :=
      ih (hdisj.subset (Finset.subset_cons ha))
        (fun i hi ↦ Set.subset_biUnion_of_mem (u := fun j ↦ (U j : Set E)) hi)
    rw [Finset.sum_cons]
    exact (add_le_add le_rfl hih).trans
      (distributionalVariation_add_le_of_disjoint (hsub a (Finset.mem_cons_self a s))
        hW_sub haW_disj u)
theorem sum_relativePerimeter_le_of_pairwiseDisjoint {ι : Type*}
    (I : Finset ι) (U : ι → Opens E) (hdisj : (I : Set ι).PairwiseDisjoint fun i ↦ (U i : Set E))
    (hsub : ∀ i ∈ I, U i ≤ Ω) (s : Set E) :
    ∑ i ∈ I, relativePerimeter μ (U i) s ≤ relativePerimeter μ Ω s :=
  sum_distributionalVariation_le_of_pairwiseDisjoint I U hdisj hsub _

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- **Disjoint ball packing bound for `relativePerimeter`** on pairwise disjoint open balls in
`U`. -/
theorem sum_relativePerimeter_openBall_le_of_pairwiseDisjoint {ι : Type*}
    (I : Finset ι) (x : ι → E) (r : ι → ℝ) (U : Opens E)
    (hdisj : (I : Set ι).PairwiseDisjoint fun i ↦ Metric.ball (x i) (r i))
    (hsub : ∀ i ∈ I, Metric.ball (x i) (r i) ⊆ (U : Set E)) (s : Set E) :
    ∑ i ∈ I, relativePerimeter volume (openBall (x i) (r i)) s ≤ relativePerimeter volume U s :=
  sum_relativePerimeter_le_of_pairwiseDisjoint I (fun i ↦ openBall (x i) (r i)) hdisj hsub s
theorem sum_relativePerimeter_openBall_le_perimeter_of_pairwiseDisjoint {ι : Type*}
    (I : Finset ι) (x : ι → E) (r : ι → ℝ)
    (hdisj : (I : Set ι).PairwiseDisjoint fun i ↦ Metric.ball (x i) (r i)) (s : Set E) :
    ∑ i ∈ I, relativePerimeter volume (openBall (x i) (r i)) s ≤ perimeter volume s :=
  sum_relativePerimeter_openBall_le_of_pairwiseDisjoint I x r ⊤ hdisj
    (fun _ _ ↦ Set.subset_univ _) s

end DisjointOpenPacking

/-! ### Section 3: Iterated Steiner Symmetrization along Lists and Sequences of Directions -/

section IteratedSteinerSymmetrization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Iterated Steiner symmetrization** `iteratedSteinerSymmetrization dirs s` along a finite list
of directions `dirs : List E`, applied from left to right. -/
@[expose] def iteratedSteinerSymmetrization (dirs : List E) (s : Set E) : Set E :=
  dirs.foldl (fun A e ↦ steinerSymmetrization e A) s
/-- **Sequential Steiner symmetrization** `steinerSymmetrizationSeq e k s` along the first `k`
directions `e 0, ..., e (k - 1)` of a sequence `e : ℕ → E`. -/
@[expose] def steinerSymmetrizationSeq (e : ℕ → E) (k : ℕ) (s : Set E) : Set E :=
  iteratedSteinerSymmetrization ((List.range k).map e) s
theorem iteratedSteinerSymmetrization_eq_steinerSymmetrizationList (dirs : List E) (s : Set E) :
    iteratedSteinerSymmetrization dirs s = steinerSymmetrizationList dirs s := by rfl
@[simp] theorem iteratedSteinerSymmetrization_nil (s : Set E) :
    iteratedSteinerSymmetrization ([] : List E) s = s := rfl
@[simp] theorem iteratedSteinerSymmetrization_cons (e : E) (dirs : List E) (s : Set E) :
    iteratedSteinerSymmetrization (e :: dirs) s =
      iteratedSteinerSymmetrization dirs (steinerSymmetrization e s) := rfl
@[simp] theorem iteratedSteinerSymmetrization_singleton (e : E) (s : Set E) :
    iteratedSteinerSymmetrization [e] s = steinerSymmetrization e s := rfl
@[simp] theorem iteratedSteinerSymmetrization_append (dirs₁ dirs₂ : List E) (s : Set E) :
    iteratedSteinerSymmetrization (dirs₁ ++ dirs₂) s =
      iteratedSteinerSymmetrization dirs₂ (iteratedSteinerSymmetrization dirs₁ s) :=
  List.foldl_append
@[simp] theorem steinerSymmetrizationSeq_zero (e : ℕ → E) (s : Set E) :
    steinerSymmetrizationSeq e 0 s = s := rfl
@[simp] theorem steinerSymmetrizationSeq_succ (e : ℕ → E) (k : ℕ) (s : Set E) :
    steinerSymmetrizationSeq e (k + 1) s =
      steinerSymmetrization (e k) (steinerSymmetrizationSeq e k s) := by
  simp [steinerSymmetrizationSeq, List.range_succ]
@[simp] theorem iteratedSteinerSymmetrization_empty (dirs : List E) :
    iteratedSteinerSymmetrization dirs (∅ : Set E) = ∅ := by
  induction dirs with | nil => rfl | cons e dirs ih => simp [ih]
@[simp] theorem iteratedSteinerSymmetrization_univ (dirs : List E) :
    iteratedSteinerSymmetrization dirs (Set.univ : Set E) = Set.univ := by
  induction dirs with | nil => rfl | cons e dirs ih => simp [ih]
theorem iteratedSteinerSymmetrization_mono (dirs : List E) {s t : Set E} (hst : s ⊆ t) :
    iteratedSteinerSymmetrization dirs s ⊆ iteratedSteinerSymmetrization dirs t := by
  induction dirs generalizing s t with
  | nil => exact hst | cons e dirs ih => exact ih (steinerSymmetrization_mono hst)
theorem steinerSymmetrizationSeq_mono (e : ℕ → E) (k : ℕ) {s t : Set E} (hst : s ⊆ t) :
    steinerSymmetrizationSeq e k s ⊆ steinerSymmetrizationSeq e k t :=
  iteratedSteinerSymmetrization_mono _ hst
/-- **Unconditional convexity preservation under Steiner symmetrization**: for any convex set
`s : Set E` and any direction `e : E`, `steinerSymmetrization e s` is convex (without any
boundedness or finite-volume assumption). -/
theorem convex_steinerSymmetrization (e : E) {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ (steinerSymmetrization e s) := by
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha_pos; · have hb1 : b = 1 := by linarith
                                          simpa [hb1] using hx₂
  rcases hb.eq_or_lt with rfl | hb_pos; · have ha1 : a = 1 := by linarith
                                          simpa [ha1] using hx₁
  rw [mem_steinerSymmetrization_iff_volume] at hx₁ hx₂ ⊢
  set y₁ := (orthogonalHyperplane e).orthogonalProjectionOnto x₁
  set y₂ := (orthogonalHyperplane e).orthogonalProjectionOnto x₂; set y₃ := a • y₁ + b • y₂
  have hproj : (orthogonalHyperplane e).orthogonalProjectionOnto (a • x₁ + b • x₂) = y₃ := by
    simp [y₃, y₁, y₂, map_add, map_smul]
  have hinner : ⟪a • x₁ + b • x₂, e⟫_ℝ = a * ⟪x₁, e⟫_ℝ + b * ⟪x₂, e⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [hproj, hinner]; rcases eq_top_or_lt_top (volume (steinerFiber e s y₃)) with htop₃ | hfin₃
  · simp [htop₃]
  · obtain ⟨u₁, hu₁⟩ : (steinerFiber e s y₁).Nonempty := nonempty_of_measure_ne_zero hx₁.1
    obtain ⟨u₂, hu₂⟩ : (steinerFiber e s y₂).Nonempty := nonempty_of_measure_ne_zero hx₂.1
    have hI₃ : (steinerFiber e s y₃).OrdConnected := hs.ordConnected_steinerFiber e y₃
    have hbdd₁ := hI₃.bddBelow_of_volume_lt_top hfin₃
    have hbdd₂ := hI₃.bddAbove_of_volume_lt_top hfin₃
    have hfin₁ : volume (steinerFiber e s y₁) < ⊤ :=
      (measure_mono (t := Set.Icc ((sInf (steinerFiber e s y₃) - b * u₂) / a)
        ((sSup (steinerFiber e s y₃) - b * u₂) / a)) fun t₁ ht₁ ↦
        have ht₃ := add_mul_mem_steinerFiber_of_convex hs ht₁ hu₂ ha hb hab
        ⟨(div_le_iff₀ ha_pos).2 (by linarith [csInf_le hbdd₁ ht₃]),
          (le_div_iff₀ ha_pos).2 (by linarith [le_csSup hbdd₂ ht₃])⟩).trans_lt measure_Icc_lt_top
    have hfin₂ : volume (steinerFiber e s y₂) < ⊤ :=
      (measure_mono (t := Set.Icc ((sInf (steinerFiber e s y₃) - a * u₁) / b)
        ((sSup (steinerFiber e s y₃) - a * u₁) / b)) fun t₂ ht₂ ↦
        have ht₃ := add_mul_mem_steinerFiber_of_convex hs hu₁ ht₂ ha hb hab
        ⟨(div_le_iff₀ hb_pos).2 (by linarith [csInf_le hbdd₁ ht₃]),
          (le_div_iff₀ hb_pos).2 (by linarith [le_csSup hbdd₂ ht₃])⟩).trans_lt measure_Icc_lt_top
    have hconc := hs.add_mul_toReal_volume_steinerFiber_le ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ ha hb hab
      hfin₁ hfin₂ hfin₃
    have hv₁_pos : 0 < (volume (steinerFiber e s y₁)).toReal := ENNReal.toReal_pos hx₁.1 hfin₁.ne
    have hv₂_pos : 0 < (volume (steinerFiber e s y₂)).toReal := ENNReal.toReal_pos hx₂.1 hfin₂.ne
    have hv₃_pos : 0 < (volume (steinerFiber e s y₃)).toReal := by nlinarith
    have hv₃_ne : volume (steinerFiber e s y₃) ≠ 0 := fun h0 ↦ by simp [h0] at hv₃_pos
    have ht₁ : 2 * |⟪x₁, e⟫_ℝ| ≤ (volume (steinerFiber e s y₁)).toReal := by
      simpa [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * |⟪x₁, e⟫_ℝ|)] using
        (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin₁.ne).mpr hx₁.2
    have ht₂ : 2 * |⟪x₂, e⟫_ℝ| ≤ (volume (steinerFiber e s y₂)).toReal := by
      simpa [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * |⟪x₂, e⟫_ℝ|)] using
        (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin₂.ne).mpr hx₂.2
    refine ⟨hv₃_ne, ?_⟩; rw [← ENNReal.ofReal_toReal hfin₃.ne]; refine ENNReal.ofReal_le_ofReal ?_
    have habs : |a * ⟪x₁, e⟫_ℝ + b * ⟪x₂, e⟫_ℝ| ≤ a * |⟪x₁, e⟫_ℝ| + b * |⟪x₂, e⟫_ℝ| :=
      (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_pos ha_pos, abs_of_pos hb_pos])
    nlinarith
/-- **Iterated Steiner symmetrization preserves convexity**. -/
theorem convex_iteratedSteinerSymmetrization (dirs : List E) {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ (iteratedSteinerSymmetrization dirs s) := by
  induction dirs generalizing s with
  | nil => exact hs | cons e dirs ih => exact ih (convex_steinerSymmetrization e hs)
theorem convex_steinerSymmetrizationSeq (e : ℕ → E) (k : ℕ) {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ (steinerSymmetrizationSeq e k s) := convex_iteratedSteinerSymmetrization _ hs
theorem subset_closedBall_steinerSymmetrization {e : E} (he : ‖e‖ = 1) {s : Set E} {R : ℝ}
    (hs : s ⊆ Metric.closedBall (0 : E) R) :
    steinerSymmetrization e s ⊆ Metric.closedBall (0 : E) R :=
  (steinerSymmetrization_mono hs).trans (steinerSymmetrization_closedBall_subset_closedBall he R)
/-- **Closed-ball containment is preserved under `iteratedSteinerSymmetrization`**. -/
theorem subset_closedBall_iteratedSteinerSymmetrization {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {s : Set E} {R : ℝ} (hs : s ⊆ Metric.closedBall (0 : E) R) :
    iteratedSteinerSymmetrization dirs s ⊆ Metric.closedBall (0 : E) R := by
  induction dirs generalizing s with | nil => exact hs | cons e dirs ih =>
    exact ih (List.forall_mem_cons.mp hdirs).2
      (subset_closedBall_steinerSymmetrization (List.forall_mem_cons.mp hdirs).1 hs)
theorem subset_closedBall_steinerSymmetrizationSeq {e : ℕ → E} (he : ∀ k, ‖e k‖ = 1) (k : ℕ)
    {s : Set E} {R : ℝ} (hs : s ⊆ Metric.closedBall (0 : E) R) :
    steinerSymmetrizationSeq e k s ⊆ Metric.closedBall (0 : E) R :=
  subset_closedBall_iteratedSteinerSymmetrization (by simp [he]) hs
theorem ball_subset_iteratedSteinerSymmetrization_ball {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) (R : ℝ) :
    Metric.ball (0 : E) R ⊆ iteratedSteinerSymmetrization dirs (Metric.ball (0 : E) R) := by
  induction dirs with | nil => exact Set.Subset.rfl | cons e dirs ih =>
    exact (ih (List.forall_mem_cons.mp hdirs).2).trans (iteratedSteinerSymmetrization_mono dirs
      (ball_subset_steinerSymmetrization_ball (List.forall_mem_cons.mp hdirs).1 R))
theorem iteratedSteinerSymmetrization_ball_subset_closedBall {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) (R : ℝ) :
    iteratedSteinerSymmetrization dirs (Metric.ball (0 : E) R) ⊆ Metric.closedBall (0 : E) R :=
  subset_closedBall_iteratedSteinerSymmetrization hdirs Metric.ball_subset_closedBall
@[simp] theorem interior_iteratedSteinerSymmetrization_ball {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {R : ℝ} (hR : 0 < R) :
    interior (iteratedSteinerSymmetrization dirs (Metric.ball (0 : E) R)) =
      Metric.ball (0 : E) R :=
  Set.Subset.antisymm ((interior_mono
      (iteratedSteinerSymmetrization_ball_subset_closedBall hdirs R)).trans_eq
    (interior_closedBall 0 hR.ne'))
    (interior_maximal (ball_subset_iteratedSteinerSymmetrization_ball hdirs R) Metric.isOpen_ball)

variable [MeasurableSpace E] [BorelSpace E]

@[measurability] theorem measurableSet_iteratedSteinerSymmetrization (dirs : List E) {s : Set E}
    (hs : MeasurableSet s) : MeasurableSet (iteratedSteinerSymmetrization dirs s) :=
  measurableSet_steinerSymmetrizationList dirs hs
@[measurability] theorem measurableSet_steinerSymmetrizationSeq (e : ℕ → E) (k : ℕ) {s : Set E}
    (hs : MeasurableSet s) : MeasurableSet (steinerSymmetrizationSeq e k s) :=
  measurableSet_iteratedSteinerSymmetrization _ hs

variable [FiniteDimensional ℝ E]

theorem iteratedSteinerSymmetrization_ae_eq {dirs : List E} (hdirs : ∀ e ∈ dirs, ‖e‖ = 1)
    {s t : Set E} (hst : s =ᵐ[volume] t) :
    iteratedSteinerSymmetrization dirs s =ᵐ[volume] iteratedSteinerSymmetrization dirs t := by
  induction dirs generalizing s t with | nil => exact hst | cons e dirs ih =>
    exact ih (List.forall_mem_cons.mp hdirs).2
      (steinerSymmetrization_ae_eq (List.forall_mem_cons.mp hdirs).1 hst)
theorem nullMeasurableSet_iteratedSteinerSymmetrization {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) :
    NullMeasurableSet (iteratedSteinerSymmetrization dirs s) volume := by
  induction dirs generalizing s with | nil => exact hs | cons e dirs ih =>
    exact ih (List.forall_mem_cons.mp hdirs).2
      (nullMeasurableSet_steinerSymmetrization (List.forall_mem_cons.mp hdirs).1 hs)
theorem nullMeasurableSet_steinerSymmetrizationSeq {e : ℕ → E} (he : ∀ k, ‖e k‖ = 1) (k : ℕ)
    {s : Set E} (hs : NullMeasurableSet s volume) :
    NullMeasurableSet (steinerSymmetrizationSeq e k s) volume :=
  nullMeasurableSet_iteratedSteinerSymmetrization (by simp [he]) hs
/-- **Volume preservation of `iteratedSteinerSymmetrization`** for measurable sets. -/
theorem volume_iteratedSteinerSymmetrization {dirs : List E} (hdirs : ∀ e ∈ dirs, ‖e‖ = 1)
    {s : Set E} (hs : MeasurableSet s) : volume (iteratedSteinerSymmetrization dirs s) = volume s :=
  volume_steinerSymmetrizationList hdirs hs
theorem volume_iteratedSteinerSymmetrization₀ {dirs : List E} (hdirs : ∀ e ∈ dirs, ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) :
    volume (iteratedSteinerSymmetrization dirs s) = volume s := by
  rcases hs with ⟨t, htm, hst⟩
  rw [measure_congr (iteratedSteinerSymmetrization_ae_eq hdirs hst),
    volume_iteratedSteinerSymmetrization hdirs htm, measure_congr hst]
theorem volume_steinerSymmetrizationSeq {e : ℕ → E} (he : ∀ k, ‖e k‖ = 1) (k : ℕ)
    {s : Set E} (hs : NullMeasurableSet s volume) :
    volume (steinerSymmetrizationSeq e k s) = volume s :=
  volume_iteratedSteinerSymmetrization₀ (by simp [he]) hs
/-- **Centered open balls are a.e. fixed under `iteratedSteinerSymmetrization`**. -/
theorem iteratedSteinerSymmetrization_ball_ae_eq {dirs : List E} (hdirs : ∀ e ∈ dirs, ‖e‖ = 1)
    (R : ℝ) : iteratedSteinerSymmetrization dirs (Metric.ball (0 : E) R) =ᵐ[volume]
      Metric.ball (0 : E) R := by
  induction dirs with | nil => exact EventuallyEq.rfl | cons e dirs ih =>
    rcases List.forall_mem_cons.mp hdirs with ⟨he, hd⟩; rw [iteratedSteinerSymmetrization_cons]
    exact (iteratedSteinerSymmetrization_ae_eq hd (steinerSymmetrization_ball_ae_eq he R)).trans
      (ih hd)
/-- **Centered closed balls are a.e. fixed under `iteratedSteinerSymmetrization`**. -/
theorem iteratedSteinerSymmetrization_closedBall_ae_eq {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) (R : ℝ) :
    iteratedSteinerSymmetrization dirs (Metric.closedBall (0 : E) R) =ᵐ[volume]
      Metric.closedBall (0 : E) R := by
  induction dirs with | nil => exact EventuallyEq.rfl | cons e dirs ih =>
    rcases List.forall_mem_cons.mp hdirs with ⟨he, hd⟩; rw [iteratedSteinerSymmetrization_cons]
    exact (iteratedSteinerSymmetrization_ae_eq hd
      (steinerSymmetrization_closedBall_ae_eq he R)).trans (ih hd)
/-- **Two-set intersection inequality for `iteratedSteinerSymmetrization`**. -/
theorem volume_inter_le_volume_iteratedSteinerSymmetrization_inter {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {s t : Set E}
    (hs : NullMeasurableSet s volume) (ht : NullMeasurableSet t volume) : volume (s ∩ t) ≤
      volume (iteratedSteinerSymmetrization dirs s ∩ iteratedSteinerSymmetrization dirs t) := by
  induction dirs generalizing s t with | nil => exact le_rfl | cons e dirs ih =>
    rcases List.forall_mem_cons.mp hdirs with ⟨he, hd⟩
    exact (volume_inter_le_volume_steinerSymmetrization_inter₀ he hs ht).trans
      (ih hd (nullMeasurableSet_steinerSymmetrization he hs)
        (nullMeasurableSet_steinerSymmetrization he ht))
theorem volume_diff_iteratedSteinerSymmetrization_le {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {s t : Set E}
    (hs : NullMeasurableSet s volume) (ht : NullMeasurableSet t volume) :
    volume (iteratedSteinerSymmetrization dirs s \ iteratedSteinerSymmetrization dirs t) ≤
      volume (s \ t) := by
  induction dirs generalizing s t with | nil => exact le_rfl | cons e dirs ih =>
    rcases List.forall_mem_cons.mp hdirs with ⟨he, hd⟩
    exact (ih hd (nullMeasurableSet_steinerSymmetrization he hs)
      (nullMeasurableSet_steinerSymmetrization he ht)).trans
      (volume_diff_steinerSymmetrization_le₀ he hs ht)
/-- **`L¹` contraction on symmetric differences for `iteratedSteinerSymmetrization`**. -/
theorem volume_symmDiff_iteratedSteinerSymmetrization_le₀ {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {s t : Set E}
    (hs : NullMeasurableSet s volume) (ht : NullMeasurableSet t volume) :
    volume (iteratedSteinerSymmetrization dirs s ∆ iteratedSteinerSymmetrization dirs t) ≤
      volume (s ∆ t) := by
  induction dirs generalizing s t with | nil => exact le_rfl | cons e dirs ih =>
    rcases List.forall_mem_cons.mp hdirs with ⟨he, hd⟩
    exact (ih hd (nullMeasurableSet_steinerSymmetrization he hs)
      (nullMeasurableSet_steinerSymmetrization he ht)).trans
      (volume_symmDiff_steinerSymmetrization_le₀ he hs ht)
theorem volume_symmDiff_iteratedSteinerSymmetrization_le {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {s t : Set E} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    volume (iteratedSteinerSymmetrization dirs s ∆ iteratedSteinerSymmetrization dirs t) ≤
      volume (s ∆ t) :=
  volume_symmDiff_iteratedSteinerSymmetrization_le₀ hdirs
    hs.nullMeasurableSet ht.nullMeasurableSet
/-- **`L¹` indicator contraction for `iteratedSteinerSymmetrization`**. -/
theorem lintegral_edist_indicator_iteratedSteinerSymmetrization_le {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {s t : Set E}
    (hs : NullMeasurableSet s volume) (ht : NullMeasurableSet t volume) :
    (∫⁻ x : E, edist ((iteratedSteinerSymmetrization dirs s).indicator (1 : E → ℝ) x)
        ((iteratedSteinerSymmetrization dirs t).indicator (1 : E → ℝ) x) ∂volume) ≤
      ∫⁻ x : E, edist (s.indicator (1 : E → ℝ) x) (t.indicator (1 : E → ℝ) x) ∂volume := by
  rw [lintegral_edist_indicator_one volume
      (nullMeasurableSet_iteratedSteinerSymmetrization hdirs hs)
      (nullMeasurableSet_iteratedSteinerSymmetrization hdirs ht),
    lintegral_edist_indicator_one volume hs ht]
  exact volume_symmDiff_iteratedSteinerSymmetrization_le₀ hdirs hs ht
theorem volume_symmDiff_iteratedSteinerSymmetrization_ball_le {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (R : ℝ) :
    volume (iteratedSteinerSymmetrization dirs s ∆ Metric.ball (0 : E) R) ≤
      volume (s ∆ Metric.ball (0 : E) R) := by
  rw [measure_congr (EventuallyEqSet.symmDiff EventuallyEq.rfl
    (iteratedSteinerSymmetrization_ball_ae_eq hdirs R).symm)]
  exact volume_symmDiff_iteratedSteinerSymmetrization_le₀ hdirs hs
    measurableSet_ball.nullMeasurableSet
theorem volume_symmDiff_iteratedSteinerSymmetrization_closedBall_le {dirs : List E}
    (hdirs : ∀ e ∈ dirs, ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (R : ℝ) :
    volume (iteratedSteinerSymmetrization dirs s ∆ Metric.closedBall (0 : E) R) ≤
      volume (s ∆ Metric.closedBall (0 : E) R) := by
  rw [measure_congr (EventuallyEqSet.symmDiff EventuallyEq.rfl
    (iteratedSteinerSymmetrization_closedBall_ae_eq hdirs R).symm)]
  exact volume_symmDiff_iteratedSteinerSymmetrization_le₀ hdirs hs
    measurableSet_closedBall.nullMeasurableSet
/-- **Monotonic decrease of the `L¹` distance to any centered open ball** along a sequence of
Steiner symmetrizations in unit directions `e : ℕ → E`. -/
theorem antitone_volume_symmDiff_steinerSymmetrizationSeq_ball {e : ℕ → E} (he : ∀ k, ‖e k‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (R : ℝ) :
    Antitone (fun k : ℕ ↦ volume (steinerSymmetrizationSeq e k s ∆ Metric.ball (0 : E) R)) :=
  antitone_nat_of_succ_le fun k ↦ by
    rw [steinerSymmetrizationSeq_succ, ← iteratedSteinerSymmetrization_singleton]
    exact volume_symmDiff_iteratedSteinerSymmetrization_ball_le
      (List.forall_mem_singleton.mpr (he k)) (nullMeasurableSet_steinerSymmetrizationSeq he k hs) R
/-- **Monotonic decrease of the `L¹` distance to any centered closed ball** along a sequence of
Steiner symmetrizations in unit directions `e : ℕ → E`. -/
theorem antitone_volume_symmDiff_steinerSymmetrizationSeq_closedBall {e : ℕ → E}
    (he : ∀ k, ‖e k‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (R : ℝ) : Antitone
      (fun k : ℕ ↦ volume (steinerSymmetrizationSeq e k s ∆ Metric.closedBall (0 : E) R)) :=
  antitone_nat_of_succ_le fun k ↦ by
    rw [steinerSymmetrizationSeq_succ, ← iteratedSteinerSymmetrization_singleton]
    exact volume_symmDiff_iteratedSteinerSymmetrization_closedBall_le
      (List.forall_mem_singleton.mpr (he k)) (nullMeasurableSet_steinerSymmetrizationSeq he k hs) R

end IteratedSteinerSymmetrization

end TauCeti
