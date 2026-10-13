/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Data.Set.SymmDiff
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# Schwarz Rearrangement, Equimeasurability, `Lᵖ` Contraction, and the Hardy–Littlewood Inequality

This file constructs the set-level Schwarz symmetrization and function-level Schwarz rearrangement
(symmetric decreasing rearrangement) on `EuclideanSpace ℝ (Fin n)`, and establishes their
fundamental measure-theoretic and `Lᵖ` properties:

1. **Set-level Schwarz symmetrization (`TauCeti.schwarzSymmetrization`)**:
   For any set `E : Set (EuclideanSpace ℝ (Fin n))`, `schwarzSymmetrization E` is the centered open
   ball `{x | unitBallVolume n * ‖x‖ₑ ^ n < volume E}`. When `volume E < ⊤`, it coincides with
   `Metric.ball 0 (schwarzRadius E)`. It is open, measurable, monotone in `volume E`, invariant
   under almost-everywhere equality, preserves Lebesgue volume (`volume_schwarzSymmetrization`),
   satisfies the two-set Riesz / Fréchet rearrangement inequality
   (`volume_inter_le_volume_schwarzSymmetrization_inter`), and contracts both one-sided set
   differences (`volume_diff_schwarzSymmetrization_le`) and symmetric differences
   (`volume_symmDiff_schwarzSymmetrization_le`).
2. **Radial profile and Schwarz rearrangement (`TauCeti.schwarzRadialProfile`,
   `TauCeti.schwarzRearrangement`)**:
   Defined via the distribution function `distributionFunction f t = volume {y | t < f y}` by
   `schwarzRadialProfile f r = sSup {t > 0 | unitBallVolume n * r ^ n < distributionFunction f t}`
   and `schwarzRearrangement f x = schwarzRadialProfile f ‖x‖`.
3. **Galois connection and superlevel / sublevel set identities**:
   `lt_schwarzRadialProfile_iff`, `lt_schwarzRearrangement_iff`, `superlevel_schwarzRearrangement`,
   and `sublevel_schwarzRearrangement` identify `{x | t < schwarzRearrangement f x}` unconditionally
   with `schwarzSymmetrization {y | t < f y}` without any continuity or finiteness hypotheses.
4. **Measurability, a.e. representative invariance, order preservation, and equimeasurability**:
   `measurable_schwarzRearrangement`, `schwarzRearrangement_congr_ae`,
   `schwarzRearrangement_mono_ae`, `volume_lt_schwarzRearrangement`,
   `lintegral_rpow_schwarzRearrangement`, `lintegral_schwarzRearrangement`,
   `eLpNorm_schwarzRearrangement`, and `memLp_schwarzRearrangement_iff`.
5. **Finiteness of superlevel volumes and of the radial profile for `r > 0`**:
   Markov bounds (`distributionFunction_le_lintegral_rpow_div`,
   `schwarzRadialProfile_rpow_le_lintegral_rpow_div`) and finiteness theorems
   (`distributionFunction_lt_top_of_memLp`, `schwarzRadialProfile_lt_top_of_memLp`,
   `schwarzRadialProfile_lt_top_of_distributionFunction_lt_top`,
   `schwarzRearrangement_lt_top_of_ne_zero`, `schwarzRearrangement_lt_top_ae`).
6. **The Hardy–Littlewood rearrangement inequality**:
   `lintegral_mul_eq_lintegral_lintegral_meas_lt` and
   `lintegral_mul_le_lintegral_schwarzRearrangement_mul`.
7. **Real-valued specialization (`TauCeti.schwarzRearrangementReal`) and `Lᵖ` contraction
   (`1 ≤ p < ∞`)**:
   One-sided hinge contraction (`lintegral_ofReal_sub_sub_schwarzRearrangementReal_le`), `L¹`
   contraction (`lintegral_enorm_sub_schwarzRearrangementReal_le`), and `Lᵖ` contraction for
   `1 ≤ p < ∞` (`lintegral_enorm_sub_rpow_schwarzRearrangementReal_le`,
   `eLpNorm_sub_schwarzRearrangementReal_le`, `eLpNorm_sub_schwarzRearrangementReal_le_of_memLp`).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal symmDiff

namespace TauCeti

variable {n : ℕ}

/-! ### Volume of Euclidean balls and set-level Schwarz symmetrization -/

/-- Volume of the unit open ball in `EuclideanSpace ℝ (Fin n)`. -/
def unitBallVolume (n : ℕ) : ℝ≥0∞ :=
  volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The volume of the unit ball in `EuclideanSpace ℝ (Fin n)` is strictly positive. -/
theorem unitBallVolume_pos (n : ℕ) : 0 < unitBallVolume n :=
  Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)

/-- The volume of the unit ball in `EuclideanSpace ℝ (Fin n)` is nonzero. -/
theorem unitBallVolume_ne_zero (n : ℕ) : unitBallVolume n ≠ 0 :=
  (unitBallVolume_pos n).ne'

/-- The volume of the unit ball in `EuclideanSpace ℝ (Fin n)` is finite. -/
theorem unitBallVolume_lt_top (n : ℕ) : unitBallVolume n < ⊤ :=
  measure_ball_lt_top

/-- The volume of the unit ball in `EuclideanSpace ℝ (Fin n)` is not `⊤`. -/
theorem unitBallVolume_ne_top (n : ℕ) : unitBallVolume n ≠ ⊤ :=
  measure_ball_lt_top.ne

/-- Volume of an open ball of radius `r ≥ 0` in `EuclideanSpace ℝ (Fin n)` (`[NeZero n]`). -/
theorem volume_ball_euclideanSpace [NeZero n] (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = unitBallVolume n * ENNReal.ofReal r ^ n := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  rw [Measure.addHaar_ball volume x hr, finrank_euclideanSpace_fin,
    ENNReal.ofReal_pow hr, mul_comm, unitBallVolume]

/-- **Schwarz symmetrization of a set** in `EuclideanSpace ℝ (Fin n)`: the centered open ball
`{x | unitBallVolume n * ‖x‖ₑ ^ n < volume E}` whose volume matches `volume E`. -/
def schwarzSymmetrization (E : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | unitBallVolume n * ‖x‖ₑ ^ n < volume E}

/-- Membership in `schwarzSymmetrization E`. -/
@[simp]
theorem mem_schwarzSymmetrization {E : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ schwarzSymmetrization E ↔ unitBallVolume n * ‖x‖ₑ ^ n < volume E :=
  Iff.rfl

/-- `schwarzSymmetrization E` depends only on `volume E`. -/
theorem schwarzSymmetrization_eq_of_volume_eq {E F : Set (EuclideanSpace ℝ (Fin n))}
    (h : volume E = volume F) :
    schwarzSymmetrization E = schwarzSymmetrization F := by
  simp only [schwarzSymmetrization, h]

/-- Almost everywhere equal sets have identical Schwarz symmetrizations. -/
theorem schwarzSymmetrization_congr_ae {E F : Set (EuclideanSpace ℝ (Fin n))}
    (h : E =ᵐ[volume] F) :
    schwarzSymmetrization E = schwarzSymmetrization F :=
  schwarzSymmetrization_eq_of_volume_eq (measure_congr h)

/-- Schwarz symmetrization is monotone with respect to set volume. -/
theorem schwarzSymmetrization_mono_volume {E F : Set (EuclideanSpace ℝ (Fin n))}
    (h : volume E ≤ volume F) :
    schwarzSymmetrization E ⊆ schwarzSymmetrization F :=
  fun _ hx ↦ hx.trans_le h

/-- Schwarz symmetrization is monotone with respect to set inclusion. -/
theorem schwarzSymmetrization_mono {E F : Set (EuclideanSpace ℝ (Fin n))} (h : E ⊆ F) :
    schwarzSymmetrization E ⊆ schwarzSymmetrization F :=
  schwarzSymmetrization_mono_volume (measure_mono h)

/-- The Schwarz symmetrization of a null set is empty. -/
@[simp]
theorem schwarzSymmetrization_of_volume_eq_zero {E : Set (EuclideanSpace ℝ (Fin n))}
    (h : volume E = 0) :
    schwarzSymmetrization E = ∅ := by
  ext x
  simp [h]

/-- The Schwarz symmetrization of the empty set is empty. -/
@[simp]
theorem schwarzSymmetrization_empty :
    schwarzSymmetrization (∅ : Set (EuclideanSpace ℝ (Fin n))) = ∅ :=
  schwarzSymmetrization_of_volume_eq_zero measure_empty

/-- The Schwarz symmetrization of a set of infinite volume is `Set.univ`. -/
@[simp]
theorem schwarzSymmetrization_of_volume_eq_top {E : Set (EuclideanSpace ℝ (Fin n))}
    (h : volume E = ⊤) :
    schwarzSymmetrization E = Set.univ := by
  ext x
  simp only [mem_schwarzSymmetrization, h, mem_univ, iff_true]
  exact ENNReal.mul_lt_top measure_ball_lt_top (ENNReal.pow_lt_top enorm_lt_top)

/-- The radius of the Schwarz symmetrization of a finite-volume set `E ⊆ EuclideanSpace ℝ (Fin n)`:
`((volume E / unitBallVolume n).toReal) ^ (1 / (n : ℝ))`. -/
def schwarzRadius (E : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (volume E / unitBallVolume n).toReal ^ (1 / (n : ℝ))

/-- `schwarzRadius E` is nonnegative. -/
theorem schwarzRadius_nonneg (E : Set (EuclideanSpace ℝ (Fin n))) : 0 ≤ schwarzRadius E :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- Volume formula in terms of `schwarzRadius E` for a set of finite volume. -/
theorem ofReal_schwarzRadius_pow [NeZero n] {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : volume E ≠ ⊤) :
    unitBallVolume n * ENNReal.ofReal (schwarzRadius E) ^ n = volume E := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hdiv_ne_top : volume E / unitBallVolume n ≠ ⊤ :=
    ENNReal.div_ne_top hE (unitBallVolume_ne_zero n)
  rw [← ENNReal.ofReal_pow (schwarzRadius_nonneg E), schwarzRadius,
    ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg,
    one_div_mul_cancel hn, Real.rpow_one, ENNReal.ofReal_toReal hdiv_ne_top,
    mul_comm, ENNReal.div_mul_cancel (unitBallVolume_ne_zero n) (unitBallVolume_ne_top n)]

/-- For any finite-volume set `E`, `schwarzSymmetrization E` is the open ball of radius
`schwarzRadius E` centered at the origin. -/
theorem schwarzSymmetrization_eq_ball [NeZero n] {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : volume E ≠ ⊤) :
    schwarzSymmetrization E = Metric.ball 0 (schwarzRadius E) := by
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  ext x
  rw [mem_schwarzSymmetrization, Metric.mem_ball, dist_zero_right, ← ofReal_schwarzRadius_pow hE]
  have hmul : unitBallVolume n * ‖x‖ₑ ^ n <
      unitBallVolume n * ENNReal.ofReal (schwarzRadius E) ^ n ↔
      ‖x‖ₑ ^ n < ENNReal.ofReal (schwarzRadius E) ^ n := by
    rw [← not_le, ← not_le,
      ENNReal.mul_le_mul_iff_right (unitBallVolume_ne_zero n) (unitBallVolume_ne_top n)]
  have hpow : ‖x‖ₑ ^ n < ENNReal.ofReal (schwarzRadius E) ^ n ↔
      ‖x‖ₑ < ENNReal.ofReal (schwarzRadius E) := by
    simp only [← ENNReal.rpow_natCast]
    exact ENNReal.rpow_lt_rpow_iff hn_real
  rw [hmul, hpow, ← ofReal_norm,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)]

/-- The Schwarz symmetrization of any set is open. -/
theorem isOpen_schwarzSymmetrization (E : Set (EuclideanSpace ℝ (Fin n))) :
    IsOpen (schwarzSymmetrization E) := by
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin n) ↦ unitBallVolume n * ‖x‖ₑ ^ n := by
    rw [show (fun x : EuclideanSpace ℝ (Fin n) ↦ unitBallVolume n * ‖x‖ₑ ^ n) =
      (fun y : ℝ≥0∞ ↦ unitBallVolume n * y) ∘ ENNReal.ofReal ∘ fun x ↦ ‖x‖ ^ n by
        ext x
        dsimp
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg x)]]
    exact (ENNReal.continuous_const_mul (unitBallVolume_ne_top n)).comp
      (ENNReal.continuous_ofReal.comp (continuous_norm.pow n))
  exact isOpen_lt hcont continuous_const

/-- The Schwarz symmetrization of any set is measurable. -/
theorem measurableSet_schwarzSymmetrization (E : Set (EuclideanSpace ℝ (Fin n))) :
    MeasurableSet (schwarzSymmetrization E) :=
  (isOpen_schwarzSymmetrization E).measurableSet

/-- **Volume preservation of Schwarz symmetrization**:
`volume (schwarzSymmetrization E) = volume E`. -/
@[simp]
theorem volume_schwarzSymmetrization [NeZero n] (E : Set (EuclideanSpace ℝ (Fin n))) :
    volume (schwarzSymmetrization E) = volume E := by
  rcases eq_or_ne (volume E) ⊤ with htop | hE
  · rw [schwarzSymmetrization_of_volume_eq_top htop, htop]
    exact measure_univ_of_isAddLeftInvariant volume
  · rw [schwarzSymmetrization_eq_ball hE, volume_ball_euclideanSpace 0 (schwarzRadius_nonneg E),
      ofReal_schwarzRadius_pow hE]

/-- Schwarz symmetrization is idempotent. -/
@[simp]
theorem schwarzSymmetrization_schwarzSymmetrization [NeZero n]
    (E : Set (EuclideanSpace ℝ (Fin n))) :
    schwarzSymmetrization (schwarzSymmetrization E) = schwarzSymmetrization E :=
  schwarzSymmetrization_eq_of_volume_eq (volume_schwarzSymmetrization E)

/-- The intersection of two Schwarz symmetrizations has volume `min (volume E) (volume F)`. -/
theorem volume_schwarzSymmetrization_inter [NeZero n]
    (E F : Set (EuclideanSpace ℝ (Fin n))) :
    volume (schwarzSymmetrization E ∩ schwarzSymmetrization F) = min (volume E) (volume F) := by
  rcases le_total (volume E) (volume F) with h | h
  · rw [inter_eq_self_of_subset_left (schwarzSymmetrization_mono_volume h),
      volume_schwarzSymmetrization, min_eq_left h]
  · rw [inter_eq_self_of_subset_right (schwarzSymmetrization_mono_volume h),
      volume_schwarzSymmetrization, min_eq_right h]

/-- **Two-set Riesz / Fréchet rearrangement inequality**: Schwarz symmetrization does not decrease
the volume of the intersection of two sets. -/
theorem volume_inter_le_volume_schwarzSymmetrization_inter [NeZero n]
    (E F : Set (EuclideanSpace ℝ (Fin n))) :
    volume (E ∩ F) ≤ volume (schwarzSymmetrization E ∩ schwarzSymmetrization F) := by
  rw [volume_schwarzSymmetrization_inter]
  exact le_min (measure_mono inter_subset_left) (measure_mono inter_subset_right)

/-- **One-sided set-difference contraction**: Schwarz symmetrization does not increase the volume of
a set difference `F \ E`. -/
theorem volume_diff_schwarzSymmetrization_le [NeZero n]
    (E F : Set (EuclideanSpace ℝ (Fin n))) :
    volume (schwarzSymmetrization F \ schwarzSymmetrization E) ≤ volume (F \ E) := by
  rcases le_or_gt (volume F) (volume E) with h | h
  · rw [sdiff_eq_empty.mpr (schwarzSymmetrization_mono_volume h), measure_empty]
    exact bot_le
  · have hE_ne_top : volume (schwarzSymmetrization E) ≠ ⊤ := by
      rw [volume_schwarzSymmetrization]
      exact (lt_of_lt_of_le h le_top).ne
    rw [measure_sdiff (schwarzSymmetrization_mono_volume h.le)
        (measurableSet_schwarzSymmetrization E).nullMeasurableSet hE_ne_top,
      volume_schwarzSymmetrization, volume_schwarzSymmetrization]
    refine tsub_le_iff_right.mpr ?_
    calc volume F ≤ volume (F \ E ∪ E) := measure_mono (by simp)
      _ ≤ volume (F \ E) + volume E := measure_union_le _ _

/-- **Symmetric-difference contraction**: Schwarz symmetrization does not increase the volume of the
symmetric difference of two sets. -/
theorem volume_symmDiff_schwarzSymmetrization_le [NeZero n]
    (E F : Set (EuclideanSpace ℝ (Fin n))) :
    volume (schwarzSymmetrization E ∆ schwarzSymmetrization F) ≤ volume (E ∆ F) := by
  rcases le_total (volume E) (volume F) with h | h
  · have hsub : schwarzSymmetrization E ∆ schwarzSymmetrization F =
        schwarzSymmetrization F \ schwarzSymmetrization E := by
      rw [Set.symmDiff_def, sdiff_eq_empty.mpr (schwarzSymmetrization_mono_volume h), empty_union]
    rw [hsub]
    exact (volume_diff_schwarzSymmetrization_le E F).trans (measure_mono subset_union_right)
  · have hsub : schwarzSymmetrization E ∆ schwarzSymmetrization F =
        schwarzSymmetrization E \ schwarzSymmetrization F := by
      rw [Set.symmDiff_def, sdiff_eq_empty.mpr (schwarzSymmetrization_mono_volume h), union_empty]
    rw [hsub]
    exact (volume_diff_schwarzSymmetrization_le F E).trans (measure_mono subset_union_left)

/-! ### Distribution function, radial profile, and Schwarz rearrangement of functions -/

/-- **Distribution function** of an `ℝ≥0∞`-valued function on `EuclideanSpace ℝ (Fin n)`:
`distributionFunction f t = volume {y | t < f y}`. -/
def distributionFunction (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (t : ℝ≥0∞) : ℝ≥0∞ :=
  volume {y | t < f y}

/-- The distribution function is antitone in the threshold `t`. -/
theorem antitone_distributionFunction (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    Antitone (distributionFunction f) :=
  fun _ _ h ↦ measure_mono fun _ hy ↦ h.trans_lt hy

/-- The distribution function at `⊤` is `0`. -/
@[simp]
theorem distributionFunction_top (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    distributionFunction f ⊤ = 0 := by
  simp [distributionFunction]

/-- Almost everywhere equal functions have identical distribution functions. -/
theorem distributionFunction_congr_ae {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : f =ᵐ[volume] g) (t : ℝ≥0∞) :
    distributionFunction f t = distributionFunction g t := by
  refine measure_congr ?_
  filter_upwards [h] with y hy
  simp [hy]

/-- Pointwise a.e. inequality implies pointwise inequality of distribution functions. -/
theorem distributionFunction_mono_ae {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : f ≤ᵐ[volume] g) (t : ℝ≥0∞) :
    distributionFunction f t ≤ distributionFunction g t := by
  have hsub : ({y | t < f y} : Set (EuclideanSpace ℝ (Fin n))) ≤ᵐ[volume] {y | t < g y} := by
    filter_upwards [h] with y hy hyf
    exact hyf.trans_le hy
  exact measure_mono_ae hsub

/-- **Radial profile of the Schwarz rearrangement** of `f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞`:
for `r : ℝ`, `schwarzRadialProfile f r` is the supremum in `ℝ≥0∞` of all levels `t > 0` whose
superlevel set `{y | t < f y}` has volume strictly greater than `unitBallVolume n * r ^ n`. -/
def schwarzRadialProfile (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  sSup {t : ℝ≥0∞ | 0 < t ∧ unitBallVolume n * ENNReal.ofReal r ^ n < distributionFunction f t}

/-- Unrestricted `sSup` characterization of `schwarzRadialProfile`. -/
theorem schwarzRadialProfile_eq_sSup (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (r : ℝ) :
    schwarzRadialProfile f r =
      sSup {t : ℝ≥0∞ | unitBallVolume n * ENNReal.ofReal r ^ n < distributionFunction f t} := by
  apply le_antisymm
  · exact sSup_le_sSup fun t ht ↦ ht.2
  · refine sSup_le fun t ht ↦ ?_
    rcases eq_or_ne t 0 with rfl | ht0
    · exact bot_le
    · exact le_sSup ⟨pos_iff_ne_zero.mpr ht0, ht⟩

/-- The radial profile `schwarzRadialProfile f` is antitone on `ℝ`. -/
theorem antitone_schwarzRadialProfile (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    Antitone (schwarzRadialProfile f) := by
  intro r₁ r₂ hr
  refine sSup_le_sSup fun t ht ↦ ⟨ht.1, ?_⟩
  have hle : unitBallVolume n * ENNReal.ofReal r₁ ^ n ≤
      unitBallVolume n * ENNReal.ofReal r₂ ^ n := by
    gcongr
  exact hle.trans_lt ht.2

/-- The radial profile `schwarzRadialProfile f` is Borel measurable. -/
@[fun_prop]
theorem measurable_schwarzRadialProfile (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    Measurable (schwarzRadialProfile f) :=
  (antitone_schwarzRadialProfile f).measurable

/-- **Schwarz rearrangement** of `f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞`: the radially symmetric
nonincreasing function `x ↦ schwarzRadialProfile f ‖x‖`. -/
def schwarzRearrangement (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  schwarzRadialProfile f ‖x‖

/-- Evaluation of `schwarzRearrangement f` at `x` in terms of `schwarzRadialProfile f ‖x‖`. -/
theorem schwarzRearrangement_apply (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin n)) :
    schwarzRearrangement f x = schwarzRadialProfile f ‖x‖ := by
  rfl

/-- Right-continuity of the distribution function along `t + (k + 1)⁻¹`. -/
theorem distributionFunction_eq_iSup_add_inv (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (t : ℝ≥0∞) :
    distributionFunction f t = ⨆ k : ℕ, distributionFunction f (t + ((k : ℝ≥0∞) + 1)⁻¹) := by
  have hunion : {y | t < f y} = ⋃ k : ℕ, {y | t + ((k : ℝ≥0∞) + 1)⁻¹ < f y} := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      have ht : t ≠ ⊤ := ne_top_of_lt h
      have hsub : 0 < f y - t := tsub_pos_iff_lt.mpr h
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hsub.ne'
      refine ⟨k, ?_⟩
      have hle : ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ :=
        ENNReal.inv_le_inv.mpr le_self_add
      have hlt : ((k : ℝ≥0∞) + 1)⁻¹ < f y - t := hle.trans_lt hk
      rw [← add_tsub_cancel_of_le h.le]
      exact ENNReal.add_lt_add_left ht hlt
    · rintro ⟨k, hk⟩
      exact le_self_add.trans_lt hk
  have hmono : Monotone fun k : ℕ ↦ {y | t + ((k : ℝ≥0∞) + 1)⁻¹ < f y} := by
    intro i j hij y (hy : t + ((i : ℝ≥0∞) + 1)⁻¹ < f y)
    have hinv : ((j : ℝ≥0∞) + 1)⁻¹ ≤ ((i : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_le_inv.mpr (add_le_add_left (Nat.cast_le.mpr hij) 1)
    exact (add_le_add_right hinv t).trans_lt hy
  rw [distributionFunction, hunion, hmono.measure_iUnion]
  rfl

/-- **Galois connection for `schwarzRadialProfile`**: `t < schwarzRadialProfile f r` if and only if
`unitBallVolume n * ENNReal.ofReal r ^ n < distributionFunction f t`. -/
theorem lt_schwarzRadialProfile_iff {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {r : ℝ} {t : ℝ≥0∞} :
    t < schwarzRadialProfile f r ↔
      unitBallVolume n * ENNReal.ofReal r ^ n < distributionFunction f t := by
  rw [schwarzRadialProfile_eq_sSup, lt_sSup_iff]
  constructor
  · rintro ⟨s, hs, hts⟩
    exact hs.trans_le (antitone_distributionFunction f hts.le)
  · intro h
    rw [distributionFunction_eq_iSup_add_inv, lt_iSup_iff] at h
    obtain ⟨k, hk⟩ := h
    have ht_ne_top : t ≠ ⊤ := by
      rintro rfl
      simp at hk
    have hinv_pos : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_pos.mpr (by simp [ENNReal.natCast_ne_top])
    exact ⟨t + ((k : ℝ≥0∞) + 1)⁻¹, hk, ENNReal.lt_add_right ht_ne_top hinv_pos.ne'⟩

/-- **Galois connection for `schwarzRearrangement`**: `t < schwarzRearrangement f x` if and only if
`x ∈ schwarzSymmetrization {y | t < f y}`. -/
theorem lt_schwarzRearrangement_iff {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    {x : EuclideanSpace ℝ (Fin n)} {t : ℝ≥0∞} :
    t < schwarzRearrangement f x ↔ x ∈ schwarzSymmetrization {y | t < f y} := by
  rw [schwarzRearrangement_apply, lt_schwarzRadialProfile_iff, mem_schwarzSymmetrization,
    distributionFunction, ofReal_norm]

/-- **Superlevel set of the Schwarz rearrangement**: for every `t : ℝ≥0∞`, the superlevel set
`{x | t < schwarzRearrangement f x}` is the Schwarz symmetrization of `{y | t < f y}`. -/
@[simp]
theorem superlevel_schwarzRearrangement (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (t : ℝ≥0∞) :
    {x | t < schwarzRearrangement f x} = schwarzSymmetrization {y | t < f y} := by
  ext x
  exact lt_schwarzRearrangement_iff

/-- **Sublevel set of the Schwarz rearrangement**: for every `t : ℝ≥0∞`, the sublevel set
`{x | schwarzRearrangement f x ≤ t}` is the complement of `schwarzSymmetrization {y | t < f y}`. -/
@[simp]
theorem sublevel_schwarzRearrangement (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (t : ℝ≥0∞) :
    {x | schwarzRearrangement f x ≤ t} = (schwarzSymmetrization {y | t < f y})ᶜ := by
  ext x
  simp [← not_lt, lt_schwarzRearrangement_iff]

/-- The Schwarz rearrangement of any function is Borel measurable. -/
@[fun_prop]
theorem measurable_schwarzRearrangement (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    Measurable (schwarzRearrangement f) :=
  (measurable_schwarzRadialProfile f).comp continuous_norm.measurable

/-- Almost everywhere equal functions have identical radial profiles. -/
theorem schwarzRadialProfile_congr_ae {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : f =ᵐ[volume] g) :
    schwarzRadialProfile f = schwarzRadialProfile g := by
  ext r
  simp only [schwarzRadialProfile, distributionFunction_congr_ae h]

/-- **A.e. representative invariance**: almost everywhere equal functions have identical Schwarz
rearrangements everywhere. -/
theorem schwarzRearrangement_congr_ae {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : f =ᵐ[volume] g) :
    schwarzRearrangement f = schwarzRearrangement g := by
  ext x
  rw [schwarzRearrangement_apply, schwarzRearrangement_apply, schwarzRadialProfile_congr_ae h]

/-- **Order preservation of the radial profile**: if `f ≤ᵐ[volume] g`, then
`schwarzRadialProfile f ≤ schwarzRadialProfile g`. -/
theorem schwarzRadialProfile_mono_ae {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : f ≤ᵐ[volume] g) :
    schwarzRadialProfile f ≤ schwarzRadialProfile g :=
  fun _ ↦ sSup_le_sSup fun t ht ↦ ⟨ht.1, ht.2.trans_le (distributionFunction_mono_ae h t)⟩

/-- **Order preservation of Schwarz rearrangement**: if `f ≤ᵐ[volume] g`, then
`schwarzRearrangement f ≤ schwarzRearrangement g` everywhere. -/
theorem schwarzRearrangement_mono_ae {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : f ≤ᵐ[volume] g) :
    schwarzRearrangement f ≤ schwarzRearrangement g :=
  fun x ↦ schwarzRadialProfile_mono_ae h ‖x‖

/-- **Equimeasurability of Schwarz rearrangement**: for every threshold `t : ℝ≥0∞`,
`volume {x | t < schwarzRearrangement f x} = volume {y | t < f y}`. -/
@[simp]
theorem volume_lt_schwarzRearrangement [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (t : ℝ≥0∞) :
    volume {x | t < schwarzRearrangement f x} = volume {y | t < f y} := by
  rw [superlevel_schwarzRearrangement, volume_schwarzSymmetrization]

/-- `schwarzRearrangement f` has the same distribution function as `f`. -/
@[simp]
theorem distributionFunction_schwarzRearrangement [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (t : ℝ≥0∞) :
    distributionFunction (schwarzRearrangement f) t = distributionFunction f t :=
  volume_lt_schwarzRearrangement f t

/-- Schwarz rearrangement is idempotent. -/
@[simp]
theorem schwarzRearrangement_schwarzRearrangement [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    schwarzRearrangement (schwarzRearrangement f) = schwarzRearrangement f := by
  ext x
  simp only [schwarzRearrangement, schwarzRadialProfile,
    distributionFunction_schwarzRearrangement]

/-! ### Layer-cake formulas and `Lᵖ` norm preservation -/

/-- **Preservation of `Lᵖ` integrals (`0 < p < ∞`)**: for any almost everywhere measurable
`f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞` and `0 < p`,
`∫⁻ x, schwarzRearrangement f x ^ p = ∫⁻ x, f x ^ p`. -/
theorem lintegral_rpow_schwarzRearrangement [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, schwarzRearrangement f x ^ p = ∫⁻ x, f x ^ p := by
  rw [lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul volume
      (measurable_schwarzRearrangement f).aemeasurable hp,
    lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul volume hf hp]
  simp only [volume_lt_schwarzRearrangement]

/-- **Layer-cake / `L¹` integral preservation**: for any almost everywhere measurable
`f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞`, `∫⁻ x, schwarzRearrangement f x = ∫⁻ x, f x`. -/
theorem lintegral_schwarzRearrangement [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume) :
    ∫⁻ x, schwarzRearrangement f x = ∫⁻ x, f x := by
  simpa using lintegral_rpow_schwarzRearrangement hf one_pos

/-- Preservation of `eLpNorm'` for `0 < q`. -/
theorem eLpNorm'_schwarzRearrangement [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume) {q : ℝ} (hq : 0 < q) :
    eLpNorm' (schwarzRearrangement f) q volume = eLpNorm' f q volume := by
  simp only [eLpNorm'_eq_lintegral_enorm, enorm_eq_self,
    lintegral_rpow_schwarzRearrangement hf hq]

/-- Preservation of `eLpNormEssSup` (`L^∞` seminorm). -/
@[simp]
theorem eLpNormEssSup_schwarzRearrangement [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    eLpNormEssSup (schwarzRearrangement f) volume = eLpNormEssSup f volume := by
  simp only [eLpNormEssSup_eq_essSup_enorm, essSup_eq_sInf, enorm_eq_self,
    volume_lt_schwarzRearrangement]

/-- **`Lᵖ` norm preservation (`0 ≤ p ≤ ∞`)**: for any almost everywhere measurable
`f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞` and any `p : ℝ≥0∞`,
`eLpNorm (schwarzRearrangement f) p volume = eLpNorm f p volume`. -/
theorem eLpNorm_schwarzRearrangement [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume) (p : ℝ≥0∞) :
    eLpNorm (schwarzRearrangement f) p volume = eLpNorm f p volume := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [eLpNorm, (measurable_schwarzRearrangement f).aestronglyMeasurable,
      hf.aestronglyMeasurable]
  rcases eq_or_ne p ⊤ with rfl | hptop
  · rw [eLpNorm_exponent_top (measurable_schwarzRearrangement f).aestronglyMeasurable,
      eLpNorm_exponent_top hf.aestronglyMeasurable, eLpNormEssSup_schwarzRearrangement]
  · rw [eLpNorm_eq_eLpNorm' hp0 hptop (measurable_schwarzRearrangement f).aestronglyMeasurable,
      eLpNorm_eq_eLpNorm' hp0 hptop hf.aestronglyMeasurable,
      eLpNorm'_schwarzRearrangement hf (ENNReal.toReal_pos hp0 hptop)]

/-- **`MemLp` equivalence**: `schwarzRearrangement f` lies in `Lᵖ` if and only if `f` lies in
`Lᵖ`. -/
theorem memLp_schwarzRearrangement_iff [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume) {p : ℝ≥0∞} :
    MemLp (schwarzRearrangement f) p volume ↔ MemLp f p volume := by
  simp only [MemLp, eLpNorm_schwarzRearrangement hf]

/-! ### Superlevel finiteness and finiteness of the radial profile for `r > 0` -/

/-- Markov / Chebyshev inequality for the distribution function of `f ^ p`. -/
theorem distributionFunction_le_lintegral_rpow_div
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    {p : ℝ} (hp : 0 < p) {t : ℝ≥0∞} (ht0 : t ≠ 0) (httop : t ≠ ⊤) :
    distributionFunction f t ≤ (∫⁻ y, f y ^ p) / t ^ p := by
  have hsub : {y | t < f y} ⊆ {y | t ^ p ≤ f y ^ p} :=
    fun y hy ↦ ENNReal.rpow_le_rpow hy.le hp.le
  exact (measure_mono hsub).trans
    (meas_ge_le_lintegral_div (hf.pow_const p)
      (ENNReal.rpow_pos (pos_iff_ne_zero.mpr ht0) httop).ne'
      (ENNReal.rpow_ne_top_of_nonneg hp.le httop))

/-- Markov inequality for the distribution function of an integrable function:
`distributionFunction f t ≤ (∫⁻ y, f y) / t`. -/
theorem distributionFunction_le_lintegral_div
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    {t : ℝ≥0∞} (ht0 : t ≠ 0) (httop : t ≠ ⊤) :
    distributionFunction f t ≤ (∫⁻ y, f y) / t := by
  simpa using distributionFunction_le_lintegral_rpow_div hf one_pos ht0 httop

/-- Every function with `∫⁻ y, f y ^ p ≠ ⊤` (`0 < p`) has finite superlevel volumes for all
`t > 0`. -/
theorem distributionFunction_lt_top_of_lintegral_rpow_ne_top
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    {p : ℝ} (hp : 0 < p) (hfin : ∫⁻ y, f y ^ p ≠ ⊤) {t : ℝ≥0∞} (ht : 0 < t) :
    distributionFunction f t < ⊤ := by
  rcases eq_or_ne t ⊤ with rfl | httop
  · simp
  · refine lt_of_le_of_lt (distributionFunction_le_lintegral_rpow_div hf hp ht.ne' httop) ?_
    exact ENNReal.div_lt_top hfin (ENNReal.rpow_pos ht httop).ne'

/-- Every `L¹` function (`∫⁻ y, f y ≠ ⊤`) has finite superlevel volumes for all `t > 0`. -/
theorem distributionFunction_lt_top_of_lintegral_ne_top
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hfin : ∫⁻ y, f y ≠ ⊤) {t : ℝ≥0∞} (ht : 0 < t) :
    distributionFunction f t < ⊤ := by
  simpa using
    distributionFunction_lt_top_of_lintegral_rpow_ne_top hf one_pos (by simpa using hfin) ht

/-- Every `MemLp f p` function with `0 < p < ∞` has finite superlevel volumes for all `t > 0`. -/
theorem distributionFunction_lt_top_of_memLp
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) {t : ℝ≥0∞} (ht : 0 < t) :
    distributionFunction f t < ⊤ := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hfin : ∫⁻ y, f y ^ p.toReal ≠ ⊤ := by
    have hlt := hf.eLpNorm_lt_top
    rw [eLpNorm_eq_eLpNorm' hp0 hptop hf.aestronglyMeasurable, eLpNorm'_eq_lintegral_enorm] at hlt
    simp only [enorm_eq_self] at hlt
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (one_div_pos.mpr hp_pos)] at hlt
    exact lt_irrefl ⊤ hlt
  exact distributionFunction_lt_top_of_lintegral_rpow_ne_top
    hf.aestronglyMeasurable.aemeasurable hp_pos hfin ht

/-- Quantitative radial bound for `schwarzRadialProfile`: for `0 < p` and `r : ℝ`,
`schwarzRadialProfile f r ^ p ≤ (∫⁻ y, f y ^ p) / (unitBallVolume n * ENNReal.ofReal r ^ n)`. -/
theorem schwarzRadialProfile_rpow_le_lintegral_rpow_div
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    {p : ℝ} (hp : 0 < p) (r : ℝ) :
    schwarzRadialProfile f r ^ p ≤
      (∫⁻ y, f y ^ p) / (unitBallVolume n * ENNReal.ofReal r ^ n) := by
  have hr_ne_top : unitBallVolume n * ENNReal.ofReal r ^ n ≠ ⊤ :=
    ENNReal.mul_ne_top (unitBallVolume_ne_top n) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  rw [← ENNReal.le_rpow_inv_iff hp]
  refine sSup_le fun t ht ↦ ?_
  rw [ENNReal.le_rpow_inv_iff hp]
  rcases eq_or_ne t ⊤ with rfl | httop
  · simp at ht
  have hmarkov := distributionFunction_le_lintegral_rpow_div hf hp ht.1.ne' httop
  have hlt := ht.2.trans_le hmarkov
  have htp0 : t ^ p ≠ 0 := (ENNReal.rpow_pos ht.1 httop).ne'
  have htp_ne_top : t ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le httop
  rcases eq_or_ne (unitBallVolume n * ENNReal.ofReal r ^ n) 0 with hr0 | hr0
  · have hint0 : ∫⁻ y, f y ^ p ≠ 0 := by
      intro h0
      rw [h0, ENNReal.zero_div] at hlt
      exact not_lt_zero hlt
    rw [hr0, ENNReal.div_zero hint0]
    exact le_top
  · have hmul : (unitBallVolume n * ENNReal.ofReal r ^ n) * t ^ p ≤ ∫⁻ y, f y ^ p :=
      (ENNReal.le_div_iff_mul_le (Or.inl htp0) (Or.inl htp_ne_top)).mp hlt.le
    rw [mul_comm] at hmul
    exact (ENNReal.le_div_iff_mul_le (Or.inl hr0) (Or.inl hr_ne_top)).mpr hmul

/-- Quantitative `L¹` radial bound:
`schwarzRadialProfile f r ≤ (∫⁻ y, f y) / (unitBallVolume n * ENNReal.ofReal r ^ n)`. -/
theorem schwarzRadialProfile_le_lintegral_div
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume) (r : ℝ) :
    schwarzRadialProfile f r ≤
      (∫⁻ y, f y) / (unitBallVolume n * ENNReal.ofReal r ^ n) := by
  simpa using schwarzRadialProfile_rpow_le_lintegral_rpow_div hf one_pos r

/-- **Finiteness of the radial profile `schwarzRadialProfile f r` for `r > 0`** when
`∫⁻ y, f y ^ p ≠ ⊤` (`0 < p`). -/
theorem schwarzRadialProfile_lt_top_of_lintegral_rpow_ne_top
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    {p : ℝ} (hp : 0 < p) (hfin : ∫⁻ y, f y ^ p ≠ ⊤) {r : ℝ} (hr : 0 < r) :
    schwarzRadialProfile f r < ⊤ := by
  rw [← ENNReal.rpow_lt_top_iff_of_pos hp]
  refine lt_of_le_of_lt (schwarzRadialProfile_rpow_le_lintegral_rpow_div hf hp r) ?_
  refine ENNReal.div_lt_top hfin ?_
  exact (ENNReal.mul_pos (unitBallVolume_ne_zero n)
    (pow_ne_zero n (ENNReal.ofReal_pos.mpr hr).ne')).ne'

/-- **Finiteness of `schwarzRadialProfile f r` for `r > 0`** under an `L¹` bound. -/
theorem schwarzRadialProfile_lt_top_of_lintegral_ne_top
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hfin : ∫⁻ y, f y ≠ ⊤) {r : ℝ} (hr : 0 < r) :
    schwarzRadialProfile f r < ⊤ := by
  simpa using
    schwarzRadialProfile_lt_top_of_lintegral_rpow_ne_top hf one_pos (by simpa using hfin) hr

/-- **Finiteness of `schwarzRadialProfile f r` for `r > 0`** for `MemLp f p` (`0 < p < ∞`). -/
theorem schwarzRadialProfile_lt_top_of_memLp
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) {r : ℝ} (hr : 0 < r) :
    schwarzRadialProfile f r < ⊤ := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hfin : ∫⁻ y, f y ^ p.toReal ≠ ⊤ := by
    have hlt := hf.eLpNorm_lt_top
    rw [eLpNorm_eq_eLpNorm' hp0 hptop hf.aestronglyMeasurable, eLpNorm'_eq_lintegral_enorm] at hlt
    simp only [enorm_eq_self] at hlt
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (one_div_pos.mpr hp_pos)] at hlt
    exact lt_irrefl ⊤ hlt
  exact schwarzRadialProfile_lt_top_of_lintegral_rpow_ne_top
    hf.aestronglyMeasurable.aemeasurable hp_pos hfin hr

/-- **General finiteness of `schwarzRadialProfile f r` for `r > 0`** for any measurable function
with finite superlevel volumes for `t > 0` and `volume {y | f y = ⊤} = 0`. -/
theorem schwarzRadialProfile_lt_top_of_distributionFunction_lt_top
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ≥0∞, 0 < t → distributionFunction f t < ⊤)
    (htop : volume {y | f y = ⊤} = 0) {r : ℝ} (hr : 0 < r) :
    schwarzRadialProfile f r < ⊤ := by
  let g := hf.mk f
  have hfg : f =ᵐ[volume] g := hf.ae_eq_mk
  rw [schwarzRadialProfile_congr_ae hfg]
  have hdistg : distributionFunction g 1 ≠ ⊤ := by
    rw [← distributionFunction_congr_ae hfg]
    exact (hdist 1 zero_lt_one).ne
  have htopg : volume {y | g y = ⊤} = 0 := by
    rw [← htop]
    refine measure_congr ?_
    filter_upwards [hfg] with y hy
    simp [hy]
  have hinter : (⋂ k : ℕ, {y | (k : ℝ≥0∞) + 1 < g y}) = {y | g y = ⊤} := by
    ext y
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h
      by_contra hne
      obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hne
      exact not_lt_of_ge (hk.le.trans le_self_add) (h k)
    · intro hy k
      rw [hy]
      exact ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top k, ENNReal.one_lt_top⟩
  have hant : Antitone fun k : ℕ ↦ {y | (k : ℝ≥0∞) + 1 < g y} := by
    intro i j hij y (hy : (j : ℝ≥0∞) + 1 < g y)
    exact (add_le_add_left (Nat.cast_le.mpr hij) 1).trans_lt hy
  have hmeas (k : ℕ) : NullMeasurableSet {y | (k : ℝ≥0∞) + 1 < g y} volume :=
    (measurableSet_lt measurable_const hf.measurable_mk).nullMeasurableSet
  have hfin0 : volume {y | ((0 : ℕ) : ℝ≥0∞) + 1 < g y} ≠ ⊤ := by
    simpa [distributionFunction] using hdistg
  have htend := tendsto_measure_iInter_atTop hmeas hant ⟨0, hfin0⟩
  rw [hinter, htopg] at htend
  have hpos : 0 < unitBallVolume n * ENNReal.ofReal r ^ n :=
    ENNReal.mul_pos (unitBallVolume_ne_zero n) (pow_ne_zero n (ENNReal.ofReal_pos.mpr hr).ne')
  obtain ⟨k, hk⟩ := (Tendsto.eventually_lt_const hpos htend).exists
  refine lt_of_le_of_lt ?_ (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top k, ENNReal.one_lt_top⟩)
  refine sSup_le fun t ht ↦ ?_
  by_contra! hlt
  exact not_lt_of_ge (antitone_distributionFunction g hlt.le) (hk.trans ht.2)

/-- Under the finiteness hypotheses of `schwarzRadialProfile_lt_top_of_distributionFunction_lt_top`,
`schwarzRearrangement f x < ⊤` for every `x ≠ 0`. -/
theorem schwarzRearrangement_lt_top_of_ne_zero
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ≥0∞, 0 < t → distributionFunction f t < ⊤)
    (htop : volume {y | f y = ⊤} = 0) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    schwarzRearrangement f x < ⊤ :=
  schwarzRadialProfile_lt_top_of_distributionFunction_lt_top hf hdist htop (norm_pos_iff.mpr hx)

/-- Under the finiteness hypotheses of `schwarzRadialProfile_lt_top_of_distributionFunction_lt_top`,
`schwarzRearrangement f x < ⊤` for almost every `x` (`[NeZero n]`). -/
theorem schwarzRearrangement_lt_top_ae [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ≥0∞, 0 < t → distributionFunction f t < ⊤)
    (htop : volume {y | f y = ⊤} = 0) :
    ∀ᵐ x ∂volume, schwarzRearrangement f x < ⊤ := by
  have h0 : volume ({0} : Set (EuclideanSpace ℝ (Fin n))) = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr h0] with x hx
  exact schwarzRearrangement_lt_top_of_ne_zero hf hdist htop hx

/-! ### The Hardy–Littlewood rearrangement inequality -/

/-- Layer-cake representation of the integral of a product `f * g` of almost everywhere measurable
`ℝ≥0∞`-valued functions. -/
theorem lintegral_mul_eq_lintegral_lintegral_meas_lt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ x, f x * g x ∂μ =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        μ ({x | ENNReal.ofReal s < f x} ∩ {x | ENNReal.ofReal t < g x}) := by
  let f' := hf.mk f
  let g' := hg.mk g
  have hfg : ∫⁻ x, f x * g x ∂μ = ∫⁻ x, (f' * g') x ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
    simp [f', g', hfx, hgx]
  rw [hfg, ← lintegral_withDensity_eq_lintegral_mul₀ hf.measurable_mk.aemeasurable
      hg.measurable_mk.aemeasurable]
  have h1 := lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul (μ.withDensity f')
    hg.measurable_mk.aemeasurable one_pos
  simp only [ENNReal.rpow_one, ENNReal.ofReal_one, one_mul, sub_self, Real.rpow_zero,
    mul_one] at h1
  rw [h1]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  have hmeas_t : MeasurableSet {x | ENNReal.ofReal t < g' x} :=
    measurableSet_lt measurable_const hg.measurable_mk
  rw [withDensity_apply f' hmeas_t]
  have h2 := lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul
    (μ.restrict {x | ENNReal.ofReal t < g' x}) hf.measurable_mk.aemeasurable one_pos
  simp only [ENNReal.rpow_one, ENNReal.ofReal_one, one_mul, sub_self, Real.rpow_zero,
    mul_one] at h2
  rw [h2]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s _ ↦ ?_
  rw [Measure.restrict_apply (measurableSet_lt measurable_const hf.measurable_mk)]
  refine measure_congr ?_
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  simp [g', hfx, hgx]

/-- **The Hardy–Littlewood rearrangement inequality**: for any two almost everywhere measurable
functions `f, g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞`,
`∫⁻ x, f x * g x ≤ ∫⁻ x, schwarzRearrangement f x * schwarzRearrangement g x`. -/
theorem lintegral_mul_le_lintegral_schwarzRearrangement_mul [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    ∫⁻ x, f x * g x ≤ ∫⁻ x, schwarzRearrangement f x * schwarzRearrangement g x := by
  rw [lintegral_mul_eq_lintegral_lintegral_meas_lt volume hf hg,
    lintegral_mul_eq_lintegral_lintegral_meas_lt volume
      (measurable_schwarzRearrangement f).aemeasurable
      (measurable_schwarzRearrangement g).aemeasurable]
  refine lintegral_mono fun t ↦ lintegral_mono fun s ↦ ?_
  rw [superlevel_schwarzRearrangement, superlevel_schwarzRearrangement]
  exact volume_inter_le_volume_schwarzSymmetrization_inter _ _

/-! ### Real-valued specialization and `Lᵖ` contraction (`1 ≤ p < ∞`) -/

/-- **Schwarz rearrangement of a real-valued function** on `EuclideanSpace ℝ (Fin n)`:
`schwarzRearrangementReal f x = (schwarzRearrangement (fun y ↦ ENNReal.ofReal (f y)) x).toReal`. -/
def schwarzRearrangementReal (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (schwarzRearrangement (fun y ↦ ENNReal.ofReal (f y)) x).toReal

/-- `schwarzRearrangementReal f` is nonnegative everywhere. -/
theorem schwarzRearrangementReal_nonneg (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ schwarzRearrangementReal f x :=
  ENNReal.toReal_nonneg

/-- `schwarzRearrangementReal f` is Borel measurable. -/
@[fun_prop]
theorem measurable_schwarzRearrangementReal (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    Measurable (schwarzRearrangementReal f) :=
  (measurable_schwarzRearrangement _).ennreal_toReal

/-- Almost everywhere equal real-valued functions have identical Schwarz rearrangements. -/
theorem schwarzRearrangementReal_congr_ae {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : f =ᵐ[volume] g) :
    schwarzRearrangementReal f = schwarzRearrangementReal g := by
  have h' : (fun y ↦ ENNReal.ofReal (f y)) =ᵐ[volume] fun y ↦ ENNReal.ofReal (g y) :=
    h.fun_comp ENNReal.ofReal
  ext x
  simp only [schwarzRearrangementReal, schwarzRearrangement_congr_ae h']

/-- **Order preservation of `schwarzRearrangementReal`**: if `f ≤ᵐ[volume] g` and `g` has finite
superlevel volumes for positive thresholds, then
`schwarzRearrangementReal f ≤ᵐ[volume] schwarzRearrangementReal g`. -/
theorem schwarzRearrangementReal_mono_ae [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : AEMeasurable g volume)
    (hfg : f ≤ᵐ[volume] g)
    (hg_dist : ∀ t : ℝ, 0 < t → volume {y | t < g y} < ⊤) :
    schwarzRearrangementReal f ≤ᵐ[volume] schwarzRearrangementReal g := by
  have hle : schwarzRearrangement (fun y ↦ ENNReal.ofReal (f y)) ≤
      schwarzRearrangement (fun y ↦ ENNReal.ofReal (g y)) :=
    schwarzRearrangement_mono_ae (hfg.mono fun _ hy ↦ ENNReal.ofReal_le_ofReal hy)
  have h0 : volume ({0} : Set (EuclideanSpace ℝ (Fin n))) = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr h0] with x (hx : x ≠ 0)
  refine ENNReal.toReal_mono ?_ (hle x)
  refine (schwarzRearrangement_lt_top_of_ne_zero hg.ennreal_ofReal ?_ (by simp) hx).ne
  intro t ht
  rcases eq_or_ne t ⊤ with rfl | httop
  · simp
  · have ht_pos : 0 < t.toReal := ENNReal.toReal_pos ht.ne' httop
    have hset : {y | t < ENNReal.ofReal (g y)} = {y | t.toReal < g y} := by
      ext y
      exact ENNReal.lt_ofReal_iff_toReal_lt httop
    simpa [distributionFunction, hset] using hg_dist t.toReal ht_pos

/-- For `x ≠ 0`, `ENNReal.ofReal (schwarzRearrangementReal f x)` recovers
`schwarzRearrangement (fun y ↦ ENNReal.ofReal (f y)) x` when `f` has finite superlevel volumes. -/
theorem ofReal_schwarzRearrangementReal_of_ne_zero
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ENNReal.ofReal (schwarzRearrangementReal f x) =
      schwarzRearrangement (fun y ↦ ENNReal.ofReal (f y)) x := by
  refine ENNReal.ofReal_toReal
    (schwarzRearrangement_lt_top_of_ne_zero hf.ennreal_ofReal ?_ ?_ hx).ne
  · intro t ht
    rcases eq_or_ne t ⊤ with rfl | httop
    · simp
    · have ht_pos : 0 < t.toReal := ENNReal.toReal_pos ht.ne' httop
      have hset : {y | t < ENNReal.ofReal (f y)} = {y | t.toReal < f y} := by
        ext y
        exact ENNReal.lt_ofReal_iff_toReal_lt httop
      simpa [distributionFunction, hset] using hdist t.toReal ht_pos
  · simp

/-- Almost everywhere compatibility between `schwarzRearrangementReal` and
`schwarzRearrangement`. -/
theorem ofReal_schwarzRearrangementReal_ae [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) :
    (fun x ↦ ENNReal.ofReal (schwarzRearrangementReal f x)) =ᵐ[volume]
      schwarzRearrangement (fun y ↦ ENNReal.ofReal (f y)) := by
  have h0 : volume ({0} : Set (EuclideanSpace ℝ (Fin n))) = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr h0] with x hx
  exact ofReal_schwarzRearrangementReal_of_ne_zero hf hdist hx

/-- Almost everywhere identification of the superlevel sets of `schwarzRearrangementReal f` with the
Schwarz symmetrizations of the superlevel sets of `f` for `s ≥ 0`. -/
theorem superlevel_schwarzRearrangementReal_ae [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) {s : ℝ} (hs : 0 ≤ s) :
    {x | s < schwarzRearrangementReal f x} =ᵐ[volume]
      schwarzSymmetrization {y | s < f y} := by
  have hset : {y | ENNReal.ofReal s < ENNReal.ofReal (f y)} = {y | s < f y} := by
    ext y
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs
  rw [← hset, ← superlevel_schwarzRearrangement]
  filter_upwards [ofReal_schwarzRearrangementReal_ae hf hdist] with x hx
  simp only [← hx, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs]

/-- **Equimeasurability of `schwarzRearrangementReal`** for thresholds `s ≥ 0`. -/
theorem volume_lt_schwarzRearrangementReal [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) {s : ℝ} (hs : 0 ≤ s) :
    volume {x | s < schwarzRearrangementReal f x} = volume {y | s < f y} := by
  rw [measure_congr (superlevel_schwarzRearrangementReal_ae hf hdist hs),
    volume_schwarzSymmetrization]

/-- Every real-valued `MemLp f p` function (`0 < p < ∞`) has finite superlevel volumes for all
`t > 0`. -/
theorem volume_lt_lt_top_of_memLp
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) {t : ℝ} (ht : 0 < t) :
    volume {y | t < f y} < ⊤ := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hfin : ∫⁻ y, ENNReal.ofReal (f y) ^ p.toReal ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop hf.eLpNorm_lt_top).ne ?_
    refine lintegral_mono fun y ↦ ENNReal.rpow_le_rpow ?_ hp_pos.le
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self (f y))
  have hdist := distributionFunction_lt_top_of_lintegral_rpow_ne_top
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal hp_pos hfin (ENNReal.ofReal_pos.mpr ht)
  have hset : {y | ENNReal.ofReal t < ENNReal.ofReal (f y)} = {y | t < f y} := by
    ext y
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le
  simpa [distributionFunction, hset] using hdist

/-- **`Lᵖ` norm preservation for `schwarzRearrangementReal`** on nonnegative functions with finite
superlevel sets. -/
theorem eLpNorm_schwarzRearrangementReal [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEMeasurable f volume)
    (hf_nn : 0 ≤ᵐ[volume] f)
    (hdist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤) (p : ℝ≥0∞) :
    eLpNorm (schwarzRearrangementReal f) p volume = eLpNorm f p volume := by
  have h1 : eLpNorm (schwarzRearrangementReal f) p volume =
      eLpNorm (schwarzRearrangement (fun y ↦ ENNReal.ofReal (f y))) p volume := by
    refine eLpNorm_congr_enorm_ae
      (measurable_schwarzRearrangementReal f).aestronglyMeasurable
      (measurable_schwarzRearrangement _).aestronglyMeasurable ?_
    filter_upwards [ofReal_schwarzRearrangementReal_ae hf hdist] with x hx
    rw [Real.enorm_of_nonneg (schwarzRearrangementReal_nonneg f x), hx, enorm_eq_self]
  have h2 : eLpNorm f p volume =
      eLpNorm (fun y ↦ ENNReal.ofReal (f y)) p volume := by
    refine eLpNorm_congr_enorm_ae
      hf.aestronglyMeasurable hf.ennreal_ofReal.aestronglyMeasurable ?_
    filter_upwards [hf_nn] with y hy
    rw [Real.enorm_of_nonneg hy, enorm_eq_self]
  rw [h1, h2, eLpNorm_schwarzRearrangement hf.ennreal_ofReal]

/-- **`MemLp` preservation for `schwarzRearrangementReal`** on nonnegative functions
(`0 < p < ∞`). -/
theorem memLp_schwarzRearrangementReal [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hf_nn : 0 ≤ᵐ[volume] f) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) :
    MemLp (schwarzRearrangementReal f) p volume := by
  rw [MemLp, eLpNorm_schwarzRearrangementReal hf.aestronglyMeasurable.aemeasurable hf_nn
    (fun t ht ↦ volume_lt_lt_top_of_memLp hf hp0 hptop ht)]
  exact hf.eLpNorm_lt_top

/-- **One-sided hinge contraction for Schwarz rearrangement**: for almost everywhere measurable
nonnegative real functions `f, g` with finite superlevel sets and any threshold `r ≥ 0`,
`∫⁻ x, ENNReal.ofReal (schwarzRearrangementReal g x - schwarzRearrangementReal f x - r) ≤
  ∫⁻ x, ENNReal.ofReal (g x - f x - r)`. -/
theorem lintegral_ofReal_sub_sub_schwarzRearrangementReal_le [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (_hf_nn : 0 ≤ᵐ[volume] f)
    (hf_dist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    (hg_dist : ∀ t : ℝ, 0 < t → volume {y | t < g y} < ⊤)
    {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ x, ENNReal.ofReal (schwarzRearrangementReal g x - schwarzRearrangementReal f x - r) ≤
      ∫⁻ x, ENNReal.ofReal (g x - f x - r) := by
  simp_rw [sub_right_comm _ _ r]
  rw [lintegral_ofReal_sub_eq_lintegral_measure volume
      (measurable_schwarzRearrangementReal f).aemeasurable
      ((measurable_schwarzRearrangementReal g).sub_const r).aemeasurable,
    lintegral_ofReal_sub_eq_lintegral_measure volume hf (hg.sub_const r)]
  refine lintegral_mono fun s ↦ ?_
  rcases lt_or_ge s 0 with hs | hs
  · have hempty :
        {a | schwarzRearrangementReal f a ≤ s ∧ s < schwarzRearrangementReal g a - r} = ∅ := by
      ext a
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hle
      exact absurd (le_trans (schwarzRearrangementReal_nonneg f a) hle) (not_le_of_gt hs)
    rw [hempty, measure_empty]
    exact bot_le
  · have hdiff1 : {a | schwarzRearrangementReal f a ≤ s ∧ s < schwarzRearrangementReal g a - r} =
        {a | s + r < schwarzRearrangementReal g a} \ {a | s < schwarzRearrangementReal f a} := by
      ext a
      simp [lt_sub_iff_add_lt, and_comm]
    have hdiff2 : {a | f a ≤ s ∧ s < g a - r} = {a | s + r < g a} \ {a | s < f a} := by
      ext a
      simp [lt_sub_iff_add_lt, and_comm]
    have hae_g := superlevel_schwarzRearrangementReal_ae hg hg_dist (add_nonneg hs hr)
    have hae_f := superlevel_schwarzRearrangementReal_ae hf hf_dist hs
    rw [hdiff1, hdiff2, measure_congr (hae_g.diff hae_f)]
    exact volume_diff_schwarzSymmetrization_le _ _

/-- **`L¹` contraction of Schwarz rearrangement**: for almost everywhere measurable nonnegative
real functions `f, g` with finite superlevel sets,
`∫⁻ x, ‖schwarzRearrangementReal f x - schwarzRearrangementReal g x‖ₑ ≤ ∫⁻ x, ‖f x - g x‖ₑ`. -/
theorem lintegral_enorm_sub_schwarzRearrangementReal_le [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hf_nn : 0 ≤ᵐ[volume] f) (hg_nn : 0 ≤ᵐ[volume] g)
    (hf_dist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    (hg_dist : ∀ t : ℝ, 0 < t → volume {y | t < g y} < ⊤) :
    ∫⁻ x, ‖schwarzRearrangementReal f x - schwarzRearrangementReal g x‖ₑ ≤
      ∫⁻ x, ‖f x - g x‖ₑ := by
  have henorm (a b : ℝ) : ‖a - b‖ₑ = ENNReal.ofReal (b - a - 0) + ENNReal.ofReal (a - b - 0) := by
    rw [ofReal_sub_sub_add_ofReal_sub_sub le_rfl, sub_zero, Real.enorm_eq_ofReal_abs]
  simp_rw [henorm]
  have hmeas1 : AEMeasurable (fun x ↦ ENNReal.ofReal (schwarzRearrangementReal g x -
      schwarzRearrangementReal f x - 0)) volume := by fun_prop
  have hmeas2 : AEMeasurable (fun x ↦ ENNReal.ofReal (g x - f x - 0)) volume := by fun_prop
  rw [lintegral_add_left' hmeas1, lintegral_add_left' hmeas2]
  exact add_le_add
    (lintegral_ofReal_sub_sub_schwarzRearrangementReal_le hf hg hf_nn hf_dist hg_dist le_rfl)
    (lintegral_ofReal_sub_sub_schwarzRearrangementReal_le hg hf hg_nn hg_dist hf_dist le_rfl)

/-- **`Lᵖ` integral contraction (`1 < p < ∞`)**: for `1 < p`, Schwarz rearrangement contracts
`∫⁻ x, ‖f x - g x‖ₑ ^ p`. -/
theorem lintegral_enorm_sub_rpow_schwarzRearrangementReal_le [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hf_nn : 0 ≤ᵐ[volume] f) (hg_nn : 0 ≤ᵐ[volume] g)
    (hf_dist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    (hg_dist : ∀ t : ℝ, 0 < t → volume {y | t < g y} < ⊤)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, ‖schwarzRearrangementReal f x - schwarzRearrangementReal g x‖ₑ ^ p ≤
      ∫⁻ x, ‖f x - g x‖ₑ ^ p := by
  let f' := hf.mk f
  let g' := hg.mk g
  have hfg : ∫⁻ x, ‖f x - g x‖ₑ ^ p = ∫⁻ x, ‖f' x - g' x‖ₑ ^ p := by
    refine lintegral_congr_ae ?_
    filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
    rw [hfx, hgx]
  rw [hfg, schwarzRearrangementReal_congr_ae hf.ae_eq_mk,
    schwarzRearrangementReal_congr_ae hg.ae_eq_mk]
  have hf'_meas : Measurable f' := hf.measurable_mk
  have hg'_meas : Measurable g' := hg.measurable_mk
  have hf'_nn : 0 ≤ᵐ[volume] f' := hf_nn.trans_eq hf.ae_eq_mk
  have hg'_nn : 0 ≤ᵐ[volume] g' := hg_nn.trans_eq hg.ae_eq_mk
  have hf'_dist (t : ℝ) (ht : 0 < t) : volume {y | t < f' y} < ⊤ := by
    have heq : volume {y | t < f y} = volume {y | t < f' y} :=
      measure_congr (hf.ae_eq_mk.mono fun y hy ↦ by dsimp [f']; rw [hy])
    rw [← heq]
    exact hf_dist t ht
  have hg'_dist (t : ℝ) (ht : 0 < t) : volume {y | t < g' y} < ⊤ := by
    have heq : volume {y | t < g y} = volume {y | t < g' y} :=
      measure_congr (hg.ae_eq_mk.mono fun y hy ↦ by dsimp [g']; rw [hy])
    rw [← heq]
    exact hg_dist t ht
  let u := schwarzRearrangementReal f'
  let v := schwarzRearrangementReal g'
  have hu_meas : Measurable u := measurable_schwarzRearrangementReal f'
  have hv_meas : Measurable v := measurable_schwarzRearrangementReal g'
  change ∫⁻ x, ‖u x - v x‖ₑ ^ p ≤ ∫⁻ x, ‖f' x - g' x‖ₑ ^ p
  simp_rw [← edist_eq_enorm_sub, edist_rpow_eq_lintegral hp]
  have hswap1 := lintegral_lintegral_swap
    (μ := volume) (ν := volume.restrict (Ioi (0 : ℝ)))
    (f := fun x r ↦ ENNReal.ofReal (p * (p - 1) * r ^ (p - 2)) *
      (ENNReal.ofReal (v x - u x - r) + ENNReal.ofReal (u x - v x - r))) (by fun_prop)
  have hswap2 := lintegral_lintegral_swap
    (μ := volume) (ν := volume.restrict (Ioi (0 : ℝ)))
    (f := fun x r ↦ ENNReal.ofReal (p * (p - 1) * r ^ (p - 2)) *
      (ENNReal.ofReal (g' x - f' x - r) + ENNReal.ofReal (f' x - g' x - r))) (by fun_prop)
  rw [hswap1, hswap2]
  refine setLIntegral_mono' measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
  rw [lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
    lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop)]
  refine mul_le_mul_right (add_le_add ?_ ?_) _
  · exact lintegral_ofReal_sub_sub_schwarzRearrangementReal_le
      hf'_meas.aemeasurable hg'_meas.aemeasurable hf'_nn hf'_dist hg'_dist hr.le
  · exact lintegral_ofReal_sub_sub_schwarzRearrangementReal_le
      hg'_meas.aemeasurable hf'_meas.aemeasurable hg'_nn hg'_dist hf'_dist hr.le

/-- **`Lᵖ` contraction of Schwarz rearrangement (`1 ≤ p < ∞`)**: for any `1 ≤ p < ⊤` and almost
everywhere measurable nonnegative real functions `f, g` with finite superlevel sets,
`eLpNorm (schwarzRearrangementReal f - schwarzRearrangementReal g) p volume ≤
  eLpNorm (f - g) p volume`. -/
theorem eLpNorm_sub_schwarzRearrangementReal_le [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hf_nn : 0 ≤ᵐ[volume] f) (hg_nn : 0 ≤ᵐ[volume] g)
    (hf_dist : ∀ t : ℝ, 0 < t → volume {y | t < f y} < ⊤)
    (hg_dist : ∀ t : ℝ, 0 < t → volume {y | t < g y} < ⊤)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hptop : p ≠ ⊤) :
    eLpNorm (schwarzRearrangementReal f - schwarzRearrangementReal g) p volume ≤
      eLpNorm (f - g) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  rw [eLpNorm_eq_eLpNorm' hp0 hptop
      ((measurable_schwarzRearrangementReal f).sub
        (measurable_schwarzRearrangementReal g)).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' hp0 hptop (hf.sub hg).aestronglyMeasurable,
    eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  have hp_real : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hptop hp1
  refine ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr (zero_le_one.trans hp_real))
  rcases eq_or_lt_of_le hp_real with hp_eq | hp_gt
  · simp only [← hp_eq, Pi.sub_apply, ENNReal.rpow_one]
    exact lintegral_enorm_sub_schwarzRearrangementReal_le hf hg hf_nn hg_nn hf_dist hg_dist
  · exact
      lintegral_enorm_sub_rpow_schwarzRearrangementReal_le hf hg hf_nn hg_nn hf_dist hg_dist hp_gt

/-- **`Lᵖ` contraction of Schwarz rearrangement (`1 ≤ p < ∞`) for `MemLp` functions**: for any
`1 ≤ p < ⊤` and nonnegative `f, g` in `Lᵖ`,
`eLpNorm (schwarzRearrangementReal f - schwarzRearrangementReal g) p volume ≤
  eLpNorm (f - g) p volume`. -/
theorem eLpNorm_sub_schwarzRearrangementReal_le_of_memLp [NeZero n]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hg : MemLp g p volume)
    (hf_nn : 0 ≤ᵐ[volume] f) (hg_nn : 0 ≤ᵐ[volume] g)
    (hp1 : 1 ≤ p) (hptop : p ≠ ⊤) :
    eLpNorm (schwarzRearrangementReal f - schwarzRearrangementReal g) p volume ≤
      eLpNorm (f - g) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  exact eLpNorm_sub_schwarzRearrangementReal_le
    hf.aestronglyMeasurable.aemeasurable hg.aestronglyMeasurable.aemeasurable
    hf_nn hg_nn
    (fun _ ht ↦ volume_lt_lt_top_of_memLp hf hp0 hptop ht)
    (fun _ ht ↦ volume_lt_lt_top_of_memLp hg hp0 hptop ht)
    hp1 hptop

end TauCeti
