/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff

/-!
# Perimeter of Euclidean Boxes and Balls

This file establishes concrete perimeter formulas and bounds for fundamental geometric sets in
finite-dimensional inner product spaces and Euclidean coordinate spaces:

1. **Divergence of the identity and radial vector fields**:
   In any finite-dimensional real inner product space `E`, `divergence id x = Module.finrank ℝ E`
   and `divergence (fun y ↦ a • (y - c)) x = a * Module.finrank ℝ E`.
2. **Open/closed ball perimeter equivalence and radial ball perimeter lower bound**:
   Since `sphere c r` has Haar measure zero in any nontrivial finite-dimensional inner product
   space, `closedBall c r` and `ball c r` have identical relative and global perimeter. Testing
   with a smooth radial cutoff of `R⁻¹ • (x - c)` yields the radial lower bound
   `P(B(c, r)) ≥ (n / r) · μ(B(c, r)) = n · r^(n - 1) · μ(B(0, 1))`.
3. **Euclidean coordinate boxes, open/closed box equivalence, and Gauss–Green on boxes**:
   We define closed and open axis-aligned boxes `euclideanBox a b` and `euclideanOpenBox a b` in
   `EuclideanSpace ℝ (Fin n)`, prove that they are `volume`-almost everywhere equal, and hence have
   identical relative and global perimeter. Using the coordinate-splitting measure-preserving
   equivalence `euclideanSplitAt i`, Fubini's theorem, and the fundamental theorem of calculus on
   each coordinate slice `boxSlice i x'`, we prove the Gauss–Green divergence formula
   `integral_euclideanBox_divergence` on `euclideanBox a b`.
4. **Exact perimeter of `n`-dimensional Euclidean boxes**:
   Combining the Gauss–Green upper bound with a smooth dual test vector field built from coordinate
   bump functions near each pair of opposite faces, we prove that for `∀ i, a i < b i`,
   `perimeter volume (euclideanBox a b) = perimeter volume (euclideanOpenBox a b) =
   ENNReal.ofReal (2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j))`, and that every
   Euclidean box has finite perimeter (`HasFinitePerimeter`).
-/

public section

open Filter Function MeasureTheory Pointwise Set TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Distributions Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-! ### Section 1: Divergence of the identity map and radial vector fields -/

/-- The divergence of the identity map `id : E → E` on a finite-dimensional real inner product
space equals the dimension `Module.finrank ℝ E`. -/
@[simp]
theorem divergence_id [FiniteDimensional ℝ E] (x : E) :
    divergence (id : E → E) x = (Module.finrank ℝ E : ℝ) := by
  simp [divergence, LinearMap.trace_id]

/-- Lambda-form of `divergence_id`: `divergence (fun y : E ↦ y) x = Module.finrank ℝ E`. -/
@[simp]
theorem divergence_fun_id [FiniteDimensional ℝ E] (x : E) :
    divergence (fun y : E ↦ y) x = (Module.finrank ℝ E : ℝ) :=
  divergence_id x

/-- Translating the identity map by subtracting a constant vector preserves its divergence
`Module.finrank ℝ E`. -/
@[simp]
theorem divergence_sub_const [FiniteDimensional ℝ E] (c x : E) :
    divergence (fun y : E ↦ y - c) x = (Module.finrank ℝ E : ℝ) := by
  simpa using divergence_comp_sub (id : E → E) c x

/-- Translating the identity map by adding a constant vector preserves its divergence
`Module.finrank ℝ E`. -/
@[simp]
theorem divergence_add_const [FiniteDimensional ℝ E] (c x : E) :
    divergence (fun y : E ↦ y + c) x = (Module.finrank ℝ E : ℝ) := by
  simpa using divergence_comp_add_right (id : E → E) c x

/-- The divergence of the scaled radial vector field `y ↦ a • (y - c)` equals
`a * Module.finrank ℝ E`. -/
theorem divergence_smul_sub_const [FiniteDimensional ℝ E] (a : ℝ) (c x : E) :
    divergence (fun y : E ↦ a • (y - c)) x = a * (Module.finrank ℝ E : ℝ) := by
  rw [show (fun y : E ↦ a • (y - c)) = a • (fun y : E ↦ y - c) from rfl,
    divergence_const_smul, divergence_sub_const]

/-! ### Section 2: Open/closed ball perimeter equivalence and radial ball perimeter lower bound -/

section BallPerimeter

variable [MeasurableSpace E] {μ : Measure E}

/-- In a subsingleton space `E`, every set has zero relative perimeter since the Fréchet
derivative and divergence of every vector field vanish identically. -/
theorem relativePerimeter_eq_zero_of_subsingleton [Subsingleton E] (s : Set E) :
    relativePerimeter μ Ω s = 0 := by
  unfold relativePerimeter distributionalVariation
  have hdiv : ∀ (φ : 𝓓(Ω, E)) (x : E), divergence (φ : E → E) x = 0 := fun φ x ↦ by
    simp [divergence, Subsingleton.elim (fderiv ℝ (φ : E → E) x) 0]
  simp [hdiv]

/-- In a subsingleton space `E`, every set has zero global perimeter. -/
theorem perimeter_eq_zero_of_subsingleton [Subsingleton E] (s : Set E) :
    perimeter μ s = 0 :=
  relativePerimeter_eq_zero_of_subsingleton s

/-- A closed ball `Metric.closedBall c r` and the corresponding open ball `Metric.ball c r` have
the same relative perimeter on every open set `Ω` with respect to any additive Haar measure `μ`. -/
theorem relativePerimeter_closedBall_eq_ball [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] (c : E) (r : ℝ) :
    relativePerimeter μ Ω (Metric.closedBall c r) = relativePerimeter μ Ω (Metric.ball c r) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [relativePerimeter_eq_zero_of_subsingleton, relativePerimeter_eq_zero_of_subsingleton]
  · rw [← Metric.ball_union_sphere,
      relativePerimeter_union_null (Metric.ball c r) (Measure.addHaar_sphere μ c r)]

/-- A closed ball `Metric.closedBall c r` and the corresponding open ball `Metric.ball c r` have
the same global perimeter with respect to any additive Haar measure `μ`. -/
theorem perimeter_closedBall_eq_ball [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] (c : E) (r : ℝ) :
    perimeter μ (Metric.closedBall c r) = perimeter μ (Metric.ball c r) :=
  relativePerimeter_closedBall_eq_ball c r

/-- **Radial lower bound on relative ball perimeter**: if `0 < r < R` and `Metric.ball c R ⊆ Ω`,
testing the distributional perimeter of `Metric.ball c r` against the radial vector field
`x ↦ R⁻¹ • (x - c)` localized by a smooth radial bump supported in `Metric.ball c R` gives
`relativePerimeter μ Ω (Metric.ball c r) ≥ ENNReal.ofReal (finrank ℝ E / R) * μ (ball c r)`. -/
theorem relativePerimeter_ball_ge_of_ball_subset [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] (c : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRΩ : Metric.ball c R ⊆ Ω) :
    ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / R) * μ (Metric.ball c r) ≤
      relativePerimeter μ Ω (Metric.ball c r) := by
  have hRpos : 0 < R := hr.trans hrR
  let R' : ℝ := (r + R) / 2
  have hrR' : r < R' := by dsimp [R']; linarith
  have hR'R : R' < R := by dsimp [R']; linarith
  let χ : ContDiffBump c := ⟨r, R', hr, hrR'⟩
  have hχ_sub : tsupport χ ⊆ Ω := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball hR'R).trans hRΩ
  let φ : 𝓓(Ω, E) :=
    { toFun := fun x ↦ R⁻¹ • (χ x • (x - c))
      contDiff' := contDiff_const.smul (χ.contDiff.smul (contDiff_id.sub contDiff_const))
      hasCompactSupport' := (χ.hasCompactSupport.smul_right).smul_left
      tsupport_subset' :=
        (tsupport_smul_subset_right _ _).trans
          ((tsupport_smul_subset_left _ _).trans hχ_sub) }
  have hφ_norm : ∀ x, ‖φ x‖ ≤ 1 := fun x ↦ by
    change ‖R⁻¹ • (χ x • (x - c))‖ ≤ 1
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hRpos.le),
      Real.norm_of_nonneg χ.nonneg]
    by_cases hx : x ∈ Metric.ball c R'
    · have hxc : ‖x - c‖ ≤ R := (mem_ball_iff_norm.1 hx).le.trans hR'R.le
      calc R⁻¹ * (χ x * ‖x - c‖) ≤ R⁻¹ * (1 * R) := by
            gcongr
            exact χ.le_one
        _ = 1 := by rw [one_mul, inv_mul_cancel₀ hRpos.ne']
    · have h0 : χ x = 0 := Function.notMem_support.1 (by rwa [χ.support_eq])
      simp [h0]
  have hdiv_ball : ∀ x ∈ Metric.ball c r,
      divergence (φ : E → E) x = (Module.finrank ℝ E : ℝ) / R := by
    intro x hx
    have hev : (φ : E → E) =ᶠ[𝓝 x] fun y ↦ R⁻¹ • (y - c) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      change R⁻¹ • (χ y • (y - c)) = R⁻¹ • (y - c)
      rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_smul]
    rw [divergence, hev.fderiv_eq, ← divergence, divergence_smul_sub_const, div_eq_inv_mul]
  have hint : ∫ x in (Ω : Set E),
      (Metric.ball c r).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ =
      (μ (Metric.ball c r)).toReal * ((Module.finrank ℝ E : ℝ) / R) := by
    have hsub : Metric.ball c r ⊆ Ω := (Metric.ball_subset_ball hrR.le).trans hRΩ
    rw [show (fun x ↦ (Metric.ball c r).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x) =
      (Metric.ball c r).indicator (fun x ↦ divergence (φ : E → E) x) by
        ext x; by_cases hx : x ∈ Metric.ball c r <;> simp [hx]]
    rw [setIntegral_indicator Metric.isOpen_ball.measurableSet, inter_eq_right.2 hsub,
      setIntegral_congr_fun Metric.isOpen_ball.measurableSet hdiv_ball, setIntegral_const,
      Measure.real, smul_eq_mul]
  have hle := le_distributionalVariation (μ := μ) φ hφ_norm
    ((Metric.ball c r).indicator fun _ ↦ (1 : ℝ))
  rwa [hint, mul_comm, ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) hRpos.le),
    ENNReal.ofReal_toReal measure_ball_lt_top.ne] at hle

/-- **Radial lower bound on ball perimeter**: for `0 < r`, the perimeter of `Metric.ball c r` is
at least `(Module.finrank ℝ E / r) * μ (Metric.ball c r)`. -/
theorem perimeter_ball_ge [FiniteDimensional ℝ E] [BorelSpace E] [IsLocallyFiniteMeasure μ]
    (c : E) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / r) * μ (Metric.ball c r) ≤
      perimeter μ (Metric.ball c r) := by
  have hlim : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / (r + 1 / (n + 1 : ℝ))) *
        μ (Metric.ball c r))
      atTop (𝓝 (ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / r) * μ (Metric.ball c r))) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr measure_ball_lt_top.ne)
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    refine tendsto_const_nhds.div ?_ hr.ne'
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine le_of_tendsto' hlim fun n ↦ ?_
  have hrR : r < r + 1 / (n + 1 : ℝ) := lt_add_of_pos_right r (by positivity)
  exact relativePerimeter_ball_ge_of_ball_subset c hr hrR (subset_univ _)

/-- **Radial lower bound on closed ball perimeter**: for `0 < r`, the perimeter of
`Metric.closedBall c r` is at least `(Module.finrank ℝ E / r) * μ (Metric.closedBall c r)`. -/
theorem perimeter_closedBall_ge [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    (c : E) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / r) * μ (Metric.closedBall c r) ≤
      perimeter μ (Metric.closedBall c r) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [perimeter_eq_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  · rw [perimeter_closedBall_eq_ball, ← Metric.ball_union_sphere]
    refine (mul_le_mul_of_nonneg_left ((measure_union_le _ _).trans
      (by simp [Measure.addHaar_sphere μ c r])) (by positivity)).trans (perimeter_ball_ge c hr)

/-- **Radial lower bound on ball perimeter in terms of the unit ball**: for `0 < r` in a
nontrivial finite-dimensional inner product space with additive Haar measure `μ`,
`perimeter μ (Metric.ball c r) ≥ n * r^(n - 1) * μ (Metric.ball 0 1)`. -/
theorem perimeter_ball_ge_unitBall [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * r ^ (Module.finrank ℝ E - 1)) *
        μ (Metric.ball (0 : E) 1) ≤
      perimeter μ (Metric.ball c r) := by
  refine le_trans ?_ (perimeter_ball_ge c hr)
  rw [Measure.addHaar_ball μ c hr.le, ← mul_assoc,
    ← ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) hr.le)]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by positivity)
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hpow : r ^ Module.finrank ℝ E = r * r ^ (Module.finrank ℝ E - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ']
  rw [hpow]
  exact le_of_eq (by field_simp [hr.ne'])

/-- **Radial lower bound on closed ball perimeter in terms of the unit ball**: for `0 < r` in a
nontrivial finite-dimensional inner product space with additive Haar measure `μ`,
`perimeter μ (Metric.closedBall c r) ≥ n * r^(n - 1) * μ (Metric.ball 0 1)`. -/
theorem perimeter_closedBall_ge_unitBall [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * r ^ (Module.finrank ℝ E - 1)) *
        μ (Metric.ball (0 : E) 1) ≤
      perimeter μ (Metric.closedBall c r) := by
  rw [perimeter_closedBall_eq_ball]; exact perimeter_ball_ge_unitBall c hr

end BallPerimeter

/-! ### Section 3: Euclidean boxes, volume, and open/closed box equivalence -/

/-- The closed axis-aligned rectangular box `∏ i, [a i, b i]` in `EuclideanSpace ℝ (Fin n)`. -/
def euclideanBox {n : ℕ} (a b : Fin n → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}

/-- The open axis-aligned rectangular box `∏ i, (a i, b i)` in `EuclideanSpace ℝ (Fin n)`. -/
def euclideanOpenBox {n : ℕ} (a b : Fin n → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, a i < x i ∧ x i < b i}

/-- The open Euclidean box `euclideanOpenBox a b` is contained in the closed Euclidean box
`euclideanBox a b`. -/
theorem euclideanOpenBox_subset_euclideanBox {n : ℕ} (a b : Fin n → ℝ) :
    euclideanOpenBox a b ⊆ euclideanBox a b :=
  fun _ hx i ↦ ⟨(hx i).1.le, (hx i).2.le⟩

/-- `euclideanBox a b` is the preimage under `WithLp.ofLp` of the order interval `Icc a b`. -/
theorem euclideanBox_eq_preimage_Icc {n : ℕ} (a b : Fin n → ℝ) :
    euclideanBox a b = WithLp.ofLp ⁻¹' Icc a b := by
  ext x; simp [euclideanBox, Pi.le_def, forall_and]

/-- `euclideanOpenBox a b` is the preimage under `WithLp.ofLp` of
`Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))`. -/
theorem euclideanOpenBox_eq_preimage_pi {n : ℕ} (a b : Fin n → ℝ) :
    euclideanOpenBox a b = WithLp.ofLp ⁻¹' (Set.pi Set.univ fun i ↦ Ioo (a i) (b i)) := by
  ext x; simp [euclideanOpenBox]

/-- Every closed Euclidean box `euclideanBox a b` is a closed set. -/
theorem isClosed_euclideanBox {n : ℕ} (a b : Fin n → ℝ) :
    IsClosed (euclideanBox a b) := by
  rw [euclideanBox_eq_preimage_Icc]; exact isClosed_Icc.preimage (PiLp.continuous_ofLp 2 _)

/-- Every closed Euclidean box `euclideanBox a b` is a compact set. -/
theorem isCompact_euclideanBox {n : ℕ} (a b : Fin n → ℝ) :
    IsCompact (euclideanBox a b) := by
  rw [euclideanBox_eq_preimage_Icc]
  exact (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isCompact_preimage.2 isCompact_Icc

/-- Every closed Euclidean box `euclideanBox a b` is measurable. -/
theorem measurableSet_euclideanBox {n : ℕ} (a b : Fin n → ℝ) :
    MeasurableSet (euclideanBox a b) :=
  (isClosed_euclideanBox a b).measurableSet

/-- Every open Euclidean box `euclideanOpenBox a b` is an open set. -/
theorem isOpen_euclideanOpenBox {n : ℕ} (a b : Fin n → ℝ) :
    IsOpen (euclideanOpenBox a b) := by
  rw [euclideanOpenBox_eq_preimage_pi]
  exact (isOpen_set_pi finite_univ fun i _ ↦ isOpen_Ioo).preimage (PiLp.continuous_ofLp 2 _)

/-- Every open Euclidean box `euclideanOpenBox a b` is measurable. -/
theorem measurableSet_euclideanOpenBox {n : ℕ} (a b : Fin n → ℝ) :
    MeasurableSet (euclideanOpenBox a b) :=
  (isOpen_euclideanOpenBox a b).measurableSet

/-- The Lebesgue volume of the closed box `euclideanBox a b` is the product of its side lengths
`∏ i, ENNReal.ofReal (b i - a i)`. -/
theorem volume_euclideanBox {n : ℕ} (a b : Fin n → ℝ) :
    volume (euclideanBox a b) = ∏ i : Fin n, ENNReal.ofReal (b i - a i) := by
  rw [euclideanBox_eq_preimage_Icc,
    (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage isClosed_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]

/-- The Lebesgue volume of the open box `euclideanOpenBox a b` is the product of its side lengths
`∏ i, ENNReal.ofReal (b i - a i)`. -/
theorem volume_euclideanOpenBox {n : ℕ} (a b : Fin n → ℝ) :
    volume (euclideanOpenBox a b) = ∏ i : Fin n, ENNReal.ofReal (b i - a i) := by
  rw [euclideanOpenBox_eq_preimage_pi,
    (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
      (isOpen_set_pi finite_univ fun i _ ↦ isOpen_Ioo).nullMeasurableSet,
    Real.volume_pi_Ioo]

/-- The open Euclidean box `euclideanOpenBox a b` and the closed Euclidean box `euclideanBox a b`
are `volume`-almost everywhere equal. -/
theorem euclideanOpenBox_ae_eq_euclideanBox {n : ℕ} (a b : Fin n → ℝ) :
    euclideanOpenBox a b =ᵐ[volume] euclideanBox a b := by
  rw [euclideanOpenBox_eq_preimage_pi, euclideanBox_eq_preimage_Icc]
  exact (PiLp.volume_preserving_ofLp (Fin n)).quasiMeasurePreserving.ae_eq_comp
    Measure.univ_pi_Ioo_ae_eq_Icc

/-- Open and closed Euclidean boxes have identical relative perimeter on every open set `Ω`. -/
theorem relativePerimeter_euclideanOpenBox_eq {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (a b : Fin n → ℝ) :
    relativePerimeter volume Ω (euclideanOpenBox a b) =
      relativePerimeter volume Ω (euclideanBox a b) :=
  relativePerimeter_congr_ae (ae_restrict_of_ae (euclideanOpenBox_ae_eq_euclideanBox a b))

/-- Open and closed Euclidean boxes have identical global perimeter. -/
theorem perimeter_euclideanOpenBox_eq {n : ℕ} (a b : Fin n → ℝ) :
    perimeter volume (euclideanOpenBox a b) = perimeter volume (euclideanBox a b) :=
  perimeter_congr_ae (euclideanOpenBox_ae_eq_euclideanBox a b)

/-- If `b i ≤ a i` for some coordinate `i`, then `euclideanBox a b` has Lebesgue volume zero. -/
theorem volume_euclideanBox_eq_zero_of_le {n : ℕ} {a b : Fin n → ℝ} (h : ∃ i, b i ≤ a i) :
    volume (euclideanBox a b) = 0 := by
  rcases h with ⟨i, hi⟩
  rw [volume_euclideanBox]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 hi))

/-- If `b i ≤ a i` for some coordinate `i`, then `euclideanBox a b` has zero perimeter. -/
theorem perimeter_euclideanBox_eq_zero_of_le {n : ℕ} {a b : Fin n → ℝ} (h : ∃ i, b i ≤ a i) :
    perimeter volume (euclideanBox a b) = 0 := by
  simpa [perimeter] using
    relativePerimeter_union_null (Ω := ⊤) ∅ (volume_euclideanBox_eq_zero_of_le h)

/-- If `b i ≤ a i` for some coordinate `i`, then `euclideanOpenBox a b` has zero perimeter. -/
theorem perimeter_euclideanOpenBox_eq_zero_of_le {n : ℕ} {a b : Fin n → ℝ} (h : ∃ i, b i ≤ a i) :
    perimeter volume (euclideanOpenBox a b) = 0 := by
  rw [perimeter_euclideanOpenBox_eq, perimeter_euclideanBox_eq_zero_of_le h]

/-! ### Section 4: Coordinate splitting, Gauss–Green on boxes, and exact box perimeter -/

/-- Measurable equivalence splitting `EuclideanSpace ℝ (Fin n)` at coordinate `i : Fin n` into
the `i`-th coordinate in `ℝ` and the remaining coordinates in `{k : Fin n // k ≠ i} → ℝ`. -/
noncomputable def euclideanSplitAt {n : ℕ} (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ᵐ ℝ × ({k : Fin n // k ≠ i} → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.trans
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ ℝ) (· = i)).trans
      ((MeasurableEquiv.piUnique (fun _ : {k : Fin n // k = i} ↦ ℝ)).prodCongr
        (MeasurableEquiv.refl _)))

/-- The coordinate-splitting equivalence `euclideanSplitAt i` is measure-preserving between
Lebesgue volume on `EuclideanSpace ℝ (Fin n)` and the product measure `volume.prod volume`. -/
theorem measurePreserving_euclideanSplitAt {n : ℕ} (i : Fin n) :
    MeasurePreserving (euclideanSplitAt i) volume (volume.prod volume) := by
  rw [euclideanSplitAt, MeasurableEquiv.coe_trans, MeasurableEquiv.coe_trans]
  have h0 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  have h1 : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ ℝ) (· = i))
      volume (volume.prod volume) := by
    convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n ↦ ℝ) (· = i)
    congr; exact Subsingleton.elim _ _
  have h2 : MeasurePreserving
      (MeasurableEquiv.piUnique (fun _ : {k : Fin n // k = i} ↦ ℝ)) volume volume := by
    convert volume_preserving_piUnique (fun _ : {k : Fin n // k = i} ↦ ℝ)
  exact ((h2.prod (MeasurePreserving.id volume)).comp h1).comp h0

/-- The coordinate slice map inserting `t : ℝ` at coordinate `i` and `x'` at all coordinates
`j ≠ i`. -/
noncomputable def boxSlice {n : ℕ} (i : Fin n) (x' : {k : Fin n // k ≠ i} → ℝ) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  (euclideanSplitAt i).symm (t, x')

/-- Evaluating `boxSlice i x' t` at coordinate `i` returns `t`. -/
@[simp]
theorem boxSlice_apply_eq {n : ℕ} (i : Fin n) (x' : {k : Fin n // k ≠ i} → ℝ) (t : ℝ) :
    boxSlice i x' t i = t := by
  simp [boxSlice, euclideanSplitAt, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd]
  rfl

/-- Evaluating `boxSlice i x' t` at coordinate `j ≠ i` returns `x' ⟨j, hj⟩`. -/
@[simp]
theorem boxSlice_apply_ne {n : ℕ} (i : Fin n) (x' : {k : Fin n // k ≠ i} → ℝ) (t : ℝ)
    {j : Fin n} (hj : j ≠ i) :
    boxSlice i x' t j = x' ⟨j, hj⟩ := by
  simp [boxSlice, euclideanSplitAt, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, hj]
  rfl

/-- `boxSlice i x' t` decomposes affinely as `boxSlice i x' 0 + t • EuclideanSpace.single i 1`. -/
theorem boxSlice_eq_add_smul {n : ℕ} (i : Fin n) (x' : {k : Fin n // k ≠ i} → ℝ) (t : ℝ) :
    boxSlice i x' t = boxSlice i x' 0 + t • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- Joint continuity of `(t, x') ↦ boxSlice i x' t`. -/
theorem continuous_boxSlice_uncurry {n : ℕ} (i : Fin n) :
    Continuous (fun p : ℝ × ({k : Fin n // k ≠ i} → ℝ) ↦ boxSlice i p.2 p.1) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp (continuous_pi fun j ↦ ?_)
  change Continuous (fun p : ℝ × ({k : Fin n // k ≠ i} → ℝ) ↦ boxSlice i p.2 p.1 j)
  by_cases hj : j = i
  · subst hj; simp_rw [boxSlice_apply_eq]; exact continuous_fst
  · simp_rw [boxSlice_apply_ne i _ _ hj]
    exact (continuous_apply (⟨j, hj⟩ : {k : Fin n // k ≠ i})).comp continuous_snd

/-- The derivative of `t ↦ boxSlice i x' t` is the `i`-th standard basis vector
`EuclideanSpace.single i 1`. -/
theorem hasDerivAt_boxSlice {n : ℕ} (i : Fin n) (x' : {k : Fin n // k ≠ i} → ℝ) (t : ℝ) :
    HasDerivAt (boxSlice i x') (EuclideanSpace.single i (1 : ℝ)) t := by
  have hfun : boxSlice i x' = fun s ↦ boxSlice i x' 0 + s • EuclideanSpace.single i (1 : ℝ) :=
    funext (boxSlice_eq_add_smul i x')
  rw [hfun]
  simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add
    (boxSlice i x' 0)

/-- Under `(euclideanSplitAt i).symm`, the box `euclideanBox a b` pulls back to the product of
`Icc (a i) (b i)` and the `(n - 1)`-dimensional face `∏_{j ≠ i} [a j, b j]`. -/
theorem euclideanSplitAt_symm_preimage_euclideanBox {n : ℕ} (i : Fin n) (a b : Fin n → ℝ) :
    (euclideanSplitAt i).symm ⁻¹' euclideanBox a b =
      Icc (a i) (b i) ×ˢ
        Set.pi Set.univ (fun j : {k : Fin n // k ≠ i} ↦ Icc (a j.1) (b j.1)) := by
  ext ⟨t, x'⟩
  simp only [mem_preimage, euclideanBox, mem_ofPred_eq, mem_prod, Set.mem_pi, mem_Icc]
  change (∀ j, a j ≤ boxSlice i x' t j ∧ boxSlice i x' t j ≤ b j) ↔ _
  refine ⟨fun h ↦ ⟨by simpa using h i, fun ⟨j, hj⟩ _ ↦ by simpa [hj] using h j⟩,
    fun ⟨ht, hx'⟩ j ↦ ?_⟩
  by_cases hj : j = i
  · subst hj; simpa using ht
  · simpa [hj] using hx' ⟨j, hj⟩ (mem_univ _)

/-- **Gauss–Green divergence formula on an `n`-dimensional Euclidean box**: for any `C¹` vector
field `φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)` and any box `euclideanBox a b`
with `∀ i, a i ≤ b i`, the integral of `divergence φ` over `euclideanBox a b` equals the sum over
all coordinates `i` of the flux integrals across the opposite faces `x i = b i` and `x i = a i`. -/
theorem integral_euclideanBox_divergence {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i ≤ b i)
    {φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hφ : ContDiff ℝ 1 φ) :
    ∫ x in euclideanBox a b, divergence φ x =
      ∑ i : Fin n,
        ∫ x' in Icc (fun j : {k : Fin n // k ≠ i} ↦ a j.1) (fun j ↦ b j.1),
          (⟪EuclideanSpace.single i (1 : ℝ), φ (boxSlice i x' (b i))⟫_ℝ -
            ⟪EuclideanSpace.single i (1 : ℝ), φ (boxSlice i x' (a i))⟫_ℝ) := by
  let e : Fin n → EuclideanSpace ℝ (Fin n) := fun i ↦ EuclideanSpace.single i (1 : ℝ)
  let g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x ↦ ⟪e i, fderiv ℝ φ x (e i)⟫_ℝ
  have hg_cont : ∀ i, Continuous (g i) := fun i ↦
    continuous_const.inner ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hdiv : ∀ x, divergence φ x = ∑ i : Fin n, g i x := fun x ↦ by
    rw [divergence_eq_sum_orthonormalBasis (EuclideanSpace.basisFun (Fin n) ℝ)]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [g, e, EuclideanSpace.basisFun_apply]
  simp_rw [hdiv]
  rw [integral_finsetSum _ fun i _ ↦
    (hg_cont i).continuousOn.integrableOn_compact (isCompact_euclideanBox a b)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  let Face : Set ({k : Fin n // k ≠ i} → ℝ) :=
    Icc (fun j : {k : Fin n // k ≠ i} ↦ a j.1) (fun j ↦ b j.1)
  have hFace : Set.pi Set.univ (fun j : {k : Fin n // k ≠ i} ↦ Icc (a j.1) (b j.1)) = Face := by
    ext x'; simp [Face, Pi.le_def]
  have hpre : (euclideanSplitAt i).symm ⁻¹' euclideanBox a b = Icc (a i) (b i) ×ˢ Face := by
    rw [euclideanSplitAt_symm_preimage_euclideanBox, hFace]
  have hmp := (measurePreserving_euclideanSplitAt i).symm
  rw [← hmp.setIntegral_preimage_emb (euclideanSplitAt i).symm.measurableEmbedding (g i)
    (euclideanBox a b), hpre]
  have hIntProd : IntegrableOn (fun p : ℝ × ({k : Fin n // k ≠ i} → ℝ) ↦ g i (boxSlice i p.2 p.1))
      (Icc (a i) (b i) ×ˢ Face) (volume.prod volume) :=
    ((hg_cont i).comp (continuous_boxSlice_uncurry i)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [IntegrableOn, ← Measure.prod_restrict] at hIntProd
  rw [← Measure.prod_restrict (Icc (a i) (b i)) Face]
  change ∫ p, g i (boxSlice i p.2 p.1)
    ∂(volume.restrict (Icc (a i) (b i))).prod (volume.restrict Face) = _
  rw [integral_prod_symm _ hIntProd]
  refine setIntegral_congr_fun isClosed_Icc.measurableSet fun x' _ ↦ ?_
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hab i)]
  have hderiv : ∀ t ∈ uIcc (a i) (b i),
      HasDerivAt (fun s ↦ ⟪e i, φ (boxSlice i x' s)⟫_ℝ) (g i (boxSlice i x' t)) t := fun t _ ↦ by
    have hdφ : HasFDerivAt φ (fderiv ℝ φ (boxSlice i x' t)) (boxSlice i x' t) :=
      (hφ.differentiable one_ne_zero _).hasFDerivAt
    have hd1 : HasDerivAt (fun s ↦ φ (boxSlice i x' s)) (fderiv ℝ φ (boxSlice i x' t) (e i)) t :=
      hdφ.comp_hasDerivAt t (hasDerivAt_boxSlice i x' t)
    simpa [g] using (hasDerivAt_const t (e i)).inner ℝ hd1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (((hg_cont i).comp
      ((continuous_boxSlice_uncurry i).comp
        (continuous_id.prodMk continuous_const))).intervalIntegrable _ _)

/-- **Upper bound on the perimeter of an `n`-dimensional Euclidean box**: for `∀ i, a i ≤ b i`,
the perimeter of `euclideanBox a b` is at most the total `(n - 1)`-dimensional surface area of its
`2n` faces, `2 * ∑ i, ∏ j ≠ i, (b j - a j)`. -/
theorem perimeter_euclideanBox_le {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i ≤ b i) :
    perimeter volume (euclideanBox a b) ≤
      ENNReal.ofReal (2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j)) := by
  rw [perimeter, relativePerimeter_eq_iSup_of_measurableSet (measurableSet_euclideanBox a b)]
  refine iSup₂_le fun φ hφ ↦ ENNReal.ofReal_le_ofReal ?_
  rw [Opens.coe_top, inter_univ,
    integral_euclideanBox_divergence hab (φ.contDiff.of_le (by simp)), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  let Face : Set ({k : Fin n // k ≠ i} → ℝ) :=
    Icc (fun j : {k : Fin n // k ≠ i} ↦ a j.1) (fun j ↦ b j.1)
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hcont : Continuous (fun x' : {k : Fin n // k ≠ i} → ℝ ↦
      ⟪e, φ (boxSlice i x' (b i))⟫_ℝ - ⟪e, φ (boxSlice i x' (a i))⟫_ℝ) := by
    have hc : ∀ t, Continuous (fun x' : {k : Fin n // k ≠ i} → ℝ ↦ boxSlice i x' t) := fun t ↦
      (continuous_boxSlice_uncurry i).comp (continuous_const.prodMk continuous_id)
    exact (continuous_const.inner (φ.continuous.comp (hc (b i)))).sub
      (continuous_const.inner (φ.continuous.comp (hc (a i))))
  have hle : ∫ x' in Face,
      (⟪e, φ (boxSlice i x' (b i))⟫_ℝ - ⟪e, φ (boxSlice i x' (a i))⟫_ℝ) ≤
      ∫ _ in Face, (2 : ℝ) := by
    refine setIntegral_mono_on (hcont.continuousOn.integrableOn_compact isCompact_Icc)
      (integrableOn_const isCompact_Icc.measure_lt_top.ne) isClosed_Icc.measurableSet fun x' _ ↦ ?_
    have h1 : ⟪e, φ (boxSlice i x' (b i))⟫_ℝ ≤ 1 :=
      (real_inner_le_norm _ _).trans (by rw [he, one_mul]; exact hφ _)
    have h2 : |⟪e, φ (boxSlice i x' (a i))⟫_ℝ| ≤ 1 :=
      (abs_real_inner_le_norm e _).trans (by rw [he, one_mul]; exact hφ _)
    linarith [neg_abs_le ⟪e, φ (boxSlice i x' (a i))⟫_ℝ]
  refine hle.trans_eq ?_
  rw [setIntegral_const, Measure.real]; dsimp only [Face]
  rw [Real.volume_Icc_pi, ENNReal.toReal_prod, smul_eq_mul, mul_comm]
  congr 1
  rw [Finset.prod_congr rfl fun j _ ↦ ENNReal.toReal_ofReal (sub_nonneg.2 (hab j.1))]
  exact (Finset.prod_subtype (Finset.univ.erase i) (by simp) (fun j ↦ b j - a j)).symm

/-- **Upper bound on the perimeter of an open Euclidean box**: for `∀ i, a i ≤ b i`,
`perimeter volume (euclideanOpenBox a b) ≤ 2 * ∑ i, ∏ j ≠ i, (b j - a j)`. -/
theorem perimeter_euclideanOpenBox_le {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i ≤ b i) :
    perimeter volume (euclideanOpenBox a b) ≤
      ENNReal.ofReal (2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j)) := by
  rw [perimeter_euclideanOpenBox_eq]; exact perimeter_euclideanBox_le hab

/-- **Inner `δ`-margin lower bound on the perimeter of a Euclidean box**: for `0 < δ` with
`2 * δ < b i - a i` in every coordinate `i`, testing against a smooth compactly supported vector
field whose `i`-th component equals `+1` on the shrunk upper face and `-1` on the shrunk lower face
yields `perimeter volume (euclideanBox a b) ≥ 2 * ∑ i, ∏ j ≠ i, (b j - a j - 2 * δ)`. -/
theorem perimeter_euclideanBox_ge_of_delta {n : ℕ} {a b : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (habδ : ∀ i : Fin n, 2 * δ < b i - a i) :
    ENNReal.ofReal (2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j - 2 * δ)) ≤
      perimeter volume (euclideanBox a b) := by
  have hab : ∀ i, a i ≤ b i := fun i ↦ by linarith [habδ i]
  let α : ∀ k : Fin n, ContDiffBump (a k) := fun k ↦ ⟨δ / 4, δ / 2, by linarith, by linarith⟩
  let β : ∀ k : Fin n, ContDiffBump (b k) := fun k ↦ ⟨δ / 4, δ / 2, by linarith, by linarith⟩
  let θ : ∀ k : Fin n, ContDiffBump ((a k + b k) / 2) :=
    fun k ↦ ⟨(b k - a k) / 2 - δ, (b k - a k) / 2 - δ / 2, by linarith [habδ k], by linarith⟩
  have hα_supp : ∀ k t, α k t ≠ 0 → a k - δ / 2 < t ∧ t < a k + δ / 2 := fun k t ht ↦ by
    have hmem : t ∈ Metric.ball (a k) (δ / 2) := (α k).support_eq ▸ Function.mem_support.2 ht
    rwa [Real.ball_eq_Ioo, mem_Ioo] at hmem
  have hβ_supp : ∀ k t, β k t ≠ 0 → b k - δ / 2 < t ∧ t < b k + δ / 2 := fun k t ht ↦ by
    have hmem : t ∈ Metric.ball (b k) (δ / 2) := (β k).support_eq ▸ Function.mem_support.2 ht
    rwa [Real.ball_eq_Ioo, mem_Ioo] at hmem
  have hθ_supp : ∀ k t, θ k t ≠ 0 → a k + δ / 2 < t ∧ t < b k - δ / 2 := fun k t ht ↦ by
    have hmem : t ∈ Metric.ball ((a k + b k) / 2) ((b k - a k) / 2 - δ / 2) :=
      (θ k).support_eq ▸ Function.mem_support.2 ht
    rw [Real.ball_eq_Ioo, mem_Ioo] at hmem
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hβα_abs : ∀ k t, |β k t - α k t| ≤ 1 := fun k t ↦ by
    by_cases hα0 : α k t = 0
    · rw [hα0, sub_zero, abs_of_nonneg (β k).nonneg]; exact (β k).le_one
    · have hβ0 : β k t = 0 := by
        by_contra hβ0; linarith [(hα_supp k t hα0).2, (hβ_supp k t hβ0).1, habδ k]
      rw [hβ0, zero_sub, abs_neg, abs_of_nonneg (α k).nonneg]; exact (α k).le_one
  have hθ_zero_of_βα : ∀ k t, β k t - α k t ≠ 0 → θ k t = 0 := fun k t hne ↦ by
    by_contra hθ0
    have h1 := hθ_supp k t hθ0
    have hα0 : α k t = 0 := by by_contra h; linarith [(hα_supp k t h).2, h1.1]
    have hβ0 : β k t = 0 := by by_contra h; linarith [(hβ_supp k t h).1, h1.2]
    exact hne (by simp [hα0, hβ0])
  let ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x ↦ (β i (x.ofLp i) - α i (x.ofLp i)) * ∏ j ∈ Finset.univ.erase i, θ j (x.ofLp j)
  have hψ_abs : ∀ i x, |ψ i x| ≤ 1 := fun i x ↦ by
    dsimp only [ψ]; rw [abs_mul]
    have hprod_nonneg : 0 ≤ ∏ j ∈ Finset.univ.erase i, θ j (x.ofLp j) :=
      Finset.prod_nonneg fun j _ ↦ (θ j).nonneg
    have hprod_le : ∏ j ∈ Finset.univ.erase i, θ j (x.ofLp j) ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ ↦ (θ j).nonneg) (fun j _ ↦ (θ j).le_one)
    rw [abs_of_nonneg hprod_nonneg]
    nlinarith [hβα_abs i (x.ofLp i), abs_nonneg (β i (x.ofLp i) - α i (x.ofLp i))]
  have hψ_disj : ∀ {i₁ i₂ : Fin n}, i₁ ≠ i₂ → ∀ x, ψ i₁ x ≠ 0 → ψ i₂ x = 0 :=
    fun {i₁ i₂} hne x h1 ↦ by
      have hθ0 : θ i₁ (x.ofLp i₁) = 0 := hθ_zero_of_βα i₁ (x.ofLp i₁) (left_ne_zero_of_mul h1)
      dsimp only [ψ]
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩) hθ0, mul_zero]
  let φ₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x ↦ ∑ i : Fin n, ψ i x • EuclideanSpace.single i (1 : ℝ)
  have hφ₀_norm : ∀ x, ‖φ₀ x‖ ≤ 1 := fun x ↦ by
    by_cases hex : ∃ i, ψ i x ≠ 0
    · rcases hex with ⟨i, hi⟩
      have hsum : φ₀ x = ψ i x • EuclideanSpace.single i (1 : ℝ) :=
        Finset.sum_eq_single i (fun j _ hj ↦ by rw [hψ_disj hj.symm x hi, zero_smul]) (by simp)
      rw [hsum, norm_smul, Real.norm_eq_abs, EuclideanSpace.single, PiLp.norm_single, norm_one,
        mul_one]
      exact hψ_abs i x
    · push Not at hex; simp [φ₀, hex]
  have hproj_contDiff : ∀ (m : WithTop ℕ∞) (k : Fin n),
      ContDiff ℝ m (fun x : EuclideanSpace ℝ (Fin n) ↦ x.ofLp k) := fun m k ↦
    (contDiff_apply ℝ ℝ k).comp ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).contDiff)
  have hψ_contDiff : ∀ i : Fin n, ContDiff ℝ (⊤ : ℕ∞) (ψ i) := fun i ↦
    (((β i).contDiff.comp (hproj_contDiff (⊤ : ℕ∞) i)).sub
      ((α i).contDiff.comp (hproj_contDiff (⊤ : ℕ∞) i))).mul
      (contDiff_prod fun j _ ↦ (θ j).contDiff.comp (hproj_contDiff (⊤ : ℕ∞) j))
  have hφ₀_contDiff : ContDiff ℝ (⊤ : ℕ∞) φ₀ :=
    ContDiff.sum fun i _ ↦ (hψ_contDiff i).smul contDiff_const
  have hφ₀_compact : HasCompactSupport φ₀ := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_euclideanBox (fun k ↦ a k - δ) (fun k ↦ b k + δ)) fun x hx ↦ ?_
    rw [Function.mem_support] at hx
    have hex : ∃ i, ψ i x ≠ 0 := by
      by_contra h; push Not at h
      exact hx (Finset.sum_eq_zero fun i _ ↦ by rw [h i, zero_smul])
    rcases hex with ⟨i, hi⟩
    intro k
    by_cases hki : k = i
    · subst hki
      have hβα : β k (x.ofLp k) - α k (x.ofLp k) ≠ 0 := left_ne_zero_of_mul hi
      by_cases hαk : α k (x.ofLp k) = 0
      · have := hβ_supp k (x.ofLp k) (by rwa [hαk, sub_zero] at hβα)
        exact ⟨by linarith [hab k], by linarith⟩
      · have := hα_supp k (x.ofLp k) hαk
        exact ⟨by linarith, by linarith [hab k]⟩
    · have hprod : ∏ j ∈ Finset.univ.erase i, θ j (x.ofLp j) ≠ 0 := right_ne_zero_of_mul hi
      have hθk : θ k (x.ofLp k) ≠ 0 := fun h0 ↦
        hprod (Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hki, Finset.mem_univ _⟩) h0)
      have := hθ_supp k (x.ofLp k) hθk
      exact ⟨by linarith, by linarith⟩
  let φ : 𝓓(⊤, EuclideanSpace ℝ (Fin n)) :=
    ⟨φ₀, hφ₀_contDiff, hφ₀_compact, subset_univ _⟩
  rw [perimeter, relativePerimeter_eq_iSup_of_measurableSet (measurableSet_euclideanBox a b)]
  refine le_iSup₂_of_le φ hφ₀_norm (ENNReal.ofReal_le_ofReal ?_)
  rw [Opens.coe_top, inter_univ,
    integral_euclideanBox_divergence hab (φ.contDiff.of_le (by simp)), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hinner : ∀ y, ⟪EuclideanSpace.single i (1 : ℝ), φ y⟫_ℝ = ψ i y := fun y ↦ by
    change ⟪EuclideanSpace.single i (1 : ℝ),
      ∑ k : Fin n, ψ k y • EuclideanSpace.single k (1 : ℝ)⟫_ℝ = _
    simp [PiLp.inner_apply, Pi.single_apply]
  simp_rw [hinner]
  have hψ_slice : ∀ x' : {k : Fin n // k ≠ i} → ℝ,
      ψ i (boxSlice i x' (b i)) - ψ i (boxSlice i x' (a i)) =
        2 * ∏ j ∈ Finset.univ.erase i, θ j (boxSlice i x' 0 j) := fun x' ↦ by
    have hprod_eq : ∀ t, (∏ j ∈ Finset.univ.erase i, θ j ((boxSlice i x' t).ofLp j)) =
        ∏ j ∈ Finset.univ.erase i, θ j (boxSlice i x' 0 j) := fun t ↦
      Finset.prod_congr rfl fun j hj ↦ by
        have hne : j ≠ i := Finset.ne_of_mem_erase hj
        change θ j (boxSlice i x' t j) = θ j (boxSlice i x' 0 j)
        rw [boxSlice_apply_ne i x' t hne, boxSlice_apply_ne i x' 0 hne]
    dsimp only [ψ]
    rw [hprod_eq (b i), hprod_eq (a i)]
    change ((β i (boxSlice i x' (b i) i) - α i (boxSlice i x' (b i) i)) * _ -
      (β i (boxSlice i x' (a i) i) - α i (boxSlice i x' (a i) i)) * _) = _
    rw [boxSlice_apply_eq, boxSlice_apply_eq]
    have hβb : β i (b i) = 1 :=
      (β i).one_of_mem_closedBall (Metric.mem_closedBall_self (by dsimp [β]; linarith))
    have hαa : α i (a i) = 1 :=
      (α i).one_of_mem_closedBall (Metric.mem_closedBall_self (by dsimp [α]; linarith))
    have hαb : α i (b i) = 0 := by by_contra h; linarith [(hα_supp i (b i) h).2, habδ i]
    have hβa : β i (a i) = 0 := by by_contra h; linarith [(hβ_supp i (a i) h).1, habδ i]
    rw [hβb, hαa, hαb, hβa]; ring
  simp_rw [hψ_slice]
  let Face : Set ({k : Fin n // k ≠ i} → ℝ) :=
    Icc (fun j : {k : Fin n // k ≠ i} ↦ a j.1) (fun j ↦ b j.1)
  let Faceδ : Set ({k : Fin n // k ≠ i} → ℝ) :=
    Icc (fun j : {k : Fin n // k ≠ i} ↦ a j.1 + δ) (fun j ↦ b j.1 - δ)
  have hFaceδ_sub : Faceδ ⊆ Face := Icc_subset_Icc (fun j ↦ by linarith) (fun j ↦ by linarith)
  have hcont : Continuous (fun x' : {k : Fin n // k ≠ i} → ℝ ↦
      2 * ∏ j ∈ Finset.univ.erase i, θ j (boxSlice i x' 0 j)) := by
    have hc0 : Continuous (fun x' : {k : Fin n // k ≠ i} → ℝ ↦ boxSlice i x' 0) :=
      (continuous_boxSlice_uncurry i).comp (continuous_const.prodMk continuous_id)
    exact continuous_const.mul (continuous_finsetProd _ fun j _ ↦
      (θ j).continuous.comp ((hproj_contDiff ⊤ j).continuous.comp hc0))
  have hle1 : ∫ x' in Faceδ, (2 : ℝ) ≤
      ∫ x' in Faceδ, (2 * ∏ j ∈ Finset.univ.erase i, θ j (boxSlice i x' 0 j)) := by
    refine setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_lt_top.ne)
      (hcont.continuousOn.integrableOn_compact isCompact_Icc) isClosed_Icc.measurableSet
      fun x' hx' ↦ ?_
    have hprod1 : ∏ j ∈ Finset.univ.erase i, θ j (boxSlice i x' 0 j) = 1 := by
      refine Finset.prod_eq_one fun j hj ↦ ?_
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      rw [boxSlice_apply_ne i x' 0 hne]
      refine (θ j).one_of_mem_closedBall ?_
      rw [Real.closedBall_eq_Icc, mem_Icc]; dsimp [θ]
      exact ⟨by linarith [hx'.1 ⟨j, hne⟩], by linarith [hx'.2 ⟨j, hne⟩]⟩
    rw [hprod1, mul_one]
  have hle2 : ∫ x' in Faceδ, (2 * ∏ j ∈ Finset.univ.erase i, θ j (boxSlice i x' 0 j)) ≤
      ∫ x' in Face, (2 * ∏ j ∈ Finset.univ.erase i, θ j (boxSlice i x' 0 j)) :=
    setIntegral_mono_set (hcont.continuousOn.integrableOn_compact isCompact_Icc)
      (ae_of_all _ fun x' ↦ mul_nonneg zero_le_two (Finset.prod_nonneg fun j _ ↦ (θ j).nonneg))
      hFaceδ_sub.eventuallyLE
  refine le_trans ?_ (hle1.trans hle2)
  rw [setIntegral_const, Measure.real]
  dsimp only [Faceδ]
  rw [Real.volume_Icc_pi, ENNReal.toReal_prod, smul_eq_mul, mul_comm]
  refine le_of_eq ?_
  congr 1
  have hsub : ∀ j : {k : Fin n // k ≠ i}, b j.1 - δ - (a j.1 + δ) = b j.1 - a j.1 - 2 * δ :=
    fun j ↦ by ring
  simp_rw [hsub]
  rw [Finset.prod_congr rfl fun j _ ↦ ENNReal.toReal_ofReal (by linarith [habδ j.1])]
  exact Finset.prod_subtype (Finset.univ.erase i) (by simp) (fun j ↦ b j - a j - 2 * δ)

/-- **Lower bound on the perimeter of a non-degenerate `n`-dimensional Euclidean box**: for
`∀ i, a i < b i`, `perimeter volume (euclideanBox a b) ≥ 2 * ∑ i, ∏ j ≠ i, (b j - a j)`. -/
theorem perimeter_euclideanBox_ge {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    ENNReal.ofReal (2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j)) ≤
      perimeter volume (euclideanBox a b) := by
  let F : ℝ → ℝ≥0∞ := fun δ ↦
    ENNReal.ofReal (2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j - 2 * δ))
  have hF_cont : Continuous F :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul
      (continuous_finsetSum _ fun i _ ↦ continuous_finsetProd _ fun j _ ↦
        continuous_const.sub (continuous_const.mul continuous_id)))
  have hF0 : F 0 = ENNReal.ofReal (2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j)) := by
    simp [F]
  rw [← hF0]
  have hev_pos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := eventually_mem_nhdsWithin
  have hev_lt : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i : Fin n, 2 * δ < b i - a i := by
    rw [eventually_all]
    intro i
    have hcont_lin : Continuous (fun δ : ℝ ↦ 2 * δ) := continuous_const.mul continuous_id
    have h0 : 2 * (0 : ℝ) < b i - a i := by linarith [hab i]
    exact (hcont_lin.tendsto 0).eventually_lt_const h0 |>.filter_mono nhdsWithin_le_nhds
  exact le_of_tendsto (hF_cont.continuousWithinAt)
    (hev_pos.mp (hev_lt.mono fun δ hlt hpos ↦ perimeter_euclideanBox_ge_of_delta hpos hlt))

/-- **Exact perimeter of a closed `n`-dimensional Euclidean box**: for `∀ i, a i < b i`,
`perimeter volume (euclideanBox a b) = 2 * ∑ i, ∏ j ≠ i, (b j - a j)`. -/
theorem perimeter_euclideanBox {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    perimeter volume (euclideanBox a b) =
      ENNReal.ofReal (2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j)) :=
  le_antisymm (perimeter_euclideanBox_le fun i ↦ (hab i).le) (perimeter_euclideanBox_ge hab)

/-- **Exact perimeter of an open `n`-dimensional Euclidean box**: for `∀ i, a i < b i`,
`perimeter volume (euclideanOpenBox a b) = 2 * ∑ i, ∏ j ≠ i, (b j - a j)`. -/
theorem perimeter_euclideanOpenBox {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    perimeter volume (euclideanOpenBox a b) =
      ENNReal.ofReal (2 * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (b j - a j)) := by
  rw [perimeter_euclideanOpenBox_eq, perimeter_euclideanBox hab]

/-- The perimeter of any closed Euclidean box `euclideanBox a b` is finite (`< ⊤`). -/
theorem perimeter_euclideanBox_lt_top {n : ℕ} (a b : Fin n → ℝ) :
    perimeter volume (euclideanBox a b) < ⊤ := by
  by_cases hab : ∀ i, a i ≤ b i
  · exact (perimeter_euclideanBox_le hab).trans_lt ENNReal.ofReal_lt_top
  · push Not at hab
    rcases hab with ⟨i, hi⟩
    rw [perimeter_euclideanBox_eq_zero_of_le ⟨i, hi.le⟩]; exact ENNReal.zero_lt_top

/-- The perimeter of any open Euclidean box `euclideanOpenBox a b` is finite (`< ⊤`). -/
theorem perimeter_euclideanOpenBox_lt_top {n : ℕ} (a b : Fin n → ℝ) :
    perimeter volume (euclideanOpenBox a b) < ⊤ := by
  rw [perimeter_euclideanOpenBox_eq]; exact perimeter_euclideanBox_lt_top a b

/-- Every closed Euclidean box `euclideanBox a b` has finite perimeter in `ℝ^n`. -/
theorem hasFinitePerimeter_euclideanBox {n : ℕ} (a b : Fin n → ℝ) :
    HasFinitePerimeter volume (euclideanBox a b) :=
  ⟨(measurableSet_euclideanBox a b).nullMeasurableSet, perimeter_euclideanBox_lt_top a b⟩

/-- Every open Euclidean box `euclideanOpenBox a b` has finite perimeter in `ℝ^n`. -/
theorem hasFinitePerimeter_euclideanOpenBox {n : ℕ} (a b : Fin n → ℝ) :
    HasFinitePerimeter volume (euclideanOpenBox a b) :=
  ⟨(measurableSet_euclideanOpenBox a b).nullMeasurableSet, perimeter_euclideanOpenBox_lt_top a b⟩

/-- Every closed Euclidean box `euclideanBox a b` has finite relative perimeter in any open set
`Ω`. -/
theorem hasFinitePerimeterIn_euclideanBox {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (a b : Fin n → ℝ) :
    HasFinitePerimeterIn volume Ω (euclideanBox a b) :=
  ⟨(measurableSet_euclideanBox a b).nullMeasurableSet,
    (relativePerimeter_mono (le_top : Ω ≤ ⊤) (euclideanBox a b)).trans_lt
      (perimeter_euclideanBox_lt_top a b)⟩

/-- Every open Euclidean box `euclideanOpenBox a b` has finite relative perimeter in any open set
`Ω`. -/
theorem hasFinitePerimeterIn_euclideanOpenBox {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (a b : Fin n → ℝ) :
    HasFinitePerimeterIn volume Ω (euclideanOpenBox a b) :=
  ⟨(measurableSet_euclideanOpenBox a b).nullMeasurableSet,
    (relativePerimeter_mono (le_top : Ω ≤ ⊤) (euclideanOpenBox a b)).trans_lt
      (perimeter_euclideanOpenBox_lt_top a b)⟩

end TauCeti
