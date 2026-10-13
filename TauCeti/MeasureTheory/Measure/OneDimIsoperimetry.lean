/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import TauCeti.MeasureTheory.Measure.EssentialBoundary
public import TauCeti.MeasureTheory.Measure.IntervalPerimeter
public import TauCeti.MeasureTheory.Measure.PerimeterSlicing
public import TauCeti.Topology.Instances.CantorFunction
import all TauCeti.MeasureTheory.Measure.EssentialBoundary
import all TauCeti.MeasureTheory.Measure.Perimeter

/-!
# One-Dimensional Isoperimetric Inequality, BV Variation Formulas, and Interval Rigidity

This file develops the one-dimensional variational theory of functions of bounded variation and
sets of finite perimeter on `ℝ`, connecting distributional total variation with classical Jordan
variation, singular Cantor-type measures, and the sharp 1D isoperimetric inequality with its
interval equality characterization.

## Main definitions and results

* `TauCeti.normedBump`, `TauCeti.bumpCDF`, `TauCeti.telescopingBumpFun`,
  `TauCeti.telescopingTestFunction`, `TauCeti.bumpMollify`: smooth bump primitives and mollifiers.
* `TauCeti.ofReal_sum_mul_sub_le_distributionalVariation`,
  `ofReal_sum_abs_sub_le_distributionalVariation`: master telescoping variation lower bounds.
* `TauCeti.eVariationOn_Icc_le_distributionalVariation_Ioo`,
  `AbsolutelyContinuousOnInterval.distributionalVariation_Ioo_eq_eVariationOn`,
  `MonotoneOn.distributionalVariation_Ioo_eq`, `distributionalVariation_Ioo_cantorFunction`:
  classical vs. variational total variation on `ℝ` and total variation `1` of `cantorFunction`.
* `TauCeti.two_le_perimeter_of_volume_pos`, `exists_Ioo_ae_eq_of_perimeter_lt_four`,
  `perimeter_eq_two_iff_exists_Ioo_ae_eq`, `perimeter_eq_two_iff_exists_ordConnected_ae_eq`,
  `ae_exists_ordConnected_ae_eq_slice_of_lintegral_perimeter_le`: sharp 1D isoperimetric
  inequality, interval rigidity below perimeter `4`, and fiberwise slice rigidity on `X × ℝ`.
-/

@[expose] public section
noncomputable section
open Filter Function MeasureTheory Set TopologicalSpace TestFunction Metric TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology Distributions
namespace TauCeti
/-! ### Section 1: Normed Bump Primitives and Master Telescoping Variation Lower Bound -/
/-- Smooth bump function parameters centered at `0` with radii `δ / 2` and `δ`. -/
def zeroBump (δ : ℝ) : ContDiffBump (0 : ℝ) :=
  if h : 0 < δ then ⟨δ / 2, δ, half_pos h, half_lt_self h⟩ else ⟨1 / 2, 1, by norm_num, by norm_num⟩
lemma zeroBump_rIn {δ : ℝ} (hδ : 0 < δ) : (zeroBump δ).rIn = δ / 2 := by simp [zeroBump, hδ]
lemma zeroBump_rOut {δ : ℝ} (hδ : 0 < δ) : (zeroBump δ).rOut = δ := by simp [zeroBump, hδ]
/-- Normalized smooth bump function centered at `0` with support `(-δ, δ)` for `δ > 0`. -/
def normedBump (δ : ℝ) : ℝ → ℝ := (zeroBump δ).normed volume
lemma nonneg_normedBump (δ x : ℝ) : 0 ≤ normedBump δ x := (zeroBump δ).nonneg_normed x
lemma contDiff_normedBump (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (normedBump δ) :=
  (zeroBump δ).contDiff_normed
lemma continuous_normedBump (δ : ℝ) : Continuous (normedBump δ) := (zeroBump δ).continuous_normed
lemma integrable_normedBump (δ : ℝ) : Integrable (normedBump δ) volume :=
  (zeroBump δ).integrable_normed
@[simp] lemma integral_normedBump (δ : ℝ) : ∫ x, normedBump δ x = 1 := (zeroBump δ).integral_normed
lemma integrable_normedBump_sub (δ x₀ : ℝ) : Integrable (fun x ↦ normedBump δ (x - x₀)) volume :=
  (integrable_normedBump δ).comp_sub_right x₀
@[simp] lemma integral_normedBump_sub (δ x₀ : ℝ) : ∫ x, normedBump δ (x - x₀) = 1 := by
  rw [integral_sub_right_eq_self (normedBump δ) x₀, integral_normedBump]
lemma support_normedBump {δ : ℝ} (hδ : 0 < δ) : support (normedBump δ) = Ioo (-δ) δ := by
  rw [normedBump, (zeroBump δ).support_normed_eq, zeroBump_rOut hδ, Real.ball_eq_Ioo,
    zero_sub, zero_add]
lemma normedBump_eq_zero_of_notMem_Ioo {δ x : ℝ} (hδ : 0 < δ) (hx : x ∉ Ioo (-δ) δ) :
    normedBump δ x = 0 := by by_contra h; exact hx (support_normedBump hδ ▸ mem_support.2 h)
lemma normedBump_le_inv {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : normedBump δ x ≤ 1 / δ := by
  have h := (zeroBump δ).normed_le_div_measure_closedBall_rIn volume x
  rw [zeroBump_rIn hδ, Real.closedBall_eq_Icc, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)] at h; ring_nf at h ⊢; exact h
/-- Smooth cumulative distribution function `z ↦ ∫ t in (-δ)..z, normedBump δ t`. -/
def bumpCDF (δ z : ℝ) : ℝ := ∫ t in (-δ)..z, normedBump δ t
lemma hasDerivAt_bumpCDF (δ z : ℝ) : HasDerivAt (bumpCDF δ) (normedBump δ z) z :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_normedBump δ).intervalIntegrable (-δ) z)
    ((continuous_normedBump δ).stronglyMeasurableAtFilter _ _)
    (continuous_normedBump δ).continuousAt
lemma contDiff_bumpCDF (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (bumpCDF δ) := by
  have heq : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞) := rfl
  rw [← heq, contDiff_succ_iff_deriv]
  exact ⟨fun z ↦ (hasDerivAt_bumpCDF δ z).differentiableAt, by simp,
    (funext fun z ↦ (hasDerivAt_bumpCDF δ z).deriv).symm ▸ contDiff_normedBump δ⟩
lemma monotone_bumpCDF (δ : ℝ) : Monotone (bumpCDF δ) := fun z₁ z₂ hz ↦ by
  rw [← sub_nonneg, bumpCDF, bumpCDF, ← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_normedBump δ).intervalIntegrable (-δ) z₁)
    ((continuous_normedBump δ).intervalIntegrable z₁ z₂), add_sub_cancel_left]
  exact intervalIntegral.integral_nonneg hz fun t _ ↦ nonneg_normedBump δ t
lemma bumpCDF_eq_zero_of_le {δ z : ℝ} (hδ : 0 < δ) (hz : z ≤ -δ) : bumpCDF δ z = 0 := by
  rw [bumpCDF, intervalIntegral.integral_of_ge hz, setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦
    normedBump_eq_zero_of_notMem_Ioo hδ (fun h ↦ ht.2.not_gt h.1), neg_zero]
lemma bumpCDF_eq_one_of_ge {δ z : ℝ} (hδ : 0 < δ) (hz : δ ≤ z) : bumpCDF δ z = 1 := by
  rw [bumpCDF, intervalIntegral.integral_of_le (by linarith), ← integral_normedBump δ]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦
    normedBump_eq_zero_of_notMem_Ioo hδ fun ht_ioo ↦ ht ⟨ht_ioo.1, ht_ioo.2.le.trans hz⟩
lemma bumpCDF_nonneg {δ : ℝ} (hδ : 0 < δ) (z : ℝ) : 0 ≤ bumpCDF δ z :=
  (bumpCDF_eq_zero_of_le hδ (min_le_right z (-δ))).symm.trans_le
    (monotone_bumpCDF δ (min_le_left z (-δ)))
lemma bumpCDF_le_one {δ : ℝ} (hδ : 0 < δ) (z : ℝ) : bumpCDF δ z ≤ 1 :=
  (monotone_bumpCDF δ (le_max_left z δ)).trans_eq (bumpCDF_eq_one_of_ge hδ (le_max_right z δ))
/-- Telescoping linear combination of shifted `bumpCDF` functions. -/
def telescopingBumpFun (δ : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ) (σ : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin m, σ k * (bumpCDF δ (x - t k.succ) - bumpCDF δ (x - t k.castSucc))
lemma contDiff_telescopingBumpFun (δ : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ) (σ : Fin m → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (telescopingBumpFun δ t σ) :=
  ContDiff.sum fun _ _ ↦ contDiff_const.mul <|
    ((contDiff_bumpCDF δ).comp (contDiff_id.sub contDiff_const)).sub
      ((contDiff_bumpCDF δ).comp (contDiff_id.sub contDiff_const))
lemma hasDerivAt_bumpCDF_sub (δ c x : ℝ) :
    HasDerivAt (fun y ↦ bumpCDF δ (y - c)) (normedBump δ (x - c)) x := by
  have h := (hasDerivAt_bumpCDF δ (x - c)).comp x ((hasDerivAt_id x).sub_const c)
  rwa [mul_one] at h
lemma hasDerivAt_telescopingBumpFun (δ : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ) (σ : Fin m → ℝ)
    (x : ℝ) : HasDerivAt (telescopingBumpFun δ t σ)
      (∑ k : Fin m, σ k * (normedBump δ (x - t k.succ) - normedBump δ (x - t k.castSucc))) x :=
  HasDerivAt.fun_sum fun k _ ↦ ((hasDerivAt_bumpCDF_sub δ (t k.succ) x).sub
    (hasDerivAt_bumpCDF_sub δ (t k.castSucc) x)).const_mul (σ k)
lemma divergence_telescopingBumpFun (δ : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ) (σ : Fin m → ℝ)
    (x : ℝ) : divergence (telescopingBumpFun δ t σ) x =
      ∑ k : Fin m, σ k * (normedBump δ (x - t k.succ) - normedBump δ (x - t k.castSucc)) := by
  rw [divergence_eq_deriv, (hasDerivAt_telescopingBumpFun δ t σ x).deriv]
lemma norm_telescopingBumpFun_le_one {δ : ℝ} (hδ : 0 < δ) {m : ℕ} {t : Fin (m + 1) → ℝ}
    (ht : Monotone t) {σ : Fin m → ℝ} (hσ : ∀ k, |σ k| ≤ 1) (x : ℝ) :
    ‖telescopingBumpFun δ t σ x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, telescopingBumpFun]; have hterm : ∀ k : Fin m,
      |σ k * (bumpCDF δ (x - t k.succ) - bumpCDF δ (x - t k.castSucc))| ≤
        bumpCDF δ (x - t k.castSucc) - bumpCDF δ (x - t k.succ) := fun k ↦ by
    have hle := monotone_bumpCDF δ (sub_le_sub_left (ht (Fin.castSucc_le_succ k)) x)
    rw [abs_mul, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
    exact mul_le_of_le_one_left (sub_nonneg.2 hle) (hσ k)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ ↦ hterm k).trans ?_)
  have h1 := Fin.sum_univ_castSucc fun j ↦ bumpCDF δ (x - t j)
  have h2 := Fin.sum_univ_succ fun j ↦ bumpCDF δ (x - t j); rw [Finset.sum_sub_distrib]
  linarith [bumpCDF_le_one hδ (x - t 0), bumpCDF_nonneg hδ (x - t (Fin.last m))]
lemma tsupport_telescopingBumpFun_subset {δ : ℝ} (hδ : 0 < δ) {m : ℕ} {t : Fin (m + 1) → ℝ}
    (ht : Monotone t) (σ : Fin m → ℝ) :
    tsupport (telescopingBumpFun δ t σ) ⊆ Icc (t 0 - δ) (t (Fin.last m) + δ) := by
  refine closure_minimal (fun x hx ↦ ?_) isClosed_Icc; rw [mem_support] at hx
  refine ⟨by_contra fun hlt ↦ hx (Finset.sum_eq_zero fun k _ ↦ ?_),
    by_contra fun hgt ↦ hx (Finset.sum_eq_zero fun k _ ↦ ?_)⟩
  · have h0 := ht (Fin.zero_le k.castSucc); have h1 := ht (Fin.castSucc_le_succ k)
    rw [bumpCDF_eq_zero_of_le hδ (by linarith), bumpCDF_eq_zero_of_le hδ (by linarith),
      sub_self, mul_zero]
  · have h1 := ht (Fin.castSucc_le_succ k); have hlast := ht (Fin.le_last k.succ)
    rw [bumpCDF_eq_one_of_ge hδ (by linarith), bumpCDF_eq_one_of_ge hδ (by linarith),
      sub_self, mul_zero]
/-- Bundled telescoping test function in `𝓓(Ω, ℝ)`. -/
def telescopingTestFunction {Ω : Opens ℝ} {δ : ℝ} (hδ : 0 < δ) {m : ℕ}
    {t : Fin (m + 1) → ℝ} (ht : Monotone t)
    (hsub : Icc (t 0 - δ) (t (Fin.last m) + δ) ⊆ (Ω : Set ℝ)) (σ : Fin m → ℝ) : 𝓓(Ω, ℝ) where
  toFun := telescopingBumpFun δ t σ
  contDiff' := contDiff_telescopingBumpFun δ t σ
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans (tsupport_telescopingBumpFun_subset hδ ht σ))
  tsupport_subset' := (tsupport_telescopingBumpFun_subset hδ ht σ).trans hsub
@[simp] lemma coe_telescopingTestFunction {Ω : Opens ℝ} {δ : ℝ} (hδ : 0 < δ) {m : ℕ}
    {t : Fin (m + 1) → ℝ} (ht : Monotone t)
    (hsub : Icc (t 0 - δ) (t (Fin.last m) + δ) ⊆ (Ω : Set ℝ)) (σ : Fin m → ℝ) :
    (telescopingTestFunction hδ ht hsub σ : ℝ → ℝ) = telescopingBumpFun δ t σ := rfl
lemma tsupport_shifted_normedBump_subset {x₀ δ : ℝ} (hδ : 0 < δ) :
    tsupport (fun x ↦ normedBump δ (x - x₀)) ⊆ Icc (x₀ - δ) (x₀ + δ) :=
  closure_minimal (fun _ hx ↦ ⟨by linarith [(support_normedBump hδ ▸ mem_support.2 hx).1],
    by linarith [(support_normedBump hδ ▸ mem_support.2 hx).2]⟩) isClosed_Icc
/-- Bundled shifted bump test function in `𝓓(Ω, ℝ)`. -/
def shiftedNormedBumpTestFunction {Ω : Opens ℝ} {x₀ δ : ℝ} (hδ : 0 < δ)
    (hsub : Icc (x₀ - δ) (x₀ + δ) ⊆ (Ω : Set ℝ)) : 𝓓(Ω, ℝ) where
  toFun x := normedBump δ (x - x₀)
  contDiff' := (contDiff_normedBump δ).comp (contDiff_id.sub contDiff_const)
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans (tsupport_shifted_normedBump_subset hδ))
  tsupport_subset' := (tsupport_shifted_normedBump_subset hδ).trans hsub
/-- Mollified evaluation `∫ x, u x * normedBump δ (x - x₀)` of `u` around `x₀` at scale `δ`. -/
def bumpMollify (u : ℝ → ℝ) (x₀ δ : ℝ) : ℝ := ∫ x, u x * normedBump δ (x - x₀)
lemma integrable_mul_shifted_normedBump {Ω : Opens ℝ} {u : ℝ → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) {x₀ δ : ℝ} (hδ : 0 < δ)
    (hsub : Icc (x₀ - δ) (x₀ + δ) ⊆ (Ω : Set ℝ)) :
    Integrable (fun x ↦ u x * normedBump δ (x - x₀)) volume := by
  simpa [shiftedNormedBumpTestFunction, smul_eq_mul, mul_comm] using
    integrable_smul_of_locallyIntegrableOn hu (shiftedNormedBumpTestFunction hδ hsub)
lemma setIntegral_mul_shifted_normedBump_eq_bumpMollify {Ω : Opens ℝ} (u : ℝ → ℝ)
    {x₀ δ : ℝ} (hδ : 0 < δ) (hsub : Icc (x₀ - δ) (x₀ + δ) ⊆ (Ω : Set ℝ)) :
    ∫ x in (Ω : Set ℝ), u x * normedBump δ (x - x₀) = bumpMollify u x₀ δ :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx ↦ by
    rw [normedBump_eq_zero_of_notMem_Ioo hδ fun h ↦
      hx (hsub ⟨by linarith [h.1], by linarith [h.2]⟩), mul_zero]
lemma integral_mul_divergence_telescopingTestFunction {Ω : Opens ℝ} {u : ℝ → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) {δ : ℝ} (hδ : 0 < δ) {m : ℕ}
    {t : Fin (m + 1) → ℝ} (ht : Monotone t)
    (hsub : Icc (t 0 - δ) (t (Fin.last m) + δ) ⊆ (Ω : Set ℝ)) (σ : Fin m → ℝ) :
    ∫ x in (Ω : Set ℝ),
        u x * divergence (telescopingTestFunction hδ ht hsub σ : ℝ → ℝ) x =
      ∑ k : Fin m, σ k * (bumpMollify u (t k.succ) δ - bumpMollify u (t k.castSucc) δ) := by
  simp_rw [coe_telescopingTestFunction, divergence_telescopingBumpFun, Finset.mul_sum]
  have hsh : ∀ j : Fin (m + 1), Icc (t j - δ) (t j + δ) ⊆ (Ω : Set ℝ) := fun j x hx ↦
    hsub ⟨by linarith [ht (Fin.zero_le j), hx.1], by linarith [ht (Fin.le_last j), hx.2]⟩
  have hint : ∀ j, IntegrableOn (fun x ↦ u x * normedBump δ (x - t j)) Ω volume := fun j ↦
    (integrable_mul_shifted_normedBump hu hδ (hsh j)).integrableOn
  rw [integral_finsetSum _ fun k _ ↦ IntegrableOn.congr_fun
    (((hint k.succ).sub (hint k.castSucc)).const_mul (σ k))
    (fun x _ ↦ by dsimp; ring) Ω.isOpen.measurableSet]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have heq : (fun x ↦ u x * (σ k * (normedBump δ (x - t k.succ) -
        normedBump δ (x - t k.castSucc)))) = fun x ↦
      σ k * (u x * normedBump δ (x - t k.succ) - u x * normedBump δ (x - t k.castSucc)) := by
    ext x; ring
  rw [heq, integral_const_mul, integral_sub (hint k.succ) (hint k.castSucc),
    setIntegral_mul_shifted_normedBump_eq_bumpMollify u hδ (hsh k.succ),
    setIntegral_mul_shifted_normedBump_eq_bumpMollify u hδ (hsh k.castSucc)]
/-- At any continuity point `x₀ ∈ Ω` of `u`, `bumpMollify u x₀ δ → u x₀` as `δ → 0⁺`. -/
theorem tendsto_bumpMollify_of_continuousAt {Ω : Opens ℝ} {u : ℝ → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) {x₀ : ℝ} (hx₀ : x₀ ∈ Ω) (hcont : ContinuousAt u x₀) :
    Tendsto (bumpMollify u x₀) (𝓝[>] 0) (𝓝 (u x₀)) := by
  rw [Metric.tendsto_nhds]; intro ε hε
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hx₀) with ⟨r₁, hr₁, hsub₁⟩
  rcases Metric.continuousAt_iff.mp hcont (ε / 2) (half_pos hε) with ⟨r₂, hr₂, hclose⟩
  filter_upwards [Ioo_mem_nhdsGT (lt_min hr₁ hr₂)] with δ ⟨hδ, hδ_lt⟩
  have hsub : Icc (x₀ - δ) (x₀ + δ) ⊆ (Ω : Set ℝ) := by
    rw [← Real.closedBall_eq_Icc]
    exact (closedBall_subset_closedBall (hδ_lt.le.trans (min_le_left _ _))).trans hsub₁
  have hdiff : bumpMollify u x₀ δ - u x₀ = ∫ x, (u x - u x₀) * normedBump δ (x - x₀) := by
    calc bumpMollify u x₀ δ - u x₀
        = (∫ x, u x * normedBump δ (x - x₀)) - ∫ x, u x₀ * normedBump δ (x - x₀) := by
          rw [integral_const_mul, integral_normedBump_sub, mul_one]; rfl
      _ = ∫ x, (u x - u x₀) * normedBump δ (x - x₀) := by
          rw [← integral_sub (integrable_mul_shifted_normedBump hu hδ hsub)
            ((integrable_normedBump_sub δ x₀).const_mul (u x₀))]
          congr 1; ext x; ring
  rw [Real.dist_eq, hdiff, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((integrable_normedBump_sub δ x₀).const_mul (ε / 2))
    (Eventually.of_forall fun x ↦ ?_)).trans_lt ?_
  · rw [norm_mul, Real.norm_of_nonneg (nonneg_normedBump δ _)]
    by_cases hx : x - x₀ ∈ Ioo (-δ) δ
    · refine mul_le_mul_of_nonneg_right (le_of_lt (hclose ?_)) (nonneg_normedBump δ _)
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1, min_le_right r₁ r₂], by linarith [hx.2, min_le_right r₁ r₂]⟩
    · rw [normedBump_eq_zero_of_notMem_Ioo hδ hx, mul_zero, mul_zero]
  · rw [integral_const_mul, integral_normedBump_sub, mul_one]; exact half_lt_self hε
/-- At `x₀ ∈ essentialExterior volume s`, `bumpMollify (s.indicator 1) x₀ δ → 0` as `δ → 0⁺`. -/
theorem tendsto_bumpMollify_indicator_zero {s : Set ℝ} {x₀ : ℝ}
    (hx₀ : x₀ ∈ essentialExterior volume s) :
    Tendsto (bumpMollify (s.indicator fun _ ↦ (1 : ℝ)) x₀) (𝓝[>] 0) (𝓝 0) := by
  have hratio : Tendsto (fun δ : ℝ ↦ 2 * (volume (s ∩ Metric.closedBall x₀ δ) /
      volume (Metric.closedBall x₀ δ)).toReal) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hx₀).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hratio ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ _
    exact integral_nonneg fun x ↦ mul_nonneg (indicator_nonneg (fun _ _ ↦ zero_le_one) x)
      (nonneg_normedBump δ _)
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    have hle2 : (∫⁻ x, ENNReal.ofReal ‖s.indicator (fun _ ↦ (1 : ℝ)) x * normedBump δ (x - x₀)‖) ≤
        ENNReal.ofReal (1 / δ) * volume (s ∩ Metric.closedBall x₀ δ) := by
      refine (lintegral_mono fun x ↦ ?_).trans
        (lintegral_indicator_const_le (s ∩ Metric.closedBall x₀ δ) (ENNReal.ofReal (1 / δ)))
      by_cases hcb : x ∈ Metric.closedBall x₀ δ
      · by_cases hxs : x ∈ s
        · simp only [mem_inter_iff, hxs, hcb, and_self, indicator_of_mem, one_mul,
            Real.norm_of_nonneg (nonneg_normedBump δ _)]
          exact ENNReal.ofReal_le_ofReal (normedBump_le_inv hδ _)
        · simp [hxs]
      · have hx_not : x - x₀ ∉ Ioo (-δ) δ := fun h ↦ hcb (by
          rw [Real.closedBall_eq_Icc]; exact ⟨by linarith [h.1], by linarith [h.2]⟩)
        simp [hcb, normedBump_eq_zero_of_notMem_Ioo hδ hx_not]
    have hvol_cb : volume (Metric.closedBall x₀ δ) = ENNReal.ofReal (2 * δ) := by
      rw [Real.closedBall_eq_Icc, Real.volume_Icc]; ring_nf
    have htop : ENNReal.ofReal (1 / δ) * volume (s ∩ Metric.closedBall x₀ δ) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ((measure_mono inter_subset_right).trans_lt (hvol_cb ▸ ENNReal.ofReal_lt_top)).ne
    refine ((Real.le_norm_self _).trans (norm_integral_le_lintegral_norm _)).trans
      ((ENNReal.toReal_mono htop hle2).trans_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, hvol_cb,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]; ring
lemma locallyIntegrableOn_top_indicator_one {s : Set ℝ} (hs : NullMeasurableSet s volume) :
    LocallyIntegrableOn (s.indicator fun _ ↦ (1 : ℝ)) (⊤ : Opens ℝ) volume :=
  locallyIntegrableOn_indicator_const (by rw [Opens.coe_top, Measure.restrict_univ]; exact hs) 1
/-- At `x₀ ∈ essentialInterior volume s`, `bumpMollify (s.indicator 1) x₀ δ → 1` as `δ → 0⁺`. -/
theorem tendsto_bumpMollify_indicator_one {s : Set ℝ} (hs : NullMeasurableSet s volume)
    {x₀ : ℝ} (hx₀ : x₀ ∈ essentialInterior volume s) :
    Tendsto (bumpMollify (s.indicator fun _ ↦ (1 : ℝ)) x₀) (𝓝[>] 0) (𝓝 1) := by
  have hx₀' : x₀ ∈ essentialExterior volume sᶜ := by rwa [essentialExterior_compl hs]
  have hsub := tendsto_const_nhds.sub (tendsto_bumpMollify_indicator_zero hx₀') (a := (1 : ℝ))
  rw [sub_zero] at hsub; refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  have h1 := integrable_mul_shifted_normedBump (x₀ := x₀)
    (locallyIntegrableOn_top_indicator_one hs) hδ (subset_univ _)
  have h2 := integrable_mul_shifted_normedBump (x₀ := x₀)
    (locallyIntegrableOn_top_indicator_one hs.compl) hδ (subset_univ _)
  have hsum : bumpMollify (s.indicator fun _ ↦ (1 : ℝ)) x₀ δ +
      bumpMollify (sᶜ.indicator fun _ ↦ (1 : ℝ)) x₀ δ = ∫ x, normedBump δ (x - x₀) := by
    dsimp [bumpMollify]; rw [← integral_add h1 h2]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by by_cases hxs : x ∈ s <;> simp [hxs])
  rw [integral_normedBump_sub] at hsum; linarith
/-- **Master telescoping lower bound on `distributionalVariation`**. -/
theorem ofReal_sum_mul_sub_le_distributionalVariation
    {Ω : Opens ℝ} {u : ℝ → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : Monotone t)
    (hsub : Icc (t 0) (t (Fin.last m)) ⊆ (Ω : Set ℝ)) {val : Fin (m + 1) → ℝ}
    (hlim : ∀ j : Fin (m + 1), Tendsto (bumpMollify u (t j)) (𝓝[>] 0) (𝓝 (val j)))
    {σ : Fin m → ℝ} (hσ : ∀ k : Fin m, |σ k| ≤ 1) :
    ENNReal.ofReal (∑ k : Fin m, σ k * (val k.succ - val k.castSucc)) ≤
      distributionalVariation volume Ω u := by
  obtain ⟨r, hr, hthick⟩ := isCompact_Icc.exists_thickening_subset_open Ω.isOpen hsub
  refine le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp <|
    tendsto_finsetSum _ fun k _ ↦ ((hlim k.succ).sub (hlim k.castSucc)).const_mul (σ k)) ?_
  filter_upwards [Ioo_mem_nhdsGT (half_pos hr)] with δ ⟨hδ, hδ_lt⟩
  have hsub_δ : Icc (t 0 - δ) (t (Fin.last m) + δ) ⊆ (Ω : Set ℝ) := fun x hx ↦ by
    let y := min (max x (t 0)) (t (Fin.last m)); refine hthick (mem_thickening_iff.2
      ⟨y, ⟨le_min (le_max_right _ _) (ht (Fin.zero_le _)), min_le_right _ _⟩, ?_⟩)
    have hy1 : x - δ ≤ y := le_min (by linarith [le_max_left x (t 0)]) (by linarith [hx.2])
    have hy2 : y ≤ x + δ := min_le_of_left_le (max_le (by linarith) (by linarith [hx.1]))
    rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩
  dsimp only [Function.comp_apply]
  rw [← integral_mul_divergence_telescopingTestFunction hu hδ ht hsub_δ σ]
  exact le_distributionalVariation (telescopingTestFunction hδ ht hsub_δ σ)
    (norm_telescopingBumpFun_le_one hδ ht hσ) u
/-- **Master absolute-value telescoping lower bound on `distributionalVariation`**. -/
theorem ofReal_sum_abs_sub_le_distributionalVariation
    {Ω : Opens ℝ} {u : ℝ → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : Monotone t)
    (hsub : Icc (t 0) (t (Fin.last m)) ⊆ (Ω : Set ℝ)) {val : Fin (m + 1) → ℝ}
    (hlim : ∀ j : Fin (m + 1), Tendsto (bumpMollify u (t j)) (𝓝[>] 0) (𝓝 (val j))) :
    ENNReal.ofReal (∑ k : Fin m, |val k.succ - val k.castSucc|) ≤
      distributionalVariation volume Ω u := by
  let σ : Fin m → ℝ := fun k ↦ if 0 ≤ val k.succ - val k.castSucc then 1 else -1
  have h_eq : (∑ k : Fin m, |val k.succ - val k.castSucc|) =
      ∑ k : Fin m, σ k * (val k.succ - val k.castSucc) :=
    Finset.sum_congr rfl fun k _ ↦ by
      dsimp [σ]; split_ifs with h <;>
        [rw [one_mul, abs_of_nonneg h]; rw [neg_one_mul, abs_of_neg (not_le.1 h)]]
  rw [h_eq]; exact ofReal_sum_mul_sub_le_distributionalVariation hu ht hsub hlim
    fun k ↦ by dsimp [σ]; split_ifs <;> simp
/-! ### Section 2: Classical vs. Variational Total Variation and the Cantor–Lebesgue Function -/
/-- Sum of absolute differences along a monotone partition in `Ω` is bounded by variation. -/
theorem ofReal_sum_abs_sub_le_distributionalVariation_of_continuousOn
    {Ω : Opens ℝ} {u : ℝ → ℝ} (hcont : ContinuousOn u Ω) {m : ℕ} {t : Fin (m + 1) → ℝ}
    (ht : Monotone t) (hsub : Icc (t 0) (t (Fin.last m)) ⊆ (Ω : Set ℝ)) :
    ENNReal.ofReal (∑ k : Fin m, |u (t k.succ) - u (t k.castSucc)|) ≤
      distributionalVariation volume Ω u := by
  have hu : LocallyIntegrableOn u Ω volume := hcont.locallyIntegrableOn Ω.isOpen.measurableSet
  refine ofReal_sum_abs_sub_le_distributionalVariation (val := fun j ↦ u (t j))
    hu ht hsub fun j ↦ ?_
  have htj : t j ∈ (Ω : Set ℝ) := hsub ⟨ht (Fin.zero_le j), ht (Fin.le_last j)⟩
  exact tendsto_bumpMollify_of_continuousAt hu htj (hcont.continuousAt (Ω.isOpen.mem_nhds htj))
/-- Two-point oscillation bound on `distributionalVariation volume Ω u` when `Icc x₀ x₁ ⊆ Ω`. -/
theorem ofReal_abs_sub_le_distributionalVariation_of_Icc_subset {Ω : Opens ℝ} {u : ℝ → ℝ}
    (hcont : ContinuousOn u Ω) {x₀ x₁ : ℝ} (hle : x₀ ≤ x₁) (hsub : Icc x₀ x₁ ⊆ (Ω : Set ℝ)) :
    ENNReal.ofReal |u x₁ - u x₀| ≤ distributionalVariation volume Ω u := by
  let t : Fin 2 → ℝ := ![x₀, x₁]
  have ht : Monotone t := Fin.monotone_iff_le_succ.2 fun k ↦ by fin_cases k; simpa [t] using hle
  simpa [t] using ofReal_sum_abs_sub_le_distributionalVariation_of_continuousOn hcont ht hsub
/-- Two-point oscillation bound on `Opens.Ioo a b`. -/
theorem ofReal_abs_sub_le_distributionalVariation_Ioo {a b : ℝ} {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Ioo a b)) {x₀ x₁ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hx₁ : x₁ ∈ Ioo a b) :
    ENNReal.ofReal |u x₁ - u x₀| ≤ distributionalVariation volume (Opens.Ioo a b) u := by
  rcases le_total x₀ x₁ with h | h
  · exact ofReal_abs_sub_le_distributionalVariation_of_Icc_subset hcont h
      (Icc_subset_Ioo hx₀.1 hx₁.2)
  · rw [abs_sub_comm]; exact ofReal_abs_sub_le_distributionalVariation_of_Icc_subset hcont h
      (Icc_subset_Ioo hx₁.1 hx₀.2)
/-- Two-point oscillation bound on `ℝ` (`⊤ : Opens ℝ`). -/
theorem ofReal_abs_sub_le_distributionalVariation_top {u : ℝ → ℝ} (hcont : Continuous u)
    (x₀ x₁ : ℝ) :
    ENNReal.ofReal |u x₁ - u x₀| ≤ distributionalVariation volume (⊤ : Opens ℝ) u := by
  rcases le_total x₀ x₁ with h | h
  · exact ofReal_abs_sub_le_distributionalVariation_of_Icc_subset hcont.continuousOn h
      (subset_univ _)
  · rw [abs_sub_comm]; exact ofReal_abs_sub_le_distributionalVariation_of_Icc_subset
      hcont.continuousOn h (subset_univ _)
/-- A continuous function on `Ioo a b` with zero distributional variation is constant. -/
theorem eq_of_distributionalVariation_Ioo_eq_zero {a b : ℝ} {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Ioo a b)) (h0 : distributionalVariation volume (Opens.Ioo a b) u = 0)
    {x₀ x₁ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hx₁ : x₁ ∈ Ioo a b) : u x₀ = u x₁ := by
  have hle := (ofReal_abs_sub_le_distributionalVariation_Ioo hcont hx₁ hx₀).trans_eq h0
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (ENNReal.ofReal_eq_zero.mp (nonpos_iff_eq_zero.mp hle)))
/-- A continuous function on `ℝ` with zero distributional variation is constant. -/
theorem eq_of_distributionalVariation_top_eq_zero {u : ℝ → ℝ} (hcont : Continuous u)
    (h0 : distributionalVariation volume (⊤ : Opens ℝ) u = 0) (x₀ x₁ : ℝ) : u x₀ = u x₁ := by
  have hle := (ofReal_abs_sub_le_distributionalVariation_top hcont x₁ x₀).trans_eq h0
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (ENNReal.ofReal_eq_zero.mp (nonpos_iff_eq_zero.mp hle)))
lemma sum_range_edist_eq_ofReal_sum (u : ℝ → ℝ) (m : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range m, edist (u (f (i + 1))) (u (f i))) =
      ENNReal.ofReal (∑ k : Fin m, |u (f k.succ) - u (f k.castSucc)|) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ edist (u (f (i + 1))) (u (f i))) m,
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _]
  exact Finset.sum_congr rfl fun k _ ↦ by simp [edist_dist, Real.dist_eq]
/-- Classical Jordan variation on an order-connected set `s ⊆ Ω` is bounded by variation. -/
theorem eVariationOn_le_distributionalVariation_of_ordConnected {Ω : Opens ℝ} {s : Set ℝ}
    (hs_ord : s.OrdConnected) (hs_sub : s ⊆ (Ω : Set ℝ)) {u : ℝ → ℝ} (hcont : ContinuousOn u Ω) :
    eVariationOn u s ≤ distributionalVariation volume Ω u :=
  iSup_le fun p ↦ (sum_range_edist_eq_ofReal_sum u p.1 p.2.1).trans_le <|
    ofReal_sum_abs_sub_le_distributionalVariation_of_continuousOn hcont
      (fun _ _ hij ↦ p.2.2.1 hij) ((hs_ord.out (p.2.2.2 0) (p.2.2.2 p.1)).trans hs_sub)
/-- Classical Jordan variation on `Ioo a b` is bounded by `distributionalVariation`. -/
theorem eVariationOn_Ioo_le_distributionalVariation_Ioo {a b : ℝ} {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Ioo a b)) :
    eVariationOn u (Ioo a b) ≤ distributionalVariation volume (Opens.Ioo a b) u :=
  eVariationOn_le_distributionalVariation_of_ordConnected ordConnected_Ioo Subset.rfl hcont
/-- Classical Jordan variation on `univ` is bounded by `distributionalVariation` on `⊤`. -/
theorem eVariationOn_univ_le_distributionalVariation_top {u : ℝ → ℝ} (hcont : Continuous u) :
    eVariationOn u univ ≤ distributionalVariation volume (⊤ : Opens ℝ) u :=
  eVariationOn_le_distributionalVariation_of_ordConnected ordConnected_univ (subset_univ _)
    hcont.continuousOn
/-- Classical Jordan variation on `Icc a b` is bounded by `distributionalVariation` on `Ioo a b`. -/
theorem eVariationOn_Icc_le_distributionalVariation_Ioo {a b : ℝ} {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc a b)) :
    eVariationOn u (Icc a b) ≤ distributionalVariation volume (Opens.Ioo a b) u := by
  refine iSup_le fun p ↦ ?_; let m := p.1; let t : Fin (m + 1) → ℝ := fun j ↦ p.2.1 j
  have ht : Monotone t := fun _ _ hij ↦ p.2.2.1 hij
  have ht_mem : ∀ j, t j ∈ Icc a b := fun j ↦ p.2.2.2 j
  have hsum : (∑ i ∈ Finset.range m, edist (u (p.2.1 (i + 1))) (u (p.2.1 i))) =
      ENNReal.ofReal (∑ k : Fin m, |u (t k.succ) - u (t k.castSucc)|) :=
    sum_range_edist_eq_ofReal_sum u m p.2.1
  rw [hsum]; rcases ((ht_mem 0).1.trans (ht_mem 0).2).eq_or_lt with rfl | hlt
  · have hconst : ∀ k : Fin m, |u (t k.succ) - u (t k.castSucc)| = 0 := fun k ↦ by
      rw [le_antisymm (ht_mem k.succ).2 (ht_mem k.succ).1,
        le_antisymm (ht_mem k.castSucc).2 (ht_mem k.castSucc).1, sub_self, abs_zero]
    simp [hconst]
  · let tr : ℝ → Fin (m + 1) → ℝ := fun r j ↦ max (a + r) (min (b - r) (t j))
    have htr_tend : ∀ j, Tendsto (fun r ↦ u (tr r j)) (𝓝[>] 0) (𝓝 (u (t j))) := fun j ↦ by
      have hc : Continuous fun r : ℝ ↦ tr r j := by dsimp [tr]; fun_prop
      have h0 : tr 0 j = t j := by
        dsimp [tr]; rw [add_zero, sub_zero, min_eq_right (ht_mem j).2, max_eq_right (ht_mem j).1]
      refine (hcont (t j) (ht_mem j)).tendsto.comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (h0 ▸ hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_)
      filter_upwards [Ioo_mem_nhdsGT (half_pos (sub_pos.2 hlt))] with r ⟨hr, hr_lt⟩
      exact ⟨le_trans (by linarith) (le_max_left _ _),
        max_le (by linarith) ((min_le_left _ _).trans (by linarith))⟩
    refine le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp <|
      tendsto_finsetSum _ fun k _ ↦ ((htr_tend k.succ).sub (htr_tend k.castSucc)).abs) ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos (sub_pos.2 hlt))] with r ⟨hr, hr_lt⟩
    have htr_mono : Monotone (tr r) := fun _ _ hij ↦
      max_le_max_left _ (min_le_min_left _ (ht hij))
    have htr_sub : Icc (tr r 0) (tr r (Fin.last m)) ⊆ (Opens.Ioo a b : Set ℝ) := fun x hx ↦ by
      have h0 : a + r ≤ tr r 0 := le_max_left _ _
      have hlast : tr r (Fin.last m) ≤ b - r := max_le (by linarith) (min_le_left _ _)
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact ofReal_sum_abs_sub_le_distributionalVariation_of_continuousOn
      (hcont.mono Ioo_subset_Icc_self) htr_mono htr_sub
/-- Variational total variation equals classical Jordan variation for AC functions on `[a, b]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.distributionalVariation_Ioo_eq_eVariationOn
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    distributionalVariation volume (Opens.Ioo a b) f = eVariationOn f (Icc a b) :=
  le_antisymm (hf.distributionalVariation_Ioo_le_eVariationOn hab)
    (eVariationOn_Icc_le_distributionalVariation_Ioo (uIcc_of_le hab ▸ hf.continuousOn))
/-- Variational total variation equals `∫⁻ x in Ioo a b, ‖deriv f x‖ₑ` for AC functions. -/
theorem _root_.AbsolutelyContinuousOnInterval.distributionalVariation_Ioo_eq_lintegral_enorm_deriv
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    distributionalVariation volume (Opens.Ioo a b) f = ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ :=
  le_antisymm (hf.distributionalVariation_Ioo_le hab)
    ((hf.lintegral_enorm_deriv_le_eVariationOn hab).trans
      (hf.distributionalVariation_Ioo_eq_eVariationOn hab).ge)
/-- Classical Jordan variation equals `∫⁻ x in Ioo a b, ‖deriv f x‖ₑ` for AC functions. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_Icc_eq_lintegral_enorm_deriv
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    eVariationOn f (Icc a b) = ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ := by
  rw [← hf.distributionalVariation_Ioo_eq_eVariationOn hab,
    hf.distributionalVariation_Ioo_eq_lintegral_enorm_deriv hab]
lemma relativePerimeter_Ioo_lt_le_one_of_monotoneOn {a b : ℝ} {u : ℝ → ℝ}
    (hmono : MonotoneOn u (Icc a b)) (t : ℝ) :
    relativePerimeter volume (Opens.Ioo a b) {x | t < u x} ≤ 1 := by
  classical
  let S := {x ∈ Ioo a b | t < u x}
  have h_ae_S : ({x | t < u x} : Set ℝ) =ᵐ[volume.restrict (Opens.Ioo a b : Set ℝ)] S := by
    change ∀ᵐ x ∂volume.restrict (Ioo a b), (x ∈ {x | t < u x}) = (x ∈ S)
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun x hx ↦ propext ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩
  rw [relativePerimeter_congr_ae h_ae_S]; rcases S.eq_empty_or_nonempty with hEmpty | hNonempty
  · rw [hEmpty, relativePerimeter_empty]; exact zero_le_one
  · let c := sInf S
    have hbdd : BddBelow S := ⟨a, fun x hx ↦ hx.1.1.le⟩; have hcb : c < b := by
      rcases hNonempty with ⟨x₀, hx₀⟩; exact (csInf_le hbdd hx₀).trans_lt hx₀.1.2
    have hsub1 : Ioo c b ⊆ S := fun x hx ↦ by
      obtain ⟨y, hyS, hyx⟩ := exists_lt_of_csInf_lt hNonempty hx.1
      have hx_ioo : x ∈ Ioo a b := ⟨hyS.1.1.trans hyx, hx.2⟩; exact ⟨hx_ioo, hyS.2.trans_le
        (hmono (Ioo_subset_Icc_self hyS.1) (Ioo_subset_Icc_self hx_ioo) hyx.le)⟩
    have hsub2 : S ⊆ Ico c b := fun x hx ↦ ⟨csInf_le hbdd hx, hx.1.2⟩
    have hS_ae : S =ᵐ[volume] Ioo c b :=
      EventuallyLE.antisymm ((LE.le.eventuallySubset hsub2).trans Ioo_ae_eq_Ico.symm.le)
        (LE.le.eventuallySubset hsub1)
    rw [relativePerimeter_congr_ae (ae_restrict_of_ae hS_ae),
      relativePerimeter_Ioo (Opens.Ioo a b) hcb]
    have hb_not : b ∉ Opens.Ioo a b := by simp
    simp only [hb_not, ↓reduceIte, add_zero]; split_ifs <;> norm_num
/-- Coarea upper bound on `distributionalVariation` for a monotone function on `Icc a b`. -/
theorem _root_.MonotoneOn.distributionalVariation_Ioo_le {a b : ℝ} (hab : a ≤ b) {u : ℝ → ℝ}
    (hmono : MonotoneOn u (Icc a b)) :
    distributionalVariation volume (Opens.Ioo a b) u ≤ ENNReal.ofReal (u b - u a) := by
  have hu_meas : AEStronglyMeasurable u (volume.restrict (Opens.Ioo a b : Set ℝ)) :=
    (aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
      (hmono.mono Ioo_subset_Icc_self)).aestronglyMeasurable
  have h_clamp : ∀ᵐ x ∂volume.restrict (Opens.Ioo a b : Set ℝ),
      min (max (u x) (u a)) (u b) = u x := by
    rw [Opens.coe_Ioo, ae_restrict_iff' measurableSet_Ioo]; exact Eventually.of_forall fun x hx ↦ by
      rw [max_eq_left (hmono (left_mem_Icc.2 hab) (Ioo_subset_Icc_self hx) hx.1.le),
        min_eq_left (hmono (Ioo_subset_Icc_self hx) (right_mem_Icc.2 hab) hx.2.le)]
  rw [← distributionalVariation_congr_ae h_clamp]
  refine (distributionalVariation_min_max_le_lintegral_relativePerimeter
    (hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab) hu_meas).trans
    ((lintegral_mono fun t ↦ relativePerimeter_Ioo_lt_le_one_of_monotoneOn hmono t).trans_eq ?_)
  simp [Real.volume_Ioo]
/-- Exact variational total variation `ENNReal.ofReal (u b - u a)` for continuous monotone `u`. -/
theorem _root_.MonotoneOn.distributionalVariation_Ioo_eq {a b : ℝ} (hab : a ≤ b) {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc a b)) (hmono : MonotoneOn u (Icc a b)) :
    distributionalVariation volume (Opens.Ioo a b) u = ENNReal.ofReal (u b - u a) := by
  refine le_antisymm (hmono.distributionalVariation_Ioo_le hab) ?_
  have hev := hmono.eVariationOn_eq (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
  rw [inter_self] at hev; rw [← hev]; exact eVariationOn_Icc_le_distributionalVariation_Ioo hcont
/-- Whole-space distributional variation on `ℝ` is the supremum over bounded open intervals. -/
theorem distributionalVariation_top_eq_iSup_Ioo (u : ℝ → ℝ) :
    distributionalVariation volume (⊤ : Opens ℝ) u =
      ⨆ (a : ℝ) (b : ℝ), distributionalVariation volume (Opens.Ioo a b) u := by
  refine le_antisymm (iSup₂_le fun φ hφ ↦ ?_)
    (iSup₂_le fun a b ↦ distributionalVariation_mono le_top u)
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball 0; let R' := max R 1
  have hsub : tsupport (φ : ℝ → ℝ) ⊆ (Opens.Ioo (-R') R' : Set ℝ) := by
    refine hR.trans ?_; rw [Real.ball_eq_Ioo, zero_sub, zero_add]
    exact Ioo_subset_Ioo (neg_le_neg (le_max_left _ _)) (le_max_left _ _)
  let φ' : 𝓓(Opens.Ioo (-R') R', ℝ) := ⟨φ.toFun, φ.contDiff', φ.hasCompactSupport', hsub⟩
  have h_int : ∫ x in ((⊤ : Opens ℝ) : Set ℝ), u x * divergence (φ : ℝ → ℝ) x =
      ∫ x in (Opens.Ioo (-R') R' : Set ℝ), u x * divergence (φ' : ℝ → ℝ) x := by
    rw [setIntegral_mul_divergence_eq_integral, setIntegral_mul_divergence_eq_integral]; rfl
  rw [h_int]; exact le_iSup₂_of_le (-R') R' (le_iSup₂_of_le φ' hφ le_rfl)
/-- **Variational total variation of the Cantor–Lebesgue function on `(0, 1)` is `1`**. -/
@[simp] theorem distributionalVariation_Ioo_cantorFunction :
    distributionalVariation volume (Opens.Ioo 0 1) cantorFunction = 1 := by
  rw [(monotone_cantorFunction.monotoneOn _).distributionalVariation_Ioo_eq zero_le_one
    continuous_cantorFunction.continuousOn, cantorFunction_one, cantorFunction_zero, sub_zero,
    ENNReal.ofReal_one]
/-- **Variational total variation of the Cantor–Lebesgue function on `ℝ` is `1`**. -/
@[simp] theorem distributionalVariation_top_cantorFunction :
    distributionalVariation volume (⊤ : Opens ℝ) cantorFunction = 1 := by
  refine le_antisymm (distributionalVariation_top_eq_iSup_Ioo _ ▸ iSup₂_le fun a b ↦ ?_)
    (distributionalVariation_Ioo_cantorFunction ▸
      distributionalVariation_mono le_top cantorFunction)
  rcases le_or_gt a b with hab | hab
  · rw [(monotone_cantorFunction.monotoneOn _).distributionalVariation_Ioo_eq hab
      continuous_cantorFunction.continuousOn, ENNReal.ofReal_le_one]
    linarith [cantorFunction_nonneg a, cantorFunction_le_one b]
  · exact iSup₂_le fun φ _ ↦ by simp [Opens.coe_Ioo, Ioo_eq_empty hab.not_gt]
/-- The Cantor–Lebesgue function belongs to `IsBVOn volume (Opens.Ioo 0 1)`. -/
theorem isBVOn_Ioo_cantorFunction : IsBVOn volume (Opens.Ioo 0 1) cantorFunction :=
  ⟨(continuous_cantorFunction.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self,
    by rw [distributionalVariation_Ioo_cantorFunction]; exact ENNReal.one_lt_top⟩
/-- The Cantor–Lebesgue function belongs to `IsLocallyBVOn volume ⊤`. -/
theorem isLocallyBVOn_top_cantorFunction : IsLocallyBVOn volume (⊤ : Opens ℝ) cantorFunction :=
  ⟨continuous_cantorFunction.locallyIntegrable.locallyIntegrableOn _, fun _ _ _ ↦
    (distributionalVariation_mono le_top cantorFunction).trans_lt
      (by rw [distributionalVariation_top_cantorFunction]; exact ENNReal.one_lt_top)⟩
/-- **Singular BV gap for the Cantor–Lebesgue function**: `∫⁻ ‖deriv cantorFunction‖ₑ < 1`. -/
theorem lintegral_enorm_deriv_lt_distributionalVariation_cantorFunction :
    (∫⁻ x in Ioo (0 : ℝ) 1, ‖deriv cantorFunction x‖ₑ) <
      distributionalVariation volume (Opens.Ioo 0 1) cantorFunction := by
  rw [restrict_Ioo_eq_restrict_Icc, lintegral_enorm_deriv_cantorFunction,
    distributionalVariation_Ioo_cantorFunction]; exact zero_lt_one
/-! ### Section 3: Sharp 1D Isoperimetric Inequality and `OrdConnected` Interval Rigidity -/
/-- Essential-exterior and essential-interior points force `1 ≤ perimeter volume s`. -/
theorem one_le_perimeter_of_mem_essentialExterior_of_mem_essentialInterior
    {s : Set ℝ} (hs : NullMeasurableSet s volume) {x₀ x₁ : ℝ}
    (hx₀ : x₀ ∈ essentialExterior volume s) (hx₁ : x₁ ∈ essentialInterior volume s) :
    1 ≤ perimeter volume s := by
  have hu := locallyIntegrableOn_top_indicator_one hs; rcases le_total x₀ x₁ with hle | hle
  · have ht : Monotone ![x₀, x₁] := Fin.monotone_iff_le_succ.2 fun k ↦ by fin_cases k; exact hle
    simpa [perimeter, relativePerimeter] using ofReal_sum_abs_sub_le_distributionalVariation
      (val := ![0, 1]) hu ht (subset_univ _) fun j ↦ by
        fin_cases j
        exacts [tendsto_bumpMollify_indicator_zero hx₀, tendsto_bumpMollify_indicator_one hs hx₁]
  · have ht : Monotone ![x₁, x₀] := Fin.monotone_iff_le_succ.2 fun k ↦ by fin_cases k; exact hle
    simpa [perimeter, relativePerimeter] using ofReal_sum_abs_sub_le_distributionalVariation
      (val := ![1, 0]) hu ht (subset_univ _) fun j ↦ by
        fin_cases j
        exacts [tendsto_bumpMollify_indicator_one hs hx₁, tendsto_bumpMollify_indicator_zero hx₀]
/-- An essential-interior point between two essential-exterior points forces `2 ≤ perimeter`. -/
theorem two_le_perimeter_of_essentialExterior_essentialInterior {s : Set ℝ}
    (hs : NullMeasurableSet s volume) {x₀ x₁ x₂ : ℝ} (h01 : x₀ ≤ x₁) (h12 : x₁ ≤ x₂)
    (hx₀ : x₀ ∈ essentialExterior volume s) (hx₁ : x₁ ∈ essentialInterior volume s)
    (hx₂ : x₂ ∈ essentialExterior volume s) : 2 ≤ perimeter volume s := by
  let t : Fin 3 → ℝ := ![x₀, x₁, x₂]; let val : Fin 3 → ℝ := ![0, 1, 0]
  have ht : Monotone t := Fin.monotone_iff_le_succ.2 fun k ↦ by fin_cases k <;> simpa [t]
  have h := ofReal_sum_abs_sub_le_distributionalVariation (val := val)
    (locallyIntegrableOn_top_indicator_one hs) ht (subset_univ _) fun j ↦ by
      fin_cases j; exacts [tendsto_bumpMollify_indicator_zero hx₀,
        tendsto_bumpMollify_indicator_one hs hx₁, tendsto_bumpMollify_indicator_zero hx₂]
  have hsum : (∑ k : Fin 2, |val k.succ - val k.castSucc|) = 2 := by
    simp [Fin.sum_univ_two, val]; norm_num
  rw [hsum, ENNReal.ofReal_ofNat] at h; exact h
/-- Five alternating essential-exterior/interior points force `4 ≤ perimeter volume s`. -/
theorem four_le_perimeter_of_essentialExterior_between_essentialInterior {s : Set ℝ}
    (hs : NullMeasurableSet s volume) {x₀ x₁ y x₂ x₃ : ℝ}
    (h01 : x₀ ≤ x₁) (h1y : x₁ ≤ y) (hy2 : y ≤ x₂) (h23 : x₂ ≤ x₃)
    (hx₀ : x₀ ∈ essentialExterior volume s) (hx₁ : x₁ ∈ essentialInterior volume s)
    (hy : y ∈ essentialExterior volume s) (hx₂ : x₂ ∈ essentialInterior volume s)
    (hx₃ : x₃ ∈ essentialExterior volume s) : 4 ≤ perimeter volume s := by
  let t : Fin 5 → ℝ := ![x₀, x₁, y, x₂, x₃]; let val : Fin 5 → ℝ := ![0, 1, 0, 1, 0]
  have ht : Monotone t := Fin.monotone_iff_le_succ.2 fun k ↦ by fin_cases k <;> simpa [t]
  have h := ofReal_sum_abs_sub_le_distributionalVariation (val := val)
    (locallyIntegrableOn_top_indicator_one hs) ht (subset_univ _) fun j ↦ by
      fin_cases j; exacts [tendsto_bumpMollify_indicator_zero hx₀,
        tendsto_bumpMollify_indicator_one hs hx₁, tendsto_bumpMollify_indicator_zero hy,
        tendsto_bumpMollify_indicator_one hs hx₂, tendsto_bumpMollify_indicator_zero hx₃]
  have hsum : (∑ k : Fin 4, |val k.succ - val k.castSucc|) = 4 := by
    simp [Fin.sum_univ_four, val]; norm_num
  rw [hsum, ENNReal.ofReal_ofNat] at h; exact h
/-- Any null-measurable set `s ⊆ ℝ` of positive Lebesgue measure has nonempty essential interior. -/
theorem exists_mem_essentialInterior_of_volume_pos {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (h0 : 0 < volume s) :
    (essentialInterior volume s).Nonempty :=
  nonempty_of_measure_ne_zero (μ := volume)
    ((measure_congr (essentialInterior_ae_eq hs)).trans_ne h0.ne')
/-- Any null-measurable set `s ⊆ ℝ` with `0 < volume sᶜ` has nonempty essential exterior. -/
theorem exists_mem_essentialExterior_of_volume_compl_pos {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (h0 : 0 < volume sᶜ) :
    (essentialExterior volume s).Nonempty :=
  nonempty_of_measure_ne_zero (μ := volume)
    ((measure_congr (essentialExterior_ae_eq hs)).trans_ne h0.ne')
/-- If `s ⊆ ℝ` is null-measurable with `0 < volume s` and `0 < volume sᶜ`, then `1 ≤ perimeter`. -/
theorem one_le_perimeter_of_volume_pos_of_volume_compl_pos {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (h0 : 0 < volume s) (hcompl : 0 < volume sᶜ) :
    1 ≤ perimeter volume s := by
  obtain ⟨x₀, hx₀⟩ := exists_mem_essentialExterior_of_volume_compl_pos hs hcompl
  obtain ⟨x₁, hx₁⟩ := exists_mem_essentialInterior_of_volume_pos hs h0
  exact one_le_perimeter_of_mem_essentialExterior_of_mem_essentialInterior hs hx₀ hx₁
lemma compl_essentialExterior_ae_eq {s : Set ℝ} (hs : NullMeasurableSet s volume) :
    (essentialExterior volume s)ᶜ =ᵐ[volume] s := by
  simpa only [compl_compl] using (essentialExterior_ae_eq hs).compl
/-- Any finite-measure null-measurable set `s ⊆ ℝ` has essential-exterior points below `a`. -/
theorem exists_lt_mem_essentialExterior_of_volume_lt_top {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) (a : ℝ) :
    ∃ x₀ < a, x₀ ∈ essentialExterior volume s := by
  by_contra! h
  have hvol : volume (Iio a) ≤ volume s := (measure_mono fun x hx ↦ h x hx).trans_eq
    (measure_congr (compl_essentialExterior_ae_eq hs))
  rw [Real.volume_Iio] at hvol; exact htop.not_ge hvol
/-- Any finite-measure null-measurable set `s ⊆ ℝ` has essential-exterior points above `b`. -/
theorem exists_gt_mem_essentialExterior_of_volume_lt_top {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) (b : ℝ) :
    ∃ x₃ > b, x₃ ∈ essentialExterior volume s := by
  by_contra! h
  have hvol : volume (Ioi b) ≤ volume s := (measure_mono fun x hx ↦ h x hx).trans_eq
    (measure_congr (compl_essentialExterior_ae_eq hs))
  rw [Real.volume_Ioi] at hvol; exact htop.not_ge hvol
/-- **Sharp 1D Isoperimetric Inequality**: `0 < volume s < ⊤` implies `2 ≤ perimeter volume s`. -/
theorem two_le_perimeter_of_volume_pos {s : Set ℝ} (hs : NullMeasurableSet s volume)
    (h0 : 0 < volume s) (htop : volume s < ⊤) : 2 ≤ perimeter volume s := by
  obtain ⟨x₁, hx₁⟩ := exists_mem_essentialInterior_of_volume_pos hs h0
  obtain ⟨x₀, hx₀_lt, hx₀⟩ := exists_lt_mem_essentialExterior_of_volume_lt_top hs htop x₁
  obtain ⟨x₂, hx₂_gt, hx₂⟩ := exists_gt_mem_essentialExterior_of_volume_lt_top hs htop x₁
  exact two_le_perimeter_of_essentialExterior_essentialInterior hs hx₀_lt.le hx₂_gt.le hx₀ hx₁ hx₂
/-- Below perimeter `4`, no essential-exterior point lies between two essential-interior points. -/
theorem notMem_essentialExterior_of_mem_essentialInterior_of_perimeter_lt_four {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) (hper : perimeter volume s < 4)
    {x₁ y x₂ : ℝ} (hx₁ : x₁ ∈ essentialInterior volume s)
    (hx₂ : x₂ ∈ essentialInterior volume s) (h1y : x₁ ≤ y) (hy2 : y ≤ x₂) :
    y ∉ essentialExterior volume s := by
  intro hy; obtain ⟨x₀, hx₀_lt, hx₀⟩ := exists_lt_mem_essentialExterior_of_volume_lt_top hs htop x₁
  obtain ⟨x₃, hx₃_gt, hx₃⟩ := exists_gt_mem_essentialExterior_of_volume_lt_top hs htop x₂
  exact hper.not_ge (four_le_perimeter_of_essentialExterior_between_essentialInterior hs
    hx₀_lt.le h1y hy2 hx₃_gt.le hx₀ hx₁ hy hx₂ hx₃)
/-- **1D Interval Rigidity below Perimeter `4`**: `s =ᵐ[volume] Ioo a b` for some `a ≤ b`. -/
theorem exists_Ioo_ae_eq_of_perimeter_lt_four {s : Set ℝ} (hs : NullMeasurableSet s volume)
    (htop : volume s < ⊤) (hper : perimeter volume s < 4) :
    ∃ a b : ℝ, a ≤ b ∧ (s =ᵐ[volume] Ioo a b) := by
  let E := essentialInterior volume s; rcases E.eq_empty_or_nonempty with hEmpty | ⟨x₁, hx₁⟩
  · refine ⟨0, 0, le_rfl, ?_⟩; rw [Ioo_self, ← hEmpty]; exact (essentialInterior_ae_eq hs).symm
  · obtain ⟨x₀, hx₀_lt, hx₀⟩ := exists_lt_mem_essentialExterior_of_volume_lt_top hs htop x₁
    obtain ⟨x₃, hx₃_gt, hx₃⟩ := exists_gt_mem_essentialExterior_of_volume_lt_top hs htop x₁
    have hbdd_below : BddBelow E := ⟨x₀, fun x hx ↦ by_contra fun hlt ↦
      notMem_essentialExterior_of_mem_essentialInterior_of_perimeter_lt_four
        hs htop hper hx hx₁ (not_le.1 hlt).le hx₀_lt.le hx₀⟩
    have hbdd_above : BddAbove E := ⟨x₃, fun x hx ↦ by_contra fun hgt ↦
      notMem_essentialExterior_of_mem_essentialInterior_of_perimeter_lt_four
        hs htop hper hx₁ hx hx₃_gt.le (not_le.1 hgt).le hx₃⟩
    let a := sInf E; let b := sSup E
    have hab : a ≤ b := (csInf_le hbdd_below hx₁).trans (le_csSup hbdd_above hx₁)
    have hE_sub : E ⊆ Icc a b := fun x hx ↦ ⟨csInf_le hbdd_below hx, le_csSup hbdd_above hx⟩
    have hIoo_sub : Ioo a b ⊆ (essentialExterior volume s)ᶜ := fun y hy ↦ by
      obtain ⟨u, huE, huy⟩ := exists_lt_of_csInf_lt ⟨x₁, hx₁⟩ hy.1
      obtain ⟨v, hvE, hyv⟩ := exists_lt_of_lt_csSup ⟨x₁, hx₁⟩ hy.2
      exact notMem_essentialExterior_of_mem_essentialInterior_of_perimeter_lt_four
        hs htop hper huE hvE huy.le hyv.le
    refine ⟨a, b, hab, EventuallyLE.antisymm ?_ ?_⟩
    · exact (essentialInterior_ae_eq hs).symm.le.trans
        ((LE.le.eventuallySubset hE_sub).trans Ioo_ae_eq_Icc.symm.le)
    · exact (LE.le.eventuallySubset hIoo_sub).trans (compl_essentialExterior_ae_eq hs).le
/-- `0 < volume s < ⊤` and `perimeter volume s < 4` imply `s =ᵐ[volume] Ioo a b` with `a < b`. -/
theorem exists_Ioo_lt_ae_eq_of_perimeter_lt_four {s : Set ℝ} (hs : NullMeasurableSet s volume)
    (h0 : 0 < volume s) (htop : volume s < ⊤) (hper : perimeter volume s < 4) :
    ∃ a b : ℝ, a < b ∧ (s =ᵐ[volume] Ioo a b) := by
  obtain ⟨a, b, hab, hae⟩ := exists_Ioo_ae_eq_of_perimeter_lt_four hs htop hper
  refine ⟨a, b, hab.lt_of_ne ?_, hae⟩; rintro rfl; have hvol := measure_congr hae
  rw [Ioo_self, measure_empty] at hvol; exact h0.ne' hvol
/-- `volume s < ⊤` and `perimeter volume s < 4` imply `s` is a.e. equal to an `OrdConnected` set. -/
theorem exists_ordConnected_ae_eq_of_perimeter_lt_four {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) (hper : perimeter volume s < 4) :
    ∃ I : Set ℝ, I.OrdConnected ∧ (s =ᵐ[volume] I) := by
  obtain ⟨a, b, -, hae⟩ := exists_Ioo_ae_eq_of_perimeter_lt_four hs htop hper
  exact ⟨Ioo a b, ordConnected_Ioo, hae⟩
/-- **1D Perimeter Dichotomy below `4`**: `perimeter volume s = 0` or `perimeter volume s = 2`. -/
theorem perimeter_eq_zero_or_eq_two_of_perimeter_lt_four {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) (hper : perimeter volume s < 4) :
    perimeter volume s = 0 ∨ perimeter volume s = 2 := by
  obtain ⟨a, b, hab, hae⟩ := exists_Ioo_ae_eq_of_perimeter_lt_four hs htop hper
  rw [perimeter_congr_ae hae]; rcases hab.eq_or_lt with rfl | hlt
  · left; exact perimeter_Ioo_of_ge le_rfl
  · right; exact perimeter_Ioo hlt
/-- **Sharp 1D Isoperimetric Equality Characterization (Open Intervals)**. -/
theorem perimeter_eq_two_iff_exists_Ioo_ae_eq {s : Set ℝ} (hs : NullMeasurableSet s volume)
    (htop : volume s < ⊤) :
    perimeter volume s = 2 ↔ ∃ a b : ℝ, a < b ∧ (s =ᵐ[volume] Ioo a b) := by
  refine ⟨fun hper ↦ ?_, fun ⟨a, b, hab, hae⟩ ↦ by rw [perimeter_congr_ae hae, perimeter_Ioo hab]⟩
  have h0 : 0 < volume s := pos_iff_ne_zero.2 fun hzero ↦ by
    have hae : s =ᵐ[volume] (∅ : Set ℝ) := ae_eq_empty.2 hzero
    rw [perimeter_congr_ae hae, perimeter, relativePerimeter_empty] at hper; norm_num at hper
  exact exists_Ioo_lt_ae_eq_of_perimeter_lt_four hs h0 htop (by rw [hper]; norm_num)
/-- **Sharp 1D Isoperimetric Equality Characterization (`OrdConnected` Sets)**. -/
theorem perimeter_eq_two_iff_exists_ordConnected_ae_eq {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (h0 : 0 < volume s) (htop : volume s < ⊤) :
    perimeter volume s = 2 ↔ ∃ I : Set ℝ, I.OrdConnected ∧ (s =ᵐ[volume] I) :=
  ⟨fun hper ↦ exists_ordConnected_ae_eq_of_perimeter_lt_four hs htop (by rw [hper]; norm_num),
    fun ⟨I, hI, hae⟩ ↦ by
      rw [perimeter_congr_ae hae]
      exact hI.perimeter_eq_two (measure_congr hae ▸ h0) (measure_congr hae ▸ htop)⟩

/-! ### Section 4: 1D Slice Isoperimetric Inequality and Equality Rigidity on Product Spaces -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
lemma measurable_volume_slice {s : Set (X × ℝ)} (hs : MeasurableSet s) :
    Measurable fun y : X ↦ volume {t : ℝ | (y, t) ∈ s} := by
  have hm : Measurable fun y : X ↦
      ∫⁻ t : ℝ, s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (y, t) ∂volume :=
    (measurable_const.indicator hs).lintegral_prod_right'
  convert hm using 1; ext y; have hind : (fun t : ℝ ↦ s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (y, t)) =
      {t : ℝ | (y, t) ∈ s}.indicator 1 := by ext t; by_cases h : (y, t) ∈ s <;> simp [h]
  rw [hind]; exact (lintegral_indicator_one (hs.preimage measurable_prodMk_left)).symm
/-- If `(μ.prod volume) s < ⊤`, then `μ`-a.e. vertical slice has finite 1D Lebesgue measure. -/
theorem ae_volume_slice_lt_top {s : Set (X × ℝ)} (hs : MeasurableSet s)
    (htop : (μ.prod (volume : Measure ℝ)) s < ⊤) :
    ∀ᵐ y ∂μ, volume {t : ℝ | (y, t) ∈ s} < ⊤ := by
  refine ae_lt_top (measurable_volume_slice hs) ?_
  have heq : (∫⁻ y : X, volume {t : ℝ | (y, t) ∈ s} ∂μ) = (μ.prod (volume : Measure ℝ)) s := by
    rw [Measure.prod_apply hs]; rfl
  exact heq ▸ htop.ne
/-- **Slice Isoperimetric Lower Bound** on product spaces `X × ℝ`. -/
theorem two_mul_measure_slice_pos_le_lintegral_perimeter_slice {s : Set (X × ℝ)}
    (hs : MeasurableSet s) (hfin : ∀ᵐ y ∂μ, volume {t : ℝ | (y, t) ∈ s} < ⊤) :
    2 * μ {y : X | 0 < volume {t : ℝ | (y, t) ∈ s}} ≤
      ∫⁻ y : X, perimeter volume {t : ℝ | (y, t) ∈ s} ∂μ := by
  let A : Set X := {y : X | 0 < volume {t : ℝ | (y, t) ∈ s}}
  have hA_meas : MeasurableSet A := measurable_volume_slice hs measurableSet_Ioi
  rw [← lintegral_indicator_const hA_meas (2 : ℝ≥0∞)]
  refine lintegral_mono_ae (hfin.mono fun y hy ↦ ?_); by_cases hyA : y ∈ A
  · rw [indicator_of_mem hyA]
    exact two_le_perimeter_of_volume_pos
      (hs.preimage measurable_prodMk_left).nullMeasurableSet hyA hy
  · rw [indicator_of_notMem hyA]; exact zero_le
/-- **Slice Isoperimetric Lower Bound for Finite-Measure Product Sets**. -/
theorem two_mul_measure_slice_pos_le_lintegral_perimeter_slice_of_measure_lt_top
    {s : Set (X × ℝ)} (hs : MeasurableSet s) (htop : (μ.prod (volume : Measure ℝ)) s < ⊤) :
    2 * μ {y : X | 0 < volume {t : ℝ | (y, t) ∈ s}} ≤
      ∫⁻ y : X, perimeter volume {t : ℝ | (y, t) ∈ s} ∂μ :=
  two_mul_measure_slice_pos_le_lintegral_perimeter_slice hs (ae_volume_slice_lt_top hs htop)
/-- **Fiberwise Interval Rigidity below Perimeter `4`** on `X × ℝ`. -/
theorem ae_exists_ordConnected_ae_eq_slice_of_ae_perimeter_lt_four {s : Set (X × ℝ)}
    (hs : MeasurableSet s) (hfin : ∀ᵐ y ∂μ, volume {t : ℝ | (y, t) ∈ s} < ⊤)
    (hper : ∀ᵐ y ∂μ, perimeter volume {t : ℝ | (y, t) ∈ s} < 4) :
    ∀ᵐ y ∂μ, ∃ I : Set ℝ, I.OrdConnected ∧ ({t : ℝ | (y, t) ∈ s} =ᵐ[volume] I) := by
  filter_upwards [hfin, hper] with y hy hpy; exact exists_ordConnected_ae_eq_of_perimeter_lt_four
    (hs.preimage measurable_prodMk_left).nullMeasurableSet hy hpy
/-- **Slice Isoperimetric Equality Rigidity** on `X × ℝ`. -/
theorem ae_exists_ordConnected_ae_eq_slice_of_lintegral_perimeter_le {s : Set (X × ℝ)}
    (hs : MeasurableSet s) (hfin : ∀ᵐ y ∂μ, volume {t : ℝ | (y, t) ∈ s} < ⊤)
    (hmeas_lt : μ {y : X | 0 < volume {t : ℝ | (y, t) ∈ s}} < ⊤)
    (hf_meas : AEMeasurable (fun y : X ↦ perimeter volume {t : ℝ | (y, t) ∈ s}) μ)
    (hle : (∫⁻ y : X, perimeter volume {t : ℝ | (y, t) ∈ s} ∂μ) ≤
      2 * μ {y : X | 0 < volume {t : ℝ | (y, t) ∈ s}}) :
    ∀ᵐ y ∂μ, ∃ I : Set ℝ, I.OrdConnected ∧ ({t : ℝ | (y, t) ∈ s} =ᵐ[volume] I) := by
  let A : Set X := {y : X | 0 < volume {t : ℝ | (y, t) ∈ s}}
  have hA_meas : MeasurableSet A := measurable_volume_slice hs measurableSet_Ioi
  let g : X → ℝ≥0∞ := A.indicator fun _ ↦ 2
  let f : X → ℝ≥0∞ := fun y ↦ perimeter volume {t : ℝ | (y, t) ∈ s}
  have h_ae_le : g ≤ᵐ[μ] f := hfin.mono fun y hy ↦ by
    by_cases hyA : y ∈ A
    · simp only [g, indicator_of_mem hyA]
      exact two_le_perimeter_of_volume_pos
        (hs.preimage measurable_prodMk_left).nullMeasurableSet hyA hy
    · simp [g, hyA]
  have hint_g : ∫⁻ y, g y ∂μ = 2 * μ A := lintegral_indicator_const hA_meas 2
  have hint_lt : (∫⁻ y, g y ∂μ) ≠ ⊤ :=
    hint_g ▸ ENNReal.mul_ne_top ENNReal.ofNat_ne_top hmeas_lt.ne
  have hae_eq : g =ᵐ[μ] f :=
    ae_eq_of_ae_le_of_lintegral_le h_ae_le hint_lt hf_meas (hint_g.symm ▸ hle)
  refine ae_exists_ordConnected_ae_eq_slice_of_ae_perimeter_lt_four hs hfin
    (hae_eq.mono fun y hgf ↦ ?_)
  change f y < 4; rw [← hgf]; by_cases hyA : y ∈ A <;> simp [g, hyA]; norm_num

end TauCeti
