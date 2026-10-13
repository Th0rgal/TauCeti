/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.BoxPerimeter
public import TauCeti.MeasureTheory.Measure.IntervalPerimeter
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.BoxPerimeter
import all TauCeti.MeasureTheory.Measure.IntervalPerimeter

/-!
# Directional Variation, Line-Slicing, `OrdConnected` Perimeter, and Lipschitz BV Composition

This file develops four foundational tools for functions of bounded variation and sets of finite
perimeter:

1. **Directional variation and orthonormal basis characterization of `BV` and finite perimeter**:
   We define `directionalVariation μ Ω v u` and `directionalPerimeter μ Ω v s` via
   `constSmulTestFunction` and `innerTestFunction`, and prove the orthonormal basis inequalities
   `distributionalVariation_le_sum_directionalVariation` and
   `isBVOn_iff_forall_directionalVariation_lt_top`.
2. **One-dimensional line-slicing inequalities**:
   By slicing test functions along fibers of `E × ℝ` and coordinate lines `boxSlice i x'` in
   `EuclideanSpace ℝ (Fin n)`, we prove `directionalVariation_snd_le_lintegral_slice` and
   `directionalVariation_single_le_lintegral_boxSlice`.
3. **Perimeter of arbitrary `OrdConnected` subsets of `ℝ`**:
   Every finite-measure `OrdConnected` set `I ⊆ ℝ` satisfies `I =ᵐ[volume] Ioo (sInf I) (sSup I)`
   and `perimeter volume I = if 0 < volume I then 2 else 0 ≤ 2` (`OrdConnected.perimeter_eq_two`).
4. **Lattice operations and Lipschitz scalar composition in `BV`**:
   We prove superlevel coarea bounds for `max (u x) c`, `min (u x) c`, `|u x|`, and `f ∘ u` for any
   `K`-Lipschitz function `f : ℝ → ℝ`.
-/

public section

open Filter Function LineDeriv MeasureTheory MeasureTheory.Measure Set TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Distributions Topology

namespace TauCeti

/-! ### Section 1: Directional variation and orthonormal basis characterization of BV -/

section DirectionalVariation

variable {E : Type*} [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E] {Ω : Opens E}

/-- Bundled directional test vector field `x ↦ ψ x • v` in `𝓓(Ω, E)`. -/
noncomputable def constSmulTestFunction (ψ : 𝓓(Ω, ℝ)) (v : E) : 𝓓(Ω, E) where
  toFun x := ψ x • v
  contDiff' := ψ.contDiff.smul contDiff_const
  hasCompactSupport' := ψ.hasCompactSupport.smul_right
  tsupport_subset' := (tsupport_smul_subset_left _ _).trans ψ.tsupport_subset

/-- Evaluating `constSmulTestFunction ψ v` at `x` gives `ψ x • v`. -/
@[simp] theorem constSmulTestFunction_apply (ψ : 𝓓(Ω, ℝ)) (v x : E) :
    constSmulTestFunction ψ v x = ψ x • v := by rfl
/-- Coercing `constSmulTestFunction ψ v` to a function gives `fun x ↦ ψ x • v`. -/
@[simp] theorem coe_constSmulTestFunction (ψ : 𝓓(Ω, ℝ)) (v : E) :
    (constSmulTestFunction ψ v : E → E) = fun x ↦ ψ x • v := by rfl

/-- Outside `Ω`, the directional derivative `fderiv ℝ (ψ : E → ℝ) x v` of `ψ : 𝓓(Ω, ℝ)` vanishes. -/
theorem fderiv_testFunction_eq_zero_of_notMem (ψ : 𝓓(Ω, ℝ)) (v : E) {x : E}
    (hx : x ∉ (Ω : Set E)) : fderiv ℝ (ψ : E → ℝ) x v = 0 := by
  have hx' : x ∉ tsupport (ψ : E → ℝ) := fun h ↦ hx (ψ.tsupport_subset h)
  simp [(notMem_tsupport_iff_eventuallyEq.1 hx').fderiv_eq]

variable [MeasurableSpace E] {μ : Measure E}

/-- The **directional variation** of `u : E → ℝ` in direction `v : E` on `Ω : Opens E`. -/
noncomputable def directionalVariation (μ : Measure E := by volume_tac) (Ω : Opens E) (v : E)
    (u : E → ℝ) : ℝ≥0∞ :=
  ⨆ (ψ : 𝓓(Ω, ℝ)) (_ : ∀ x, ‖ψ x‖ ≤ 1),
    ENNReal.ofReal (∫ x in (Ω : Set E), u x * fderiv ℝ (ψ : E → ℝ) x v ∂μ)

/-- The **directional perimeter** of `s : Set E` in direction `v : E` on `Ω : Opens E`. -/
noncomputable def directionalPerimeter (μ : Measure E := by volume_tac) (Ω : Opens E) (v : E)
    (s : Set E) : ℝ≥0∞ := directionalVariation μ Ω v (s.indicator fun _ ↦ (1 : ℝ))

/-- Any unit scalar test function `ψ : 𝓓(Ω, ℝ)` bounds `directionalVariation` below. -/
theorem le_directionalVariation (ψ : 𝓓(Ω, ℝ)) (hψ : ∀ x, ‖ψ x‖ ≤ 1) (v : E) (u : E → ℝ) :
    ENNReal.ofReal (∫ x in (Ω : Set E), u x * fderiv ℝ (ψ : E → ℝ) x v ∂μ) ≤
      directionalVariation μ Ω v u :=
  le_iSup₂ (f := fun (ψ : 𝓓(Ω, ℝ)) (_ : ∀ x, ‖ψ x‖ ≤ 1) ↦
    ENNReal.ofReal (∫ x in (Ω : Set E), u x * fderiv ℝ (ψ : E → ℝ) x v ∂μ)) ψ hψ

/-- Absolute-value lower bound for `directionalVariation` against any unit scalar test function. -/
theorem abs_le_directionalVariation (ψ : 𝓓(Ω, ℝ)) (hψ : ∀ x, ‖ψ x‖ ≤ 1) (v : E) (u : E → ℝ) :
    ENNReal.ofReal |∫ x in (Ω : Set E), u x * fderiv ℝ (ψ : E → ℝ) x v ∂μ| ≤
      directionalVariation μ Ω v u := by
  rcases le_total 0 (∫ x in (Ω : Set E), u x * fderiv ℝ (ψ : E → ℝ) x v ∂μ) with h0 | h0
  · rw [abs_of_nonneg h0]; exact le_directionalVariation ψ hψ v u
  · rw [abs_of_nonpos h0]
    have h := le_directionalVariation (μ := μ) (-ψ) (fun x ↦ by simpa using hψ x) v u
    have hcoe : ((-ψ : 𝓓(Ω, ℝ)) : E → ℝ) = -(ψ : E → ℝ) := rfl
    simpa only [hcoe, fderiv_neg, _root_.neg_apply, mul_neg, integral_neg] using h

/-- `directionalVariation` equals the supremum of `ofReal |∫ x in Ω, u x * fderiv ψ x v|`. -/
theorem directionalVariation_eq_iSup_abs (μ : Measure E) (Ω : Opens E) (v : E) (u : E → ℝ) :
    directionalVariation μ Ω v u = ⨆ (ψ : 𝓓(Ω, ℝ)) (_ : ∀ x, ‖ψ x‖ ≤ 1),
      ENNReal.ofReal |∫ x in (Ω : Set E), u x * fderiv ℝ (ψ : E → ℝ) x v ∂μ| :=
  le_antisymm (iSup₂_le fun ψ hψ ↦ le_iSup₂_of_le ψ hψ (ENNReal.ofReal_le_ofReal (le_abs_self _)))
    (iSup₂_le fun ψ hψ ↦ abs_le_directionalVariation ψ hψ v u)

/-- `directionalVariation` is invariant under almost-everywhere equality on `Ω`. -/
theorem directionalVariation_congr_ae {v : E} {u₁ u₂ : E → ℝ} (h : u₁ =ᵐ[μ.restrict Ω] u₂) :
    directionalVariation μ Ω v u₁ = directionalVariation μ Ω v u₂ := by
  unfold directionalVariation
  refine iSup_congr fun ψ ↦ iSup_congr fun _ ↦ congrArg ENNReal.ofReal (integral_congr_ae ?_)
  filter_upwards [h] with x hx using by rw [hx]

/-- `directionalPerimeter` is invariant under almost-everywhere set equality on `Ω`. -/
theorem directionalPerimeter_congr_ae {v : E} {s t : Set E} (h : s =ᵐ[μ.restrict Ω] t) :
    directionalPerimeter μ Ω v s = directionalPerimeter μ Ω v t := by
  refine directionalVariation_congr_ae (h.mono fun x hx ↦ ?_)
  have hmem : x ∈ s ↔ x ∈ t := by simpa [eq_iff_iff] using hx
  by_cases hxs : x ∈ s <;> [simp [hxs, hmem.1 hxs]; simp [hxs, mt hmem.2 hxs]]

/-- Directional variation along the zero vector is `0`. -/
@[simp] theorem directionalVariation_zero_left (u : E → ℝ) :
    directionalVariation μ Ω 0 u = 0 := by simp [directionalVariation]
/-- Directional variation of the zero function is `0`. -/
@[simp] theorem directionalVariation_zero (v : E) :
    directionalVariation μ Ω v 0 = 0 := by simp [directionalVariation]
/-- Directional perimeter of the empty set is `0`. -/
@[simp] theorem directionalPerimeter_empty (v : E) :
    directionalPerimeter μ Ω v ∅ = 0 := by simp [directionalPerimeter, directionalVariation]

/-- Negating the direction vector preserves `directionalVariation`. -/
@[simp] theorem directionalVariation_neg_left (v : E) (u : E → ℝ) :
    directionalVariation μ Ω (-v) u = directionalVariation μ Ω v u := by
  rw [directionalVariation_eq_iSup_abs, directionalVariation_eq_iSup_abs]
  refine iSup_congr fun ψ ↦ iSup_congr fun _ ↦ ?_
  simp only [map_neg, mul_neg, integral_neg, abs_neg]

/-- Scaling the direction vector by `c : ℝ` scales `directionalVariation` by `ofReal |c|`. -/
theorem directionalVariation_smul_left (c : ℝ) (v : E) (u : E → ℝ) :
    directionalVariation μ Ω (c • v) u = ENNReal.ofReal |c| * directionalVariation μ Ω v u := by
  rw [directionalVariation_eq_iSup_abs, directionalVariation_eq_iSup_abs, ENNReal.mul_iSup]
  refine iSup_congr fun ψ ↦ ?_; rw [ENNReal.mul_iSup]; refine iSup_congr fun _ ↦ ?_
  have hmul : (fun x ↦ u x * fderiv ℝ (ψ : E → ℝ) x (c • v)) =
      fun x ↦ c * (u x * fderiv ℝ (ψ : E → ℝ) x v) := by
    ext x; simp [map_smul, smul_eq_mul, mul_left_comm]
  rw [hmul, integral_const_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]

/-- If `u` is locally integrable on `Ω`, then `x ↦ u x * fderiv ℝ ψ x v` is integrable on `E`. -/
theorem integrable_mul_fderiv_of_locallyIntegrableOn [BorelSpace E]
    {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ) (ψ : 𝓓(Ω, ℝ)) (v : E) :
    Integrable (fun x ↦ u x * fderiv ℝ (ψ : E → ℝ) x v) μ := by
  refine (integrable_lineDeriv_smul_of_locallyIntegrableOn hu ψ v).congr
    (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [(ψ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv, smul_eq_mul, mul_comm]

/-- If `u` is locally integrable on `Ω`, then `x ↦ u x * fderiv ℝ ψ x v` is integrable on `Ω`. -/
theorem integrableOn_mul_fderiv_of_locallyIntegrableOn [BorelSpace E]
    {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ) (ψ : 𝓓(Ω, ℝ)) (v : E) :
    IntegrableOn (fun x ↦ u x * fderiv ℝ (ψ : E → ℝ) x v) Ω μ :=
  (integrable_mul_fderiv_of_locallyIntegrableOn hu ψ v).integrableOn

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E] {Ω : Opens E}

/-- The divergence of `constSmulTestFunction ψ v` at `x` equals `fderiv ℝ (ψ : E → ℝ) x v`. -/
theorem divergence_constSmulTestFunction [FiniteDimensional ℝ E] (ψ : 𝓓(Ω, ℝ)) (v x : E) :
    divergence (constSmulTestFunction ψ v : E → E) x = fderiv ℝ (ψ : E → ℝ) x v := by
  rw [coe_constSmulTestFunction,
    divergence_smul (ψ.contDiff.differentiable (by simp) x) (differentiableAt_const v),
    divergence_const, mul_zero, zero_add]

/-- Bundled scalar test function `x ↦ ⟪v, φ x⟫_ℝ` in `𝓓(Ω, ℝ)`. -/
noncomputable def innerTestFunction (v : E) (φ : 𝓓(Ω, E)) : 𝓓(Ω, ℝ) :=
  TestFunction.postcompCLM (𝕜 := ℝ) (innerSL ℝ v) φ

/-- Evaluating `innerTestFunction v φ` at `x` yields `⟪v, φ x⟫_ℝ`. -/
@[simp] theorem innerTestFunction_apply (v : E) (φ : 𝓓(Ω, E)) (x : E) :
    innerTestFunction v φ x = ⟪v, φ x⟫_ℝ := by rfl

/-- Directional derivative of `innerTestFunction v φ` at `x` along `w`. -/
theorem fderiv_innerTestFunction (v w : E) (φ : 𝓓(Ω, E)) (x : E) :
    fderiv ℝ (innerTestFunction v φ : E → ℝ) x w = ⟪v, fderiv ℝ (φ : E → E) x w⟫_ℝ := by
  have hd : DifferentiableAt ℝ (φ : E → E) x := φ.contDiff.differentiable (by simp) x
  have hdψ : HasFDerivAt (innerTestFunction v φ : E → ℝ)
      ((innerSL ℝ v).comp (fderiv ℝ (φ : E → E) x)) x :=
    (innerSL ℝ v).hasFDerivAt.comp x hd.hasFDerivAt
  rw [hdψ.fderiv]; rfl

variable [MeasurableSpace E] {μ : Measure E}

/-- For `‖v‖ ≤ 1`, `directionalVariation μ Ω v u ≤ distributionalVariation μ Ω u`. -/
theorem directionalVariation_le_distributionalVariation [FiniteDimensional ℝ E] {v : E}
    (hv : ‖v‖ ≤ 1) (u : E → ℝ) : directionalVariation μ Ω v u ≤ distributionalVariation μ Ω u := by
  refine iSup₂_le fun ψ hψ ↦ ?_
  have hnorm : ∀ x, ‖constSmulTestFunction ψ v x‖ ≤ 1 := fun x ↦ by
    rw [constSmulTestFunction_apply, norm_smul]; nlinarith [hψ x, hv, norm_nonneg v]
  simpa only [divergence_constSmulTestFunction] using
    le_distributionalVariation (μ := μ) (constSmulTestFunction ψ v) hnorm u

/-- For `‖v‖ ≤ 1`, `directionalPerimeter μ Ω v s ≤ relativePerimeter μ Ω s`. -/
theorem directionalPerimeter_le_relativePerimeter [FiniteDimensional ℝ E] {v : E}
    (hv : ‖v‖ ≤ 1) (s : Set E) : directionalPerimeter μ Ω v s ≤ relativePerimeter μ Ω s :=
  directionalVariation_le_distributionalVariation hv _

/-- For any `v : E`, `directionalVariation μ Ω v u ≤ ‖v‖ * distributionalVariation μ Ω u`. -/
theorem directionalVariation_le_norm_mul_distributionalVariation [FiniteDimensional ℝ E]
    (v : E) (u : E → ℝ) :
    directionalVariation μ Ω v u ≤ ENNReal.ofReal ‖v‖ * distributionalVariation μ Ω u := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hv_eq : v = ‖v‖ • (‖v‖⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    conv_lhs => rw [hv_eq]
    rw [directionalVariation_smul_left, abs_of_pos hpos]; gcongr
    exact directionalVariation_le_distributionalVariation
      (by rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']) u

/-- **Orthonormal basis upper bound on total variation**. -/
theorem distributionalVariation_le_sum_directionalVariation [BorelSpace E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) :
    distributionalVariation μ Ω u ≤ ∑ i : ι, directionalVariation μ Ω (b i) u := by
  refine iSup₂_le fun φ hφ ↦ ?_
  have hdiv : ∀ x, u x * divergence (φ : E → E) x =
      ∑ i : ι, u x * fderiv ℝ (innerTestFunction (b i) φ : E → ℝ) x (b i) := fun x ↦ by
    rw [divergence_eq_sum_orthonormalBasis b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [fderiv_innerTestFunction]
  simp_rw [hdiv]
  rw [integral_finsetSum _ fun i _ ↦
    integrableOn_mul_fderiv_of_locallyIntegrableOn hu (innerTestFunction (b i) φ) (b i)]
  have hsum : ENNReal.ofReal (∑ i : ι, ∫ x in (Ω : Set E),
        u x * fderiv ℝ (innerTestFunction (b i) φ : E → ℝ) x (b i) ∂μ) ≤
      ∑ i : ι, ENNReal.ofReal |∫ x in (Ω : Set E),
        u x * fderiv ℝ (innerTestFunction (b i) φ : E → ℝ) x (b i) ∂μ| := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _]
    exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun _ _ ↦ le_abs_self _)
  refine hsum.trans (Finset.sum_le_sum fun i _ ↦ ?_)
  refine abs_le_directionalVariation (innerTestFunction (b i) φ) (fun x ↦ ?_) (b i) u
  rw [innerTestFunction_apply, Real.norm_eq_abs]
  exact (abs_real_inner_le_norm (b i) (φ x)).trans (by rw [b.orthonormal.1 i, one_mul]; exact hφ x)

/-- **Orthonormal basis upper bound on relative perimeter**. -/
theorem relativePerimeter_le_sum_directionalPerimeter
    [FiniteDimensional ℝ E] [BorelSpace E] [IsLocallyFiniteMeasure μ]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {s : Set E}
    (hs : NullMeasurableSet s (μ.restrict Ω)) :
    relativePerimeter μ Ω s ≤ ∑ i : ι, directionalPerimeter μ Ω (b i) s :=
  distributionalVariation_le_sum_directionalVariation b (locallyIntegrableOn_indicator_const hs 1)

/-- **Orthonormal basis characterization of `IsBVOn`**. -/
theorem isBVOn_iff_forall_directionalVariation_lt_top
    [FiniteDimensional ℝ E] [BorelSpace E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {u : E → ℝ} (hu : IntegrableOn u Ω μ) :
    IsBVOn μ Ω u ↔ ∀ i : ι, directionalVariation μ Ω (b i) u < ⊤ :=
  ⟨fun h i ↦
      (directionalVariation_le_distributionalVariation (b.orthonormal.1 i).le u).trans_lt h.2,
    fun h ↦ ⟨hu, (distributionalVariation_le_sum_directionalVariation b
      hu.locallyIntegrableOn).trans_lt (ENNReal.sum_lt_top.2 fun i _ ↦ h i)⟩⟩

/-- **Orthonormal basis characterization of `HasFinitePerimeterIn`**. -/
theorem hasFinitePerimeterIn_iff_forall_directionalPerimeter_lt_top
    [FiniteDimensional ℝ E] [BorelSpace E] [IsLocallyFiniteMeasure μ]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {s : Set E}
    (hs : NullMeasurableSet s (μ.restrict Ω)) :
    HasFinitePerimeterIn μ Ω s ↔ ∀ i : ι, directionalPerimeter μ Ω (b i) s < ⊤ :=
  ⟨fun h i ↦ (directionalPerimeter_le_relativePerimeter (b.orthonormal.1 i).le s).trans_lt h.2,
    fun h ↦ ⟨hs, (relativePerimeter_le_sum_directionalPerimeter b hs).trans_lt
      (ENNReal.sum_lt_top.2 fun i _ ↦ h i)⟩⟩

/-- Whole-space specialization of `hasFinitePerimeterIn_iff_forall_directionalPerimeter_lt_top`. -/
theorem hasFinitePerimeter_iff_forall_directionalPerimeter_lt_top
    [FiniteDimensional ℝ E] [BorelSpace E] [IsLocallyFiniteMeasure μ]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {s : Set E} (hs : NullMeasurableSet s μ) :
    HasFinitePerimeter μ s ↔ ∀ i : ι, directionalPerimeter μ ⊤ (b i) s < ⊤ :=
  hasFinitePerimeterIn_iff_forall_directionalPerimeter_lt_top b (by simpa using hs)

end InnerProductSpace

end DirectionalVariation

/-! ### Section 2: One-dimensional line-slicing inequalities for directional variation -/

section LineSlicing

private lemma locallyIntegrable_indicator_const_of_nullMeasurableSet {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] {ν : Measure X} [IsLocallyFiniteMeasure ν]
    {s : Set X} (hs : NullMeasurableSet s ν) (c : ℝ) :
    LocallyIntegrable (s.indicator fun _ ↦ c) ν := by
  refine ((locallyIntegrable_const c).indicator (measurableSet_toMeasurable ν s)).congr
    (hs.toMeasurable_ae_eq.mono fun x hx ↦ ?_)
  have hmem : x ∈ toMeasurable ν s ↔ x ∈ s := by simpa [eq_iff_iff] using hx
  by_cases hxs : x ∈ s <;> [simp [hxs, hmem.2 hxs]; simp [hxs, mt hmem.1 hxs]]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fiber slice `t ↦ ψ (y, t)` in `𝓓((⊤ : Opens ℝ), ℝ)` of `ψ : 𝓓((⊤ : Opens (E × ℝ)), ℝ)`. -/
noncomputable def sliceTestFunction (ψ : 𝓓((⊤ : Opens (E × ℝ)), ℝ)) (y : E) :
    𝓓((⊤ : Opens ℝ), ℝ) where
  toFun t := ψ (y, t)
  contDiff' := ψ.contDiff.comp (contDiff_const.prodMk contDiff_id)
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact
    (ψ.hasCompactSupport.isCompact.image continuous_snd) fun t ht ↦
      ⟨(y, t), subset_tsupport _ ht, rfl⟩
  tsupport_subset' := subset_univ _

/-- Evaluating `sliceTestFunction ψ y` at `t` gives `ψ (y, t)`. -/
@[simp] theorem sliceTestFunction_apply (ψ : 𝓓((⊤ : Opens (E × ℝ)), ℝ)) (y : E) (t : ℝ) :
    sliceTestFunction ψ y t = ψ (y, t) := by rfl

/-- The derivative of `sliceTestFunction ψ y` at `t` equals `fderiv ℝ ψ (y, t) (0, 1)`. -/
theorem hasDerivAt_sliceTestFunction (ψ : 𝓓((⊤ : Opens (E × ℝ)), ℝ)) (y : E) (t : ℝ) :
    HasDerivAt (sliceTestFunction ψ y : ℝ → ℝ) (fderiv ℝ (ψ : E × ℝ → ℝ) (y, t) (0, 1)) t := by
  have hd : HasFDerivAt (ψ : E × ℝ → ℝ) (fderiv ℝ (ψ : E × ℝ → ℝ) (y, t)) (y, t) :=
    (ψ.contDiff.differentiable (by simp) (y, t)).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ ↦ (y, s)) ((0 : E), (1 : ℝ)) t := by
    have hfun : (fun s : ℝ ↦ (y, s)) = fun s ↦ (y, (0 : ℝ)) + s • ((0 : E), (1 : ℝ)) := by
      ext s <;> simp
    rw [hfun]
    simpa using ((hasDerivAt_id t).smul_const ((0 : E), (1 : ℝ))).const_add (y, (0 : ℝ))
  exact hd.comp_hasDerivAt t hline

/-- The 1D divergence of `sliceTestFunction ψ y` at `t` equals `fderiv ℝ ψ (y, t) (0, 1)`. -/
theorem divergence_sliceTestFunction (ψ : 𝓓((⊤ : Opens (E × ℝ)), ℝ)) (y : E) (t : ℝ) :
    divergence (sliceTestFunction ψ y : ℝ → ℝ) t = fderiv ℝ (ψ : E × ℝ → ℝ) (y, t) (0, 1) := by
  rw [divergence_eq_deriv, (hasDerivAt_sliceTestFunction ψ y t).deriv]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [SFinite μ]

/-- **1D line-slicing inequality for directional variation on `E × ℝ`**. -/
theorem directionalVariation_snd_le_lintegral_slice
    {u : E × ℝ → ℝ} (hu : LocallyIntegrable u (μ.prod (volume : Measure ℝ))) :
    directionalVariation (μ.prod (volume : Measure ℝ)) ⊤ (0, 1) u ≤
      ∫⁻ y : E, distributionalVariation volume ⊤ (fun t : ℝ ↦ u (y, t)) ∂μ := by
  refine iSup₂_le fun ψ hψ ↦ ?_
  have hint : Integrable (fun z : E × ℝ ↦ u z * fderiv ℝ (ψ : E × ℝ → ℝ) z (0, 1))
      (μ.prod (volume : Measure ℝ)) :=
    integrable_mul_fderiv_of_locallyIntegrableOn (hu.locallyIntegrableOn ⊤) ψ (0, 1)
  rw [Opens.coe_top, Measure.restrict_univ, integral_prod _ hint]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y ↦ ?_)
  rw [Real.enorm_eq_ofReal_abs]
  have hslice : (∫ t : ℝ, u (y, t) * fderiv ℝ (ψ : E × ℝ → ℝ) (y, t) (0, 1)) =
      ∫ t in ((⊤ : Opens ℝ) : Set ℝ),
        u (y, t) * divergence (sliceTestFunction ψ y : ℝ → ℝ) t := by
    simp only [Opens.coe_top, Measure.restrict_univ, divergence_sliceTestFunction]
  rw [hslice]
  exact abs_le_distributionalVariation (sliceTestFunction ψ y) (fun t ↦ hψ (y, t))
    (fun t ↦ u (y, t))

/-- **1D line-slicing inequality for directional perimeter on `E × ℝ`**. -/
theorem directionalPerimeter_snd_le_lintegral_slice [IsLocallyFiniteMeasure μ]
    {s : Set (E × ℝ)} (hs : NullMeasurableSet s (μ.prod (volume : Measure ℝ))) :
    directionalPerimeter (μ.prod (volume : Measure ℝ)) ⊤ (0, 1) s ≤
      ∫⁻ y : E, perimeter volume {t : ℝ | (y, t) ∈ s} ∂μ := by
  refine (directionalVariation_snd_le_lintegral_slice
    (locallyIntegrable_indicator_const_of_nullMeasurableSet hs 1)).trans (lintegral_mono fun y ↦ ?_)
  have heq : (fun t : ℝ ↦ s.indicator (fun _ ↦ (1 : ℝ)) (y, t)) =
      {t : ℝ | (y, t) ∈ s}.indicator (fun _ ↦ (1 : ℝ)) := by
    ext t; by_cases h : (y, t) ∈ s <;> simp [h]
  rw [perimeter, relativePerimeter, heq]

/-- Coordinate-line slice `t ↦ ψ (boxSlice i x' t)` in `𝓓((⊤ : Opens ℝ), ℝ)`. -/
noncomputable def boxSliceTestFunction {n : ℕ}
    (ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (i : Fin n)
    (x' : {k : Fin n // k ≠ i} → ℝ) : 𝓓((⊤ : Opens ℝ), ℝ) where
  toFun t := ψ (boxSlice i x' t)
  contDiff' := by
    rw [funext (boxSlice_eq_add_smul i x')]
    exact ψ.contDiff.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact
    (ψ.hasCompactSupport.isCompact.image (PiLp.continuous_apply 2 _ i)) fun t ht ↦
      ⟨boxSlice i x' t, subset_tsupport _ ht, boxSlice_apply_eq i x' t⟩
  tsupport_subset' := subset_univ _

/-- Evaluating `boxSliceTestFunction ψ i x'` at `t` gives `ψ (boxSlice i x' t)`. -/
@[simp] theorem boxSliceTestFunction_apply {n : ℕ}
    (ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (i : Fin n)
    (x' : {k : Fin n // k ≠ i} → ℝ) (t : ℝ) :
    boxSliceTestFunction ψ i x' t = ψ (boxSlice i x' t) := by rfl

/-- Divergence of `boxSliceTestFunction ψ i x'` at `t` along `EuclideanSpace.single i 1`. -/
theorem divergence_boxSliceTestFunction {n : ℕ}
    (ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (i : Fin n)
    (x' : {k : Fin n // k ≠ i} → ℝ) (t : ℝ) :
    divergence (boxSliceTestFunction ψ i x' : ℝ → ℝ) t =
      fderiv ℝ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (boxSlice i x' t)
        (EuclideanSpace.single i (1 : ℝ)) := by
  have hd : HasFDerivAt (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
      (fderiv ℝ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (boxSlice i x' t)) (boxSlice i x' t) :=
    (ψ.contDiff.differentiable (by simp) _).hasFDerivAt
  rw [divergence_eq_deriv]; exact (hd.comp_hasDerivAt t (hasDerivAt_boxSlice i x' t)).deriv

/-- **Coordinate line-slicing inequality for directional variation**. -/
theorem directionalVariation_single_le_lintegral_boxSlice {n : ℕ} (i : Fin n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : LocallyIntegrable u volume) :
    directionalVariation volume ⊤ (EuclideanSpace.single i (1 : ℝ)) u ≤
      ∫⁻ x' : ({k : Fin n // k ≠ i} → ℝ),
        distributionalVariation volume ⊤ (fun t : ℝ ↦ u (boxSlice i x' t)) := by
  refine iSup₂_le fun ψ hψ ↦ ?_
  set e := EuclideanSpace.single i (1 : ℝ)
  set F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x ↦ u x * fderiv ℝ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) x e
  have hF_int : Integrable F volume :=
    integrable_mul_fderiv_of_locallyIntegrableOn (hu.locallyIntegrableOn ⊤) ψ e
  have hmp := (measurePreserving_euclideanSplitAt i).symm
  have hF_prod : Integrable (F ∘ (euclideanSplitAt i).symm) (volume.prod volume) :=
    (hmp.integrable_comp_emb (euclideanSplitAt i).symm.measurableEmbedding).2 hF_int
  have hint_eq : ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))),
      F x = ∫ x', ∫ t, F (boxSlice i x' t) := by
    rw [Opens.coe_top, Measure.restrict_univ,
      ← hmp.integral_comp (euclideanSplitAt i).symm.measurableEmbedding F]
    exact integral_prod_symm (F ∘ (euclideanSplitAt i).symm) hF_prod
  rw [hint_eq]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x' ↦ ?_)
  rw [Real.enorm_eq_ofReal_abs]
  have hslice : (∫ t : ℝ, F (boxSlice i x' t)) =
      ∫ t in ((⊤ : Opens ℝ) : Set ℝ),
        u (boxSlice i x' t) * divergence (boxSliceTestFunction ψ i x' : ℝ → ℝ) t := by
    simp only [F, e, Opens.coe_top, Measure.restrict_univ, divergence_boxSliceTestFunction]
  rw [hslice]
  exact abs_le_distributionalVariation (boxSliceTestFunction ψ i x')
    (fun t ↦ hψ (boxSlice i x' t)) (fun t ↦ u (boxSlice i x' t))

/-- **Coordinate line-slicing inequality for directional perimeter**. -/
theorem directionalPerimeter_single_le_lintegral_boxSlice {n : ℕ} (i : Fin n)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : NullMeasurableSet s volume) :
    directionalPerimeter volume ⊤ (EuclideanSpace.single i (1 : ℝ)) s ≤
      ∫⁻ x' : ({k : Fin n // k ≠ i} → ℝ),
        perimeter volume {t : ℝ | boxSlice i x' t ∈ s} := by
  refine (directionalVariation_single_le_lintegral_boxSlice i
    (locallyIntegrable_indicator_const_of_nullMeasurableSet hs 1)).trans
    (lintegral_mono fun x' ↦ ?_)
  have heq : (fun t : ℝ ↦ s.indicator (fun _ ↦ (1 : ℝ)) (boxSlice i x' t)) =
      {t : ℝ | boxSlice i x' t ∈ s}.indicator (fun _ ↦ (1 : ℝ)) := by
    ext t; by_cases h : boxSlice i x' t ∈ s <;> simp [h]
  rw [perimeter, relativePerimeter, heq]

end LineSlicing

/-! ### Section 3: One-dimensional `OrdConnected` interval perimeter characterization -/

section OrdConnectedPerimeter

/-- Any `OrdConnected` subset `I : Set ℝ` of finite Lebesgue measure is bounded above. -/
theorem _root_.Set.OrdConnected.bddAbove_of_volume_lt_top {I : Set ℝ} (hI : I.OrdConnected)
    (htop : volume I < ⊤) : BddAbove I := by
  rcases I.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact bddAbove_empty
  · refine ⟨x₀ + (volume I).toReal, fun y hy ↦ ?_⟩
    rcases le_or_gt x₀ y with hle | hlt
    · have hsub : ENNReal.ofReal (y - x₀) ≤ volume I :=
        Real.volume_Icc ▸ measure_mono (hI.out hx₀ hy)
      have hle' := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop.ne).2 hsub
      rw [ENNReal.toReal_ofReal (sub_nonneg.2 hle)] at hle'; linarith
    · linarith [ENNReal.toReal_nonneg (a := volume I)]

/-- Any `OrdConnected` subset `I : Set ℝ` of finite Lebesgue measure is bounded below. -/
theorem _root_.Set.OrdConnected.bddBelow_of_volume_lt_top {I : Set ℝ} (hI : I.OrdConnected)
    (htop : volume I < ⊤) : BddBelow I := by
  rcases I.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact bddBelow_empty
  · refine ⟨x₀ - (volume I).toReal, fun y hy ↦ ?_⟩
    rcases le_or_gt y x₀ with hle | hlt
    · have hsub : ENNReal.ofReal (x₀ - y) ≤ volume I :=
        Real.volume_Icc ▸ measure_mono (hI.out hy hx₀)
      have hle' := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop.ne).2 hsub
      rw [ENNReal.toReal_ofReal (sub_nonneg.2 hle)] at hle'; linarith
    · linarith [ENNReal.toReal_nonneg (a := volume I)]

/-- For any bounded `OrdConnected` subset `I : Set ℝ`, `Ioo (sInf I) (sSup I) ⊆ I`. -/
theorem _root_.Set.OrdConnected.Ioo_sInf_sSup_subset {I : Set ℝ} (hI : I.OrdConnected)
    (hbdd₁ : BddBelow I) (hbdd₂ : BddAbove I) : Ioo (sInf I) (sSup I) ⊆ I := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp [Real.sInf_empty, Real.sSup_empty]
  · intro t ht
    obtain ⟨x, hx, hxt⟩ := (csInf_lt_iff hbdd₁ hne).1 ht.1
    obtain ⟨y, hy, hty⟩ := (lt_csSup_iff hbdd₂ hne).1 ht.2
    exact hI.out hx hy ⟨hxt.le, hty.le⟩

/-- Any bounded subset `I : Set ℝ` is contained in `Icc (sInf I) (sSup I)`. -/
theorem subset_Icc_sInf_sSup {I : Set ℝ} (hbdd₁ : BddBelow I) (hbdd₂ : BddAbove I) :
    I ⊆ Icc (sInf I) (sSup I) := fun _ hx ↦ ⟨csInf_le hbdd₁ hx, le_csSup hbdd₂ hx⟩

/-- Every finite-measure `OrdConnected` set `I : Set ℝ` is a.e. equal to `Ioo (sInf I) (sSup I)`. -/
theorem _root_.Set.OrdConnected.ae_eq_Ioo_sInf_sSup {I : Set ℝ} (hI : I.OrdConnected)
    (htop : volume I < ⊤) : I =ᵐ[volume] Ioo (sInf I) (sSup I) := by
  have hbdd₁ := hI.bddBelow_of_volume_lt_top htop
  have hbdd₂ := hI.bddAbove_of_volume_lt_top htop
  rw [ae_eq_set]
  refine ⟨measure_mono_null (sdiff_le_sdiff_right (subset_Icc_sInf_sSup hbdd₁ hbdd₂))
    (ae_eq_set.1 Ioo_ae_eq_Icc.symm).1, ?_⟩
  rw [sdiff_eq_empty.2 (hI.Ioo_sInf_sSup_subset hbdd₁ hbdd₂), measure_empty]

/-- For any `OrdConnected` set `I : Set ℝ` with `0 < volume I < ⊤`, `sInf I < sSup I`. -/
theorem _root_.Set.OrdConnected.sInf_lt_sSup_of_volume_pos {I : Set ℝ} (hI : I.OrdConnected)
    (h0 : 0 < volume I) (htop : volume I < ⊤) : sInf I < sSup I := by
  have hvol : volume I = ENNReal.ofReal (sSup I - sInf I) := by
    rw [measure_congr (hI.ae_eq_Ioo_sInf_sSup htop), Real.volume_Ioo]
  rwa [hvol, ENNReal.ofReal_pos, sub_pos] at h0

/-- **Exact perimeter of any `OrdConnected` interval of positive finite measure**. -/
theorem _root_.Set.OrdConnected.perimeter_eq_two {I : Set ℝ} (hI : I.OrdConnected)
    (h0 : 0 < volume I) (htop : volume I < ⊤) : perimeter volume I = 2 := by
  rw [perimeter_congr_ae (hI.ae_eq_Ioo_sInf_sSup htop),
    perimeter_Ioo (hI.sInf_lt_sSup_of_volume_pos h0 htop)]

/-- **Dichotomy for the perimeter of a finite-measure `OrdConnected` set**. -/
theorem _root_.Set.OrdConnected.perimeter_eq_two_or_zero {I : Set ℝ} (hI : I.OrdConnected)
    (htop : volume I < ⊤) [Decidable (0 < volume I)] :
    perimeter volume I = if 0 < volume I then 2 else 0 := by
  split_ifs with h0
  · exact hI.perimeter_eq_two h0 htop
  · rw [perimeter_congr_ae (ae_eq_empty.2 (nonpos_iff_eq_zero.1 (not_lt.1 h0))), perimeter_empty]

/-- Every finite-measure `OrdConnected` subset `I : Set ℝ` has `perimeter volume I ≤ 2`. -/
theorem _root_.Set.OrdConnected.perimeter_le_two {I : Set ℝ} (hI : I.OrdConnected)
    (htop : volume I < ⊤) : perimeter volume I ≤ 2 := by
  classical rw [hI.perimeter_eq_two_or_zero htop]; split_ifs <;> simp

/-- Every finite-measure `OrdConnected` subset `I : Set ℝ` has finite perimeter. -/
theorem _root_.Set.OrdConnected.hasFinitePerimeter_of_volume_lt_top {I : Set ℝ}
    (hI : I.OrdConnected) (htop : volume I < ⊤) : HasFinitePerimeter volume I := by
  refine ⟨?_, (hI.perimeter_le_two htop).trans_lt ENNReal.ofNat_lt_top⟩
  rw [Opens.coe_top, Measure.restrict_univ]
  exact measurableSet_Ioo.nullMeasurableSet.congr (hI.ae_eq_Ioo_sInf_sSup htop).symm

end OrdConnectedPerimeter

/-! ### Section 4: Lattice operations and Lipschitz scalar composition in BV -/

section LatticeAndLipschitzBV

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

omit [BorelSpace E] in
/-- Composing `LocallyIntegrableOn u Ω μ` with `LipschitzWith K f` is `LocallyIntegrableOn`. -/
theorem _root_.LipschitzWith.locallyIntegrableOn_comp {K : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ) :
    LocallyIntegrableOn (f ∘ u) Ω μ := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu ⊢
  intro C hCΩ hC
  have huC := hu C hCΩ hC
  refine ((huC.norm.const_mul (K : ℝ)).add
    (integrableOn_const (C := ‖f 0‖) hC.measure_lt_top.ne)).mono'
    (hf.continuous.comp_aestronglyMeasurable huC.aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ ?_)
  dsimp only [Pi.add_apply, Function.comp_apply]
  have hdist := hf.dist_le_mul (u x) 0
  rw [dist_eq_norm, dist_zero_right] at hdist
  linarith [norm_le_norm_sub_add (f (u x)) (f 0)]

/-- **Upper truncation coarea inequality** for `max (u x) c`. -/
theorem distributionalVariation_max_const_le {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ)
    (c : ℝ) : distributionalVariation μ Ω (fun x ↦ max (u x) c) ≤
      ∫⁻ t in Ioi c, relativePerimeter μ Ω {x | t < u x} := by
  have hmax : LocallyIntegrableOn (fun x ↦ max (u x) c) Ω μ := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu ⊢
    exact fun K hKΩ hK ↦ (hu K hKΩ hK).sup (integrableOn_const hK.measure_lt_top.ne)
  refine (distributionalVariation_le_lintegral_relativePerimeter_real hmax).trans ?_
  have h_ind : (fun t : ℝ ↦ relativePerimeter μ Ω {x | t < max (u x) c}) =
      (Ici c).indicator (fun t : ℝ ↦ relativePerimeter μ Ω {x | t < u x}) := by
    ext t; by_cases htc : t ∈ Ici c
    · rw [indicator_of_mem htc]; congr 1; ext x; simp [lt_max_iff, not_lt.2 (mem_Ici.1 htc)]
    · rw [indicator_of_notMem htc, show {x | t < max (u x) c} = univ by
        ext x; simp [lt_max_iff, not_le.1 (mt mem_Ici.2 htc)], relativePerimeter_univ]
  rw [h_ind, lintegral_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]

/-- **Lower truncation coarea inequality** for `min (u x) c`. -/
theorem distributionalVariation_min_const_le {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ)
    (c : ℝ) : distributionalVariation μ Ω (fun x ↦ min (u x) c) ≤
      ∫⁻ t in Iio c, relativePerimeter μ Ω {x | t < u x} := by
  have hmin : LocallyIntegrableOn (fun x ↦ min (u x) c) Ω μ := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu ⊢
    exact fun K hKΩ hK ↦ (hu K hKΩ hK).inf (integrableOn_const hK.measure_lt_top.ne)
  refine (distributionalVariation_le_lintegral_relativePerimeter_real hmin).trans ?_
  have h_ind : (fun t : ℝ ↦ relativePerimeter μ Ω {x | t < min (u x) c}) =
      (Iio c).indicator (fun t : ℝ ↦ relativePerimeter μ Ω {x | t < u x}) := by
    ext t; by_cases htc : t ∈ Iio c
    · rw [indicator_of_mem htc]; congr 1; ext x; simp [lt_min_iff, mem_Iio.1 htc]
    · rw [indicator_of_notMem htc, show {x | t < min (u x) c} = ∅ by
        ext x; simp [lt_min_iff, mt mem_Iio.2 htc], relativePerimeter_empty]
  rw [h_ind, lintegral_indicator measurableSet_Iio]

/-- **Absolute-value coarea inequality** for `|u x|`. -/
theorem distributionalVariation_abs_le_lintegral_relativePerimeter {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) : distributionalVariation μ Ω (fun x ↦ |u x|) ≤
      ∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x} := by
  have habs : (fun x ↦ |u x|) = (fun x ↦ max (u x) 0) + (fun x ↦ -min (u x) 0) := by
    ext x; rcases le_total 0 (u x) with h | h <;> simp [abs_of_nonneg, abs_of_nonpos, h]
  have hmax : LocallyIntegrableOn (fun x ↦ max (u x) 0) Ω μ := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu ⊢
    exact fun K hKΩ hK ↦ (hu K hKΩ hK).sup (integrableOn_const hK.measure_lt_top.ne)
  have hmin : LocallyIntegrableOn (fun x ↦ -min (u x) 0) Ω μ := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu ⊢
    exact fun K hKΩ hK ↦ ((hu K hKΩ hK).inf (integrableOn_const hK.measure_lt_top.ne)).neg
  rw [habs]
  refine (distributionalVariation_add_le hmax hmin).trans ?_
  rw [distributionalVariation_fun_neg]
  refine (add_le_add (distributionalVariation_max_const_le hu 0)
    (distributionalVariation_min_const_le hu 0)).trans ?_
  have hdisj : Disjoint (Ioi (0 : ℝ)) (Iio 0) :=
    Set.disjoint_left.2 fun _ h1 h2 ↦ lt_asymm h1 h2
  rw [← lintegral_union measurableSet_Iio hdisj]; exact setLIntegral_le_lintegral _ _

/-- **1D fundamental theorem of calculus for a Lipschitz function on a level truncation**. -/
theorem _root_.LipschitzWith.clamp_sub_eq_setIntegral_indicator_deriv {K : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    f (min (max y a) b) - f a = ∫ t in Ioo a b, {t : ℝ | t < y}.indicator (deriv f) t := by
  set c := min (max y a) b
  have hac : a ≤ c := le_min (le_max_right y a) hab
  have hsub : f c - f a = ∫ t in Ioo a c, deriv f t := by
    rw [← hf.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub,
      intervalIntegral.integral_of_le hac, integral_Ioc_eq_integral_Ioo]
  rw [hsub, show {t : ℝ | t < y} = Iio y from rfl, setIntegral_indicator measurableSet_Iio]
  have hinter : Ioo a b ∩ Iio y = Ioo a c := by
    ext t; simp only [mem_inter_iff, mem_Ioo, mem_Iio, c, lt_min_iff, lt_max_iff]
    refine ⟨fun ⟨⟨hat, htb⟩, hty⟩ ↦ ⟨hat, Or.inl hty, htb⟩, ?_⟩
    rintro ⟨hat, hty | hta, htb⟩
    · exact ⟨⟨hat, htb⟩, hty⟩
    · linarith
  rw [hinter]

private lemma integral_lipschitz_clamp_mul_divergence_of_measurable {K : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a ≤ b) {u : E → ℝ} (hu_meas : Measurable u)
    (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), f (min (max (u x) a) b) * divergence (φ : E → E) x ∂μ =
      ∫ t in Ioo a b, deriv f t *
        (∫ x in (Ω : Set E),
          {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) := by
  let ν := volume.restrict (Ioo a b)
  let μΩ := μ.restrict (Ω : Set E)
  let S : Set (E × ℝ) := {p : E × ℝ | p.2 < u p.1}
  have hS : MeasurableSet S := measurableSet_lt measurable_snd (hu_meas.comp measurable_fst)
  let F : E × ℝ → ℝ := S.indicator fun p ↦ deriv f p.2 * divergence (φ : E → E) p.1
  have hF_meas : Measurable F :=
    (((measurable_deriv f).comp measurable_snd).mul
      ((continuous_divergence_testFunction φ).measurable.comp measurable_fst)).indicator hS
  have hF_slice : ∀ x t, F (x, t) =
      deriv f t * ({y | t < u y}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x) := by
    intro x t; by_cases h : t < u x <;> simp [F, S, h]
  have hF_slice' : ∀ x t, F (x, t) =
      ({t : ℝ | t < u x}.indicator (deriv f) t) * divergence (φ : E → E) x := by
    intro x t; by_cases h : t < u x <;> simp [F, S, h]
  have hF_int : Integrable F (μΩ.prod ν) := by
    have hdom : Integrable (fun p : E × ℝ ↦ ‖divergence (φ : E → E) p.1‖ * (K : ℝ)) (μΩ.prod ν) :=
      (integrableOn_divergence_testFunction (μ := μ) φ).norm.mul_prod
        (integrableOn_const (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
    refine hdom.mono' hF_meas.aestronglyMeasurable (Eventually.of_forall fun p ↦ ?_)
    dsimp only [F]
    refine (norm_indicator_le_norm_self _ p).trans ?_
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hf) (norm_nonneg _)
  have hL : (∫ x, ∫ t, F (x, t) ∂ν ∂μΩ) =
      ∫ x in (Ω : Set E), f (min (max (u x) a) b) * divergence (φ : E → E) x ∂μ := by
    rw [← integral_add_const_mul_divergence (fun x ↦ f (min (max (u x) a) b)) (-f a) φ]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [integral_congr_ae (Eventually.of_forall fun t ↦ hF_slice' x t), integral_mul_const]
    change (∫ t in Ioo a b, {t : ℝ | t < u x}.indicator (deriv f) t) *
        divergence (φ : E → E) x = _
    rw [← hf.clamp_sub_eq_setIntegral_indicator_deriv hab, sub_eq_add_neg]
  rw [← hL, ← integral_prod F hF_int, integral_prod_symm F hF_int]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp_rw [hF_slice _ t, integral_const_mul]; rfl

/-- **Truncated Lipschitz composition layer-cake identity**. -/
theorem _root_.LipschitzWith.integral_clamp_mul_divergence_eq_integral_superlevel
    {K : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith K f) {a b : ℝ} (hab : a ≤ b) {u : E → ℝ}
    (hu : AEStronglyMeasurable u (μ.restrict Ω)) (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), f (min (max (u x) a) b) * divergence (φ : E → E) x ∂μ =
      ∫ t in Ioo a b, deriv f t *
        (∫ x in (Ω : Set E),
          {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) := by
  let v : E → ℝ := hu.mk u
  have hv_meas : Measurable v := hu.stronglyMeasurable_mk.measurable
  have huv : u =ᵐ[μ.restrict Ω] v := hu.ae_eq_mk
  have hL : ∫ x in (Ω : Set E), f (min (max (u x) a) b) * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω : Set E), f (min (max (v x) a) b) * divergence (φ : E → E) x ∂μ :=
    integral_congr_ae (huv.mono fun x hx ↦ by dsimp only; rw [hx])
  have hR : ∀ t : ℝ,
      ∫ x in (Ω : Set E),
        {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω : Set E),
        {x | t < v x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ := fun t ↦ by
    refine integral_congr_ae (huv.mono fun x hx ↦ ?_)
    by_cases h : t < u x <;> [have hv : t < v x := hx ▸ h; have hv : ¬ t < v x := hx ▸ h] <;>
      simp [h, hv]
  rw [hL, integral_lipschitz_clamp_mul_divergence_of_measurable hf hab hv_meas φ]; simp_rw [hR]

/-- **Truncated Lipschitz composition coarea bound**. -/
theorem _root_.LipschitzWith.distributionalVariation_clamp_le_lintegral_relativePerimeter
    {K : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith K f) {a b : ℝ} (hab : a ≤ b) {u : E → ℝ}
    (hu : AEStronglyMeasurable u (μ.restrict Ω)) :
    distributionalVariation μ Ω (fun x ↦ f (min (max (u x) a) b)) ≤
      (K : ℝ≥0∞) * ∫⁻ t in Ioo a b, relativePerimeter μ Ω {x | t < u x} := by
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [hf.integral_clamp_mul_divergence_eq_integral_superlevel hab hu φ]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [← Real.enorm_eq_ofReal_abs, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t ↦ ?_)
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  refine mul_le_mul' ?_
    (abs_le_distributionalVariation φ hφ ({x | t < u x}.indicator fun _ ↦ (1 : ℝ)))
  rw [← Real.norm_eq_abs, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (norm_deriv_le_of_lipschitz hf)

/-- **Lipschitz scalar composition coarea bound**. -/
theorem distributionalVariation_comp_lipschitz_le_lintegral_relativePerimeter
    {K : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith K f) {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) :
    distributionalVariation μ Ω (f ∘ u) ≤
      (K : ℝ≥0∞) * ∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x} := by
  refine iSup₂_le fun φ hφ ↦ ?_
  have hconv : Tendsto
      (fun n : ℕ ↦ ∫ x in (Ω : Set E),
        f (min (max (u x) (-(n : ℝ))) (n : ℝ)) * divergence (φ : E → E) x ∂μ)
      atTop (𝓝 (∫ x in (Ω : Set E), (f ∘ u) x * divergence (φ : E → E) x ∂μ)) := by
    have hdiv_aesm : AEStronglyMeasurable (fun x ↦ divergence (φ : E → E) x) (μ.restrict Ω) :=
      (continuous_divergence_testFunction φ).aestronglyMeasurable
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ ((K : ℝ) * ‖u x‖ + ‖f 0‖) * ‖divergence (φ : E → E) x‖) ?_ ?_ ?_ ?_
    · exact fun n ↦ (hf.continuous.comp_aestronglyMeasurable
        ((hu.aestronglyMeasurable.sup aestronglyMeasurable_const).inf
          aestronglyMeasurable_const)).mul hdiv_aesm
    · have h1 := (integrableOn_mul_divergence_of_locallyIntegrableOn hu φ).norm.const_mul (K : ℝ)
      have h2 := ((integrableOn_divergence_testFunction (μ := μ) φ).const_mul (f 0)).norm
      refine (h1.add h2).congr (Eventually.of_forall fun x ↦ ?_)
      dsimp only [Pi.add_apply]; rw [norm_mul, norm_mul]; ring
    · refine fun n ↦ ae_of_all _ fun x ↦ ?_
      set y := min (max (u x) (-(n : ℝ))) (n : ℝ)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hy : ‖y‖ ≤ ‖u x‖ := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le]
        exact ⟨le_min (le_trans (neg_abs_le _) (le_max_left _ _)) (by linarith [abs_nonneg (u x)]),
          min_le_of_left_le (max_le (le_abs_self _) (by linarith [abs_nonneg (u x)]))⟩
      have hdist := hf.dist_le_mul y 0
      rw [dist_eq_norm, dist_zero_right] at hdist
      have hfy : ‖f y‖ ≤ (K : ℝ) * ‖u x‖ + ‖f 0‖ := by
        have := mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg K)
        linarith [norm_le_norm_sub_add (f y) (f 0)]
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right hfy (norm_nonneg _)
    · refine ae_of_all _ fun x ↦ tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|u x|⌉₊] with n hn
      have hle : |u x| ≤ n := (Nat.le_ceil |u x|).trans (Nat.cast_le.2 hn)
      rw [abs_le] at hle; simp [Function.comp_apply, max_eq_left hle.1, min_eq_left hle.2]
  have hlim := (ENNReal.continuous_ofReal.tendsto _).comp hconv
  refine le_of_tendsto' hlim fun n ↦ ?_
  have hn : (-(n : ℝ)) ≤ (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (le_distributionalVariation φ hφ _).trans
    ((hf.distributionalVariation_clamp_le_lintegral_relativePerimeter hn
      hu.aestronglyMeasurable).trans
      (mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le))

/-- Whole-space form of `distributionalVariation_comp_lipschitz_le_lintegral_relativePerimeter`. -/
theorem distributionalVariation_top_comp_lipschitz_le_lintegral_perimeter
    {K : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith K f) {u : E → ℝ} (hu : LocallyIntegrable u μ) :
    distributionalVariation μ ⊤ (f ∘ u) ≤
      (K : ℝ≥0∞) * ∫⁻ t : ℝ, perimeter μ {x | t < u x} :=
  distributionalVariation_comp_lipschitz_le_lintegral_relativePerimeter hf
    (hu.locallyIntegrableOn (⊤ : Opens E))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Composing `IntegrableOn u Ω μ` with `LipschitzWith K f` (`f 0 = 0`) preserves `IntegrableOn`. -/
theorem _root_.LipschitzWith.integrableOn_comp_of_map_zero {K : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) (hf0 : f 0 = 0) {u : E → ℝ} (hu : IntegrableOn u Ω μ) :
    IntegrableOn (f ∘ u) Ω μ := by
  refine (hu.norm.const_mul (K : ℝ)).mono'
    (hf.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ ?_)
  have h := hf.dist_le_mul (u x) 0
  rwa [hf0, dist_zero_right, dist_zero_right] at h

/-- Composing `IntegrableOn u Ω μ` with `LipschitzWith K f` (`f 0 = 0`) preserves `IsBVOn`. -/
theorem _root_.LipschitzWith.isBVOn_comp_of_map_zero {K : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) (hf0 : f 0 = 0) {u : E → ℝ} (hu : IntegrableOn u Ω μ)
    (hper : ∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x} < ⊤) :
    IsBVOn μ Ω (f ∘ u) :=
  ⟨hf.integrableOn_comp_of_map_zero hf0 hu,
    (distributionalVariation_comp_lipschitz_le_lintegral_relativePerimeter hf
      hu.locallyIntegrableOn).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hper)⟩

end LatticeAndLipschitzBV

end TauCeti
