/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport

/-!
# Smooth cutoffs, level truncations, the full signed coarea inequality, and disjoint-union perimeter

This file develops the calculus of smooth cutoffs, level truncations, the full signed scalar BV
coarea inequality on `ℝ`, and disjoint-union and nested-difference perimeter bounds:

1. **Divergence product rule and smooth cutoff test vector fields**: for a scalar function
   `η : E → ℝ` differentiable at `x` and a vector field `φ : E → E` differentiable at `x`,
   `divergence (fun y ↦ η y • φ y) x = η x * divergence φ x + fderiv ℝ η x (φ x)`. When `η` is
   smooth (`ContDiff ℝ ⊤ η`) and `φ : 𝓓(Ω, E)`, pointwise scalar multiplication defines a bundled
   test vector field `smulTestFunction hη φ : 𝓓(Ω, E)`.
2. **Multiplication of `BV` and `BV_loc` functions by smooth cutoffs**: for any locally integrable
   function `u` on `Ω` and smooth `η`, the integral of `(η * u) * divergence φ` decomposes via the
   divergence product rule into the pairing of `u` with `divergence (smulTestFunction hη φ)` minus
   the lower-order drift `∫ x in Ω, u x * fderiv ℝ η x (φ x) ∂μ`. Taking the supremum over unit
   test vector fields yields the smooth cutoff variation estimate
   `distributionalVariation μ Ω (fun x ↦ η x * u x) ≤
     ENNReal.ofReal M * distributionalVariation μ Ω u + ∫⁻ x in Ω, ‖u x‖ₑ * ‖fderiv ℝ η x‖ₑ ∂μ`,
   showing that `IsBVOn` is preserved under multiplication by bounded smooth functions with bounded
   derivative, and that `IsLocallyBVOn` functions restrict to `IsBVOn` on relatively compact open
   subsets `U` with `closure U ⊆ Ω`.
3. **Truncation layer-cake formula and full signed scalar BV coarea inequality**: for any `a ≤ b`
   and `AEStronglyMeasurable u (μ.restrict Ω)`, the level truncation `min (max (u x) a) b` satisfies
   `∫ x in Ω, min (max (u x) a) b * divergence φ x ∂μ =
     ∫ t in Ioo a b, (∫ x in Ω, {x | t < u x}.indicator 1 x * divergence φ x ∂μ)` and
   `distributionalVariation μ Ω (fun x ↦ min (max (u x) a) b) ≤
     ∫⁻ t in Ioo a b, relativePerimeter μ Ω {x | t < u x}`. Letting `a = -n` and `b = n` as
   `n → ∞` via dominated convergence yields the full signed scalar BV coarea inequality on `ℝ`,
   `distributionalVariation μ Ω u ≤ ∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x}`, without any
   nonnegativity assumption on `u`.
4. **Disjoint-union and nested set-difference perimeter bounds**: if `s` and `t` are a.e. disjoint
   in `Ω`, then `relativePerimeter μ Ω (s ∪ t) ≤ relativePerimeter μ Ω s + relativePerimeter μ Ω t`.
   Combining this with complement invariance yields `relativePerimeter μ Ω (s \ t) ≤
   relativePerimeter μ Ω s + relativePerimeter μ Ω t` for nested sets `t ⊆ s`, and in particular
   for concentric annuli `closedBall c R \ ball c r`.

## Main results

* `TauCeti.divergence_smul`, `TauCeti.smulTestFunction`, `TauCeti.divergence_smulTestFunction`:
  Leibniz product rule for `divergence` and bundled smooth scalar multiplication on `𝓓(Ω, E)`.
* `TauCeti.integral_smul_mul_divergence`, `TauCeti.distributionalVariation_mul_smooth_le`,
  `TauCeti.IsBVOn.mul_smooth_of_bounded`, `TauCeti.IsLocallyBVOn.isBVOn_of_isCompact_closure`,
  `TauCeti.IsLocallyBVOn.isBVOn_mul_smooth_of_isCompact_closure`: smooth cutoff estimates for `BV`
  and `BV_loc`.
* `TauCeti.clamp_sub_eq_setIntegral_indicator`,
  `TauCeti.integral_clamp_mul_divergence_eq_integral_superlevel`,
  `TauCeti.distributionalVariation_min_max_le_lintegral_relativePerimeter`,
  `TauCeti.tendsto_integral_clamp_nat_mul_divergence`,
  `TauCeti.integral_mul_divergence_eq_integral_superlevel_real`,
  `TauCeti.distributionalVariation_le_lintegral_relativePerimeter_real`: truncation layer-cake
  formulas and the full signed scalar BV coarea inequality on `ℝ`.
* `TauCeti.relativePerimeter_union_le_of_ae_disjoint`,
  `TauCeti.relativePerimeter_union_le_of_disjoint`, `TauCeti.perimeter_union_le_of_disjoint`,
  `TauCeti.relativePerimeter_diff_le_of_subset`, `TauCeti.perimeter_diff_le_of_subset`,
  `TauCeti.perimeter_closedBall_diff_ball_le`: disjoint-union and nested-difference perimeter
  inequalities.
-/

public section

open Filter Function MeasureTheory Pointwise Set TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Distributions Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-! ### Part 1: Divergence Leibniz / product rule and smooth cutoff test vector fields -/

section DivergenceProductRule

/-- **Leibniz product rule for divergence**: for a scalar function `η : E → ℝ` differentiable at `x`
and a vector field `φ : E → E` differentiable at `x`,
`divergence (fun y ↦ η y • φ y) x = η x * divergence φ x + fderiv ℝ η x (φ x)`. -/
theorem divergence_smul [FiniteDimensional ℝ E] {η : E → ℝ} {φ : E → E} {x : E}
    (hη : DifferentiableAt ℝ η x) (hφ : DifferentiableAt ℝ φ x) :
    divergence (fun y ↦ η y • φ y) x = η x * divergence φ x + fderiv ℝ η x (φ x) := by
  let b := stdOrthonormalBasis ℝ E
  rw [divergence_eq_sum_orthonormalBasis b, divergence_eq_sum_orthonormalBasis b, Finset.mul_sum]
  have hsum : fderiv ℝ η x (φ x) = ∑ i, fderiv ℝ η x (b i) * ⟪b i, φ x⟫_ℝ := by
    conv_lhs => rw [← b.sum_repr' (φ x), map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]
  rw [hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (fun y ↦ η y • φ y) = η • φ from rfl, fderiv_smul hη hφ]
  simp [inner_add_right, inner_smul_right]

/-- Pointwise multiplication of a test vector field `φ : 𝓓(Ω, E)` by a smooth scalar function
`η : E → ℝ` (`ContDiff ℝ ⊤ η`) as a bundled test vector field in `𝓓(Ω, E)`. -/
noncomputable def smulTestFunction {η : E → ℝ} (hη : ContDiff ℝ ⊤ η)
    (φ : 𝓓(Ω, E)) : 𝓓(Ω, E) where
  toFun x := η x • φ x
  contDiff' := (hη.of_le le_top).smul φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.smul_left
  tsupport_subset' := (tsupport_smul_subset_right η φ).trans φ.tsupport_subset

/-- Evaluating `smulTestFunction hη φ` at `x` yields `η x • φ x`. -/
@[simp]
theorem smulTestFunction_apply {η : E → ℝ} (hη : ContDiff ℝ ⊤ η)
    (φ : 𝓓(Ω, E)) (x : E) :
    smulTestFunction hη φ x = η x • φ x := by rfl

/-- Coercing `smulTestFunction hη φ` to a function gives `fun x ↦ η x • φ x`. -/
@[simp]
theorem coe_smulTestFunction {η : E → ℝ} (hη : ContDiff ℝ ⊤ η) (φ : 𝓓(Ω, E)) :
    (smulTestFunction hη φ : E → E) = fun x ↦ η x • φ x := by rfl

/-- Divergence of the smooth cutoff test vector field `smulTestFunction hη φ`. -/
theorem divergence_smulTestFunction [FiniteDimensional ℝ E] {η : E → ℝ} (hη : ContDiff ℝ ⊤ η)
    (φ : 𝓓(Ω, E)) (x : E) :
    divergence (smulTestFunction hη φ : E → E) x =
      η x * divergence (φ : E → E) x + fderiv ℝ η x (φ x) :=
  divergence_smul (hη.differentiable (by simp) x) (φ.contDiff.differentiable (by simp) x)

end DivergenceProductRule

/-! ### Part 2: Multiplication of BV and BV_loc functions by smooth cutoffs -/

section SmoothCutoffs

variable [MeasurableSpace E] {μ : Measure E}

/-- **Leibniz integral identity for smooth cutoffs**: for any locally integrable function `u` on
`Ω`, any smooth scalar function `η : E → ℝ`, and any test vector field `φ : 𝓓(Ω, E)`,
`∫ x in Ω, (η x * u x) * divergence φ x ∂μ =
  ∫ x in Ω, u x * divergence (smulTestFunction hη φ) x ∂μ - ∫ x in Ω, u x * fderiv ℝ η x (φ x) ∂μ`.
-/
theorem integral_smul_mul_divergence [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} (hu : LocallyIntegrableOn u Ω μ) (hη : ContDiff ℝ ⊤ η) (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), (η x * u x) * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω : Set E), u x * divergence (smulTestFunction hη φ : E → E) x ∂μ -
        ∫ x in (Ω : Set E), u x * fderiv ℝ η x (φ x) ∂μ := by
  have h1' : IntegrableOn (fun x ↦ (u x * η x) * divergence (φ : E → E) x) Ω μ :=
    integrableOn_mul_divergence_of_locallyIntegrableOn
      (hu.mul_continuousOn hη.continuous.continuousOn Ω.isOpen.isLocallyClosed) φ
  have h1 : IntegrableOn (fun x ↦ (η x * u x) * divergence (φ : E → E) x) Ω μ := by
    simpa only [mul_comm (η _)] using h1'
  have h2 : IntegrableOn (fun x ↦ u x * divergence (smulTestFunction hη φ : E → E) x) Ω μ :=
    integrableOn_mul_divergence_of_locallyIntegrableOn hu (smulTestFunction hη φ)
  have hsub : (fun x ↦ u x * fderiv ℝ η x (φ x)) =
      fun x ↦ u x * divergence (smulTestFunction hη φ : E → E) x -
        (η x * u x) * divergence (φ : E → E) x := by
    ext x
    rw [divergence_smulTestFunction hη φ x]
    ring
  have h3 : IntegrableOn (fun x ↦ u x * fderiv ℝ η x (φ x)) Ω μ := hsub ▸ h2.sub h1
  have h4 : (fun x ↦ (η x * u x) * divergence (φ : E → E) x) =
      fun x ↦ u x * divergence (smulTestFunction hη φ : E → E) x -
        u x * fderiv ℝ η x (φ x) := by
    ext x
    rw [divergence_smulTestFunction hη φ x]
    ring
  rw [h4, integral_sub h2 h3]

/-- Symmetric form of `integral_smul_mul_divergence` for `(u x * η x) * divergence φ x`. -/
theorem integral_mul_smul_divergence [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} (hu : LocallyIntegrableOn u Ω μ) (hη : ContDiff ℝ ⊤ η) (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), (u x * η x) * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω : Set E), u x * divergence (smulTestFunction hη φ : E → E) x ∂μ -
        ∫ x in (Ω : Set E), u x * fderiv ℝ η x (φ x) ∂μ := by
  simpa only [mul_comm (u _)] using integral_smul_mul_divergence hu hη φ

/-- **Smooth cutoff variation bound**: if `u` is locally integrable on `Ω` and `η : E → ℝ` is
smooth with `‖η x‖ ≤ M` on `Ω` (`0 ≤ M`), then
`distributionalVariation μ Ω (fun x ↦ η x * u x) ≤
  ENNReal.ofReal M * distributionalVariation μ Ω u + ∫⁻ x in Ω, ‖u x‖ₑ * ‖fderiv ℝ η x‖ₑ ∂μ`. -/
theorem distributionalVariation_mul_smooth_le [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} {M : ℝ} (hu : LocallyIntegrableOn u Ω μ) (hη : ContDiff ℝ ⊤ η)
    (hM : 0 ≤ M) (hηM : ∀ x ∈ (Ω : Set E), ‖η x‖ ≤ M) :
    distributionalVariation μ Ω (fun x ↦ η x * u x) ≤
      ENNReal.ofReal M * distributionalVariation μ Ω u +
        ∫⁻ x in (Ω : Set E), ‖u x‖ₑ * ‖fderiv ℝ η x‖ₑ ∂μ := by
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [integral_smul_mul_divergence hu hη φ]
  set I₁ := ∫ x in (Ω : Set E), u x * divergence (smulTestFunction hη φ : E → E) x ∂μ
  set I₂ := ∫ x in (Ω : Set E), u x * fderiv ℝ η x (φ x) ∂μ
  have hle : I₁ - I₂ ≤ |I₁| + |I₂| := by linarith [le_abs_self I₁, neg_abs_le I₂]
  refine (ENNReal.ofReal_le_ofReal hle).trans ?_
  rw [ENNReal.ofReal_add (abs_nonneg I₁) (abs_nonneg I₂)]
  refine add_le_add ?_ ?_
  · rcases eq_or_lt_of_le hM with rfl | hMpos
    · simp only [ENNReal.ofReal_zero, zero_mul, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero,
        abs_nonpos_iff]
      have hψzero : (smulTestFunction hη φ : E → E) = 0 := by
        ext x
        by_cases hx : x ∈ (Ω : Set E)
        · have h0 : η x = 0 := norm_le_zero_iff.1 (hηM x hx)
          simp [h0]
        · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)
          simp [h0]
      simp [I₁, hψzero]
    · let ψ : 𝓓(Ω, E) := M⁻¹ • smulTestFunction hη φ
      have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
        change ‖M⁻¹ • (η x • φ x)‖ ≤ 1
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hM)]
        by_cases hx : x ∈ (Ω : Set E)
        · calc M⁻¹ * (‖η x‖ * ‖φ x‖) ≤ M⁻¹ * (M * 1) := by
                gcongr
                · exact hηM x hx
                · exact hφ x
            _ = 1 := by rw [mul_one, inv_mul_cancel₀ hMpos.ne']
        · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)
          simp [h0]
      have hI₁ : I₁ = M * ∫ x in (Ω : Set E), u x * divergence (ψ : E → E) x ∂μ := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ ?_
        have hdiv : divergence (ψ : E → E) x = M⁻¹ * divergence (smulTestFunction hη φ : E → E) x :=
          divergence_const_smul M⁻¹ (smulTestFunction hη φ : E → E) x
        rw [hdiv]
        calc u x * divergence (smulTestFunction hη φ : E → E) x
            = (M * M⁻¹) * (u x * divergence (smulTestFunction hη φ : E → E) x) := by
              rw [mul_inv_cancel₀ hMpos.ne', one_mul]
          _ = M * (u x * (M⁻¹ * divergence (smulTestFunction hη φ : E → E) x)) := by ring
      rw [hI₁, abs_mul, abs_of_pos hMpos, ENNReal.ofReal_mul hM]
      gcongr
      exact abs_le_distributionalVariation ψ hψ_norm u
  · rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans
      (setLIntegral_mono' Ω.isOpen.measurableSet fun x _ ↦ ?_)
    rw [enorm_mul]
    gcongr
    have hle' : ‖fderiv ℝ η x (φ x)‖ ≤ ‖fderiv ℝ η x‖ * 1 :=
      (fderiv ℝ η x).le_opNorm (φ x) |>.trans
        (mul_le_mul_of_nonneg_left (hφ x) (norm_nonneg _))
    simpa [enorm_le_iff_norm_le] using hle'

/-- Symmetric form of `distributionalVariation_mul_smooth_le` for `fun x ↦ u x * η x`. -/
theorem distributionalVariation_mul_smooth_right_le [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} {M : ℝ} (hu : LocallyIntegrableOn u Ω μ) (hη : ContDiff ℝ ⊤ η)
    (hM : 0 ≤ M) (hηM : ∀ x ∈ (Ω : Set E), ‖η x‖ ≤ M) :
    distributionalVariation μ Ω (fun x ↦ u x * η x) ≤
      ENNReal.ofReal M * distributionalVariation μ Ω u +
        ∫⁻ x in (Ω : Set E), ‖u x‖ₑ * ‖fderiv ℝ η x‖ₑ ∂μ := by
  simpa only [mul_comm (u _)] using distributionalVariation_mul_smooth_le hu hη hM hηM

/-- Multiplication by a smooth function `η` with bounded value and bounded derivative on `Ω`
preserves `IsBVOn μ Ω`. -/
theorem IsBVOn.mul_smooth_of_bounded [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} {M L : ℝ} (hu : IsBVOn μ Ω u) (hη : ContDiff ℝ ⊤ η)
    (hM : 0 ≤ M) (hηM : ∀ x ∈ (Ω : Set E), ‖η x‖ ≤ M)
    (hηL : ∀ x ∈ (Ω : Set E), ‖fderiv ℝ η x‖ ≤ L) :
    IsBVOn μ Ω (fun x ↦ η x * u x) := by
  refine ⟨hu.1.bdd_mul (hη.continuous.continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet)
    (ae_restrict_of_forall_mem Ω.isOpen.measurableSet hηM), ?_⟩
  refine (distributionalVariation_mul_smooth_le hu.1.locallyIntegrableOn hη hM hηM).trans_lt ?_
  refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2, ?_⟩
  have hle : ∫⁻ x in (Ω : Set E), ‖u x‖ₑ * ‖fderiv ℝ η x‖ₑ ∂μ ≤
      ∫⁻ x in (Ω : Set E), ‖u x‖ₑ * ENNReal.ofReal L ∂μ :=
    setLIntegral_mono' Ω.isOpen.measurableSet fun x hx ↦ by
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hηL x hx)
  rw [lintegral_mul_const'' _ hu.1.aestronglyMeasurable.enorm] at hle
  exact hle.trans_lt (ENNReal.mul_lt_top hu.1.2 ENNReal.ofReal_lt_top)

/-- Right-multiplication version of `IsBVOn.mul_smooth_of_bounded`. -/
theorem IsBVOn.mul_smooth_right_of_bounded [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} {M L : ℝ} (hu : IsBVOn μ Ω u) (hη : ContDiff ℝ ⊤ η)
    (hM : 0 ≤ M) (hηM : ∀ x ∈ (Ω : Set E), ‖η x‖ ≤ M)
    (hηL : ∀ x ∈ (Ω : Set E), ‖fderiv ℝ η x‖ ≤ L) :
    IsBVOn μ Ω (fun x ↦ u x * η x) := by
  simpa only [mul_comm (u _)] using hu.mul_smooth_of_bounded hη hM hηM hηL

/-- Every function in `IsLocallyBVOn μ Ω` restricts to `IsBVOn μ U` on any relatively compact open
subset `U` with `closure U ⊆ Ω`. -/
theorem IsLocallyBVOn.isBVOn_of_isCompact_closure {u : E → ℝ} {U : Opens E}
    (hu : IsLocallyBVOn μ Ω u) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) :
    IsBVOn μ U u :=
  ⟨(hu.1.integrableOn_compact_subset hUΩ hU).mono_set subset_closure, hu.2 U hU hUΩ⟩

/-- On an open set `U` with compact closure, multiplying any `IsBVOn μ U` function by a smooth
function `η : E → ℝ` yields a function in `IsBVOn μ U`. -/
theorem IsBVOn.mul_smooth_of_isCompact_closure [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} {U : Opens E} (hu : IsBVOn μ U u) (hU : IsCompact (closure (U : Set E)))
    (hη : ContDiff ℝ ⊤ η) :
    IsBVOn μ U (fun x ↦ η x * u x) := by
  obtain ⟨M, hM⟩ := hU.exists_bound_of_continuousOn hη.continuous.continuousOn
  obtain ⟨L, hL⟩ := hU.exists_bound_of_continuousOn
    ((hη.continuous_fderiv (by simp)).continuousOn)
  exact hu.mul_smooth_of_bounded hη (le_max_right M 0)
    (fun x hx ↦ (hM x (subset_closure hx)).trans (le_max_left M 0))
    (fun x hx ↦ hL x (subset_closure hx))

/-- Right-multiplication version of `IsBVOn.mul_smooth_of_isCompact_closure`. -/
theorem IsBVOn.mul_smooth_right_of_isCompact_closure [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} {U : Opens E} (hu : IsBVOn μ U u) (hU : IsCompact (closure (U : Set E)))
    (hη : ContDiff ℝ ⊤ η) :
    IsBVOn μ U (fun x ↦ u x * η x) := by
  simpa only [mul_comm (u _)] using hu.mul_smooth_of_isCompact_closure hU hη

/-- If `u` has locally bounded variation on `Ω`, `U` is a relatively compact open subset with
`closure U ⊆ Ω`, and `η : E → ℝ` is smooth, then `fun x ↦ η x * u x` has bounded variation on `U`
(`IsBVOn μ U (fun x ↦ η x * u x)`). -/
theorem IsLocallyBVOn.isBVOn_mul_smooth_of_isCompact_closure [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} {U : Opens E} (hu : IsLocallyBVOn μ Ω u) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (hη : ContDiff ℝ ⊤ η) :
    IsBVOn μ U (fun x ↦ η x * u x) :=
  (hu.isBVOn_of_isCompact_closure hU hUΩ).mul_smooth_of_isCompact_closure hU hη

/-- Right-multiplication version of `IsLocallyBVOn.isBVOn_mul_smooth_of_isCompact_closure`. -/
theorem IsLocallyBVOn.isBVOn_mul_smooth_right_of_isCompact_closure [FiniteDimensional ℝ E]
    [BorelSpace E] {u η : E → ℝ} {U : Opens E} (hu : IsLocallyBVOn μ Ω u)
    (hU : IsCompact (closure (U : Set E))) (hUΩ : closure (U : Set E) ⊆ Ω)
    (hη : ContDiff ℝ ⊤ η) :
    IsBVOn μ U (fun x ↦ u x * η x) :=
  (hu.isBVOn_of_isCompact_closure hU hUΩ).mul_smooth_right_of_isCompact_closure hU hη

/-- Under the hypotheses of `IsLocallyBVOn.isBVOn_mul_smooth_of_isCompact_closure`, the variational
total variation `distributionalVariation μ U (fun x ↦ η x * u x)` is finite. -/
theorem IsLocallyBVOn.distributionalVariation_mul_smooth_lt_top_of_isCompact_closure
    [FiniteDimensional ℝ E] [BorelSpace E] {u η : E → ℝ} {U : Opens E}
    (hu : IsLocallyBVOn μ Ω u) (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (hη : ContDiff ℝ ⊤ η) :
    distributionalVariation μ U (fun x ↦ η x * u x) < ⊤ :=
  (hu.isBVOn_mul_smooth_of_isCompact_closure hU hUΩ hη).2

end SmoothCutoffs

/-! ### Part 3: Truncation layer-cake formula and full signed scalar BV coarea inequality -/

section TruncationAndSignedCoarea

variable [MeasurableSpace E] {μ : Measure E}

/-- **One-dimensional Cavalieri identity for level truncation**: for any `a ≤ b` and `y : ℝ`,
`min (max y a) b - a = ∫ t in Ioo a b, {t : ℝ | t < y}.indicator 1 t`. -/
theorem clamp_sub_eq_setIntegral_indicator {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    min (max y a) b - a = ∫ t in Ioo a b, {t : ℝ | t < y}.indicator (fun _ ↦ (1 : ℝ)) t := by
  rw [show {t : ℝ | t < y} = Iio y from rfl, setIntegral_indicator measurableSet_Iio,
    Ioo_inter_Iio, setIntegral_const, Measure.real, Real.volume_Ioo, smul_eq_mul, mul_one]
  by_cases hya : y ≤ a
  · have hmin : min b y = y := min_eq_right (hya.trans hab)
    rw [hmin, max_eq_right hya, min_eq_left hab, sub_self,
      ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 hya), ENNReal.toReal_zero]
  · have hya' : a < y := not_le.1 hya
    have hmin : a ≤ min b y := le_min hab hya'.le
    rw [ENNReal.toReal_ofReal (sub_nonneg.2 hmin), max_eq_left hya'.le, min_comm]

/-- Any `μ.restrict Ω`-a.e. strongly measurable function that is uniformly bounded on `Ω` is locally
integrable on `Ω` with respect to any locally finite Borel measure `μ`. -/
theorem locallyIntegrableOn_of_aestronglyMeasurable_of_bounded [FiniteDimensional ℝ E]
    [BorelSpace E] [IsLocallyFiniteMeasure μ] {u : E → ℝ}
    (hu : AEStronglyMeasurable u (μ.restrict Ω)) {C : ℝ} (hC : ∀ x ∈ (Ω : Set E), ‖u x‖ ≤ C) :
    LocallyIntegrableOn u Ω μ := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed]
  intro K hKΩ hK
  exact (integrableOn_const (C := C) hK.measure_lt_top.ne).mono' (hu.mono_set hKΩ)
    (ae_restrict_of_forall_mem hK.measurableSet fun x hx ↦ hC x (hKΩ hx))

/-- **Layer-cake / Cavalieri divergence identity for level truncations**: for any `a ≤ b`, any
`μ.restrict Ω`-a.e. strongly measurable function `u : E → ℝ` (without any integrability or sign
assumption), and any test vector field `φ : 𝓓(Ω, E)`,
`∫ x in Ω, min (max (u x) a) b * divergence φ x ∂μ =
  ∫ t in Ioo a b, (∫ x in Ω, {x | t < u x}.indicator 1 x * divergence φ x ∂μ)`. -/
theorem integral_clamp_mul_divergence_eq_integral_superlevel [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] {a b : ℝ} (hab : a ≤ b) {u : E → ℝ}
    (hu : AEStronglyMeasurable u (μ.restrict Ω)) (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), min (max (u x) a) b * divergence (φ : E → E) x ∂μ =
      ∫ t in Ioo a b,
        (∫ x in (Ω : Set E),
          {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) := by
  let v : E → ℝ := fun x ↦ min (max (u x) a) b - a
  have hv_nonneg : ∀ x, 0 ≤ v x := fun x ↦ sub_nonneg.2 (le_min (le_max_right (u x) a) hab)
  have hv_le : ∀ x, v x ≤ b - a := fun x ↦ sub_le_sub_right (min_le_right _ _) a
  have hv_aesm : AEStronglyMeasurable v (μ.restrict Ω) :=
    ((hu.sup aestronglyMeasurable_const).inf aestronglyMeasurable_const).sub
      aestronglyMeasurable_const
  have hv_loc : LocallyIntegrableOn v Ω μ :=
    locallyIntegrableOn_of_aestronglyMeasurable_of_bounded hv_aesm fun x _ ↦ by
      rw [Real.norm_of_nonneg (hv_nonneg x)]
      exact hv_le x
  have h1 : ∫ x in (Ω : Set E), min (max (u x) a) b * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω : Set E), v x * divergence (φ : E → E) x ∂μ := by
    simpa [v] using integral_add_const_mul_divergence v a φ
  rw [h1, integral_mul_divergence_eq_integral_superlevel hv_loc (fun x _ ↦ hv_nonneg x) φ]
  set H : ℝ → ℝ := fun t ↦
    ∫ x in (Ω : Set E),
      {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ
  have hG : ∀ s ∈ Ioi (0 : ℝ),
      (∫ x in (Ω : Set E),
        {x | s < v x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) =
        (Ioo 0 (b - a)).indicator (fun s ↦ H (s + a)) s := by
    intro s hs
    rw [mem_Ioi] at hs
    by_cases hsb : s < b - a
    · have hs_mem : s ∈ Ioo 0 (b - a) := ⟨hs, hsb⟩
      rw [indicator_of_mem hs_mem]
      have hset : {x | s < v x} = {x | s + a < u x} := by
        ext x
        change s < min (max (u x) a) b - a ↔ s + a < u x
        rw [lt_sub_iff_add_lt, lt_min_iff, lt_max_iff]
        exact ⟨fun h ↦ h.1.resolve_right (by linarith),
          fun h ↦ ⟨Or.inl h, by linarith⟩⟩
      simp only [H, hset]
    · have hs_notMem : s ∉ Ioo 0 (b - a) := fun h ↦ hsb h.2
      rw [indicator_of_notMem hs_notMem]
      have hset : {x | s < v x} = ∅ := by
        ext x
        change s < v x ↔ False
        simp [not_lt.2 ((hv_le x).trans (not_lt.1 hsb))]
      simp [hset]
  rw [setIntegral_congr_fun measurableSet_Ioi hG, setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.2 Ioo_subset_Ioi_self]
  have hpre : (· + a) ⁻¹' Ioo a b = Ioo 0 (b - a) := by
    ext s; simp
  rw [← hpre]
  exact (measurePreserving_add_right volume a).setIntegral_preimage_emb
    (Homeomorph.addRight a).measurableEmbedding H (Ioo a b)

/-- **Coarea inequality for level truncations**: for any `a ≤ b` and any `μ.restrict Ω`-a.e.
strongly measurable function `u : E → ℝ`,
`distributionalVariation μ Ω (fun x ↦ min (max (u x) a) b) ≤
  ∫⁻ t in Ioo a b, relativePerimeter μ Ω {x | t < u x}`. -/
theorem distributionalVariation_min_max_le_lintegral_relativePerimeter
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {a b : ℝ} (hab : a ≤ b)
    {u : E → ℝ} (hu : AEStronglyMeasurable u (μ.restrict Ω)) :
    distributionalVariation μ Ω (fun x ↦ min (max (u x) a) b) ≤
      ∫⁻ t in Ioo a b, relativePerimeter μ Ω {x | t < u x} := by
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [integral_clamp_mul_divergence_eq_integral_superlevel hab hu φ]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t ↦ ?_)
  rw [Real.enorm_eq_ofReal_abs]
  exact abs_le_distributionalVariation φ hφ ({x | t < u x}.indicator fun _ ↦ (1 : ℝ))

/-- Whole-space specialization of `distributionalVariation_min_max_le_lintegral_relativePerimeter`.
-/
theorem distributionalVariation_top_min_max_le_lintegral_perimeter
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {a b : ℝ} (hab : a ≤ b)
    {u : E → ℝ} (hu : AEStronglyMeasurable u μ) :
    distributionalVariation μ ⊤ (fun x ↦ min (max (u x) a) b) ≤
      ∫⁻ t in Ioo a b, perimeter μ {x | t < u x} :=
  distributionalVariation_min_max_le_lintegral_relativePerimeter hab (by simpa using hu)

private lemma abs_clamp_nat_le (y : ℝ) (n : ℕ) :
    |min (max y (-(n : ℝ))) (n : ℝ)| ≤ |y| := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · exact le_min (le_trans (neg_abs_le y) (le_max_left _ _)) (by linarith [abs_nonneg y])
  · exact min_le_of_left_le (max_le (le_abs_self y) (by linarith [abs_nonneg y]))

private lemma clamp_nat_eq_of_abs_le {y : ℝ} {n : ℕ} (h : |y| ≤ n) :
    min (max y (-(n : ℝ))) (n : ℝ) = y := by
  rw [abs_le] at h
  rw [max_eq_left h.1, min_eq_left h.2]

/-- As `n → ∞`, the integral of the symmetric truncation `min (max (u x) (-n)) n` against
`divergence φ` converges to `∫ x in Ω, u x * divergence φ x ∂μ` for any locally integrable function
`u` on `Ω`. -/
theorem tendsto_integral_clamp_nat_mul_divergence [FiniteDimensional ℝ E] [BorelSpace E]
    {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, E)) :
    Tendsto
      (fun n : ℕ ↦
        ∫ x in (Ω : Set E),
          min (max (u x) (-(n : ℝ))) (n : ℝ) * divergence (φ : E → E) x ∂μ)
      atTop (𝓝 (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ)) := by
  have hdiv_aesm : AEStronglyMeasurable (fun x ↦ divergence (φ : E → E) x) (μ.restrict Ω) :=
    (continuous_divergence_testFunction φ).aestronglyMeasurable
  refine tendsto_integral_of_dominated_convergence
    (fun x ↦ ‖u x * divergence (φ : E → E) x‖) ?_ ?_ ?_ ?_
  · intro n
    exact (((hu.aestronglyMeasurable.sup aestronglyMeasurable_const).inf
      aestronglyMeasurable_const).mul hdiv_aesm)
  · exact (integrableOn_mul_divergence_of_locallyIntegrableOn hu φ).norm
  · intro n
    refine ae_of_all _ fun x ↦ ?_
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (u x)]
    exact mul_le_mul_of_nonneg_right (abs_clamp_nat_le (u x) n) (norm_nonneg _)
  · refine ae_of_all _ fun x ↦ tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|u x|⌉₊] with n hn
    rw [clamp_nat_eq_of_abs_le ((Nat.le_ceil |u x|).trans (Nat.cast_le.2 hn))]

/-- **Improper signed Cavalieri / layer-cake divergence identity**: for any locally integrable
function `u` on `Ω` and any test vector field `φ : 𝓓(Ω, E)`, the superlevel integral over
`(-n, n)` converges as `n → ∞` to `∫ x in Ω, u x * divergence φ x ∂μ`. -/
theorem tendsto_setIntegral_Ioo_nat_superlevel_mul_divergence [FiniteDimensional ℝ E]
    [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ)
    (φ : 𝓓(Ω, E)) :
    Tendsto
      (fun n : ℕ ↦
        ∫ t in Ioo (-(n : ℝ)) (n : ℝ),
          (∫ x in (Ω : Set E),
            {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ))
      atTop (𝓝 (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ)) := by
  have h_eq : ∀ n : ℕ,
      (∫ t in Ioo (-(n : ℝ)) (n : ℝ),
        (∫ x in (Ω : Set E),
          {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ)) =
      ∫ x in (Ω : Set E),
        min (max (u x) (-(n : ℝ))) (n : ℝ) * divergence (φ : E → E) x ∂μ := fun n ↦
    (integral_clamp_mul_divergence_eq_integral_superlevel
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) hu.aestronglyMeasurable φ).symm
  simp_rw [h_eq]
  exact tendsto_integral_clamp_nat_mul_divergence hu φ

/-- **Full signed Cavalieri / layer-cake divergence identity on `ℝ`**: whenever the superlevel
pairing `t ↦ ∫ x in Ω, {x | t < u x}.indicator 1 x * divergence φ x ∂μ` is integrable on `ℝ`, its
integral over `ℝ` equals `∫ x in Ω, u x * divergence φ x ∂μ`. -/
theorem integral_mul_divergence_eq_integral_superlevel_real [FiniteDimensional ℝ E]
    [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ)
    (φ : 𝓓(Ω, E))
    (hInt : Integrable
      (fun t : ℝ ↦ ∫ x in (Ω : Set E),
        {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) volume) :
    ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ =
      ∫ t : ℝ,
        (∫ x in (Ω : Set E),
          {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) := by
  set H : ℝ → ℝ := fun t ↦
    ∫ x in (Ω : Set E),
      {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ
  have hlim₂ : Tendsto (fun n : ℕ ↦ ∫ t in Ioo (-(n : ℝ)) (n : ℝ), H t) atTop
      (𝓝 (∫ t : ℝ, H t)) := by
    simp_rw [← integral_indicator (measurableSet_Ioo (a := -(_ : ℝ)))]
    refine tendsto_integral_of_dominated_convergence (fun t ↦ ‖H t‖) ?_ hInt.norm ?_ ?_
    · exact fun n ↦ hInt.aestronglyMeasurable.indicator measurableSet_Ioo
    · exact fun n ↦ ae_of_all _ fun t ↦ norm_indicator_le_norm_self H t
    · refine ae_of_all _ fun t ↦ tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (⌈|t|⌉₊ + 1)] with n hn
      have ht : t ∈ Ioo (-(n : ℝ)) (n : ℝ) := by
        have hlt : |t| < n := calc
          |t| ≤ ⌈|t|⌉₊ := Nat.le_ceil |t|
          _ < (⌈|t|⌉₊ + 1 : ℝ) := by linarith
          _ ≤ n := by exact_mod_cast hn
        exact abs_lt.1 hlt
      exact (indicator_of_mem ht H).symm
  exact tendsto_nhds_unique (tendsto_setIntegral_Ioo_nat_superlevel_mul_divergence hu φ) hlim₂

/-- Specialization of `integral_mul_divergence_eq_integral_superlevel_real` when `‖φ x‖ ≤ 1` and
`∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x} < ⊤`. -/
theorem integral_mul_divergence_eq_integral_superlevel_real_of_lintegral_lt_top
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, E)) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ ∫ x in (Ω : Set E),
        {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) volume)
    (hper : ∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x} < ⊤) :
    ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ =
      ∫ t : ℝ,
        (∫ x in (Ω : Set E),
          {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) := by
  refine integral_mul_divergence_eq_integral_superlevel_real hu φ ⟨hmeas, ?_⟩
  refine (lintegral_mono fun t ↦ ?_).trans_lt hper
  rw [Real.enorm_eq_ofReal_abs]
  exact abs_le_distributionalVariation φ hφ ({x | t < u x}.indicator fun _ ↦ (1 : ℝ))

/-- **Full signed scalar BV coarea inequality on `Ω`**: for any locally integrable (possibly
signed) function `u : E → ℝ` on `Ω`,
`distributionalVariation μ Ω u ≤ ∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x}`. -/
theorem distributionalVariation_le_lintegral_relativePerimeter_real
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) :
    distributionalVariation μ Ω u ≤ ∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x} := by
  refine iSup₂_le fun φ hφ ↦ ?_
  have hlim : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal
        (∫ x in (Ω : Set E),
          min (max (u x) (-(n : ℝ))) (n : ℝ) * divergence (φ : E → E) x ∂μ))
      atTop (𝓝 (ENNReal.ofReal (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_integral_clamp_nat_mul_divergence hu φ)
  refine le_of_tendsto' hlim fun n ↦ ?_
  have hn : (-(n : ℝ)) ≤ (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (le_distributionalVariation φ hφ _).trans
    ((distributionalVariation_min_max_le_lintegral_relativePerimeter hn
      hu.aestronglyMeasurable).trans (setLIntegral_le_lintegral _ _))

/-- **Global signed scalar BV coarea inequality on `E`**: for any locally integrable function
`u : E → ℝ`,
`distributionalVariation μ ⊤ u ≤ ∫⁻ t : ℝ, perimeter μ {x | t < u x}`. -/
theorem distributionalVariation_top_le_lintegral_perimeter_real
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → ℝ}
    (hu : LocallyIntegrable u μ) :
    distributionalVariation μ ⊤ u ≤ ∫⁻ t : ℝ, perimeter μ {x | t < u x} :=
  distributionalVariation_le_lintegral_relativePerimeter_real (hu.locallyIntegrableOn (⊤ : Opens E))

/-- If an integrable (possibly signed) function `u` on `Ω` has a finite superlevel-perimeter
integral `∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x} < ⊤`, then `u` has bounded variation on `Ω`
(`IsBVOn μ Ω u`). -/
theorem isBVOn_of_lintegral_relativePerimeter_real_lt_top
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → ℝ}
    (hu : IntegrableOn u Ω μ) (hper : ∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x} < ⊤) :
    IsBVOn μ Ω u :=
  ⟨hu, (distributionalVariation_le_lintegral_relativePerimeter_real
    hu.locallyIntegrableOn).trans_lt hper⟩

/-- If `u` is `μ.restrict Ω`-null-measurable and `t ↦ relativePerimeter μ Ω {x | t < u x}` has
finite Lebesgue integral on `ℝ`, then for almost every `t : ℝ` the superlevel set `{x | t < u x}`
has finite perimeter in `Ω` (`HasFinitePerimeterIn μ Ω {x | t < u x}`). -/
theorem ae_hasFinitePerimeterIn_superlevel_real {u : E → ℝ}
    (hu : NullMeasurable u (μ.restrict Ω))
    (hmeas : AEMeasurable (fun t : ℝ ↦ relativePerimeter μ Ω {x | t < u x}) volume)
    (hper : ∫⁻ t : ℝ, relativePerimeter μ Ω {x | t < u x} < ⊤) :
    ∀ᵐ t : ℝ, HasFinitePerimeterIn μ Ω {x | t < u x} := by
  filter_upwards [ae_lt_top' hmeas hper.ne] with t ht using ⟨nullMeasurableSet_superlevel hu t, ht⟩

/-- Whole-space specialization of `ae_hasFinitePerimeterIn_superlevel_real`. -/
theorem ae_hasFinitePerimeter_superlevel_real {u : E → ℝ}
    (hu : NullMeasurable u μ)
    (hmeas : AEMeasurable (fun t : ℝ ↦ perimeter μ {x | t < u x}) volume)
    (hper : ∫⁻ t : ℝ, perimeter μ {x | t < u x} < ⊤) :
    ∀ᵐ t : ℝ, HasFinitePerimeter μ {x | t < u x} :=
  ae_hasFinitePerimeterIn_superlevel_real (by simpa using hu) hmeas hper

end TruncationAndSignedCoarea

/-! ### Part 4: Disjoint-union and nested set-difference perimeter bounds -/

section DisjointUnionAndDifferencePerimeter

variable [MeasurableSpace E] {μ : Measure E}

/-- For any `μ.restrict Ω`-null-measurable set `s` and constant `c : ℝ`, the indicator function
`s.indicator (fun _ ↦ c)` is locally integrable on `Ω`. -/
theorem locallyIntegrableOn_indicator_const [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] {s : Set E} (hs : NullMeasurableSet s (μ.restrict Ω)) (c : ℝ) :
    LocallyIntegrableOn (s.indicator fun _ ↦ c) Ω μ := by
  have hm : MeasurableSet (toMeasurable (μ.restrict Ω) s) := measurableSet_toMeasurable _ _
  have hae : (toMeasurable (μ.restrict Ω) s).indicator (fun _ ↦ c) =ᵐ[μ.restrict Ω]
      s.indicator (fun _ ↦ c) := by
    filter_upwards [hs.toMeasurable_ae_eq] with x hx
    by_cases hxs : x ∈ s
    · have hxt : x ∈ toMeasurable (μ.restrict Ω) s := hx.mpr hxs
      simp [hxs, hxt]
    · have hxt : x ∉ toMeasurable (μ.restrict Ω) s := fun h ↦ hxs (hx.mp h)
      simp [hxs, hxt]
  exact locallyIntegrableOn_of_aestronglyMeasurable_of_bounded
    ((aestronglyMeasurable_const.indicator hm).congr hae)
    fun x _ ↦ norm_indicator_le_norm_self _ x

/-- **Subadditivity of relative perimeter on a.e.-disjoint unions**: if `s` and `t` are
`μ.restrict Ω`-null-measurable and `μ.restrict Ω (s ∩ t) = 0`, then
`relativePerimeter μ Ω (s ∪ t) ≤ relativePerimeter μ Ω s + relativePerimeter μ Ω t`. -/
theorem relativePerimeter_union_le_of_ae_disjoint [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] {s t : Set E} (hs : NullMeasurableSet s (μ.restrict Ω))
    (ht : NullMeasurableSet t (μ.restrict Ω)) (hst : μ.restrict Ω (s ∩ t) = 0) :
    relativePerimeter μ Ω (s ∪ t) ≤ relativePerimeter μ Ω s + relativePerimeter μ Ω t := by
  have hae : (s ∪ t).indicator (fun _ ↦ (1 : ℝ)) =ᵐ[μ.restrict Ω]
      s.indicator (fun _ ↦ (1 : ℝ)) + t.indicator (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [compl_mem_ae_iff.2 hst] with x hx
    exact Set.indicator_union_of_notMem_inter hx _
  rw [relativePerimeter, distributionalVariation_congr_ae hae]
  exact distributionalVariation_add_le
    (locallyIntegrableOn_indicator_const hs 1) (locallyIntegrableOn_indicator_const ht 1)

/-- **Subadditivity of relative perimeter on disjoint unions**: if `s` and `t` are disjoint and
`μ.restrict Ω`-null-measurable, then
`relativePerimeter μ Ω (s ∪ t) ≤ relativePerimeter μ Ω s + relativePerimeter μ Ω t`. -/
theorem relativePerimeter_union_le_of_disjoint [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] {s t : Set E} (hs : NullMeasurableSet s (μ.restrict Ω))
    (ht : NullMeasurableSet t (μ.restrict Ω)) (hst : Disjoint s t) :
    relativePerimeter μ Ω (s ∪ t) ≤ relativePerimeter μ Ω s + relativePerimeter μ Ω t :=
  relativePerimeter_union_le_of_ae_disjoint hs ht (by simp [hst.inter_eq])

/-- Whole-space specialization of `relativePerimeter_union_le_of_ae_disjoint`. -/
theorem perimeter_union_le_of_ae_disjoint [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] {s t : Set E} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t μ) (hst : μ (s ∩ t) = 0) :
    perimeter μ (s ∪ t) ≤ perimeter μ s + perimeter μ t := by
  rw [perimeter, perimeter, perimeter]
  exact relativePerimeter_union_le_of_ae_disjoint
    (by simpa using hs) (by simpa using ht) (by simpa using hst)

/-- **Subadditivity of perimeter on disjoint unions**: if `s` and `t` are disjoint and
`μ`-null-measurable, then `perimeter μ (s ∪ t) ≤ perimeter μ s + perimeter μ t`. -/
theorem perimeter_union_le_of_disjoint [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] {s t : Set E} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t μ) (hst : Disjoint s t) :
    perimeter μ (s ∪ t) ≤ perimeter μ s + perimeter μ t :=
  perimeter_union_le_of_ae_disjoint hs ht (by simp [hst.inter_eq])

/-- `HasFinitePerimeterIn μ Ω` is closed under a.e.-disjoint unions. -/
theorem HasFinitePerimeterIn.union_of_ae_disjoint [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] {s t : Set E} (hs : HasFinitePerimeterIn μ Ω s)
    (ht : HasFinitePerimeterIn μ Ω t) (hst : μ.restrict Ω (s ∩ t) = 0) :
    HasFinitePerimeterIn μ Ω (s ∪ t) :=
  ⟨hs.1.union ht.1,
    (relativePerimeter_union_le_of_ae_disjoint hs.1 ht.1 hst).trans_lt
      (ENNReal.add_lt_top.2 ⟨hs.2, ht.2⟩)⟩

/-- `HasFinitePerimeterIn μ Ω` is closed under disjoint unions. -/
theorem HasFinitePerimeterIn.union_of_disjoint [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] {s t : Set E} (hs : HasFinitePerimeterIn μ Ω s)
    (ht : HasFinitePerimeterIn μ Ω t) (hst : Disjoint s t) :
    HasFinitePerimeterIn μ Ω (s ∪ t) :=
  hs.union_of_ae_disjoint ht (by simp [hst.inter_eq])

/-- `HasFinitePerimeter μ` is closed under a.e.-disjoint unions. -/
theorem HasFinitePerimeter.union_of_ae_disjoint [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] {s t : Set E} (hs : HasFinitePerimeter μ s)
    (ht : HasFinitePerimeter μ t) (hst : μ (s ∩ t) = 0) :
    HasFinitePerimeter μ (s ∪ t) :=
  HasFinitePerimeterIn.union_of_ae_disjoint hs ht (by simpa using hst)

/-- `HasFinitePerimeter μ` is closed under disjoint unions. -/
theorem HasFinitePerimeter.union_of_disjoint [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] {s t : Set E} (hs : HasFinitePerimeter μ s)
    (ht : HasFinitePerimeter μ t) (hst : Disjoint s t) :
    HasFinitePerimeter μ (s ∪ t) :=
  HasFinitePerimeterIn.union_of_disjoint hs ht hst

/-- **Nested set-difference relative perimeter bound**: if `t ⊆ s` and `s`, `t` are
`μ.restrict Ω`-null-measurable, then
`relativePerimeter μ Ω (s \ t) ≤ relativePerimeter μ Ω s + relativePerimeter μ Ω t`. -/
theorem relativePerimeter_diff_le_of_subset [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] {s t : Set E} (hs : NullMeasurableSet s (μ.restrict Ω))
    (ht : NullMeasurableSet t (μ.restrict Ω)) (hts : t ⊆ s) :
    relativePerimeter μ Ω (s \ t) ≤ relativePerimeter μ Ω s + relativePerimeter μ Ω t := by
  rw [← relativePerimeter_compl (s \ t), Set.sdiff_eq, compl_inter, compl_compl,
    ← relativePerimeter_compl s]
  exact relativePerimeter_union_le_of_disjoint hs.compl ht (disjoint_compl_left_iff_subset.2 hts)

/-- **Nested set-difference perimeter bound**: if `t ⊆ s` and `s`, `t` are `μ`-null-measurable,
then `perimeter μ (s \ t) ≤ perimeter μ s + perimeter μ t`. -/
theorem perimeter_diff_le_of_subset [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] {s t : Set E} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t μ) (hts : t ⊆ s) :
    perimeter μ (s \ t) ≤ perimeter μ s + perimeter μ t :=
  relativePerimeter_diff_le_of_subset (by simpa using hs) (by simpa using ht) hts

/-- `HasFinitePerimeterIn μ Ω` is closed under nested set differences `s \ t` when `t ⊆ s`. -/
theorem HasFinitePerimeterIn.diff_of_subset [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] {s t : Set E} (hs : HasFinitePerimeterIn μ Ω s)
    (ht : HasFinitePerimeterIn μ Ω t) (hts : t ⊆ s) :
    HasFinitePerimeterIn μ Ω (s \ t) :=
  ⟨hs.1.diff ht.1,
    (relativePerimeter_diff_le_of_subset hs.1 ht.1 hts).trans_lt
      (ENNReal.add_lt_top.2 ⟨hs.2, ht.2⟩)⟩

/-- `HasFinitePerimeter μ` is closed under nested set differences `s \ t` when `t ⊆ s`. -/
theorem HasFinitePerimeter.diff_of_subset [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] {s t : Set E} (hs : HasFinitePerimeter μ s)
    (ht : HasFinitePerimeter μ t) (hts : t ⊆ s) :
    HasFinitePerimeter μ (s \ t) :=
  HasFinitePerimeterIn.diff_of_subset hs ht hts

/-- **Annulus relative perimeter bound**: for `r ≤ R`, the relative perimeter of the concentric
annulus `closedBall c R \ ball c r` in `Ω` is at most
`relativePerimeter μ Ω (closedBall c R) + relativePerimeter μ Ω (ball c r)`. -/
theorem relativePerimeter_closedBall_diff_ball_le [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] (c : E) {r R : ℝ} (hrR : r ≤ R) :
    relativePerimeter μ Ω (Metric.closedBall c R \ Metric.ball c r) ≤
      relativePerimeter μ Ω (Metric.closedBall c R) + relativePerimeter μ Ω (Metric.ball c r) :=
  relativePerimeter_diff_le_of_subset
    measurableSet_closedBall.nullMeasurableSet measurableSet_ball.nullMeasurableSet
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hrR))

/-- **Annulus perimeter bound**: for `r ≤ R`, the perimeter of the concentric annulus
`closedBall c R \ ball c r` is at most
`perimeter μ (closedBall c R) + perimeter μ (ball c r)`. -/
theorem perimeter_closedBall_diff_ball_le [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] (c : E) {r R : ℝ} (hrR : r ≤ R) :
    perimeter μ (Metric.closedBall c R \ Metric.ball c r) ≤
      perimeter μ (Metric.closedBall c R) + perimeter μ (Metric.ball c r) :=
  relativePerimeter_closedBall_diff_ball_le c hrR

end DisjointUnionAndDifferencePerimeter

end TauCeti
