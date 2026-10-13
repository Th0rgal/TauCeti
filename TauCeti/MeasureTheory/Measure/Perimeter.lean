/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

/-!
# Variational total variation, BV functions, and relative perimeter

This file develops the distributional/variational theory of functions of bounded variation and sets
of finite perimeter on open subsets of a finite-dimensional real inner product space `E`:

1. **Divergence of vector fields and test vector fields**: for `φ : E → E`, the divergence
   `divergence φ x = LinearMap.trace ℝ E (fderiv ℝ φ x).toLinearMap` equals
   `∑ i, ⟪b i, fderiv ℝ φ x (b i)⟫_ℝ` in any orthonormal basis `b`. For a bundled test vector field
   `φ : 𝓓(Ω, E)`, `divergence φ` is the underlying function of a bundled scalar test function
   `divergenceTestFunction φ : 𝓓(Ω, ℝ)` and satisfies
   `∫ x in Ω, divergence (φ : E → E) x ∂μ = 0` for any additive Haar measure `μ`.
2. **Variational total variation and BV predicates**: the variational total variation
   `distributionalVariation μ Ω u` is the supremum of
   `ENNReal.ofReal (∫ x in Ω, u x * divergence φ x ∂μ)` over test vector fields `φ : 𝓓(Ω, E)` with
   `∀ x, ‖φ x‖ ≤ 1`. We prove equivalence with the absolute-value supremum, invariance under
   almost-everywhere equality on `Ω`, vanishing on constants, invariance under negation and additive
   constants, monotonicity with respect to the open domain, subadditivity, positive homogeneity,
   lower semicontinuity under distributional pairing convergence, and the weak-derivative upper
   bound `distributionalVariation μ Ω u ≤ ∫⁻ x in Ω, ‖v x‖ₑ ∂μ` for `HasWeakFDerivOn μ Ω u v`. We
   also define `IsBVOn` and `IsLocallyBVOn`.
3. **Relative perimeter and sets of finite perimeter**: the relative perimeter
   `relativePerimeter μ Ω s` of `s : Set E` in `Ω : Opens E` is the variational total variation of
   its characteristic function `s.indicator 1`, and `perimeter μ s = relativePerimeter μ ⊤ s`. We
   establish `relativePerimeter_empty`, `relativePerimeter_univ`, invariance under almost-everywhere
   set equality (`=ᵐ[μ.restrict Ω]`) and null modifications, unconditional complement invariance
   `relativePerimeter μ Ω sᶜ = relativePerimeter μ Ω s` (and `perimeter μ sᶜ = perimeter μ s`
   without any finite-volume hypothesis), domain monotonicity, locality, and lower semicontinuity.

## Main definitions

* `TauCeti.divergence`: divergence `LinearMap.trace ℝ E (fderiv ℝ φ x).toLinearMap` of a vector
  field `φ : E → E`.
* `TauCeti.divergenceTestFunction`: bundled scalar test function `𝓓(Ω, ℝ)` representing the
  divergence of a test vector field `φ : 𝓓(Ω, E)`.
* `TauCeti.distributionalVariation`: variational total variation of `u : E → ℝ` on `Ω : Opens E`.
* `TauCeti.IsBVOn`, `TauCeti.IsLocallyBVOn`: global and local bounded variation predicates on `Ω`.
* `TauCeti.relativePerimeter`, `TauCeti.perimeter`: relative perimeter in `Ω` and whole-space
  perimeter of a set `s : Set E`.
* `TauCeti.HasFinitePerimeterIn`, `TauCeti.HasFinitePerimeter`,
  `TauCeti.HasLocallyFinitePerimeterIn`: sets of finite and locally finite perimeter.

## Main results

* `TauCeti.integral_divergence_testFunction_eq_zero`: `∫ x in Ω, divergence φ x ∂μ = 0` for
  `φ : 𝓓(Ω, E)`.
* `TauCeti.distributionalVariation_eq_iSup_abs`, `TauCeti.distributionalVariation_congr_ae`,
  `TauCeti.distributionalVariation_const`, `TauCeti.distributionalVariation_add_const`,
  `TauCeti.distributionalVariation_const_sub`, `TauCeti.distributionalVariation_mono`,
  `TauCeti.distributionalVariation_add_le`, `TauCeti.distributionalVariation_smul`,
  `TauCeti.distributionalVariation_le_liminf`: core properties of variational total variation.
* `TauCeti.HasWeakFDerivOn.integral_mul_divergence_eq_neg`,
  `TauCeti.HasWeakFDerivOn.distributionalVariation_le_lintegral_enorm`: integration by parts and
  variation bound for weakly differentiable functions.
* `TauCeti.relativePerimeter_congr_ae`, `TauCeti.relativePerimeter_compl`,
  `TauCeti.perimeter_compl`, `TauCeti.HasFinitePerimeterIn.compl_iff`,
  `TauCeti.HasFinitePerimeter.compl_iff`, `TauCeti.relativePerimeter_mono`,
  `TauCeti.relativePerimeter_le_liminf`: core API for relative and whole-space perimeter.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace TestFunction LineDeriv
open scoped ENNReal NNReal InnerProductSpace Distributions Topology symmDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω U V : Opens E}

/-! ### Divergence of vector fields and test vector fields -/

/-- The **divergence** of a vector field `φ : E → E` at `x : E`, defined intrinsically as the
trace of its Fréchet derivative `fderiv ℝ φ x`. -/
noncomputable def divergence (φ : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ φ x).toLinearMap

/-- In any orthonormal basis `b` of `E`, the divergence of `φ` at `x` is
`∑ i, ⟪b i, fderiv ℝ φ x (b i)⟫_ℝ`. -/
theorem divergence_eq_sum_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (φ : E → E) (x : E) :
    divergence φ x = ∑ i, ⟪b i, fderiv ℝ φ x (b i)⟫_ℝ :=
  LinearMap.trace_eq_sum_inner (fderiv ℝ φ x).toLinearMap b

/-- In any orthonormal basis `b` of `E`, the divergence of `φ` at `x` is
`∑ i, ⟪fderiv ℝ φ x (b i), b i⟫_ℝ`. -/
theorem divergence_eq_sum_orthonormalBasis_right {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (φ : E → E) (x : E) :
    divergence φ x = ∑ i, ⟪fderiv ℝ φ x (b i), b i⟫_ℝ := by
  rw [divergence_eq_sum_orthonormalBasis b]
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ (b i)

/-- The divergence of the zero vector field vanishes identically. -/
@[simp]
theorem divergence_zero (x : E) : divergence (0 : E → E) x = 0 := by
  simp [divergence]

/-- The divergence of a constant vector field vanishes identically. -/
@[simp]
theorem divergence_const (v x : E) : divergence (fun _ : E ↦ v) x = 0 := by
  simp [divergence]

/-- Divergence commutes with negation of a vector field. -/
@[simp]
theorem divergence_neg (φ : E → E) (x : E) : divergence (-φ) x = -divergence φ x := by
  simp [divergence, fderiv_neg]

/-- Divergence commutes with pointwise negation of a vector field. -/
@[simp]
theorem divergence_fun_neg (φ : E → E) (x : E) :
    divergence (fun y ↦ -φ y) x = -divergence φ x :=
  divergence_neg φ x

/-- Divergence is homogeneous with respect to real scalar multiplication. -/
@[simp]
theorem divergence_const_smul (c : ℝ) (φ : E → E) (x : E) :
    divergence (c • φ) x = c * divergence φ x := by
  simp [divergence, fderiv_const_smul_field]

/-- Divergence is additive on vector fields differentiable at `x`. -/
theorem divergence_add {φ ψ : E → E} {x : E} (hφ : DifferentiableAt ℝ φ x)
    (hψ : DifferentiableAt ℝ ψ x) :
    divergence (φ + ψ) x = divergence φ x + divergence ψ x := by
  simp [divergence, fderiv_add hφ hψ]

/-- Outside `Ω`, the divergence of `φ : 𝓓(Ω, E)` vanishes. -/
theorem divergence_testFunction_eq_zero_of_notMem (φ : 𝓓(Ω, E)) {x : E} (hx : x ∉ (Ω : Set E)) :
    divergence (φ : E → E) x = 0 := by
  have hx' : x ∉ tsupport (φ : E → E) := fun h ↦ hx (φ.tsupport_subset h)
  have hev : (φ : E → E) =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx'
  simp [divergence, hev.fderiv_eq]

/-- Since `divergence (φ : E → E)` vanishes outside `Ω`, integrating `u x * divergence φ x` over
`Ω` agrees with integrating over the whole space `E`. -/
theorem setIntegral_mul_divergence_eq_integral [MeasurableSpace E] (μ : Measure E) (u : E → ℝ)
    (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ =
      ∫ x, u x * divergence (φ : E → E) x ∂μ := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
  rw [divergence_testFunction_eq_zero_of_notMem φ hx, mul_zero]

private lemma testFunction_sum_apply {ι : Type*} (s : Finset ι) (f : ι → 𝓓(Ω, ℝ)) (x : E) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s _ ih => simp [ih]

section DivergenceTestFunction

variable [FiniteDimensional ℝ E]

/-- The divergence of a bundled test vector field `φ : 𝓓(Ω, E)` as a bundled scalar test function
in `𝓓(Ω, ℝ)`. -/
noncomputable def divergenceTestFunction (φ : 𝓓(Ω, E)) : 𝓓(Ω, ℝ) :=
  ∑ i, ∂_{(stdOrthonormalBasis ℝ E) i}
    (TestFunction.postcompCLM (𝕜 := ℝ) (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)) φ)

/-- Evaluating `divergenceTestFunction φ` at `x` yields `divergence (φ : E → E) x`. -/
@[simp]
theorem divergenceTestFunction_apply (φ : 𝓓(Ω, E)) (x : E) :
    divergenceTestFunction φ x = divergence (φ : E → E) x := by
  unfold divergenceTestFunction
  rw [divergence_eq_sum_orthonormalBasis (stdOrthonormalBasis ℝ E), testFunction_sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lineDerivOp_apply]
  set v := (stdOrthonormalBasis ℝ E) i
  set ψ : 𝓓(Ω, ℝ) := TestFunction.postcompCLM (𝕜 := ℝ) (innerSL ℝ v) φ
  have hd : DifferentiableAt ℝ (φ : E → E) x := φ.contDiff.differentiable (by simp) x
  have hdψ : HasFDerivAt (ψ : E → ℝ) ((innerSL ℝ v).comp (fderiv ℝ (φ : E → E) x)) x :=
    (innerSL ℝ v).hasFDerivAt.comp x hd.hasFDerivAt
  rw [(hdψ.hasLineDerivAt v).lineDeriv]
  rfl

/-- The underlying function of `divergenceTestFunction φ` is `divergence (φ : E → E)`. -/
@[simp]
theorem coe_divergenceTestFunction (φ : 𝓓(Ω, E)) :
    (divergenceTestFunction φ : E → ℝ) = divergence (φ : E → E) :=
  funext (divergenceTestFunction_apply φ)

/-- The divergence of a test vector field `φ : 𝓓(Ω, E)` is smooth (`ContDiff ℝ ⊤`). -/
theorem contDiff_divergence_testFunction (φ : 𝓓(Ω, E)) :
    ContDiff ℝ (⊤ : ℕ∞) (divergence (φ : E → E)) := by
  rw [← coe_divergenceTestFunction]
  exact (divergenceTestFunction φ).contDiff

/-- The divergence of a test vector field `φ : 𝓓(Ω, E)` is continuous. -/
theorem continuous_divergence_testFunction (φ : 𝓓(Ω, E)) :
    Continuous (divergence (φ : E → E)) := by
  rw [← coe_divergenceTestFunction]
  exact (divergenceTestFunction φ).continuous

/-- The divergence of a test vector field `φ : 𝓓(Ω, E)` has compact support. -/
theorem hasCompactSupport_divergence_testFunction (φ : 𝓓(Ω, E)) :
    HasCompactSupport (divergence (φ : E → E)) := by
  rw [← coe_divergenceTestFunction]
  exact (divergenceTestFunction φ).hasCompactSupport

/-- The topological support of `divergence (φ : E → E)` is contained in `Ω`. -/
theorem tsupport_divergence_testFunction_subset (φ : 𝓓(Ω, E)) :
    tsupport (divergence (φ : E → E)) ⊆ Ω := by
  rw [← coe_divergenceTestFunction]
  exact (divergenceTestFunction φ).tsupport_subset

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- The divergence of a test vector field `φ : 𝓓(Ω, E)` is integrable with respect to any measure
that is finite on compact sets. -/
theorem integrable_divergence_testFunction [IsFiniteMeasureOnCompacts μ] (φ : 𝓓(Ω, E)) :
    Integrable (divergence (φ : E → E)) μ :=
  (continuous_divergence_testFunction φ).integrable_of_hasCompactSupport
    (hasCompactSupport_divergence_testFunction φ)

/-- The divergence of a test vector field `φ : 𝓓(Ω, E)` is integrable on `Ω`. -/
theorem integrableOn_divergence_testFunction [IsFiniteMeasureOnCompacts μ] (φ : 𝓓(Ω, E)) :
    IntegrableOn (divergence (φ : E → E)) Ω μ :=
  (integrable_divergence_testFunction φ).integrableOn

/-- If `u : E → ℝ` is locally integrable on `Ω`, then `x ↦ u x * divergence (φ : E → E) x` is
integrable on `E` for every test vector field `φ : 𝓓(Ω, E)`. -/
theorem integrable_mul_divergence_of_locallyIntegrableOn {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, E)) :
    Integrable (fun x ↦ u x * divergence (φ : E → E) x) μ := by
  have h := integrable_smul_of_locallyIntegrableOn hu (divergenceTestFunction φ)
  simpa [coe_divergenceTestFunction, smul_eq_mul, mul_comm] using h

/-- If `u : E → ℝ` is locally integrable on `Ω`, then `x ↦ u x * divergence (φ : E → E) x` is
integrable on `Ω` for every test vector field `φ : 𝓓(Ω, E)`. -/
theorem integrableOn_mul_divergence_of_locallyIntegrableOn {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, E)) :
    IntegrableOn (fun x ↦ u x * divergence (φ : E → E) x) Ω μ :=
  (integrable_mul_divergence_of_locallyIntegrableOn hu φ).integrableOn

/-- **Divergence theorem for test vector fields on an open set `Ω`**: for any additive Haar measure
`μ` on `E` and any test vector field `φ : 𝓓(Ω, E)`, `∫ x in Ω, divergence φ x ∂μ = 0`. -/
@[simp]
theorem integral_divergence_testFunction_eq_zero [μ.IsAddHaarMeasure] (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), divergence (φ : E → E) x ∂μ = 0 := by
  have h1 : ∫ x in (Ω : Set E), divergence (φ : E → E) x ∂μ =
      ∫ x, divergence (φ : E → E) x ∂μ := by
    simpa using setIntegral_mul_divergence_eq_integral μ (fun _ ↦ (1 : ℝ)) φ
  rw [h1]
  have h2 : (fun x ↦ divergence (φ : E → E) x) =
      fun x ↦ ∑ i, (∂_{(stdOrthonormalBasis ℝ E) i}
        (TestFunction.postcompCLM (𝕜 := ℝ) (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)) φ) : 𝓓(Ω, ℝ))
        x := by
    ext x
    rw [← divergenceTestFunction_apply, divergenceTestFunction, testFunction_sum_apply]
  rw [h2, integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp_rw [lineDerivOp_apply]
    exact TestFunction.integral_lineDeriv_eq_zero _ _
  · intro i _
    set ψ : 𝓓(Ω, ℝ) :=
      ∂_{(stdOrthonormalBasis ℝ E) i}
        (TestFunction.postcompCLM (𝕜 := ℝ) (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)) φ)
    exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport

/-- Adding a constant `c` to any function `u : E → ℝ` does not change its integral against the
divergence of a test vector field `φ : 𝓓(Ω, E)`. -/
theorem integral_add_const_mul_divergence [μ.IsAddHaarMeasure] (u : E → ℝ) (c : ℝ)
    (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), (u x + c) * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ := by
  have hc : IntegrableOn (fun x ↦ c * divergence (φ : E → E) x) Ω μ :=
    (integrableOn_divergence_testFunction φ).const_mul c
  have hc0 : ∫ x in (Ω : Set E), c * divergence (φ : E → E) x ∂μ = 0 := by
    rw [integral_const_mul, integral_divergence_testFunction_eq_zero, mul_zero]
  have hfun : (fun x ↦ (u x + c) * divergence (φ : E → E) x) =
      fun x ↦ u x * divergence (φ : E → E) x + c * divergence (φ : E → E) x := by
    ext x; ring
  rw [hfun]
  by_cases hu : IntegrableOn (fun x ↦ u x * divergence (φ : E → E) x) Ω μ
  · rw [integral_add hu hc, hc0, add_zero]
  · have huc : ¬ IntegrableOn (fun x ↦ u x * divergence (φ : E → E) x +
        c * divergence (φ : E → E) x) Ω μ := fun h ↦
      hu (by convert h.sub hc using 1; ext x; simp [Pi.sub_apply])
    rw [integral_undef huc, integral_undef hu]

end DivergenceTestFunction

/-! ### Variational total variation (`distributionalVariation`) and BV functions -/

variable [MeasurableSpace E] {μ : Measure E}

/-- The **variational total variation** of `u : E → ℝ` on an open set `Ω : Opens E` with respect to
a measure `μ`, defined as the supremum of `ENNReal.ofReal (∫ x in Ω, u x * divergence φ x ∂μ)` over
all smooth compactly supported vector fields `φ : 𝓓(Ω, E)` satisfying `∀ x, ‖φ x‖ ≤ 1`. -/
noncomputable def distributionalVariation (μ : Measure E := by volume_tac) (Ω : Opens E)
    (u : E → ℝ) : ℝ≥0∞ :=
  ⨆ (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1),
    ENNReal.ofReal (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ)

/-- Any admissible test vector field `φ : 𝓓(Ω, E)` with `∀ x, ‖φ x‖ ≤ 1` gives a lower bound for
`distributionalVariation μ Ω u`. -/
theorem le_distributionalVariation (φ : 𝓓(Ω, E)) (hφ : ∀ x, ‖φ x‖ ≤ 1) (u : E → ℝ) :
    ENNReal.ofReal (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ) ≤
      distributionalVariation μ Ω u :=
  le_iSup₂ (f := fun (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) ↦
    ENNReal.ofReal (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ)) φ hφ

/-- For any test vector field `φ : 𝓓(Ω, E)` with `∀ x, ‖φ x‖ ≤ 1`,
`ENNReal.ofReal |∫ x in Ω, u x * divergence φ x ∂μ| ≤ distributionalVariation μ Ω u`. -/
theorem abs_le_distributionalVariation (φ : 𝓓(Ω, E)) (hφ : ∀ x, ‖φ x‖ ≤ 1) (u : E → ℝ) :
    ENNReal.ofReal |∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ| ≤
      distributionalVariation μ Ω u := by
  rcases le_total 0 (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ) with hnonneg | hnonpos
  · rw [abs_of_nonneg hnonneg]
    exact le_distributionalVariation φ hφ u
  · rw [abs_of_nonpos hnonpos]
    have hneg : ∀ x, ‖(-φ : 𝓓(Ω, E)) x‖ ≤ 1 := fun x ↦ by simpa using hφ x
    have h := le_distributionalVariation (μ := μ) (-φ) hneg u
    have hint : ∫ x in (Ω : Set E), u x * divergence ((-φ : 𝓓(Ω, E)) : E → E) x ∂μ =
        -∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ := by
      have hcoe : ((-φ : 𝓓(Ω, E)) : E → E) = -(φ : E → E) := rfl
      simp_rw [hcoe, divergence_neg, mul_neg, integral_neg]
    rwa [hint] at h

/-- Replacing `ENNReal.ofReal (∫ ...)` by `ENNReal.ofReal |∫ ...|` in the definition of
`distributionalVariation` yields the same supremum. -/
theorem distributionalVariation_eq_iSup_abs (μ : Measure E) (Ω : Opens E) (u : E → ℝ) :
    distributionalVariation μ Ω u =
      ⨆ (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1),
        ENNReal.ofReal |∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ| := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun φ hφ ↦ le_iSup₂_of_le φ hφ ?_
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · exact iSup₂_le fun φ hφ ↦ abs_le_distributionalVariation φ hφ u

/-- `distributionalVariation` is invariant under almost-everywhere equality on `Ω`. -/
theorem distributionalVariation_congr_ae {u v : E → ℝ} (huv : u =ᵐ[μ.restrict Ω] v) :
    distributionalVariation μ Ω u = distributionalVariation μ Ω v := by
  unfold distributionalVariation
  refine iSup_congr fun φ ↦ iSup_congr fun _ ↦ ?_
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [huv] with x hx
  rw [hx]

/-- The variational total variation of the zero function is `0`. -/
@[simp]
theorem distributionalVariation_zero : distributionalVariation μ Ω 0 = 0 := by
  simp [distributionalVariation]

/-- The variational total variation of `fun _ ↦ 0` is `0`. -/
@[simp]
theorem distributionalVariation_fun_zero : distributionalVariation μ Ω (fun _ ↦ 0) = 0 :=
  distributionalVariation_zero

/-- Negating a function preserves `distributionalVariation`. -/
@[simp]
theorem distributionalVariation_neg (u : E → ℝ) :
    distributionalVariation μ Ω (-u) = distributionalVariation μ Ω u := by
  rw [distributionalVariation_eq_iSup_abs, distributionalVariation_eq_iSup_abs]
  refine iSup_congr fun φ ↦ iSup_congr fun _ ↦ ?_
  simp only [Pi.neg_apply, neg_mul, integral_neg, abs_neg]

/-- Pointwise negation preserves `distributionalVariation`. -/
@[simp]
theorem distributionalVariation_fun_neg (u : E → ℝ) :
    distributionalVariation μ Ω (fun x ↦ -u x) = distributionalVariation μ Ω u :=
  distributionalVariation_neg u

/-- **Domain monotonicity of variational total variation**: if `U ≤ V` as open subsets of `E`, then
`distributionalVariation μ U u ≤ distributionalVariation μ V u`. -/
theorem distributionalVariation_mono (hUV : U ≤ V) (u : E → ℝ) :
    distributionalVariation μ U u ≤ distributionalVariation μ V u := by
  refine iSup₂_le fun φ hφ ↦ ?_
  let ψ : 𝓓(V, E) := TestFunction.monoCLM ℝ φ
  have hψ_coe : (ψ : E → E) = (φ : E → E) := by
    ext x
    simp [ψ, TestFunction.monoCLM_apply, hUV]
  have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
    rw [congrFun hψ_coe x]
    exact hφ x
  have hint : ∫ x in (U : Set E), u x * divergence (φ : E → E) x ∂μ =
      ∫ x in (V : Set E), u x * divergence (ψ : E → E) x ∂μ := by
    rw [setIntegral_mul_divergence_eq_integral, setIntegral_mul_divergence_eq_integral, hψ_coe]
  rw [hint]
  exact le_distributionalVariation ψ hψ_norm u

/-- **Scalar homogeneity of variational total variation**:
`distributionalVariation μ Ω (c • u) = ENNReal.ofReal |c| * distributionalVariation μ Ω u`. -/
theorem distributionalVariation_smul (c : ℝ) (u : E → ℝ) :
    distributionalVariation μ Ω (c • u) = ENNReal.ofReal |c| * distributionalVariation μ Ω u := by
  rw [distributionalVariation_eq_iSup_abs, distributionalVariation_eq_iSup_abs, ENNReal.mul_iSup]
  refine iSup_congr fun φ ↦ ?_
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun _ ↦ ?_
  have hmul : (fun x ↦ (c • u) x * divergence (φ : E → E) x) =
      fun x ↦ c * (u x * divergence (φ : E → E) x) := by
    ext x; simp [smul_eq_mul, mul_assoc]
  rw [hmul, integral_const_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]

/-- **Lower semicontinuity of variational total variation**: if
`∫ x in Ω, uSeq n x * divergence φ x` tends to `∫ x in Ω, u x * divergence φ x` along a filter `l`
for every test vector field `φ : 𝓓(Ω, E)`, then
`distributionalVariation μ Ω u ≤ liminf (fun n ↦ distributionalVariation μ Ω (uSeq n)) l`. -/
theorem distributionalVariation_le_liminf {ι : Type*} {l : Filter ι} {uSeq : ι → E → ℝ}
    {u : E → ℝ}
    (hconv : ∀ φ : 𝓓(Ω, E),
      Tendsto (fun n ↦ ∫ x in (Ω : Set E), uSeq n x * divergence (φ : E → E) x ∂μ) l
        (𝓝 (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ))) :
    distributionalVariation μ Ω u ≤
      liminf (fun n ↦ distributionalVariation μ Ω (uSeq n)) l := by
  rcases eq_or_ne l ⊥ with rfl | hl
  · simp [liminf]
  have : l.NeBot := ⟨hl⟩
  refine iSup₂_le fun φ hφ ↦ ?_
  have hlim : Tendsto
      (fun n ↦ ENNReal.ofReal (∫ x in (Ω : Set E), uSeq n x * divergence (φ : E → E) x ∂μ)) l
      (𝓝 (ENNReal.ofReal (∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hconv φ)
  rw [← hlim.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n ↦ ?_)
  exact le_distributionalVariation φ hφ (uSeq n)

section FiniteDimensionalBV

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- The variational total variation of a constant function on `Ω` is `0` for any additive Haar
measure `μ`. -/
@[simp]
theorem distributionalVariation_const [μ.IsAddHaarMeasure] (c : ℝ) :
    distributionalVariation μ Ω (fun _ ↦ c) = 0 := by
  unfold distributionalVariation
  simp [integral_const_mul, integral_divergence_testFunction_eq_zero]

/-- Adding a constant `c` to `u` preserves `distributionalVariation` for any additive Haar measure
`μ`. -/
@[simp]
theorem distributionalVariation_add_const [μ.IsAddHaarMeasure] (u : E → ℝ) (c : ℝ) :
    distributionalVariation μ Ω (fun x ↦ u x + c) = distributionalVariation μ Ω u := by
  unfold distributionalVariation
  refine iSup_congr fun φ ↦ iSup_congr fun _ ↦ ?_
  rw [integral_add_const_mul_divergence]

/-- Subtracting a constant `c` from `u` preserves `distributionalVariation` for any additive Haar
measure `μ`. -/
@[simp]
theorem distributionalVariation_sub_const [μ.IsAddHaarMeasure] (u : E → ℝ) (c : ℝ) :
    distributionalVariation μ Ω (fun x ↦ u x - c) = distributionalVariation μ Ω u := by
  simp [sub_eq_add_neg]

/-- Subtracting `u` from a constant `c` preserves `distributionalVariation` for any additive Haar
measure `μ`. -/
@[simp]
theorem distributionalVariation_const_sub [μ.IsAddHaarMeasure] (u : E → ℝ) (c : ℝ) :
    distributionalVariation μ Ω (fun x ↦ c - u x) = distributionalVariation μ Ω u := by
  have h : (fun x ↦ c - u x) = fun x ↦ -u x + c := by ext x; ring
  rw [h, distributionalVariation_add_const, distributionalVariation_fun_neg]

alias distributionalVariation_sub_const_left := distributionalVariation_const_sub

/-- **Subadditivity of variational total variation**: for locally integrable functions `u, v` on
`Ω`, `distributionalVariation μ Ω (u + v) ≤
distributionalVariation μ Ω u + distributionalVariation μ Ω v`. -/
theorem distributionalVariation_add_le {u v : E → ℝ} (hu : LocallyIntegrableOn u Ω μ)
    (hv : LocallyIntegrableOn v Ω μ) :
    distributionalVariation μ Ω (u + v) ≤
      distributionalVariation μ Ω u + distributionalVariation μ Ω v := by
  refine iSup₂_le fun φ hφ ↦ ?_
  have hsplit : (fun x ↦ (u + v) x * divergence (φ : E → E) x) =
      fun x ↦ u x * divergence (φ : E → E) x + v x * divergence (φ : E → E) x := by
    ext x; simp [add_mul]
  rw [hsplit, integral_add (integrableOn_mul_divergence_of_locallyIntegrableOn hu φ)
    (integrableOn_mul_divergence_of_locallyIntegrableOn hv φ)]
  exact (ENNReal.ofReal_add_le).trans
    (add_le_add (le_distributionalVariation φ hφ u) (le_distributionalVariation φ hφ v))

/-- **Integration by parts against `divergence` for a weakly differentiable function**: if
`HasWeakFDerivOn μ Ω u v` (`v : E → E →L[ℝ] ℝ`), then for every test vector field `φ : 𝓓(Ω, E)`,
`∫ x in Ω, u x * divergence φ x ∂μ = - ∫ x in Ω, v x (φ x) ∂μ`. -/
theorem HasWeakFDerivOn.integral_mul_divergence_eq_neg {u : E → ℝ} {v : E → E →L[ℝ] ℝ}
    (h : HasWeakFDerivOn μ Ω u v) (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ =
      -∫ x in (Ω : Set E), v x (φ x) ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  set ψ : Fin (Module.finrank ℝ E) → 𝓓(Ω, ℝ) :=
    fun i ↦ TestFunction.postcompCLM (𝕜 := ℝ) (innerSL ℝ (b i)) φ
  have hL : ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ =
      ∫ x, divergence (φ : E → E) x * u x ∂μ := by
    rw [setIntegral_mul_divergence_eq_integral]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  have hdiv : (fun x ↦ divergence (φ : E → E) x * u x) =
      fun x ↦ ∑ i, lineDeriv ℝ (ψ i : E → ℝ) x (b i) • u x := by
    ext x
    rw [← divergenceTestFunction_apply, divergenceTestFunction, testFunction_sum_apply,
      Finset.sum_mul]
    simp [ψ, b, smul_eq_mul]
  rw [hL, hdiv, integral_finsetSum _ fun i _ ↦
    integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn (ψ i) (b i)]
  have hterm (i : Fin (Module.finrank ℝ E)) :
      ∫ x, lineDeriv ℝ (ψ i : E → ℝ) x (b i) • u x ∂μ =
        -∫ x, (ψ i : E → ℝ) x • v x (b i) ∂μ :=
    (h.hasWeakLineDerivOn (b i)).integral_lineDeriv_smul_eq_neg_integral_smul (ψ i)
  simp_rw [hterm, Finset.sum_neg_distrib, neg_inj]
  rw [← integral_finsetSum _ fun i _ ↦
    integrable_smul_of_locallyIntegrableOn
      (h.hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv (ψ i)]
  have hR : ∫ x in (Ω : Set E), v x (φ x) ∂μ = ∫ x, v x (φ x) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    simp [φ.zero_on_compl hx]
  rw [hR]
  congr 1 with x
  have hrepr : φ x = ∑ i, ⟪b i, φ x⟫_ℝ • b i := (b.sum_repr' (φ x)).symm
  conv_rhs => rw [hrepr, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [ψ, postcompCLM_apply, smul_eq_mul]

/-- **Weak-derivative bound on variational total variation**: if `HasWeakFDerivOn μ Ω u v`, then
`distributionalVariation μ Ω u ≤ ∫⁻ x in Ω, ‖v x‖ₑ ∂μ`. -/
theorem HasWeakFDerivOn.distributionalVariation_le_lintegral_enorm {u : E → ℝ}
    {v : E → E →L[ℝ] ℝ} (h : HasWeakFDerivOn μ Ω u v) :
    distributionalVariation μ Ω u ≤ ∫⁻ x in (Ω : Set E), ‖v x‖ₑ ∂μ := by
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [h.integral_mul_divergence_eq_neg φ]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [abs_neg, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine lintegral_mono fun x ↦ ?_
  have hφ1 : ‖φ x‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ENNReal.ofReal_le_one]
    exact hφ x
  calc ‖v x (φ x)‖ₑ ≤ ‖v x‖ₑ * ‖φ x‖ₑ := ContinuousLinearMap.le_opENorm (v x) (φ x)
    _ ≤ ‖v x‖ₑ * 1 := by gcongr
    _ = ‖v x‖ₑ := mul_one _

end FiniteDimensionalBV

/-- A function `u : E → ℝ` has **bounded variation** on `Ω : Opens E` (`IsBVOn μ Ω u`) if `u` is
integrable on `Ω` and its variational total variation `distributionalVariation μ Ω u` is finite. -/
def IsBVOn (μ : Measure E := by volume_tac) (Ω : Opens E) (u : E → ℝ) : Prop :=
  IntegrableOn u Ω μ ∧ distributionalVariation μ Ω u < ⊤

/-- A function `u : E → ℝ` has **locally bounded variation** on `Ω : Opens E`
(`IsLocallyBVOn μ Ω u`) if `u` is locally integrable on `Ω` and has finite variational total
variation on every relatively compact open subset `U` with `closure U ⊆ Ω`. -/
def IsLocallyBVOn (μ : Measure E := by volume_tac) (Ω : Opens E) (u : E → ℝ) : Prop :=
  LocallyIntegrableOn u Ω μ ∧
    ∀ U : Opens E, IsCompact (closure (U : Set E)) → closure (U : Set E) ⊆ Ω →
      distributionalVariation μ U u < ⊤

/-- `IsBVOn` is invariant under almost-everywhere equality on `Ω`. -/
theorem IsBVOn.congr_ae {u v : E → ℝ} (hu : IsBVOn μ Ω u) (huv : u =ᵐ[μ.restrict Ω] v) :
    IsBVOn μ Ω v :=
  ⟨hu.1.congr_fun_ae huv, (distributionalVariation_congr_ae huv.symm).trans_lt hu.2⟩

/-- `IsBVOn` is closed under negation. -/
theorem IsBVOn.neg {u : E → ℝ} (hu : IsBVOn μ Ω u) : IsBVOn μ Ω (-u) :=
  ⟨hu.1.neg, by simpa using hu.2⟩

/-- `IsBVOn` is closed under addition. -/
theorem IsBVOn.add [FiniteDimensional ℝ E] [BorelSpace E] {u v : E → ℝ} (hu : IsBVOn μ Ω u)
    (hv : IsBVOn μ Ω v) : IsBVOn μ Ω (u + v) :=
  ⟨hu.1.add hv.1,
    (distributionalVariation_add_le hu.1.locallyIntegrableOn hv.1.locallyIntegrableOn).trans_lt
      (ENNReal.add_lt_top.2 ⟨hu.2, hv.2⟩)⟩

/-- `IsBVOn` is closed under real scalar multiplication. -/
theorem IsBVOn.smul {u : E → ℝ} (hu : IsBVOn μ Ω u) (c : ℝ) : IsBVOn μ Ω (c • u) :=
  ⟨hu.1.smul c, by
    rw [distributionalVariation_smul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2⟩

/-- Every function in `IsBVOn μ Ω` belongs to `IsLocallyBVOn μ Ω`. -/
theorem IsBVOn.isLocallyBVOn {u : E → ℝ} (hu : IsBVOn μ Ω u) : IsLocallyBVOn μ Ω u :=
  ⟨hu.1.locallyIntegrableOn, fun _ _ hU ↦
    (distributionalVariation_mono (subset_closure.trans hU) u).trans_lt hu.2⟩

/-! ### Relative perimeter, whole-space perimeter, and sets of finite perimeter -/

/-- The **relative perimeter** `P(s; Ω)` of a set `s : Set E` in an open set `Ω : Opens E`, defined
as the variational total variation of its characteristic function `s.indicator 1` on `Ω`. -/
noncomputable def relativePerimeter (μ : Measure E := by volume_tac) (Ω : Opens E)
    (s : Set E) : ℝ≥0∞ :=
  distributionalVariation μ Ω (s.indicator fun _ ↦ (1 : ℝ))

/-- The **perimeter** `P(s)` of a set `s : Set E` in the whole space `E`, defined as
`relativePerimeter μ ⊤ s`. -/
noncomputable def perimeter (μ : Measure E := by volume_tac) (s : Set E) : ℝ≥0∞ :=
  relativePerimeter μ ⊤ s

/-- A set `s : Set E` has **finite perimeter in `Ω`** (`HasFinitePerimeterIn μ Ω s`) if `s` is
null-measurable with respect to `μ.restrict Ω` and `relativePerimeter μ Ω s < ⊤`. -/
def HasFinitePerimeterIn (μ : Measure E := by volume_tac) (Ω : Opens E) (s : Set E) : Prop :=
  NullMeasurableSet s (μ.restrict Ω) ∧ relativePerimeter μ Ω s < ⊤

/-- A set `s : Set E` has **finite perimeter** in `E` (`HasFinitePerimeter μ s`) if it is
`μ`-null-measurable and `perimeter μ s < ⊤`. Notably, `HasFinitePerimeter` does not require
`μ s < ⊤`. -/
def HasFinitePerimeter (μ : Measure E := by volume_tac) (s : Set E) : Prop :=
  HasFinitePerimeterIn μ ⊤ s

/-- A set `s : Set E` has **locally finite perimeter in `Ω`** (`HasLocallyFinitePerimeterIn μ Ω s`)
if `s` is null-measurable on `Ω` and has finite relative perimeter on every relatively compact open
subset `U` with `closure U ⊆ Ω`. -/
def HasLocallyFinitePerimeterIn (μ : Measure E := by volume_tac) (Ω : Opens E)
    (s : Set E) : Prop :=
  NullMeasurableSet s (μ.restrict Ω) ∧
    ∀ U : Opens E, IsCompact (closure (U : Set E)) → closure (U : Set E) ⊆ Ω →
      relativePerimeter μ U s < ⊤

/-- Explicit supremum formula for `relativePerimeter μ Ω s` in terms of `∫ x in s ∩ Ω, div φ` for
measurable `s`. -/
theorem relativePerimeter_eq_iSup_of_measurableSet {s : Set E} (hs : MeasurableSet s) :
    relativePerimeter μ Ω s =
      ⨆ (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1),
        ENNReal.ofReal (∫ x in s ∩ (Ω : Set E), divergence (φ : E → E) x ∂μ) := by
  unfold relativePerimeter distributionalVariation
  refine iSup_congr fun φ ↦ iSup_congr fun _ ↦ ?_
  congr 1
  have hind : (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x) =
      s.indicator (divergence (φ : E → E)) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hind, integral_indicator hs, Measure.restrict_restrict hs]

/-- The relative perimeter of the empty set is `0`. -/
@[simp]
theorem relativePerimeter_empty : relativePerimeter μ Ω ∅ = 0 := by
  simp [relativePerimeter]

/-- The whole-space perimeter of the empty set is `0`. -/
@[simp]
theorem perimeter_empty : perimeter μ (∅ : Set E) = 0 := by
  simp [perimeter]

/-- **Almost-everywhere invariance of relative perimeter**: if `s =ᵐ[μ.restrict Ω] t`, then
`relativePerimeter μ Ω s = relativePerimeter μ Ω t`. -/
theorem relativePerimeter_congr_ae {s t : Set E} (h : s =ᵐ[μ.restrict Ω] t) :
    relativePerimeter μ Ω s = relativePerimeter μ Ω t := by
  refine distributionalVariation_congr_ae ?_
  filter_upwards [h] with x hx
  have hmem : x ∈ s ↔ x ∈ t := by simpa [eq_iff_iff] using hx
  by_cases hxs : x ∈ s
  · simp [hxs, hmem.1 hxs]
  · simp [hxs, mt hmem.2 hxs]

/-- **Almost-everywhere invariance of whole-space perimeter**: if `s =ᵐ[μ] t`, then
`perimeter μ s = perimeter μ t`. -/
theorem perimeter_congr_ae {s t : Set E} (h : s =ᵐ[μ] t) :
    perimeter μ s = perimeter μ t := by
  refine relativePerimeter_congr_ae ?_
  simpa [Opens.coe_top] using h

/-- **Locality of relative perimeter**: if `s ∩ Ω =ᵐ[μ] t ∩ Ω`, then
`relativePerimeter μ Ω s = relativePerimeter μ Ω t`. -/
theorem relativePerimeter_eq_of_inter_ae_eq [OpensMeasurableSpace E] {s t : Set E}
    (h : (s ∩ (Ω : Set E) : Set E) =ᵐ[μ] (t ∩ (Ω : Set E) : Set E)) :
    relativePerimeter μ Ω s = relativePerimeter μ Ω t := by
  refine relativePerimeter_congr_ae ?_
  change ∀ᵐ x ∂μ.restrict Ω, (x ∈ s) = (x ∈ t)
  rw [ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [h] with x hx hxΩ
  have hiff : x ∈ s ∩ (Ω : Set E) ↔ x ∈ t ∩ (Ω : Set E) := by simpa [eq_iff_iff] using hx
  exact propext ⟨fun hxs ↦ (hiff.1 ⟨hxs, hxΩ⟩).1, fun hxt ↦ (hiff.2 ⟨hxt, hxΩ⟩).1⟩

/-- Intersecting `s` with `Ω` does not change `relativePerimeter μ Ω s`. -/
@[simp]
theorem relativePerimeter_inter_self [OpensMeasurableSpace E] (s : Set E) :
    relativePerimeter μ Ω (s ∩ Ω) = relativePerimeter μ Ω s :=
  relativePerimeter_eq_of_inter_ae_eq (by simp [inter_assoc])

/-- Removing a `μ`-null set `N` does not change `relativePerimeter μ Ω s`. -/
theorem relativePerimeter_diff_null (s : Set E) {N : Set E} (hN : μ N = 0) :
    relativePerimeter μ Ω (s \ N) = relativePerimeter μ Ω s :=
  relativePerimeter_congr_ae (sdiff_ae_eq_self.2
    (Measure.restrict_le_self.absolutelyContinuous (measure_mono_null inter_subset_right hN)))

/-- Taking the union with a `μ`-null set `N` does not change `relativePerimeter μ Ω s`. -/
theorem relativePerimeter_union_null (s : Set E) {N : Set E} (hN : μ N = 0) :
    relativePerimeter μ Ω (s ∪ N) = relativePerimeter μ Ω s :=
  relativePerimeter_congr_ae (union_ae_eq_left_of_ae_eq_empty
    (ae_eq_empty.2 (Measure.restrict_le_self.absolutelyContinuous hN)))

/-- Removing a `μ`-null set `N` does not change `perimeter μ s`. -/
theorem perimeter_diff_null (s : Set E) {N : Set E} (hN : μ N = 0) :
    perimeter μ (s \ N) = perimeter μ s :=
  relativePerimeter_diff_null s hN

/-- Taking the union with a `μ`-null set `N` does not change `perimeter μ s`. -/
theorem perimeter_union_null (s : Set E) {N : Set E} (hN : μ N = 0) :
    perimeter μ (s ∪ N) = perimeter μ s :=
  relativePerimeter_union_null s hN

/-- **Punctured ball**: for a measure `μ` with no singleton atoms, removing the center `{c}` from
`Metric.ball c r` leaves its relative perimeter in `Ω` unchanged. -/
@[simp]
theorem relativePerimeter_ball_diff_singleton [NullSingletonClass μ] (c : E) (r : ℝ) :
    relativePerimeter μ Ω (Metric.ball c r \ {c}) = relativePerimeter μ Ω (Metric.ball c r) :=
  relativePerimeter_diff_null (Metric.ball c r) (measure_singleton c)

/-- For a measure `μ` with no singleton atoms, removing the center `{c}` from `Metric.ball c r`
leaves its whole-space perimeter unchanged. -/
@[simp]
theorem perimeter_ball_diff_singleton [NullSingletonClass μ] (c : E) (r : ℝ) :
    perimeter μ (Metric.ball c r \ {c}) = perimeter μ (Metric.ball c r) :=
  perimeter_diff_null (Metric.ball c r) (measure_singleton c)

/-- **Domain monotonicity of relative perimeter**: if `U ≤ V` as open subsets of `E`, then
`relativePerimeter μ U s ≤ relativePerimeter μ V s`. -/
theorem relativePerimeter_mono (hUV : U ≤ V) (s : Set E) :
    relativePerimeter μ U s ≤ relativePerimeter μ V s :=
  distributionalVariation_mono hUV _

/-- Every set of finite perimeter in `Ω` has locally finite perimeter in `Ω`. -/
theorem HasFinitePerimeterIn.hasLocallyFinitePerimeterIn {s : Set E}
    (hs : HasFinitePerimeterIn μ Ω s) : HasLocallyFinitePerimeterIn μ Ω s :=
  ⟨hs.1, fun _ _ hU ↦ (relativePerimeter_mono (subset_closure.trans hU) s).trans_lt hs.2⟩

/-- **Lower semicontinuity of relative perimeter**: if the indicator pairings
`∫ x in Ω, (sSeq n).indicator 1 x * divergence φ x ∂μ` converge to
`∫ x in Ω, s.indicator 1 x * divergence φ x ∂μ` along a filter `l` for every test vector field
`φ : 𝓓(Ω, E)`, then
`relativePerimeter μ Ω s ≤ liminf (fun n ↦ relativePerimeter μ Ω (sSeq n)) l`. -/
theorem relativePerimeter_le_liminf {ι : Type*} {l : Filter ι} {sSeq : ι → Set E} {s : Set E}
    (hconv : ∀ φ : 𝓓(Ω, E),
      Tendsto (fun n ↦ ∫ x in (Ω : Set E),
        (sSeq n).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) l
        (𝓝 (∫ x in (Ω : Set E), s.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ))) :
    relativePerimeter μ Ω s ≤ liminf (fun n ↦ relativePerimeter μ Ω (sSeq n)) l :=
  distributionalVariation_le_liminf hconv

section FiniteDimensionalPerimeter

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

/-- The relative perimeter of `Set.univ` is `0` for any additive Haar measure `μ`. -/
@[simp]
theorem relativePerimeter_univ : relativePerimeter μ Ω Set.univ = 0 := by simp [relativePerimeter]

/-- The whole-space perimeter of `Set.univ` is `0` for any additive Haar measure `μ`. -/
@[simp]
theorem perimeter_univ : perimeter μ (Set.univ : Set E) = 0 := by simp [perimeter]

/-- **Complement invariance of relative perimeter**: `P(sᶜ; Ω) = P(s; Ω)` for every set `s : Set E`
and any additive Haar measure `μ` (without any finite-measure assumption on `s`). -/
@[simp]
theorem relativePerimeter_compl (s : Set E) :
    relativePerimeter μ Ω sᶜ = relativePerimeter μ Ω s := by
  unfold relativePerimeter
  have h : (sᶜ.indicator fun _ : E ↦ (1 : ℝ)) =
      fun x ↦ 1 - s.indicator (fun _ ↦ (1 : ℝ)) x := by
    ext x; by_cases hx : x ∈ s <;> simp [hx]
  rw [h, distributionalVariation_const_sub]

/-- **Complement invariance of whole-space perimeter**: `P(sᶜ) = P(s)` for every set `s : Set E`
and any additive Haar measure `μ` (without any finite-measure assumption on `s`). -/
@[simp]
theorem perimeter_compl (s : Set E) : perimeter μ sᶜ = perimeter μ s := relativePerimeter_compl s

/-- `HasFinitePerimeterIn` is preserved under taking complements. -/
theorem HasFinitePerimeterIn.compl {s : Set E} (hs : HasFinitePerimeterIn μ Ω s) :
    HasFinitePerimeterIn μ Ω sᶜ :=
  ⟨hs.1.compl, by simpa using hs.2⟩

/-- `sᶜ` has finite perimeter in `Ω` if and only if `s` has finite perimeter in `Ω`. -/
@[simp]
theorem HasFinitePerimeterIn.compl_iff {s : Set E} :
    HasFinitePerimeterIn μ Ω sᶜ ↔ HasFinitePerimeterIn μ Ω s :=
  ⟨fun h ↦ by simpa using h.compl, fun h ↦ h.compl⟩

/-- `HasFinitePerimeter` is preserved under taking complements. -/
theorem HasFinitePerimeter.compl {s : Set E} (hs : HasFinitePerimeter μ s) :
    HasFinitePerimeter μ sᶜ :=
  HasFinitePerimeterIn.compl hs

/-- `sᶜ` has finite perimeter on `E` if and only if `s` has finite perimeter on `E`. -/
@[simp]
theorem HasFinitePerimeter.compl_iff {s : Set E} :
    HasFinitePerimeter μ sᶜ ↔ HasFinitePerimeter μ s :=
  HasFinitePerimeterIn.compl_iff

/-- **Exterior of a ball**: the complement `(Metric.ball c r)ᶜ` has the same perimeter as
`Metric.ball c r`, even when `(Metric.ball c r)ᶜ` has infinite volume. -/
theorem perimeter_compl_ball (c : E) (r : ℝ) :
    perimeter μ (Metric.ball c r)ᶜ = perimeter μ (Metric.ball c r) :=
  perimeter_compl (Metric.ball c r)

end FiniteDimensionalPerimeter

end TauCeti
