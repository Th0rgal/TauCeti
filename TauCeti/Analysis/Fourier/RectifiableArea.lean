/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.SignedArea
public import TauCeti.MeasureTheory.Measure.Hausdorff.CurveMultiplicity
public import TauCeti.Topology.EMetricSpace.Arclength
public import TauCeti.Topology.EMetricSpace.Reparametrization
public import TauCeti.Topology.Instances.CantorFunction

/-!
# Geometric Signed Area of Rectifiable Plane Curves, Circle Rigidity, and the Cantor Circle
This file develops the geometric signed area for continuous rectifiable plane curves
`γ : ℝ → EuclideanSpace ℝ (Fin 2)` on `[a, b]` via canonical unit-speed arclength factorization
(`TauCeti.arcLengthReparam`), proves the sharp length--signed-area isoperimetric inequality and
circle trace rigidity, establishes invariance and sign reversal under monotone and antitone
continuous onto reparametrizations, and constructs the non-absolutely-continuous
Cantor-reparametrized circle `cantorCircleCurve`.
## Main definitions and results
* `TauCeti.signedAreaEuclidean`, `TauCeti.rectifiableSignedArea`: geometric signed area of a
  rectifiable plane curve via `arcLengthReparam`.
* `TauCeti.ae_norm_deriv_arcLengthReparam`,
  `TauCeti.intervalIntegral_norm_deriv_sq_arcLengthReparam`: unit-speed derivative and energy.
* `TauCeti.four_mul_pi_mul_abs_rectifiableSignedArea_le`,
  `TauCeti.exists_sphere_trace_of_rectifiableSignedArea_eq`: sharp rectifiable length--area
  inequality and circle trace rigidity.
* `TauCeti.rectifiableSignedArea_comp_of_monotoneOn`,
  `TauCeti.rectifiableSignedArea_comp_of_antitoneOn`: reparametrization invariance and sign
  reversal.
* `TauCeti.cantorCircleCurve`, `TauCeti.not_absolutelyContinuousOnInterval_cantorCircleCurve`,
  `TauCeti.four_mul_pi_mul_abs_rectifiableSignedArea_cantorCircleCurve_eq`: the non-AC Cantor
  circle and its sharp isoperimetric equality.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open scoped Real Interval ENNReal NNReal Topology EuclideanGeometry

namespace TauCeti

/-! ### Unit-speed derivative and energy identities for `arcLengthReparam` -/

section UnitSpeedEnergy
variable {E : Type*} [NormedAddCommGroup E] {γ : ℝ → E} {a b : ℝ}
/-- `arcLengthReparam γ a b` is absolutely continuous on every compact interval `[s₁, s₂]`. -/
theorem absolutelyContinuousOnInterval_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ
  (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (s₁ s₂ : ℝ) : AbsolutelyContinuousOnInterval
  (arcLengthReparam γ a b) s₁ s₂ := (lipschitzWith_arcLengthReparam hab hγ
  hc).lipschitzOnWith.absolutelyContinuousOnInterval
variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]
/-- The derivative of `arcLengthReparam γ a b` belongs to `L²` on every compact interval. -/
theorem memLp_deriv_arcLengthReparam_Icc (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (s₁ s₂ : ℝ) :
    MemLp (deriv (arcLengthReparam γ a b)) 2 (volume.restrict (Icc s₁ s₂)) :=
  MemLp.of_bound (aestronglyMeasurable_deriv _ _) 1 (Filter.Eventually.of_forall fun _ ↦ by
    simpa using norm_deriv_le_of_lipschitz (lipschitzWith_arcLengthReparam hab hγ hc))
/-- **Unit-speed derivative identity**: `‖deriv (arcLengthReparam γ a b) s‖ = 1` a.e. -/
theorem ae_norm_deriv_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc :
    ContinuousOn γ (Icc a b)) : ∀ᵐ s ∂(volume.restrict (Icc 0 (variationOnFromTo γ (Icc a b) a b))),
    ‖deriv (arcLengthReparam γ a b) s‖ = 1 := by
  set L := variationOnFromTo γ (Icc a b) a b
  have hL : 0 ≤ L := variationOnFromTo.nonneg_of_le γ (Icc a b) hab
  have hac := absolutelyContinuousOnInterval_arcLengthReparam hab hγ hc 0 L
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hac.ae_deriv_variationOnFromTo_eq_norm_deriv hL, (volume : Measure ℝ).ae_ne 0,
    (volume : Measure ℝ).ae_ne L] with s hs₁ hs₀ hsL hs_mem
  have hs_oo : s ∈ Ioo 0 L := ⟨hs_mem.1.lt_of_ne' hs₀, hs_mem.2.lt_of_ne hsL⟩
  have hderiv : HasDerivAt (variationOnFromTo (arcLengthReparam γ a b) (Icc 0 L) 0) 1 s :=
    (hasDerivAt_id s).congr_of_eventuallyEq <| Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs_oo)
      fun _ hu ↦ variationOnFromTo_arcLengthReparam_zero hab hγ hc (Ioo_subset_Icc_self hu)
  rw [← hs₁ hs_mem, hderiv.deriv]
/-- **Unit-speed derivative identity** on `Icc 0 (eVariationOn γ (Icc a b)).toReal`. -/
theorem ae_norm_deriv_arcLengthReparam_toReal (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) : ∀ᵐ s ∂(volume.restrict (Icc 0 (eVariationOn γ (Icc a
    b)).toReal)), ‖deriv (arcLengthReparam γ a b) s‖ = 1 := by
  rw [← variationOnFromTo_Icc_self_right hab]; exact ae_norm_deriv_arcLengthReparam hab hγ hc
/-- Speed integral of `arcLengthReparam γ a b` over `[0, (eVariationOn γ (Icc a b)).toReal]`. -/
@[simp] theorem intervalIntegral_norm_deriv_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn
    γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) : ∫ s in 0..(eVariationOn γ (Icc a b)).toReal,
    ‖deriv (arcLengthReparam γ a b) s‖ = (eVariationOn γ (Icc a b)).toReal := by
  simpa using intervalIntegral_norm_deriv_eq_of_ae_eq_const ENNReal.toReal_nonneg
    (ae_norm_deriv_arcLengthReparam_toReal hab hγ hc)
/-- **Unit-speed energy identity** for `arcLengthReparam γ a b`. -/
@[simp] theorem intervalIntegral_norm_deriv_sq_arcLengthReparam (hab : a ≤ b) (hγ :
    BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) : ∫ s in 0..(eVariationOn γ (Icc
    a b)).toReal, ‖deriv (arcLengthReparam γ a b) s‖ ^ 2 = (eVariationOn γ (Icc a b)).toReal := by
  simpa using intervalIntegral_norm_deriv_sq_eq_of_ae_eq_const ENNReal.toReal_nonneg
    (ae_norm_deriv_arcLengthReparam_toReal hab hγ hc)
/-- Length--energy product identity for `arcLengthReparam γ a b`. -/
theorem mul_intervalIntegral_norm_deriv_sq_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ
    (Icc a b)) (hc : ContinuousOn γ (Icc a b)) : (eVariationOn γ (Icc a b)).toReal * (∫ s in
    0..(eVariationOn γ (Icc a b)).toReal, ‖deriv (arcLengthReparam γ a b) s‖ ^ 2) = (eVariationOn γ
    (Icc a b)).toReal ^ 2 := by rw [intervalIntegral_norm_deriv_sq_arcLengthReparam hab hγ hc, sq]

end UnitSpeedEnergy

/-! ### Coordinates in `EuclideanSpace ℝ (Fin 2)` and geometric signed area -/

section RectifiableSignedArea
variable {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
/-- Coordinate derivative of a differentiable curve `σ : ℝ → EuclideanSpace ℝ (Fin 2)`. -/
theorem deriv_euclidean_apply {σ : ℝ → EuclideanSpace ℝ (Fin 2)} {t : ℝ} (h : DifferentiableAt ℝ σ
  t) (i : Fin 2) : deriv (fun s ↦ σ s i) t = deriv σ t i := ((EuclideanSpace.proj i : EuclideanSpace
  ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t h.hasDerivAt).deriv
/-- Squared norm of a vector in `EuclideanSpace ℝ (Fin 2)` as the sum of squared coordinates. -/
theorem norm_sq_eq_add_sq (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
/-- Squared Euclidean distance in `EuclideanSpace ℝ (Fin 2)` in terms of coordinates. -/
theorem dist_euclidean_sq (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by rw [dist_eq_norm, norm_sq_eq_add_sq]; rfl
/-- Each coordinate of an absolutely continuous curve in `EuclideanSpace ℝ (Fin 2)` is AC. -/
theorem absolutelyContinuousOnInterval_euclidean_coord {σ : ℝ → EuclideanSpace ℝ (Fin 2)} (hσ :
  AbsolutelyContinuousOnInterval σ a b) (i : Fin 2) : AbsolutelyContinuousOnInterval (fun s ↦ σ s i)
  a b := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).lipschitzWith
  |>.comp_absolutelyContinuousOnInterval hσ
/-- Each coordinate of `arcLengthReparam γ a b` is `1`-Lipschitz. -/
theorem lipschitzWith_arcLengthReparam_coord (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc
    : ContinuousOn γ (Icc a b)) (i : Fin 2) : LipschitzWith 1 (fun s ↦ arcLengthReparam γ a b s i)
    := by
  have hσ := lipschitzWith_arcLengthReparam hab hγ hc; rw [lipschitzWith_iff_dist_le_mul] at hσ ⊢
  exact fun s₁ s₂ ↦ (PiLp.norm_apply_le (arcLengthReparam γ a b s₁ - arcLengthReparam γ a b s₂)
    i).trans (hσ s₁ s₂)
/-- Each coordinate of `arcLengthReparam γ a b` is absolutely continuous on every interval. -/
theorem absolutelyContinuousOnInterval_arcLengthReparam_coord (hab : a ≤ b) (hγ : BoundedVariationOn
  γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (i : Fin 2) (s₁ s₂ : ℝ) :
  AbsolutelyContinuousOnInterval (fun s ↦ arcLengthReparam γ a b s i) s₁ s₂ :=
  (lipschitzWith_arcLengthReparam_coord hab hγ hc i).lipschitzOnWith.absolutelyContinuousOnInterval
/-- Each coordinate derivative of `arcLengthReparam γ a b` belongs to `L²` on `Ioc s₁ s₂`. -/
theorem memLp_deriv_arcLengthReparam_coord_Ioc (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (i : Fin 2) (s₁ s₂ : ℝ) :
    MemLp (deriv (fun s ↦ arcLengthReparam γ a b s i)) 2 (volume.restrict (Ioc s₁ s₂)) :=
  MemLp.of_bound (aestronglyMeasurable_deriv _ _) 1 (Filter.Eventually.of_forall fun _ ↦ by
    simpa using norm_deriv_le_of_lipschitz (lipschitzWith_arcLengthReparam_coord hab hγ hc i))
/-- Periodicity of `arcLengthReparam γ a b` on `[0, (eVariationOn γ (Icc a b)).toReal]`. -/
theorem arcLengthReparam_add_toReal_eq_zero {X : Type*} [EMetricSpace X] {γ : ℝ → X} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) :
    arcLengthReparam γ a b (0 + (eVariationOn γ (Icc a b)).toReal) = arcLengthReparam γ a b 0 := by
  rw [zero_add, ← variationOnFromTo_Icc_self_right hab]
  exact (arcLengthReparam_closed hab hγ hc hclosed).symm
/-- Coordinate energy integral of `arcLengthReparam γ a b` on `[0, (eVariationOn γ _).toReal]`. -/
theorem intervalIntegral_deriv_coord_sq_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ
    (Icc a b)) (hc : ContinuousOn γ (Icc a b)) : (∫ s in 0..(eVariationOn γ (Icc a b)).toReal,
    (deriv (fun u ↦ arcLengthReparam γ a b u 0) s ^ 2 + deriv (fun u ↦ arcLengthReparam γ a b u 1) s
    ^ 2)) = (eVariationOn γ (Icc a b)).toReal := by
  have hac := absolutelyContinuousOnInterval_arcLengthReparam hab hγ hc 0 (eVariationOn γ (Icc a
    b)).toReal
  have hcongr : (∫ s in 0..(eVariationOn γ (Icc a b)).toReal,
      (deriv (fun u ↦ arcLengthReparam γ a b u 0) s ^ 2 +
        deriv (fun u ↦ arcLengthReparam γ a b u 1) s ^ 2)) =
      ∫ s in 0..(eVariationOn γ (Icc a b)).toReal, ‖deriv (arcLengthReparam γ a b) s‖ ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with s hs hmem
    have hd := hs (uIoc_subset_uIcc hmem)
    rw [deriv_euclidean_apply hd 0, deriv_euclidean_apply hd 1, norm_sq_eq_add_sq]
  rw [hcongr, intervalIntegral_norm_deriv_sq_arcLengthReparam hab hγ hc]
/-- Signed area of a plane curve `γ : ℝ → EuclideanSpace ℝ (Fin 2)` on `[a, a + T]`. -/
noncomputable def signedAreaEuclidean (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a T : ℝ) : ℝ := signedArea
  (fun t ↦ γ t 0) (fun t ↦ γ t 1) a T
/-- **Geometric signed area** of a rectifiable plane curve via `arcLengthReparam γ a b`. -/
noncomputable def rectifiableSignedArea (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : ℝ :=
  signedArea (fun s ↦ arcLengthReparam γ a b s 0) (fun s ↦ arcLengthReparam γ a b s 1) 0
  (eVariationOn γ (Icc a b)).toReal
/-- `rectifiableSignedArea` expressed via `signedAreaEuclidean`. -/
theorem rectifiableSignedArea_eq_signedAreaEuclidean (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
  rectifiableSignedArea γ a b = signedAreaEuclidean (arcLengthReparam γ a b) 0 (eVariationOn γ (Icc
  a b)).toReal := rfl
/-- `rectifiableSignedArea γ a b` via `variationOnFromTo γ (Icc a b) a b` for `a ≤ b`. -/
theorem rectifiableSignedArea_eq_variationOnFromTo (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (hab : a ≤ b)
    : rectifiableSignedArea γ a b = signedArea (fun s ↦ arcLengthReparam γ a b s 0) (fun s ↦
    arcLengthReparam γ a b s 1) 0 (variationOnFromTo γ (Icc a b) a b) := by
  rw [rectifiableSignedArea, variationOnFromTo_Icc_self_right hab]
/-- If `eVariationOn γ (Icc a b) = 0`, then `rectifiableSignedArea γ a b = 0`. -/
theorem rectifiableSignedArea_of_eVariationOn_eq_zero (h0 : eVariationOn γ (Icc a b) = 0) :
    rectifiableSignedArea γ a b = 0 := by simp [rectifiableSignedArea, h0]
/-- On a singleton interval `[a, a]`, `rectifiableSignedArea γ a a = 0`. -/
@[simp] theorem rectifiableSignedArea_self (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a : ℝ) :
    rectifiableSignedArea γ a a = 0 := by simp [rectifiableSignedArea]
/-- Integration-by-parts representation `∫ x dy` of `rectifiableSignedArea`. -/
theorem rectifiableSignedArea_eq_integral_mul_deriv (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a
    b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) : rectifiableSignedArea γ a b = ∫ s in
    0..(eVariationOn γ (Icc a b)).toReal, arcLengthReparam γ a b s 0 * deriv (fun u ↦
    arcLengthReparam γ a b u 1) s := by
  have hcl := arcLengthReparam_add_toReal_eq_zero hab hγ hc hclosed
  simpa [rectifiableSignedArea, zero_add] using signedArea_eq_integral_mul_deriv
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 0 0 _)
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 1 0 _) (congrArg (fun v :
    EuclideanSpace ℝ (Fin 2) ↦ v 0) hcl) (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hcl)
/-- Integration-by-parts representation `- ∫ y dx` of `rectifiableSignedArea`. -/
theorem rectifiableSignedArea_eq_neg_integral_deriv_mul (hab : a ≤ b) (hγ : BoundedVariationOn γ
    (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) : rectifiableSignedArea γ a b =
    -∫ s in 0..(eVariationOn γ (Icc a b)).toReal, deriv (fun u ↦ arcLengthReparam γ a b u 0) s *
    arcLengthReparam γ a b s 1 := by
  have hcl := arcLengthReparam_add_toReal_eq_zero hab hγ hc hclosed
  simpa [rectifiableSignedArea, zero_add] using signedArea_eq_neg_integral_deriv_mul
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 0 0 _)
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 1 0 _) (congrArg (fun v :
    EuclideanSpace ℝ (Fin 2) ↦ v 0) hcl) (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hcl)

end RectifiableSignedArea

/-! ### Sharp length--signed-area isoperimetric inequality and circle trace rigidity -/

section IsoperimetricInequalityAndRigidity
variable {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
/-- **Sharp length--signed-area isoperimetric inequality** for closed rectifiable plane curves. -/
theorem four_mul_pi_mul_abs_rectifiableSignedArea_le (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a
    b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) : 4 * Real.pi * |rectifiableSignedArea
    γ a b| ≤ (eVariationOn γ (Icc a b)).toReal ^ 2 := by
  rcases (ENNReal.toReal_nonneg (a := eVariationOn γ (Icc a b))).eq_or_lt with hL0 | hL
  · rw [rectifiableSignedArea, ← hL0, signedArea_zero_right, abs_zero, mul_zero, sq, mul_zero]
  · have hcl := arcLengthReparam_add_toReal_eq_zero hab hγ hc hclosed
    have hle := four_mul_pi_mul_abs_signedArea_le hL
      (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 0 0 _)
      (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 1 0 _) (congrArg (fun v :
      EuclideanSpace ℝ (Fin 2) ↦ v 0) hcl) (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hcl)
      (memLp_deriv_arcLengthReparam_coord_Ioc hab hγ hc 0 0 _)
      (memLp_deriv_arcLengthReparam_coord_Ioc hab hγ hc 1 0 _)
    simpa only [rectifiableSignedArea, zero_add, intervalIntegral_deriv_coord_sq_arcLengthReparam
      hab hγ hc, ← sq] using hle
/-- **Sharp length--signed-area inequality** (positive orientation). -/
theorem four_mul_pi_mul_rectifiableSignedArea_le (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
  (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) : 4 * Real.pi * rectifiableSignedArea γ a b
  ≤ (eVariationOn γ (Icc a b)).toReal ^ 2 := (mul_le_mul_of_nonneg_left (le_abs_self _) (by
  positivity)).trans (four_mul_pi_mul_abs_rectifiableSignedArea_le hab hγ hc hclosed)
/-- **Sharp length--signed-area inequality** (negative orientation). -/
theorem neg_four_mul_pi_mul_rectifiableSignedArea_le (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a
    b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) : -(4 * Real.pi *
    rectifiableSignedArea γ a b) ≤ (eVariationOn γ (Icc a b)).toReal ^ 2 := by
  rw [← mul_neg]; exact (mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)).trans
    (four_mul_pi_mul_abs_rectifiableSignedArea_le hab hγ hc hclosed)
/-- **Sharp Hausdorff-length--signed-area inequality** for a simple closed rectifiable curve. -/
theorem four_mul_pi_mul_abs_rectifiableSignedArea_le_hausdorff (hab : a ≤ b) (hγ :
    BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj :
    InjOn γ (Ico a b)) : 4 * Real.pi * |rectifiableSignedArea γ a b| ≤ (μHE[1] (γ '' Icc a
    b)).toReal ^ 2 := by
  rw [euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hc hinj]
  exact four_mul_pi_mul_abs_rectifiableSignedArea_le hab hγ hc hclosed
/-- **Circle rigidity for `rectifiableSignedArea`** via `arcLengthReparam γ a b`. -/
theorem four_mul_pi_mul_abs_rectifiableSignedArea_eq_iff (hab : a ≤ b) (hγ : BoundedVariationOn γ
    (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hL : 0 < (eVariationOn γ (Icc
    a b)).toReal) : 4 * Real.pi * |rectifiableSignedArea γ a b| = (eVariationOn γ (Icc a b)).toReal
    ^ 2 ↔ (∃ c₁ c₂ r₁ r₂ : ℝ, ∀ s ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal, arcLengthReparam γ a b
    s 0 = c₁ + r₁ * Real.cos (2 * Real.pi * s / (eVariationOn γ (Icc a b)).toReal) - r₂ * Real.sin
    (2 * Real.pi * s / (eVariationOn γ (Icc a b)).toReal) ∧ arcLengthReparam γ a b s 1 = c₂ + r₁ *
    Real.sin (2 * Real.pi * s / (eVariationOn γ (Icc a b)).toReal) + r₂ * Real.cos (2 * Real.pi * s
    / (eVariationOn γ (Icc a b)).toReal)) ∨ (∃ c₁ c₂ r₁ r₂ : ℝ, ∀ s ∈ Icc 0 (eVariationOn γ (Icc a
    b)).toReal, arcLengthReparam γ a b s 0 = c₁ + r₁ * Real.cos (2 * Real.pi * s / (eVariationOn γ
    (Icc a b)).toReal) + r₂ * Real.sin (2 * Real.pi * s / (eVariationOn γ (Icc a b)).toReal) ∧
    arcLengthReparam γ a b s 1 = c₂ - r₁ * Real.sin (2 * Real.pi * s / (eVariationOn γ (Icc a
    b)).toReal) + r₂ * Real.cos (2 * Real.pi * s / (eVariationOn γ (Icc a b)).toReal)) := by
  have hcl := arcLengthReparam_add_toReal_eq_zero hab hγ hc hclosed
  have hiff := four_mul_pi_mul_abs_signedArea_eq_iff hL
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 0 0 _)
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 1 0 _) (congrArg (fun v :
    EuclideanSpace ℝ (Fin 2) ↦ v 0) hcl) (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hcl)
    (memLp_deriv_arcLengthReparam_coord_Ioc hab hγ hc 0 0 _) (memLp_deriv_arcLengthReparam_coord_Ioc
    hab hγ hc 1 0 _)
  simpa only [rectifiableSignedArea, zero_add, sub_zero,
    intervalIntegral_deriv_coord_sq_arcLengthReparam hab hγ hc, ← sq] using hiff
/-- Positively oriented rotated circle curve on `[0, T]`. -/
noncomputable def rotatedCircle (c₁ c₂ r₁ r₂ T s : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[c₁ + r₁ *
  Real.cos (2 * Real.pi * s / T) - r₂ * Real.sin (2 * Real.pi * s / T), c₂ + r₁ * Real.sin (2 *
  Real.pi * s / T) + r₂ * Real.cos (2 * Real.pi * s / T)]
/-- Image of `[0, T]` (`0 < T`) under `rotatedCircle c₁ c₂ r₁ r₂ T`. -/
theorem image_rotatedCircle_Icc {T : ℝ} (hT : 0 < T) (c₁ c₂ r₁ r₂ : ℝ) : rotatedCircle c₁ c₂ r₁ r₂ T
    '' Icc 0 T = Metric.sphere (!₂[c₁, c₂] : EuclideanSpace ℝ (Fin 2)) (Real.sqrt (r₁ ^ 2 + r₂ ^ 2))
    := by
  set c : EuclideanSpace ℝ (Fin 2) := !₂[c₁, c₂]; set R := Real.sqrt (r₁ ^ 2 + r₂ ^ 2)
  have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
  have hR_sq : R ^ 2 = r₁ ^ 2 + r₂ ^ 2 := Real.sq_sqrt (by positivity); refine Subset.antisymm ?_ ?_
  · rintro _ ⟨s, _, rfl⟩
    rw [Metric.mem_sphere, ← sq_eq_sq₀ dist_nonneg hR_nonneg, dist_euclidean_sq, hR_sq]
    simp only [rotatedCircle, c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    calc (c₁ + r₁ * Real.cos (2 * Real.pi * s / T) -
            r₂ * Real.sin (2 * Real.pi * s / T) - c₁) ^ 2 +
          (c₂ + r₁ * Real.sin (2 * Real.pi * s / T) +
            r₂ * Real.cos (2 * Real.pi * s / T) - c₂) ^ 2
        = (r₁ ^ 2 + r₂ ^ 2) * (Real.cos (2 * Real.pi * s / T) ^ 2 +
            Real.sin (2 * Real.pi * s / T) ^ 2) := by ring
      _ = r₁ ^ 2 + r₂ ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  · intro p hp
    rw [Metric.mem_sphere, ← sq_eq_sq₀ dist_nonneg hR_nonneg, dist_euclidean_sq, hR_sq] at hp
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hp
    rcases eq_or_ne (r₁ ^ 2 + r₂ ^ 2) 0 with h0 | hne
    · have hr₁ : r₁ = 0 := by nlinarith [sq_nonneg r₁, sq_nonneg r₂]
      have hr₂ : r₂ = 0 := by nlinarith [sq_nonneg r₁, sq_nonneg r₂]
      have hp0 : p 0 = c₁ := by nlinarith [sq_nonneg (p 0 - c₁), sq_nonneg (p 1 - c₂)]
      have hp1 : p 1 = c₂ := by nlinarith [sq_nonneg (p 0 - c₁), sq_nonneg (p 1 - c₂)]
      refine ⟨0, left_mem_Icc.2 hT.le, ?_⟩
      ext i; fin_cases i <;> simp [rotatedCircle, hr₁, hr₂, hp0, hp1]
    · set u₁ := p 0 - c₁; set u₂ := p 1 - c₂
      set x₀ := (r₁ * u₁ + r₂ * u₂) / (r₁ ^ 2 + r₂ ^ 2)
      set y₀ := (r₁ * u₂ - r₂ * u₁) / (r₁ ^ 2 + r₂ ^ 2)
      have hxy₀ : (!₂[x₀, y₀] : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1 := by
        rw [Metric.mem_sphere, ← sq_eq_sq₀ dist_nonneg zero_le_one, dist_euclidean_sq]
        simp only [PiLp.zero_apply, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, one_pow]; dsimp only [x₀, y₀]; field_simp; nlinarith [hp]
      rw [← image_circleCurve_Icc_two_pi 0 zero_le_one] at hxy₀; rcases hxy₀ with ⟨θ, hθ, hθ_eq⟩
      have hcos : Real.cos θ = x₀ := by
        simpa [circleCurve] using congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hθ_eq
      have hsin : Real.sin θ = y₀ := by
        simpa [circleCurve] using congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hθ_eq
      refine ⟨θ * T / (2 * Real.pi), ⟨div_nonneg (mul_nonneg hθ.1 hT.le) Real.two_pi_pos.le, ?_⟩,
        ?_⟩
      · rw [div_le_iff₀ Real.two_pi_pos]; nlinarith [hθ.2]
      · have harg : 2 * Real.pi * (θ * T / (2 * Real.pi)) / T = θ := by
          have : (2 : ℝ) * Real.pi ≠ 0 := Real.two_pi_pos.ne'; have : T ≠ 0 := hT.ne'; field_simp
        have h0 : c₁ + r₁ * x₀ - r₂ * y₀ = p 0 := by dsimp only [x₀, y₀, u₁, u₂]; field_simp; ring
        have h1 : c₂ + r₁ * y₀ + r₂ * x₀ = p 1 := by dsimp only [x₀, y₀, u₁, u₂]; field_simp; ring
        ext i; fin_cases i <;> simp [rotatedCircle, harg, hcos, hsin, h0, h1]
/-- **Geometric circle trace rigidity** for closed continuous rectifiable plane curves. -/
theorem exists_sphere_trace_of_rectifiableSignedArea_eq (hab : a ≤ b) (hγ : BoundedVariationOn γ
    (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (heq : 4 * Real.pi *
    |rectifiableSignedArea γ a b| = (eVariationOn γ (Icc a b)).toReal ^ 2) : ∃ (c : EuclideanSpace ℝ
    (Fin 2)) (r : ℝ), 0 ≤ r ∧ γ '' Icc a b = Metric.sphere c r := by
  set L := (eVariationOn γ (Icc a b)).toReal
  have hL_eq : variationOnFromTo γ (Icc a b) a b = L := variationOnFromTo_Icc_self_right hab
  rcases (ENNReal.toReal_nonneg (a := eVariationOn γ (Icc a b))).eq_or_lt with hL0 | hL
  · refine ⟨γ a, 0, le_rfl, ?_⟩
    have hconst : ∀ t ∈ Icc a b, γ t = γ a := (hγ.variationOnFromTo_Icc_eq_zero_iff hab).1
      (hL_eq.trans hL0.symm)
    rw [Metric.sphere_zero]
    refine Subset.antisymm (fun _ ⟨t, ht, h⟩ ↦ by simp [← h, hconst t ht]) ?_
    rintro _ rfl; exact ⟨a, left_mem_Icc.2 hab, rfl⟩
  · rw [← image_arcLengthReparam_Icc hab hγ hc, hL_eq]
    rcases (four_mul_pi_mul_abs_rectifiableSignedArea_eq_iff hab hγ hc hclosed hL).1 heq with
      ⟨c₁, c₂, r₁, r₂, hpos⟩ | ⟨c₁, c₂, r₁, r₂, hneg⟩
    · refine ⟨!₂[c₁, c₂], Real.sqrt (r₁ ^ 2 + r₂ ^ 2), Real.sqrt_nonneg _, ?_⟩
      have heqOn : EqOn (arcLengthReparam γ a b) (rotatedCircle c₁ c₂ r₁ r₂ L) (Icc 0 L) := by
        intro s hs; ext i; fin_cases i; exacts [(hpos s hs).1, (hpos s hs).2]
      rw [image_congr heqOn, image_rotatedCircle_Icc hL]
    · refine ⟨!₂[c₁, c₂], Real.sqrt (r₁ ^ 2 + r₂ ^ 2), Real.sqrt_nonneg _, ?_⟩
      have heqOn : EqOn (arcLengthReparam γ a b)
          (rotatedCircle c₁ c₂ r₁ r₂ L ∘ fun s ↦ L - s) (Icc 0 L) := by
        intro s hs; dsimp only [Function.comp_apply, rotatedCircle]
        have harg : 2 * Real.pi * (L - s) / L = -(2 * Real.pi * s / L) + 2 * Real.pi := by
          have : L ≠ 0 := hL.ne'; field_simp; ring
        have hcos : Real.cos (2 * Real.pi * (L - s) / L) = Real.cos (2 * Real.pi * s / L) := by
          rw [harg, Real.cos_add_two_pi, Real.cos_neg]
        have hsin : Real.sin (2 * Real.pi * (L - s) / L) = -Real.sin (2 * Real.pi * s / L) := by
          rw [harg, Real.sin_add_two_pi, Real.sin_neg]
        ext i; (fin_cases i <;> simp [(hneg s hs).1, (hneg s hs).2, hcos, hsin, L]); ring
      have himg : (fun s ↦ L - s) '' Icc 0 L = Icc 0 L := by simp
      rw [image_congr heqOn, image_comp, himg, image_rotatedCircle_Icc hL]
/-- **Simple closed curve circle trace rigidity with exact radius**. -/
theorem exists_sphere_trace_of_rectifiableSignedArea_eq_of_injOn_Ico (hab : a ≤ b) (hγ :
    BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj :
    InjOn γ (Ico a b)) (heq : 4 * Real.pi * |rectifiableSignedArea γ a b| = (eVariationOn γ (Icc a
    b)).toReal ^ 2) : ∃ c : EuclideanSpace ℝ (Fin 2), γ '' Icc a b = Metric.sphere c ((eVariationOn
    γ (Icc a b)).toReal / (2 * Real.pi)) := by
  obtain ⟨c, r, hr, htrace⟩ := exists_sphere_trace_of_rectifiableSignedArea_eq hab hγ hc hclosed heq
  refine ⟨c, ?_⟩
  have hmeas : ENNReal.ofReal (2 * Real.pi * r) = eVariationOn γ (Icc a b) := by
    rw [← euclideanHausdorffMeasure_sphere_two c hr, ← htrace,
      euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hc hinj]
  have htoReal : 2 * Real.pi * r = (eVariationOn γ (Icc a b)).toReal := by
    rw [← hmeas, ENNReal.toReal_ofReal (by positivity)]
  have hr_eq : r = (eVariationOn γ (Icc a b)).toReal / (2 * Real.pi) := by
    rw [← htoReal, mul_div_cancel_left₀ r Real.two_pi_pos.ne']
  rwa [← hr_eq]

end IsoperimetricInequalityAndRigidity

/-! ### Reparametrization invariance, orientation reversal, and agreement on unit-speed curves -/

section ReparametrizationInvariance
variable {X : Type*} [EMetricSpace X]
/-- Equal cumulative variation on `Icc a b` implies equal curve values. -/
theorem eq_of_variationOnFromTo_Icc_eq {γ : ℝ → X} {a b t₁ t₂ : ℝ} (hγ : BoundedVariationOn γ (Icc a
    b)) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) (h : variationOnFromTo γ (Icc a b) a t₁ =
    variationOnFromTo γ (Icc a b) a t₂) : γ t₁ = γ t₂ := by
  rw [← edist_eq_zero, ← nonpos_iff_eq_zero]
  refine (hγ.edist_le_edist_variationOnFromTo_Icc ht₁ ht₂).trans_eq ?_; rw [h, edist_self]
/-- **Uniqueness of the arclength factorization** on `Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem eq_arcLengthReparam_of_comp_variationOnFromTo {γ σ : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hσ : ∀ t ∈ Icc a b, σ (variationOnFromTo γ (Icc a b) a t) = γ t) :
    EqOn σ (arcLengthReparam γ a b) (Icc 0 (variationOnFromTo γ (Icc a b) a b)) := fun s hs ↦ by
  rw [← variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc hs, hσ _ (arcLengthInv_mem_Icc hab hγ hc
    s), variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc hs, arcLengthReparam_apply]
/-- **Independence of `rectifiableSignedArea` from the choice of AC factorization**. -/
theorem rectifiableSignedArea_eq_of_comp_variationOnFromTo {γ σ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b
    : ℝ} (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hσ_ac : AbsolutelyContinuousOnInterval σ 0 (eVariationOn γ (Icc a
    b)).toReal) (hσ : ∀ t ∈ Icc a b, σ (variationOnFromTo γ (Icc a b) a t) = γ t) : signedArea (fun
    s ↦ σ s 0) (fun s ↦ σ s 1) 0 (eVariationOn γ (Icc a b)).toReal = rectifiableSignedArea γ a b :=
    by
  set L := (eVariationOn γ (Icc a b)).toReal; have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hL_eq : variationOnFromTo γ (Icc a b) a b = L := variationOnFromTo_Icc_self_right hab
  have heq : EqOn σ (arcLengthReparam γ a b) (Icc 0 L) := hL_eq ▸
    eq_arcLengthReparam_of_comp_variationOnFromTo hab hγ hc hσ
  have hcl := arcLengthReparam_add_toReal_eq_zero hab hγ hc hclosed
  have hσ_cl : σ (0 + L) = σ 0 := by
    rw [zero_add, heq (right_mem_Icc.2 hL), heq (left_mem_Icc.2 hL), ← zero_add L, hcl]
  have hσ_ac' : AbsolutelyContinuousOnInterval σ 0 (0 + L) := by rwa [zero_add]
  rw [rectifiableSignedArea, signedArea_eq_integral_mul_deriv
    (absolutelyContinuousOnInterval_euclidean_coord hσ_ac' 0)
    (absolutelyContinuousOnInterval_euclidean_coord hσ_ac' 1) (congrArg (fun v : EuclideanSpace ℝ
    (Fin 2) ↦ v 0) hσ_cl) (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hσ_cl),
    signedArea_eq_integral_mul_deriv (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ
    hc 0 0 _) (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 1 0 _) (congrArg (fun
    v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hcl) (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1)
    hcl)]
  refine intervalIntegral.integral_congr_ae ?_; rw [zero_add, uIoc_of_le hL]
  filter_upwards [(volume : Measure ℝ).ae_ne L] with t ht hmem
  have hmem_oo : t ∈ Ioo 0 L := ⟨hmem.1, hmem.2.lt_of_ne ht⟩
  have hderiv : deriv (fun s ↦ σ s 1) t = deriv (fun s ↦ arcLengthReparam γ a b s 1) t :=
    Filter.EventuallyEq.deriv_eq <| Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hmem_oo)
      fun _ hs ↦ congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) (heq (Ioo_subset_Icc_self hs))
  rw [congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) (heq (Ioo_subset_Icc_self hmem_oo)), hderiv]
/-- **Invariance of `arcLengthReparam` under monotone continuous onto reparametrization**. -/
theorem arcLengthReparam_comp_of_monotoneOn {γ : ℝ → X} {a b c d : ℝ} {φ : ℝ → ℝ} (hcd : c ≤ d) (hγ
    : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hφ : MonotoneOn φ (Icc c d))
    (hcont : ContinuousOn φ (Icc c d)) (hφc : φ c = a) (hφd : φ d = b) : arcLengthReparam (γ ∘ φ) c
    d = arcLengthReparam γ a b := by
  have hab : a ≤ b := hφc ▸ hφd ▸ hφ (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd
  have hmaps : MapsTo φ (Icc c d) (Icc a b) := mapsTo_Icc_of_monotoneOn hφ hφc hφd
  have hγφ : BoundedVariationOn (γ ∘ φ) (Icc c d) :=
    (boundedVariationOn_comp_iff_of_monotoneOn_continuousOn γ hcd hφ hcont hφc hφd).2 hγ
  have hcφ : ContinuousOn (γ ∘ φ) (Icc c d) := hc.comp hcont hmaps
  ext s; rw [arcLengthReparam_apply, arcLengthReparam_apply, Function.comp_apply]
  have ht : arcLengthInv (γ ∘ φ) c d s ∈ Icc c d := arcLengthInv_mem_Icc hcd hγφ hcφ s
  refine eq_of_variationOnFromTo_Icc_eq hγ (hmaps ht) (arcLengthInv_mem_Icc hab hγ hc s) ?_
  have hpts := variationOnFromTo_comp_pts_eq_of_monotoneOn_continuousOn γ hφ hcont hφc hφd
    (left_mem_Icc.2 hcd) ht
  rw [hφc] at hpts; rw [← hpts, variationOnFromTo_arcLengthInv hcd hγφ hcφ s,
    variationOnFromTo_comp_eq_of_monotoneOn_continuousOn γ hcd hφ hcont hφc hφd,
    variationOnFromTo_arcLengthInv hab hγ hc s]
/-- **Invariance of `rectifiableSignedArea` under monotone continuous onto reparametrization**. -/
theorem rectifiableSignedArea_comp_of_monotoneOn {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b c d : ℝ} {φ
    : ℝ → ℝ} (hcd : c ≤ d) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hφ
    : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d)) (hφc : φ c = a) (hφd : φ d = b) :
    rectifiableSignedArea (γ ∘ φ) c d = rectifiableSignedArea γ a b := by
  rw [rectifiableSignedArea, rectifiableSignedArea, arcLengthReparam_comp_of_monotoneOn hcd hγ hc hφ
    hcont hφc hφd, eVariationOn_comp_eq_of_monotoneOn_continuousOn γ hcd hφ hcont hφc hφd]
/-- **Behavior of `arcLengthReparam` under antitone continuous onto reparametrization**. -/
theorem arcLengthReparam_comp_of_antitoneOn {γ : ℝ → X} {a b c d : ℝ} {φ : ℝ → ℝ} (hcd : c ≤ d) (hγ
    : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hφ : AntitoneOn φ (Icc c d))
    (hcont : ContinuousOn φ (Icc c d)) (hφc : φ c = b) (hφd : φ d = a) (s : ℝ) : arcLengthReparam (γ
    ∘ φ) c d s = arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a b - s) := by
  have hab : a ≤ b := hφd ▸ hφc ▸ hφ (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd
  have hmaps : MapsTo φ (Icc c d) (Icc a b) := mapsTo_Icc_of_antitoneOn hφ hφc hφd
  have hγφ : BoundedVariationOn (γ ∘ φ) (Icc c d) :=
    (boundedVariationOn_comp_iff_of_antitoneOn_continuousOn γ hcd hφ hcont hφc hφd).2 hγ
  have hcφ : ContinuousOn (γ ∘ φ) (Icc c d) := hc.comp hcont hmaps
  set L := variationOnFromTo γ (Icc a b) a b
  have hL : 0 ≤ L := variationOnFromTo.nonneg_of_le γ (Icc a b) hab
  set t := arcLengthInv (γ ∘ φ) c d s; have ht : t ∈ Icc c d := arcLengthInv_mem_Icc hcd hγφ hcφ s
  rw [arcLengthReparam_apply, arcLengthReparam_apply, Function.comp_apply]
  refine eq_of_variationOnFromTo_Icc_eq hγ (hmaps ht) (arcLengthInv_mem_Icc hab hγ hc (L - s)) ?_
  have hadd := variationOnFromTo.add hγ.locallyBoundedVariationOn (left_mem_Icc.2 hab) (hmaps ht)
    (right_mem_Icc.2 hab)
  have hpts := variationOnFromTo_comp_pts_eq_neg_of_antitoneOn_continuousOn γ hφ hcont hφc hφd
    (left_mem_Icc.2 hcd) ht
  rw [hφc, variationOnFromTo.eq_neg_swap γ (Icc a b) b (φ t), neg_neg] at hpts
  have hval : variationOnFromTo γ (Icc a b) a (φ t) =
      L - variationOnFromTo (γ ∘ φ) (Icc c d) c t := by linarith [hadd, hpts]
  rw [hval, variationOnFromTo_arcLengthInv hcd hγφ hcφ s,
    variationOnFromTo_comp_eq_of_antitoneOn_continuousOn γ hcd hφ hcont hφc hφd,
    variationOnFromTo_arcLengthInv hab hγ hc (L - s)]
  change L - max 0 (min L s) = max 0 (min L (L - s)); rcases le_total s 0 with hs₀ | hs₀
  · rw [min_eq_right (hs₀.trans hL), max_eq_left hs₀, sub_zero,
      min_eq_left (by linarith), max_eq_right hL]
  rcases le_total L s with hsL | hsL
  · rw [min_eq_left hsL, max_eq_right hL, sub_self,
      min_eq_right (by linarith), max_eq_left (by linarith)]
  · rw [min_eq_right hsL, max_eq_right hs₀,
      min_eq_right (by linarith), max_eq_right (by linarith)]
/-- Under time reversal `t ↦ a + b - t` on `Icc a b`, `arcLengthReparam` reverses `s ↦ L - s`. -/
theorem arcLengthReparam_reverse {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc
  a b)) (hc : ContinuousOn γ (Icc a b)) (s : ℝ) : arcLengthReparam (fun t ↦ γ (a + b - t)) a b s =
  arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a b - s) :=
  arcLengthReparam_comp_of_antitoneOn hab hγ hc (antitoneOn_add_sub_Icc a b) (continuousOn_const.sub
  continuousOn_id) (by ring) (by ring) s
/-- **Sign reversal of `rectifiableSignedArea` under antitone continuous reparametrization**. -/
theorem rectifiableSignedArea_comp_of_antitoneOn {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b c d : ℝ} {φ
    : ℝ → ℝ} (hcd : c ≤ d) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d)) (hφc : φ
    c = b) (hφd : φ d = a) : rectifiableSignedArea (γ ∘ φ) c d = -rectifiableSignedArea γ a b := by
  have hab : a ≤ b := hφd ▸ hφc ▸ hφ (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd
  have hmaps : MapsTo φ (Icc c d) (Icc a b) := mapsTo_Icc_of_antitoneOn hφ hφc hφd
  have hγφ : BoundedVariationOn (γ ∘ φ) (Icc c d) :=
    (boundedVariationOn_comp_iff_of_antitoneOn_continuousOn γ hcd hφ hcont hφc hφd).2 hγ
  have hcφ : ContinuousOn (γ ∘ φ) (Icc c d) := hc.comp hcont hmaps
  set T := (eVariationOn γ (Icc a b)).toReal
  have hL_eq : variationOnFromTo γ (Icc a b) a b = T := variationOnFromTo_Icc_self_right hab
  have hcl := arcLengthReparam_add_toReal_eq_zero hab hγ hc hclosed
  have hclφ : (γ ∘ φ) c = (γ ∘ φ) d := by simp [Function.comp_apply, hφc, hφd, hclosed]
  have hcl' := arcLengthReparam_add_toReal_eq_zero hcd hγφ hcφ hclφ
  have hT_eq : (eVariationOn (γ ∘ φ) (Icc c d)).toReal = T := by
    rw [eVariationOn_comp_eq_of_antitoneOn_continuousOn γ hcd hφ hcont hφc hφd]
  rw [hT_eq] at hcl'
  have hreparam : arcLengthReparam (γ ∘ φ) c d = fun s ↦ arcLengthReparam γ a b (T - s) := by
    ext s i; rw [arcLengthReparam_comp_of_antitoneOn hcd hγ hc hφ hcont hφc hφd s, hL_eq]
  rw [rectifiableSignedArea, rectifiableSignedArea, hT_eq, signedArea_eq_integral_mul_deriv
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hcd hγφ hcφ 0 0 _)
    (absolutelyContinuousOnInterval_arcLengthReparam_coord hcd hγφ hcφ 1 0 _) (congrArg (fun v :
    EuclideanSpace ℝ (Fin 2) ↦ v 0) hcl') (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hcl'),
    signedArea_eq_integral_mul_deriv (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ
    hc 0 0 _) (absolutelyContinuousOnInterval_arcLengthReparam_coord hab hγ hc 1 0 _) (congrArg (fun
    v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hcl) (congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1)
    hcl), hreparam]
  have hd : (fun s ↦ arcLengthReparam γ a b (T - s) 0 *
      deriv (fun u ↦ arcLengthReparam γ a b (T - u) 1) s) =
      fun s ↦ -(arcLengthReparam γ a b (T - s) 0 *
        deriv (fun u ↦ arcLengthReparam γ a b u 1) (T - s)) := by
    ext s; rw [deriv_comp_const_sub (f := fun u ↦ arcLengthReparam γ a b u 1)]; ring
  rw [hd, intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left (fun s ↦
    arcLengthReparam γ a b s 0 * deriv (fun u ↦ arcLengthReparam γ a b u 1) s) T, zero_add,
    sub_self, sub_zero]
/-- **Sign reversal of `rectifiableSignedArea` under time reversal `t ↦ a + b - t`**. -/
@[simp] theorem rectifiableSignedArea_reverse {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab : a
  ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) :
  rectifiableSignedArea (fun t ↦ γ (a + b - t)) a b = -rectifiableSignedArea γ a b :=
  rectifiableSignedArea_comp_of_antitoneOn hab hγ hc hclosed (antitoneOn_add_sub_Icc a b)
  (continuousOn_const.sub continuousOn_id) (by ring) (by ring)
/-- For a unit-speed AC curve `γ` on `[0, L]`, `variationOnFromTo γ (Icc 0 L) 0 s = s`. -/
theorem variationOnFromTo_eq_self_of_unitSpeed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {γ : ℝ → E} {L s : ℝ} (hL : 0 ≤ L) (hγ : AbsolutelyContinuousOnInterval
    γ 0 L) (hunit : ∀ᵐ t ∂(volume.restrict (Icc 0 L)), ‖deriv γ t‖ = 1) (hs : s ∈ Icc 0 L) :
    variationOnFromTo γ (Icc 0 L) 0 s = s := by
  have hsub : uIcc 0 s ⊆ uIcc 0 L := by
    rw [uIcc_of_le hs.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hs.2
  have hac_s : AbsolutelyContinuousOnInterval γ 0 s := hγ.mono hsub
  have hunit_s : ∀ᵐ t ∂(volume.restrict (Icc 0 s)), ‖deriv γ t‖ = 1 :=
    ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right hs.2) hunit
  have heq_set : variationOnFromTo γ (Icc 0 L) 0 s = variationOnFromTo γ (uIcc 0 s) 0 s := by
    rw [uIcc_of_le hs.1, variationOnFromTo.eq_of_le _ _ hs.1, variationOnFromTo.eq_of_le _ _ hs.1,
      inter_eq_self_of_subset_right (Icc_subset_Icc_right hs.2), inter_self]
  rw [heq_set, hac_s.variationOnFromTo_eq_integral_norm_deriv,
    intervalIntegral_norm_deriv_eq_of_ae_eq_const hs.1 hunit_s, sub_zero, mul_one]
/-- For a unit-speed AC curve `γ` on `[0, L]`, `arcLengthReparam γ 0 L` agrees with `γ`. -/
theorem eqOn_arcLengthReparam_of_unitSpeed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {γ : ℝ → E} {L : ℝ} (hL : 0 ≤ L) (hγ : AbsolutelyContinuousOnInterval γ
    0 L) (hunit : ∀ᵐ t ∂(volume.restrict (Icc 0 L)), ‖deriv γ t‖ = 1) : EqOn (arcLengthReparam γ 0
    L) γ (Icc 0 L) := by
  have hbv : BoundedVariationOn γ (Icc 0 L) := by
    simpa [uIcc_of_le hL] using hγ.boundedVariationOn
  have hc : ContinuousOn γ (Icc 0 L) := by simpa [uIcc_of_le hL] using hγ.continuousOn
  have hL_var : variationOnFromTo γ (Icc 0 L) 0 L = L := variationOnFromTo_eq_self_of_unitSpeed hL
    hγ hunit (right_mem_Icc.2 hL)
  intro s hs; have hs' : s ∈ Icc 0 (variationOnFromTo γ (Icc 0 L) 0 L) := by rwa [hL_var]
  exact (eq_arcLengthReparam_of_comp_variationOnFromTo hL hbv hc
    (fun t ht ↦ by rw [variationOnFromTo_eq_self_of_unitSpeed hL hγ hunit ht]) hs').symm
/-- **Agreement of `rectifiableSignedArea` with `signedArea`** for unit-speed AC curves. -/
theorem rectifiableSignedArea_eq_signedArea_of_unitSpeed {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {L : ℝ}
    (hL : 0 ≤ L) (hγ : AbsolutelyContinuousOnInterval γ 0 L) (hclosed : γ 0 = γ L) (hunit : ∀ᵐ t
    ∂(volume.restrict (Icc 0 L)), ‖deriv γ t‖ = 1) : rectifiableSignedArea γ 0 L = signedArea (fun s
    ↦ γ s 0) (fun s ↦ γ s 1) 0 L := by
  have hbv : BoundedVariationOn γ (Icc 0 L) := by
    simpa [uIcc_of_le hL] using hγ.boundedVariationOn
  have hc : ContinuousOn γ (Icc 0 L) := by simpa [uIcc_of_le hL] using hγ.continuousOn
  have hL_var : (eVariationOn γ (Icc 0 L)).toReal = L := by
    rw [← variationOnFromTo_Icc_self_right hL]
    exact variationOnFromTo_eq_self_of_unitSpeed hL hγ hunit (right_mem_Icc.2 hL)
  have h := (rectifiableSignedArea_eq_of_comp_variationOnFromTo hL hbv hc hclosed
    (by rwa [hL_var]) fun t ht ↦ by
      rw [variationOnFromTo_eq_self_of_unitSpeed hL hγ hunit ht]).symm
  rwa [hL_var] at h
/-- Total variation of `circleCurve c r` over `[0, 2π]` for arbitrary `r : ℝ`. -/
theorem eVariationOn_circleCurve_two_pi_abs (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) : eVariationOn
    (circleCurve c r) (Icc 0 (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi * |r|) := by
  have hac := absolutelyContinuousOnInterval_circleCurve c r 0 (2 * Real.pi)
  rw [hac.eVariationOn_eq_ofReal_integral_norm_deriv Real.two_pi_pos.le]
  simp_rw [norm_deriv_circleCurve]; simp
/-- `circleCurve c r` has bounded variation on every interval `Icc a b`. -/
theorem boundedVariationOn_circleCurve_Icc (c : EuclideanSpace ℝ (Fin 2)) (r a b : ℝ) :
  BoundedVariationOn (circleCurve c r) (Icc a b) := (absolutelyContinuousOnInterval_circleCurve c r
  a b).boundedVariationOn.mono fun _ hx ↦ uIcc_of_le (hx.1.trans hx.2) ▸ hx
/-- Cumulative signed variation of `circleCurve c r` on `Icc 0 (2 * π)` (`0 ≤ r`). -/
theorem variationOnFromTo_circleCurve_two_pi (c : EuclideanSpace ℝ (Fin 2)) {r t : ℝ} (hr : 0 ≤ r)
    (ht : t ∈ Icc 0 (2 * Real.pi)) : variationOnFromTo (circleCurve c r) (Icc 0 (2 * Real.pi)) 0 t =
    t * r := by
  rw [variationOnFromTo.eq_of_le _ _ ht.1, inter_eq_self_of_subset_right (Icc_subset_Icc_right
    ht.2), eVariationOn_circleCurve_Icc c hr ht.1, sub_zero, ENNReal.toReal_ofReal (mul_nonneg ht.1
    hr)]
/-- Canonical arclength reparametrization of `circleCurve c r` on `[0, 2π]` (`0 < r`). -/
theorem arcLengthReparam_circleCurve_apply (c : EuclideanSpace ℝ (Fin 2)) {r s : ℝ} (hr : 0 < r) (hs
    : s ∈ Icc 0 (2 * Real.pi * r)) : arcLengthReparam (circleCurve c r) 0 (2 * Real.pi) s =
    circleCurve c r (s / r) := by
  have hvar : variationOnFromTo (circleCurve c r) (Icc 0 (2 * Real.pi)) 0 (2 * Real.pi) = 2 *
    Real.pi * r := variationOnFromTo_circleCurve_two_pi c hr.le (right_mem_Icc.2 Real.two_pi_pos.le)
  have hs' :
      s ∈ Icc 0 (variationOnFromTo (circleCurve c r) (Icc 0 (2 * Real.pi)) 0 (2 * Real.pi)) := by
    rwa [hvar]
  exact (eq_arcLengthReparam_of_comp_variationOnFromTo (σ := fun u ↦ circleCurve c r (u / r))
    Real.two_pi_pos.le (boundedVariationOn_circleCurve_Icc c r 0 (2 * Real.pi))
    (continuous_circleCurve c r).continuousOn
    (fun t ht ↦ by
      rw [variationOnFromTo_circleCurve_two_pi c hr.le ht, mul_div_cancel_right₀ t hr.ne'])
    hs').symm
/-- **Geometric signed area of `circleCurve c r` over `[0, 2π]`** (`0 ≤ r`). -/
@[simp] theorem rectifiableSignedArea_circleCurve (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤
    r) : rectifiableSignedArea (circleCurve c r) 0 (2 * Real.pi) = Real.pi * r ^ 2 := by
  rcases hr.eq_or_lt with rfl | hpos
  · simp [rectifiableSignedArea, eVariationOn_circleCurve_two_pi c le_rfl]
  · set L := 2 * Real.pi * r; have hL : 0 < L := by positivity
    have hvar : (eVariationOn (circleCurve c r) (Icc 0 (2 * Real.pi))).toReal = L := by
      rw [eVariationOn_circleCurve_two_pi c hr, ENNReal.toReal_ofReal hL.le]
    have hcl : circleCurve c r 0 = circleCurve c r (2 * Real.pi) := by
      simpa using ((periodic_circleCurve c r) 0).symm
    have hσ_ac : AbsolutelyContinuousOnInterval (fun s ↦ circleCurve c r (s / r)) 0 L :=
      contDiff_const.contDiffOn.absolutelyContinuousOnInterval.add
      (absolutelyContinuousOnInterval_vec2 (contDiff_const.mul (Real.contDiff_cos.comp
      (contDiff_id.div_const r))).contDiffOn.absolutelyContinuousOnInterval (contDiff_const.mul
      (Real.contDiff_sin.comp (contDiff_id.div_const r))).contDiffOn.absolutelyContinuousOnInterval)
    have harea := rectifiableSignedArea_eq_of_comp_variationOnFromTo
      (σ := fun s ↦ circleCurve c r (s / r)) Real.two_pi_pos.le
      (boundedVariationOn_circleCurve_Icc c r 0 (2 * Real.pi))
      (continuous_circleCurve c r).continuousOn hcl (by rwa [hvar])
      (fun t ht ↦ by
        rw [variationOnFromTo_circleCurve_two_pi c hr ht, mul_div_cancel_right₀ t hpos.ne'])
    rw [← harea, hvar]; have harg (s : ℝ) : 2 * Real.pi * (s - 0) / L = s / r := by
      dsimp [L]; have : (2 : ℝ) * Real.pi ≠ 0 := Real.two_pi_pos.ne'
      have : r ≠ 0 := hpos.ne'; field_simp; ring
    have hx : (fun s ↦ circleCurve c r (s / r) 0) = fun t ↦
        c 0 + r * Real.cos (2 * Real.pi * (t - 0) / L) -
          0 * Real.sin (2 * Real.pi * (t - 0) / L) := by ext s; rw [harg s]; simp [circleCurve]
    have hy : (fun s ↦ circleCurve c r (s / r) 1) = fun t ↦
        c 1 + r * Real.sin (2 * Real.pi * (t - 0) / L) +
          0 * Real.cos (2 * Real.pi * (t - 0) / L) := by ext s; rw [harg s]; simp [circleCurve]
    rw [hx, hy, signedArea_circle_pos hL 0 (c 0) (c 1) r 0]; ring
/-- `circleCurve c r` (`0 ≤ r`) achieves equality in the sharp rectifiable isoperimetric bound. -/
theorem four_mul_pi_mul_abs_rectifiableSignedArea_circleCurve_eq (c : EuclideanSpace ℝ (Fin 2)) {r :
    ℝ} (hr : 0 ≤ r) : 4 * Real.pi * |rectifiableSignedArea (circleCurve c r) 0 (2 * Real.pi)| =
    (eVariationOn (circleCurve c r) (Icc 0 (2 * Real.pi))).toReal ^ 2 := by
  rw [rectifiableSignedArea_circleCurve c hr, eVariationOn_circleCurve_two_pi c hr,
    ENNReal.toReal_ofReal (by positivity), abs_of_nonneg (by positivity)]; ring

end ReparametrizationInvariance

/-! ### The non-absolutely-continuous Cantor-reparametrized circle -/

section CantorCircle

/-- Strictly increasing continuous homeomorphism `t ↦ 2 * π * cantorHomeomorphFun t`. -/
noncomputable def cantorAngleFun (t : ℝ) : ℝ := 2 * Real.pi * cantorHomeomorphFun t
/-- `cantorAngleFun 0 = 0`. -/
@[simp] theorem cantorAngleFun_zero : cantorAngleFun 0 = 0 := by simp [cantorAngleFun]
/-- `cantorAngleFun 1 = 2 * π`. -/
@[simp] theorem cantorAngleFun_one : cantorAngleFun 1 = 2 * Real.pi := by simp [cantorAngleFun]
/-- `cantorAngleFun` is continuous. -/
@[fun_prop] theorem continuous_cantorAngleFun : Continuous cantorAngleFun := continuous_const.mul
  continuous_cantorHomeomorphFun
/-- `cantorAngleFun` is strictly increasing. -/
theorem strictMono_cantorAngleFun : StrictMono cantorAngleFun :=
  strictMono_cantorHomeomorphFun.const_mul Real.two_pi_pos
/-- `cantorAngleFun` is monotone. -/
theorem monotone_cantorAngleFun : Monotone cantorAngleFun := strictMono_cantorAngleFun.monotone
/-- `cantorAngleFun` maps `Icc 0 1` onto `Icc 0 (2 * π)`. -/
@[simp] theorem image_cantorAngleFun_Icc : cantorAngleFun '' Icc 0 1 = Icc 0 (2 * Real.pi) :=
  image_Icc_of_monotoneOn_continuousOn zero_le_one (monotone_cantorAngleFun.monotoneOn _)
  continuous_cantorAngleFun.continuousOn cantorAngleFun_zero cantorAngleFun_one
/-- `cantorAngleFun` maps `Ico 0 1` into `Ico 0 (2 * π)`. -/
theorem mapsTo_cantorAngleFun_Ico : MapsTo cantorAngleFun (Ico 0 1) (Ico 0 (2 * Real.pi)) :=
  fun _ ht ↦ ⟨by simpa using monotone_cantorAngleFun ht.1,
    by simpa using strictMono_cantorAngleFun ht.2⟩
/-- Outside `cantorSet`, `cantorAngleFun` has derivative `π`. -/
theorem hasDerivAt_cantorAngleFun_of_not_mem_cantorSet {t : ℝ} (ht : t ∉ cantorSet) : HasDerivAt
    cantorAngleFun Real.pi t := by
  unfold cantorAngleFun
  convert (hasDerivAt_cantorHomeomorphFun_of_not_mem_cantorSet ht).const_mul (2 * Real.pi) using 1
  ring
/-- The **Cantor-reparametrized circle** `t ↦ circleCurve c r (2 * π * cantorHomeomorphFun t)`. -/
noncomputable def cantorCircleCurve (c : EuclideanSpace ℝ (Fin 2)) (r t : ℝ) : EuclideanSpace ℝ (Fin
  2) := circleCurve c r (cantorAngleFun t)
variable (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
/-- `cantorCircleCurve c r` as the composition `circleCurve c r ∘ cantorAngleFun`. -/
theorem cantorCircleCurve_eq_comp : cantorCircleCurve c r = circleCurve c r ∘ cantorAngleFun := rfl
/-- At `0`, `cantorCircleCurve c r 0 = circleCurve c r 0 = c + !₂[r, 0]`. -/
@[simp] theorem cantorCircleCurve_zero : cantorCircleCurve c r 0 = c + !₂[r, 0] := by
  simp [cantorCircleCurve, circleCurve]
/-- `cantorCircleCurve c r` is closed on `[0, 1]`. -/
@[simp] theorem cantorCircleCurve_one : cantorCircleCurve c r 1 = cantorCircleCurve c r 0 := by
  simpa [cantorCircleCurve] using (periodic_circleCurve c r) 0
/-- `cantorCircleCurve c r` is continuous on `ℝ`. -/
@[fun_prop] theorem continuous_cantorCircleCurve : Continuous (cantorCircleCurve c r) :=
  (continuous_circleCurve c r).comp continuous_cantorAngleFun
/-- `cantorCircleCurve c r` is continuous on `Icc 0 1`. -/
theorem continuousOn_cantorCircleCurve : ContinuousOn (cantorCircleCurve c r) (Icc 0 1) :=
  (continuous_cantorCircleCurve c r).continuousOn
/-- For `r ≠ 0`, `cantorCircleCurve c r` is a simple closed curve on `[0, 1]`. -/
theorem injOn_cantorCircleCurve_Ico {r : ℝ} (hr : r ≠ 0) : InjOn (cantorCircleCurve c r) (Ico 0 1)
  := (injOn_circleCurve_Ico c hr).comp strictMono_cantorAngleFun.injective.injOn
  mapsTo_cantorAngleFun_Ico
/-- For `0 ≤ r`, the trace of `cantorCircleCurve c r` on `Icc 0 1` is `Metric.sphere c r`. -/
@[simp] theorem image_cantorCircleCurve_Icc {r : ℝ} (hr : 0 ≤ r) : cantorCircleCurve c r '' Icc 0 1
    = Metric.sphere c r := by
  rw [cantorCircleCurve_eq_comp, image_comp, image_cantorAngleFun_Icc, image_circleCurve_Icc_two_pi
    c hr]
/-- Total variation of `cantorCircleCurve c r` on `Icc 0 1` for arbitrary `r : ℝ`. -/
theorem eVariationOn_cantorCircleCurve_Icc_abs : eVariationOn (cantorCircleCurve c r) (Icc 0 1) =
    ENNReal.ofReal (2 * Real.pi * |r|) := by
  rw [cantorCircleCurve_eq_comp, eVariationOn_comp_eq_of_monotoneOn_continuousOn (circleCurve c r)
    zero_le_one (monotone_cantorAngleFun.monotoneOn _) continuous_cantorAngleFun.continuousOn
    cantorAngleFun_zero cantorAngleFun_one, eVariationOn_circleCurve_two_pi_abs c r]
/-- For `0 ≤ r`, `eVariationOn (cantorCircleCurve c r) (Icc 0 1) = ENNReal.ofReal (2 * π * r)`. -/
@[simp] theorem eVariationOn_cantorCircleCurve_Icc {r : ℝ} (hr : 0 ≤ r) : eVariationOn
    (cantorCircleCurve c r) (Icc 0 1) = ENNReal.ofReal (2 * Real.pi * r) := by
  rw [eVariationOn_cantorCircleCurve_Icc_abs, abs_of_nonneg hr]
/-- `cantorCircleCurve c r` has bounded variation on `Icc 0 1`. -/
theorem boundedVariationOn_cantorCircleCurve_Icc : BoundedVariationOn (cantorCircleCurve c r) (Icc 0
    1) := by
  rw [BoundedVariationOn, eVariationOn_cantorCircleCurve_Icc_abs]; exact ENNReal.ofReal_ne_top
/-- Cumulative signed variation of `cantorCircleCurve c r` on `Icc 0 1` (`0 ≤ r`). -/
theorem variationOnFromTo_cantorCircleCurve_Icc {r t : ℝ} (hr : 0 ≤ r) (ht : t ∈ Icc 0 1) :
    variationOnFromTo (cantorCircleCurve c r) (Icc 0 1) 0 t = 2 * Real.pi * r * cantorHomeomorphFun
    t := by
  have hpts := variationOnFromTo_comp_pts_eq_of_monotoneOn_continuousOn (circleCurve c r)
    (monotone_cantorAngleFun.monotoneOn _) continuous_cantorAngleFun.continuousOn
    cantorAngleFun_zero cantorAngleFun_one (left_mem_Icc.2 zero_le_one) ht
  have hmem : cantorAngleFun t ∈ Icc 0 (2 * Real.pi) := mapsTo_Icc_of_monotoneOn
    (monotone_cantorAngleFun.monotoneOn _) cantorAngleFun_zero cantorAngleFun_one ht
  rw [cantorCircleCurve_eq_comp, hpts, cantorAngleFun_zero, variationOnFromTo_circleCurve_two_pi c
    hr hmem, cantorAngleFun]; ring
/-- For `0 ≤ r`, `μHE[1] (cantorCircleCurve c r '' Icc 0 1) = ENNReal.ofReal (2 * π * r)`. -/
theorem euclideanHausdorffMeasure_image_cantorCircleCurve_Icc {r : ℝ} (hr : 0 ≤ r) : μHE[1]
    (cantorCircleCurve c r '' Icc 0 1) = ENNReal.ofReal (2 * Real.pi * r) := by
  rw [image_cantorCircleCurve_Icc c hr, euclideanHausdorffMeasure_sphere_two c hr]
/-- Outside `cantorSet`, `cantorCircleCurve c r` has derivative `π • deriv (circleCurve c r) _`. -/
theorem hasDerivAt_cantorCircleCurve_of_not_mem_cantorSet {t : ℝ} (ht : t ∉ cantorSet) : HasDerivAt
    (cantorCircleCurve c r) (Real.pi • deriv (circleCurve c r) (cantorAngleFun t)) t := by
  rw [deriv_circleCurve]; exact (hasDerivAt_circleCurve c r (cantorAngleFun t)).scomp t
    (hasDerivAt_cantorAngleFun_of_not_mem_cantorSet ht)
/-- Outside `cantorSet`, `‖deriv (cantorCircleCurve c r) t‖ = π * |r|`. -/
theorem norm_deriv_cantorCircleCurve_of_not_mem_cantorSet {t : ℝ} (ht : t ∉ cantorSet) : ‖deriv
    (cantorCircleCurve c r) t‖ = Real.pi * |r| := by
  rw [(hasDerivAt_cantorCircleCurve_of_not_mem_cantorSet c r ht).deriv, norm_smul,
    Real.norm_of_nonneg Real.pi_pos.le, norm_deriv_circleCurve]
/-- Almost everywhere, `‖deriv (cantorCircleCurve c r) t‖ = π * |r|`. -/
theorem ae_norm_deriv_cantorCircleCurve : ∀ᵐ t ∂volume, ‖deriv (cantorCircleCurve c r) t‖ = Real.pi
    * |r| := by
  filter_upwards [compl_mem_ae_iff.mpr volume_cantorSet] with t ht
    using norm_deriv_cantorCircleCurve_of_not_mem_cantorSet c r ht
/-- The naive derivative speed integral `∫ t in 0..1, ‖deriv (cantorCircleCurve c r) t‖`. -/
@[simp] theorem intervalIntegral_norm_deriv_cantorCircleCurve : ∫ t in (0 : ℝ)..1, ‖deriv
    (cantorCircleCurve c r) t‖ = Real.pi * |r| := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ Real.pi * |r|)]; · simp
  · filter_upwards [ae_norm_deriv_cantorCircleCurve c r] with t ht _ using ht
/-- The lower Lebesgue integral `∫⁻ t in Icc 0 1, ‖deriv (cantorCircleCurve c r) t‖ₑ`. -/
@[simp] theorem lintegral_enorm_deriv_cantorCircleCurve : ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv
    (cantorCircleCurve c r) t‖ₑ = ENNReal.ofReal (Real.pi * |r|) := by
  have hae : (fun t ↦ ‖deriv (cantorCircleCurve c r) t‖ₑ) =ᵐ[volume.restrict (Icc 0 1)]
      fun _ ↦ ENNReal.ofReal (Real.pi * |r|) := by
    refine ae_restrict_of_ae ?_; filter_upwards [ae_norm_deriv_cantorCircleCurve c r] with t ht
    rw [← enorm_norm, ht, Real.enorm_of_nonneg (by positivity)]
  rw [lintegral_congr_ae hae, setLIntegral_const, Real.volume_Icc]; simp
/-- **Strict variation gap for `cantorCircleCurve`** (`r ≠ 0`). -/
theorem lintegral_enorm_deriv_cantorCircleCurve_lt_eVariationOn {r : ℝ} (hr : r ≠ 0) : (∫⁻ t in Icc
    (0 : ℝ) 1, ‖deriv (cantorCircleCurve c r) t‖ₑ) < eVariationOn (cantorCircleCurve c r) (Icc 0 1)
    := by
  rw [lintegral_enorm_deriv_cantorCircleCurve, eVariationOn_cantorCircleCurve_Icc_abs]
  have hpos : 0 < |r| := abs_pos.mpr hr
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith [Real.pi_pos])
/-- **The Cantor-reparametrized circle `cantorCircleCurve c r` (`r ≠ 0`) is not AC on `[0, 1]`**. -/
theorem not_absolutelyContinuousOnInterval_cantorCircleCurve {r : ℝ} (hr : r ≠ 0) : ¬
    AbsolutelyContinuousOnInterval (cantorCircleCurve c r) 0 1 := by
  intro hac; exact (lintegral_enorm_deriv_cantorCircleCurve_lt_eVariationOn c hr).ne
    hac.eVariationOn_eq_lintegral_enorm_deriv.symm
/-- `arcLengthReparam` of `cantorCircleCurve` equals `arcLengthReparam` of `circleCurve`. -/
@[simp] theorem arcLengthReparam_cantorCircleCurve_eq_circleCurve : arcLengthReparam
  (cantorCircleCurve c r) 0 1 = arcLengthReparam (circleCurve c r) 0 (2 * Real.pi) :=
  arcLengthReparam_comp_of_monotoneOn zero_le_one (boundedVariationOn_circleCurve_Icc c r 0 (2 *
  Real.pi)) (continuous_circleCurve c r).continuousOn (monotone_cantorAngleFun.monotoneOn _)
  continuous_cantorAngleFun.continuousOn cantorAngleFun_zero cantorAngleFun_one
/-- Formula for `arcLengthReparam (cantorCircleCurve c r) 0 1 s` on `Icc 0 (2 * π * r)`. -/
theorem arcLengthReparam_cantorCircleCurve_apply {r s : ℝ} (hr : 0 < r) (hs : s ∈ Icc 0 (2 * Real.pi
    * r)) : arcLengthReparam (cantorCircleCurve c r) 0 1 s = circleCurve c r (s / r) := by
  rw [arcLengthReparam_cantorCircleCurve_eq_circleCurve, arcLengthReparam_circleCurve_apply c hr hs]
/-- `rectifiableSignedArea` of `cantorCircleCurve` equals that of `circleCurve`. -/
@[simp] theorem rectifiableSignedArea_cantorCircleCurve_eq_circleCurve : rectifiableSignedArea
  (cantorCircleCurve c r) 0 1 = rectifiableSignedArea (circleCurve c r) 0 (2 * Real.pi) :=
  rectifiableSignedArea_comp_of_monotoneOn zero_le_one (boundedVariationOn_circleCurve_Icc c r 0 (2
  * Real.pi)) (continuous_circleCurve c r).continuousOn (monotone_cantorAngleFun.monotoneOn _)
  continuous_cantorAngleFun.continuousOn cantorAngleFun_zero cantorAngleFun_one
/-- **Geometric signed area of `cantorCircleCurve c r` (`0 ≤ r`)** equals `π * r ^ 2`. -/
theorem rectifiableSignedArea_cantorCircleCurve {r : ℝ} (hr : 0 ≤ r) : rectifiableSignedArea
    (cantorCircleCurve c r) 0 1 = Real.pi * r ^ 2 := by
  rw [rectifiableSignedArea_cantorCircleCurve_eq_circleCurve, rectifiableSignedArea_circleCurve c
    hr]
/-- **Sharp isoperimetric equality for the non-AC Cantor circle** (`0 ≤ r`). -/
theorem four_mul_pi_mul_abs_rectifiableSignedArea_cantorCircleCurve_eq {r : ℝ} (hr : 0 ≤ r) : 4 *
    Real.pi * |rectifiableSignedArea (cantorCircleCurve c r) 0 1| = (eVariationOn (cantorCircleCurve
    c r) (Icc 0 1)).toReal ^ 2 ∧ 4 * Real.pi * |rectifiableSignedArea (cantorCircleCurve c r) 0 1| =
    (μHE[1] (cantorCircleCurve c r '' Icc 0 1)).toReal ^ 2 := by
  rw [rectifiableSignedArea_cantorCircleCurve c hr, eVariationOn_cantorCircleCurve_Icc c hr,
    euclideanHausdorffMeasure_image_cantorCircleCurve_Icc c hr, ENNReal.toReal_ofReal (by
    positivity), abs_of_nonneg (by positivity)]; constructor <;> ring

end CantorCircle

end TauCeti
