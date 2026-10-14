/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.IntervalAverage
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Wirtinger's inequality for periodic functions

Let `f : ℝ → V` be an absolutely continuous function on `[a, b]` with `f a = f b`, valued in a
finite-dimensional real inner product space, whose derivative is square integrable. **Wirtinger's
inequality** bounds the `L²` distance of `f` from its mean by its derivative, with the sharp
constant:

`∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤ ((b - a) / (2π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2`
(`TauCeti.integral_norm_sub_average_sq_le_of_absolutelyContinuousOnInterval`, and
`TauCeti.integral_norm_sub_average_sq_le` for everywhere-differentiable functions).

Equality holds if and only if `f - ⨍ y in a..b, f y` is a first harmonic on `[a, b]`:

`f x - ⨍ y in a..b, f y = cos (2π x / (b - a)) • u + sin (2π x / (b - a)) • v` for all `x ∈ [a, b]`
(`TauCeti.integral_norm_sub_average_sq_eq_iff`).

The proof is Fourier-analytic: for `n ≠ 0` integration by parts for absolutely continuous functions
(`TauCeti.fourierCoeffOn_of_absolutelyContinuousOnInterval`) expresses the `n`-th Fourier
coefficient of `f` on `[a, b]` as that of `deriv f` divided by `2πin / (b - a)`, the zeroth
coefficient of `f` minus its mean vanishes, and Parseval's identity (`hasSum_sq_fourierCoeffOn`)
turns the coefficientwise comparison into the inequality and identifies the equality case with the
vanishing of all Fourier modes `n ∉ {-1, 0, 1}`. Vector values reduce to complex scalars
coordinatewise in an orthonormal basis.

Together with the Cauchy--Schwarz inequality it bounds the integral of any continuous bilinear
form along a loop: since `∫ B(m, f') = B(m, f b - f a) = 0` for the mean `m`,

`‖∫ x in a..b, B (f x) (f' x)‖ ≤ ‖B‖ * ((b - a) / (2π)) * ∫ x in a..b, ‖f' x‖ ^ 2`
(`ContinuousLinearMap.norm_integral_apply_apply_le` and
`ContinuousLinearMap.norm_integral_apply_apply_le_of_absolutelyContinuousOnInterval`).

For `B` a symplectic form this is the isoperimetric inequality for the symplectic area of a loop,
the estimate behind removal of singularities and energy quantization for holomorphic curves.

## Main results

* `TauCeti.fourierCoeffOn_of_absolutelyContinuousOnInterval` and
  `TauCeti.fourierCoeffOn_deriv_of_absolutelyContinuousOnInterval`: Fourier integration by parts
  for absolutely continuous functions.
* `TauCeti.integral_norm_sub_average_sq_le_of_absolutelyContinuousOnInterval` and
  `TauCeti.integral_norm_sub_average_sq_le`: Wirtinger's inequality for absolutely continuous and
  everywhere-differentiable periodic functions.
* `TauCeti.integral_norm_sub_average_sq_eq_iff` and
  `TauCeti.integral_norm_sq_eq_iff_of_integral_eq_zero`: first-harmonic characterization of
  equality in Wirtinger's inequality.
* `TauCeti.periodic_wirtinger` and `TauCeti.periodic_wirtinger_eq_iff`: the periodic Wirtinger
  inequality and equality characterization on `[0, T]`.
* `ContinuousLinearMap.norm_integral_apply_apply_le` and
  `ContinuousLinearMap.norm_integral_apply_apply_le_of_absolutelyContinuousOnInterval`: the bound
  on the integral of a bilinear form along a loop.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, Cambridge University Press, 1934,
  Theorem 258 (Wirtinger's inequality).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.4 (the isoperimetric inequality, proved by the
  same Fourier argument).
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval RealInnerProductSpace

namespace TauCeti

variable {a b : ℝ}

/-! ### Calculus and Fourier integration by parts for absolutely continuous functions -/

section AbsolutelyContinuous

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- An absolutely continuous function on `[[a, b]]` with values in a finite-dimensional real inner
product space is differentiable almost everywhere on `[[a, b]]`. -/
theorem ae_differentiableAt_of_finiteDimensional {f : ℝ → V}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ x : ℝ, x ∈ [[a, b]] → DifferentiableAt ℝ f x := by
  set e := stdOrthonormalBasis ℝ V
  have hcoord : ∀ i, ∀ᵐ x : ℝ, x ∈ [[a, b]] → DifferentiableAt ℝ (fun t ↦ ⟪e i, f t⟫) x :=
    fun i ↦ ((innerSL ℝ (e i)).lipschitzWith.comp_absolutelyContinuousOnInterval
      hf).ae_differentiableAt
  filter_upwards [Filter.eventually_all.mpr hcoord] with x hx hmem
  have hsum : DifferentiableAt ℝ (fun t ↦ ∑ i, ⟪e i, f t⟫ • e i) x :=
    DifferentiableAt.fun_sum fun i _ ↦ (hx i hmem).smul_const (e i)
  convert hsum using 1
  ext t
  exact (e.sum_repr' (f t)).symm

/-- The derivative of an absolutely continuous function on `[[a, b]]` with values in a
finite-dimensional real inner product space is interval integrable on `a..b`. -/
theorem intervalIntegrable_deriv_of_finiteDimensional {f : ℝ → V}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b := by
  set e := stdOrthonormalBasis ℝ V
  have hcoord (i) : IntervalIntegrable (fun x ↦ deriv (fun t ↦ ⟪e i, f t⟫) x • e i) volume a b := by
    have hi := ((innerSL ℝ (e i)).lipschitzWith.comp_absolutelyContinuousOnInterval
      hf).intervalIntegrable_deriv
    exact ⟨hi.1.smul_const (e i), hi.2.smul_const (e i)⟩
  have hsum : IntervalIntegrable (fun x ↦ ∑ i, deriv (fun t ↦ ⟪e i, f t⟫) x • e i) volume a b := by
    convert IntervalIntegrable.sum Finset.univ fun i _ ↦ hcoord i with x
    simp
  refine hsum.congr_ae ?_
  filter_upwards [ae_restrict_of_ae (ae_differentiableAt_of_finiteDimensional hf),
    self_mem_ae_restrict measurableSet_uIoc] with x hx hxIoc
  have hxd := hx (uIoc_subset_uIcc hxIoc)
  have hd (i) : deriv (fun t ↦ ⟪e i, f t⟫) x = ⟪e i, deriv f x⟫ :=
    ((innerSL ℝ (e i)).hasFDerivAt.comp_hasDerivAt x hxd.hasDerivAt).deriv
  simp_rw [hd]
  exact e.sum_repr' (deriv f x)

/-- **Fundamental Theorem of Calculus** for absolutely continuous functions into a
finite-dimensional real inner product space. -/
theorem integral_deriv_eq_sub_of_finiteDimensional {f : ℝ → V}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ x in a..b, deriv f x = f b - f a := by
  have hint := intervalIntegrable_deriv_of_finiteDimensional hf
  refine ext_inner_left ℝ fun v ↦ ?_
  change (innerSL ℝ v) (∫ x in a..b, deriv f x) = (innerSL ℝ v) (f b - f a)
  rw [← (innerSL ℝ v).intervalIntegral_comp_comm hint, map_sub]
  have hv := ((innerSL ℝ v).lipschitzWith.comp_absolutelyContinuousOnInterval
    hf).integral_deriv_eq_sub
  simp only [Function.comp_def, innerSL_apply_apply] at hv ⊢
  rw [← hv]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_differentiableAt_of_finiteDimensional hf] with x hx hxIoc
  exact (((innerSL ℝ v).hasFDerivAt.comp_hasDerivAt x
    (hx (uIoc_subset_uIcc hxIoc)).hasDerivAt).deriv).symm

/-- **Integration by parts** for complex-valued absolutely continuous functions. -/
theorem integral_mul_deriv_eq_deriv_mul_complex {f g : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ x in a..b, f x * deriv g x = f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x := by
  have hprod : ∫ x in a..b, (deriv f x * g x + f x * deriv g x) = f b * g b - f a * g a := by
    change ∫ x in a..b, (deriv f x * g x + f x * deriv g x) = f b • g b - f a • g a
    rw [← integral_deriv_eq_sub_of_finiteDimensional (hf.fun_smul hg)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_differentiableAt_of_finiteDimensional hf,
      ae_differentiableAt_of_finiteDimensional hg] with x hxf hxg hxIoc
    have hx := uIoc_subset_uIcc hxIoc
    exact ((hxf hx).hasDerivAt.mul (hxg hx).hasDerivAt).deriv.symm
  rw [← hprod, ← intervalIntegral.integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact ((intervalIntegrable_deriv_of_finiteDimensional hf).mul_continuousOn hg.continuousOn).add
      ((intervalIntegrable_deriv_of_finiteDimensional hg).continuousOn_mul hf.continuousOn)
  · exact (intervalIntegrable_deriv_of_finiteDimensional hf).mul_continuousOn hg.continuousOn

/-- **Fourier integration by parts for absolutely continuous functions**: for `n ≠ 0`, the `n`-th
Fourier coefficient of an absolutely continuous function `f : ℝ → ℂ` on `[a, b]` is expressed in
terms of the boundary jump `f b - f a` and the `n`-th Fourier coefficient of `deriv f`. -/
theorem fourierCoeffOn_of_absolutelyContinuousOnInterval (hab : a < b) {f : ℝ → ℂ} {n : ℤ}
    (hn : n ≠ 0) (hf : AbsolutelyContinuousOnInterval f a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) -
        (b - a) * fourierCoeffOn hab (deriv f) n) := by
  rw [← ofReal_sub]
  have hT : Fact (0 < b - a) := ⟨by linarith⟩
  set G : ℝ → ℂ :=
    fun y : ℝ ↦ ((b - a : ℝ) : ℂ) / (-2 * π * I * n) * fourier (-n) (y : AddCircle (b - a))
  have hG_deriv (x : ℝ) : HasDerivAt G (fourier (-n) (x : AddCircle (b - a))) x :=
    has_antideriv_at_fourier_neg hT hn x
  have hG_lip : LipschitzWith 1 G := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (hG_deriv x).differentiableAt) fun x ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, (hG_deriv x).deriv, NNReal.coe_one]
    exact (fourier (-n)).norm_coe_le_norm (x : AddCircle (b - a)) |>.trans_eq (fourier_norm (-n))
  have hG_ac : AbsolutelyContinuousOnInterval G a b :=
    (hG_lip.lipschitzOnWith).absolutelyContinuousOnInterval
  simp_rw [fourierCoeffOn_eq_integral, smul_eq_mul, real_smul, ofReal_div, ofReal_one]
  conv => pattern (occs := 1 2 3) fourier _ _ * _ <;> (rw [mul_comm])
  have hderivG : (fun x : ℝ ↦ f x * fourier (-n) (x : AddCircle (b - a))) =
      fun x : ℝ ↦ f x * deriv G x := by
    ext x
    rw [(hG_deriv x).deriv]
  rw [hderivG, integral_mul_deriv_eq_deriv_mul_complex hf hG_ac]
  dsimp only [G]
  have : ∀ u v w : ℂ, u * ((b - a : ℝ) / v * w) = (b - a : ℝ) / v * (u * w) := by intros; ring
  conv in intervalIntegral _ _ _ _ => congr; ext; rw [this]
  rw [(by ring :
    ((b - a : ℝ) : ℂ) / (-2 * π * I * n) = ((b - a : ℝ) : ℂ) * (1 / (-2 * π * I * n)))]
  have s2 : (b : AddCircle (b - a)) = (a : AddCircle (b - a)) := by
    simpa using AddCircle.coe_add_period (b - a) a
  rw [s2, intervalIntegral.integral_const_mul, ← sub_mul, mul_sub, mul_sub]
  congr 1
  · conv_lhs => rw [mul_comm, mul_div, mul_one]
    rw [div_eq_iff (ofReal_ne_zero.mpr hT.out.ne')]
    ring
  · ring

/-- For a periodic absolutely continuous function `f : ℝ → ℂ` on `[a, b]` with `f a = f b`, the
`n`-th Fourier coefficient of `deriv f` is `2πin / (b - a)` times that of `f` for every `n : ℤ`. -/
theorem fourierCoeffOn_deriv_of_absolutelyContinuousOnInterval (hab : a < b) {f : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfab : f a = f b) (n : ℤ) :
    fourierCoeffOn hab (deriv f) n =
      2 * π * I * n / (b - a) * fourierCoeffOn hab f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fourierCoeffOn_eq_integral, integral_deriv_eq_sub_of_finiteDimensional hf, hfab]
  · have hba : ((b : ℂ) - a) ≠ 0 := by
      rw [← ofReal_sub]
      exact ofReal_ne_zero.mpr (sub_pos.mpr hab).ne'
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    rw [fourierCoeffOn_of_absolutelyContinuousOnInterval hab hn hf, hfab, sub_self, mul_zero,
       zero_sub]
    field_simp

end AbsolutelyContinuous

/-! ### Complex Fourier characterization of first harmonics -/

section FirstHarmonicComplex

private theorem fourierCoeffOn_fourier (hab : a < b) (m n : ℤ) :
    fourierCoeffOn hab (fun x : ℝ ↦ fourier m (x : AddCircle (b - a))) n =
      if n = m then 1 else 0 := by
  have : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  have h1 : fourierCoeffOn hab (fun x : ℝ ↦ fourier m (x : AddCircle (b - a))) n =
      fourierCoeff (T := b - a) (fourier m) n := by
    rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral (fourier m) n a,
      add_sub_cancel]
  rw [h1, fourierCoeff_fourier, Pi.single_apply]

private theorem fourierCoeffOn_add (hab : a < b) {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) (n : ℤ) :
    fourierCoeffOn hab (fun x ↦ f x + g x) n = fourierCoeffOn hab f n + fourierCoeffOn hab g n := by
  have hc : Continuous (fun x : ℝ ↦ fourier (-n) (x : AddCircle (b - a))) :=
    (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  simp_rw [fourierCoeffOn_eq_integral, smul_eq_mul, mul_add]
  rw [intervalIntegral.integral_add (hf.continuousOn_mul hc.continuousOn)
    (hg.continuousOn_mul hc.continuousOn), smul_add]

private theorem fourierCoeffOn_sub (hab : a < b) {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) (n : ℤ) :
    fourierCoeffOn hab (fun x ↦ f x - g x) n = fourierCoeffOn hab f n - fourierCoeffOn hab g n := by
  have hc : Continuous (fun x : ℝ ↦ fourier (-n) (x : AddCircle (b - a))) :=
    (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  simp_rw [fourierCoeffOn_eq_integral, smul_eq_mul, mul_sub]
  rw [intervalIntegral.integral_sub (hf.continuousOn_mul hc.continuousOn)
    (hg.continuousOn_mul hc.continuousOn), smul_sub]

private theorem memLp_two_of_continuousOn_Icc {h : ℝ → ℂ} (hh : ContinuousOn h (Icc a b)) :
    MemLp h 2 (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  exact MemLp.of_bound ((hh.aestronglyMeasurable measurableSet_Icc).mono_set Ioc_subset_Icc_self) C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx ↦ hC x (Ioc_subset_Icc_self hx))

private theorem eq_zero_of_forall_fourierCoeffOn_eq_zero (hab : a < b) {h : ℝ → ℂ}
    (hh : ContinuousOn h (Icc a b)) (hcoeff : ∀ n : ℤ, fourierCoeffOn hab h n = 0) :
    ∀ x ∈ Icc a b, h x = 0 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hsum := hasSum_sq_fourierCoeffOn hab (memLp_two_of_continuousOn_Icc hh)
  simp only [hcoeff, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    smul_eq_mul] at hsum
  have hint0 : ∫ x in a..b, ‖h x‖ ^ 2 = 0 := by
    have := hsum.unique hasSum_zero
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero hba.ne')
  have hcont_norm : ContinuousOn (fun x ↦ ‖h x‖ ^ 2) (Icc a b) := hh.norm.pow 2
  have hint_norm : IntervalIntegrable (fun x ↦ ‖h x‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hcont_norm.integrableOn_Icc
  have hae : (fun x ↦ ‖h x‖ ^ 2) =ᵐ[volume.restrict (Ioc a b)] 0 :=
    (integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) hint_norm).mp hint0
  have hae_Icc : (fun x ↦ ‖h x‖ ^ 2) =ᵐ[volume.restrict (Icc a b)] 0 :=
    ae_restrict_of_ae_eq_of_ae_restrict Ioc_ae_eq_Icc hae
  have hzero_on := Measure.eqOn_Icc_of_ae_eq volume hab.ne hae_Icc hcont_norm continuousOn_const
  intro x hx
  have hx0 : ‖h x‖ ^ 2 = 0 := hzero_on hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx0)

private theorem fourier_one_add_fourier_neg_one_eq (c₁ c₂ : ℂ) (x : ℝ) :
    c₁ * fourier 1 (x : AddCircle (b - a)) + c₂ * fourier (-1) (x : AddCircle (b - a)) =
      Real.cos (2 * π * x / (b - a)) • (c₁ + c₂) +
        Real.sin (2 * π * x / (b - a)) • ((c₁ - c₂) * I) := by
  set θ : ℝ := 2 * π * x / (b - a)
  have h1 : fourier 1 (x : AddCircle (b - a)) = ↑(Real.cos θ) + ↑(Real.sin θ) * I := by
    rw [fourier_coe_apply, Int.cast_one]
    have hθ : (2 * ↑π * I * 1 * ↑x / ↑(b - a) : ℂ) = ↑θ * I := by
      push_cast [θ]
      ring
    rw [hθ, exp_mul_I, ofReal_cos, ofReal_sin]
  have h2 : fourier (-1) (x : AddCircle (b - a)) = ↑(Real.cos θ) - ↑(Real.sin θ) * I := by
    rw [fourier_coe_apply, Int.cast_neg, Int.cast_one]
    have hθ : (2 * ↑π * I * -1 * ↑x / ↑(b - a) : ℂ) = (-↑θ) * I := by
      push_cast [θ]
      ring
    rw [hθ, exp_mul_I, Complex.cos_neg, Complex.sin_neg, ofReal_cos, ofReal_sin]
    ring
  rw [h1, h2, real_smul, real_smul]
  ring

private theorem cos_smul_add_sin_smul_eq_fourier (α β : ℂ) (x : ℝ) :
    Real.cos (2 * π * x / (b - a)) • α + Real.sin (2 * π * x / (b - a)) • β =
      ((α - I * β) / 2) * fourier 1 (x : AddCircle (b - a)) +
        ((α + I * β) / 2) * fourier (-1) (x : AddCircle (b - a)) := by
  rw [fourier_one_add_fourier_neg_one_eq, real_smul, real_smul, real_smul, real_smul]
  linear_combination ((Real.sin (2 * π * x / (b - a)) : ℂ) * β) * I_sq

private theorem eq_first_harmonic_iff_fourierCoeffOn_eq_zero (hab : a < b) {g : ℝ → ℂ}
    (hgc : ContinuousOn g (Icc a b)) :
    (∃ α β : ℂ, ∀ x ∈ Icc a b,
      g x = Real.cos (2 * π * x / (b - a)) • α + Real.sin (2 * π * x / (b - a)) • β) ↔
      ∀ n : ℤ, n ≠ 1 → n ≠ -1 → fourierCoeffOn hab g n = 0 := by
  have hcont_f (m : ℤ) : Continuous (fun x : ℝ ↦ fourier m (x : AddCircle (b - a))) :=
    (map_continuous (fourier m)).comp (AddCircle.continuous_mk' _)
  have hint_g : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hgc.integrableOn_Icc
  refine ⟨?_, fun hcoeff ↦ ?_⟩
  · rintro ⟨α, β, hαβ⟩ n hn1 hn_neg1
    set c₁ : ℂ := (α - I * β) / 2
    set c₂ : ℂ := (α + I * β) / 2
    set P : ℝ → ℂ := fun x ↦
      c₁ * fourier 1 (x : AddCircle (b - a)) + c₂ * fourier (-1) (x : AddCircle (b - a))
    have hgeP : g =ᵐ[volume.restrict (Ioc a b)] P := by
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx ↦ ?_
      rw [hαβ x (Ioc_subset_Icc_self hx), cos_smul_add_sin_smul_eq_fourier]
    rw [fourierCoeffOn_congr_ae hab hgeP,
      fourierCoeffOn_add hab ((hcont_f 1).const_mul c₁ |>.intervalIntegrable a b)
        ((hcont_f (-1)).const_mul c₂ |>.intervalIntegrable a b),
      fourierCoeffOn.const_mul, fourierCoeffOn.const_mul,
      fourierCoeffOn_fourier hab 1 n, fourierCoeffOn_fourier hab (-1) n]
    simp [hn1, hn_neg1]
  · set c₁ : ℂ := fourierCoeffOn hab g 1
    set c₂ : ℂ := fourierCoeffOn hab g (-1)
    set P : ℝ → ℂ := fun x ↦
      c₁ * fourier 1 (x : AddCircle (b - a)) + c₂ * fourier (-1) (x : AddCircle (b - a))
    have hPc : Continuous P :=
      ((hcont_f 1).const_mul c₁).add ((hcont_f (-1)).const_mul c₂)
    have hdiff_zero : ∀ x ∈ Icc a b, g x - P x = 0 := by
      refine eq_zero_of_forall_fourierCoeffOn_eq_zero hab (hgc.sub hPc.continuousOn) fun n ↦ ?_
      rw [fourierCoeffOn_sub hab hint_g (hPc.intervalIntegrable a b),
        fourierCoeffOn_add hab ((hcont_f 1).const_mul c₁ |>.intervalIntegrable a b)
          ((hcont_f (-1)).const_mul c₂ |>.intervalIntegrable a b),
        fourierCoeffOn.const_mul, fourierCoeffOn.const_mul,
        fourierCoeffOn_fourier hab 1 n, fourierCoeffOn_fourier hab (-1) n]
      by_cases hn1 : n = 1
      · subst hn1; simp [c₁]
      · by_cases hn_neg1 : n = -1
        · subst hn_neg1; simp [c₂]
        · simp [hn1, hn_neg1, hcoeff n hn1 hn_neg1]
    refine ⟨c₁ + c₂, (c₁ - c₂) * I, fun x hx ↦ ?_⟩
    rw [sub_eq_zero.mp (hdiff_zero x hx)]
    dsimp only [P]
    exact fourier_one_add_fourier_neg_one_eq c₁ c₂ x

private theorem absolutelyContinuousOnInterval_const {E : Type*} [PseudoMetricSpace E]
    (c : E) (a b : ℝ) : AbsolutelyContinuousOnInterval (fun _ ↦ c) a b := by
  simpa [AbsolutelyContinuousOnInterval] using tendsto_const_nhds

/-- Wirtinger's inequality for complex-valued absolutely continuous functions. -/
private theorem integral_norm_sub_average_sq_le_complex_of_absolutelyContinuousOnInterval
    (hab : a < b) {f : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f a b) (hfab : f a = f b)
    (hf' : MemLp (deriv f) 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by
  set m := ⨍ y in a..b, f y
  set g : ℝ → ℂ := fun x ↦ f x - m
  have hba : 0 < b - a := sub_pos.2 hab
  have hfc : ContinuousOn f [[a, b]] := hf.continuousOn
  have hg : AbsolutelyContinuousOnInterval g a b :=
    hf.sub (absolutelyContinuousOnInterval_const m a b)
  have hgc : ContinuousOn g (Icc a b) := by
    rw [← uIcc_of_le hab.le]
    exact hg.continuousOn
  have hgL2 : MemLp g 2 (volume.restrict (Ioc a b)) := memLp_two_of_continuousOn_Icc hgc
  have hderiv_g : deriv g = deriv f := funext fun x ↦ deriv_sub_const m
  have hcoeff (n : ℤ) : ‖fourierCoeffOn hab g n‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab (deriv f) n‖ ^ 2 := by
    rcases eq_or_ne n 0 with rfl | hn
    · have hzero : fourierCoeffOn hab g 0 = 0 := by
        have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable
        have hba' : (b : ℂ) - a ≠ 0 := by exact_mod_cast hba.ne'
        simp [fourierCoeffOn_eq_integral, g, m, interval_average_eq,
          intervalIntegral.integral_sub hfi intervalIntegrable_const, hba']
      simpa [hzero] using (by positivity :
        0 ≤ ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab (deriv f) 0‖ ^ 2)
    · have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have hnorm : ‖fourierCoeffOn hab g n‖ =
          (b - a) / (2 * π) / |(n : ℝ)| * ‖fourierCoeffOn hab (deriv f) n‖ := by
        rw [fourierCoeffOn_of_absolutelyContinuousOnInterval hab hn hg, hderiv_g]
        simp [g, hfab, ← ofReal_sub, abs_of_pos hba, abs_of_pos Real.pi_pos]
        field_simp
      rw [hnorm, mul_pow]
      gcongr ?_ ^ 2 * _
      exact div_le_self (by positivity) hn'
  have hsum := hasSum_le hcoeff (hasSum_sq_fourierCoeffOn hab hgL2)
    ((hasSum_sq_fourierCoeffOn hab hf').mul_left (((b - a) / (2 * π)) ^ 2))
  rw [smul_eq_mul, smul_eq_mul, mul_left_comm] at hsum
  exact le_of_mul_le_mul_left hsum (inv_pos.2 hba)

/-- Equality characterization in Wirtinger's inequality for complex-valued absolutely continuous
functions. -/
private theorem integral_norm_sub_average_sq_eq_iff_complex (hab : a < b)
    {f : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f a b) (hfab : f a = f b)
    (hf' : MemLp (deriv f) 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 =
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 ↔
      ∃ α β : ℂ, ∀ x ∈ Icc a b,
        f x - ⨍ y in a..b, f y =
          Real.cos (2 * π * x / (b - a)) • α + Real.sin (2 * π * x / (b - a)) • β := by
  set m := ⨍ y in a..b, f y
  set g : ℝ → ℂ := fun x ↦ f x - m
  have hba : 0 < b - a := sub_pos.2 hab
  have hfc : ContinuousOn f [[a, b]] := hf.continuousOn
  have hg : AbsolutelyContinuousOnInterval g a b :=
    hf.sub (absolutelyContinuousOnInterval_const m a b)
  have hgc : ContinuousOn g (Icc a b) := by
    rw [← uIcc_of_le hab.le]
    exact hg.continuousOn
  have hgL2 : MemLp g 2 (volume.restrict (Ioc a b)) := memLp_two_of_continuousOn_Icc hgc
  have hderiv_g : deriv g = deriv f := funext fun x ↦ deriv_sub_const m
  have hzero_g : fourierCoeffOn hab g 0 = 0 := by
    have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable
    have hba' : (b : ℂ) - a ≠ 0 := by exact_mod_cast hba.ne'
    simp [fourierCoeffOn_eq_integral, g, m, interval_average_eq,
      intervalIntegral.integral_sub hfi intervalIntegrable_const, hba']
  have hzero_df : fourierCoeffOn hab (deriv f) 0 = 0 := by
    simp [fourierCoeffOn_eq_integral, integral_deriv_eq_sub_of_finiteDimensional hf, hfab]
  have hrel (n : ℤ) :
      ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab (deriv f) n‖ ^ 2 =
        (n : ℝ) ^ 2 * ‖fourierCoeffOn hab g n‖ ^ 2 := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hzero_g, hzero_df]
    · have hnorm : ‖fourierCoeffOn hab g n‖ =
          (b - a) / (2 * π) / |(n : ℝ)| * ‖fourierCoeffOn hab (deriv f) n‖ := by
        rw [fourierCoeffOn_of_absolutelyContinuousOnInterval hab hn hg, hderiv_g]
        simp [g, hfab, ← ofReal_sub, abs_of_pos hba, abs_of_pos Real.pi_pos]
        field_simp
      have hn0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
      have hsq : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs (n : ℝ)
      rw [hnorm, mul_pow, div_pow, div_pow, hsq]
      field_simp
  have hnonneg (n : ℤ) :
      0 ≤ ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab (deriv f) n‖ ^ 2 -
        ‖fourierCoeffOn hab g n‖ ^ 2 := by
    rw [hrel n]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hzero_g]
    · have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [← sq_abs]
        nlinarith
      nlinarith [sq_nonneg ‖fourierCoeffOn hab g n‖]
  have hterm_zero (n : ℤ) :
      ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab (deriv f) n‖ ^ 2 -
        ‖fourierCoeffOn hab g n‖ ^ 2 = 0 ↔
        (n ≠ 1 → n ≠ -1 → fourierCoeffOn hab g n = 0) := by
    rw [hrel n, ← sub_one_mul]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [hzero_g]
    · by_cases hn1 : n = 1
      · subst hn1; simp
      · by_cases hn_neg1 : n = -1
        · subst hn_neg1; simp
        · have hsq_ne : (n : ℝ) ^ 2 - 1 ≠ 0 := by
            intro hsq
            have habs : |(n : ℝ)| = 1 := by
              have : (n : ℝ) ^ 2 = 1 ^ 2 := by linarith
              simpa using (sq_eq_sq_iff_abs_eq_abs (n : ℝ) 1).mp this
            have h_int : |n| = 1 := by exact_mod_cast habs
            rcases abs_eq (by omega : (0 : ℤ) ≤ 1) |>.mp h_int with rfl | rfl
            · exact hn1 rfl
            · exact hn_neg1 rfl
          simp [hn1, hn_neg1, hsq_ne]
  have hsum_diff := ((hasSum_sq_fourierCoeffOn hab hf').mul_left (((b - a) / (2 * π)) ^ 2)).sub
    (hasSum_sq_fourierCoeffOn hab hgL2)
  rw [smul_eq_mul, smul_eq_mul, mul_left_comm] at hsum_diff
  rw [eq_first_harmonic_iff_fourierCoeffOn_eq_zero hab hgc]
  have hsum_zero_iff :
      (∫ x in a..b, ‖g x‖ ^ 2 = ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2) ↔
        (b - a)⁻¹ * (((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2) -
          (b - a)⁻¹ * ∫ x in a..b, ‖g x‖ ^ 2 = 0 := by
    rw [← mul_sub, mul_eq_zero, or_iff_right (inv_ne_zero hba.ne'), sub_eq_zero, eq_comm]
  rw [hsum_zero_iff]
  refine ⟨fun h0 n ↦ (hterm_zero n).mp ?_, fun hall ↦ ?_⟩
  · rw [h0] at hsum_diff
    exact congrFun ((hasSum_zero_iff_of_nonneg hnonneg).mp hsum_diff) n
  · refine hsum_diff.unique ?_
    convert hasSum_zero with n
    exact (hterm_zero n).mpr (hall n)

end FirstHarmonicComplex

/-! ### Wirtinger's inequality and equality characterization in finite-dimensional spaces -/

/-- **Wirtinger's inequality for absolutely continuous functions.** An absolutely continuous
function on `[a, b]` with `f a = f b`, valued in a finite-dimensional real inner product space and
with square-integrable derivative, deviates from its mean in `L²` by at most `(b - a) / (2π)` times
the `L²` norm of its derivative. -/
theorem integral_norm_sub_average_sq_le_of_absolutelyContinuousOnInterval {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (hab : a < b)
    {f : ℝ → V} (hf : AbsolutelyContinuousOnInterval f a b) (hfab : f a = f b)
    (hf' : MemLp (deriv f) 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by
  set e := stdOrthonormalBasis ℝ V
  let L (i : Fin (Module.finrank ℝ V)) : V →L[ℝ] ℂ := ofRealCLM.comp (innerSL ℝ (e i))
  have hL (i) (v : V) : ‖L i v‖ ^ 2 = ⟪e i, v⟫ ^ 2 := by simp [L]
  have hfc : ContinuousOn f [[a, b]] := hf.continuousOn
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable
  have hm (i) : ⨍ y in a..b, L i (f y) = L i (⨍ y in a..b, f y) := by
    rw [interval_average_eq, interval_average_eq, (L i).map_smul,
      (L i).intervalIntegral_comp_comm hfi]
  have hderiv_ae (i) :
      deriv (fun x ↦ L i (f x)) =ᵐ[volume.restrict (Ioc a b)] fun x ↦ L i (deriv f x) := by
    filter_upwards [ae_restrict_of_ae (ae_differentiableAt_of_finiteDimensional hf),
      self_mem_ae_restrict measurableSet_Ioc] with x hx hxIoc
    have hxd := hx (uIcc_of_le hab.le ▸ Ioc_subset_Icc_self hxIoc)
    exact ((L i).hasFDerivAt.comp_hasDerivAt x hxd.hasDerivAt).deriv
  have hcoord (i) : ∫ x in a..b, ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪e i, deriv f x⟫ ^ 2 := by
    have hf_i : AbsolutelyContinuousOnInterval (fun x ↦ L i (f x)) a b :=
      (L i).lipschitzWith.comp_absolutelyContinuousOnInterval hf
    have hf_i' : MemLp (deriv (fun x ↦ L i (f x))) 2 (volume.restrict (Ioc a b)) :=
      ((L i).comp_memLp' hf').ae_eq (hderiv_ae i).symm
    have h := integral_norm_sub_average_sq_le_complex_of_absolutelyContinuousOnInterval hab
      hf_i (by rw [hfab]) hf_i'
    have hint_eq : ∫ x in a..b, ‖deriv (fun x ↦ L i (f x)) x‖ ^ 2 =
        ∫ x in a..b, ⟪e i, deriv f x⟫ ^ 2 := by
      refine intervalIntegral.integral_congr_ae_restrict ?_
      rw [uIoc_of_le hab.le]
      filter_upwards [hderiv_ae i] with x hx
      rw [hx, hL i]
    simp_rw [hm i, ← (L i).map_sub, hL i, hint_eq] at h
    exact h
  have hint₁ (i) : IntervalIntegrable (fun x ↦ ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2) volume a b :=
    ((continuousOn_const.inner (hfc.sub continuousOn_const)).pow 2).intervalIntegrable
  have hint₂ (i) : IntervalIntegrable (fun x ↦ ⟪e i, deriv f x⟫ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      ((innerSL ℝ (e i)).comp_memLp' hf').integrable_sq
  calc ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2
      = ∑ i, ∫ x in a..b, ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2 := by
        simp_rw [← e.sum_sq_inner_right]
        exact intervalIntegral.integral_finsetSum fun i _ ↦ hint₁ i
    _ ≤ ∑ i, ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪e i, deriv f x⟫ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by
        rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum fun i _ ↦ hint₂ i]
        simp_rw [e.sum_sq_inner_right]

/-- **Equality in Wirtinger's inequality.** For an absolutely continuous function `f : ℝ → V` on
`[a, b]` with `f a = f b` and square-integrable derivative, equality holds in Wirtinger's
inequality if and only if `f - ⨍ y in a..b, f y` is a first harmonic
`x ↦ cos (2π x / (b - a)) • u + sin (2π x / (b - a)) • v` on `[a, b]`. -/
theorem integral_norm_sub_average_sq_eq_iff {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (hab : a < b) {f : ℝ → V}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfab : f a = f b)
    (hf' : MemLp (deriv f) 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 =
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 ↔
      ∃ u v : V, ∀ x ∈ Icc a b,
        f x - ⨍ y in a..b, f y =
          Real.cos (2 * π * x / (b - a)) • u + Real.sin (2 * π * x / (b - a)) • v := by
  set e := stdOrthonormalBasis ℝ V
  let L (i : Fin (Module.finrank ℝ V)) : V →L[ℝ] ℂ := ofRealCLM.comp (innerSL ℝ (e i))
  have hL (i) (v : V) : ‖L i v‖ ^ 2 = ⟪e i, v⟫ ^ 2 := by simp [L]
  have hfc : ContinuousOn f [[a, b]] := hf.continuousOn
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable
  have hm (i) : ⨍ y in a..b, L i (f y) = L i (⨍ y in a..b, f y) := by
    rw [interval_average_eq, interval_average_eq, (L i).map_smul,
      (L i).intervalIntegral_comp_comm hfi]
  have hderiv_ae (i) :
      deriv (fun x ↦ L i (f x)) =ᵐ[volume.restrict (Ioc a b)] fun x ↦ L i (deriv f x) := by
    filter_upwards [ae_restrict_of_ae (ae_differentiableAt_of_finiteDimensional hf),
      self_mem_ae_restrict measurableSet_Ioc] with x hx hxIoc
    have hxd := hx (uIcc_of_le hab.le ▸ Ioc_subset_Icc_self hxIoc)
    exact ((L i).hasFDerivAt.comp_hasDerivAt x hxd.hasDerivAt).deriv
  have hf_i (i) : AbsolutelyContinuousOnInterval (fun x ↦ L i (f x)) a b :=
    (L i).lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have hf_i' (i) : MemLp (deriv (fun x ↦ L i (f x))) 2 (volume.restrict (Ioc a b)) :=
    ((L i).comp_memLp' hf').ae_eq (hderiv_ae i).symm
  have hint_eq (i) : ∫ x in a..b, ‖deriv (fun x ↦ L i (f x)) x‖ ^ 2 =
      ∫ x in a..b, ⟪e i, deriv f x⟫ ^ 2 := by
    refine intervalIntegral.integral_congr_ae_restrict ?_
    rw [uIoc_of_le hab.le]
    filter_upwards [hderiv_ae i] with x hx
    rw [hx, hL i]
  have hcoord_le (i) : ∫ x in a..b, ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪e i, deriv f x⟫ ^ 2 := by
    have h := integral_norm_sub_average_sq_le_complex_of_absolutelyContinuousOnInterval hab
      (hf_i i) (by rw [hfab]) (hf_i' i)
    simp_rw [hm i, ← (L i).map_sub, hL i, hint_eq i] at h
    exact h
  have hcoord_eq_iff (i) :
      ∫ x in a..b, ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2 =
        ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪e i, deriv f x⟫ ^ 2 ↔
        ∃ α β : ℂ, ∀ x ∈ Icc a b,
          L i (f x - ⨍ y in a..b, f y) =
            Real.cos (2 * π * x / (b - a)) • α + Real.sin (2 * π * x / (b - a)) • β := by
    have h := integral_norm_sub_average_sq_eq_iff_complex hab
      (hf_i i) (by rw [hfab]) (hf_i' i)
    simp_rw [hm i, ← (L i).map_sub, hL i, hint_eq i] at h
    exact h
  have hint₁ (i) : IntervalIntegrable (fun x ↦ ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2) volume a b :=
    ((continuousOn_const.inner (hfc.sub continuousOn_const)).pow 2).intervalIntegrable
  have hint₂ (i) : IntervalIntegrable (fun x ↦ ⟪e i, deriv f x⟫ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      ((innerSL ℝ (e i)).comp_memLp' hf').integrable_sq
  have hsum_lhs : ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 =
      ∑ i, ∫ x in a..b, ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2 := by
    simp_rw [← e.sum_sq_inner_right]
    exact intervalIntegral.integral_finsetSum fun i _ ↦ hint₁ i
  have hsum_rhs : ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 =
      ∑ i, ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪e i, deriv f x⟫ ^ 2 := by
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum fun i _ ↦ hint₂ i]
    simp_rw [e.sum_sq_inner_right]
  rw [hsum_lhs, hsum_rhs, Finset.sum_eq_sum_iff_of_le fun i _ ↦ hcoord_le i]
  simp_rw [Finset.mem_univ, forall_true_left, hcoord_eq_iff]
  refine ⟨fun hall ↦ ?_, ?_⟩
  · choose α β hαβ using hall
    refine ⟨∑ i, (α i).re • e i, ∑ i, (β i).re • e i, fun x hx ↦ ?_⟩
    rw [← e.sum_repr' (f x - ⨍ y in a..b, f y), Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hre := congrArg Complex.re (hαβ i x hx)
    simp only [L, ContinuousLinearMap.comp_apply, ofRealCLM_apply,
      innerSL_apply_apply, ofReal_re, add_re, real_smul, mul_re, ofReal_im, zero_mul,
      sub_zero] at hre
    rw [hre, add_smul, smul_smul, smul_smul]
  · rintro ⟨u, v, huv⟩ i
    refine ⟨L i u, L i v, fun x hx ↦ ?_⟩
    rw [huv x hx, map_add, (L i).map_smul, (L i).map_smul]

/-- **Mean-zero Wirtinger inequality** for absolutely continuous functions on `[a, b]`. -/
theorem integral_norm_sq_le_of_absolutelyContinuousOnInterval_of_integral_eq_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (hab : a < b)
    {f : ℝ → V} (hf : AbsolutelyContinuousOnInterval f a b) (hfab : f a = f b)
    (hmean : ∫ x in a..b, f x = 0)
    (hf' : MemLp (deriv f) 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x‖ ^ 2 ≤ ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by
  have havg : ⨍ y in a..b, f y = 0 := by rw [interval_average_eq, hmean, smul_zero]
  simpa [havg] using integral_norm_sub_average_sq_le_of_absolutelyContinuousOnInterval hab hf hfab
    hf'

/-- **Equality in the mean-zero Wirtinger inequality** on `[a, b]`. -/
theorem integral_norm_sq_eq_iff_of_integral_eq_zero {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (hab : a < b) {f : ℝ → V}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfab : f a = f b)
    (hmean : ∫ x in a..b, f x = 0)
    (hf' : MemLp (deriv f) 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x‖ ^ 2 = ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 ↔
      ∃ u v : V, ∀ x ∈ Icc a b,
        f x = Real.cos (2 * π * x / (b - a)) • u + Real.sin (2 * π * x / (b - a)) • v := by
  have havg : ⨍ y in a..b, f y = 0 := by rw [interval_average_eq, hmean, smul_zero]
  simpa [havg] using integral_norm_sub_average_sq_eq_iff hab hf hfab hf'

private theorem memLp_deriv_two_of_intervalIntegrable_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (hab : a < b) {f : ℝ → V}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (henergy : IntervalIntegrable (fun x ↦ ‖deriv f x‖ ^ 2) volume a b) :
    MemLp (deriv f) 2 (volume.restrict (Ioc a b)) :=
  (memLp_two_iff_integrable_sq_norm
    (intervalIntegrable_deriv_of_finiteDimensional hf).1.aestronglyMeasurable).2
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 henergy)

/-- **Sharp periodic Wirtinger inequality on `[0, T]`** for functions into a finite-dimensional
real inner product space. -/
theorem periodic_wirtinger_norm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {f : ℝ → V} {T : ℝ} (hT : 0 < T)
    (hf : AbsolutelyContinuousOnInterval f 0 T) (hperiod : f 0 = f T)
    (hmean : (∫ t in (0 : ℝ)..T, f t) = 0)
    (henergy : IntervalIntegrable (fun t ↦ ‖deriv f t‖ ^ 2) volume 0 T) :
    (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) ≤
      (T / (2 * Real.pi)) ^ 2 * ∫ t in (0 : ℝ)..T, ‖deriv f t‖ ^ 2 := by
  simpa [sub_zero] using
    integral_norm_sq_le_of_absolutelyContinuousOnInterval_of_integral_eq_zero hT hf hperiod hmean
      (memLp_deriv_two_of_intervalIntegrable_norm_sq hT hf henergy)

/-- **First-harmonic equality characterization on `[0, T]`** for functions into a
finite-dimensional real inner product space. -/
theorem periodic_wirtinger_norm_eq_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {f : ℝ → V} {T : ℝ} (hT : 0 < T)
    (hf : AbsolutelyContinuousOnInterval f 0 T) (hperiod : f 0 = f T)
    (hmean : (∫ t in (0 : ℝ)..T, f t) = 0)
    (henergy : IntervalIntegrable (fun t ↦ ‖deriv f t‖ ^ 2) volume 0 T) :
    (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) =
      (T / (2 * Real.pi)) ^ 2 * ∫ t in (0 : ℝ)..T, ‖deriv f t‖ ^ 2 ↔
      ∃ u v : V, ∀ t ∈ Icc 0 T,
        f t = Real.cos (2 * Real.pi * t / T) • u + Real.sin (2 * Real.pi * t / T) • v := by
  simpa [sub_zero] using
    integral_norm_sq_eq_iff_of_integral_eq_zero hT hf hperiod hmean
      (memLp_deriv_two_of_intervalIntegrable_norm_sq hT hf henergy)

/-- **Sharp periodic Wirtinger inequality on `[0, T]`** for real-valued absolutely continuous
functions. -/
theorem periodic_wirtinger {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : AbsolutelyContinuousOnInterval f 0 T) (hperiod : f 0 = f T)
    (hmean : (∫ t in (0 : ℝ)..T, f t) = 0)
    (henergy : IntervalIntegrable (fun t ↦ (deriv f t) ^ 2) volume 0 T) :
    (∫ t in (0 : ℝ)..T, (f t) ^ 2) ≤
      (T / (2 * Real.pi)) ^ 2 * ∫ t in (0 : ℝ)..T, (deriv f t) ^ 2 := by
  have henergy' : IntervalIntegrable (fun t ↦ ‖deriv f t‖ ^ 2) volume 0 T := by
    simpa [Real.norm_eq_abs, sq_abs] using henergy
  simpa [Real.norm_eq_abs, sq_abs] using periodic_wirtinger_norm hT hf hperiod hmean henergy'

/-- **First-harmonic equality characterization on `[0, T]`** for real-valued absolutely continuous
functions: equality holds in `TauCeti.periodic_wirtinger` if and only if
`f t = a * cos (2π t / T) + b * sin (2π t / T)` on `[0, T]`. -/
theorem periodic_wirtinger_eq_iff {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : AbsolutelyContinuousOnInterval f 0 T) (hperiod : f 0 = f T)
    (hmean : (∫ t in (0 : ℝ)..T, f t) = 0)
    (henergy : IntervalIntegrable (fun t ↦ (deriv f t) ^ 2) volume 0 T) :
    (∫ t in (0 : ℝ)..T, (f t) ^ 2) =
      (T / (2 * Real.pi)) ^ 2 * ∫ t in (0 : ℝ)..T, (deriv f t) ^ 2 ↔
      ∃ a b : ℝ, ∀ t ∈ Icc 0 T,
        f t = a * Real.cos (2 * Real.pi * t / T) + b * Real.sin (2 * Real.pi * t / T) := by
  have henergy' : IntervalIntegrable (fun t ↦ ‖deriv f t‖ ^ 2) volume 0 T := by
    simpa [Real.norm_eq_abs, sq_abs] using henergy
  have h := periodic_wirtinger_norm_eq_iff hT hf hperiod hmean henergy'
  simp only [Real.norm_eq_abs, sq_abs, smul_eq_mul] at h
  rw [h]
  refine ⟨fun ⟨u, v, huv⟩ ↦ ⟨u, v, fun t ht ↦ by linarith [huv t ht]⟩,
    fun ⟨u, v, huv⟩ ↦ ⟨u, v, fun t ht ↦ by linarith [huv t ht]⟩⟩

/-! ### Wirtinger's inequality for everywhere-differentiable functions -/

/-- Wirtinger's inequality for complex-valued functions; the vector-valued
`TauCeti.integral_norm_sub_average_sq_le` reduces to it coordinatewise. -/
private theorem integral_norm_sub_average_sq_le_complex (hab : a < b) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  set m := ⨍ y in a..b, f y
  set g : ℝ → ℂ := fun x => f x - m
  have hba : 0 < b - a := sub_pos.2 hab
  have hfc : ContinuousOn f [[a, b]] := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hg : ∀ x ∈ [[a, b]], HasDerivAt g (f' x) x := fun x hx => (hf x hx).sub_const m
  -- `g` is continuous on the compact interval, hence bounded, hence square integrable.
  have hgL2 : MemLp g 2 (volume.restrict (Ioc a b)) := by
    have hgc : ContinuousOn g (Icc a b) := by
      rw [← uIcc_of_le hab.le]
      exact hfc.sub continuousOn_const
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
    exact MemLp.of_bound ((hgc.aestronglyMeasurable measurableSet_Icc).mono_set
      Ioc_subset_Icc_self) C
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Ioc_subset_Icc_self hx))
  have hf'int : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hf'.integrable one_le_two)
  -- Coefficientwise comparison of the Fourier coefficients of `g = f - m` and `f'`.
  have hcoeff (n : ℤ) : ‖fourierCoeffOn hab g n‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab f' n‖ ^ 2 := by
    rcases eq_or_ne n 0 with rfl | hn
    · -- The zeroth coefficient of `g` is its mean, which vanishes.
      have hzero : fourierCoeffOn hab g 0 = 0 := by
        have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable
        have hba' : (b : ℂ) - a ≠ 0 := by exact_mod_cast hba.ne'
        simp [fourierCoeffOn_eq_integral, g, m, interval_average_eq,
          intervalIntegral.integral_sub hfi intervalIntegrable_const, hba']
      simpa [hzero] using (by positivity :
        0 ≤ ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab f' 0‖ ^ 2)
    · -- Integration by parts: the coefficient of `g` is that of `f'` over `-2πin / (b - a)`.
      have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have hnorm : ‖fourierCoeffOn hab g n‖ =
          (b - a) / (2 * π) / |(n : ℝ)| * ‖fourierCoeffOn hab f' n‖ := by
        rw [fourierCoeffOn_of_hasDerivAt hab hn hg hf'int]
        simp [g, hfab, ← ofReal_sub, abs_of_pos hba, abs_of_pos Real.pi_pos]
        field_simp
      rw [hnorm, mul_pow]
      gcongr ?_ ^ 2 * _
      exact div_le_self (by positivity) hn'
  have hsum := hasSum_le hcoeff (hasSum_sq_fourierCoeffOn hab hgL2)
    ((hasSum_sq_fourierCoeffOn hab hf').mul_left (((b - a) / (2 * π)) ^ 2))
  rw [smul_eq_mul, smul_eq_mul, mul_left_comm] at hsum
  exact le_of_mul_le_mul_left hsum (inv_pos.2 hba)

/-- **Wirtinger's inequality.** A function on `[a, b]` with `f a = f b`, valued in a
finite-dimensional real inner product space and with square-integrable derivative, deviates from
its mean in `L²` by at most `(b - a) / (2π)` times the `L²` norm of its derivative. -/
theorem integral_norm_sub_average_sq_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (hab : a < b) {f f' : ℝ → V}
    (hf : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  set e := stdOrthonormalBasis ℝ V
  -- The `i`-th coordinate, read as a complex number.
  let L (i : Fin (Module.finrank ℝ V)) : V →L[ℝ] ℂ := ofRealCLM.comp (innerSL ℝ (e i))
  have hL (i) (v : V) : ‖L i v‖ ^ 2 = ⟪e i, v⟫ ^ 2 := by simp [L]
  have hfc : ContinuousOn f [[a, b]] := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable
  have hm (i) : ⨍ y in a..b, L i (f y) = L i (⨍ y in a..b, f y) := by
    rw [interval_average_eq, interval_average_eq, (L i).map_smul,
      (L i).intervalIntegral_comp_comm hfi]
  have hcoord (i) : ∫ x in a..b, ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪e i, f' x⟫ ^ 2 := by
    have h := integral_norm_sub_average_sq_le_complex hab
      (f := fun x => L i (f x)) (f' := fun x => L i (f' x))
      (fun x hx => (L i).hasFDerivAt.comp_hasDerivAt x (hf x hx)) (by rw [hfab])
      ((L i).comp_memLp' hf')
    simp_rw [hm i, ← (L i).map_sub, hL i] at h
    exact h
  have hint₁ (i) : IntervalIntegrable (fun x => ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2) volume a b :=
    ((continuousOn_const.inner (hfc.sub continuousOn_const)).pow 2).intervalIntegrable
  have hint₂ (i) : IntervalIntegrable (fun x => ⟪e i, f' x⟫ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      ((innerSL ℝ (e i)).comp_memLp' hf').integrable_sq
  calc ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2
      = ∑ i, ∫ x in a..b, ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2 := by
        simp_rw [← e.sum_sq_inner_right]
        exact intervalIntegral.integral_finsetSum fun i _ => hint₁ i
    _ ≤ ∑ i, ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪e i, f' x⟫ ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
        rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum fun i _ => hint₂ i]
        simp_rw [e.sum_sq_inner_right]

end TauCeti

namespace ContinuousLinearMap

variable {a b : ℝ}

/-- Along an absolutely continuous loop `f` on `[a, b]` with square-integrable derivative, the
integral of a continuous bilinear form `B (f x) (deriv f x)` is bounded by `‖B‖ (b - a) / (2π)`
times the `L²` energy of the loop. -/
theorem norm_integral_apply_apply_le_of_absolutelyContinuousOnInterval {V G : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (B : V →L[ℝ] V →L[ℝ] G) (hab : a < b) {f : ℝ → V}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfab : f a = f b)
    (hf' : MemLp (deriv f) 2 (volume.restrict (Ioc a b))) :
    ‖∫ x in a..b, B (f x) (deriv f x)‖ ≤
      ‖B‖ * ((b - a) / (2 * π)) * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by
  set m := ⨍ y in a..b, f y
  set c := (b - a) / (2 * π)
  have hc : 0 < c := div_pos (sub_pos.2 hab) (by positivity)
  have hfc : ContinuousOn f [[a, b]] := hf.continuousOn
  have hf'int : IntegrableOn (deriv f) (Ioc a b) := hf'.integrable one_le_two
  have hf'ii : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hf'int
  have hsq : IntervalIntegrable (fun x ↦ ‖deriv f x‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      ((memLp_two_iff_integrable_sq_norm hf'.aestronglyMeasurable).1 hf')
  have hdev : IntervalIntegrable (fun x ↦ ‖f x - m‖ ^ 2) volume a b :=
    ((hfc.sub continuousOn_const).norm.pow 2).intervalIntegrable
  have hmean : ∫ x in a..b, B m (deriv f x) = 0 := by
    rw [(B m).intervalIntegral_comp_comm hf'ii,
      TauCeti.integral_deriv_eq_sub_of_finiteDimensional hf, hfab, sub_self, map_zero]
  have hpt (x : ℝ) : ‖B (f x - m) (deriv f x)‖ ≤
      ‖B‖ * ((c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖deriv f x‖ ^ 2) / 2) := by
    refine (B.le_opNorm₂ _ _).trans ?_
    rw [mul_assoc]
    gcongr
    have hsplit :
        (c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖deriv f x‖ ^ 2) / 2 - ‖f x - m‖ * ‖deriv f x‖ =
          c⁻¹ * (‖f x - m‖ - c * ‖deriv f x‖) ^ 2 / 2 := by
      field_simp
      ring
    have : 0 ≤ c⁻¹ * (‖f x - m‖ - c * ‖deriv f x‖) ^ 2 / 2 := by positivity
    linarith
  have hbound : IntervalIntegrable
      (fun x ↦ ‖B‖ * ((c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖deriv f x‖ ^ 2) / 2)) volume a b :=
    (((hdev.const_mul c⁻¹).add (hsq.const_mul c)).div_const 2).const_mul ‖B‖
  have hint : IntervalIntegrable (fun x ↦ B (f x - m) (deriv f x)) volume a b :=
    hbound.mono_fun' (B.aestronglyMeasurable_comp₂
      (((hfc.sub continuousOn_const).mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc) hf'ii.def'.aestronglyMeasurable) (Filter.Eventually.of_forall hpt)
  have hrewrite :
      ∫ x in a..b, B (f x) (deriv f x) = ∫ x in a..b, B (f x - m) (deriv f x) := by
    have hBm : IntervalIntegrable (fun x ↦ B m (deriv f x)) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 ((B m).integrable_comp hf'int)
    rw [← add_zero (∫ x in a..b, B (f x - m) (deriv f x)), ← hmean,
      ← intervalIntegral.integral_add hint hBm]
    simp [map_sub]
  rw [hrewrite]
  refine (norm_integral_le_of_norm_le hab.le (Filter.Eventually.of_forall fun x _ ↦ hpt x)
    hbound).trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_add (hdev.const_mul c⁻¹) (hsq.const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have key : (c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) ≤ c * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by
    calc (c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2)
        ≤ c⁻¹ * (c ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2) := by
          gcongr
          exact TauCeti.integral_norm_sub_average_sq_le_of_absolutelyContinuousOnInterval hab hf
            hfab hf'
      _ = c * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by field_simp
  calc ‖B‖ * (((c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) + c * ∫ x in a..b, ‖deriv f x‖ ^ 2) / 2)
      ≤ ‖B‖ * (((c * ∫ x in a..b, ‖deriv f x‖ ^ 2) + c * ∫ x in a..b, ‖deriv f x‖ ^ 2) / 2) := by
        gcongr
    _ = ‖B‖ * c * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by ring

/-- Along a loop `f` on `[a, b]` with square-integrable derivative, the integral of a continuous
bilinear form `B (f x) (f' x)` is bounded by `‖B‖ (b - a) / (2π)` times the `L²` energy of the
loop. For a symplectic form `B` the left side is twice the symplectic area enclosed by the loop,
and this is the isoperimetric inequality. -/
theorem norm_integral_apply_apply_le {V G : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (B : V →L[ℝ] V →L[ℝ] G) (hab : a < b) {f f' : ℝ → V}
    (hf : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ‖∫ x in a..b, B (f x) (f' x)‖ ≤
      ‖B‖ * ((b - a) / (2 * π)) * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  set m := ⨍ y in a..b, f y
  set c := (b - a) / (2 * π)
  have hc : 0 < c := div_pos (sub_pos.2 hab) (by positivity)
  have hfc : ContinuousOn f [[a, b]] := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf'int : IntegrableOn f' (Ioc a b) := hf'.integrable one_le_two
  have hf'ii : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hf'int
  have hsq : IntervalIntegrable (fun x => ‖f' x‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      ((memLp_two_iff_integrable_sq_norm hf'.aestronglyMeasurable).1 hf')
  have hdev : IntervalIntegrable (fun x => ‖f x - m‖ ^ 2) volume a b :=
    ((hfc.sub continuousOn_const).norm.pow 2).intervalIntegrable
  -- The mean contributes nothing, since `∫ f' = f b - f a = 0`.
  have hmean : ∫ x in a..b, B m (f' x) = 0 := by
    rw [(B m).intervalIntegral_comp_comm hf'ii,
      integral_eq_sub_of_hasDerivAt hf hf'ii, hfab, sub_self, map_zero]
  -- Pointwise, `‖B (f - m) f'‖ ≤ ‖B‖ (‖f - m‖² / c + c ‖f'‖²) / 2`.
  have hpt (x : ℝ) : ‖B (f x - m) (f' x)‖ ≤
      ‖B‖ * ((c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖f' x‖ ^ 2) / 2) := by
    refine (B.le_opNorm₂ _ _).trans ?_
    rw [mul_assoc]
    gcongr
    have hsplit : (c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖f' x‖ ^ 2) / 2 - ‖f x - m‖ * ‖f' x‖ =
        c⁻¹ * (‖f x - m‖ - c * ‖f' x‖) ^ 2 / 2 := by
      field_simp
      ring
    have : 0 ≤ c⁻¹ * (‖f x - m‖ - c * ‖f' x‖) ^ 2 / 2 := by positivity
    linarith
  have hbound : IntervalIntegrable
      (fun x => ‖B‖ * ((c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖f' x‖ ^ 2) / 2)) volume a b :=
    (((hdev.const_mul c⁻¹).add (hsq.const_mul c)).div_const 2).const_mul ‖B‖
  have hint : IntervalIntegrable (fun x => B (f x - m) (f' x)) volume a b :=
    hbound.mono_fun' (B.aestronglyMeasurable_comp₂
      (((hfc.sub continuousOn_const).mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc) hf'ii.def'.aestronglyMeasurable) (Filter.Eventually.of_forall hpt)
  have hrewrite : ∫ x in a..b, B (f x) (f' x) = ∫ x in a..b, B (f x - m) (f' x) := by
    have hBm : IntervalIntegrable (fun x => B m (f' x)) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 ((B m).integrable_comp hf'int)
    rw [← add_zero (∫ x in a..b, B (f x - m) (f' x)), ← hmean,
      ← intervalIntegral.integral_add hint hBm]
    simp [map_sub]
  rw [hrewrite]
  refine (norm_integral_le_of_norm_le hab.le (Filter.Eventually.of_forall fun x _ => hpt x)
    hbound).trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_add (hdev.const_mul c⁻¹) (hsq.const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- Wirtinger's inequality bounds the deviation term by the energy term.
  have key : (c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) ≤ c * ∫ x in a..b, ‖f' x‖ ^ 2 := by
    calc (c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) ≤ c⁻¹ * (c ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2) := by
          gcongr
          exact TauCeti.integral_norm_sub_average_sq_le hab hf hfab hf'
      _ = c * ∫ x in a..b, ‖f' x‖ ^ 2 := by field_simp
  calc ‖B‖ * (((c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) + c * ∫ x in a..b, ‖f' x‖ ^ 2) / 2)
      ≤ ‖B‖ * (((c * ∫ x in a..b, ‖f' x‖ ^ 2) + c * ∫ x in a..b, ‖f' x‖ ^ 2) / 2) := by
        gcongr
    _ = ‖B‖ * c * ∫ x in a..b, ‖f' x‖ ^ 2 := by ring

end ContinuousLinearMap
