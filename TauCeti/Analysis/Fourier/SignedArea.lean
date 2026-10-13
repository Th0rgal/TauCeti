/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Analysis.Fourier.Wirtinger

/-!
# Signed area of closed absolutely continuous plane curves and circle rigidity

For a closed plane curve `(x, y)` on `[a, a + T]` (`T > 0`), the **signed area** enclosed by the
curve is defined by the real boundary integral

`signedArea x y a T = (1 / 2) * ∫ t in a..(a + T), (x t * deriv y t - y t * deriv x t)`.

When `x` and `y` are absolutely continuous on `[a, a + T]` with `x (a + T) = x a`,
`y (a + T) = y a`, and square-integrable derivatives, integration by parts shows that
`signedArea x y a T = ∫ t in a..(a + T), x t * deriv y t = - ∫ t in a..(a + T), deriv x t * y t`
and that `signedArea` is invariant under translations of `x` and `y`.

Combining the periodic Wirtinger inequality (`TauCeti.Analysis.Fourier.Wirtinger`) with the exact
`L²` deficiency identity for `deriv x ± (2π / T) * (y - ȳ)` and `deriv y ∓ (2π / T) * (x - x̄)`
yields the **sharp area--energy inequality**:

`4 * π * |signedArea x y a T| ≤ T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)`.

Whereas the mean-zero periodic Wirtinger equality permits general first harmonics (ellipses),
equality in the area--energy inequality forces the almost-everywhere Cauchy--Riemann-type system
`deriv x t = ∓ (2π / T) * (y t - ȳ)` and `deriv y t = ± (2π / T) * (x t - x̄)`. Integrating the
rotated coordinates via the fundamental theorem of calculus for absolutely continuous functions
shows that equality holds if and only if `(x, y)` is a constant curve or a translated circle
traversed once at constant angular speed `2π / T` with one of the two orientations.

## Main definitions

* `TauCeti.signedArea`: signed area
  `(1 / 2) * ∫ t in a..(a + T), (x t * deriv y t - y t * deriv x t)` of a parameterized plane
  curve `(x, y)` on `[a, a + T]`.
* `TauCeti.signedAreaProd`, `TauCeti.signedAreaComplex`: bundled plane-curve variants for
  `γ : ℝ → ℝ × ℝ` and `γ : ℝ → ℂ`.

## Main results

* `TauCeti.signedArea_eq_integral_mul_deriv`, `TauCeti.signedArea_eq_neg_integral_deriv_mul`,
  `TauCeti.signedArea_add_const`: integration by parts and translation invariance of signed area.
* `TauCeti.area_energy_deficiency_identity`: exact `L²` deficiency decomposition of
  `T * ∫ (deriv x ^ 2 + deriv y ^ 2) - 4π σ * signedArea x y a T`.
* `TauCeti.four_mul_pi_mul_signedArea_le`, `TauCeti.neg_four_mul_pi_mul_signedArea_le`,
  `TauCeti.four_mul_pi_mul_abs_signedArea_le`: the sharp area--energy inequality.
* `TauCeti.eq_circle_of_ae_deriv_eq`: solution of the linear rotation system
  `deriv x = -ω (y - c₂)`, `deriv y = ω (x - c₁)` a.e. via the fundamental theorem of calculus
  for absolutely continuous functions.
* `TauCeti.four_mul_pi_mul_signedArea_eq_iff_ae_deriv`,
  `TauCeti.four_mul_pi_mul_signedArea_eq_iff`,
  `TauCeti.four_mul_pi_mul_abs_signedArea_eq_iff`: complete equality characterizations by the
  almost-everywhere derivative relation and by constant-speed circles.
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval

namespace TauCeti

variable {a b T : ℝ}

/-! ### Definition and basic properties of signed area -/

/-- The **signed area** enclosed by a plane curve `(x, y)` on `[a, a + T]`, defined by the
boundary line integral `(1 / 2) * ∫ t in a..(a + T), (x t * deriv y t - y t * deriv x t)`. -/
noncomputable def signedArea (x y : ℝ → ℝ) (a T : ℝ) : ℝ :=
  (1 / 2) * ∫ t in a..(a + T), (x t * deriv y t - y t * deriv x t)

/-- Signed area of a plane curve `γ : ℝ → ℝ × ℝ` on `[a, a + T]`. -/
noncomputable def signedAreaProd (γ : ℝ → ℝ × ℝ) (a T : ℝ) : ℝ :=
  signedArea (Prod.fst ∘ γ) (Prod.snd ∘ γ) a T

/-- Signed area of a complex-valued plane curve `γ : ℝ → ℂ` on `[a, a + T]`. -/
noncomputable def signedAreaComplex (γ : ℝ → ℂ) (a T : ℝ) : ℝ :=
  signedArea (Complex.re ∘ γ) (Complex.im ∘ γ) a T

/-- Signed area on a degenerate interval of length `0` vanishes. -/
@[simp]
theorem signedArea_zero_right (x y : ℝ → ℝ) (a : ℝ) : signedArea x y a 0 = 0 := by
  simp [signedArea]

/-- Swapping the coordinates `(x, y)` reverses the orientation and negates `signedArea`. -/
theorem signedArea_swap (x y : ℝ → ℝ) (a T : ℝ) :
    signedArea y x a T = -signedArea x y a T := by
  unfold signedArea
  have h : (fun t ↦ y t * deriv x t - x t * deriv y t) =
      fun t ↦ -(x t * deriv y t - y t * deriv x t) := by ext t; ring
  rw [h, intervalIntegral.integral_neg]
  ring

/-- Negating the first coordinate negates `signedArea`. -/
@[simp]
theorem signedArea_neg_left (x y : ℝ → ℝ) (a T : ℝ) :
    signedArea (fun t ↦ -x t) y a T = -signedArea x y a T := by
  unfold signedArea
  have h : (fun t ↦ -x t * deriv y t - y t * deriv (fun s ↦ -x s) t) =
      fun t ↦ -(x t * deriv y t - y t * deriv x t) := by
    ext t
    rw [show (fun s ↦ -x s) = -x from rfl, deriv.neg]
    ring
  rw [h, intervalIntegral.integral_neg]
  ring

/-- Negating the second coordinate negates `signedArea`. -/
@[simp]
theorem signedArea_neg_right (x y : ℝ → ℝ) (a T : ℝ) :
    signedArea x (fun t ↦ -y t) a T = -signedArea x y a T := by
  rw [signedArea_swap (fun t ↦ -y t) x, signedArea_neg_left, signedArea_swap, neg_neg]

/-- For closed absolutely continuous functions `x, y : ℝ → ℝ` on `[a, a + T]`, integration by parts
gives `∫ t in a..(a + T), x t * deriv y t = - ∫ t in a..(a + T), deriv x t * y t`. -/
theorem intervalIntegral_mul_deriv_eq_neg_of_periodic {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a) :
    ∫ t in a..(a + T), x t * deriv y t = -∫ t in a..(a + T), deriv x t * y t := by
  rw [hx.integral_mul_deriv_eq_deriv_mul hy, hx_per, hy_per, sub_self, zero_sub]

/-- For a closed absolutely continuous plane curve `(x, y)` on `[a, a + T]`,
`signedArea x y a T = ∫ t in a..(a + T), x t * deriv y t`. -/
theorem signedArea_eq_integral_mul_deriv {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a) :
    signedArea x y a T = ∫ t in a..(a + T), x t * deriv y t := by
  unfold signedArea
  have h1 : IntervalIntegrable (fun t ↦ x t * deriv y t) volume a (a + T) :=
    hy.intervalIntegrable_deriv.continuousOn_mul hx.continuousOn
  have h2 : IntervalIntegrable (fun t ↦ y t * deriv x t) volume a (a + T) :=
    hx.intervalIntegrable_deriv.continuousOn_mul hy.continuousOn
  rw [intervalIntegral.integral_sub h1 h2,
    hy.integral_mul_deriv_eq_deriv_mul hx, hx_per, hy_per, sub_self, zero_sub]
  have hcomm : (fun t ↦ deriv y t * x t) = fun t ↦ x t * deriv y t := by ext t; ring
  rw [hcomm]
  ring

/-- For a closed absolutely continuous plane curve `(x, y)` on `[a, a + T]`,
`signedArea x y a T = - ∫ t in a..(a + T), deriv x t * y t`. -/
theorem signedArea_eq_neg_integral_deriv_mul {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a) :
    signedArea x y a T = -∫ t in a..(a + T), deriv x t * y t := by
  rw [signedArea_eq_integral_mul_deriv hx hy hx_per hy_per,
    intervalIntegral_mul_deriv_eq_neg_of_periodic hx hy hx_per hy_per]

private theorem absolutelyContinuousOnInterval_const_real (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) a b := by
  simpa [AbsolutelyContinuousOnInterval] using tendsto_const_nhds

/-- **Translation invariance of signed area**: shifting a closed absolutely continuous curve
`(x, y)` by any constant vector `(c₁, c₂)` leaves `signedArea` unchanged. -/
theorem signedArea_add_const {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a) (c₁ c₂ : ℝ) :
    signedArea (fun t ↦ x t + c₁) (fun t ↦ y t + c₂) a T = signedArea x y a T := by
  have hx' : AbsolutelyContinuousOnInterval (fun t ↦ x t + c₁) a (a + T) :=
    hx.add (absolutelyContinuousOnInterval_const_real c₁ a (a + T))
  have hy' : AbsolutelyContinuousOnInterval (fun t ↦ y t + c₂) a (a + T) :=
    hy.add (absolutelyContinuousOnInterval_const_real c₂ a (a + T))
  rw [signedArea_eq_integral_mul_deriv hx' hy' (by simp [hx_per]) (by simp [hy_per]),
    signedArea_eq_integral_mul_deriv hx hy hx_per hy_per]
  have hd : deriv (fun t ↦ y t + c₂) = deriv y := funext fun _ ↦ deriv_add_const c₂
  have hsplit : (fun t ↦ (x t + c₁) * deriv (fun s ↦ y s + c₂) t) =
      fun t ↦ x t * deriv y t + c₁ * deriv y t := by ext t; rw [hd]; ring
  rw [hsplit, intervalIntegral.integral_add
    (hy.intervalIntegrable_deriv.continuousOn_mul hx.continuousOn)
    (hy.intervalIntegrable_deriv.const_mul c₁),
    intervalIntegral.integral_const_mul, hy.integral_deriv_eq_sub, hy_per, sub_self,
    mul_zero, add_zero]

/-- Subtracting a constant vector `(c₁, c₂)` leaves `signedArea` unchanged. -/
theorem signedArea_sub_const {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a) (c₁ c₂ : ℝ) :
    signedArea (fun t ↦ x t - c₁) (fun t ↦ y t - c₂) a T = signedArea x y a T := by
  simpa [sub_eq_add_neg] using signedArea_add_const hx hy hx_per hy_per (-c₁) (-c₂)

/-- Centering `x` by its interval average `⨍ s in a..(a + T), x s` in the integral representation
of `signedArea`. -/
theorem signedArea_eq_integral_sub_average_mul_deriv {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a) :
    signedArea x y a T =
      ∫ t in a..(a + T), (x t - ⨍ s in a..(a + T), x s) * deriv y t := by
  have hc : AbsolutelyContinuousOnInterval (fun t ↦ x t - ⨍ s in a..(a + T), x s) a (a + T) :=
    hx.sub (absolutelyContinuousOnInterval_const_real _ a (a + T))
  have hshift := signedArea_sub_const hx hy hx_per hy_per (⨍ s in a..(a + T), x s) 0
  simp only [sub_zero] at hshift
  rw [← hshift, signedArea_eq_integral_mul_deriv hc hy (by simp [hx_per]) hy_per]

/-! ### Explicit derivatives, signed area, and energy of constant-speed circles -/

private theorem hasDerivAt_circle_coord (a ω c₁ c₂ r₁ r₂ t : ℝ) :
    HasDerivAt (fun s ↦ c₁ + r₁ * Real.cos (ω * (s - a)) - r₂ * Real.sin (ω * (s - a)))
      (-ω * (r₁ * Real.sin (ω * (t - a)) + r₂ * Real.cos (ω * (t - a)))) t ∧
    HasDerivAt (fun s ↦ c₂ + r₁ * Real.sin (ω * (s - a)) + r₂ * Real.cos (ω * (s - a)))
      (ω * (r₁ * Real.cos (ω * (t - a)) - r₂ * Real.sin (ω * (t - a)))) t := by
  have hθ : HasDerivAt (fun s ↦ ω * (s - a)) ω t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_mul ω
  have hcos : HasDerivAt (fun s ↦ Real.cos (ω * (s - a))) (-Real.sin (ω * (t - a)) * ω) t :=
    hθ.cos
  have hsin : HasDerivAt (fun s ↦ Real.sin (ω * (s - a))) (Real.cos (ω * (t - a)) * ω) t :=
    hθ.sin
  refine ⟨?_, ?_⟩
  · convert ((hasDerivAt_const t c₁).add (hcos.const_mul r₁)).sub (hsin.const_mul r₂) using 1
    ring
  · convert ((hasDerivAt_const t c₂).add (hsin.const_mul r₁)).add (hcos.const_mul r₂) using 1
    ring

private theorem lipschitzWith_circle_coord (a ω c r₁ r₂ : ℝ) :
    LipschitzWith (‖ω‖₊ * (‖r₁‖₊ + ‖r₂‖₊))
      (fun s ↦ c + r₁ * Real.cos (ω * (s - a)) + r₂ * Real.sin (ω * (s - a))) := by
  have hd (t : ℝ) :
      HasDerivAt (fun s ↦ c + r₁ * Real.cos (ω * (s - a)) + r₂ * Real.sin (ω * (s - a)))
        (ω * (r₂ * Real.cos (ω * (t - a)) - r₁ * Real.sin (ω * (t - a)))) t := by
    have h := (hasDerivAt_circle_coord a ω c 0 r₁ (-r₂) t).1
    convert h using 1
    · ext s; ring
    · ring
  refine lipschitzWith_of_nnnorm_deriv_le (fun t ↦ (hd t).differentiableAt) (fun t ↦ ?_)
  rw [← NNReal.coe_le_coe, coe_nnnorm, (hd t).deriv]
  push_cast
  simp only [Real.norm_eq_abs, abs_mul]
  gcongr
  calc |r₂ * Real.cos (ω * (t - a)) - r₁ * Real.sin (ω * (t - a))|
      ≤ |r₂ * Real.cos (ω * (t - a))| + |r₁ * Real.sin (ω * (t - a))| := abs_sub _ _
    _ = |r₂| * |Real.cos (ω * (t - a))| + |r₁| * |Real.sin (ω * (t - a))| := by
        rw [abs_mul, abs_mul]
    _ ≤ |r₂| * 1 + |r₁| * 1 := by
        gcongr
        · exact Real.abs_cos_le_one _
        · exact Real.abs_sin_le_one _
    _ = |r₁| + |r₂| := by ring

private theorem absolutelyContinuousOnInterval_circle_coord (a b ω c r₁ r₂ : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun s ↦ c + r₁ * Real.cos (ω * (s - a)) + r₂ * Real.sin (ω * (s - a))) a b :=
  (lipschitzWith_circle_coord a ω c r₁ r₂).lipschitzOnWith.absolutelyContinuousOnInterval

/-- The signed area of a positively oriented circle
`x t = c₁ + r₁ cos(2π(t - a)/T) - r₂ sin(2π(t - a)/T)`,
`y t = c₂ + r₁ sin(2π(t - a)/T) + r₂ cos(2π(t - a)/T)` on `[a, a + T]` (`T > 0`) is
`π * (r₁ ^ 2 + r₂ ^ 2)`. -/
theorem signedArea_circle_pos (hT : 0 < T) (a c₁ c₂ r₁ r₂ : ℝ) :
    signedArea
      (fun t ↦ c₁ + r₁ * Real.cos (2 * Real.pi * (t - a) / T) -
        r₂ * Real.sin (2 * Real.pi * (t - a) / T))
      (fun t ↦ c₂ + r₁ * Real.sin (2 * Real.pi * (t - a) / T) +
        r₂ * Real.cos (2 * Real.pi * (t - a) / T)) a T =
      Real.pi * (r₁ ^ 2 + r₂ ^ 2) := by
  set ω := 2 * Real.pi / T
  have hω (t : ℝ) : 2 * Real.pi * (t - a) / T = ω * (t - a) := by dsimp [ω]; ring
  simp_rw [hω]
  set x₀ : ℝ → ℝ := fun t ↦ r₁ * Real.cos (ω * (t - a)) - r₂ * Real.sin (ω * (t - a))
  set y₀ : ℝ → ℝ := fun t ↦ r₁ * Real.sin (ω * (t - a)) + r₂ * Real.cos (ω * (t - a))
  have hx₀ : AbsolutelyContinuousOnInterval x₀ a (a + T) := by
    simpa [x₀, sub_eq_add_neg, neg_mul] using
      absolutelyContinuousOnInterval_circle_coord a (a + T) ω 0 r₁ (-r₂)
  have hy₀ : AbsolutelyContinuousOnInterval y₀ a (a + T) := by
    have h := absolutelyContinuousOnInterval_circle_coord a (a + T) ω 0 r₂ r₁
    convert h using 1; ext t; dsimp [y₀]; ring
  have hωT : ω * T = 2 * Real.pi := by dsimp [ω]; field_simp
  have hx₀_per : x₀ (a + T) = x₀ a := by simp [x₀, hωT]
  have hy₀_per : y₀ (a + T) = y₀ a := by simp [y₀, hωT]
  have hshift :
      signedArea (fun t ↦ c₁ + r₁ * Real.cos (ω * (t - a)) - r₂ * Real.sin (ω * (t - a)))
        (fun t ↦ c₂ + r₁ * Real.sin (ω * (t - a)) + r₂ * Real.cos (ω * (t - a))) a T =
        signedArea x₀ y₀ a T := by
    have h := signedArea_add_const hx₀ hy₀ hx₀_per hy₀_per c₁ c₂
    convert h using 2 <;> (ext t; dsimp [x₀, y₀]; ring)
  rw [hshift]
  unfold signedArea
  have hpt (t : ℝ) : x₀ t * deriv y₀ t - y₀ t * deriv x₀ t = ω * (r₁ ^ 2 + r₂ ^ 2) := by
    have hd := hasDerivAt_circle_coord a ω 0 0 r₁ r₂ t
    have hdx : deriv x₀ t = -ω * y₀ t := by
      simpa [x₀, y₀, sub_eq_add_neg] using hd.1.deriv
    have hdy : deriv y₀ t = ω * x₀ t := by
      simpa [x₀, y₀] using hd.2.deriv
    rw [hdx, hdy]
    calc x₀ t * (ω * x₀ t) - y₀ t * (-ω * y₀ t)
        = ω * ((r₁ ^ 2 + r₂ ^ 2) * (Real.cos (ω * (t - a)) ^ 2 + Real.sin (ω * (t - a)) ^ 2)) := by
          dsimp [x₀, y₀]; ring
      _ = ω * (r₁ ^ 2 + r₂ ^ 2) := by rw [Real.cos_sq_add_sin_sq, mul_one]
  simp_rw [hpt, intervalIntegral.integral_const, smul_eq_mul]
  dsimp [ω]
  have : a + T - a = T := by ring
  rw [this]
  field_simp

/-- The signed area of a negatively oriented circle
`x t = c₁ + r₁ cos(2π(t - a)/T) + r₂ sin(2π(t - a)/T)`,
`y t = c₂ - r₁ sin(2π(t - a)/T) + r₂ cos(2π(t - a)/T)` on `[a, a + T]` (`T > 0`) is
`-π * (r₁ ^ 2 + r₂ ^ 2)`. -/
theorem signedArea_circle_neg (hT : 0 < T) (a c₁ c₂ r₁ r₂ : ℝ) :
    signedArea
      (fun t ↦ c₁ + r₁ * Real.cos (2 * Real.pi * (t - a) / T) +
        r₂ * Real.sin (2 * Real.pi * (t - a) / T))
      (fun t ↦ c₂ - r₁ * Real.sin (2 * Real.pi * (t - a) / T) +
        r₂ * Real.cos (2 * Real.pi * (t - a) / T)) a T =
      -(Real.pi * (r₁ ^ 2 + r₂ ^ 2)) := by
  have hx :
      (fun t ↦ c₁ + r₁ * Real.cos (2 * Real.pi * (t - a) / T) +
        r₂ * Real.sin (2 * Real.pi * (t - a) / T)) =
      (fun t ↦ c₁ + r₂ * Real.sin (2 * Real.pi * (t - a) / T) +
        r₁ * Real.cos (2 * Real.pi * (t - a) / T)) := by
    ext t; ring
  have hy :
      (fun t ↦ c₂ - r₁ * Real.sin (2 * Real.pi * (t - a) / T) +
        r₂ * Real.cos (2 * Real.pi * (t - a) / T)) =
      (fun t ↦ c₂ + r₂ * Real.cos (2 * Real.pi * (t - a) / T) -
        r₁ * Real.sin (2 * Real.pi * (t - a) / T)) := by
    ext t; ring
  rw [hx, hy, signedArea_swap, signedArea_circle_pos hT a c₂ c₁ r₂ r₁]
  ring

/-! ### Exact `L²` deficiency identity and the sharp area--energy inequality -/

/-- **Exact `L²` area--energy deficiency identity** for closed absolutely continuous plane curves:
for `T > 0` and `σ ∈ {-1, 1}` (`σ ^ 2 = 1`), the difference between the scaled energy
`T * ∫ (deriv x ^ 2 + deriv y ^ 2)` and `4π σ * signedArea x y a T` decomposes into the sum of
the Wirtinger deficiencies of `x` and `y` and the `L²` norm of the Cauchy--Riemann residual
`(deriv x + σ ω (y - ȳ), deriv y - σ ω (x - x̄))` with `ω = 2π / T`. -/
theorem area_energy_deficiency_identity (hT : 0 < T) {σ : ℝ} (hσ : σ ^ 2 = 1) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a)
    (hx' : MemLp (deriv x) 2 (volume.restrict (Ioc a (a + T))))
    (hy' : MemLp (deriv y) 2 (volume.restrict (Ioc a (a + T)))) :
    T * (∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)) -
        4 * Real.pi * (σ * signedArea x y a T) =
      (T / 2) * ((∫ t in a..(a + T), deriv x t ^ 2) -
        (2 * Real.pi / T) ^ 2 * ∫ t in a..(a + T), (x t - ⨍ s in a..(a + T), x s) ^ 2) +
      (T / 2) * ((∫ t in a..(a + T), deriv y t ^ 2) -
        (2 * Real.pi / T) ^ 2 * ∫ t in a..(a + T), (y t - ⨍ s in a..(a + T), y s) ^ 2) +
      (T / 2) * ∫ t in a..(a + T),
        ((deriv x t + σ * (2 * Real.pi / T) * (y t - ⨍ s in a..(a + T), y s)) ^ 2 +
         (deriv y t - σ * (2 * Real.pi / T) * (x t - ⨍ s in a..(a + T), x s)) ^ 2) := by
  set ω := 2 * Real.pi / T
  set mx := ⨍ s in a..(a + T), x s
  set my := ⨍ s in a..(a + T), y s
  set x₀ : ℝ → ℝ := fun t ↦ x t - mx
  set y₀ : ℝ → ℝ := fun t ↦ y t - my
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hx₀_cont : ContinuousOn x₀ [[a, a + T]] := hx.continuousOn.sub continuousOn_const
  have hy₀_cont : ContinuousOn y₀ [[a, a + T]] := hy.continuousOn.sub continuousOn_const
  have hx'_sq : IntervalIntegrable (fun t ↦ deriv x t ^ 2) volume a (a + T) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    simpa [IntegrableOn, Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hx'.aestronglyMeasurable).1 hx'
  have hy'_sq : IntervalIntegrable (fun t ↦ deriv y t ^ 2) volume a (a + T) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    simpa [IntegrableOn, Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hy'.aestronglyMeasurable).1 hy'
  have hx₀_sq : IntervalIntegrable (fun t ↦ x₀ t ^ 2) volume a (a + T) :=
    (hx₀_cont.pow 2).intervalIntegrable
  have hy₀_sq : IntervalIntegrable (fun t ↦ y₀ t ^ 2) volume a (a + T) :=
    (hy₀_cont.pow 2).intervalIntegrable
  have hx₀dy : IntervalIntegrable (fun t ↦ x₀ t * deriv y t) volume a (a + T) :=
    hy.intervalIntegrable_deriv.continuousOn_mul hx₀_cont
  have hy₀dx : IntervalIntegrable (fun t ↦ y₀ t * deriv x t) volume a (a + T) :=
    hx.intervalIntegrable_deriv.continuousOn_mul hy₀_cont
  have harea :
      2 * signedArea x y a T = ∫ t in a..(a + T), (x₀ t * deriv y t - y₀ t * deriv x t) := by
    rw [← signedArea_sub_const hx hy hx_per hy_per mx my]
    unfold signedArea
    have hdx : deriv x₀ = deriv x := funext fun _ ↦ deriv_sub_const mx
    have hdy : deriv y₀ = deriv y := funext fun _ ↦ deriv_sub_const my
    rw [hdx, hdy]
    ring
  have hres_eq : (fun t ↦ (deriv x t + σ * ω * y₀ t) ^ 2 + (deriv y t - σ * ω * x₀ t) ^ 2) =
      fun t ↦ ((deriv x t ^ 2 + deriv y t ^ 2) + (ω ^ 2 * x₀ t ^ 2 + ω ^ 2 * y₀ t ^ 2)) -
        2 * σ * ω * (x₀ t * deriv y t - y₀ t * deriv x t) := by
    ext t
    linear_combination (ω ^ 2 * (x₀ t ^ 2 + y₀ t ^ 2)) * hσ
  have hres_int :
      ∫ t in a..(a + T), ((deriv x t + σ * ω * y₀ t) ^ 2 + (deriv y t - σ * ω * x₀ t) ^ 2) =
        ((∫ t in a..(a + T), deriv x t ^ 2) + ∫ t in a..(a + T), deriv y t ^ 2) +
        (ω ^ 2 * (∫ t in a..(a + T), x₀ t ^ 2) + ω ^ 2 * ∫ t in a..(a + T), y₀ t ^ 2) -
        2 * σ * ω * (2 * signedArea x y a T) := by
    rw [hres_eq, intervalIntegral.integral_sub
      ((hx'_sq.add hy'_sq).add ((hx₀_sq.const_mul (ω ^ 2)).add (hy₀_sq.const_mul (ω ^ 2))))
      ((hx₀dy.sub hy₀dx).const_mul (2 * σ * ω)),
      intervalIntegral.integral_add (hx'_sq.add hy'_sq)
        ((hx₀_sq.const_mul (ω ^ 2)).add (hy₀_sq.const_mul (ω ^ 2))),
      intervalIntegral.integral_add hx'_sq hy'_sq,
      intervalIntegral.integral_add (hx₀_sq.const_mul (ω ^ 2)) (hy₀_sq.const_mul (ω ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, ← harea]
  have hsum_energy : ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2) =
      (∫ t in a..(a + T), deriv x t ^ 2) + ∫ t in a..(a + T), deriv y t ^ 2 :=
    intervalIntegral.integral_add hx'_sq hy'_sq
  have hω_area :
      (T / 2) * (2 * σ * ω * (2 * signedArea x y a T)) =
        4 * Real.pi * (σ * signedArea x y a T) := by
    dsimp [ω]; field_simp; ring
  rw [hsum_energy, hres_int]
  linarith [hω_area]

private theorem wirtinger_deficiency_nonneg (hT : 0 < T) {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a (a + T)) (hf_per : f (a + T) = f a)
    (hf' : MemLp (deriv f) 2 (volume.restrict (Ioc a (a + T)))) :
    0 ≤ (∫ t in a..(a + T), deriv f t ^ 2) -
      (2 * Real.pi / T) ^ 2 * ∫ t in a..(a + T), (f t - ⨍ s in a..(a + T), f s) ^ 2 := by
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hw :=
    integral_norm_sub_average_sq_le_of_absolutelyContinuousOnInterval hab hf hf_per.symm hf'
  simp only [Real.norm_eq_abs, sq_abs, add_sub_cancel_left] at hw
  have hw' : (2 * Real.pi / T) ^ 2 * ∫ t in a..(a + T), (f t - ⨍ s in a..(a + T), f s) ^ 2 ≤
      ∫ t in a..(a + T), deriv f t ^ 2 := by
    calc (2 * Real.pi / T) ^ 2 * ∫ t in a..(a + T), (f t - ⨍ s in a..(a + T), f s) ^ 2
        ≤ (2 * Real.pi / T) ^ 2 * ((T / (2 * Real.pi)) ^ 2 * ∫ t in a..(a + T), deriv f t ^ 2) := by
          gcongr
      _ = ∫ t in a..(a + T), deriv f t ^ 2 := by field_simp
  linarith

/-- **Sharp area--energy inequality** (signed form): for any closed absolutely continuous plane
curve `(x, y)` on `[a, a + T]` (`T > 0`) with square-integrable derivative,
`4 * π * signedArea x y a T ≤ T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)`. -/
theorem four_mul_pi_mul_signedArea_le (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a)
    (hx' : MemLp (deriv x) 2 (volume.restrict (Ioc a (a + T))))
    (hy' : MemLp (deriv y) 2 (volume.restrict (Ioc a (a + T)))) :
    4 * Real.pi * signedArea x y a T ≤
      T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2) := by
  have hid := area_energy_deficiency_identity hT (σ := 1) (by norm_num) hx hy hx_per hy_per hx' hy'
  rw [one_mul] at hid
  have hwx := wirtinger_deficiency_nonneg hT hx hx_per hx'
  have hwy := wirtinger_deficiency_nonneg hT hy hy_per hy'
  have hres : 0 ≤ ∫ t in a..(a + T),
      ((deriv x t + 1 * (2 * Real.pi / T) * (y t - ⨍ s in a..(a + T), y s)) ^ 2 +
       (deriv y t - 1 * (2 * Real.pi / T) * (x t - ⨍ s in a..(a + T), x s)) ^ 2) :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ ↦ by positivity
  nlinarith

/-- **Sharp area--energy inequality** (negated signed form): for any closed absolutely continuous
plane curve `(x, y)` on `[a, a + T]` (`T > 0`) with square-integrable derivative,
`- (4 * π * signedArea x y a T) ≤ T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)`. -/
theorem neg_four_mul_pi_mul_signedArea_le (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a)
    (hx' : MemLp (deriv x) 2 (volume.restrict (Ioc a (a + T))))
    (hy' : MemLp (deriv y) 2 (volume.restrict (Ioc a (a + T)))) :
    -(4 * Real.pi * signedArea x y a T) ≤
      T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2) := by
  have h := four_mul_pi_mul_signedArea_le hT hy hx hy_per hx_per hy' hx'
  rw [signedArea_swap, mul_neg] at h
  convert h using 2
  refine intervalIntegral.integral_congr fun t _ ↦ by ring

/-- **Sharp area--energy inequality**: for any closed absolutely continuous plane curve `(x, y)` on
`[a, a + T]` (`T > 0`) with square-integrable derivative,
`4 * π * |signedArea x y a T| ≤ T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)`. -/
theorem four_mul_pi_mul_abs_signedArea_le (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a)
    (hx' : MemLp (deriv x) 2 (volume.restrict (Ioc a (a + T))))
    (hy' : MemLp (deriv y) 2 (volume.restrict (Ioc a (a + T)))) :
    4 * Real.pi * |signedArea x y a T| ≤
      T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2) := by
  rcases le_total 0 (signedArea x y a T) with h | h
  · rw [abs_of_nonneg h]
    exact four_mul_pi_mul_signedArea_le hT hx hy hx_per hy_per hx' hy'
  · rw [abs_of_nonpos h, mul_neg]
    exact neg_four_mul_pi_mul_signedArea_le hT hx hy hx_per hy_per hx' hy'

/-- Specialization of `four_mul_pi_mul_abs_signedArea_le` to `[0, T]` with `IntervalIntegrable`
energy hypotheses. -/
theorem four_mul_pi_mul_abs_signedArea_zero_le (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x 0 T)
    (hy : AbsolutelyContinuousOnInterval y 0 T)
    (hx_per : x T = x 0) (hy_per : y T = y 0)
    (hx' : IntervalIntegrable (fun t ↦ deriv x t ^ 2) volume 0 T)
    (hy' : IntervalIntegrable (fun t ↦ deriv y t ^ 2) volume 0 T) :
    4 * Real.pi * |signedArea x y 0 T| ≤
      T * ∫ t in (0 : ℝ)..T, (deriv x t ^ 2 + deriv y t ^ 2) := by
  have hx_mem : MemLp (deriv x) 2 (volume.restrict (Ioc 0 (0 + T))) := by
    rw [zero_add]
    refine (memLp_two_iff_integrable_sq_norm
      hx.intervalIntegrable_deriv.1.aestronglyMeasurable).2 ?_
    simpa [IntegrableOn, Real.norm_eq_abs, sq_abs] using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hx'
  have hy_mem : MemLp (deriv y) 2 (volume.restrict (Ioc 0 (0 + T))) := by
    rw [zero_add]
    refine (memLp_two_iff_integrable_sq_norm
      hy.intervalIntegrable_deriv.1.aestronglyMeasurable).2 ?_
    simpa [IntegrableOn, Real.norm_eq_abs, sq_abs] using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hy'
  have h := four_mul_pi_mul_abs_signedArea_le hT (a := 0)
    (by rwa [zero_add]) (by rwa [zero_add]) (by rwa [zero_add]) (by rwa [zero_add]) hx_mem hy_mem
  rwa [zero_add] at h

/-! ### Solving the almost-everywhere derivative relation via the AC FTC -/

/-- **AC FTC solver for the planar rotation system**: if `x, y : ℝ → ℝ` are absolutely continuous
on `[a, b]` (`a ≤ b`) and satisfy `deriv x t = -ω * (y t - c₂)` and `deriv y t = ω * (x t - c₁)`
for `volume`-almost every `t ∈ Icc a b`, then `(x, y)` is the circle centered at `(c₁, c₂)` with
initial point `(x a, y a)` traversed at angular speed `ω`. -/
theorem eq_circle_of_ae_deriv_eq (hab : a ≤ b) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a b)
    (hy : AbsolutelyContinuousOnInterval y a b) (ω c₁ c₂ : ℝ)
    (hderiv : ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv x t = -ω * (y t - c₂) ∧ deriv y t = ω * (x t - c₁)) :
    ∀ t ∈ Icc a b,
      x t = c₁ + (x a - c₁) * Real.cos (ω * (t - a)) - (y a - c₂) * Real.sin (ω * (t - a)) ∧
      y t = c₂ + (x a - c₁) * Real.sin (ω * (t - a)) + (y a - c₂) * Real.cos (ω * (t - a)) := by
  set x₀ : ℝ → ℝ := fun t ↦ x t - c₁
  set y₀ : ℝ → ℝ := fun t ↦ y t - c₂
  set C : ℝ → ℝ := fun t ↦ Real.cos (ω * (t - a))
  set S : ℝ → ℝ := fun t ↦ Real.sin (ω * (t - a))
  set u : ℝ → ℝ := fun t ↦ x₀ t * C t + y₀ t * S t
  set v : ℝ → ℝ := fun t ↦ -x₀ t * S t + y₀ t * C t
  have hx₀ : AbsolutelyContinuousOnInterval x₀ a b :=
    hx.sub (absolutelyContinuousOnInterval_const_real c₁ a b)
  have hy₀ : AbsolutelyContinuousOnInterval y₀ a b :=
    hy.sub (absolutelyContinuousOnInterval_const_real c₂ a b)
  have hC : AbsolutelyContinuousOnInterval C a b := by
    simpa [C] using absolutelyContinuousOnInterval_circle_coord a b ω 0 1 0
  have hS : AbsolutelyContinuousOnInterval S a b := by
    simpa [S] using absolutelyContinuousOnInterval_circle_coord a b ω 0 0 1
  have hu : AbsolutelyContinuousOnInterval u a b := (hx₀.fun_mul hC).add (hy₀.fun_mul hS)
  have hv : AbsolutelyContinuousOnInterval v a b := (hx₀.neg.fun_mul hS).add (hy₀.fun_mul hC)
  have hu_deriv_zero : ∀ᵐ t ∂volume, t ∈ Icc a b → deriv u t = 0 ∧ deriv v t = 0 := by
    filter_upwards [hx.ae_differentiableAt, hy.ae_differentiableAt, hderiv] with t hxt hyt hdt ht
    have ht_uIcc : t ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hx₀_d : HasDerivAt x₀ (deriv x t) t := (hxt ht_uIcc).hasDerivAt.sub_const c₁
    have hy₀_d : HasDerivAt y₀ (deriv y t) t := (hyt ht_uIcc).hasDerivAt.sub_const c₂
    have hθ : HasDerivAt (fun s ↦ ω * (s - a)) ω t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul ω
    have hC_d : HasDerivAt C (-S t * ω) t := hθ.cos
    have hS_d : HasDerivAt S (C t * ω) t := hθ.sin
    have hu_d : HasDerivAt u (deriv x t * C t + x₀ t * (-S t * ω) +
        (deriv y t * S t + y₀ t * (C t * ω))) t :=
      (hx₀_d.mul hC_d).add (hy₀_d.mul hS_d)
    have hv_d : HasDerivAt v (-deriv x t * S t + -x₀ t * (C t * ω) +
        (deriv y t * C t + y₀ t * (-S t * ω))) t :=
      (hx₀_d.neg.mul hS_d).add (hy₀_d.mul hC_d)
    rw [hu_d.deriv, hv_d.deriv, (hdt ht).1, (hdt ht).2]
    dsimp [x₀, y₀]
    constructor <;> ring
  intro t ht
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc_right ht.2
  have hu_t : u t - u a = 0 := by
    rw [← (hu.mono hsub).integral_deriv_eq_sub]
    have hcongr : ∫ s in a..t, deriv u s = ∫ _ in a..t, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le ht.1]
      filter_upwards [hu_deriv_zero] with s hs hs_mem
      exact (hs ⟨hs_mem.1.le, hs_mem.2.trans ht.2⟩).1
    rw [hcongr, intervalIntegral.integral_zero]
  have hv_t : v t - v a = 0 := by
    rw [← (hv.mono hsub).integral_deriv_eq_sub]
    have hcongr : ∫ s in a..t, deriv v s = ∫ _ in a..t, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le ht.1]
      filter_upwards [hu_deriv_zero] with s hs hs_mem
      exact (hs ⟨hs_mem.1.le, hs_mem.2.trans ht.2⟩).2
    rw [hcongr, intervalIntegral.integral_zero]
  have hua : u t = x a - c₁ := by
    have : u a = x a - c₁ := by simp [u, x₀, C, S]
    linarith
  have hva : v t = y a - c₂ := by
    have : v a = y a - c₂ := by simp [v, y₀, C, S]
    linarith
  have hCS : C t ^ 2 + S t ^ 2 = 1 := Real.cos_sq_add_sin_sq (ω * (t - a))
  constructor
  · linear_combination (C t) * hua - (S t) * hva - (x₀ t) * hCS
  · linear_combination (S t) * hua + (C t) * hva - (y₀ t) * hCS

/-! ### Complete equality characterizations in the sharp area--energy inequality -/

private theorem eq_of_eqOn_circle_pos (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a) (c₁ c₂ r₁ r₂ : ℝ)
    (hxy : ∀ t ∈ Icc a (a + T),
      x t = c₁ + r₁ * Real.cos (2 * Real.pi * (t - a) / T) -
        r₂ * Real.sin (2 * Real.pi * (t - a) / T) ∧
      y t = c₂ + r₁ * Real.sin (2 * Real.pi * (t - a) / T) +
        r₂ * Real.cos (2 * Real.pi * (t - a) / T)) :
    4 * Real.pi * signedArea x y a T =
      T * (∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)) := by
  set ω := 2 * Real.pi / T
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hω (t : ℝ) : ω * (t - a) = 2 * Real.pi * (t - a) / T := by dsimp [ω]; ring
  set X : ℝ → ℝ := fun t ↦ c₁ + r₁ * Real.cos (ω * (t - a)) - r₂ * Real.sin (ω * (t - a))
  set Y : ℝ → ℝ := fun t ↦ c₂ + r₁ * Real.sin (ω * (t - a)) + r₂ * Real.cos (ω * (t - a))
  have hxX : EqOn x X (Icc a (a + T)) := fun t ht ↦ by simpa [X, hω t] using (hxy t ht).1
  have hyY : EqOn y Y (Icc a (a + T)) := fun t ht ↦ by simpa [Y, hω t] using (hxy t ht).2
  have hae_deriv : ∀ᵐ t ∂volume, t ∈ Ioc a (a + T) →
      deriv x t = deriv X t ∧ deriv y t = deriv Y t := by
    have hae_Ioo : (Ioo a (a + T) : Set ℝ) =ᵐ[volume] Ioc a (a + T) := Ioo_ae_eq_Ioc
    filter_upwards [hae_Ioo] with t ht ht_Ioc
    have ht_Ioo : t ∈ Ioo a (a + T) := by rwa [ht]
    have hx_ev : x =ᶠ[nhds t] X :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht_Ioo.1 ht_Ioo.2)
        fun s hs ↦ hxX (Ioo_subset_Icc_self hs)
    have hy_ev : y =ᶠ[nhds t] Y :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht_Ioo.1 ht_Ioo.2)
        fun s hs ↦ hyY (Ioo_subset_Icc_self hs)
    exact ⟨hx_ev.deriv_eq, hy_ev.deriv_eq⟩
  have harea_eq : signedArea x y a T = Real.pi * (r₁ ^ 2 + r₂ ^ 2) := by
    rw [signedArea_eq_integral_mul_deriv hx hy hx_per hy_per]
    have hX_ac : AbsolutelyContinuousOnInterval X a (a + T) := by
      simpa [X, sub_eq_add_neg, neg_mul] using
        absolutelyContinuousOnInterval_circle_coord a (a + T) ω c₁ r₁ (-r₂)
    have hY_ac : AbsolutelyContinuousOnInterval Y a (a + T) := by
      have h := absolutelyContinuousOnInterval_circle_coord a (a + T) ω c₂ r₂ r₁
      convert h using 1; ext t; dsimp [Y]; ring
    have hωT : ω * T = 2 * Real.pi := by dsimp [ω]; field_simp
    have hX_per : X (a + T) = X a := by simp [X, hωT]
    have hY_per : Y (a + T) = Y a := by simp [Y, hωT]
    have hcirc_area := signedArea_circle_pos hT a c₁ c₂ r₁ r₂
    simp_rw [← hω] at hcirc_area
    rw [← hcirc_area, signedArea_eq_integral_mul_deriv hX_ac hY_ac hX_per hY_per]
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab.le]
    filter_upwards [hae_deriv] with t ht ht_mem
    rw [hxX (Ioc_subset_Icc_self ht_mem), (ht ht_mem).2]
  have henergy_eq : ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2) =
      T * (ω ^ 2 * (r₁ ^ 2 + r₂ ^ 2)) := by
    have hconst : ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2) =
        ∫ _ in a..(a + T), ω ^ 2 * (r₁ ^ 2 + r₂ ^ 2) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hab.le]
      filter_upwards [hae_deriv] with t ht ht_mem
      have hd := hasDerivAt_circle_coord a ω c₁ c₂ r₁ r₂ t
      rw [(ht ht_mem).1, (ht ht_mem).2, hd.1.deriv, hd.2.deriv]
      calc (-ω * (r₁ * Real.sin (ω * (t - a)) + r₂ * Real.cos (ω * (t - a)))) ^ 2 +
            (ω * (r₁ * Real.cos (ω * (t - a)) - r₂ * Real.sin (ω * (t - a)))) ^ 2
          = ω ^ 2 * ((r₁ ^ 2 + r₂ ^ 2) *
              (Real.cos (ω * (t - a)) ^ 2 + Real.sin (ω * (t - a)) ^ 2)) := by ring
        _ = ω ^ 2 * (r₁ ^ 2 + r₂ ^ 2) := by rw [Real.cos_sq_add_sin_sq, mul_one]
    rw [hconst, intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
  rw [harea_eq, henergy_eq]
  dsimp [ω]
  field_simp
  ring

/-- **Almost-everywhere derivative characterization of equality** (positive orientation):
for a closed absolutely continuous plane curve `(x, y)` on `[a, a + T]` (`T > 0`) with
square-integrable derivative, `4 * π * signedArea x y a T = T * ∫ (deriv x ^ 2 + deriv y ^ 2)`
holds if and only if `deriv x t = - (2π / T) * (y t - ȳ)` and `deriv y t = (2π / T) * (x t - x̄)`
for `volume`-almost every `t ∈ Icc a (a + T)`. -/
theorem four_mul_pi_mul_signedArea_eq_iff_ae_deriv (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a)
    (hx' : MemLp (deriv x) 2 (volume.restrict (Ioc a (a + T))))
    (hy' : MemLp (deriv y) 2 (volume.restrict (Ioc a (a + T)))) :
    4 * Real.pi * signedArea x y a T =
      T * (∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)) ↔
      ∀ᵐ t ∂volume, t ∈ Icc a (a + T) →
        deriv x t = -(2 * Real.pi / T) * (y t - ⨍ s in a..(a + T), y s) ∧
        deriv y t = (2 * Real.pi / T) * (x t - ⨍ s in a..(a + T), x s) := by
  set ω := 2 * Real.pi / T
  set mx := ⨍ s in a..(a + T), x s
  set my := ⨍ s in a..(a + T), y s
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hid := area_energy_deficiency_identity hT (σ := 1) (by norm_num) hx hy hx_per hy_per hx' hy'
  simp only [one_mul] at hid
  set R : ℝ → ℝ := fun t ↦
    (deriv x t + ω * (y t - my)) ^ 2 + (deriv y t - ω * (x t - mx)) ^ 2
  have hx'_sq : IntervalIntegrable (fun t ↦ deriv x t ^ 2) volume a (a + T) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    simpa [IntegrableOn, Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hx'.aestronglyMeasurable).1 hx'
  have hy'_sq : IntervalIntegrable (fun t ↦ deriv y t ^ 2) volume a (a + T) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    simpa [IntegrableOn, Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hy'.aestronglyMeasurable).1 hy'
  have hR_int : IntervalIntegrable R volume a (a + T) := by
    have h1 : IntervalIntegrable (fun t ↦ (deriv x t + ω * (y t - my)) ^ 2) volume a (a + T) := by
      have hsub : ContinuousOn (fun t ↦ ω * (y t - my)) [[a, a + T]] :=
        continuousOn_const.mul (hy.continuousOn.sub continuousOn_const)
      have heq : (fun t ↦ (deriv x t + ω * (y t - my)) ^ 2) =
          fun t ↦ deriv x t ^ 2 + 2 * ((ω * (y t - my)) * deriv x t) + (ω * (y t - my)) ^ 2 := by
        ext t; ring
      rw [heq]
      exact (hx'_sq.add ((hx.intervalIntegrable_deriv.continuousOn_mul hsub).const_mul 2)).add
        (hsub.pow 2).intervalIntegrable
    have h2 : IntervalIntegrable (fun t ↦ (deriv y t - ω * (x t - mx)) ^ 2) volume a (a + T) := by
      have hsub : ContinuousOn (fun t ↦ ω * (x t - mx)) [[a, a + T]] :=
        continuousOn_const.mul (hx.continuousOn.sub continuousOn_const)
      have heq : (fun t ↦ (deriv y t - ω * (x t - mx)) ^ 2) =
          fun t ↦ deriv y t ^ 2 - 2 * ((ω * (x t - mx)) * deriv y t) + (ω * (x t - mx)) ^ 2 := by
        ext t; ring
      rw [heq]
      exact (hy'_sq.sub ((hy.intervalIntegrable_deriv.continuousOn_mul hsub).const_mul 2)).add
        (hsub.pow 2).intervalIntegrable
    exact h1.add h2
  refine ⟨fun heq ↦ ?_, fun hae ↦ ?_⟩
  · have hwx := wirtinger_deficiency_nonneg hT hx hx_per hx'
    have hwy := wirtinger_deficiency_nonneg hT hy hy_per hy'
    have hR_nonneg : 0 ≤ ∫ t in a..(a + T), R t :=
      intervalIntegral.integral_nonneg hab.le fun _ _ ↦ by dsimp [R]; positivity
    have hR_zero : ∫ t in a..(a + T), R t = 0 := by nlinarith [hid, heq]
    have hae_Ioc : R =ᵐ[volume.restrict (Ioc a (a + T))] 0 :=
      (integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
        (Filter.Eventually.of_forall fun _ ↦ by dsimp [R]; positivity) hR_int).1 hR_zero
    have hae_Icc : R =ᵐ[volume.restrict (Icc a (a + T))] 0 :=
      ae_restrict_of_ae_eq_of_ae_restrict Ioc_ae_eq_Icc hae_Ioc
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc] at hae_Icc
    filter_upwards [hae_Icc] with t ht ht_mem
    have h0 : (deriv x t + ω * (y t - my)) ^ 2 + (deriv y t - ω * (x t - mx)) ^ 2 = 0 := ht ht_mem
    have h1 : (deriv x t + ω * (y t - my)) ^ 2 = 0 := by
      nlinarith [sq_nonneg (deriv x t + ω * (y t - my)), sq_nonneg (deriv y t - ω * (x t - mx))]
    have h2 : (deriv y t - ω * (x t - mx)) ^ 2 = 0 := by
      nlinarith [sq_nonneg (deriv x t + ω * (y t - my)), sq_nonneg (deriv y t - ω * (x t - mx))]
    exact ⟨by linarith [sq_eq_zero_iff.1 h1], by linarith [sq_eq_zero_iff.1 h2]⟩
  · have hcirc := eq_circle_of_ae_deriv_eq hab.le hx hy ω mx my hae
    have hω (t : ℝ) : ω * (t - a) = 2 * Real.pi * (t - a) / T := by dsimp [ω]; ring
    exact eq_of_eqOn_circle_pos hT hx hy hx_per hy_per mx my (x a - mx) (y a - my)
      fun t ht ↦ by simpa [hω t] using hcirc t ht

/-- **Almost-everywhere derivative characterization of equality** (negative orientation):
for a closed absolutely continuous plane curve `(x, y)` on `[a, a + T]` (`T > 0`) with
square-integrable derivative, `- (4 * π * signedArea x y a T) = T * ∫ (deriv x ^ 2 + deriv y ^ 2)`
holds if and only if `deriv x t = (2π / T) * (y t - ȳ)` and `deriv y t = - (2π / T) * (x t - x̄)`
for `volume`-almost every `t ∈ Icc a (a + T)`. -/
theorem neg_four_mul_pi_mul_signedArea_eq_iff_ae_deriv (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a)
    (hx' : MemLp (deriv x) 2 (volume.restrict (Ioc a (a + T))))
    (hy' : MemLp (deriv y) 2 (volume.restrict (Ioc a (a + T)))) :
    -(4 * Real.pi * signedArea x y a T) =
      T * (∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)) ↔
      ∀ᵐ t ∂volume, t ∈ Icc a (a + T) →
        deriv x t = (2 * Real.pi / T) * (y t - ⨍ s in a..(a + T), y s) ∧
        deriv y t = -(2 * Real.pi / T) * (x t - ⨍ s in a..(a + T), x s) := by
  have h := four_mul_pi_mul_signedArea_eq_iff_ae_deriv hT hy hx hy_per hx_per hy' hx'
  have hswap_area : 4 * Real.pi * signedArea y x a T = -(4 * Real.pi * signedArea x y a T) := by
    rw [signedArea_swap, mul_neg]
  have hswap_energy : (∫ t in a..(a + T), (deriv y t ^ 2 + deriv x t ^ 2)) =
      ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2) :=
    intervalIntegral.integral_congr fun _ _ ↦ add_comm _ _
  rw [← hswap_area, ← hswap_energy, h]
  refine ⟨fun hae ↦ ?_, fun hae ↦ ?_⟩ <;>
  · filter_upwards [hae] with t ht ht_mem
    exact ⟨(ht ht_mem).2, (ht ht_mem).1⟩

/-- **Circle rigidity for signed area** (positive orientation): equality
`4 * π * signedArea x y a T = T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)` holds if and
only if `(x, y)` on `Icc a (a + T)` is a positively oriented circle traversed once at constant
angular speed `2π / T` (including the degenerate case `r₁ = r₂ = 0` of a constant curve). -/
theorem four_mul_pi_mul_signedArea_eq_iff (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a)
    (hx' : MemLp (deriv x) 2 (volume.restrict (Ioc a (a + T))))
    (hy' : MemLp (deriv y) 2 (volume.restrict (Ioc a (a + T)))) :
    4 * Real.pi * signedArea x y a T =
      T * (∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)) ↔
      ∃ c₁ c₂ r₁ r₂ : ℝ, ∀ t ∈ Icc a (a + T),
        x t = c₁ + r₁ * Real.cos (2 * Real.pi * (t - a) / T) -
          r₂ * Real.sin (2 * Real.pi * (t - a) / T) ∧
        y t = c₂ + r₁ * Real.sin (2 * Real.pi * (t - a) / T) +
          r₂ * Real.cos (2 * Real.pi * (t - a) / T) := by
  refine ⟨fun heq ↦ ?_, fun ⟨c₁, c₂, r₁, r₂, hxy⟩ ↦
    eq_of_eqOn_circle_pos hT hx hy hx_per hy_per c₁ c₂ r₁ r₂ hxy⟩
  have hae := (four_mul_pi_mul_signedArea_eq_iff_ae_deriv hT hx hy hx_per hy_per hx' hy').1 heq
  set ω := 2 * Real.pi / T
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hω (t : ℝ) : ω * (t - a) = 2 * Real.pi * (t - a) / T := by dsimp [ω]; ring
  have hcirc := eq_circle_of_ae_deriv_eq hab.le hx hy ω
    (⨍ s in a..(a + T), x s) (⨍ s in a..(a + T), y s) hae
  refine ⟨⨍ s in a..(a + T), x s, ⨍ s in a..(a + T), y s,
    x a - ⨍ s in a..(a + T), x s, y a - ⨍ s in a..(a + T), y s, fun t ht ↦ ?_⟩
  simpa [hω t] using hcirc t ht

/-- **Circle rigidity for signed area** (negative orientation): equality
`- (4 * π * signedArea x y a T) = T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)` holds if
and only if `(x, y)` on `Icc a (a + T)` is a negatively oriented circle traversed once at constant
angular speed `2π / T` (including the degenerate case `r₁ = r₂ = 0` of a constant curve). -/
theorem neg_four_mul_pi_mul_signedArea_eq_iff (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a)
    (hx' : MemLp (deriv x) 2 (volume.restrict (Ioc a (a + T))))
    (hy' : MemLp (deriv y) 2 (volume.restrict (Ioc a (a + T)))) :
    -(4 * Real.pi * signedArea x y a T) =
      T * (∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)) ↔
      ∃ c₁ c₂ r₁ r₂ : ℝ, ∀ t ∈ Icc a (a + T),
        x t = c₁ + r₁ * Real.cos (2 * Real.pi * (t - a) / T) +
          r₂ * Real.sin (2 * Real.pi * (t - a) / T) ∧
        y t = c₂ - r₁ * Real.sin (2 * Real.pi * (t - a) / T) +
          r₂ * Real.cos (2 * Real.pi * (t - a) / T) := by
  have h := four_mul_pi_mul_signedArea_eq_iff hT hy hx hy_per hx_per hy' hx'
  have hswap_area : 4 * Real.pi * signedArea y x a T = -(4 * Real.pi * signedArea x y a T) := by
    rw [signedArea_swap, mul_neg]
  have hswap_energy : (∫ t in a..(a + T), (deriv y t ^ 2 + deriv x t ^ 2)) =
      ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2) :=
    intervalIntegral.integral_congr fun _ _ ↦ add_comm _ _
  rw [← hswap_area, ← hswap_energy, h]
  refine ⟨fun ⟨c₂, c₁, r₂, r₁, hxy⟩ ↦ ⟨c₁, c₂, r₁, r₂, fun t ht ↦ ?_⟩,
    fun ⟨c₁, c₂, r₁, r₂, hxy⟩ ↦ ⟨c₂, c₁, r₂, r₁, fun t ht ↦ ?_⟩⟩
  · exact ⟨by linarith [(hxy t ht).2], by linarith [(hxy t ht).1]⟩
  · exact ⟨by linarith [(hxy t ht).2], by linarith [(hxy t ht).1]⟩

/-- **Complete equality characterization in the sharp area--energy inequality**: for any closed
absolutely continuous plane curve `(x, y)` on `[a, a + T]` (`T > 0`) with square-integrable
derivative, `4 * π * |signedArea x y a T| = T * ∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)`
holds if and only if `(x, y)` on `Icc a (a + T)` is a constant curve or a translated circle
traversed once at constant angular speed `2π / T` with either positive or negative orientation. -/
theorem four_mul_pi_mul_abs_signedArea_eq_iff (hT : 0 < T) {x y : ℝ → ℝ}
    (hx : AbsolutelyContinuousOnInterval x a (a + T))
    (hy : AbsolutelyContinuousOnInterval y a (a + T))
    (hx_per : x (a + T) = x a) (hy_per : y (a + T) = y a)
    (hx' : MemLp (deriv x) 2 (volume.restrict (Ioc a (a + T))))
    (hy' : MemLp (deriv y) 2 (volume.restrict (Ioc a (a + T)))) :
    4 * Real.pi * |signedArea x y a T| =
      T * (∫ t in a..(a + T), (deriv x t ^ 2 + deriv y t ^ 2)) ↔
      (∃ c₁ c₂ r₁ r₂ : ℝ, ∀ t ∈ Icc a (a + T),
        x t = c₁ + r₁ * Real.cos (2 * Real.pi * (t - a) / T) -
          r₂ * Real.sin (2 * Real.pi * (t - a) / T) ∧
        y t = c₂ + r₁ * Real.sin (2 * Real.pi * (t - a) / T) +
          r₂ * Real.cos (2 * Real.pi * (t - a) / T)) ∨
      (∃ c₁ c₂ r₁ r₂ : ℝ, ∀ t ∈ Icc a (a + T),
        x t = c₁ + r₁ * Real.cos (2 * Real.pi * (t - a) / T) +
          r₂ * Real.sin (2 * Real.pi * (t - a) / T) ∧
        y t = c₂ - r₁ * Real.sin (2 * Real.pi * (t - a) / T) +
          r₂ * Real.cos (2 * Real.pi * (t - a) / T)) := by
  rw [← four_mul_pi_mul_signedArea_eq_iff hT hx hy hx_per hy_per hx' hy',
    ← neg_four_mul_pi_mul_signedArea_eq_iff hT hx hy hx_per hy_per hx' hy']
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases le_total 0 (signedArea x y a T) with hsa | hsa
    · left; rwa [abs_of_nonneg hsa] at h
    · right; rwa [abs_of_nonpos hsa, mul_neg] at h
  · have habs_le := four_mul_pi_mul_abs_signedArea_le hT hx hy hx_per hy_per hx' hy'
    rcases h with h1 | h2
    · refine le_antisymm habs_le ?_
      rw [← h1]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    · refine le_antisymm habs_le ?_
      rw [← h2, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)

end TauCeti
