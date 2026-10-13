/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.Perimeter

/-!
# Geometric invariance, homogeneous scaling, isometric transport, and the coarea inequality for BV

This file establishes the geometric invariance and scaling laws of `divergence`,
`distributionalVariation`, `relativePerimeter`, and `perimeter` on finite-dimensional real inner
product spaces, together with the Cavalieri / layer-cake divergence identity and the variational
coarea inequality relating total variation to the integral of superlevel-set perimeters:

1. **Translation invariance**: `divergence`, `distributionalVariation`, `relativePerimeter`, and
   `perimeter` are invariant under left and right translations (`x ↦ x + a`, `x ↦ a + x`,
   `x ↦ x - a`, and pointwise set translations `a +ᵥ s`).
2. **Homogeneous scaling under positive dilations `r > 0`**: under `x ↦ r • x`, the divergence
   scales by `r`, and for any additive Haar measure `μ`, the variational total variation of
   `x ↦ u (r⁻¹ • x)` and the perimeter of `r • s` scale by `r ^ (Module.finrank ℝ E) / r` (which
   simplifies to `r ^ (Module.finrank ℝ E - 1)` when `E` is nontrivial).
3. **Linear isometry transport**: for any linear isometric equivalence `L : E ≃ₗᵢ[ℝ] F`, the
   conjugated vector field `y ↦ L (φ (L.symm y))` has divergence `divergence φ (L.symm y)`, and
   `distributionalVariation`, `relativePerimeter`, and `perimeter` are preserved under pullback and
   pushforward along `L`.
4. **Cavalieri / layer-cake divergence identity and coarea inequality**: for any nonnegative
   locally integrable function `u` on `Ω` and any test vector field `φ : 𝓓(Ω, E)`,
   `∫ x in Ω, u x * divergence φ x ∂μ =
     ∫ t in Ioi 0, (∫ x in Ω, {x | t < u x}.indicator 1 x * divergence φ x ∂μ)`. Taking the
   supremum over admissible test vector fields yields the variational coarea inequality
   `distributionalVariation μ Ω u ≤ ∫⁻ t in Ioi 0, relativePerimeter μ Ω {x | t < u x}`.

## Main results

* `TauCeti.divergence_comp_add_right`, `TauCeti.divergence_comp_add_left`,
  `TauCeti.distributionalVariation_comp_add_right`, `TauCeti.distributionalVariation_comp_add_left`,
  `TauCeti.perimeter_vadd`, `TauCeti.HasFinitePerimeter.vadd_iff`: translation invariance of
  divergence, variational total variation, and perimeter.
* `TauCeti.divergence_comp_smul`, `TauCeti.distributionalVariation_comp_inv_smul`,
  `TauCeti.distributionalVariation_top_comp_inv_smul_of_nontrivial`,
  `TauCeti.perimeter_smul`, `TauCeti.perimeter_smul_of_nontrivial`,
  `TauCeti.HasFinitePerimeter.smul_iff`: homogeneous scaling under positive dilations.
* `TauCeti.divergence_conj_linearIsometryEquiv`,
  `TauCeti.distributionalVariation_comp_linearIsometryEquiv`,
  `TauCeti.perimeter_image_linearIsometryEquiv`,
  `TauCeti.perimeter_preimage_linearIsometryEquiv`,
  `TauCeti.HasFinitePerimeter.image_linearIsometryEquiv_iff`: invariance under linear isometric
  equivalences.
* `TauCeti.integral_mul_divergence_eq_integral_superlevel`,
  `TauCeti.distributionalVariation_le_lintegral_relativePerimeter_superlevel`,
  `TauCeti.distributionalVariation_top_le_lintegral_perimeter_superlevel`,
  `TauCeti.isBVOn_of_lintegral_relativePerimeter_superlevel_lt_top`,
  `TauCeti.ae_hasFinitePerimeterIn_superlevel`: layer-cake divergence identity and variational
  coarea inequality.
-/

public section

open Filter Function MeasureTheory Pointwise Set TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Distributions Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {Ω : Opens E}

/-- Precomposing a bundled test function `φ : 𝓓(Ω, F)` with a smooth homeomorphism `g : E' ≃ₜ E`
yields a bundled test function on `Ω.comap ⟨g, g.continuous⟩`. -/
private def compHomeomorph {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {Ω : Opens E} (g : E' ≃ₜ E) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (φ : 𝓓(Ω, F)) : 𝓓(Ω.comap ⟨g, g.continuous⟩, F) where
  toFun := φ ∘ g
  contDiff' := φ.contDiff.comp hg
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph g
  tsupport_subset' := by
    rw [tsupport_comp_eq_preimage (φ : E → F) g]
    exact preimage_mono φ.tsupport_subset

/-! ### Translation invariance of divergence, variational total variation, and perimeter -/

/-- Right translation commutes with `divergence`. -/
@[simp]
theorem divergence_comp_add_right (φ : E → E) (a x : E) :
    divergence (fun y ↦ φ (y + a)) x = divergence φ (x + a) := by
  simp [divergence, fderiv_comp_add_right]

/-- Left translation commutes with `divergence`. -/
@[simp]
theorem divergence_comp_add_left (φ : E → E) (a x : E) :
    divergence (fun y ↦ φ (a + y)) x = divergence φ (a + x) := by
  simp [divergence, fderiv_comp_add_left]

/-- Subtraction of a constant vector commutes with `divergence`. -/
@[simp]
theorem divergence_comp_sub (φ : E → E) (a x : E) :
    divergence (fun y ↦ φ (y - a)) x = divergence φ (x - a) := by
  simp [sub_eq_add_neg]

section Translation

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- **Right-translation invariance of variational total variation** on a localized open set `Ω`. -/
theorem distributionalVariation_comp_add_right [μ.IsAddRightInvariant] (Ω : Opens E) (u : E → ℝ)
    (a : E) :
    distributionalVariation μ (Ω.comap ⟨(· + a), by fun_prop⟩) (fun x ↦ u (x + a)) =
      distributionalVariation μ Ω u := by
  have hle : ∀ (V : Opens E) (v : E → ℝ) (b : E),
      distributionalVariation μ V v ≤
        distributionalVariation μ (V.comap ⟨(· + b), by fun_prop⟩) (fun x ↦ v (x + b)) := by
    intro V v b
    refine iSup₂_le fun φ hφ ↦ ?_
    let ψ : 𝓓(V.comap ⟨(· + b), by fun_prop⟩, E) :=
      compHomeomorph (Homeomorph.addRight b) (contDiff_id.add contDiff_const) φ
    have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ hφ (x + b)
    have hint : ∫ x in (V : Set E), v x * divergence (φ : E → E) x ∂μ =
        ∫ x in (V.comap ⟨(· + b), by fun_prop⟩ : Set E),
          v (x + b) * divergence (ψ : E → E) x ∂μ := by
      rw [setIntegral_mul_divergence_eq_integral, setIntegral_mul_divergence_eq_integral]
      have hdiv : ∀ x, divergence (ψ : E → E) x = divergence (φ : E → E) (x + b) :=
        divergence_comp_add_right (φ : E → E) b
      simp_rw [hdiv]
      exact (integral_add_right_eq_self (fun x ↦ v x * divergence (φ : E → E) x) b).symm
    rw [hint]
    exact le_distributionalVariation ψ hψ_norm (fun x ↦ v (x + b))
  refine le_antisymm ?_ (hle Ω u a)
  have h := hle (Ω.comap ⟨(· + a), by fun_prop⟩) (fun x ↦ u (x + a)) (-a)
  have hΩ : (Ω.comap ⟨(· + a), by fun_prop⟩).comap ⟨(· + -a), by fun_prop⟩ = Ω := by ext x; simp
  have hu : (fun x ↦ u (x + -a + a)) = u := by ext x; simp
  rwa [hΩ, hu] at h

/-- **Right-translation invariance of global variational total variation** on `⊤ : Opens E`. -/
@[simp]
theorem distributionalVariation_top_comp_add_right [μ.IsAddRightInvariant] (u : E → ℝ) (a : E) :
    distributionalVariation μ ⊤ (fun x ↦ u (x + a)) = distributionalVariation μ ⊤ u :=
  distributionalVariation_comp_add_right ⊤ u a

/-- **Left-translation invariance of variational total variation** on a localized open set `Ω`. -/
theorem distributionalVariation_comp_add_left [μ.IsAddLeftInvariant] (Ω : Opens E) (u : E → ℝ)
    (a : E) :
    distributionalVariation μ (Ω.comap ⟨(a + ·), by fun_prop⟩) (fun x ↦ u (a + x)) =
      distributionalVariation μ Ω u := by
  have hle : ∀ (V : Opens E) (v : E → ℝ) (b : E),
      distributionalVariation μ V v ≤
        distributionalVariation μ (V.comap ⟨(b + ·), by fun_prop⟩) (fun x ↦ v (b + x)) := by
    intro V v b
    refine iSup₂_le fun φ hφ ↦ ?_
    let ψ : 𝓓(V.comap ⟨(b + ·), by fun_prop⟩, E) :=
      compHomeomorph (Homeomorph.addLeft b) (contDiff_const.add contDiff_id) φ
    have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ hφ (b + x)
    have hint : ∫ x in (V : Set E), v x * divergence (φ : E → E) x ∂μ =
        ∫ x in (V.comap ⟨(b + ·), by fun_prop⟩ : Set E),
          v (b + x) * divergence (ψ : E → E) x ∂μ := by
      rw [setIntegral_mul_divergence_eq_integral, setIntegral_mul_divergence_eq_integral]
      have hdiv : ∀ x, divergence (ψ : E → E) x = divergence (φ : E → E) (b + x) :=
        divergence_comp_add_left (φ : E → E) b
      simp_rw [hdiv]
      exact (integral_add_left_eq_self (fun x ↦ v x * divergence (φ : E → E) x) b).symm
    rw [hint]
    exact le_distributionalVariation ψ hψ_norm (fun x ↦ v (b + x))
  refine le_antisymm ?_ (hle Ω u a)
  have h := hle (Ω.comap ⟨(a + ·), by fun_prop⟩) (fun x ↦ u (a + x)) (-a)
  have hΩ : (Ω.comap ⟨(a + ·), by fun_prop⟩).comap ⟨(-a + ·), by fun_prop⟩ = Ω := by ext x; simp
  have hu : (fun x ↦ u (a + (-a + x))) = u := by ext x; simp
  rwa [hΩ, hu] at h

/-- **Left-translation invariance of global variational total variation** on `⊤ : Opens E`. -/
@[simp]
theorem distributionalVariation_top_comp_add_left [μ.IsAddLeftInvariant] (u : E → ℝ) (a : E) :
    distributionalVariation μ ⊤ (fun x ↦ u (a + x)) = distributionalVariation μ ⊤ u :=
  distributionalVariation_comp_add_left ⊤ u a

/-- **Subtraction invariance of variational total variation** on a localized open set `Ω`. -/
theorem distributionalVariation_comp_sub [μ.IsAddRightInvariant] (Ω : Opens E) (u : E → ℝ)
    (a : E) :
    distributionalVariation μ (Ω.comap ⟨(· - a), by fun_prop⟩) (fun x ↦ u (x - a)) =
      distributionalVariation μ Ω u := by
  simpa [sub_eq_add_neg] using distributionalVariation_comp_add_right Ω u (-a)

/-- **Subtraction invariance of global variational total variation** on `⊤ : Opens E`. -/
@[simp]
theorem distributionalVariation_top_comp_sub [μ.IsAddRightInvariant] (u : E → ℝ) (a : E) :
    distributionalVariation μ ⊤ (fun x ↦ u (x - a)) = distributionalVariation μ ⊤ u :=
  distributionalVariation_comp_sub ⊤ u a

/-- **Right-translation preimage invariance of relative perimeter**. -/
theorem relativePerimeter_preimage_add_right [μ.IsAddRightInvariant] (Ω : Opens E) (s : Set E)
    (a : E) :
    relativePerimeter μ (Ω.comap ⟨(· + a), by fun_prop⟩) ((· + a) ⁻¹' s) =
      relativePerimeter μ Ω s := by
  unfold relativePerimeter
  have hind : (((· + a) ⁻¹' s).indicator fun _ : E ↦ (1 : ℝ)) =
      fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) (x + a) := by
    ext x; by_cases hx : x + a ∈ s <;> simp [hx]
  rw [hind, distributionalVariation_comp_add_right]

/-- **Left-translation preimage invariance of relative perimeter**. -/
theorem relativePerimeter_preimage_add_left [μ.IsAddLeftInvariant] (Ω : Opens E) (s : Set E)
    (a : E) :
    relativePerimeter μ (Ω.comap ⟨(a + ·), by fun_prop⟩) ((a + ·) ⁻¹' s) =
      relativePerimeter μ Ω s := by
  unfold relativePerimeter
  have hind : (((a + ·) ⁻¹' s).indicator fun _ : E ↦ (1 : ℝ)) =
      fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) (a + x) := by
    ext x; by_cases hx : a + x ∈ s <;> simp [hx]
  rw [hind, distributionalVariation_comp_add_left]

/-- **Translation invariance of relative perimeter** for `a +ᵥ s`. -/
theorem relativePerimeter_vadd [μ.IsAddLeftInvariant] (Ω : Opens E) (a : E) (s : Set E) :
    relativePerimeter μ (Ω.comap ⟨(-a + ·), by fun_prop⟩) (a +ᵥ s) =
      relativePerimeter μ Ω s := by
  rw [← preimage_vadd_neg]
  exact relativePerimeter_preimage_add_left Ω s (-a)

/-- **Right-translation preimage invariance of whole-space perimeter**. -/
@[simp]
theorem perimeter_preimage_add_right [μ.IsAddRightInvariant] (s : Set E) (a : E) :
    perimeter μ ((· + a) ⁻¹' s) = perimeter μ s :=
  relativePerimeter_preimage_add_right ⊤ s a

/-- **Left-translation preimage invariance of whole-space perimeter**. -/
@[simp]
theorem perimeter_preimage_add_left [μ.IsAddLeftInvariant] (s : Set E) (a : E) :
    perimeter μ ((a + ·) ⁻¹' s) = perimeter μ s :=
  relativePerimeter_preimage_add_left ⊤ s a

/-- **Translation invariance of whole-space perimeter**: `P(a +ᵥ s) = P(s)`. -/
@[simp]
theorem perimeter_vadd [μ.IsAddLeftInvariant] (a : E) (s : Set E) :
    perimeter μ (a +ᵥ s) = perimeter μ s :=
  relativePerimeter_vadd ⊤ a s

/-- `HasFinitePerimeter` is preserved under right-translation preimages. -/
theorem HasFinitePerimeter.preimage_add_right [μ.IsAddRightInvariant] {s : Set E}
    (hs : HasFinitePerimeter μ s) (a : E) :
    HasFinitePerimeter μ ((· + a) ⁻¹' s) := by
  refine ⟨?_, ?_⟩
  · rw [Opens.coe_top, Measure.restrict_univ]
    have h0 : NullMeasurableSet s μ := by simpa [Opens.coe_top] using hs.1
    exact h0.preimage (measurePreserving_add_right μ a).quasiMeasurePreserving
  · change perimeter μ ((· + a) ⁻¹' s) < ⊤
    rw [perimeter_preimage_add_right]; exact hs.2

/-- `(· + a) ⁻¹' s` has finite perimeter if and only if `s` has finite perimeter. -/
@[simp]
theorem HasFinitePerimeter.preimage_add_right_iff [μ.IsAddRightInvariant] {s : Set E} (a : E) :
    HasFinitePerimeter μ ((· + a) ⁻¹' s) ↔ HasFinitePerimeter μ s :=
  ⟨fun h ↦ by convert h.preimage_add_right (-a); ext x; simp, fun h ↦ h.preimage_add_right a⟩

/-- `HasFinitePerimeter` is preserved under left-translation preimages. -/
theorem HasFinitePerimeter.preimage_add_left [μ.IsAddLeftInvariant] {s : Set E}
    (hs : HasFinitePerimeter μ s) (a : E) :
    HasFinitePerimeter μ ((a + ·) ⁻¹' s) := by
  refine ⟨?_, ?_⟩
  · rw [Opens.coe_top, Measure.restrict_univ]
    have h0 : NullMeasurableSet s μ := by simpa [Opens.coe_top] using hs.1
    exact h0.preimage (measurePreserving_add_left μ a).quasiMeasurePreserving
  · change perimeter μ ((a + ·) ⁻¹' s) < ⊤
    rw [perimeter_preimage_add_left]; exact hs.2

/-- `(a + ·) ⁻¹' s` has finite perimeter if and only if `s` has finite perimeter. -/
@[simp]
theorem HasFinitePerimeter.preimage_add_left_iff [μ.IsAddLeftInvariant] {s : Set E} (a : E) :
    HasFinitePerimeter μ ((a + ·) ⁻¹' s) ↔ HasFinitePerimeter μ s :=
  ⟨fun h ↦ by convert h.preimage_add_left (-a); ext x; simp, fun h ↦ h.preimage_add_left a⟩

/-- `HasFinitePerimeter` is preserved under pointwise translation `a +ᵥ s`. -/
theorem HasFinitePerimeter.vadd [μ.IsAddLeftInvariant] {s : Set E}
    (hs : HasFinitePerimeter μ s) (a : E) :
    HasFinitePerimeter μ (a +ᵥ s) := by
  rw [← preimage_vadd_neg]; exact hs.preimage_add_left (-a)

/-- `a +ᵥ s` has finite perimeter if and only if `s` has finite perimeter. -/
@[simp]
theorem HasFinitePerimeter.vadd_iff [μ.IsAddLeftInvariant] {s : Set E} (a : E) :
    HasFinitePerimeter μ (a +ᵥ s) ↔ HasFinitePerimeter μ s :=
  ⟨fun h ↦ by simpa using h.vadd (-a), fun h ↦ h.vadd a⟩

end Translation

/-! ### Homogeneous dilation scaling of divergence, variational total variation, and perimeter -/

/-- Precomposing a vector field `φ` with scalar multiplication by `r : ℝ` scales its divergence by
`r`: `divergence (fun y ↦ φ (r • y)) x = r * divergence φ (r • x)`. -/
@[simp]
theorem divergence_comp_smul (φ : E → E) (r : ℝ) (x : E) :
    divergence (fun y ↦ φ (r • y)) x = r * divergence φ (r • x) := by
  simp [divergence, fderiv_comp_smul]

section DilationScaling

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

private lemma distributionalVariation_comp_inv_smul_le (Ω : Opens E) (u : E → ℝ) {r : ℝ}
    (hr : 0 < r) :
    ENNReal.ofReal (r ^ Module.finrank ℝ E / r) * distributionalVariation μ Ω u ≤
      distributionalVariation μ (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩) (fun x ↦ u (r⁻¹ • x)) := by
  rw [distributionalVariation, ENNReal.mul_iSup]
  refine iSup_le fun φ ↦ ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hφ ↦ ?_
  let ψ : 𝓓(Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩, E) :=
    compHomeomorph (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))
      (contDiff_const.smul contDiff_id) φ
  have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ hφ (r⁻¹ • x)
  have hpos : 0 ≤ r ^ Module.finrank ℝ E / r := div_nonneg (pow_nonneg hr.le _) hr.le
  rw [← ENNReal.ofReal_mul hpos]
  have hint : (r ^ Module.finrank ℝ E / r) *
        ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩ : Set E),
        u (r⁻¹ • x) * divergence (ψ : E → E) x ∂μ := by
    rw [setIntegral_mul_divergence_eq_integral, setIntegral_mul_divergence_eq_integral]
    have hdiv : ∀ x, u (r⁻¹ • x) * divergence (ψ : E → E) x =
        r⁻¹ * (u (r⁻¹ • x) * divergence (φ : E → E) (r⁻¹ • x)) := fun x ↦ by
      change u (r⁻¹ • x) * divergence (fun y ↦ (φ : E → E) (r⁻¹ • y)) x = _
      rw [divergence_comp_smul]; ring
    simp_rw [hdiv, integral_const_mul]
    rw [μ.integral_comp_inv_smul_of_nonneg (fun x ↦ u x * divergence (φ : E → E) x) hr.le]
    simp [smul_eq_mul, div_eq_inv_mul, mul_assoc]
  rw [hint]
  exact le_distributionalVariation ψ hψ_norm (fun x ↦ u (r⁻¹ • x))

/-- **Homogeneous dilation scaling of variational total variation**: for `0 < r`,
`distributionalVariation μ (Ω.comap ⟨(r⁻¹ • ·), _⟩) (fun x ↦ u (r⁻¹ • x)) =
  ENNReal.ofReal (r ^ Module.finrank ℝ E / r) * distributionalVariation μ Ω u`. -/
theorem distributionalVariation_comp_inv_smul (Ω : Opens E) (u : E → ℝ) {r : ℝ} (hr : 0 < r) :
    distributionalVariation μ (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩) (fun x ↦ u (r⁻¹ • x)) =
      ENNReal.ofReal (r ^ Module.finrank ℝ E / r) * distributionalVariation μ Ω u := by
  refine le_antisymm ?_ (distributionalVariation_comp_inv_smul_le Ω u hr)
  have h := distributionalVariation_comp_inv_smul_le (μ := μ)
    (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩) (fun x ↦ u (r⁻¹ • x)) (inv_pos.2 hr)
  have hΩ : (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩).comap ⟨(r⁻¹⁻¹ • ·), by fun_prop⟩ = Ω := by
    ext x; simp [inv_inv, smul_smul, inv_mul_cancel₀ hr.ne']
  have hu : (fun x ↦ u (r⁻¹ • r⁻¹⁻¹ • x)) = u := by
    ext x; simp [inv_inv, smul_smul, inv_mul_cancel₀ hr.ne']
  rw [hΩ, hu] at h
  have hmul : ENNReal.ofReal (r ^ Module.finrank ℝ E / r) *
      (ENNReal.ofReal (r⁻¹ ^ Module.finrank ℝ E / r⁻¹) *
        distributionalVariation μ (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩) (fun x ↦ u (r⁻¹ • x))) =
      distributionalVariation μ (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩) (fun x ↦ u (r⁻¹ • x)) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hr.le _) hr.le)]
    have h1 : (r ^ Module.finrank ℝ E / r) * (r⁻¹ ^ Module.finrank ℝ E / r⁻¹) = 1 := by
      rw [inv_pow]
      have hpow : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
      have hr' : r ≠ 0 := hr.ne'
      field_simp
    rw [h1, ENNReal.ofReal_one, one_mul]
  rw [← hmul]; gcongr

/-- **Global homogeneous dilation scaling of variational total variation** on `⊤ : Opens E`. -/
theorem distributionalVariation_top_comp_inv_smul (u : E → ℝ) {r : ℝ} (hr : 0 < r) :
    distributionalVariation μ ⊤ (fun x ↦ u (r⁻¹ • x)) =
      ENNReal.ofReal (r ^ Module.finrank ℝ E / r) * distributionalVariation μ ⊤ u :=
  distributionalVariation_comp_inv_smul ⊤ u hr

omit [MeasurableSpace E] [BorelSpace E] in
/-- On a nontrivial space `E`, `r ^ Module.finrank ℝ E / r = r ^ (Module.finrank ℝ E - 1)`. -/
private lemma pow_finrank_div_self [Nontrivial E] {r : ℝ} (hr : r ≠ 0) :
    r ^ Module.finrank ℝ E / r = r ^ (Module.finrank ℝ E - 1) := by
  have hpos : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  rw [pow_sub₀ r hr hpos, pow_one, div_eq_mul_inv]

/-- **Homogeneous dilation scaling of variational total variation** on a nontrivial space `E` with
exponent `Module.finrank ℝ E - 1`. -/
theorem distributionalVariation_comp_inv_smul_of_nontrivial [Nontrivial E] (Ω : Opens E)
    (u : E → ℝ) {r : ℝ} (hr : 0 < r) :
    distributionalVariation μ (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩) (fun x ↦ u (r⁻¹ • x)) =
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * distributionalVariation μ Ω u := by
  rw [distributionalVariation_comp_inv_smul Ω u hr, pow_finrank_div_self hr.ne']

/-- **Global homogeneous dilation scaling of variational total variation** on a nontrivial space `E`
with exponent `Module.finrank ℝ E - 1`. -/
theorem distributionalVariation_top_comp_inv_smul_of_nontrivial [Nontrivial E] (u : E → ℝ)
    {r : ℝ} (hr : 0 < r) :
    distributionalVariation μ ⊤ (fun x ↦ u (r⁻¹ • x)) =
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * distributionalVariation μ ⊤ u :=
  distributionalVariation_comp_inv_smul_of_nontrivial ⊤ u hr

/-- **Homogeneous scaling of variational total variation under `x ↦ u (r • x)`** for `0 < r`. -/
theorem distributionalVariation_comp_smul (Ω : Opens E) (u : E → ℝ) {r : ℝ} (hr : 0 < r) :
    distributionalVariation μ (Ω.comap ⟨(r • ·), by fun_prop⟩) (fun x ↦ u (r • x)) =
      ENNReal.ofReal (r⁻¹ ^ Module.finrank ℝ E / r⁻¹) * distributionalVariation μ Ω u := by
  simpa [inv_inv] using distributionalVariation_comp_inv_smul (μ := μ) Ω u (inv_pos.2 hr)

/-- **Global homogeneous scaling of variational total variation under `x ↦ u (r • x)`**. -/
theorem distributionalVariation_top_comp_smul (u : E → ℝ) {r : ℝ} (hr : 0 < r) :
    distributionalVariation μ ⊤ (fun x ↦ u (r • x)) =
      ENNReal.ofReal (r⁻¹ ^ Module.finrank ℝ E / r⁻¹) * distributionalVariation μ ⊤ u :=
  distributionalVariation_comp_smul ⊤ u hr

/-- **Homogeneous scaling of relative perimeter** under a positive dilation `r > 0`. -/
theorem relativePerimeter_smul (Ω : Opens E) {r : ℝ} (hr : 0 < r) (s : Set E) :
    relativePerimeter μ (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩) (r • s) =
      ENNReal.ofReal (r ^ Module.finrank ℝ E / r) * relativePerimeter μ Ω s := by
  unfold relativePerimeter
  have hind : ((r • s).indicator fun _ : E ↦ (1 : ℝ)) =
      fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) (r⁻¹ • x) := by
    ext x; by_cases hx : r⁻¹ • x ∈ s <;> simp [hx, mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  rw [hind, distributionalVariation_comp_inv_smul Ω _ hr]

/-- **Homogeneous scaling of relative perimeter** on a nontrivial space `E` with exponent
`Module.finrank ℝ E - 1`. -/
theorem relativePerimeter_smul_of_nontrivial [Nontrivial E] (Ω : Opens E) {r : ℝ} (hr : 0 < r)
    (s : Set E) :
    relativePerimeter μ (Ω.comap ⟨(r⁻¹ • ·), by fun_prop⟩) (r • s) =
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * relativePerimeter μ Ω s := by
  rw [relativePerimeter_smul Ω hr s, pow_finrank_div_self hr.ne']

/-- **Homogeneous scaling of whole-space perimeter**: for `0 < r`,
`perimeter μ (r • s) = ENNReal.ofReal (r ^ Module.finrank ℝ E / r) * perimeter μ s`. -/
theorem perimeter_smul {r : ℝ} (hr : 0 < r) (s : Set E) :
    perimeter μ (r • s) = ENNReal.ofReal (r ^ Module.finrank ℝ E / r) * perimeter μ s :=
  relativePerimeter_smul ⊤ hr s

/-- **Homogeneous scaling of whole-space perimeter on a nontrivial space `E`** (`dim E ≥ 1`): for
`0 < r`, `perimeter μ (r • s) = ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * perimeter μ s`. -/
theorem perimeter_smul_of_nontrivial [Nontrivial E] {r : ℝ} (hr : 0 < r) (s : Set E) :
    perimeter μ (r • s) = ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * perimeter μ s :=
  relativePerimeter_smul_of_nontrivial ⊤ hr s

private lemma quasiMeasurePreserving_smul {r : ℝ} (hr : r ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : E ↦ r • x) μ μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [μ.map_addHaar_smul hr]
  exact Measure.AbsolutelyContinuous.rfl.smul_left _

/-- `HasFinitePerimeter` is preserved under positive dilations `r • s` (`0 < r`). -/
theorem HasFinitePerimeter.smul {s : Set E} (hs : HasFinitePerimeter μ s) {r : ℝ} (hr : 0 < r) :
    HasFinitePerimeter μ (r • s) := by
  refine ⟨?_, ?_⟩
  · have hpre : r • s = (fun x : E ↦ r⁻¹ • x) ⁻¹' s := by
      ext x; simp [mem_smul_set_iff_inv_smul_mem₀ hr.ne']
    rw [Opens.coe_top, Measure.restrict_univ, hpre]
    have h0 : NullMeasurableSet s μ := by simpa [Opens.coe_top] using hs.1
    exact h0.preimage (quasiMeasurePreserving_smul (inv_ne_zero hr.ne'))
  · change perimeter μ (r • s) < ⊤
    rw [perimeter_smul hr s]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.2

/-- For `0 < r`, `r • s` has finite perimeter if and only if `s` has finite perimeter. -/
theorem HasFinitePerimeter.smul_iff {s : Set E} {r : ℝ} (hr : 0 < r) :
    HasFinitePerimeter μ (r • s) ↔ HasFinitePerimeter μ s :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hr.ne'] using h.smul (inv_pos.2 hr),
    fun h ↦ h.smul hr⟩

end DilationScaling

/-! ### Linear isometry transport (`L : E ≃ₗᵢ[ℝ] F`) -/

/-- Conjugating a vector field `φ : E → E` by a linear isometric equivalence `L : E ≃ₗᵢ[ℝ] F`
preserves its divergence: `divergence (fun z ↦ L (φ (L.symm z))) y = divergence φ (L.symm y)`. -/
@[simp]
theorem divergence_conj_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) (φ : E → E) (y : F) :
    divergence (fun z ↦ L (φ (L.symm z))) y = divergence φ (L.symm y) := by
  unfold divergence
  have h1 : (fun z ↦ L (φ (L.symm z))) =
      (L.toContinuousLinearEquiv : E → F) ∘ (φ ∘ L.symm.toContinuousLinearEquiv) := rfl
  rw [h1, L.toContinuousLinearEquiv.comp_fderiv, L.symm.toContinuousLinearEquiv.comp_right_fderiv]
  exact LinearMap.trace_conj' (fderiv ℝ φ (L.symm y)).toLinearMap L.toLinearEquiv

/-- Conjugating a vector field `ψ : F → F` by `L.symm` for `L : E ≃ₗᵢ[ℝ] F` preserves its
divergence: `divergence (fun z ↦ L.symm (ψ (L z))) x = divergence ψ (L x)`. -/
@[simp]
theorem divergence_conj_symm_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) (ψ : F → F) (x : E) :
    divergence (fun z ↦ L.symm (ψ (L z))) x = divergence ψ (L x) :=
  divergence_conj_linearIsometryEquiv L.symm ψ x

section LinearIsometryTransport

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} {ν : Measure F}

private lemma distributionalVariation_comp_linearIsometryEquiv_le_of_measurePreserving
    {L : E ≃ₗᵢ[ℝ] F} (hL : MeasurePreserving L μ ν) (Ω : Opens F) (u : F → ℝ) :
    distributionalVariation ν Ω u ≤
      distributionalVariation μ (Ω.comap ⟨L, L.continuous⟩) (u ∘ L) := by
  refine iSup₂_le fun φ hφ ↦ ?_
  let ψ₀ : 𝓓(Ω.comap ⟨L, L.continuous⟩, F) := compHomeomorph L.toHomeomorph L.contDiff φ
  let ψ : 𝓓(Ω.comap ⟨L, L.continuous⟩, E) :=
    TestFunction.postcompCLM (𝕜 := ℝ) L.symm.toContinuousLinearEquiv.toContinuousLinearMap ψ₀
  have hψ_apply : (ψ : E → E) = fun x ↦ L.symm (φ (L x)) := rfl
  have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
    change ‖L.symm (φ (L x))‖ ≤ 1; rw [L.symm.norm_map]; exact hφ (L x)
  have hint : ∫ y in (Ω : Set F), u y * divergence (φ : F → F) y ∂ν =
      ∫ x in (Ω.comap ⟨L, L.continuous⟩ : Set E),
        (u ∘ L) x * divergence (ψ : E → E) x ∂μ := by
    rw [setIntegral_mul_divergence_eq_integral, setIntegral_mul_divergence_eq_integral, hψ_apply]
    simp_rw [divergence_conj_symm_linearIsometryEquiv L (φ : F → F)]
    exact (hL.integral_comp' (f := L.toHomeomorph.toMeasurableEquiv)
      (fun y ↦ u y * divergence (φ : F → F) y)).symm
  rw [hint]
  exact le_distributionalVariation ψ hψ_norm (u ∘ L)

/-- **Measure-preserving linear isometry transport of variational total variation** on an open set
`Ω : Opens F`. -/
theorem distributionalVariation_comp_linearIsometryEquiv_of_measurePreserving
    {L : E ≃ₗᵢ[ℝ] F} (hL : MeasurePreserving L μ ν) (Ω : Opens F) (u : F → ℝ) :
    distributionalVariation μ (Ω.comap ⟨L, L.continuous⟩) (u ∘ L) =
      distributionalVariation ν Ω u := by
  refine le_antisymm ?_
    (distributionalVariation_comp_linearIsometryEquiv_le_of_measurePreserving hL Ω u)
  have hsymm : MeasurePreserving L.symm ν μ := hL.symm L.toHomeomorph.toMeasurableEquiv
  have h := distributionalVariation_comp_linearIsometryEquiv_le_of_measurePreserving hsymm
    (Ω.comap ⟨L, L.continuous⟩) (u ∘ L)
  have hΩ : (Ω.comap ⟨L, L.continuous⟩).comap ⟨L.symm, L.symm.continuous⟩ = Ω := by ext y; simp
  have hu : (u ∘ L) ∘ L.symm = u := by ext y; simp
  rwa [hΩ, hu] at h

/-- **Measure-preserving linear isometry transport of global variational total variation** on
`⊤ : Opens F`. -/
theorem distributionalVariation_top_comp_linearIsometryEquiv_of_measurePreserving
    {L : E ≃ₗᵢ[ℝ] F} (hL : MeasurePreserving L μ ν) (u : F → ℝ) :
    distributionalVariation μ ⊤ (u ∘ L) = distributionalVariation ν ⊤ u :=
  distributionalVariation_comp_linearIsometryEquiv_of_measurePreserving hL ⊤ u

/-- **Measure-preserving linear isometry preimage invariance of relative perimeter**. -/
theorem relativePerimeter_preimage_linearIsometryEquiv_of_measurePreserving
    {L : E ≃ₗᵢ[ℝ] F} (hL : MeasurePreserving L μ ν) (Ω : Opens F) (s : Set F) :
    relativePerimeter μ (Ω.comap ⟨L, L.continuous⟩) (L ⁻¹' s) =
      relativePerimeter ν Ω s := by
  unfold relativePerimeter
  have hind : ((L ⁻¹' s).indicator fun _ : E ↦ (1 : ℝ)) =
      (s.indicator fun _ : F ↦ (1 : ℝ)) ∘ L := by
    ext x; by_cases hx : L x ∈ s <;> simp [hx]
  rw [hind, distributionalVariation_comp_linearIsometryEquiv_of_measurePreserving hL]

/-- **Measure-preserving linear isometry image invariance of relative perimeter**. -/
theorem relativePerimeter_image_linearIsometryEquiv_of_measurePreserving
    {L : E ≃ₗᵢ[ℝ] F} (hL : MeasurePreserving L μ ν) (Ω : Opens E) (s : Set E) :
    relativePerimeter ν (Ω.comap ⟨L.symm, L.symm.continuous⟩) (L '' s) =
      relativePerimeter μ Ω s := by
  have hsymm : MeasurePreserving L.symm ν μ := hL.symm L.toHomeomorph.toMeasurableEquiv
  have himg : L '' s = L.symm ⁻¹' s := L.toEquiv.image_eq_preimage_symm s
  rw [himg]
  exact relativePerimeter_preimage_linearIsometryEquiv_of_measurePreserving hsymm Ω s

/-- **Measure-preserving linear isometry preimage invariance of whole-space perimeter**. -/
theorem perimeter_preimage_linearIsometryEquiv_of_measurePreserving
    {L : E ≃ₗᵢ[ℝ] F} (hL : MeasurePreserving L μ ν) (s : Set F) :
    perimeter μ (L ⁻¹' s) = perimeter ν s :=
  relativePerimeter_preimage_linearIsometryEquiv_of_measurePreserving hL ⊤ s

/-- **Measure-preserving linear isometry image invariance of whole-space perimeter**. -/
theorem perimeter_image_linearIsometryEquiv_of_measurePreserving
    {L : E ≃ₗᵢ[ℝ] F} (hL : MeasurePreserving L μ ν) (s : Set E) :
    perimeter ν (L '' s) = perimeter μ s :=
  relativePerimeter_image_linearIsometryEquiv_of_measurePreserving hL ⊤ s

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Linear isometry invariance of variational total variation** with respect to `volume` on a
localized open set `Ω : Opens F`. -/
theorem distributionalVariation_comp_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) (Ω : Opens F)
    (u : F → ℝ) :
    distributionalVariation volume (Ω.comap ⟨L, L.continuous⟩) (u ∘ L) =
      distributionalVariation volume Ω u :=
  distributionalVariation_comp_linearIsometryEquiv_of_measurePreserving L.measurePreserving Ω u

/-- **Linear isometry invariance of global variational total variation** with respect to
`volume`. -/
@[simp]
theorem distributionalVariation_top_comp_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) (u : F → ℝ) :
    distributionalVariation volume ⊤ (u ∘ L) = distributionalVariation volume ⊤ u :=
  distributionalVariation_comp_linearIsometryEquiv L ⊤ u

/-- **Linear isometry preimage invariance of relative perimeter** with respect to `volume`. -/
theorem relativePerimeter_preimage_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) (Ω : Opens F) (s : Set F) :
    relativePerimeter volume (Ω.comap ⟨L, L.continuous⟩) (L ⁻¹' s) =
      relativePerimeter volume Ω s :=
  relativePerimeter_preimage_linearIsometryEquiv_of_measurePreserving L.measurePreserving Ω s

/-- **Linear isometry image invariance of relative perimeter** with respect to `volume`. -/
theorem relativePerimeter_image_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) (Ω : Opens E) (s : Set E) :
    relativePerimeter volume (Ω.comap ⟨L.symm, L.symm.continuous⟩) (L '' s) =
      relativePerimeter volume Ω s :=
  relativePerimeter_image_linearIsometryEquiv_of_measurePreserving L.measurePreserving Ω s

/-- **Linear isometry preimage invariance of whole-space perimeter** with respect to `volume`. -/
@[simp]
theorem perimeter_preimage_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) (s : Set F) :
    perimeter volume (L ⁻¹' s) = perimeter volume s :=
  perimeter_preimage_linearIsometryEquiv_of_measurePreserving L.measurePreserving s

/-- **Linear isometry image invariance of whole-space perimeter** with respect to `volume`. -/
@[simp]
theorem perimeter_image_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) (s : Set E) :
    perimeter volume (L '' s) = perimeter volume s :=
  perimeter_image_linearIsometryEquiv_of_measurePreserving L.measurePreserving s

/-- `HasFinitePerimeter` with respect to `volume` is preserved under preimages along a linear
isometric equivalence `L : E ≃ₗᵢ[ℝ] F`. -/
theorem HasFinitePerimeter.preimage_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) {s : Set F}
    (hs : HasFinitePerimeter volume s) :
    HasFinitePerimeter volume (L ⁻¹' s) := by
  refine ⟨?_, ?_⟩
  · rw [Opens.coe_top, Measure.restrict_univ]
    have h0 : NullMeasurableSet s volume := by simpa [Opens.coe_top] using hs.1
    exact h0.preimage L.measurePreserving.quasiMeasurePreserving
  · change perimeter volume (L ⁻¹' s) < ⊤
    rw [perimeter_preimage_linearIsometryEquiv]; exact hs.2

/-- `L ⁻¹' s` has finite perimeter if and only if `s` has finite perimeter. -/
@[simp]
theorem HasFinitePerimeter.preimage_linearIsometryEquiv_iff (L : E ≃ₗᵢ[ℝ] F) {s : Set F} :
    HasFinitePerimeter volume (L ⁻¹' s) ↔ HasFinitePerimeter volume s :=
  ⟨fun h ↦ by convert h.preimage_linearIsometryEquiv L.symm; ext y; simp,
    fun h ↦ h.preimage_linearIsometryEquiv L⟩

/-- `HasFinitePerimeter` with respect to `volume` is preserved under images along a linear
isometric equivalence `L : E ≃ₗᵢ[ℝ] F`. -/
theorem HasFinitePerimeter.image_linearIsometryEquiv (L : E ≃ₗᵢ[ℝ] F) {s : Set E}
    (hs : HasFinitePerimeter volume s) :
    HasFinitePerimeter volume (L '' s) := by
  have himg : L '' s = L.symm ⁻¹' s := L.toEquiv.image_eq_preimage_symm s
  rw [himg]; exact hs.preimage_linearIsometryEquiv L.symm

/-- `L '' s` has finite perimeter if and only if `s` has finite perimeter. -/
@[simp]
theorem HasFinitePerimeter.image_linearIsometryEquiv_iff (L : E ≃ₗᵢ[ℝ] F) {s : Set E} :
    HasFinitePerimeter volume (L '' s) ↔ HasFinitePerimeter volume s := by
  have himg : L '' s = L.symm ⁻¹' s := L.toEquiv.image_eq_preimage_symm s
  rw [himg, HasFinitePerimeter.preimage_linearIsometryEquiv_iff]

end LinearIsometryTransport

/-! ### Cavalieri / layer-cake divergence identity and the scalar BV coarea inequality -/

section CoareaInequality

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

private lemma integrableOn_Ioi_indicator_Iio_const (a c : ℝ) :
    IntegrableOn ((Iio a).indicator fun _ ↦ c) (Ioi (0 : ℝ)) volume := by
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact integrableOn_const (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)

private lemma integral_Ioi_indicator_Iio_const {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    ∫ t in Ioi (0 : ℝ), (Iio a).indicator (fun _ ↦ c) t = a * c := by
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Iio_inter_Ioi, setIntegral_const, Measure.real, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith), sub_zero, smul_eq_mul]

private lemma integral_mul_divergence_eq_integral_superlevel_of_measurable [SFinite μ]
    {u : E → ℝ} (hu_meas : Measurable u) (hu : LocallyIntegrableOn u Ω μ)
    (hu_nonneg : ∀ x, 0 ≤ u x) (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ =
      ∫ t in Ioi (0 : ℝ),
        (∫ x in (Ω : Set E),
          {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let μΩ := μ.restrict (Ω : Set E)
  let S : Set (E × ℝ) := {p : E × ℝ | p.2 < u p.1}
  have hS : MeasurableSet S := measurableSet_lt measurable_snd (hu_meas.comp measurable_fst)
  let F : E × ℝ → ℝ := S.indicator fun p ↦ divergence (φ : E → E) p.1
  have hF_meas : Measurable F :=
    ((continuous_divergence_testFunction φ).measurable.comp measurable_fst).indicator hS
  have hF_slice : ∀ x t, F (x, t) =
      {y | t < u y}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x := by
    intro x t; by_cases h : t < u x <;> simp [F, S, h]
  have hF_slice' : ∀ x t, F (x, t) =
      (Iio (u x)).indicator (fun _ ↦ divergence (φ : E → E) x) t := by
    intro x t; by_cases h : t < u x <;> simp [F, S, h]
  have hF_norm_slice : ∀ x t, ‖F (x, t)‖ =
      (Iio (u x)).indicator (fun _ ↦ ‖divergence (φ : E → E) x‖) t := by
    intro x t; by_cases h : t < u x <;> simp [F, S, h]
  have hF_int : Integrable F (μΩ.prod ν) := by
    rw [integrable_prod_iff hF_meas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x ↦ ?_, ?_⟩
    · simp_rw [hF_slice' x]
      exact integrableOn_Ioi_indicator_Iio_const (u x) (divergence (φ : E → E) x)
    · have hnorm_int : (fun x ↦ ∫ t, ‖F (x, t)‖ ∂ν) =
          fun x ↦ u x * ‖divergence (φ : E → E) x‖ := by
        ext x; simp_rw [hF_norm_slice x]
        exact integral_Ioi_indicator_Iio_const (hu_nonneg x) ‖divergence (φ : E → E) x‖
      rw [hnorm_int]
      have hint := (integrableOn_mul_divergence_of_locallyIntegrableOn hu φ).norm
      simpa [norm_mul, abs_of_nonneg (hu_nonneg _)] using hint
  have h1 := integral_prod F hF_int
  have h2 := integral_prod_symm F hF_int
  have hL : (∫ x, ∫ t, F (x, t) ∂ν ∂μΩ) =
      ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp_rw [hF_slice' x]
    exact integral_Ioi_indicator_Iio_const (hu_nonneg x) (divergence (φ : E → E) x)
  rw [← hL, ← h1, h2]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  exact integral_congr_ae (Eventually.of_forall fun x ↦ hF_slice x t)

/-- **Cavalieri / layer-cake identity against test-vector-field divergence**: for any locally
integrable function `u : E → ℝ` on `Ω` satisfying `∀ x ∈ Ω, 0 ≤ u x` and any test vector field
`φ : 𝓓(Ω, E)`,
`∫ x in Ω, u x * divergence φ x ∂μ =
  ∫ t in Ioi 0, (∫ x in Ω, {x | t < u x}.indicator 1 x * divergence φ x ∂μ)`. -/
theorem integral_mul_divergence_eq_integral_superlevel [SFinite μ] {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hu_nonneg : ∀ x ∈ (Ω : Set E), 0 ≤ u x) (φ : 𝓓(Ω, E)) :
    ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ =
      ∫ t in Ioi (0 : ℝ),
        (∫ x in (Ω : Set E),
          {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ) := by
  have huae : AEStronglyMeasurable u (μ.restrict Ω) := hu.aestronglyMeasurable
  let v : E → ℝ := fun x ↦ max 0 (huae.mk u x)
  have hv_meas : Measurable v := measurable_const.max huae.stronglyMeasurable_mk.measurable
  have hv_nonneg : ∀ x, 0 ≤ v x := fun x ↦ le_max_left 0 _
  have huv : u =ᵐ[μ.restrict Ω] v := by
    filter_upwards [huae.ae_eq_mk, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    simp [v, ← hx, max_eq_right (hu_nonneg x hxΩ)]
  have hv_loc : LocallyIntegrableOn v Ω μ := hu.congr huv
  have hL : ∫ x in (Ω : Set E), u x * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω : Set E), v x * divergence (φ : E → E) x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [huv] with x hx using by rw [hx]
  have hR : ∀ t : ℝ,
      ∫ x in (Ω : Set E),
        {x | t < u x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω : Set E),
        {x | t < v x}.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ := fun t ↦ by
    refine integral_congr_ae ?_
    filter_upwards [huv] with x hx
    by_cases h : t < u x
    · have hv : t < v x := hx ▸ h; simp [h, hv]
    · have hv : ¬ t < v x := hx ▸ h; simp [h, hv]
  rw [hL, integral_mul_divergence_eq_integral_superlevel_of_measurable hv_meas hv_loc hv_nonneg φ]
  simp_rw [hR]

/-- **Scalar BV coarea inequality on an open set `Ω`**: for any locally integrable nonnegative
function `u : E → ℝ` on `Ω`,
`distributionalVariation μ Ω u ≤ ∫⁻ t in Ioi 0, relativePerimeter μ Ω {x | t < u x}`. -/
theorem distributionalVariation_le_lintegral_relativePerimeter_superlevel [SFinite μ] {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hu_nonneg : ∀ x ∈ (Ω : Set E), 0 ≤ u x) :
    distributionalVariation μ Ω u ≤
      ∫⁻ t in Ioi (0 : ℝ), relativePerimeter μ Ω {x | t < u x} := by
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [integral_mul_divergence_eq_integral_superlevel hu hu_nonneg φ]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t ↦ ?_)
  rw [Real.enorm_eq_ofReal_abs]
  exact abs_le_distributionalVariation φ hφ ({x | t < u x}.indicator fun _ ↦ (1 : ℝ))

/-- **Global scalar BV coarea inequality**: for any locally integrable nonnegative function
`u : E → ℝ`,
`distributionalVariation μ ⊤ u ≤ ∫⁻ t in Ioi 0, perimeter μ {x | t < u x}`. -/
theorem distributionalVariation_top_le_lintegral_perimeter_superlevel [SFinite μ] {u : E → ℝ}
    (hu : LocallyIntegrable u μ) (hu_nonneg : ∀ x, 0 ≤ u x) :
    distributionalVariation μ ⊤ u ≤
      ∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | t < u x} :=
  distributionalVariation_le_lintegral_relativePerimeter_superlevel
    (hu.locallyIntegrableOn (⊤ : Opens E)) (fun x _ ↦ hu_nonneg x)

/-- If a nonnegative integrable function `u` on `Ω` has a finite superlevel-perimeter integral
`∫⁻ t in Ioi 0, relativePerimeter μ Ω {x | t < u x} < ⊤`, then `u` has bounded variation on `Ω`
(`IsBVOn μ Ω u`). -/
theorem isBVOn_of_lintegral_relativePerimeter_superlevel_lt_top [SFinite μ] {u : E → ℝ}
    (hu : IntegrableOn u Ω μ) (hu_nonneg : ∀ x ∈ (Ω : Set E), 0 ≤ u x)
    (hper : ∫⁻ t in Ioi (0 : ℝ), relativePerimeter μ Ω {x | t < u x} < ⊤) :
    IsBVOn μ Ω u :=
  ⟨hu, (distributionalVariation_le_lintegral_relativePerimeter_superlevel
    hu.locallyIntegrableOn hu_nonneg).trans_lt hper⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Every superlevel set `{x | t < u x}` of a `μ.restrict Ω`-null-measurable function `u : E → ℝ`
is `μ.restrict Ω`-null-measurable. -/
theorem nullMeasurableSet_superlevel {u : E → ℝ} (hu : NullMeasurable u (μ.restrict Ω))
    (t : ℝ) : NullMeasurableSet {x | t < u x} (μ.restrict Ω) :=
  hu measurableSet_Ioi

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If `u` is `μ.restrict Ω`-null-measurable and `t ↦ relativePerimeter μ Ω {x | t < u x}` has
finite Lebesgue integral on `(0, ∞)`, then for almost every `t > 0` the superlevel set
`{x | t < u x}` has finite perimeter in `Ω` (`HasFinitePerimeterIn μ Ω {x | t < u x}`). -/
theorem ae_hasFinitePerimeterIn_superlevel {u : E → ℝ} (hu : NullMeasurable u (μ.restrict Ω))
    (hmeas : AEMeasurable (fun t ↦ relativePerimeter μ Ω {x | t < u x})
      (volume.restrict (Ioi (0 : ℝ))))
    (hper : ∫⁻ t in Ioi (0 : ℝ), relativePerimeter μ Ω {x | t < u x} < ⊤) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), HasFinitePerimeterIn μ Ω {x | t < u x} := by
  filter_upwards [ae_lt_top' hmeas hper.ne] with t ht using ⟨nullMeasurableSet_superlevel hu t, ht⟩

end CoareaInequality

end TauCeti
