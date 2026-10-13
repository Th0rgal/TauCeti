/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski

/-!
# Higher-dimensional Prékopa–Leindler and Brunn–Minkowski inequalities

This file establishes the **Prékopa–Leindler inequality** and the **Brunn–Minkowski inequality** in
every finite dimension.

Starting from the one-dimensional Prékopa–Leindler inequality (`Real.lintegral_prekopa_leindler`)
and the zero-dimensional base case (`HasPrekopaLeindler.of_subsingleton`), we prove that the
Prékopa–Leindler property (`MeasureTheory.HasPrekopaLeindler`) is preserved under:
* scalar multiplication of a measure (`HasPrekopaLeindler.smul`),
* pushforward along any measurable `ℝ`-linear map (`HasPrekopaLeindler.map_linearMap`) and any
  measure-preserving linear equivalence or linear isometry equivalence,
* finite products of σ-finite measures via Tonelli's theorem (`HasPrekopaLeindler.prod`).

By induction on the dimension `n` via `MeasurableEquiv.piFinSuccAbove` and uniqueness of additive
Haar measure on finite-dimensional real normed spaces (`isAddLeftInvariant_eq_smul`), it follows
that every additive Haar measure `μ` on any finite-dimensional real normed space `E` satisfies the
Prékopa–Leindler inequality (`HasPrekopaLeindler.of_isAddHaarMeasure`,
`MeasureTheory.lintegral_prekopa_leindler`, and `MeasureTheory.integral_prekopa_leindler`).

From the higher-dimensional Prékopa–Leindler inequality we then derive:
* the **multiplicative (dimension-free) Brunn–Minkowski inequality**
  `μ A ^ (1 - θ) * μ B ^ θ ≤ μ ((1 - θ) • A + θ • B)` for compact, Borel-measurable, and
  `μ`-null-measurable sets `A, B ⊆ E` (without assuming `(1 - θ) • A + θ • B` is measurable),
* the **unweighted additive Brunn–Minkowski inequality** in dimension `n = Module.finrank ℝ E ≥ 1`:
  `μ A ^ (1 / (n : ℝ)) + μ B ^ (1 / (n : ℝ)) ≤ μ (A + B) ^ (1 / (n : ℝ))` for nonempty compact,
  Borel-measurable, and `μ`-null-measurable sets `A, B ⊆ E` (without assuming `A + B` is
  measurable),
* the **weighted additive Brunn–Minkowski inequality** for `0 ≤ θ ≤ 1`:
  `ENNReal.ofReal (1 - θ) * μ A ^ (1 / (n : ℝ)) + ENNReal.ofReal θ * μ B ^ (1 / (n : ℝ)) ≤
  μ ((1 - θ) • A + θ • B) ^ (1 / (n : ℝ))`.

## Main definitions and results

* `MeasureTheory.HasPrekopaLeindler`: predicate stating that a measure `μ` on an `ℝ`-module `E`
  satisfies the Prékopa–Leindler inequality for all `0 < θ < 1` and all measurable functions
  `f, g, h : E → ℝ≥0∞`.
* `MeasureTheory.HasPrekopaLeindler.prod`: Tonelli tensorization of `HasPrekopaLeindler` for
  product measures `μ.prod ν`.
* `MeasureTheory.HasPrekopaLeindler.of_isAddHaarMeasure`: every additive Haar measure `μ` on a
  finite-dimensional real normed space `E` satisfies `HasPrekopaLeindler`.
* `MeasureTheory.lintegral_prekopa_leindler`, `MeasureTheory.lintegral_prekopa_leindler_of_ae_eq`,
  `MeasureTheory.lintegral_ofReal_prekopa_leindler`, and `MeasureTheory.integral_prekopa_leindler`:
  higher-dimensional Prékopa–Leindler inequalities in `ℝ≥0∞` and Bochner `ℝ` forms.
* `MeasureTheory.measure_smul_add_smul_ge_geom_mean` and
  `MeasureTheory.measure_smul_add_smul_ge_geom_mean_of_nullMeasurableSet`: multiplicative
  Brunn–Minkowski inequality in finite-dimensional real normed spaces.
* `MeasureTheory.measure_add_rpow_inv_finrank_ge`,
  `MeasureTheory.measure_add_rpow_inv_finrank_ge_of_nullMeasurableSet`, and
  `EuclideanSpace.volume_add_rpow_inv_ge`: unweighted additive Brunn–Minkowski inequality in all
  dimensions `n ≥ 1`.
* `MeasureTheory.measure_smul_add_smul_rpow_inv_finrank_ge`,
  `MeasureTheory.measure_smul_add_smul_rpow_inv_finrank_ge_of_nullMeasurableSet`, and
  `EuclideanSpace.volume_smul_add_smul_rpow_inv_ge`: weighted additive Brunn–Minkowski inequality
  in all dimensions `n ≥ 1`.

## References

* H. Brunn, *Über Ovale und Eiflächen*, Dissertation, München, 1887.
* H. Minkowski, *Geometrie der Zahlen*, Teubner, Leipzig, 1896.
* A. Prékopa, *Logarithmic concave measures with application to stochastic programming*,
  Acta Sci. Math. (Szeged) **32** (1971), 301–316.
* L. Leindler, *On a certain converse of Hölder's inequality. II*, Acta Sci. Math. (Szeged)
  **33** (1972), 217–223.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. (N.S.) **39** (2002),
  355–405.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Pointwise ENNReal NNReal Topology

private theorem ennreal_rpow_one_sub_mul_rpow_self (c : ℝ≥0∞) {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    c ^ (1 - θ) * c ^ θ = c := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  rcases eq_or_ne c 0 with rfl | hc0
  · simp [h1θ, hθ₀]
  rcases eq_or_ne c ⊤ with rfl | hctop
  · simp [h1θ, hθ₀]
  rw [← ENNReal.rpow_add _ _ hc0 hctop, sub_add_cancel, ENNReal.rpow_one]

private theorem ennreal_iSup_rpow {ι : Sort*} (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, f i ^ p :=
  (ENNReal.orderIsoRpow p hp).map_iSup f

namespace MeasureTheory

/-! ### The `HasPrekopaLeindler` property, tensorization, and linear transport -/

section GeneralModule

variable {E F : Type*} [AddCommMonoid E] [Module ℝ E] [MeasurableSpace E]
  [AddCommMonoid F] [Module ℝ F] [MeasurableSpace F]

/-- A measure `μ` on an `ℝ`-module `E` satisfies the **Prékopa–Leindler property**
(`HasPrekopaLeindler μ`) if for every `0 < θ < 1` and all measurable functions
`f, g, h : E → ℝ≥0∞` satisfying `f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)` for all
`x, y : E`, one has `(∫⁻ x, f x ∂μ) ^ (1 - θ) * (∫⁻ y, g y ∂μ) ^ θ ≤ ∫⁻ z, h z ∂μ`. -/
def HasPrekopaLeindler (μ : Measure E) : Prop :=
  ∀ ⦃θ : ℝ⦄, 0 < θ → θ < 1 → ∀ ⦃f g h : E → ℝ≥0∞⦄,
    Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) →
    (∫⁻ x, f x ∂μ) ^ (1 - θ) * (∫⁻ y, g y ∂μ) ^ θ ≤ ∫⁻ z, h z ∂μ

/-- Applying `HasPrekopaLeindler μ` directly to measurable functions `f, g, h : E → ℝ≥0∞`. -/
theorem HasPrekopaLeindler.lintegral_prekopa_leindler {μ : Measure E} (hμ : HasPrekopaLeindler μ)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) {f g h : E → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫⁻ x, f x ∂μ) ^ (1 - θ) * (∫⁻ y, g y ∂μ) ^ θ ≤ ∫⁻ z, h z ∂μ :=
  hμ hθ₀ hθ₁ hf hg hh hle

/-- **Prékopa–Leindler inequality via measurable representatives**: if `f =ᵐ[μ] f₀`, `g =ᵐ[μ] g₀`,
and `h =ᵐ[μ] h₀` where `f₀, g₀, h₀ : E → ℝ≥0∞` are measurable and satisfy
`f₀ x ^ (1 - θ) * g₀ y ^ θ ≤ h₀ ((1 - θ) • x + θ • y)` for all `x, y : E`, then
`(∫⁻ x, f x ∂μ) ^ (1 - θ) * (∫⁻ y, g y ∂μ) ^ θ ≤ ∫⁻ z, h z ∂μ`. -/
theorem HasPrekopaLeindler.lintegral_prekopa_leindler_of_ae_eq {μ : Measure E}
    (hμ : HasPrekopaLeindler μ) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h f₀ g₀ h₀ : E → ℝ≥0∞}
    (hf : f =ᵐ[μ] f₀) (hg : g =ᵐ[μ] g₀) (hh : h =ᵐ[μ] h₀)
    (hf₀ : Measurable f₀) (hg₀ : Measurable g₀) (hh₀ : Measurable h₀)
    (hle : ∀ x y, f₀ x ^ (1 - θ) * g₀ y ^ θ ≤ h₀ ((1 - θ) • x + θ • y)) :
    (∫⁻ x, f x ∂μ) ^ (1 - θ) * (∫⁻ y, g y ∂μ) ^ θ ≤ ∫⁻ z, h z ∂μ := by
  rw [lintegral_congr_ae hf, lintegral_congr_ae hg, lintegral_congr_ae hh]
  exact hμ hθ₀ hθ₁ hf₀ hg₀ hh₀ hle

/-- **Prékopa–Leindler inequality for real-valued nonnegative functions via `ENNReal.ofReal`** under
`HasPrekopaLeindler μ`. -/
theorem HasPrekopaLeindler.lintegral_ofReal_prekopa_leindler {μ : Measure E}
    (hμ : HasPrekopaLeindler μ) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : E → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ y, 0 ≤ g y)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ^ (1 - θ) * (∫⁻ y, ENNReal.ofReal (g y) ∂μ) ^ θ ≤
      ∫⁻ z, ENNReal.ofReal (h z) ∂μ := by
  refine hμ hθ₀ hθ₁ hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal fun x y ↦ ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (hf_nn x) (sub_pos.2 hθ₁).le,
    ENNReal.ofReal_rpow_of_nonneg (hg_nn y) hθ₀.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf_nn x) _)]
  exact ENNReal.ofReal_le_ofReal (hle x y)

/-- **Prékopa–Leindler inequality for Bochner-integrable nonnegative real-valued functions** under
`HasPrekopaLeindler μ`. -/
theorem HasPrekopaLeindler.integral_prekopa_leindler {μ : Measure E}
    (hμ : HasPrekopaLeindler μ) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : E → ℝ} (hf_m : Measurable f) (hg_m : Measurable g) (hh_m : Measurable h)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ y, 0 ≤ g y)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫ x, f x ∂μ) ^ (1 - θ) * (∫ y, g y ∂μ) ^ θ ≤ ∫ z, h z ∂μ := by
  have h1θ : 0 ≤ 1 - θ := (sub_pos.2 hθ₁).le
  have hh_nn (z : E) : 0 ≤ h z := by
    have hz : (1 - θ) • z + θ • z = z := by rw [← add_smul, sub_add_cancel, one_smul]
    rw [← hz]
    exact (mul_nonneg (Real.rpow_nonneg (hf_nn z) _) (Real.rpow_nonneg (hg_nn z) _)).trans
      (hle z z)
  have hf_int : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hf_nn
  have hg_int : 0 ≤ ∫ y, g y ∂μ := integral_nonneg hg_nn
  have hh_int : 0 ≤ ∫ z, h z ∂μ := integral_nonneg hh_nn
  have h_enn := hμ.lintegral_ofReal_prekopa_leindler hθ₀ hθ₁ hf_m hg_m hh_m hf_nn hg_nn hle
  rw [← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf_nn),
    ← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg_nn),
    ← ofReal_integral_eq_lintegral_ofReal hh (Eventually.of_forall hh_nn),
    ENNReal.ofReal_rpow_of_nonneg hf_int h1θ,
    ENNReal.ofReal_rpow_of_nonneg hg_int hθ₀.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hf_int _)] at h_enn
  exact (ENNReal.ofReal_le_ofReal_iff hh_int).1 h_enn

/-- **Prékopa–Leindler inequality for Bochner-integrable functions via measurable representatives**
under `HasPrekopaLeindler μ`. -/
theorem HasPrekopaLeindler.integral_prekopa_leindler_of_ae_eq {μ : Measure E}
    (hμ : HasPrekopaLeindler μ) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h f₀ g₀ h₀ : E → ℝ}
    (hf_ae : f =ᵐ[μ] f₀) (hg_ae : g =ᵐ[μ] g₀) (hh_ae : h =ᵐ[μ] h₀)
    (hf₀_m : Measurable f₀) (hg₀_m : Measurable g₀) (hh₀_m : Measurable h₀)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hf₀_nn : ∀ x, 0 ≤ f₀ x) (hg₀_nn : ∀ y, 0 ≤ g₀ y)
    (hle : ∀ x y, f₀ x ^ (1 - θ) * g₀ y ^ θ ≤ h₀ ((1 - θ) • x + θ • y)) :
    (∫ x, f x ∂μ) ^ (1 - θ) * (∫ y, g y ∂μ) ^ θ ≤ ∫ z, h z ∂μ := by
  rw [integral_congr_ae hf_ae, integral_congr_ae hg_ae, integral_congr_ae hh_ae]
  exact hμ.integral_prekopa_leindler hθ₀ hθ₁ hf₀_m hg₀_m hh₀_m
    (hf.congr hf_ae) (hg.congr hg_ae) (hh.congr hh_ae) hf₀_nn hg₀_nn hle

/-- The zero measure on `E` satisfies `HasPrekopaLeindler`. -/
theorem HasPrekopaLeindler.zero : HasPrekopaLeindler (0 : Measure E) := by
  intro θ hθ₀ hθ₁ f g h _ _ _ _
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  simp [h1θ, hθ₀]

/-- **Zero-dimensional base case**: every measure `μ` on a subsingleton `ℝ`-module `E` satisfies
`HasPrekopaLeindler`. -/
theorem HasPrekopaLeindler.of_subsingleton [Subsingleton E] (μ : Measure E) :
    HasPrekopaLeindler μ := by
  intro θ hθ₀ hθ₁ f g h _ _ _ hle
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  have h_const (u : E → ℝ≥0∞) : ∫⁻ x, u x ∂μ = u 0 * μ Set.univ := by
    have hu : u = fun _ ↦ u 0 := funext fun x ↦ congrArg u (Subsingleton.elim x 0)
    rw [hu, lintegral_const]
  rw [h_const f, h_const g, h_const h, ENNReal.mul_rpow_of_nonneg _ _ h1θ.le,
    ENNReal.mul_rpow_of_nonneg _ _ hθ₀.le, mul_mul_mul_comm,
    ennreal_rpow_one_sub_mul_rpow_self (μ Set.univ) hθ₀ hθ₁]
  refine mul_le_mul' ?_ le_rfl
  simpa [Subsingleton.elim ((1 - θ) • (0 : E) + θ • (0 : E)) 0] using hle 0 0

/-- Scaling a measure `μ` by any constant `c : ℝ≥0∞` preserves `HasPrekopaLeindler`. -/
theorem HasPrekopaLeindler.smul {μ : Measure E} (hμ : HasPrekopaLeindler μ) (c : ℝ≥0∞) :
    HasPrekopaLeindler (c • μ) := by
  intro θ hθ₀ hθ₁ f g h hf hg hh hle
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ.le, ENNReal.mul_rpow_of_nonneg _ _ hθ₀.le,
    mul_mul_mul_comm, ennreal_rpow_one_sub_mul_rpow_self c hθ₀ hθ₁]
  exact mul_le_mul' le_rfl (hμ hθ₀ hθ₁ hf hg hh hle)

/-- Pushing forward a measure satisfying `HasPrekopaLeindler` along a measurable `ℝ`-linear map
`L : E →ₗ[ℝ] F` preserves `HasPrekopaLeindler`. -/
theorem HasPrekopaLeindler.map_linearMap {μ : Measure E} (hμ : HasPrekopaLeindler μ)
    (L : E →ₗ[ℝ] F) (hL : Measurable L) :
    HasPrekopaLeindler (Measure.map L μ) := by
  intro θ hθ₀ hθ₁ f g h hf hg hh hle
  rw [lintegral_map hf hL, lintegral_map hg hL, lintegral_map hh hL]
  refine hμ hθ₀ hθ₁ (hf.comp hL) (hg.comp hL) (hh.comp hL) fun x y ↦ ?_
  simpa [map_add, map_smul] using hle (L x) (L y)

/-- **Measure-preserving linear transport**: if `L : E →ₗ[ℝ] F` is measure-preserving from `(E, μ)`
to `(F, ν)` and `HasPrekopaLeindler μ`, then `HasPrekopaLeindler ν`. -/
theorem HasPrekopaLeindler.of_measurePreserving {μ : Measure E} {ν : Measure F}
    (hμ : HasPrekopaLeindler μ) (L : E →ₗ[ℝ] F) (hpres : MeasurePreserving L μ ν) :
    HasPrekopaLeindler ν :=
  hpres.map_eq ▸ hμ.map_linearMap L hpres.measurable

/-- **Continuous linear equivalence transport**: if `e : E ≃L[ℝ] F` is measure-preserving from
`(E, μ)` to `(F, ν)` and `HasPrekopaLeindler μ`, then `HasPrekopaLeindler ν`. -/
theorem HasPrekopaLeindler.of_measurePreserving_continuousLinearEquiv
    [TopologicalSpace E] [TopologicalSpace F] {μ : Measure E} {ν : Measure F}
    (hμ : HasPrekopaLeindler μ) (e : E ≃L[ℝ] F) (hpres : MeasurePreserving e μ ν) :
    HasPrekopaLeindler ν :=
  hμ.of_measurePreserving e.toLinearMap hpres

/-- **Linear isometry equivalence transport**: if `e : E ≃ₗᵢ[ℝ] F` is measure-preserving from
`(E, μ)` to `(F, ν)` and `HasPrekopaLeindler μ`, then `HasPrekopaLeindler ν`. -/
theorem HasPrekopaLeindler.of_measurePreserving_linearIsometryEquiv
    {E' F' : Type*} [SeminormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E']
    [SeminormedAddCommGroup F'] [NormedSpace ℝ F'] [MeasurableSpace F']
    {μ : Measure E'} {ν : Measure F'} (hμ : HasPrekopaLeindler μ) (e : E' ≃ₗᵢ[ℝ] F')
    (hpres : MeasurePreserving e μ ν) :
    HasPrekopaLeindler ν :=
  hμ.of_measurePreserving e.toLinearEquiv.toLinearMap hpres

/-- **Product / Tonelli tensorization of Prékopa–Leindler**: if `(E, μ)` and `(F, ν)` satisfy
`HasPrekopaLeindler` and `ν` is s-finite, then `(E × F, μ.prod ν)` satisfies
`HasPrekopaLeindler`. -/
theorem HasPrekopaLeindler.prod {μ : Measure E} {ν : Measure F} [SFinite ν]
    (hμ : HasPrekopaLeindler μ) (hν : HasPrekopaLeindler ν) :
    HasPrekopaLeindler (μ.prod ν) := by
  intro θ hθ₀ hθ₁ f g h hf hg hh hle
  rw [lintegral_prod f hf.aemeasurable, lintegral_prod g hg.aemeasurable,
    lintegral_prod h hh.aemeasurable]
  have hF : Measurable fun x ↦ ∫⁻ y, f (x, y) ∂ν := hf.lintegral_prod_right'
  have hG : Measurable fun x ↦ ∫⁻ y, g (x, y) ∂ν := hg.lintegral_prod_right'
  have hH : Measurable fun x ↦ ∫⁻ y, h (x, y) ∂ν := hh.lintegral_prod_right'
  refine hμ hθ₀ hθ₁ hF hG hH fun x₁ x₂ ↦ ?_
  refine hν hθ₀ hθ₁ (hf.comp (measurable_const.prodMk measurable_id))
    (hg.comp (measurable_const.prodMk measurable_id))
    (hh.comp (measurable_const.prodMk measurable_id)) fun y₁ y₂ ↦ ?_
  exact hle (x₁, y₁) (x₂, y₂)

/-- **Prékopa–Leindler inequality on a product space `E × F`**: if `HasPrekopaLeindler μ`,
`HasPrekopaLeindler ν`, and `[SFinite ν]`, then `μ.prod ν` satisfies the Prékopa–Leindler
inequality. -/
theorem lintegral_prekopa_leindler_prod {μ : Measure E} {ν : Measure F} [SFinite ν]
    (hμ : HasPrekopaLeindler μ) (hν : HasPrekopaLeindler ν) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : E × F → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫⁻ x, f x ∂μ.prod ν) ^ (1 - θ) * (∫⁻ y, g y ∂μ.prod ν) ^ θ ≤ ∫⁻ z, h z ∂μ.prod ν :=
  (hμ.prod hν) hθ₀ hθ₁ hf hg hh hle

end GeneralModule

/-! ### Induction on dimension and additive Haar measures on finite-dimensional spaces -/

/-- **One-dimensional base case**: Lebesgue measure `volume` on `ℝ` satisfies
`HasPrekopaLeindler`. -/
theorem HasPrekopaLeindler.real_volume : HasPrekopaLeindler (volume : Measure ℝ) := by
  intro θ hθ₀ hθ₁ f g h hf hg hh hle
  exact Real.lintegral_prekopa_leindler hθ₀ hθ₁ hf.aemeasurable hg.aemeasurable hh.aemeasurable hle

/-- **Induction on dimension**: for every `n : ℕ`, Lebesgue measure `volume` on `Fin n → ℝ`
satisfies `HasPrekopaLeindler`. -/
theorem HasPrekopaLeindler.pi_fin_real : ∀ n : ℕ, HasPrekopaLeindler (volume : Measure (Fin n → ℝ))
  | 0 => HasPrekopaLeindler.of_subsingleton volume
  | n + 1 => by
    have hprod : HasPrekopaLeindler ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      HasPrekopaLeindler.real_volume.prod (HasPrekopaLeindler.pi_fin_real n)
    have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
    let L : (ℝ × (Fin n → ℝ)) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
      { toFun := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
        map_add' := fun x y ↦ by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp [MeasurableEquiv.piFinSuccAbove]
        map_smul' := fun c x ↦ by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp [MeasurableEquiv.piFinSuccAbove] }
    exact hprod.of_measurePreserving L hpres

/-- **All-dimensional Prékopa–Leindler theorem for additive Haar measures**: every additive Haar
measure `μ` on a finite-dimensional real normed space `E` satisfies `HasPrekopaLeindler`. -/
theorem HasPrekopaLeindler.of_isAddHaarMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] :
    HasPrekopaLeindler μ := by
  set n := Module.finrank ℝ E
  let e : (Fin n → ℝ) ≃L[ℝ] E :=
    (LinearEquiv.ofFinrankEq (Fin n → ℝ) E (by simp [n])).toContinuousLinearEquiv
  let ν : Measure E := Measure.map e volume
  have : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hν : HasPrekopaLeindler ν :=
    (HasPrekopaLeindler.pi_fin_real n).map_linearMap e.toLinearMap e.continuous.measurable
  rw [isAddLeftInvariant_eq_smul μ ν]
  exact hν.smul (μ.addHaarScalarFactor ν)

/-- Lebesgue measure `volume` on `EuclideanSpace ℝ (Fin n)` satisfies `HasPrekopaLeindler` for
every `n : ℕ`. -/
theorem HasPrekopaLeindler.euclideanSpace (n : ℕ) :
    HasPrekopaLeindler (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  HasPrekopaLeindler.of_isAddHaarMeasure volume

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Higher-dimensional Prékopa–Leindler inequality** in extended nonnegative form: for any
additive Haar measure `μ` on a finite-dimensional real normed space `E`, `0 < θ < 1`, and
measurable functions `f, g, h : E → ℝ≥0∞` satisfying
`f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)` for all `x, y : E`,
`(∫⁻ x, f x ∂μ) ^ (1 - θ) * (∫⁻ y, g y ∂μ) ^ θ ≤ ∫⁻ z, h z ∂μ`. -/
theorem lintegral_prekopa_leindler {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫⁻ x, f x ∂μ) ^ (1 - θ) * (∫⁻ y, g y ∂μ) ^ θ ≤ ∫⁻ z, h z ∂μ :=
  (HasPrekopaLeindler.of_isAddHaarMeasure μ) hθ₀ hθ₁ hf hg hh hle

/-- **Higher-dimensional Prékopa–Leindler inequality via measurable representatives**: if
`f =ᵐ[μ] f₀`, `g =ᵐ[μ] g₀`, and `h =ᵐ[μ] h₀` with measurable representatives `f₀, g₀, h₀ : E → ℝ≥0∞`
satisfying `f₀ x ^ (1 - θ) * g₀ y ^ θ ≤ h₀ ((1 - θ) • x + θ • y)` for all `x, y : E`, then
`(∫⁻ x, f x ∂μ) ^ (1 - θ) * (∫⁻ y, g y ∂μ) ^ θ ≤ ∫⁻ z, h z ∂μ`. -/
theorem lintegral_prekopa_leindler_of_ae_eq {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h f₀ g₀ h₀ : E → ℝ≥0∞}
    (hf : f =ᵐ[μ] f₀) (hg : g =ᵐ[μ] g₀) (hh : h =ᵐ[μ] h₀)
    (hf₀ : Measurable f₀) (hg₀ : Measurable g₀) (hh₀ : Measurable h₀)
    (hle : ∀ x y, f₀ x ^ (1 - θ) * g₀ y ^ θ ≤ h₀ ((1 - θ) • x + θ • y)) :
    (∫⁻ x, f x ∂μ) ^ (1 - θ) * (∫⁻ y, g y ∂μ) ^ θ ≤ ∫⁻ z, h z ∂μ :=
  (HasPrekopaLeindler.of_isAddHaarMeasure μ).lintegral_prekopa_leindler_of_ae_eq
    hθ₀ hθ₁ hf hg hh hf₀ hg₀ hh₀ hle

/-- **Higher-dimensional Prékopa–Leindler inequality for real-valued nonnegative functions via
`ENNReal.ofReal`**. -/
theorem lintegral_ofReal_prekopa_leindler {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : E → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ y, 0 ≤ g y)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ^ (1 - θ) * (∫⁻ y, ENNReal.ofReal (g y) ∂μ) ^ θ ≤
      ∫⁻ z, ENNReal.ofReal (h z) ∂μ :=
  (HasPrekopaLeindler.of_isAddHaarMeasure μ).lintegral_ofReal_prekopa_leindler
    hθ₀ hθ₁ hf hg hh hf_nn hg_nn hle

/-- **Higher-dimensional Prékopa–Leindler inequality for Bochner-integrable nonnegative real-valued
functions**. -/
theorem integral_prekopa_leindler {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : E → ℝ} (hf_m : Measurable f) (hg_m : Measurable g) (hh_m : Measurable h)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ y, 0 ≤ g y)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫ x, f x ∂μ) ^ (1 - θ) * (∫ y, g y ∂μ) ^ θ ≤ ∫ z, h z ∂μ :=
  (HasPrekopaLeindler.of_isAddHaarMeasure μ).integral_prekopa_leindler
    hθ₀ hθ₁ hf_m hg_m hh_m hf hg hh hf_nn hg_nn hle

/-- **Higher-dimensional Prékopa–Leindler inequality for Bochner-integrable functions via measurable
representatives**. -/
theorem integral_prekopa_leindler_of_ae_eq {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h f₀ g₀ h₀ : E → ℝ}
    (hf_ae : f =ᵐ[μ] f₀) (hg_ae : g =ᵐ[μ] g₀) (hh_ae : h =ᵐ[μ] h₀)
    (hf₀_m : Measurable f₀) (hg₀_m : Measurable g₀) (hh₀_m : Measurable h₀)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hf₀_nn : ∀ x, 0 ≤ f₀ x) (hg₀_nn : ∀ y, 0 ≤ g₀ y)
    (hle : ∀ x y, f₀ x ^ (1 - θ) * g₀ y ^ θ ≤ h₀ ((1 - θ) • x + θ • y)) :
    (∫ x, f x ∂μ) ^ (1 - θ) * (∫ y, g y ∂μ) ^ θ ≤ ∫ z, h z ∂μ :=
  (HasPrekopaLeindler.of_isAddHaarMeasure μ).integral_prekopa_leindler_of_ae_eq
    hθ₀ hθ₁ hf_ae hg_ae hh_ae hf₀_m hg₀_m hh₀_m hf hg hh hf₀_nn hg₀_nn hle

/-! ### Elementary measure laws, measurable cores, and decreasing compact continuity -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- Every nonempty `μ`-null-measurable subset `A ⊆ E` contains a nonempty Borel-measurable subset
`A' ⊆ A` of the same `μ`-measure. -/
theorem NullMeasurableSet.exists_nonempty_measurable_subset_measure_eq [MeasurableSingletonClass E]
    {A : Set E} (hAn : A.Nonempty) (hAm : NullMeasurableSet A μ) :
    ∃ A' ⊆ A, A'.Nonempty ∧ MeasurableSet A' ∧ μ A' = μ A := by
  obtain ⟨t, hts, htm, htae⟩ := hAm.exists_measurable_subset_ae_eq
  obtain ⟨a, ha⟩ := hAn
  refine ⟨t ∪ {a}, union_subset hts (singleton_subset_iff.2 ha), by simp,
    htm.union (measurableSet_singleton a), ?_⟩
  exact le_antisymm (measure_mono (union_subset hts (singleton_subset_iff.2 ha)))
    ((measure_congr htae).symm.trans_le (measure_mono subset_union_left))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- **Continuity from above for decreasing compact sets**: for an antitone sequence `K : ℕ → Set E`
of compact sets and any measure `μ` that is finite on compact sets,
`μ (⋂ k, K k) = ⨅ k, μ (K k)`. -/
theorem IsCompact.measure_iInter_of_antitone [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]
    {K : ℕ → Set E} (hK : ∀ k, IsCompact (K k)) (hant : Antitone K) :
    μ (⋂ k, K k) = ⨅ k, μ (K k) :=
  hant.measure_iInter (fun k ↦ (hK k).nullMeasurableSet) ⟨0, (hK 0).measure_lt_top.ne⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Right translation invariance of an additive Haar measure `μ` under singleton Minkowski addition
`A + {c}`. -/
theorem measure_add_singleton (A : Set E) (c : E) : μ (A + {c}) = μ A := by simp

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Left translation invariance of an additive Haar measure `μ` under singleton Minkowski addition
`{c} + A`. -/
theorem measure_singleton_add (c : E) (A : Set E) : μ ({c} + A) = μ A := by simp

/-- **Homogeneity of `μ (r • A) ^ (1 / finrank)`**: for `1 ≤ Module.finrank ℝ E` and any `r : ℝ`,
`μ (r • A) ^ (1 / (Module.finrank ℝ E : ℝ)) =
ENNReal.ofReal |r| * μ A ^ (1 / (Module.finrank ℝ E : ℝ))`. -/
theorem measure_smul_rpow_inv_finrank (r : ℝ) (A : Set E) (hn : 1 ≤ Module.finrank ℝ E) :
    μ (r • A) ^ (1 / (Module.finrank ℝ E : ℝ)) =
      ENNReal.ofReal |r| * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have hn_pos : (0 : ℝ) < Module.finrank ℝ E := by positivity
  have hinv_nn : 0 ≤ 1 / (Module.finrank ℝ E : ℝ) := by positivity
  rw [addHaar_smul μ r A, ENNReal.mul_rpow_of_nonneg _ _ hinv_nn]
  congr 1
  rw [abs_pow, ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (abs_nonneg r) _) hinv_nn,
    ← Real.rpow_natCast |r| _, ← Real.rpow_mul (abs_nonneg r),
    mul_one_div_cancel hn_pos.ne', Real.rpow_one]

/-- **Homogeneity of `μ (r • A) ^ (1 / finrank)` for nonnegative scalars `r ≥ 0`**. -/
theorem measure_smul_rpow_inv_finrank_of_nonneg {r : ℝ} (hr : 0 ≤ r) (A : Set E)
    (hn : 1 ≤ Module.finrank ℝ E) :
    μ (r • A) ^ (1 / (Module.finrank ℝ E : ℝ)) =
      ENNReal.ofReal r * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rw [measure_smul_rpow_inv_finrank μ r A hn, abs_of_nonneg hr]

/-! ### Multiplicative (dimension-free) Brunn–Minkowski inequality -/

/-- **Multiplicative Brunn–Minkowski inequality for compact sets**: for `0 < θ < 1` and compact sets
`K, L ⊆ E`, `μ K ^ (1 - θ) * μ L ^ θ ≤ μ ((1 - θ) • K + θ • L)`. -/
theorem measure_smul_add_smul_ge_geom_mean_of_isCompact {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) :
    μ K ^ (1 - θ) * μ L ^ θ ≤ μ ((1 - θ) • K + θ • L) := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  set S := (1 - θ) • K + θ • L
  have hS : IsCompact S := (hK.smul (1 - θ)).add (hL.smul θ)
  have hf : Measurable (K.indicator (1 : E → ℝ≥0∞)) := measurable_const.indicator hK.measurableSet
  have hg : Measurable (L.indicator (1 : E → ℝ≥0∞)) := measurable_const.indicator hL.measurableSet
  have hh : Measurable (S.indicator (1 : E → ℝ≥0∞)) := measurable_const.indicator hS.measurableSet
  have hPL := lintegral_prekopa_leindler μ hθ₀ hθ₁ hf hg hh fun x y ↦ by
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ L
      · have hxy : (1 - θ) • x + θ • y ∈ S :=
          add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
        simp [hx, hy, hxy]
      · simp [hy, hθ₀]
    · simp [hx, h1θ]
  simpa [lintegral_indicator_one hK.measurableSet, lintegral_indicator_one hL.measurableSet,
    lintegral_indicator_one hS.measurableSet] using hPL

/-- **Multiplicative Brunn–Minkowski inequality for Borel-measurable sets**: for `0 < θ < 1` and
measurable sets `A, B ⊆ E` (without assuming `(1 - θ) • A + θ • B` is measurable),
`μ A ^ (1 - θ) * μ B ^ θ ≤ μ ((1 - θ) • A + θ • B)`. -/
theorem measure_smul_add_smul_ge_geom_mean {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {A B : Set E} (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    μ A ^ (1 - θ) * μ B ^ θ ≤ μ ((1 - θ) • A + θ • B) := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  have hA_sup : μ A ^ (1 - θ) = ⨆ (K : Set E) (_ : K ⊆ A) (_ : IsCompact K), μ K ^ (1 - θ) := by
    rw [hAm.measure_eq_iSup_isCompact μ]
    simp_rw [ennreal_iSup_rpow _ h1θ]
  have hB_sup : μ B ^ θ = ⨆ (L : Set E) (_ : L ⊆ B) (_ : IsCompact L), μ L ^ θ := by
    rw [hBm.measure_eq_iSup_isCompact μ]
    simp_rw [ennreal_iSup_rpow _ hθ₀]
  rw [hA_sup, hB_sup]
  simp_rw [ENNReal.iSup_mul, ENNReal.mul_iSup]
  refine iSup₂_le fun K hKA ↦ iSup₂_le fun hK L ↦ iSup₂_le fun hLB hL ↦ ?_
  refine (measure_smul_add_smul_ge_geom_mean_of_isCompact μ hθ₀ hθ₁ hK hL).trans (measure_mono ?_)
  exact add_subset_add (smul_set_mono hKA) (smul_set_mono hLB)

/-- **Multiplicative Brunn–Minkowski inequality for `μ`-null-measurable sets**: for `0 < θ < 1` and
`μ`-null-measurable sets `A, B ⊆ E` (without assuming `(1 - θ) • A + θ • B` is measurable),
`μ A ^ (1 - θ) * μ B ^ θ ≤ μ ((1 - θ) • A + θ • B)`. -/
theorem measure_smul_add_smul_ge_geom_mean_of_nullMeasurableSet {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) {A B : Set E}
    (hAm : NullMeasurableSet A μ) (hBm : NullMeasurableSet B μ) :
    μ A ^ (1 - θ) * μ B ^ θ ≤ μ ((1 - θ) • A + θ • B) := by
  obtain ⟨A', hA'A, hA'm, hA'ae⟩ := hAm.exists_measurable_subset_ae_eq
  obtain ⟨B', hB'B, hB'm, hB'ae⟩ := hBm.exists_measurable_subset_ae_eq
  rw [← measure_congr hA'ae, ← measure_congr hB'ae]
  refine (measure_smul_add_smul_ge_geom_mean μ hθ₀ hθ₁ hA'm hB'm).trans (measure_mono ?_)
  exact add_subset_add (smul_set_mono hA'A) (smul_set_mono hB'B)

/-- **Multiplicative Brunn–Minkowski inequality for `volume`** on a finite-dimensional real normed
space `E` with `[MeasureSpace E] [(volume : Measure E).IsAddHaarMeasure]`. -/
theorem volume_smul_add_smul_ge_geom_mean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {A B : Set E} (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    volume A ^ (1 - θ) * volume B ^ θ ≤ volume ((1 - θ) • A + θ • B) :=
  measure_smul_add_smul_ge_geom_mean volume hθ₀ hθ₁ hAm hBm

/-! ### Unweighted and weighted additive Brunn–Minkowski inequalities in dimension `n ≥ 1` -/

/-- **All-dimensional unweighted Brunn–Minkowski inequality for Borel-measurable sets**: for
`1 ≤ Module.finrank ℝ E` and nonempty measurable sets `A, B ⊆ E` (with no measurability assumption
on `A + B`),
`μ A ^ (1 / (Module.finrank ℝ E : ℝ)) + μ B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
μ (A + B) ^ (1 / (Module.finrank ℝ E : ℝ))`. -/
theorem measure_add_rpow_inv_finrank_ge (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hAn : A.Nonempty) (hAm : MeasurableSet A)
    (hBn : B.Nonempty) (hBm : MeasurableSet B) :
    μ A ^ (1 / (Module.finrank ℝ E : ℝ)) + μ B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      μ (A + B) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  set p : ℝ := 1 / (Module.finrank ℝ E : ℝ)
  have hp : 0 < p := by positivity
  obtain ⟨a₀, ha₀⟩ := hAn
  obtain ⟨b₀, hb₀⟩ := hBn
  rcases eq_or_ne (μ A) 0 with hA0 | hA0
  · rw [hA0, ENNReal.zero_rpow_of_pos hp, zero_add]
    refine ENNReal.rpow_le_rpow ?_ hp.le
    calc μ B = μ ({a₀} + B) := by simp
      _ ≤ μ (A + B) := measure_mono (add_subset_add_right (singleton_subset_iff.2 ha₀))
  rcases eq_or_ne (μ B) 0 with hB0 | hB0
  · rw [hB0, ENNReal.zero_rpow_of_pos hp, add_zero]
    refine ENNReal.rpow_le_rpow ?_ hp.le
    calc μ A = μ (A + {b₀}) := by simp
      _ ≤ μ (A + B) := measure_mono (add_subset_add_left (singleton_subset_iff.2 hb₀))
  rcases eq_or_ne (μ A) ⊤ with hAtop | hAtop
  · have hAB : μ (A + B) = ⊤ := top_unique <| by
      calc ⊤ = μ A := hAtop.symm
        _ = μ (A + {b₀}) := by simp
        _ ≤ μ (A + B) := measure_mono (add_subset_add_left (singleton_subset_iff.2 hb₀))
    simp [hAB, hp]
  rcases eq_or_ne (μ B) ⊤ with hBtop | hBtop
  · have hAB : μ (A + B) = ⊤ := top_unique <| by
      calc ⊤ = μ B := hBtop.symm
        _ = μ ({a₀} + B) := by simp
        _ ≤ μ (A + B) := measure_mono (add_subset_add_right (singleton_subset_iff.2 ha₀))
    simp [hAB, hp]
  set a : ℝ := (μ A ^ p).toReal
  set b : ℝ := (μ B ^ p).toReal
  have hAp_0 : μ A ^ p ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hAtop).ne'
  have hAp_top : μ A ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le hAtop
  have hBp_0 : μ B ^ p ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hB0) hBtop).ne'
  have hBp_top : μ B ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le hBtop
  have ha : 0 < a := ENNReal.toReal_pos hAp_0 hAp_top
  have hb : 0 < b := ENNReal.toReal_pos hBp_0 hBp_top
  have hab : 0 < a + b := add_pos ha hb
  have ha_ofReal : ENNReal.ofReal a = μ A ^ p := ENNReal.ofReal_toReal hAp_top
  have hb_ofReal : ENNReal.ofReal b = μ B ^ p := ENNReal.ofReal_toReal hBp_top
  set A₁ : Set E := a⁻¹ • A
  set B₁ : Set E := b⁻¹ • B
  have hA₁m : MeasurableSet A₁ := hAm.const_smul (Units.mk0 a⁻¹ (inv_ne_zero ha.ne'))
  have hB₁m : MeasurableSet B₁ := hBm.const_smul (Units.mk0 b⁻¹ (inv_ne_zero hb.ne'))
  have hA₁_rpow : μ A₁ ^ p = 1 := by
    rw [measure_smul_rpow_inv_finrank_of_nonneg μ (inv_nonneg.2 ha.le) A hn, ← ha_ofReal,
      ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le), inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]
  have hB₁_rpow : μ B₁ ^ p = 1 := by
    rw [measure_smul_rpow_inv_finrank_of_nonneg μ (inv_nonneg.2 hb.le) B hn, ← hb_ofReal,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hb.le), inv_mul_cancel₀ hb.ne', ENNReal.ofReal_one]
  have hA₁_meas : μ A₁ = 1 := by
    have h := congrArg (fun x : ℝ≥0∞ ↦ x ^ (Module.finrank ℝ E : ℝ)) hA₁_rpow
    dsimp [p] at h
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel (by positivity : (Module.finrank ℝ E : ℝ) ≠ 0),
      ENNReal.rpow_one, ENNReal.one_rpow] at h
  have hB₁_meas : μ B₁ = 1 := by
    have h := congrArg (fun x : ℝ≥0∞ ↦ x ^ (Module.finrank ℝ E : ℝ)) hB₁_rpow
    dsimp [p] at h
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel (by positivity : (Module.finrank ℝ E : ℝ) ≠ 0),
      ENNReal.rpow_one, ENNReal.one_rpow] at h
  set θ : ℝ := b / (a + b)
  have hθ₀ : 0 < θ := div_pos hb hab
  have hθ₁ : θ < 1 := (div_lt_one hab).2 (lt_add_of_pos_left b ha)
  have h1θ_eq : 1 - θ = a / (a + b) := by
    rw [sub_div' hab.ne']
    ring
  have hset : (1 - θ) • A₁ + θ • B₁ = (a + b)⁻¹ • (A + B) := by
    have h1 : (1 - θ) • A₁ = (a + b)⁻¹ • A := by
      rw [h1θ_eq, smul_smul]
      congr 1
      field_simp
    have h2 : θ • B₁ = (a + b)⁻¹ • B := by
      rw [smul_smul]
      dsimp [θ]
      congr 1
      field_simp
    rw [h1, h2, smul_add]
  have hbm := measure_smul_add_smul_ge_geom_mean μ hθ₀ hθ₁ hA₁m hB₁m
  rw [hA₁_meas, hB₁_meas, ENNReal.one_rpow, ENNReal.one_rpow, mul_one, hset] at hbm
  have hbm_p : 1 ≤ μ ((a + b)⁻¹ • (A + B)) ^ p := by
    simpa using ENNReal.rpow_le_rpow hbm hp.le
  rw [measure_smul_rpow_inv_finrank_of_nonneg μ (inv_nonneg.2 hab.le) (A + B) hn] at hbm_p
  calc μ A ^ p + μ B ^ p
      = ENNReal.ofReal (a + b) * 1 := by
        rw [mul_one, ENNReal.ofReal_add ha.le hb.le, ha_ofReal, hb_ofReal]
    _ ≤ ENNReal.ofReal (a + b) * (ENNReal.ofReal (a + b)⁻¹ * μ (A + B) ^ p) :=
        mul_le_mul' le_rfl hbm_p
    _ = μ (A + B) ^ p := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hab.le, mul_inv_cancel₀ hab.ne',
          ENNReal.ofReal_one, one_mul]

/-- **All-dimensional unweighted Brunn–Minkowski inequality for compact sets**. -/
theorem measure_add_rpow_inv_finrank_ge_of_isCompact (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hAn : A.Nonempty) (hAc : IsCompact A)
    (hBn : B.Nonempty) (hBc : IsCompact B) :
    μ A ^ (1 / (Module.finrank ℝ E : ℝ)) + μ B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      μ (A + B) ^ (1 / (Module.finrank ℝ E : ℝ)) :=
  measure_add_rpow_inv_finrank_ge μ hn hAn hAc.measurableSet hBn hBc.measurableSet

/-- **All-dimensional unweighted Brunn–Minkowski inequality for `μ`-null-measurable sets** (with no
measurability assumption on `A + B`). -/
theorem measure_add_rpow_inv_finrank_ge_of_nullMeasurableSet (hn : 1 ≤ Module.finrank ℝ E)
    {A B : Set E} (hAn : A.Nonempty) (hAm : NullMeasurableSet A μ)
    (hBn : B.Nonempty) (hBm : NullMeasurableSet B μ) :
    μ A ^ (1 / (Module.finrank ℝ E : ℝ)) + μ B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      μ (A + B) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  obtain ⟨A', hA'A, hA'n, hA'm, hA'eq⟩ :=
    hAm.exists_nonempty_measurable_subset_measure_eq μ hAn
  obtain ⟨B', hB'B, hB'n, hB'm, hB'eq⟩ :=
    hBm.exists_nonempty_measurable_subset_measure_eq μ hBn
  rw [← hA'eq, ← hB'eq]
  refine (measure_add_rpow_inv_finrank_ge μ hn hA'n hA'm hB'n hB'm).trans ?_
  exact ENNReal.rpow_le_rpow (measure_mono (add_subset_add hA'A hB'B)) (by positivity)

/-- **All-dimensional weighted Brunn–Minkowski inequality for Borel-measurable sets**: for
`1 ≤ Module.finrank ℝ E`, `0 ≤ θ ≤ 1`, and nonempty measurable sets `A, B ⊆ E`,
`ENNReal.ofReal (1 - θ) * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) +
ENNReal.ofReal θ * μ B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
μ ((1 - θ) • A + θ • B) ^ (1 / (Module.finrank ℝ E : ℝ))`. -/
theorem measure_smul_add_smul_rpow_inv_finrank_ge (hn : 1 ≤ Module.finrank ℝ E)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    {A B : Set E} (hAn : A.Nonempty) (hAm : MeasurableSet A)
    (hBn : B.Nonempty) (hBm : MeasurableSet B) :
    ENNReal.ofReal (1 - θ) * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) +
        ENNReal.ofReal θ * μ B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      μ ((1 - θ) • A + θ • B) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rcases eq_or_lt_of_le hθ₀ with rfl | hθ₀'
  · simp [zero_smul_set hBn]
  rcases eq_or_lt_of_le hθ₁ with rfl | hθ₁'
  · simp [zero_smul_set hAn]
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁'
  have hA'm : MeasurableSet ((1 - θ) • A) := hAm.const_smul (Units.mk0 (1 - θ) h1θ.ne')
  have hB'm : MeasurableSet (θ • B) := hBm.const_smul (Units.mk0 θ hθ₀'.ne')
  have h := measure_add_rpow_inv_finrank_ge μ hn hAn.smul_set hA'm hBn.smul_set hB'm
  rwa [measure_smul_rpow_inv_finrank_of_nonneg μ h1θ.le A hn,
    measure_smul_rpow_inv_finrank_of_nonneg μ hθ₀'.le B hn] at h

/-- **All-dimensional weighted Brunn–Minkowski inequality for compact sets**. -/
theorem measure_smul_add_smul_rpow_inv_finrank_ge_of_isCompact (hn : 1 ≤ Module.finrank ℝ E)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    {A B : Set E} (hAn : A.Nonempty) (hAc : IsCompact A)
    (hBn : B.Nonempty) (hBc : IsCompact B) :
    ENNReal.ofReal (1 - θ) * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) +
        ENNReal.ofReal θ * μ B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      μ ((1 - θ) • A + θ • B) ^ (1 / (Module.finrank ℝ E : ℝ)) :=
  measure_smul_add_smul_rpow_inv_finrank_ge μ hn hθ₀ hθ₁ hAn hAc.measurableSet hBn hBc.measurableSet

/-- **All-dimensional weighted Brunn–Minkowski inequality for `μ`-null-measurable sets** (with no
measurability assumption on `(1 - θ) • A + θ • B`). -/
theorem measure_smul_add_smul_rpow_inv_finrank_ge_of_nullMeasurableSet
    (hn : 1 ≤ Module.finrank ℝ E) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    {A B : Set E} (hAn : A.Nonempty) (hAm : NullMeasurableSet A μ)
    (hBn : B.Nonempty) (hBm : NullMeasurableSet B μ) :
    ENNReal.ofReal (1 - θ) * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) +
        ENNReal.ofReal θ * μ B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      μ ((1 - θ) • A + θ • B) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  obtain ⟨A', hA'A, hA'n, hA'm, hA'eq⟩ :=
    hAm.exists_nonempty_measurable_subset_measure_eq μ hAn
  obtain ⟨B', hB'B, hB'n, hB'm, hB'eq⟩ :=
    hBm.exists_nonempty_measurable_subset_measure_eq μ hBn
  rw [← hA'eq, ← hB'eq]
  refine (measure_smul_add_smul_rpow_inv_finrank_ge μ hn hθ₀ hθ₁ hA'n hA'm hB'n hB'm).trans ?_
  exact ENNReal.rpow_le_rpow
    (measure_mono (add_subset_add (smul_set_mono hA'A) (smul_set_mono hB'B))) (by positivity)

/-- **All-dimensional unweighted Brunn–Minkowski inequality for `volume`**. -/
theorem volume_add_rpow_inv_finrank_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    (hn : 1 ≤ Module.finrank ℝ E) {A B : Set E}
    (hAn : A.Nonempty) (hAm : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hBm : NullMeasurableSet B volume) :
    volume A ^ (1 / (Module.finrank ℝ E : ℝ)) + volume B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      volume (A + B) ^ (1 / (Module.finrank ℝ E : ℝ)) :=
  measure_add_rpow_inv_finrank_ge_of_nullMeasurableSet volume hn hAn hAm hBn hBm

/-- **All-dimensional weighted Brunn–Minkowski inequality for `volume`**. -/
theorem volume_smul_add_smul_rpow_inv_finrank_ge {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] (hn : 1 ≤ Module.finrank ℝ E)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) {A B : Set E}
    (hAn : A.Nonempty) (hAm : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hBm : NullMeasurableSet B volume) :
    ENNReal.ofReal (1 - θ) * volume A ^ (1 / (Module.finrank ℝ E : ℝ)) +
        ENNReal.ofReal θ * volume B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      volume ((1 - θ) • A + θ • B) ^ (1 / (Module.finrank ℝ E : ℝ)) :=
  measure_smul_add_smul_rpow_inv_finrank_ge_of_nullMeasurableSet volume hn hθ₀ hθ₁ hAn hAm hBn hBm

end FiniteDimensional

end MeasureTheory

namespace EuclideanSpace

/-- **Brunn–Minkowski inequality on `EuclideanSpace ℝ (Fin n)`** for `1 ≤ n` and nonempty
Lebesgue-measurable sets `A, B`:
`volume A ^ (1 / (n : ℝ)) + volume B ^ (1 / (n : ℝ)) ≤ volume (A + B) ^ (1 / (n : ℝ))`. -/
theorem volume_add_rpow_inv_ge {n : ℕ} (hn : 1 ≤ n)
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hAn : A.Nonempty) (hAm : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hBm : NullMeasurableSet B volume) :
    volume A ^ (1 / (n : ℝ)) + volume B ^ (1 / (n : ℝ)) ≤
      volume (A + B) ^ (1 / (n : ℝ)) := by
  have hn' : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simpa using hn
  simpa using MeasureTheory.volume_add_rpow_inv_finrank_ge hn' hAn hAm hBn hBm

/-- **Weighted Brunn–Minkowski inequality on `EuclideanSpace ℝ (Fin n)`** for `1 ≤ n`,
`0 ≤ θ ≤ 1`, and nonempty Lebesgue-measurable sets `A, B`:
`ENNReal.ofReal (1 - θ) * volume A ^ (1 / (n : ℝ)) +
ENNReal.ofReal θ * volume B ^ (1 / (n : ℝ)) ≤
volume ((1 - θ) • A + θ • B) ^ (1 / (n : ℝ))`. -/
theorem volume_smul_add_smul_rpow_inv_ge {n : ℕ} (hn : 1 ≤ n)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hAn : A.Nonempty) (hAm : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hBm : NullMeasurableSet B volume) :
    ENNReal.ofReal (1 - θ) * volume A ^ (1 / (n : ℝ)) +
        ENNReal.ofReal θ * volume B ^ (1 / (n : ℝ)) ≤
      volume ((1 - θ) • A + θ • B) ^ (1 / (n : ℝ)) := by
  have hn' : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simpa using hn
  simpa using MeasureTheory.volume_smul_add_smul_rpow_inv_finrank_ge hn' hθ₀ hθ₁ hAn hAm hBn hBm

end EuclideanSpace
