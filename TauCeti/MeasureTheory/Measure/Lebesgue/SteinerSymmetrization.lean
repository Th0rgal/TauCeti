/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Steiner Symmetrization and the Euclidean Isodiametric Inequality

For a unit vector `e` in a finite-dimensional real inner product space `E`, the orthogonal
complement `orthogonalHyperplane e := (ℝ ∙ e)ᗮ` induces an isometric splitting
`WithLp 2 (orthogonalHyperplane e × ℝ) ≃ₗᵢ[ℝ] E` via `(y, t) ↦ (y : E) + t • e` with inverse
`x ↦ ((orthogonalHyperplane e).orthogonalProjectionOnto x, ⟪x, e⟫_ℝ)`. This splitting is
measure-preserving between product Lebesgue measure on `orthogonalHyperplane e × ℝ` and Lebesgue
measure on `E`.

Steiner symmetrization `steinerSymmetrization e s` replaces each one-dimensional fiber
`steinerFiber e s y = {t : ℝ | (y : E) + t • e ∈ s}` over `y : orthogonalHyperplane e` by the
centered closed interval `symmetricInterval (steinerFiber e s y)` of the same one-dimensional
Lebesgue measure (with measure `0` mapped to `∅` and measure `⊤` mapped to `Set.univ`). We establish
section measurability, Fubini volume preservation, invariance under a.e. modifications,
monotonicity, reflection symmetry in `orthogonalHyperplane e`, preservation of reflection symmetry
in orthogonal directions, preservation of centered balls up to null sets, the two-set intersection
inequality, `L¹` contraction on symmetric differences, and diameter non-expansion.

Iterating Steiner symmetrization across the vectors of an orthonormal basis transforms the closure
of any bounded set into a measurable origin-symmetric set of at least the same volume and at most
the same diameter, yielding the sharp Euclidean isodiametric inequality
`volume s ≤ volume (Metric.closedBall (0 : E) (Metric.diam s / 2))`.

## Main definitions

* `TauCeti.MeasureTheory.orthogonalHyperplane`: the orthogonal hyperplane `(ℝ ∙ e)ᗮ`.
* `TauCeti.MeasureTheory.orthogonalHyperplaneProdEquiv`: the linear isometry equivalence
  `WithLp 2 (orthogonalHyperplane e × ℝ) ≃ₗᵢ[ℝ] E` for a unit vector `e`.
* `TauCeti.MeasureTheory.orthogonalHyperplaneProdMeasurableEquiv`: the measurable equivalence
  `(orthogonalHyperplane e × ℝ) ≃ᵐ E` for a unit vector `e`.
* `TauCeti.MeasureTheory.symmetricInterval`: the centered closed interval in `ℝ` with the same
  Lebesgue measure as a given subset of `ℝ`.
* `TauCeti.MeasureTheory.steinerFiber`: the one-dimensional slice `{t : ℝ | (y : E) + t • e ∈ s}`
  of `s : Set E` over `y : orthogonalHyperplane e`.
* `TauCeti.MeasureTheory.steinerSymmetrization`: Steiner symmetrization of `s : Set E` in
  direction `e`.
* `TauCeti.MeasureTheory.steinerSymmetrizationList`: iterated Steiner symmetrization along a list of
  directions.
* `TauCeti.MeasureTheory.steinerSymmetrizationBasis`: iterated Steiner symmetrization along an
  orthonormal basis.

## Main results

* `TauCeti.MeasureTheory.norm_add_smul_sq_of_mem_orthogonalHyperplane`: Pythagorean identity
  `‖y + t • e‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2` for `y ∈ orthogonalHyperplane e` and `‖e‖ = 1`.
* `TauCeti.MeasureTheory.measurePreserving_orthogonalHyperplaneProd`: `(y, t) ↦ (y : E) + t • e`
  preserves volume from `orthogonalHyperplane e × ℝ` to `E`.
* `TauCeti.MeasureTheory.volume_steinerSymmetrization`: Steiner symmetrization preserves volume on
  measurable sets.
* `TauCeti.MeasureTheory.steinerSymmetrization_ae_eq`: Steiner symmetrization respects `=ᵐ[volume]`.
* `TauCeti.MeasureTheory.volume_inter_le_volume_steinerSymmetrization_inter` and
  `TauCeti.MeasureTheory.volume_symmDiff_steinerSymmetrization_le`: Riesz rearrangement inequality
  for two indicator functions and `L¹` contraction on symmetric differences.
* `TauCeti.MeasureTheory.ediam_steinerSymmetrization_le` and
  `TauCeti.MeasureTheory.diam_steinerSymmetrization_le`: Steiner symmetrization does not increase
  diameter.
* `TauCeti.MeasureTheory.volume_le_volume_closedBall_diam_div_two`,
  `TauCeti.MeasureTheory.volume_le_volume_ball_diam_div_two`, and
  `TauCeti.MeasureTheory.volume_le_pow_diam_div_two_mul_volume_unitBall`: the sharp Euclidean
  isodiametric inequality.
-/

public section

noncomputable section

open MeasureTheory Set Filter Metric Submodule
open scoped ENNReal symmDiff InnerProductSpace

namespace TauCeti.MeasureTheory

section OrthogonalHyperplane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hyperplane orthogonal to a vector `e : E`, defined as `(ℝ ∙ e)ᗮ`. -/
def orthogonalHyperplane (e : E) : Submodule ℝ E :=
  (ℝ ∙ e)ᗮ

instance (e : E) : (orthogonalHyperplane e).HasOrthogonalProjection :=
  inferInstanceAs (ℝ ∙ e)ᗮ.HasOrthogonalProjection

theorem mem_orthogonalHyperplane_iff {e x : E} :
    x ∈ orthogonalHyperplane e ↔ ⟪x, e⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_left

theorem mem_orthogonalHyperplane_iff_inner_left {e x : E} :
    x ∈ orthogonalHyperplane e ↔ ⟪e, x⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

theorem inner_eq_zero_of_mem_orthogonalHyperplane {e y : E} (hy : y ∈ orthogonalHyperplane e) :
    ⟪y, e⟫_ℝ = 0 :=
  mem_orthogonalHyperplane_iff.mp hy

theorem inner_left_eq_zero_of_mem_orthogonalHyperplane {e y : E}
    (hy : y ∈ orthogonalHyperplane e) : ⟪e, y⟫_ℝ = 0 :=
  mem_orthogonalHyperplane_iff_inner_left.mp hy

@[simp]
theorem coe_inner_orthogonalHyperplane_eq_zero (e : E) (y : orthogonalHyperplane e) :
    ⟪(y : E), e⟫_ℝ = 0 :=
  inner_eq_zero_of_mem_orthogonalHyperplane y.2

@[simp]
theorem inner_coe_orthogonalHyperplane_eq_zero (e : E) (y : orthogonalHyperplane e) :
    ⟪e, (y : E)⟫_ℝ = 0 :=
  inner_left_eq_zero_of_mem_orthogonalHyperplane y.2

theorem self_mem_orthogonalHyperplane_orthogonal (e : E) :
    e ∈ (orthogonalHyperplane e)ᗮ :=
  (ℝ ∙ e).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self e)

theorem smul_self_mem_orthogonalHyperplane_orthogonal (e : E) (t : ℝ) :
    t • e ∈ (orthogonalHyperplane e)ᗮ :=
  Submodule.smul_mem _ t (self_mem_orthogonalHyperplane_orthogonal e)

@[simp]
theorem orthogonalProjectionOnto_orthogonalHyperplane_self (e : E) :
    (orthogonalHyperplane e).orthogonalProjectionOnto e = 0 :=
  Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero e

@[simp]
theorem starProjection_orthogonalHyperplane_self (e : E) :
    (orthogonalHyperplane e).starProjection e = 0 :=
  Submodule.starProjection_orthogonalComplement_singleton_eq_zero e

theorem orthogonalProjectionOnto_orthogonalHyperplane_smul_self (e : E) (t : ℝ) :
    (orthogonalHyperplane e).orthogonalProjectionOnto (t • e) = 0 := by
  rw [map_smul, orthogonalProjectionOnto_orthogonalHyperplane_self, smul_zero]

@[simp]
theorem orthogonalProjectionOnto_orthogonalHyperplane_add_smul
    (e : E) (y : orthogonalHyperplane e) (t : ℝ) :
    (orthogonalHyperplane e).orthogonalProjectionOnto ((y : E) + t • e) = y := by
  rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    orthogonalProjectionOnto_orthogonalHyperplane_smul_self, add_zero]

theorem starProjection_orthogonalHyperplane_apply {e : E} (he : ‖e‖ = 1) (x : E) :
    (orthogonalHyperplane e).starProjection x = x - ⟪x, e⟫_ℝ • e := by
  change (ℝ ∙ e)ᗮ.starProjection x = x - ⟪x, e⟫_ℝ • e
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ he, real_inner_comm]

theorem orthogonalProjection_orthogonalHyperplane_add_inner_smul
    {e : E} (he : ‖e‖ = 1) (x : E) :
    ((orthogonalHyperplane e).orthogonalProjectionOnto x : E) + ⟪x, e⟫_ℝ • e = x := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply,
    starProjection_orthogonalHyperplane_apply he, sub_add_cancel]

theorem inner_add_smul_self_of_mem_orthogonalHyperplane
    {e y : E} (he : ‖e‖ = 1) (hy : y ∈ orthogonalHyperplane e) (t : ℝ) :
    ⟪y + t • e, e⟫_ℝ = t := by
  rw [inner_add_left, inner_eq_zero_of_mem_orthogonalHyperplane hy, zero_add,
    inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq, he, one_pow, mul_one]

@[simp]
theorem inner_coe_add_smul_self {e : E} (he : ‖e‖ = 1) (y : orthogonalHyperplane e) (t : ℝ) :
    ⟪(y : E) + t • e, e⟫_ℝ = t :=
  inner_add_smul_self_of_mem_orthogonalHyperplane he y.2 t

/-- Pythagorean identity for the orthogonal hyperplane decomposition `y + t • e` with
`y ∈ orthogonalHyperplane e` and `‖e‖ = 1`. -/
theorem norm_add_smul_sq_of_mem_orthogonalHyperplane
    {e y : E} (he : ‖e‖ = 1) (hy : y ∈ orthogonalHyperplane e) (t : ℝ) :
    ‖y + t • e‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  have hortho : ⟪y, t • e⟫_ℝ = 0 := by
    rw [inner_smul_right, inner_eq_zero_of_mem_orthogonalHyperplane hy, mul_zero]
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_real hortho, ← sq, ← sq, norm_smul, Real.norm_eq_abs,
    he, mul_one, sq_abs]

@[simp]
theorem norm_coe_add_smul_sq {e : E} (he : ‖e‖ = 1) (y : orthogonalHyperplane e) (t : ℝ) :
    ‖(y : E) + t • e‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 :=
  norm_add_smul_sq_of_mem_orthogonalHyperplane he y.2 t

/-- The linear isometry equivalence `WithLp 2 (orthogonalHyperplane e × ℝ) ≃ₗᵢ[ℝ] E` mapping
`(y, t)` to `(y : E) + t • e`, with inverse `x ↦ (orthogonalProjectionOnto x, ⟪x, e⟫_ℝ)`. -/
def orthogonalHyperplaneProdEquiv {e : E} (he : ‖e‖ = 1) :
    WithLp 2 (orthogonalHyperplane e × ℝ) ≃ₗᵢ[ℝ] E where
  toFun yt := (yt.fst : E) + yt.snd • e
  invFun x := WithLp.toLp 2 ((orthogonalHyperplane e).orthogonalProjectionOnto x, ⟪x, e⟫_ℝ)
  map_add' yt₁ yt₂ := by
    simp only [WithLp.add_fst, Submodule.coe_add, WithLp.add_snd, add_smul]
    abel
  map_smul' c yt := by
    simp only [WithLp.smul_fst, SetLike.val_smul, WithLp.smul_snd, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add]
  left_inv yt := by
    dsimp only
    rw [orthogonalProjectionOnto_orthogonalHyperplane_add_smul, inner_coe_add_smul_self he]
    rfl
  right_inv x := orthogonalProjection_orthogonalHyperplane_add_inner_smul he x
  norm_map' yt := by
    change ‖(yt.fst : E) + yt.snd • e‖ = ‖yt‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_coe_add_smul_sq he,
      WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

@[simp]
theorem orthogonalHyperplaneProdEquiv_apply {e : E} (he : ‖e‖ = 1)
    (yt : WithLp 2 (orthogonalHyperplane e × ℝ)) :
    orthogonalHyperplaneProdEquiv he yt = (yt.fst : E) + yt.snd • e := by
  rfl

theorem orthogonalHyperplaneProdEquiv_toLp {e : E} (he : ‖e‖ = 1)
    (y : orthogonalHyperplane e) (t : ℝ) :
    orthogonalHyperplaneProdEquiv he (WithLp.toLp 2 (y, t)) = (y : E) + t • e := by
  rfl

@[simp]
theorem orthogonalHyperplaneProdEquiv_symm_apply {e : E} (he : ‖e‖ = 1) (x : E) :
    (orthogonalHyperplaneProdEquiv he).symm x =
      WithLp.toLp 2 ((orthogonalHyperplane e).orthogonalProjectionOnto x, ⟪x, e⟫_ℝ) := by
  rfl

theorem fst_orthogonalHyperplaneProdEquiv_symm_apply {e : E} (he : ‖e‖ = 1) (x : E) :
    ((orthogonalHyperplaneProdEquiv he).symm x).fst =
      (orthogonalHyperplane e).orthogonalProjectionOnto x := by
  rfl

theorem snd_orthogonalHyperplaneProdEquiv_symm_apply {e : E} (he : ‖e‖ = 1) (x : E) :
    ((orthogonalHyperplaneProdEquiv he).symm x).snd = ⟪x, e⟫_ℝ := by
  rfl

theorem reflection_orthogonalHyperplane_apply {e : E} (he : ‖e‖ = 1) (x : E) :
    (orthogonalHyperplane e).reflection x = x - (2 * ⟪x, e⟫_ℝ) • e := by
  rw [Submodule.reflection_apply, starProjection_orthogonalHyperplane_apply he, two_smul,
    two_mul, add_smul]
  abel

@[simp]
theorem reflection_orthogonalHyperplane_self (e : E) :
    (orthogonalHyperplane e).reflection e = -e :=
  Submodule.reflection_orthogonalComplement_singleton_eq_neg e

@[simp]
theorem reflection_orthogonalHyperplane_coe_add_smul
    (e : E) (y : orthogonalHyperplane e) (t : ℝ) :
    (orthogonalHyperplane e).reflection ((y : E) + t • e) = (y : E) + (-t) • e := by
  rw [map_add, Submodule.reflection_mem_subspace_eq_self y.2, map_smul,
    reflection_orthogonalHyperplane_self, smul_neg, neg_smul]

@[simp]
theorem orthogonalProjectionOnto_reflection_orthogonalHyperplane (e : E) (x : E) :
    (orthogonalHyperplane e).orthogonalProjectionOnto ((orthogonalHyperplane e).reflection x) =
      (orthogonalHyperplane e).orthogonalProjectionOnto x := by
  rw [Submodule.reflection_apply, two_smul, map_sub, map_add,
    ← Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, add_sub_cancel_right]

@[simp]
theorem inner_reflection_orthogonalHyperplane_self (e : E) (x : E) :
    ⟪(orthogonalHyperplane e).reflection x, e⟫_ℝ = -⟪x, e⟫_ℝ := by
  calc
    ⟪(orthogonalHyperplane e).reflection x, e⟫_ℝ
      = ⟪(orthogonalHyperplane e).reflection x,
          (orthogonalHyperplane e).reflection (-e)⟫_ℝ := by
        rw [map_neg, reflection_orthogonalHyperplane_self, neg_neg]
    _ = ⟪x, -e⟫_ℝ := LinearIsometryEquiv.inner_map_map _ _ _
    _ = -⟪x, e⟫_ℝ := inner_neg_right x e

end OrthogonalHyperplane

section MeasurePreservingDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- The measurable equivalence `(orthogonalHyperplane e × ℝ) ≃ᵐ E` mapping `(y, t)` to
`(y : E) + t • e`. -/
def orthogonalHyperplaneProdMeasurableEquiv {e : E} (he : ‖e‖ = 1) :
    (orthogonalHyperplane e × ℝ) ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 (orthogonalHyperplane e × ℝ)).trans
    (orthogonalHyperplaneProdEquiv he).toHomeomorph.toMeasurableEquiv

@[simp]
theorem orthogonalHyperplaneProdMeasurableEquiv_apply {e : E} (he : ‖e‖ = 1)
    (p : orthogonalHyperplane e × ℝ) :
    orthogonalHyperplaneProdMeasurableEquiv he p = (p.1 : E) + p.2 • e := by
  rfl

@[simp]
theorem orthogonalHyperplaneProdMeasurableEquiv_symm_apply {e : E} (he : ‖e‖ = 1) (x : E) :
    (orthogonalHyperplaneProdMeasurableEquiv he).symm x =
      ((orthogonalHyperplane e).orthogonalProjectionOnto x, ⟪x, e⟫_ℝ) := by
  rfl

variable [FiniteDimensional ℝ E]

/-- The measurable equivalence `orthogonalHyperplaneProdMeasurableEquiv` is measure-preserving from
`(volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ)` to
`(volume : Measure E)`. -/
theorem measurePreserving_orthogonalHyperplaneProdMeasurableEquiv {e : E} (he : ‖e‖ = 1) :
    MeasurePreserving (orthogonalHyperplaneProdMeasurableEquiv he)
      ((volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ))
      (volume : Measure E) :=
  (WithLp.volume_preserving_toLp (orthogonalHyperplane e) ℝ).trans
    (orthogonalHyperplaneProdEquiv he).measurePreserving

/-- The map `(y, t) ↦ (y : E) + t • e` is measure-preserving from
`(volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ)` to
`(volume : Measure E)`. -/
theorem measurePreserving_orthogonalHyperplaneProd {e : E} (he : ‖e‖ = 1) :
    MeasurePreserving (fun p : orthogonalHyperplane e × ℝ ↦ (p.1 : E) + p.2 • e)
      ((volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ))
      (volume : Measure E) :=
  measurePreserving_orthogonalHyperplaneProdMeasurableEquiv he

/-- The inverse decomposition `x ↦ ((orthogonalHyperplane e).orthogonalProjectionOnto x, ⟪x, e⟫_ℝ)`
is measure-preserving from `(volume : Measure E)` to
`(volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ)`. -/
theorem measurePreserving_orthogonalHyperplaneProdMeasurableEquiv_symm {e : E} (he : ‖e‖ = 1) :
    MeasurePreserving (orthogonalHyperplaneProdMeasurableEquiv he).symm
      (volume : Measure E)
      ((volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ)) :=
  (measurePreserving_orthogonalHyperplaneProdMeasurableEquiv he).symm

end MeasurePreservingDecomposition

section SymmetricInterval

/-- The centered closed interval in `ℝ` with the same one-dimensional Lebesgue measure as `t`,
with the convention that measure `0` gives `∅` and measure `⊤` gives `Set.univ`. -/
def symmetricInterval (t : Set ℝ) : Set ℝ :=
  if volume t = 0 then ∅
  else if volume t = ⊤ then Set.univ
  else Set.Icc (-(volume t).toReal / 2) ((volume t).toReal / 2)

theorem symmetricInterval_of_volume_eq_zero {t : Set ℝ} (h : volume t = 0) :
    symmetricInterval t = ∅ := by
  simp [symmetricInterval, h]

theorem symmetricInterval_of_volume_eq_top {t : Set ℝ} (h : volume t = ⊤) :
    symmetricInterval t = Set.univ := by
  simp [symmetricInterval, h]

theorem symmetricInterval_of_volume_ne_zero_of_ne_top {t : Set ℝ}
    (h₀ : volume t ≠ 0) (htop : volume t ≠ ⊤) :
    symmetricInterval t = Set.Icc (-(volume t).toReal / 2) ((volume t).toReal / 2) := by
  simp [symmetricInterval, h₀, htop]

@[simp]
theorem symmetricInterval_empty : symmetricInterval (∅ : Set ℝ) = ∅ :=
  symmetricInterval_of_volume_eq_zero measure_empty

@[simp]
theorem symmetricInterval_univ : symmetricInterval (Set.univ : Set ℝ) = Set.univ :=
  symmetricInterval_of_volume_eq_top Real.volume_univ

theorem mem_symmetricInterval_iff {t : Set ℝ} {r : ℝ} :
    r ∈ symmetricInterval t ↔ volume t ≠ 0 ∧ ENNReal.ofReal (2 * |r|) ≤ volume t := by
  by_cases h₀ : volume t = 0
  · simp [symmetricInterval_of_volume_eq_zero h₀, h₀]
  by_cases htop : volume t = ⊤
  · simp [symmetricInterval_of_volume_eq_top htop, htop]
  rw [symmetricInterval_of_volume_ne_zero_of_ne_top h₀ htop, Set.mem_Icc, neg_div, ← abs_le,
    le_div_iff₀ zero_lt_two, mul_comm, ← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal htop]
  exact ⟨fun h ↦ ⟨h₀, h⟩, And.right⟩

theorem symmetricInterval_congr_volume {s t : Set ℝ} (h : volume s = volume t) :
    symmetricInterval s = symmetricInterval t := by
  ext r
  simp [mem_symmetricInterval_iff, h]

theorem symmetricInterval_congr_ae {s t : Set ℝ} (h : s =ᵐ[volume] t) :
    symmetricInterval s = symmetricInterval t :=
  symmetricInterval_congr_volume (measure_congr h)

theorem symmetricInterval_mono_volume {s t : Set ℝ} (h : volume s ≤ volume t) :
    symmetricInterval s ⊆ symmetricInterval t := by
  intro r hr
  rw [mem_symmetricInterval_iff] at hr ⊢
  exact ⟨ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hr.1) h), hr.2.trans h⟩

theorem symmetricInterval_mono {s t : Set ℝ} (h : s ⊆ t) :
    symmetricInterval s ⊆ symmetricInterval t :=
  symmetricInterval_mono_volume (measure_mono h)

@[simp]
theorem neg_mem_symmetricInterval_iff {t : Set ℝ} {r : ℝ} :
    -r ∈ symmetricInterval t ↔ r ∈ symmetricInterval t := by
  simp [mem_symmetricInterval_iff]

theorem preimage_neg_symmetricInterval (t : Set ℝ) :
    Neg.neg ⁻¹' symmetricInterval t = symmetricInterval t := by
  ext r
  exact neg_mem_symmetricInterval_iff

theorem isClosed_symmetricInterval (t : Set ℝ) : IsClosed (symmetricInterval t) := by
  by_cases h₀ : volume t = 0
  · rw [symmetricInterval_of_volume_eq_zero h₀]
    exact isClosed_empty
  by_cases htop : volume t = ⊤
  · rw [symmetricInterval_of_volume_eq_top htop]
    exact isClosed_univ
  rw [symmetricInterval_of_volume_ne_zero_of_ne_top h₀ htop]
  exact isClosed_Icc

@[measurability]
theorem measurableSet_symmetricInterval (t : Set ℝ) : MeasurableSet (symmetricInterval t) :=
  (isClosed_symmetricInterval t).measurableSet

theorem convex_symmetricInterval (t : Set ℝ) : Convex ℝ (symmetricInterval t) := by
  by_cases h₀ : volume t = 0
  · rw [symmetricInterval_of_volume_eq_zero h₀]
    exact convex_empty
  by_cases htop : volume t = ⊤
  · rw [symmetricInterval_of_volume_eq_top htop]
    exact convex_univ
  rw [symmetricInterval_of_volume_ne_zero_of_ne_top h₀ htop]
  exact convex_Icc _ _

theorem ordConnected_symmetricInterval (t : Set ℝ) : Set.OrdConnected (symmetricInterval t) :=
  (convex_symmetricInterval t).ordConnected

@[simp]
theorem volume_symmetricInterval (t : Set ℝ) :
    volume (symmetricInterval t) = volume t := by
  by_cases h₀ : volume t = 0
  · rw [symmetricInterval_of_volume_eq_zero h₀, measure_empty, h₀]
  by_cases htop : volume t = ⊤
  · rw [symmetricInterval_of_volume_eq_top htop, Real.volume_univ, htop]
  rw [symmetricInterval_of_volume_ne_zero_of_ne_top h₀ htop, Real.volume_Icc,
    show (volume t).toReal / 2 - -(volume t).toReal / 2 = (volume t).toReal by ring,
    ENNReal.ofReal_toReal htop]

@[simp]
theorem symmetricInterval_symmetricInterval (t : Set ℝ) :
    symmetricInterval (symmetricInterval t) = symmetricInterval t :=
  symmetricInterval_congr_volume (volume_symmetricInterval t)

theorem symmetricInterval_inter_symmetricInterval (s t : Set ℝ) :
    symmetricInterval s ∩ symmetricInterval t =
      if volume s ≤ volume t then symmetricInterval s else symmetricInterval t := by
  split_ifs with h
  · exact Set.inter_eq_left.mpr (symmetricInterval_mono_volume h)
  · exact Set.inter_eq_right.mpr (symmetricInterval_mono_volume (le_of_not_ge h))

@[simp]
theorem volume_symmetricInterval_inter_symmetricInterval (s t : Set ℝ) :
    volume (symmetricInterval s ∩ symmetricInterval t) = min (volume s) (volume t) := by
  rw [symmetricInterval_inter_symmetricInterval]
  split_ifs with h
  · rw [volume_symmetricInterval, min_eq_left h]
  · rw [volume_symmetricInterval, min_eq_right (le_of_not_ge h)]

/-- One-dimensional two-set Riesz rearrangement inequality: replacing two subsets of `ℝ` by their
centered symmetric intervals does not decrease the measure of their intersection. -/
theorem volume_inter_le_volume_symmetricInterval_inter (s t : Set ℝ) :
    volume (s ∩ t) ≤ volume (symmetricInterval s ∩ symmetricInterval t) := by
  rw [volume_symmetricInterval_inter_symmetricInterval]
  exact le_min (measure_mono Set.inter_subset_left) (measure_mono Set.inter_subset_right)

/-- One-dimensional `L¹` contraction for `symmetricInterval`: replacing two subsets of `ℝ` by their
centered symmetric intervals does not increase the measure of their symmetric difference. -/
theorem volume_symmDiff_symmetricInterval_le (s t : Set ℝ) :
    volume (symmDiff (symmetricInterval s) (symmetricInterval t)) ≤ volume (symmDiff s t) := by
  have hle : ∀ a b : Set ℝ, volume a ≤ volume b →
      volume (symmDiff (symmetricInterval a) (symmetricInterval b)) ≤ volume (symmDiff a b) := by
    intro a b hab
    have hsub : symmetricInterval a ⊆ symmetricInterval b := symmetricInterval_mono_volume hab
    have hsd : symmDiff (symmetricInterval a) (symmetricInterval b) =
        symmetricInterval b \ symmetricInterval a := by
      ext x
      have := @hsub x
      simp only [Set.mem_symmDiff, Set.mem_sdiff]
      tauto
    rw [hsd]
    by_cases ha : volume a = ⊤
    · have hb : volume b = ⊤ := top_unique (ha ▸ hab)
      rw [symmetricInterval_of_volume_eq_top ha, symmetricInterval_of_volume_eq_top hb,
        Set.sdiff_self, measure_empty]
      exact zero_le
    · rw [measure_sdiff hsub (measurableSet_symmetricInterval a).nullMeasurableSet
        (by rwa [volume_symmetricInterval]), volume_symmetricInterval, volume_symmetricInterval]
      refine tsub_le_iff_left.mpr ?_
      calc
        volume b ≤ volume (a ∪ symmDiff a b) :=
          measure_mono (by intro x hx; rw [Set.mem_union, Set.mem_symmDiff]; tauto)
        _ ≤ volume a + volume (symmDiff a b) := measure_union_le a (symmDiff a b)
  rcases le_total (volume s) (volume t) with h | h
  · exact hle s t h
  · rw [symmDiff_comm (symmetricInterval s), symmDiff_comm s]
    exact hle t s h

end SymmetricInterval

section SteinerSymmetrization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The one-dimensional slice of `s : Set E` in direction `e : E` over `y : orthogonalHyperplane e`,
defined as `{t : ℝ | (y : E) + t • e ∈ s}`. -/
def steinerFiber (e : E) (s : Set E) (y : orthogonalHyperplane e) : Set ℝ :=
  {t : ℝ | (y : E) + t • e ∈ s}

@[simp]
theorem mem_steinerFiber_iff {e : E} {s : Set E} {y : orthogonalHyperplane e} {t : ℝ} :
    t ∈ steinerFiber e s y ↔ (y : E) + t • e ∈ s := by
  rfl

@[simp]
theorem steinerFiber_empty (e : E) (y : orthogonalHyperplane e) :
    steinerFiber e (∅ : Set E) y = ∅ := by
  rfl

@[simp]
theorem steinerFiber_univ (e : E) (y : orthogonalHyperplane e) :
    steinerFiber e (Set.univ : Set E) y = Set.univ := by
  rfl

theorem steinerFiber_mono {e : E} {s t : Set E} (hst : s ⊆ t) (y : orthogonalHyperplane e) :
    steinerFiber e s y ⊆ steinerFiber e t y :=
  fun _ hr ↦ hst hr

@[simp]
theorem steinerFiber_inter (e : E) (s t : Set E) (y : orthogonalHyperplane e) :
    steinerFiber e (s ∩ t) y = steinerFiber e s y ∩ steinerFiber e t y := by
  rfl

@[simp]
theorem steinerFiber_union (e : E) (s t : Set E) (y : orthogonalHyperplane e) :
    steinerFiber e (s ∪ t) y = steinerFiber e s y ∪ steinerFiber e t y := by
  rfl

@[simp]
theorem steinerFiber_sdiff (e : E) (s t : Set E) (y : orthogonalHyperplane e) :
    steinerFiber e (s \ t) y = steinerFiber e s y \ steinerFiber e t y := by
  rfl

@[simp]
theorem steinerFiber_compl (e : E) (s : Set E) (y : orthogonalHyperplane e) :
    steinerFiber e sᶜ y = (steinerFiber e s y)ᶜ := by
  rfl

@[simp]
theorem steinerFiber_symmDiff (e : E) (s t : Set E) (y : orthogonalHyperplane e) :
    steinerFiber e (symmDiff s t) y = symmDiff (steinerFiber e s y) (steinerFiber e t y) := by
  rfl

/-- Steiner symmetrization of a set `s : Set E` in direction `e : E`, replacing each fiber
`steinerFiber e s y` over `y : orthogonalHyperplane e` by
`symmetricInterval (steinerFiber e s y)`. -/
def steinerSymmetrization (e : E) (s : Set E) : Set E :=
  {x : E | ⟪x, e⟫_ℝ ∈
    symmetricInterval (steinerFiber e s ((orthogonalHyperplane e).orthogonalProjectionOnto x))}

theorem mem_steinerSymmetrization_iff {e : E} {s : Set E} {x : E} :
    x ∈ steinerSymmetrization e s ↔
      ⟪x, e⟫_ℝ ∈
        symmetricInterval
          (steinerFiber e s ((orthogonalHyperplane e).orthogonalProjectionOnto x)) := by
  rfl

theorem mem_steinerSymmetrization_iff_volume {e : E} {s : Set E} {x : E} :
    x ∈ steinerSymmetrization e s ↔
      volume (steinerFiber e s ((orthogonalHyperplane e).orthogonalProjectionOnto x)) ≠ 0 ∧
        ENNReal.ofReal (2 * |⟪x, e⟫_ℝ|) ≤
          volume (steinerFiber e s ((orthogonalHyperplane e).orthogonalProjectionOnto x)) :=
  mem_symmetricInterval_iff

@[simp]
theorem steinerSymmetrization_empty (e : E) :
    steinerSymmetrization e (∅ : Set E) = ∅ := by
  ext x
  simp [mem_steinerSymmetrization_iff]

@[simp]
theorem steinerSymmetrization_univ (e : E) :
    steinerSymmetrization e (Set.univ : Set E) = Set.univ := by
  ext x
  simp [mem_steinerSymmetrization_iff]

theorem steinerSymmetrization_mono {e : E} {s t : Set E} (hst : s ⊆ t) :
    steinerSymmetrization e s ⊆ steinerSymmetrization e t :=
  fun _ hx ↦ symmetricInterval_mono (steinerFiber_mono hst _) hx

@[simp]
theorem steinerFiber_steinerSymmetrization {e : E} (he : ‖e‖ = 1) (s : Set E)
    (y : orthogonalHyperplane e) :
    steinerFiber e (steinerSymmetrization e s) y = symmetricInterval (steinerFiber e s y) := by
  ext t
  simp [mem_steinerFiber_iff, mem_steinerSymmetrization_iff, he]

theorem volume_steinerFiber_steinerSymmetrization {e : E} (he : ‖e‖ = 1) (s : Set E)
    (y : orthogonalHyperplane e) :
    volume (steinerFiber e (steinerSymmetrization e s) y) = volume (steinerFiber e s y) := by
  rw [steinerFiber_steinerSymmetrization he, volume_symmetricInterval]

@[simp]
theorem steinerSymmetrization_idempotent {e : E} (he : ‖e‖ = 1) (s : Set E) :
    steinerSymmetrization e (steinerSymmetrization e s) = steinerSymmetrization e s := by
  ext x
  simp [mem_steinerSymmetrization_iff, steinerFiber_steinerSymmetrization he]

/-- Reflection symmetry of `steinerSymmetrization e s` across `orthogonalHyperplane e`. -/
@[simp]
theorem mem_steinerSymmetrization_reflection_iff (e : E) (s : Set E) (x : E) :
    (orthogonalHyperplane e).reflection x ∈ steinerSymmetrization e s ↔
      x ∈ steinerSymmetrization e s := by
  simp [mem_steinerSymmetrization_iff]

@[simp]
theorem preimage_reflection_steinerSymmetrization (e : E) (s : Set E) :
    (orthogonalHyperplane e).reflection ⁻¹' steinerSymmetrization e s =
      steinerSymmetrization e s := by
  ext x
  exact mem_steinerSymmetrization_reflection_iff e s x

@[simp]
theorem image_reflection_steinerSymmetrization (e : E) (s : Set E) :
    (orthogonalHyperplane e).reflection '' steinerSymmetrization e s =
      steinerSymmetrization e s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [mem_steinerSymmetrization_reflection_iff]
  · intro hx
    exact ⟨(orthogonalHyperplane e).reflection x,
      (mem_steinerSymmetrization_reflection_iff e s x).mpr hx,
      Submodule.reflection_reflection _ x⟩

/-- Equivariance of `steinerSymmetrization e` under reflection in any orthogonal hyperplane
`orthogonalHyperplane e'` with `⟪e, e'⟫_ℝ = 0`. -/
theorem preimage_reflection_orthogonal_steinerSymmetrization
    {e e' : E} (he : ‖e‖ = 1) (hee' : ⟪e, e'⟫_ℝ = 0) (s : Set E) :
    (orthogonalHyperplane e').reflection ⁻¹' steinerSymmetrization e s =
      steinerSymmetrization e ((orthogonalHyperplane e').reflection ⁻¹' s) := by
  set R' : E ≃ₗᵢ[ℝ] E := (orthogonalHyperplane e').reflection
  have hR'e : R' e = e :=
    Submodule.reflection_mem_subspace_eq_self (mem_orthogonalHyperplane_iff.mpr hee')
  have hR'inner : ∀ z : E, ⟪R' z, e⟫_ℝ = ⟪z, e⟫_ℝ := fun z ↦ by
    calc
      ⟪R' z, e⟫_ℝ = ⟪R' z, R' e⟫_ℝ := by rw [hR'e]
      _ = ⟪z, e⟫_ℝ := R'.inner_map_map z e
  have hR'proj : ∀ x : E,
      ((orthogonalHyperplane e).orthogonalProjectionOnto (R' x) : E) =
        R' ((orthogonalHyperplane e).orthogonalProjectionOnto x) := fun x ↦ by
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.coe_orthogonalProjectionOnto_apply,
      starProjection_orthogonalHyperplane_apply he, starProjection_orthogonalHyperplane_apply he,
      map_sub, map_smul, hR'inner, hR'e]
  ext x
  have hfiber :
      steinerFiber e s ((orthogonalHyperplane e).orthogonalProjectionOnto (R' x)) =
        steinerFiber e (R' ⁻¹' s) ((orthogonalHyperplane e).orthogonalProjectionOnto x) := by
    ext t
    have hpt :
        R' ((orthogonalHyperplane e).orthogonalProjectionOnto x) + t • e =
          R' (((orthogonalHyperplane e).orthogonalProjectionOnto x : E) + t • e) := by
      rw [map_add, map_smul, hR'e]
    simp only [mem_steinerFiber_iff, Set.mem_preimage, hR'proj, hpt]
  simp only [Set.mem_preimage, mem_steinerSymmetrization_iff, hR'inner, hfiber]

/-- If `s` is symmetric with respect to `orthogonalHyperplane e'` and `⟪e, e'⟫_ℝ = 0`, then
`steinerSymmetrization e s` is also symmetric with respect to `orthogonalHyperplane e'`. -/
theorem preimage_reflection_orthogonal_steinerSymmetrization_eq_self
    {e e' : E} (he : ‖e‖ = 1) (hee' : ⟪e, e'⟫_ℝ = 0) {s : Set E}
    (hs : (orthogonalHyperplane e').reflection ⁻¹' s = s) :
    (orthogonalHyperplane e').reflection ⁻¹' steinerSymmetrization e s =
      steinerSymmetrization e s := by
  rw [preimage_reflection_orthogonal_steinerSymmetrization he hee', hs]

theorem mem_steinerSymmetrization_reflection_orthogonal_iff
    {e e' : E} (he : ‖e‖ = 1) (hee' : ⟪e, e'⟫_ℝ = 0) {s : Set E}
    (hs : ∀ x, (orthogonalHyperplane e').reflection x ∈ s ↔ x ∈ s) (x : E) :
    (orthogonalHyperplane e').reflection x ∈ steinerSymmetrization e s ↔
      x ∈ steinerSymmetrization e s := by
  have hs' : (orthogonalHyperplane e').reflection ⁻¹' s = s := Set.ext hs
  exact Set.ext_iff.mp
    (preimage_reflection_orthogonal_steinerSymmetrization_eq_self he hee' hs') x

end SteinerSymmetrization

section MeasurabilityAndVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

@[measurability]
theorem measurableSet_steinerFiber {e : E} {s : Set E} (hs : MeasurableSet s)
    (y : orthogonalHyperplane e) :
    MeasurableSet (steinerFiber e s y) := by
  have hcont : Continuous fun t : ℝ ↦ (y : E) + t • e := by fun_prop
  exact hcont.measurable hs

@[fun_prop]
theorem measurable_volume_steinerFiber {e : E} {s : Set E} (hs : MeasurableSet s) :
    Measurable fun y : orthogonalHyperplane e ↦ volume (steinerFiber e s y) := by
  have hcont : Continuous fun p : orthogonalHyperplane e × ℝ ↦ (p.1 : E) + p.2 • e := by fun_prop
  exact measurable_measure_prodMk_left (hcont.measurable hs)

@[measurability]
theorem measurableSet_steinerSymmetrization {e : E} {s : Set E} (hs : MeasurableSet s) :
    MeasurableSet (steinerSymmetrization e s) := by
  let proj := (orthogonalHyperplane e).orthogonalProjectionOnto
  have hproj : Measurable (proj : E → orthogonalHyperplane e) := proj.continuous.measurable
  have hvol : Measurable fun x : E ↦ volume (steinerFiber e s (proj x)) :=
    (measurable_volume_steinerFiber hs).comp hproj
  have hnorm : Measurable fun x : E ↦ ENNReal.ofReal (2 * |⟪x, e⟫_ℝ|) := by fun_prop
  have heq : steinerSymmetrization e s =
      {x : E | volume (steinerFiber e s (proj x)) ≠ 0} ∩
        {x : E | ENNReal.ofReal (2 * |⟪x, e⟫_ℝ|) ≤ volume (steinerFiber e s (proj x))} := by
    ext x
    exact mem_steinerSymmetrization_iff_volume
  rw [heq]
  exact (hvol (measurableSet_singleton 0).compl).inter (measurableSet_le hnorm hvol)

theorem preimage_orthogonalHyperplaneProdMeasurableEquiv_steinerFiber
    {e : E} (he : ‖e‖ = 1) (s : Set E) (y : orthogonalHyperplane e) :
    Prod.mk y ⁻¹' (orthogonalHyperplaneProdMeasurableEquiv he ⁻¹' s) = steinerFiber e s y := by
  rfl

variable [FiniteDimensional ℝ E]

/-- Fubini slice formula for the volume of a measurable set along `orthogonalHyperplane e`. -/
theorem volume_eq_lintegral_steinerFiber {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : MeasurableSet s) :
    volume s = ∫⁻ y : orthogonalHyperplane e, volume (steinerFiber e s y) ∂volume := by
  rw [← (measurePreserving_orthogonalHyperplaneProdMeasurableEquiv he).measure_preimage_equiv s,
    Measure.prod_apply ((orthogonalHyperplaneProdMeasurableEquiv he).measurable hs)]
  rfl

/-- Fubini slice formula for the volume of a null-measurable set along `orthogonalHyperplane e`. -/
theorem volume_eq_lintegral_steinerFiber₀ {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = ∫⁻ y : orthogonalHyperplane e, volume (steinerFiber e s y) ∂volume := by
  have hmp := measurePreserving_orthogonalHyperplaneProdMeasurableEquiv he
  rw [← hmp.measure_preimage_equiv s,
    Measure.prod_apply₀ (hs.preimage hmp.quasiMeasurePreserving)]
  rfl

/-- If `s =ᵐ[volume] t`, then for a.e. `y : orthogonalHyperplane e` the fibers `steinerFiber e s y`
and `steinerFiber e t y` agree a.e. in one-dimensional Lebesgue measure. -/
theorem ae_steinerFiber_ae_eq {e : E} (he : ‖e‖ = 1) {s t : Set E} (hst : s =ᵐ[volume] t) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume,
      steinerFiber e s y =ᵐ[volume] steinerFiber e t y := by
  have hmp := measurePreserving_orthogonalHyperplaneProdMeasurableEquiv he
  have hpre :
      (orthogonalHyperplaneProdMeasurableEquiv he ⁻¹' s : Set (orthogonalHyperplane e × ℝ)) =ᵐ[
        (volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ)]
      orthogonalHyperplaneProdMeasurableEquiv he ⁻¹' t :=
    hmp.quasiMeasurePreserving.preimage_ae_eq hst
  exact Measure.ae_ae_of_ae_prod hpre

/-- If `s =ᵐ[volume] t`, then for a.e. `y : orthogonalHyperplane e` the fibers have the same
one-dimensional volume. -/
theorem ae_volume_steinerFiber_eq {e : E} (he : ‖e‖ = 1) {s t : Set E} (hst : s =ᵐ[volume] t) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume,
      volume (steinerFiber e s y) = volume (steinerFiber e t y) := by
  filter_upwards [ae_steinerFiber_ae_eq he hst] with y hy using measure_congr hy

/-- Steiner symmetrization respects `=ᵐ[volume]`: replacing `s` by a volume-a.e. equal set `t`
produces a volume-a.e. equal Steiner symmetral. -/
theorem steinerSymmetrization_ae_eq {e : E} (he : ‖e‖ = 1) {s t : Set E}
    (hst : s =ᵐ[volume] t) :
    steinerSymmetrization e s =ᵐ[volume] steinerSymmetrization e t := by
  have hprod : ∀ᵐ p : orthogonalHyperplane e × ℝ ∂
      ((volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ)),
      volume (steinerFiber e s p.1) = volume (steinerFiber e t p.1) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_volume_steinerFiber_eq he hst)
  have hmp := measurePreserving_orthogonalHyperplaneProdMeasurableEquiv_symm he
  have hE : ∀ᵐ x : E ∂volume,
      volume (steinerFiber e s ((orthogonalHyperplane e).orthogonalProjectionOnto x)) =
        volume (steinerFiber e t ((orthogonalHyperplane e).orthogonalProjectionOnto x)) := by
    have := hmp.quasiMeasurePreserving.ae hprod
    simpa using this
  filter_upwards [hE] with x hx
  exact propext (by
    rw [mem_steinerSymmetrization_iff, mem_steinerSymmetrization_iff,
      symmetricInterval_congr_volume hx])

@[measurability]
theorem nullMeasurableSet_steinerSymmetrization {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    NullMeasurableSet (steinerSymmetrization e s) volume := by
  rcases hs with ⟨t, htm, hst⟩
  exact (measurableSet_steinerSymmetrization htm).nullMeasurableSet.congr
    (steinerSymmetrization_ae_eq he hst).symm

/-- Steiner symmetrization preserves Lebesgue volume on measurable sets. -/
@[simp]
theorem volume_steinerSymmetrization {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : MeasurableSet s) :
    volume (steinerSymmetrization e s) = volume s := by
  rw [volume_eq_lintegral_steinerFiber he (measurableSet_steinerSymmetrization hs),
    volume_eq_lintegral_steinerFiber he hs]
  simp_rw [volume_steinerFiber_steinerSymmetrization he]

/-- Steiner symmetrization preserves Lebesgue volume on null-measurable sets. -/
theorem volume_steinerSymmetrization₀ {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume (steinerSymmetrization e s) = volume s := by
  rcases hs with ⟨t, htm, hst⟩
  rw [measure_congr (steinerSymmetrization_ae_eq he hst), volume_steinerSymmetrization he htm,
    measure_congr hst]

/-- Two-set intersection inequality (Riesz rearrangement inequality for indicators) under Steiner
symmetrization for measurable sets. -/
theorem volume_inter_le_volume_steinerSymmetrization_inter {e : E} (he : ‖e‖ = 1) {s t : Set E}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    volume (s ∩ t) ≤ volume (steinerSymmetrization e s ∩ steinerSymmetrization e t) := by
  rw [volume_eq_lintegral_steinerFiber he (hs.inter ht),
    volume_eq_lintegral_steinerFiber he
      ((measurableSet_steinerSymmetrization hs).inter (measurableSet_steinerSymmetrization ht))]
  refine lintegral_mono fun y ↦ ?_
  simp only [steinerFiber_inter, steinerFiber_steinerSymmetrization he]
  exact volume_inter_le_volume_symmetricInterval_inter _ _

/-- Two-set intersection inequality under Steiner symmetrization for null-measurable sets. -/
theorem volume_inter_le_volume_steinerSymmetrization_inter₀ {e : E} (he : ‖e‖ = 1) {s t : Set E}
    (hs : NullMeasurableSet s volume) (ht : NullMeasurableSet t volume) :
    volume (s ∩ t) ≤ volume (steinerSymmetrization e s ∩ steinerSymmetrization e t) := by
  rcases hs with ⟨s', hs'm, hss'⟩
  rcases ht with ⟨t', ht'm, htt'⟩
  rw [measure_congr (hss'.inter htt'),
    measure_congr
      ((steinerSymmetrization_ae_eq he hss').inter (steinerSymmetrization_ae_eq he htt'))]
  exact volume_inter_le_volume_steinerSymmetrization_inter he hs'm ht'm

/-- `L¹` contraction on symmetric differences under Steiner symmetrization for measurable sets. -/
theorem volume_symmDiff_steinerSymmetrization_le {e : E} (he : ‖e‖ = 1) {s t : Set E}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    volume (symmDiff (steinerSymmetrization e s) (steinerSymmetrization e t)) ≤
      volume (symmDiff s t) := by
  rw [volume_eq_lintegral_steinerFiber he
      ((measurableSet_steinerSymmetrization hs).symmDiff (measurableSet_steinerSymmetrization ht)),
    volume_eq_lintegral_steinerFiber he (hs.symmDiff ht)]
  refine lintegral_mono fun y ↦ ?_
  simp only [steinerFiber_symmDiff, steinerFiber_steinerSymmetrization he]
  exact volume_symmDiff_symmetricInterval_le _ _

/-- `L¹` contraction on symmetric differences under Steiner symmetrization for null-measurable
sets. -/
theorem volume_symmDiff_steinerSymmetrization_le₀ {e : E} (he : ‖e‖ = 1) {s t : Set E}
    (hs : NullMeasurableSet s volume) (ht : NullMeasurableSet t volume) :
    volume (symmDiff (steinerSymmetrization e s) (steinerSymmetrization e t)) ≤
      volume (symmDiff s t) := by
  rcases hs with ⟨s', hs'm, hss'⟩
  rcases ht with ⟨t', ht'm, htt'⟩
  rw [measure_congr (hss'.symmDiff htt'),
    measure_congr
      ((steinerSymmetrization_ae_eq he hss').symmDiff (steinerSymmetrization_ae_eq he htt'))]
  exact volume_symmDiff_steinerSymmetrization_le he hs'm ht'm

end MeasurabilityAndVolume

section BallsAndDiameter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem steinerFiber_ball_zero {e : E} (he : ‖e‖ = 1) (r : ℝ) (y : orthogonalHyperplane e) :
    steinerFiber e (Metric.ball (0 : E) r) y =
      if ‖y‖ < r then Set.Ioo (-Real.sqrt (r ^ 2 - ‖y‖ ^ 2)) (Real.sqrt (r ^ 2 - ‖y‖ ^ 2))
      else ∅ := by
  ext t
  simp only [mem_steinerFiber_iff, Metric.mem_ball, dist_zero_right]
  split_ifs with hy
  · have hr : 0 ≤ r := le_of_lt (lt_of_le_of_lt (norm_nonneg y) hy)
    have hsub : 0 ≤ r ^ 2 - ‖y‖ ^ 2 := sub_nonneg.mpr (sq_le_sq₀ (norm_nonneg y) hr |>.mpr hy.le)
    rw [Set.mem_Ioo, ← abs_lt, ← sq_lt_sq₀ (abs_nonneg t) (Real.sqrt_nonneg _),
      sq_abs, Real.sq_sqrt hsub, lt_sub_iff_add_lt', ← norm_coe_add_smul_sq he y t,
      sq_lt_sq₀ (norm_nonneg _) hr]
  · simp only [Set.mem_empty_iff_false, iff_false, not_lt]
    have hle : ‖y‖ ≤ ‖(y : E) + t • e‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_coe_add_smul_sq he]
      linarith [sq_nonneg t]
    exact le_trans (not_lt.mp hy) hle

theorem steinerFiber_closedBall_zero {e : E} (he : ‖e‖ = 1) (r : ℝ)
    (y : orthogonalHyperplane e) :
    steinerFiber e (Metric.closedBall (0 : E) r) y =
      if 0 ≤ r ∧ ‖y‖ ≤ r then Set.Icc (-Real.sqrt (r ^ 2 - ‖y‖ ^ 2)) (Real.sqrt (r ^ 2 - ‖y‖ ^ 2))
      else ∅ := by
  ext t
  simp only [mem_steinerFiber_iff, Metric.mem_closedBall, dist_zero_right]
  split_ifs with hy
  · have hsub : 0 ≤ r ^ 2 - ‖y‖ ^ 2 :=
      sub_nonneg.mpr (sq_le_sq₀ (norm_nonneg y) hy.1 |>.mpr hy.2)
    rw [Set.mem_Icc, ← abs_le, ← sq_le_sq₀ (abs_nonneg t) (Real.sqrt_nonneg _),
      sq_abs, Real.sq_sqrt hsub, le_sub_iff_add_le', ← norm_coe_add_smul_sq he y t,
      sq_le_sq₀ (norm_nonneg _) hy.1]
  · simp only [Set.mem_empty_iff_false, iff_false]
    intro hle
    have hyr : ‖y‖ ≤ r := by
      have : ‖y‖ ≤ ‖(y : E) + t • e‖ := by
        rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_coe_add_smul_sq he]
        linarith [sq_nonneg t]
      exact le_trans this hle
    exact hy ⟨le_trans (norm_nonneg y) hyr, hyr⟩

theorem volume_steinerFiber_ball_zero_eq_closedBall_zero {e : E} (he : ‖e‖ = 1) (r : ℝ)
    (y : orthogonalHyperplane e) :
    volume (steinerFiber e (Metric.ball (0 : E) r) y) =
      volume (steinerFiber e (Metric.closedBall (0 : E) r) y) := by
  rw [steinerFiber_ball_zero he, steinerFiber_closedBall_zero he]
  split_ifs with h1 h2 h2
  · rw [Real.volume_Ioo, Real.volume_Icc]
  · exfalso
    exact h2 ⟨le_of_lt (lt_of_le_of_lt (norm_nonneg y) h1), h1.le⟩
  · have heq : ‖y‖ = r := le_antisymm h2.2 (not_lt.mp h1)
    simp [heq]
  · rfl

theorem steinerSymmetrization_ball_eq_steinerSymmetrization_closedBall
    {e : E} (he : ‖e‖ = 1) (r : ℝ) :
    steinerSymmetrization e (Metric.ball (0 : E) r) =
      steinerSymmetrization e (Metric.closedBall (0 : E) r) := by
  ext x
  simp only [mem_steinerSymmetrization_iff]
  rw [symmetricInterval_congr_volume (volume_steinerFiber_ball_zero_eq_closedBall_zero he r _)]

theorem mem_steinerSymmetrization_ball_zero_iff {e : E} (he : ‖e‖ = 1) {r : ℝ} {x : E} :
    x ∈ steinerSymmetrization e (Metric.ball (0 : E) r) ↔
      ‖(orthogonalHyperplane e).orthogonalProjectionOnto x‖ < r ∧ ‖x‖ ≤ r := by
  set y := (orthogonalHyperplane e).orthogonalProjectionOnto x
  set t := ⟪x, e⟫_ℝ
  have hx : x = (y : E) + t • e :=
    (orthogonalProjection_orthogonalHyperplane_add_inner_smul he x).symm
  have hnorm : ‖x‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
    rw [hx, norm_coe_add_smul_sq he]
  rw [mem_steinerSymmetrization_iff, steinerFiber_ball_zero he r y]
  split_ifs with hy
  · have hr : 0 ≤ r := le_of_lt (lt_of_le_of_lt (norm_nonneg y) hy)
    have hpos : 0 < Real.sqrt (r ^ 2 - ‖y‖ ^ 2) :=
      Real.sqrt_pos.mpr (sub_pos.mpr (sq_lt_sq₀ (norm_nonneg y) hr |>.mpr hy))
    have hvol : volume (Set.Ioo (-Real.sqrt (r ^ 2 - ‖y‖ ^ 2)) (Real.sqrt (r ^ 2 - ‖y‖ ^ 2))) =
        ENNReal.ofReal (2 * Real.sqrt (r ^ 2 - ‖y‖ ^ 2)) := by
      rw [Real.volume_Ioo, sub_neg_eq_add, two_mul]
    rw [mem_symmetricInterval_iff, hvol]
    have hne : ENNReal.ofReal (2 * Real.sqrt (r ^ 2 - ‖y‖ ^ 2)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity), mul_le_mul_iff_right₀ zero_lt_two,
      ← sq_le_sq₀ (abs_nonneg t) (Real.sqrt_nonneg _), sq_abs,
      Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp hpos)),
      le_sub_iff_add_le', ← hnorm, sq_le_sq₀ (norm_nonneg x) hr]
    exact ⟨fun h ↦ ⟨hy, h.2⟩, fun h ↦ ⟨hne, h.2⟩⟩
  · rw [symmetricInterval_empty]
    exact ⟨fun h ↦ False.elim (Set.notMem_empty _ h), fun h ↦ False.elim (hy h.1)⟩

theorem ball_subset_steinerSymmetrization_ball {e : E} (he : ‖e‖ = 1) (r : ℝ) :
    Metric.ball (0 : E) r ⊆ steinerSymmetrization e (Metric.ball (0 : E) r) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [mem_steinerSymmetrization_ball_zero_iff he]
  exact ⟨lt_of_le_of_lt (Submodule.norm_orthogonalProjectionOnto_apply_le _ x) hx, hx.le⟩

theorem steinerSymmetrization_ball_subset_closedBall {e : E} (he : ‖e‖ = 1) (r : ℝ) :
    steinerSymmetrization e (Metric.ball (0 : E) r) ⊆ Metric.closedBall (0 : E) r := by
  intro x hx
  rw [mem_steinerSymmetrization_ball_zero_iff he] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hx.2

theorem steinerSymmetrization_closedBall_subset_closedBall {e : E} (he : ‖e‖ = 1) (r : ℝ) :
    steinerSymmetrization e (Metric.closedBall (0 : E) r) ⊆ Metric.closedBall (0 : E) r := by
  rw [← steinerSymmetrization_ball_eq_steinerSymmetrization_closedBall he]
  exact steinerSymmetrization_ball_subset_closedBall he r

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Steiner symmetrization preserves open balls centered at the origin up to a set of volume
zero. -/
theorem steinerSymmetrization_ball_ae_eq {e : E} (he : ‖e‖ = 1) (r : ℝ) :
    steinerSymmetrization e (Metric.ball (0 : E) r) =ᵐ[volume] Metric.ball (0 : E) r := by
  have : Nontrivial E := ⟨⟨e, 0, fun h ↦ by simp [h] at he⟩⟩
  have hsub₁ := ball_subset_steinerSymmetrization_ball he r
  have hsub₂ := steinerSymmetrization_ball_subset_closedBall he r
  have hdiff :
      volume (steinerSymmetrization e (Metric.ball (0 : E) r) \ Metric.ball (0 : E) r) = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc
      volume (steinerSymmetrization e (Metric.ball (0 : E) r) \ Metric.ball (0 : E) r)
        ≤ volume (Metric.closedBall (0 : E) r \ Metric.ball (0 : E) r) :=
          measure_mono (Set.sdiff_subset_sdiff_left hsub₂)
      _ = volume (Metric.closedBall (0 : E) r) - volume (Metric.ball (0 : E) r) :=
          measure_sdiff Metric.ball_subset_closedBall measurableSet_ball.nullMeasurableSet
            measure_ball_lt_top.ne
      _ = 0 := by rw [Measure.addHaar_closedBall_eq_addHaar_ball, tsub_self]
  exact ae_eq_set.mpr ⟨hdiff, by rw [Set.sdiff_eq_empty.mpr hsub₁, measure_empty]⟩

/-- Steiner symmetrization preserves closed balls centered at the origin up to a set of volume
zero. -/
theorem steinerSymmetrization_closedBall_ae_eq {e : E} (he : ‖e‖ = 1) (r : ℝ) :
    steinerSymmetrization e (Metric.closedBall (0 : E) r) =ᵐ[volume]
      Metric.closedBall (0 : E) r := by
  have : Nontrivial E := ⟨⟨e, 0, fun h ↦ by simp [h] at he⟩⟩
  rw [← steinerSymmetrization_ball_eq_steinerSymmetrization_closedBall he]
  refine (steinerSymmetrization_ball_ae_eq he r).trans ?_
  have hdiff : volume (Metric.closedBall (0 : E) r \ Metric.ball (0 : E) r) = 0 := by
    rw [measure_sdiff Metric.ball_subset_closedBall measurableSet_ball.nullMeasurableSet
      measure_ball_lt_top.ne, Measure.addHaar_closedBall_eq_addHaar_ball, tsub_self]
  exact ae_eq_set.mpr
    ⟨by rw [Set.sdiff_eq_empty.mpr Metric.ball_subset_closedBall, measure_empty], hdiff⟩

end BallsAndDiameter

section DiameterNonExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma abs_sub_add_abs_sub_le {a₁ b₁ a₂ b₂ M : ℝ}
    (h11 : |a₁ - a₂| ≤ M) (h12 : |a₁ - b₂| ≤ M)
    (h21 : |b₁ - a₂| ≤ M) (h22 : |b₁ - b₂| ≤ M) :
    |a₁ - b₁| + |a₂ - b₂| ≤ 2 * M := by
  rcases abs_cases (a₁ - b₁) with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;>
    rcases abs_cases (a₂ - b₂) with ⟨h₂, _⟩ | ⟨h₂, _⟩ <;>
    linarith [(abs_le.mp h11).1, (abs_le.mp h11).2, (abs_le.mp h12).1, (abs_le.mp h12).2,
      (abs_le.mp h21).1, (abs_le.mp h21).2, (abs_le.mp h22).1, (abs_le.mp h22).2]

theorem ediam_steinerFiber_le {e : E} (he : ‖e‖ = 1) (s : Set E) (y : orthogonalHyperplane e) :
    Metric.ediam (steinerFiber e s y) ≤ Metric.ediam s := by
  refine Metric.ediam_le fun t₁ ht₁ t₂ ht₂ ↦ ?_
  have hdist : edist t₁ t₂ = edist ((y : E) + t₁ • e) ((y : E) + t₂ • e) := by
    rw [edist_dist, edist_dist, Real.dist_eq, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul,
      norm_smul, Real.norm_eq_abs, he, mul_one]
  rw [hdist]
  exact Metric.edist_le_ediam_of_mem ht₁ ht₂

theorem isBounded_steinerFiber {e : E} (he : ‖e‖ = 1) {s : Set E} (hs : Bornology.IsBounded s)
    (y : orthogonalHyperplane e) :
    Bornology.IsBounded (steinerFiber e s y) := by
  rw [Metric.isBounded_iff_ediam_ne_top] at hs ⊢
  exact ne_top_of_le_ne_top hs (ediam_steinerFiber_le he s y)

/-- Steiner symmetrization in a unit direction `e` does not increase the extended diameter
`Metric.ediam`. -/
theorem ediam_steinerSymmetrization_le {e : E} (he : ‖e‖ = 1) (s : Set E) :
    Metric.ediam (steinerSymmetrization e s) ≤ Metric.ediam s := by
  by_cases hs : Bornology.IsBounded s
  · rw [← ENNReal.ofReal_toReal hs.ediam_ne_top, ← Metric.diam]
    refine Metric.ediam_le fun x₁ hx₁ x₂ hx₂ ↦ ?_
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    set y₁ := (orthogonalHyperplane e).orthogonalProjectionOnto x₁
    set t₁ := ⟪x₁, e⟫_ℝ
    set y₂ := (orthogonalHyperplane e).orthogonalProjectionOnto x₂
    set t₂ := ⟪x₂, e⟫_ℝ
    set F₁ := steinerFiber e s y₁
    set F₂ := steinerFiber e s y₂
    have hx₁_eq : x₁ = (y₁ : E) + t₁ • e :=
      (orthogonalProjection_orthogonalHyperplane_add_inner_smul he x₁).symm
    have hx₂_eq : x₂ = (y₂ : E) + t₂ • e :=
      (orthogonalProjection_orthogonalHyperplane_add_inner_smul he x₂).symm
    have hpyth_x : dist x₁ x₂ ^ 2 = ‖(y₁ - y₂ : orthogonalHyperplane e)‖ ^ 2 + (t₁ - t₂) ^ 2 := by
      rw [dist_eq_norm, hx₁_eq, hx₂_eq,
        show ((y₁ : E) + t₁ • e) - ((y₂ : E) + t₂ • e) =
          ((y₁ - y₂ : orthogonalHyperplane e) : E) + (t₁ - t₂) • e by
          simp only [Submodule.coe_sub, sub_smul]; abel,
        norm_coe_add_smul_sq he]
    have hF₁_mem : volume F₁ ≠ 0 ∧ ENNReal.ofReal (2 * |t₁|) ≤ volume F₁ :=
      mem_steinerSymmetrization_iff_volume.mp hx₁
    have hF₂_mem : volume F₂ ≠ 0 ∧ ENNReal.ofReal (2 * |t₂|) ≤ volume F₂ :=
      mem_steinerSymmetrization_iff_volume.mp hx₂
    have hF₁_ne : F₁.Nonempty := nonempty_of_measure_ne_zero hF₁_mem.1
    have hF₂_ne : F₂.Nonempty := nonempty_of_measure_ne_zero hF₂_mem.1
    have hF₁_bdd : Bornology.IsBounded F₁ := isBounded_steinerFiber he hs y₁
    have hF₂_bdd : Bornology.IsBounded F₂ := isBounded_steinerFiber he hs y₂
    have hF₁_vol : volume F₁ ≤ ENNReal.ofReal (Metric.diam F₁) := by
      rw [Metric.diam, ENNReal.ofReal_toReal hF₁_bdd.ediam_ne_top]
      exact Real.volume_le_diam F₁
    have hF₂_vol : volume F₂ ≤ ENNReal.ofReal (Metric.diam F₂) := by
      rw [Metric.diam, ENNReal.ofReal_toReal hF₂_bdd.ediam_ne_top]
      exact Real.volume_le_diam F₂
    have ht₁_le : 2 * |t₁| ≤ Metric.diam F₁ :=
      (ENNReal.ofReal_le_ofReal_iff Metric.diam_nonneg).mp (hF₁_mem.2.trans hF₁_vol)
    have ht₂_le : 2 * |t₂| ≤ Metric.diam F₂ :=
      (ENNReal.ofReal_le_ofReal_iff Metric.diam_nonneg).mp (hF₂_mem.2.trans hF₂_vol)
    have hpyth_uv : ∀ u ∈ F₁, ∀ v ∈ F₂,
        ‖(y₁ - y₂ : orthogonalHyperplane e)‖ ^ 2 + (u - v) ^ 2 ≤ Metric.diam s ^ 2 := by
      intro u hu v hv
      have hdist : ‖((y₁ : E) + u • e) - ((y₂ : E) + v • e)‖ ≤ Metric.diam s := by
        rw [← dist_eq_norm]
        exact Metric.dist_le_diam_of_mem hs hu hv
      have heq : ‖((y₁ : E) + u • e) - ((y₂ : E) + v • e)‖ ^ 2 =
          ‖(y₁ - y₂ : orthogonalHyperplane e)‖ ^ 2 + (u - v) ^ 2 := by
        rw [show ((y₁ : E) + u • e) - ((y₂ : E) + v • e) =
            ((y₁ - y₂ : orthogonalHyperplane e) : E) + (u - v) • e by
            simp only [Submodule.coe_sub, sub_smul]; abel,
          norm_coe_add_smul_sq he]
      rw [← heq]
      exact sq_le_sq₀ (norm_nonneg _) Metric.diam_nonneg |>.mpr hdist
    rcases hF₁_ne with ⟨u₀, hu₀⟩
    rcases hF₂_ne with ⟨v₀, hv₀⟩
    have hy_le : ‖(y₁ - y₂ : orthogonalHyperplane e)‖ ^ 2 ≤ Metric.diam s ^ 2 := by
      linarith [hpyth_uv u₀ hu₀ v₀ hv₀, sq_nonneg (u₀ - v₀)]
    set M := Real.sqrt (Metric.diam s ^ 2 - ‖(y₁ - y₂ : orthogonalHyperplane e)‖ ^ 2)
    have hM_nonneg : 0 ≤ M := Real.sqrt_nonneg _
    have huv_le : ∀ u ∈ F₁, ∀ v ∈ F₂, |u - v| ≤ M := by
      intro u hu v hv
      rw [← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt ?_
      linarith [hpyth_uv u hu v hv]
    have hsum_dist : ∀ a₁ ∈ F₁, ∀ b₁ ∈ F₁, ∀ a₂ ∈ F₂, ∀ b₂ ∈ F₂,
        dist a₁ b₁ + dist a₂ b₂ ≤ 2 * M := by
      intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
      rw [Real.dist_eq, Real.dist_eq]
      exact abs_sub_add_abs_sub_le
        (huv_le a₁ ha₁ a₂ ha₂) (huv_le a₁ ha₁ b₂ hb₂)
        (huv_le b₁ hb₁ a₂ ha₂) (huv_le b₁ hb₁ b₂ hb₂)
    have hdiam₁ : ∀ a₂ ∈ F₂, ∀ b₂ ∈ F₂, Metric.diam F₁ ≤ 2 * M - dist a₂ b₂ := by
      intro a₂ ha₂ b₂ hb₂
      refine Metric.diam_le_of_forall_dist_le ?_ (fun a₁ ha₁ b₁ hb₁ ↦ ?_)
      · have := hsum_dist u₀ hu₀ u₀ hu₀ a₂ ha₂ b₂ hb₂
        linarith [dist_self u₀]
      · linarith [hsum_dist a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂]
    have hdiam_sum : Metric.diam F₁ + Metric.diam F₂ ≤ 2 * M := by
      have h₂ : Metric.diam F₂ ≤ 2 * M - Metric.diam F₁ := by
        refine Metric.diam_le_of_forall_dist_le ?_ (fun a₂ ha₂ b₂ hb₂ ↦ ?_)
        · have := hdiam₁ v₀ hv₀ v₀ hv₀
          linarith [dist_self v₀]
        · linarith [hdiam₁ a₂ ha₂ b₂ hb₂]
      linarith
    have ht_diff : |t₁ - t₂| ≤ M := by
      have htri : 2 * |t₁ - t₂| ≤ 2 * |t₁| + 2 * |t₂| := by
        linarith [abs_sub t₁ t₂]
      linarith
    have ht_sq : (t₁ - t₂) ^ 2 ≤
        Metric.diam s ^ 2 - ‖(y₁ - y₂ : orthogonalHyperplane e)‖ ^ 2 := by
      have := sq_le_sq₀ (abs_nonneg (t₁ - t₂)) hM_nonneg |>.mpr ht_diff
      rwa [sq_abs, Real.sq_sqrt (sub_nonneg.mpr hy_le)] at this
    rw [← sq_le_sq₀ dist_nonneg Metric.diam_nonneg, hpyth_x]
    linarith
  · rw [Metric.ediam_of_unbounded hs]
    exact le_top

/-- Steiner symmetrization of a bounded set in a unit direction is bounded. -/
theorem isBounded_steinerSymmetrization {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (steinerSymmetrization e s) := by
  rw [Metric.isBounded_iff_ediam_ne_top] at hs ⊢
  exact ne_top_of_le_ne_top hs (ediam_steinerSymmetrization_le he s)

/-- Steiner symmetrization of a bounded set in a unit direction `e` does not increase
`Metric.diam`. -/
theorem diam_steinerSymmetrization_le {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : Bornology.IsBounded s) :
    Metric.diam (steinerSymmetrization e s) ≤ Metric.diam s :=
  ENNReal.toReal_mono hs.ediam_ne_top (ediam_steinerSymmetrization_le he s)

end DiameterNonExpansion

section IsodiametricInequality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Any bounded origin-symmetric set `s : Set E` is contained in the closed ball centered at `0` of
radius `Metric.diam s / 2`. -/
theorem subset_closedBall_diam_div_two_of_neg_mem {s : Set E} (hs : Bornology.IsBounded s)
    (hs_symm : ∀ x ∈ s, -x ∈ s) :
    s ⊆ Metric.closedBall (0 : E) (Metric.diam s / 2) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ zero_lt_two]
  have hdist : dist x (-x) ≤ Metric.diam s :=
    Metric.dist_le_diam_of_mem hs hx (hs_symm x hx)
  have htwo : dist x (-x) = ‖x‖ * 2 := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul, Real.norm_ofNat, mul_comm]
  rwa [htwo] at hdist

/-- Iterated Steiner symmetrization along a list of directions `l : List E`, applied from left to
right. -/
def steinerSymmetrizationList (l : List E) (s : Set E) : Set E :=
  l.foldl (fun acc e ↦ steinerSymmetrization e acc) s

@[simp]
theorem steinerSymmetrizationList_nil (s : Set E) :
    steinerSymmetrizationList ([] : List E) s = s := by
  rfl

@[simp]
theorem steinerSymmetrizationList_cons (e : E) (l : List E) (s : Set E) :
    steinerSymmetrizationList (e :: l) s =
      steinerSymmetrizationList l (steinerSymmetrization e s) := by
  rfl

theorem ediam_steinerSymmetrizationList_le {l : List E} (hl : ∀ e ∈ l, ‖e‖ = 1) (s : Set E) :
    Metric.ediam (steinerSymmetrizationList l s) ≤ Metric.ediam s := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons e l ih =>
    rw [steinerSymmetrizationList_cons]
    exact (ih (fun e' he' ↦ hl e' (List.mem_cons_of_mem e he')) _).trans
      (ediam_steinerSymmetrization_le (hl e List.mem_cons_self) s)

theorem isBounded_steinerSymmetrizationList {l : List E} (hl : ∀ e ∈ l, ‖e‖ = 1) {s : Set E}
    (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (steinerSymmetrizationList l s) := by
  rw [Metric.isBounded_iff_ediam_ne_top] at hs ⊢
  exact ne_top_of_le_ne_top hs (ediam_steinerSymmetrizationList_le hl s)

theorem diam_steinerSymmetrizationList_le {l : List E} (hl : ∀ e ∈ l, ‖e‖ = 1) {s : Set E}
    (hs : Bornology.IsBounded s) :
    Metric.diam (steinerSymmetrizationList l s) ≤ Metric.diam s :=
  ENNReal.toReal_mono hs.ediam_ne_top (ediam_steinerSymmetrizationList_le hl s)

theorem preimage_reflection_steinerSymmetrizationList_of_forall_ortho
    {l : List E} {e' : E} (hl : ∀ e ∈ l, ‖e‖ = 1) (hortho : ∀ e ∈ l, ⟪e, e'⟫_ℝ = 0)
    {s : Set E} (hs : (orthogonalHyperplane e').reflection ⁻¹' s = s) :
    (orthogonalHyperplane e').reflection ⁻¹' steinerSymmetrizationList l s =
      steinerSymmetrizationList l s := by
  induction l generalizing s with
  | nil => exact hs
  | cons e l ih =>
    rw [steinerSymmetrizationList_cons]
    refine ih (fun u hu ↦ hl u (List.mem_cons_of_mem e hu))
      (fun u hu ↦ hortho u (List.mem_cons_of_mem e hu)) ?_
    exact preimage_reflection_orthogonal_steinerSymmetrization_eq_self
      (hl e List.mem_cons_self) (hortho e List.mem_cons_self) hs

theorem preimage_reflection_steinerSymmetrizationList_of_mem
    {l : List E} (hl : ∀ e ∈ l, ‖e‖ = 1) (hpair : l.Pairwise (fun e₁ e₂ ↦ ⟪e₁, e₂⟫_ℝ = 0))
    (s : Set E) {e : E} (he : e ∈ l) :
    (orthogonalHyperplane e).reflection ⁻¹' steinerSymmetrizationList l s =
      steinerSymmetrizationList l s := by
  induction l generalizing s with
  | nil => nomatch he
  | cons u l ih =>
    rw [List.pairwise_cons] at hpair
    rw [List.mem_cons] at he
    rw [steinerSymmetrizationList_cons]
    rcases he with rfl | he
    · refine preimage_reflection_steinerSymmetrizationList_of_forall_ortho
        (fun v hv ↦ hl v (List.mem_cons_of_mem e hv))
        (fun v hv ↦ by rw [real_inner_comm]; exact hpair.1 v hv)
        (preimage_reflection_steinerSymmetrization e s)
    · exact ih (fun v hv ↦ hl v (List.mem_cons_of_mem u hv)) hpair.2
        (steinerSymmetrization u s) he

/-- Composition of hyperplane reflections along a list of directions `l : List E`. -/
def reflectionList (l : List E) : E ≃ₗᵢ[ℝ] E :=
  l.foldl (fun acc e ↦ acc.trans (orthogonalHyperplane e).reflection)
    (LinearIsometryEquiv.refl ℝ E)

theorem reflectionList_foldl_apply (l : List E) (f : E ≃ₗᵢ[ℝ] E) (x : E) :
    (l.foldl (fun acc e ↦ acc.trans (orthogonalHyperplane e).reflection) f) x =
      l.foldl (fun z e ↦ (orthogonalHyperplane e).reflection z) (f x) := by
  induction l generalizing f with
  | nil => rfl
  | cons e l ih =>
    simp only [List.foldl_cons]
    exact ih (f.trans (orthogonalHyperplane e).reflection)

theorem reflectionList_apply (l : List E) (x : E) :
    reflectionList l x = l.foldl (fun z e ↦ (orthogonalHyperplane e).reflection z) x :=
  reflectionList_foldl_apply l (LinearIsometryEquiv.refl ℝ E) x

private theorem foldl_reflection_mem {l : List E} {s : Set E}
    (h : ∀ e ∈ l, (orthogonalHyperplane e).reflection ⁻¹' s = s) {x : E} (hx : x ∈ s) :
    l.foldl (fun z e ↦ (orthogonalHyperplane e).reflection z) x ∈ s := by
  induction l generalizing x with
  | nil => exact hx
  | cons e l ih =>
    simp only [List.foldl_cons]
    refine ih (fun u hu ↦ h u (List.mem_cons_of_mem e hu)) ?_
    have he := h e List.mem_cons_self
    rwa [← Set.mem_preimage, he]

private theorem foldl_reflection_eq_self_of_forall_ortho {l : List E} {v : E}
    (hortho : ∀ e ∈ l, ⟪v, e⟫_ℝ = 0) :
    l.foldl (fun z e ↦ (orthogonalHyperplane e).reflection z) v = v := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.foldl_cons]
    rw [Submodule.reflection_mem_subspace_eq_self
      (mem_orthogonalHyperplane_iff.mpr (hortho e List.mem_cons_self))]
    exact ih (fun u hu ↦ hortho u (List.mem_cons_of_mem e hu))

private theorem reflectionList_apply_eq_neg_of_mem {l : List E}
    (hpair : l.Pairwise (fun e₁ e₂ ↦ ⟪e₁, e₂⟫_ℝ = 0)) {e : E} (he : e ∈ l) :
    reflectionList l e = -e := by
  rw [reflectionList_apply]
  induction l with
  | nil => nomatch he
  | cons u l ih =>
    rw [List.pairwise_cons] at hpair
    rw [List.mem_cons] at he
    simp only [List.foldl_cons]
    rcases he with rfl | he
    · rw [reflection_orthogonalHyperplane_self]
      exact foldl_reflection_eq_self_of_forall_ortho fun v hv ↦ by
        rw [inner_neg_left, hpair.1 v hv, neg_zero]
    · have hue : ⟪e, u⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact hpair.1 e he
      rw [Submodule.reflection_mem_subspace_eq_self (mem_orthogonalHyperplane_iff.mpr hue)]
      exact ih hpair.2 he

/-- Iterated Steiner symmetrization along an orthonormal basis
`b : OrthonormalBasis (Fin n) ℝ E`. -/
def steinerSymmetrizationBasis {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (s : Set E) : Set E :=
  steinerSymmetrizationList ((List.finRange n).map b) s

theorem norm_eq_one_of_mem_map_finRange {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) :
    ∀ e ∈ (List.finRange n).map b, ‖e‖ = 1 := by
  intro e he
  rcases List.mem_map.mp he with ⟨i, _, rfl⟩
  exact b.norm_eq_one i

theorem pairwise_ortho_map_finRange {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) :
    ((List.finRange n).map b).Pairwise (fun e₁ e₂ ↦ ⟪e₁, e₂⟫_ℝ = 0) := by
  rw [List.pairwise_map]
  exact (List.nodup_finRange n).imp fun hij ↦ b.orthonormal.2 hij

theorem ediam_steinerSymmetrizationBasis_le {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (s : Set E) :
    Metric.ediam (steinerSymmetrizationBasis b s) ≤ Metric.ediam s :=
  ediam_steinerSymmetrizationList_le (norm_eq_one_of_mem_map_finRange b) s

theorem isBounded_steinerSymmetrizationBasis {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    {s : Set E} (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (steinerSymmetrizationBasis b s) :=
  isBounded_steinerSymmetrizationList (norm_eq_one_of_mem_map_finRange b) hs

theorem diam_steinerSymmetrizationBasis_le {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    {s : Set E} (hs : Bornology.IsBounded s) :
    Metric.diam (steinerSymmetrizationBasis b s) ≤ Metric.diam s :=
  diam_steinerSymmetrizationList_le (norm_eq_one_of_mem_map_finRange b) hs

@[simp]
theorem preimage_reflection_steinerSymmetrizationBasis {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (s : Set E) (i : Fin n) :
    (orthogonalHyperplane (b i)).reflection ⁻¹' steinerSymmetrizationBasis b s =
      steinerSymmetrizationBasis b s :=
  preimage_reflection_steinerSymmetrizationList_of_mem
    (norm_eq_one_of_mem_map_finRange b) (pairwise_ortho_map_finRange b) s
    (List.mem_map_of_mem (List.mem_finRange i))

theorem reflectionList_map_finRange_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (x : E) :
    reflectionList ((List.finRange n).map b) x = -x := by
  conv_lhs => rw [← b.sum_repr' x]
  rw [map_sum]
  have hterm : ∀ i : Fin n,
      reflectionList ((List.finRange n).map b) (⟪b i, x⟫_ℝ • b i) = -(⟪b i, x⟫_ℝ • b i) := by
    intro i
    rw [map_smul,
      reflectionList_apply_eq_neg_of_mem (pairwise_ortho_map_finRange b)
        (List.mem_map_of_mem (List.mem_finRange i)),
      smul_neg]
  simp_rw [hterm, Finset.sum_neg_distrib, b.sum_repr' x]

/-- Iterated Steiner symmetrization along an orthonormal basis produces an origin-symmetric set. -/
theorem neg_mem_steinerSymmetrizationBasis {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (s : Set E) {x : E} (hx : x ∈ steinerSymmetrizationBasis b s) :
    -x ∈ steinerSymmetrizationBasis b s := by
  rw [← reflectionList_map_finRange_apply b x, reflectionList_apply]
  refine foldl_reflection_mem ?_ hx
  intro e he
  rcases List.mem_map.mp he with ⟨i, _, rfl⟩
  exact preimage_reflection_steinerSymmetrizationBasis b s i

theorem preimage_neg_steinerSymmetrizationBasis {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (s : Set E) :
    Neg.neg ⁻¹' steinerSymmetrizationBasis b s = steinerSymmetrizationBasis b s := by
  ext x
  exact ⟨fun hx ↦ by simpa using neg_mem_steinerSymmetrizationBasis b s hx,
    neg_mem_steinerSymmetrizationBasis b s⟩

/-- Iterated Steiner symmetrization of a bounded set along an orthonormal basis is contained in
the centered closed ball of radius `Metric.diam s / 2`. -/
theorem steinerSymmetrizationBasis_subset_closedBall_diam_div_two
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {s : Set E} (hs : Bornology.IsBounded s) :
    steinerSymmetrizationBasis b s ⊆ Metric.closedBall (0 : E) (Metric.diam s / 2) := by
  refine (subset_closedBall_diam_div_two_of_neg_mem
    (isBounded_steinerSymmetrizationBasis b hs)
    (fun x hx ↦ neg_mem_steinerSymmetrizationBasis b s hx)).trans ?_
  exact Metric.closedBall_subset_closedBall
    (div_le_div_of_nonneg_right (diam_steinerSymmetrizationBasis_le b hs) zero_le_two)

variable [MeasurableSpace E] [BorelSpace E]

@[measurability]
theorem measurableSet_steinerSymmetrizationList (l : List E) {s : Set E} (hs : MeasurableSet s) :
    MeasurableSet (steinerSymmetrizationList l s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons e l ih =>
    rw [steinerSymmetrizationList_cons]
    exact ih (measurableSet_steinerSymmetrization hs)

@[measurability]
theorem measurableSet_steinerSymmetrizationBasis {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    {s : Set E} (hs : MeasurableSet s) :
    MeasurableSet (steinerSymmetrizationBasis b s) :=
  measurableSet_steinerSymmetrizationList _ hs

variable [FiniteDimensional ℝ E]

theorem volume_le_volume_closedBall_diam_div_two_of_neg_mem {s : Set E}
    (hs : Bornology.IsBounded s) (hs_symm : ∀ x ∈ s, -x ∈ s) :
    volume s ≤ volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) :=
  measure_mono (subset_closedBall_diam_div_two_of_neg_mem hs hs_symm)

theorem volume_steinerSymmetrizationList {l : List E} (hl : ∀ e ∈ l, ‖e‖ = 1) {s : Set E}
    (hs : MeasurableSet s) :
    volume (steinerSymmetrizationList l s) = volume s := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih =>
    rw [steinerSymmetrizationList_cons,
      ih (fun u hu ↦ hl u (List.mem_cons_of_mem e hu)) (measurableSet_steinerSymmetrization hs),
      volume_steinerSymmetrization (hl e List.mem_cons_self) hs]

@[simp]
theorem volume_steinerSymmetrizationBasis {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    {s : Set E} (hs : MeasurableSet s) :
    volume (steinerSymmetrizationBasis b s) = volume s :=
  volume_steinerSymmetrizationList (norm_eq_one_of_mem_map_finRange b) hs

/-- **The Euclidean Isodiametric Inequality (closed-ball form)**: the volume of any bounded set
`s : Set E` is at most the volume of the closed ball of the same diameter centered at the
origin. -/
theorem volume_le_volume_closedBall_diam_div_two {s : Set E} (hs : Bornology.IsBounded s) :
    volume s ≤ volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) := by
  let b := stdOrthonormalBasis ℝ E
  calc
    volume s ≤ volume (closure s) := measure_mono subset_closure
    _ = volume (steinerSymmetrizationBasis b (closure s)) :=
      (volume_steinerSymmetrizationBasis b isClosed_closure.measurableSet).symm
    _ ≤ volume (Metric.closedBall (0 : E) (Metric.diam (closure s) / 2)) :=
      measure_mono (steinerSymmetrizationBasis_subset_closedBall_diam_div_two b hs.closure)
    _ = volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) := by
      rw [Metric.diam_closure]

/-- **The Euclidean Isodiametric Inequality (open-ball form)**: in a nontrivial finite-dimensional
real inner product space, the volume of any bounded set `s : Set E` is at most the volume of the
open ball of radius `Metric.diam s / 2`. -/
theorem volume_le_volume_ball_diam_div_two [Nontrivial E] {s : Set E}
    (hs : Bornology.IsBounded s) :
    volume s ≤ volume (Metric.ball (0 : E) (Metric.diam s / 2)) := by
  rw [← Measure.addHaar_closedBall_eq_addHaar_ball]
  exact volume_le_volume_closedBall_diam_div_two hs

/-- **The Euclidean Isodiametric Inequality (unit-ball scaling form)**: for any bounded set
`s : Set E`, `volume s ≤ (Metric.diam s / 2) ^ (finrank ℝ E) * volume (Metric.ball 0 1)`. -/
theorem volume_le_pow_diam_div_two_mul_volume_unitBall {s : Set E}
    (hs : Bornology.IsBounded s) :
    volume s ≤
      ENNReal.ofReal (Metric.diam s / 2) ^ Module.finrank ℝ E *
        volume (Metric.ball (0 : E) 1) := by
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · rw [Module.finrank_zero_of_subsingleton, pow_zero, one_mul]
    refine measure_mono fun x _ ↦ ?_
    rw [Metric.mem_ball, Subsingleton.elim x 0, dist_self]
    exact zero_lt_one
  · calc
      volume s ≤ volume (Metric.closedBall (0 : E) (Metric.diam s / 2)) :=
        volume_le_volume_closedBall_diam_div_two hs
      _ = ENNReal.ofReal (Metric.diam s / 2) ^ Module.finrank ℝ E *
          volume (Metric.ball (0 : E) 1) := by
        rw [InnerProductSpace.volume_closedBall, InnerProductSpace.volume_ball]
        simp

end IsodiametricInequality

end TauCeti.MeasureTheory
