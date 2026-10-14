/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.JordanIsoperimetry
import all TauCeti.Analysis.Fourier.RectifiableArea
import all TauCeti.Analysis.Fourier.SignedArea
import all TauCeti.MeasureTheory.Measure.FrontierIsoperimetry
import all TauCeti.MeasureTheory.Measure.JordanIsoperimetry
import all TauCeti.MeasureTheory.Measure.Perimeter

/-!
# Planar Quarter-Turn Normal, Jordan Winding Index, Boundary Flux, and Jordan Perimeter

This file develops the planar quarter-turn linear isometry, the oriented tangent and outward normal
vectors along a plane curve, the curve orientation sign and Jordan winding index on the enclosed
region `filledHull C \ C`, orientation-reversal and monotone reparametrization invariance laws,
the oriented boundary flux functional and its Green identity for the position vector field, and
the connection between boundary flux, De Giorgi perimeter `perimeter volume (filledHull C \ C)`,
and one-dimensional Euclidean Hausdorff measure `μHE[1] C`:

1. **Quarter-turn isometry `planeQuarterTurn` (`J v`) and oriented outward normal `-σ • J τ`**:
   `TauCeti.planeQuarterTurn`, `TauCeti.norm_planeQuarterTurn`,
   `TauCeti.inner_planeQuarterTurn_self`, `TauCeti.curveNormalVec`, `TauCeti.curveUnitTangent`,
   `TauCeti.curveOutwardNormal`, `TauCeti.curveNormalVec_eq_norm_smul_curveOutwardNormal`,
   `TauCeti.norm_curveOutwardNormal`, and `TauCeti.norm_curveNormalVec`.
2. **Orientation sign `σ ∈ {-1, 1}`, Jordan winding index on `filledHull C \ C`, and reversal /
   reparametrization laws**:
   `TauCeti.curveSignedArea`, `TauCeti.curveOrientationSign`,
   `TauCeti.curveOrientationSign_mul_signedArea`, `TauCeti.jordanWindingIndex`,
   `TauCeti.integral_jordanWindingIndex`, `TauCeti.reverseCurve`, `TauCeti.deriv_reverseCurve`,
   `TauCeti.curveNormalVec_reverseCurve`, and `TauCeti.curveSignedArea_reverseCurve`.
3. **Oriented boundary flux, radial Green identity, variational perimeter bounds, and Jordan
   perimeter equality**:
   `TauCeti.curveBoundaryFlux`, `TauCeti.curveBoundaryFlux_half_id_eq_mul_curveSignedArea`,
   `TauCeti.curveBoundaryFlux_reverseCurve`, `TauCeti.abs_curveBoundaryFlux_le_integral_norm_deriv`,
   `TauCeti.perimeter_le_of_divergence_eq_curveBoundaryFlux`,
   `TauCeti.perimeter_filledHull_diff_eq_hausdorffMeasure_of_flux`, and
   `TauCeti.jordan_isoperimetric_perimeter_two`.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric OnePoint Pointwise Set
  TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Topology Distributions Interval
open TauCeti.MeasureTheory

namespace TauCeti

/-! ### Section 1: Quarter-turn isometry `planeQuarterTurn` and oriented curve normal `-σ • J τ` -/

section QuarterTurnAndNormal

/-- Underlying linear map of the planar quarter-turn `v ↦ !₂[-v 1, v 0]`. -/
@[expose] def planeQuarterTurnLinearMap :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun v := !₂[-v 1, v 0]
  map_add' u v := by ext i; fin_cases i <;> simp [PiLp.add_apply, neg_add_rev, add_comm]
  map_smul' c v := by ext i; fin_cases i <;> simp [PiLp.smul_apply, mul_neg]
theorem norm_planeQuarterTurnLinearMap (v : EuclideanSpace ℝ (Fin 2)) :
    ‖planeQuarterTurnLinearMap v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_add_sq, norm_sq_eq_add_sq]
  simp only [planeQuarterTurnLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring
/-- Canonical counterclockwise quarter-turn linear isometry `J : ℝ² →ₗᵢ[ℝ] ℝ²`. -/
@[expose] def planeQuarterTurn : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  { planeQuarterTurnLinearMap with norm_map' := norm_planeQuarterTurnLinearMap }
theorem planeQuarterTurn_apply (v : EuclideanSpace ℝ (Fin 2)) :
    planeQuarterTurn v = !₂[-v 1, v 0] := rfl
@[simp] theorem planeQuarterTurn_apply_zero (v : EuclideanSpace ℝ (Fin 2)) :
    planeQuarterTurn v 0 = -v 1 := rfl
@[simp] theorem planeQuarterTurn_apply_one (v : EuclideanSpace ℝ (Fin 2)) :
    planeQuarterTurn v 1 = v 0 := rfl
theorem norm_planeQuarterTurn (v : EuclideanSpace ℝ (Fin 2)) :
    ‖planeQuarterTurn v‖ = ‖v‖ := planeQuarterTurn.norm_map v
theorem isometry_planeQuarterTurn :
    Isometry (planeQuarterTurn : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :=
  planeQuarterTurn.isometry
/-- Explicit coordinate expansion of the real inner product on `EuclideanSpace ℝ (Fin 2)`. -/
theorem inner_euclidean_fin_two (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪u, v⟫_ℝ = u 0 * v 0 + u 1 * v 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm]
/-- Applying `planeQuarterTurn` twice negates the vector (`J (J v) = -v`). -/
@[simp] theorem planeQuarterTurn_planeQuarterTurn (v : EuclideanSpace ℝ (Fin 2)) :
    planeQuarterTurn (planeQuarterTurn v) = -v := by ext i; fin_cases i <;> simp
/-- `planeQuarterTurn v` is orthogonal to `v` (`⟪J v, v⟫ = 0`). -/
@[simp] theorem inner_planeQuarterTurn_self (v : EuclideanSpace ℝ (Fin 2)) :
    ⟪planeQuarterTurn v, v⟫_ℝ = 0 := by rw [inner_euclidean_fin_two]; simp; ring
/-- `v` is orthogonal to `planeQuarterTurn v` (`⟪v, J v⟫ = 0`). -/
@[simp] theorem inner_self_planeQuarterTurn (v : EuclideanSpace ℝ (Fin 2)) :
    ⟪v, planeQuarterTurn v⟫_ℝ = 0 := by rw [inner_euclidean_fin_two]; simp; ring
/-- Skew-adjointness of `planeQuarterTurn`: `⟪J u, v⟫ = -⟪u, J v⟫`. -/
theorem inner_planeQuarterTurn_left (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪planeQuarterTurn u, v⟫_ℝ = -⟪u, planeQuarterTurn v⟫_ℝ := by
  rw [inner_euclidean_fin_two, inner_euclidean_fin_two]; simp
/-- Inner-product preservation under `planeQuarterTurn`: `⟪J u, J v⟫ = ⟪u, v⟫`. -/
theorem inner_planeQuarterTurn_planeQuarterTurn (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪planeQuarterTurn u, planeQuarterTurn v⟫_ℝ = ⟪u, v⟫_ℝ :=
  planeQuarterTurn.inner_map_map u v
/-- Pairing `u` with `-planeQuarterTurn v` yields `u 0 * v 1 - u 1 * v 0`. -/
theorem inner_neg_planeQuarterTurn_eq (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪u, -planeQuarterTurn v⟫_ℝ = u 0 * v 1 - u 1 * v 0 := by
  rw [inner_neg_right, inner_euclidean_fin_two]; simp; ring
/-- Pairing `u` with `-σ • planeQuarterTurn v` yields `σ * (u 0 * v 1 - u 1 * v 0)`. -/
theorem inner_smul_neg_planeQuarterTurn_eq (σ : ℝ) (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪u, -σ • planeQuarterTurn v⟫_ℝ = σ * (u 0 * v 1 - u 1 * v 0) := by
  rw [inner_euclidean_fin_two]; simp [PiLp.neg_apply, PiLp.smul_apply]; ring
/-- Unnormalized outward normal vector `-σ • J (deriv γ t)` along a plane curve `γ`. -/
@[expose] def curveNormalVec (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    EuclideanSpace ℝ (Fin 2) := -σ • planeQuarterTurn (deriv γ t)
/-- Normalized unit tangent vector `(‖deriv γ t‖)⁻¹ • deriv γ t` along a plane curve `γ`. -/
@[expose] def curveUnitTangent (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    EuclideanSpace ℝ (Fin 2) := (‖deriv γ t‖)⁻¹ • deriv γ t
/-- Oriented unit outward normal vector `-σ • J (curveUnitTangent γ t)` along a plane curve `γ`. -/
@[expose] def curveOutwardNormal (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    EuclideanSpace ℝ (Fin 2) := -σ • planeQuarterTurn (curveUnitTangent γ t)
@[simp] theorem curveNormalVec_apply_zero (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    curveNormalVec σ γ t 0 = σ * deriv γ t 1 := by
  simp [curveNormalVec, PiLp.neg_apply, PiLp.smul_apply]
@[simp] theorem curveNormalVec_apply_one (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    curveNormalVec σ γ t 1 = -(σ * deriv γ t 0) := by
  simp [curveNormalVec, PiLp.neg_apply, PiLp.smul_apply]
@[simp] theorem curveNormalVec_zero_left (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    curveNormalVec 0 γ t = 0 := by simp [curveNormalVec]
@[simp] theorem curveOutwardNormal_zero_left (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    curveOutwardNormal 0 γ t = 0 := by simp [curveOutwardNormal]
@[simp] theorem curveNormalVec_neg_left (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    curveNormalVec (-σ) γ t = -curveNormalVec σ γ t := by simp [curveNormalVec]
@[simp] theorem curveOutwardNormal_neg_left (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    curveOutwardNormal (-σ) γ t = -curveOutwardNormal σ γ t := by simp [curveOutwardNormal]
/-- `curveNormalVec σ γ t = ‖deriv γ t‖ • curveOutwardNormal σ γ t` for all `t : ℝ`. -/
theorem curveNormalVec_eq_norm_smul_curveOutwardNormal (σ : ℝ)
    (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    curveNormalVec σ γ t = ‖deriv γ t‖ • curveOutwardNormal σ γ t := by
  rcases eq_or_ne (deriv γ t) 0 with h0 | hne
  · simp [curveNormalVec, curveOutwardNormal, curveUnitTangent, h0]
  · have hn : ‖deriv γ t‖ ≠ 0 := norm_ne_zero_iff.2 hne
    ext i; fin_cases i <;>
      { simp [curveNormalVec, curveOutwardNormal, curveUnitTangent, PiLp.neg_apply, PiLp.smul_apply]
        ring_nf; rw [mul_inv_cancel_right₀ hn] }
/-- At any non-stationary point `deriv γ t ≠ 0`, `curveUnitTangent γ t` has unit norm. -/
theorem norm_curveUnitTangent {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {t : ℝ} (h : deriv γ t ≠ 0) :
    ‖curveUnitTangent γ t‖ = 1 := by
  rw [curveUnitTangent, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
/-- Pointwise bound `‖curveUnitTangent γ t‖ ≤ 1` valid at all parameters `t : ℝ`. -/
theorem norm_curveUnitTangent_le (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ‖curveUnitTangent γ t‖ ≤ 1 := by
  rcases eq_or_ne (deriv γ t) 0 with h0 | hne
  · simp [curveUnitTangent, h0]
  · exact (norm_curveUnitTangent hne).le
/-- Norm of `curveOutwardNormal σ γ t` in terms of `|σ|` and `‖curveUnitTangent γ t‖`. -/
theorem norm_curveOutwardNormal_eq (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ‖curveOutwardNormal σ γ t‖ = |σ| * ‖curveUnitTangent γ t‖ := by
  simp only [curveOutwardNormal, norm_neg, norm_smul, Real.norm_eq_abs, norm_planeQuarterTurn]
/-- When `|σ| = 1` and `deriv γ t ≠ 0`, `curveOutwardNormal σ γ t` has unit norm. -/
theorem norm_curveOutwardNormal {σ : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (hσ : |σ| = 1) (h : deriv γ t ≠ 0) : ‖curveOutwardNormal σ γ t‖ = 1 := by
  rw [norm_curveOutwardNormal_eq, hσ, one_mul, norm_curveUnitTangent h]
/-- When `|σ| ≤ 1`, `‖curveOutwardNormal σ γ t‖ ≤ 1` for all `t : ℝ`. -/
theorem norm_curveOutwardNormal_le {σ : ℝ} (hσ : |σ| ≤ 1)
    (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ‖curveOutwardNormal σ γ t‖ ≤ 1 := by
  rw [norm_curveOutwardNormal_eq]
  nlinarith [norm_nonneg (curveUnitTangent γ t), norm_curveUnitTangent_le γ t]
/-- `curveOutwardNormal σ γ t` is orthogonal to `curveUnitTangent γ t`. -/
@[simp] theorem inner_curveOutwardNormal_curveUnitTangent (σ : ℝ)
    (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ⟪curveOutwardNormal σ γ t, curveUnitTangent γ t⟫_ℝ = 0 := by
  simp only [curveOutwardNormal, real_inner_smul_left, inner_planeQuarterTurn_self, mul_zero]
/-- `curveNormalVec σ γ t` is orthogonal to the velocity vector `deriv γ t`. -/
@[simp] theorem inner_curveNormalVec_deriv (σ : ℝ)
    (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ⟪curveNormalVec σ γ t, deriv γ t⟫_ℝ = 0 := by
  simp only [curveNormalVec, real_inner_smul_left, inner_planeQuarterTurn_self, mul_zero]
/-- Norm identity `‖curveNormalVec σ γ t‖ = |σ| * ‖deriv γ t‖`. -/
@[simp] theorem norm_curveNormalVec (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ‖curveNormalVec σ γ t‖ = |σ| * ‖deriv γ t‖ := by
  simp only [curveNormalVec, norm_neg, norm_smul, Real.norm_eq_abs, norm_planeQuarterTurn]
/-- When `|σ| = 1`, `‖curveNormalVec σ γ t‖ = ‖deriv γ t‖`. -/
theorem norm_curveNormalVec_of_abs_eq_one {σ : ℝ} (hσ : |σ| = 1)
    (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ‖curveNormalVec σ γ t‖ = ‖deriv γ t‖ := by
  rw [norm_curveNormalVec, hσ, one_mul]
/-- Explicit inner product of any vector `v` with `curveNormalVec σ γ t`. -/
theorem inner_curveNormalVec_eq (σ : ℝ) (v : EuclideanSpace ℝ (Fin 2))
    (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ⟪v, curveNormalVec σ γ t⟫_ℝ = σ * (v 0 * deriv γ t 1 - v 1 * deriv γ t 0) :=
  inner_smul_neg_planeQuarterTurn_eq σ v (deriv γ t)

end QuarterTurnAndNormal

/-! ### Section 2: Orientation sign, Jordan winding index on `filledHull C \ C`, and reversal -/

section OrientationAndWinding

/-- Signed area of a plane curve `γ : ℝ → EuclideanSpace ℝ (Fin 2)` over `[a, b]`:
`curveSignedArea γ a b = (1 / 2) * ∫ t in Icc a b, (γ t 0 * deriv γ t 1 - γ t 1 * deriv γ t 0)`. -/
@[expose] def curveSignedArea (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in Icc a b, (γ t 0 * deriv γ t 1 - γ t 1 * deriv γ t 0)
/-- When `a ≤ b` and `γ` is differentiable a.e. on `Icc a b`, `curveSignedArea γ a b` coincides with
`signedAreaEuclidean γ a (b - a)`. -/
theorem curveSignedArea_eq_signedAreaEuclidean {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (hab : a ≤ b) (hdiff : ∀ᵐ t ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ γ t) :
    curveSignedArea γ a b = signedAreaEuclidean γ a (b - a) := by
  rw [curveSignedArea, signedAreaEuclidean, signedArea, add_sub_cancel,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  congr 1; refine integral_congr_ae ?_
  filter_upwards [hdiff] with t ht
  rw [deriv_euclidean_apply ht 0, deriv_euclidean_apply ht 1]
/-- For an absolutely continuous curve `γ` on `[a, b]` (`a ≤ b`), `curveSignedArea γ a b` coincides
with `signedArea (fun t ↦ γ t 0) (fun t ↦ γ t 1) a (b - a)`. -/
theorem curveSignedArea_eq_signedArea_of_absolutelyContinuousOnInterval
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab : a ≤ b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    curveSignedArea γ a b = signedArea (fun t ↦ γ t 0) (fun t ↦ γ t 1) a (b - a) := by
  refine curveSignedArea_eq_signedAreaEuclidean hab ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact ht (uIcc_of_le hab ▸ hmem)
/-- Orientation sign `curveOrientationSign γ a b ∈ {-1, 1}` of a plane curve `γ` on `[a, b]`. -/
@[expose] def curveOrientationSign (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : ℝ :=
  if 0 ≤ curveSignedArea γ a b then 1 else -1
/-- Arclength-reparametrized orientation sign `rectifiableOrientationSign γ a b ∈ {-1, 1}`. -/
@[expose] def rectifiableOrientationSign (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : ℝ :=
  if 0 ≤ rectifiableSignedArea γ a b then 1 else -1
theorem curveOrientationSign_of_nonneg {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (h : 0 ≤ curveSignedArea γ a b) : curveOrientationSign γ a b = 1 := by
  simp [curveOrientationSign, h]
theorem curveOrientationSign_of_neg {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (h : curveSignedArea γ a b < 0) : curveOrientationSign γ a b = -1 := by
  simp [curveOrientationSign, not_le.2 h]
/-- `curveOrientationSign γ a b` always belongs to `{-1, 1}`. -/
theorem curveOrientationSign_mem_pair (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    curveOrientationSign γ a b ∈ ({-1, 1} : Set ℝ) := by
  unfold curveOrientationSign; split_ifs <;> simp
@[simp] theorem abs_curveOrientationSign (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    |curveOrientationSign γ a b| = 1 := by unfold curveOrientationSign; split_ifs <;> simp
@[simp] theorem sq_curveOrientationSign (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    curveOrientationSign γ a b ^ 2 = 1 := by unfold curveOrientationSign; split_ifs <;> norm_num
@[simp] theorem curveOrientationSign_mul_self (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    curveOrientationSign γ a b * curveOrientationSign γ a b = 1 := by
  rw [← sq, sq_curveOrientationSign]
theorem curveOrientationSign_ne_zero (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    curveOrientationSign γ a b ≠ 0 := by unfold curveOrientationSign; split_ifs <;> norm_num
/-- Multiplying `curveSignedArea γ a b` by `curveOrientationSign γ a b` gives its absolute value. -/
@[simp] theorem curveOrientationSign_mul_signedArea (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    curveOrientationSign γ a b * curveSignedArea γ a b = |curveSignedArea γ a b| := by
  unfold curveOrientationSign; split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (not_le.1 h)]
/-- Factoring `curveSignedArea γ a b` as `curveOrientationSign γ a b * |curveSignedArea γ a b|`. -/
theorem signedArea_eq_curveOrientationSign_mul_abs (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    curveSignedArea γ a b = curveOrientationSign γ a b * |curveSignedArea γ a b| := by
  rw [← curveOrientationSign_mul_signedArea, ← mul_assoc, curveOrientationSign_mul_self, one_mul]
theorem rectifiableOrientationSign_mem_pair (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    rectifiableOrientationSign γ a b ∈ ({-1, 1} : Set ℝ) := by
  unfold rectifiableOrientationSign; split_ifs <;> simp
@[simp] theorem abs_rectifiableOrientationSign (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    |rectifiableOrientationSign γ a b| = 1 := by
  unfold rectifiableOrientationSign; split_ifs <;> simp
@[simp] theorem rectifiableOrientationSign_mul_rectifiableSignedArea
    (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    rectifiableOrientationSign γ a b * rectifiableSignedArea γ a b =
      |rectifiableSignedArea γ a b| := by
  unfold rectifiableOrientationSign; split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (not_le.1 h)]
/-- The oriented Jordan winding index `jordanWindingIndex σ C x` of a subset `C ⊆ E` with
orientation sign `σ : ℝ`, equal to `σ` on `filledHull C \ C` and `0` elsewhere. -/
@[expose] def jordanWindingIndex {E : Type*} [TopologicalSpace E] [Bornology E]
    (σ : ℝ) (C : Set E) (x : E) : ℝ :=
  (filledHull C \ C).indicator (fun _ ↦ σ) x
/-- Representation of `jordanWindingIndex σ C` as a set indicator on `filledHull C \ C`. -/
theorem jordanWindingIndex_eq_indicator {E : Type*} [TopologicalSpace E] [Bornology E]
    (σ : ℝ) (C : Set E) : jordanWindingIndex σ C = (filledHull C \ C).indicator (fun _ ↦ σ) := rfl
/-- On the bounded interior `filledHull C \ C`, `jordanWindingIndex σ C x = σ`. -/
theorem jordanWindingIndex_of_mem_interior {E : Type*} [TopologicalSpace E] [Bornology E]
    {σ : ℝ} {C : Set E} {x : E} (hx : x ∈ filledHull C \ C) :
    jordanWindingIndex σ C x = σ := Set.indicator_of_mem hx _
/-- On the unbounded exterior `(filledHull C)ᶜ`, `jordanWindingIndex σ C x = 0`. -/
theorem jordanWindingIndex_of_mem_compl {E : Type*} [TopologicalSpace E] [Bornology E]
    {σ : ℝ} {C : Set E} {x : E} (hx : x ∈ (filledHull C)ᶜ) :
    jordanWindingIndex σ C x = 0 := Set.indicator_of_notMem (fun h ↦ hx h.1) _
/-- On the curve `C` itself, `jordanWindingIndex σ C x = 0`. -/
theorem jordanWindingIndex_of_mem_curve {E : Type*} [TopologicalSpace E] [Bornology E]
    {σ : ℝ} {C : Set E} {x : E} (hx : x ∈ C) :
    jordanWindingIndex σ C x = 0 := Set.indicator_of_notMem (fun h ↦ h.2 hx) _
@[simp] theorem jordanWindingIndex_neg {E : Type*} [TopologicalSpace E] [Bornology E]
    (σ : ℝ) (C : Set E) (x : E) :
    jordanWindingIndex (-σ) C x = -jordanWindingIndex σ C x := by
  by_cases hx : x ∈ filledHull C \ C <;> simp [jordanWindingIndex, hx]
/-- When `|σ| = 1`, `|jordanWindingIndex σ C x|` is the indicator of `filledHull C \ C`. -/
theorem abs_jordanWindingIndex_eq_indicator {E : Type*} [TopologicalSpace E] [Bornology E]
    {σ : ℝ} (hσ : |σ| = 1) (C : Set E) (x : E) :
    |jordanWindingIndex σ C x| = (filledHull C \ C).indicator (fun _ ↦ (1 : ℝ)) x := by
  by_cases hx : x ∈ filledHull C \ C <;> simp [jordanWindingIndex, hx, hσ]
/-- Integral of `jordanWindingIndex σ C` when `filledHull C \ C` is measurable. -/
theorem integral_jordanWindingIndex_of_measurableSet {E : Type*} [TopologicalSpace E]
    [Bornology E] [MeasurableSpace E] (μ : Measure E := by volume_tac) (σ : ℝ) {C : Set E}
    (hmeas : MeasurableSet (filledHull C \ C)) :
    ∫ x, jordanWindingIndex σ C x ∂μ = σ * (μ (filledHull C \ C)).toReal := by
  rw [jordanWindingIndex_eq_indicator, integral_indicator_const _ hmeas, Measure.real_def,
    smul_eq_mul, mul_comm]
/-- Any linear isometry equivalence `e : E ≃ₗᵢ[ℝ] F` commutes with `filledHull`. -/
theorem _root_.LinearIsometryEquiv.image_filledHull {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (C : Set E) : filledHull (e '' C) = e '' filledHull C := by
  have hcomp : ∀ x : E, connectedComponentIn (e '' C)ᶜ (e x) = e '' connectedComponentIn Cᶜ x := by
    intro x
    by_cases hx : x ∈ Cᶜ
    · change connectedComponentIn (e.toHomeomorph '' C)ᶜ (e.toHomeomorph x) =
        e.toHomeomorph '' connectedComponentIn Cᶜ x
      rw [← e.toHomeomorph.image_compl]
      exact (e.toHomeomorph.image_connectedComponentIn hx).symm
    · have hex : e x ∉ (e '' C)ᶜ := by simpa [e.injective.mem_set_image] using hx
      rw [connectedComponentIn_eq_empty hex, connectedComponentIn_eq_empty hx, Set.image_empty]
  ext y; obtain ⟨x, rfl⟩ := e.surjective y
  simp only [mem_filledHull_iff, hcomp x, e.injective.mem_set_image, Metric.isBounded_iff,
    Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, e.dist_map]
/-- Any linear isometry equivalence `e : E ≃ₗᵢ[ℝ] F` commutes with `filledHull C \ C`. -/
theorem _root_.LinearIsometryEquiv.image_filledHull_diff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (C : Set E) : filledHull (e '' C) \ (e '' C) = e '' (filledHull C \ C) := by
  rw [e.image_filledHull, Set.image_sdiff e.injective]
/-- For any Jordan curve `C ⊆ EuclideanSpace ℝ (Fin 2)`, `filledHull C \ C` is open. -/
theorem isOpen_filledHull_diff_two {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : IsJordanCurve C) :
    IsOpen (filledHull C \ C) := by
  have hC' : IsJordanCurve (complexToEuclidean.symm '' C) :=
    hC.image complexToEuclidean.symm.continuous.continuousOn
      complexToEuclidean.symm.injective.injOn
  have heq : C = complexToEuclidean '' (complexToEuclidean.symm '' C) :=
    (complexToEuclidean.toEquiv.image_symm_image C).symm
  rw [heq, complexToEuclidean.image_filledHull_diff]
  exact complexToEuclidean.toHomeomorph.isOpenMap _ (isOpen_filledHull_diff hC')
/-- For any Jordan curve `C ⊆ EuclideanSpace ℝ (Fin 2)`, `filledHull C \ C` is Borel-measurable. -/
theorem measurableSet_filledHull_diff_two {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsJordanCurve C) : MeasurableSet (filledHull C \ C) :=
  (isOpen_filledHull_diff_two hC).measurableSet
/-- For any Jordan curve `C ⊆ EuclideanSpace ℝ (Fin 2)`, `0 < volume (filledHull C \ C)` and
`volume (filledHull C \ C) < ⊤`. -/
theorem volume_filledHull_diff_pos_and_lt_top_two {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsJordanCurve C) :
    0 < volume (filledHull C \ C) ∧ volume (filledHull C \ C) < ⊤ := by
  have hC' : IsJordanCurve (complexToEuclidean.symm '' C) :=
    hC.image complexToEuclidean.symm.continuous.continuousOn
      complexToEuclidean.symm.injective.injOn
  have heq : C = complexToEuclidean '' (complexToEuclidean.symm '' C) :=
    (complexToEuclidean.toEquiv.image_symm_image C).symm
  refine ⟨(isOpen_filledHull_diff_two hC).measure_pos volume ?_,
    ((isBounded_filledHull.mpr hC.isCompact.isBounded).subset sdiff_subset).measure_lt_top⟩
  rw [heq, complexToEuclidean.image_filledHull_diff]
  exact (nonempty_filledHull_diff hC').image _
/-- Unconditional integral of `jordanWindingIndex σ C` for a Jordan curve `C ⊆ ℝ²`. -/
theorem integral_jordanWindingIndex (σ : ℝ) {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsJordanCurve C) :
    ∫ x, jordanWindingIndex σ C x = σ * (volume (filledHull C \ C)).toReal :=
  integral_jordanWindingIndex_of_measurableSet volume σ (measurableSet_filledHull_diff_two hC)
/-- Unconditional integral of `jordanWindingIndex σ C` for any Jordan curve `C ⊆ ℂ`. -/
theorem integral_jordanWindingIndex_complex (σ : ℝ) {C : Set ℂ} (hC : IsJordanCurve C) :
    ∫ x, jordanWindingIndex σ C x = σ * (volume (filledHull C \ C)).toReal :=
  integral_jordanWindingIndex_of_measurableSet volume σ (measurableSet_filledHull_diff hC)
/-- Time-reversed parameterization `reverseCurve γ a b t = γ (a + b - t)` on `[a, b]`. -/
@[expose] def reverseCurve {E : Type*} (γ : ℝ → E) (a b t : ℝ) : E := γ (a + b - t)
@[simp] theorem reverseCurve_apply {E : Type*} (γ : ℝ → E) (a b t : ℝ) :
    reverseCurve γ a b t = γ (a + b - t) := rfl
theorem reverseCurve_left {E : Type*} (γ : ℝ → E) (a b : ℝ) :
    reverseCurve γ a b a = γ b := by simp [reverseCurve]
theorem reverseCurve_right {E : Type*} (γ : ℝ → E) (a b : ℝ) :
    reverseCurve γ a b b = γ a := by simp [reverseCurve]
@[simp] theorem reverseCurve_reverseCurve {E : Type*} (γ : ℝ → E) (a b : ℝ) :
    reverseCurve (reverseCurve γ a b) a b = γ := by ext t; simp [reverseCurve]
/-- Reversing a curve on `Icc a b` preserves its trace `γ '' Icc a b`. -/
@[simp] theorem image_reverseCurve_Icc {E : Type*} (γ : ℝ → E) (a b : ℝ) :
    reverseCurve γ a b '' Icc a b = γ '' Icc a b := by
  ext x; simp only [reverseCurve, mem_image, mem_Icc]
  refine ⟨fun ⟨t, ⟨ht1, ht2⟩, htx⟩ ↦ ⟨a + b - t, ⟨by linarith, by linarith⟩, htx⟩,
    fun ⟨t, ⟨ht1, ht2⟩, htx⟩ ↦ ⟨a + b - t, ⟨by linarith, by linarith⟩, by simpa using htx⟩⟩
/-- Pointwise derivative identity `deriv (reverseCurve γ a b) t = -deriv γ (a + b - t)`. -/
theorem deriv_reverseCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℝ → E) (a b t : ℝ) : deriv (reverseCurve γ a b) t = -deriv γ (a + b - t) := by
  change deriv (fun s ↦ γ (a + b - s)) t = -deriv γ (a + b - t)
  exact deriv_comp_const_sub γ (a + b) t
@[simp] theorem norm_deriv_reverseCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℝ → E) (a b t : ℝ) : ‖deriv (reverseCurve γ a b) t‖ = ‖deriv γ (a + b - t)‖ := by
  rw [deriv_reverseCurve, norm_neg]
/-- Under `reverseCurve γ a b`, the unit tangent negates. -/
theorem curveUnitTangent_reverseCurve (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b t : ℝ) :
    curveUnitTangent (reverseCurve γ a b) t = -curveUnitTangent γ (a + b - t) := by
  simp [curveUnitTangent, deriv_reverseCurve]
/-- Simultaneous reversal of curve parameterization and orientation sign leaves the unnormalized
outward normal vector invariant. -/
theorem curveNormalVec_reverseCurve (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (a b t : ℝ) :
    curveNormalVec (-σ) (reverseCurve γ a b) t = curveNormalVec σ γ (a + b - t) := by
  simp [curveNormalVec, deriv_reverseCurve]
/-- Simultaneous reversal of curve parameterization and orientation sign leaves the unit outward
normal vector invariant. -/
theorem curveOutwardNormal_reverseCurve (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (a b t : ℝ) :
    curveOutwardNormal (-σ) (reverseCurve γ a b) t = curveOutwardNormal σ γ (a + b - t) := by
  simp [curveOutwardNormal, curveUnitTangent_reverseCurve]
/-- Reflection `t ↦ a + b - t` preserves Lebesgue set integrals over `Icc a b`. -/
theorem setIntegral_Icc_comp_add_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) :
    (∫ t in Icc a b, f (a + b - t)) = ∫ t in Icc a b, f t := by
  rcases le_or_gt a b with hab | hab
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_comp_sub_left, add_sub_cancel_right, add_sub_cancel_left,
      intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  · rw [Icc_eq_empty (not_le.2 hab), setIntegral_empty, setIntegral_empty]
/-- Under `reverseCurve γ a b`, `curveSignedArea` negates unconditionally. -/
@[simp] theorem curveSignedArea_reverseCurve (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    curveSignedArea (reverseCurve γ a b) a b = -curveSignedArea γ a b := by
  unfold curveSignedArea
  let f : ℝ → ℝ := fun t ↦ γ t 0 * deriv γ t 1 - γ t 1 * deriv γ t 0
  have hfun : (fun t ↦ reverseCurve γ a b t 0 * deriv (reverseCurve γ a b) t 1 -
      reverseCurve γ a b t 1 * deriv (reverseCurve γ a b) t 0) = fun t ↦ -f (a + b - t) := by
    ext t; simp [f, reverseCurve, deriv_reverseCurve]; ring
  rw [hfun, integral_neg, setIntegral_Icc_comp_add_sub f a b]; ring
/-- When `curveSignedArea γ a b ≠ 0`, reversing the curve negates `curveOrientationSign`. -/
theorem curveOrientationSign_reverseCurve {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (hne : curveSignedArea γ a b ≠ 0) :
    curveOrientationSign (reverseCurve γ a b) a b = -curveOrientationSign γ a b := by
  unfold curveOrientationSign; rw [curveSignedArea_reverseCurve]
  rcases lt_or_gt_of_ne hne with hlt | hgt <;> { split_ifs <;> linarith }
/-- Under `reverseCurve γ a b`, `rectifiableSignedArea` negates for any closed continuous BV curve
on `[a, b]` (`a ≤ b`). -/
theorem rectifiableSignedArea_reverseCurve {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) :
    rectifiableSignedArea (reverseCurve γ a b) a b = -rectifiableSignedArea γ a b :=
  rectifiableSignedArea_reverse hab hγ hc hclosed
/-- When `rectifiableSignedArea γ a b ≠ 0`, reversing a closed continuous BV curve negates
`rectifiableOrientationSign`. -/
theorem rectifiableOrientationSign_reverseCurve {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hne : rectifiableSignedArea γ a b ≠ 0) :
    rectifiableOrientationSign (reverseCurve γ a b) a b = -rectifiableOrientationSign γ a b := by
  unfold rectifiableOrientationSign; rw [rectifiableSignedArea_reverseCurve hab hγ hc hclosed]
  rcases lt_or_gt_of_ne hne with hlt | hgt <;> { split_ifs <;> linarith }
/-- Under a differentiable reparametrization `φ : ℝ → ℝ`, `curveNormalVec σ (γ ∘ φ) t` scales by
`deriv φ t`. -/
theorem curveNormalVec_comp (σ : ℝ) {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {φ : ℝ → ℝ} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ (φ t)) (hφ : DifferentiableAt ℝ φ t) :
    curveNormalVec σ (γ ∘ φ) t = deriv φ t • curveNormalVec σ γ (φ t) := by
  ext i; fin_cases i <;>
    { simp [curveNormalVec, deriv.scomp t hγ hφ, PiLp.neg_apply, PiLp.smul_apply]; ring }
/-- Under an orientation-preserving reparametrization (`0 < deriv φ t`), the unit tangent vector is
invariant. -/
theorem curveUnitTangent_comp_of_deriv_pos {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {φ : ℝ → ℝ} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ (φ t)) (hφ : DifferentiableAt ℝ φ t) (hpos : 0 < deriv φ t) :
    curveUnitTangent (γ ∘ φ) t = curveUnitTangent γ (φ t) := by
  ext i; simp [curveUnitTangent, deriv.scomp t hγ hφ, norm_smul, Real.norm_of_nonneg hpos.le,
    PiLp.smul_apply, mul_assoc, inv_mul_cancel_left₀ hpos.ne']
/-- Under an orientation-preserving reparametrization (`0 < deriv φ t`), the unit outward normal is
invariant. -/
theorem curveOutwardNormal_comp_of_deriv_pos (σ : ℝ) {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    {φ : ℝ → ℝ} {t : ℝ} (hγ : DifferentiableAt ℝ γ (φ t)) (hφ : DifferentiableAt ℝ φ t)
    (hpos : 0 < deriv φ t) :
    curveOutwardNormal σ (γ ∘ φ) t = curveOutwardNormal σ γ (φ t) := by
  simp only [curveOutwardNormal, curveUnitTangent_comp_of_deriv_pos hγ hφ hpos]
/-- Under any monotone continuous onto reparametrization `φ : Icc c d → Icc a b`,
`rectifiableOrientationSign (γ ∘ φ) c d = rectifiableOrientationSign γ a b`. -/
theorem rectifiableOrientationSign_comp_of_monotoneOn {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    {a b c d : ℝ} {φ : ℝ → ℝ} (hcd : c ≤ d) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) :
    rectifiableOrientationSign (γ ∘ φ) c d = rectifiableOrientationSign γ a b := by
  simp only [rectifiableOrientationSign,
    rectifiableSignedArea_comp_of_monotoneOn hcd hγ hc hφ hcont hφc hφd]

end OrientationAndWinding

/-! ### Section 3: Oriented boundary flux, Green identity, and Jordan perimeter equality -/

section BoundaryFluxAndPerimeter

/-- Oriented boundary flux of a planar vector field `V` across `γ` on `[a, b]` with sign `σ`:
`curveBoundaryFlux σ γ a b V = ∫ t in Icc a b, ⟪V (γ t), curveNormalVec σ γ t⟫_ℝ`. -/
@[expose] def curveBoundaryFlux (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∫ t in Icc a b, ⟪V (γ t), curveNormalVec σ γ t⟫_ℝ
@[simp] theorem curveBoundaryFlux_zero_left (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    curveBoundaryFlux 0 γ a b V = 0 := by simp [curveBoundaryFlux]
@[simp] theorem curveBoundaryFlux_neg_left (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    curveBoundaryFlux (-σ) γ a b V = -curveBoundaryFlux σ γ a b V := by
  simp [curveBoundaryFlux, integral_neg]
@[simp] theorem curveBoundaryFlux_neg_right (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    curveBoundaryFlux σ γ a b (-V) = -curveBoundaryFlux σ γ a b V := by
  simp [curveBoundaryFlux, integral_neg]
/-- Simultaneous reversal of orientation sign `σ ↦ -σ` and curve parameterization
`γ ↦ reverseCurve γ a b` leaves `curveBoundaryFlux` invariant for every vector field `V`. -/
theorem curveBoundaryFlux_reverseCurve (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    curveBoundaryFlux (-σ) (reverseCurve γ a b) a b V = curveBoundaryFlux σ γ a b V := by
  unfold curveBoundaryFlux; simp only [curveNormalVec_reverseCurve, reverseCurve_apply]
  exact setIntegral_Icc_comp_add_sub (fun t ↦ ⟪V (γ t), curveNormalVec σ γ t⟫_ℝ) a b
/-- Pointwise Green integrand identity for `V x = (1 / 2 : ℝ) • x`. -/
theorem inner_half_smul_curveNormalVec (σ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ⟪(1 / 2 : ℝ) • γ t, curveNormalVec σ γ t⟫_ℝ =
      σ * ((1 / 2 : ℝ) * (γ t 0 * deriv γ t 1 - γ t 1 * deriv γ t 0)) := by
  rw [real_inner_smul_left, inner_curveNormalVec_eq]; ring
/-- The boundary flux of `fun x ↦ (1 / 2 : ℝ) • x` equals `σ * curveSignedArea γ a b`. -/
theorem curveBoundaryFlux_half_id_eq_mul_curveSignedArea (σ : ℝ)
    (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    curveBoundaryFlux σ γ a b (fun x ↦ (1 / 2 : ℝ) • x) = σ * curveSignedArea γ a b := by
  unfold curveBoundaryFlux curveSignedArea
  simp_rw [inner_half_smul_curveNormalVec, integral_const_mul]
/-- With the canonical orientation sign `σ = curveOrientationSign γ a b`, the boundary flux of
`fun x ↦ (1 / 2 : ℝ) • x` equals the enclosed unsigned area `|curveSignedArea γ a b|`. -/
theorem curveBoundaryFlux_curveOrientationSign_half_id
    (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    curveBoundaryFlux (curveOrientationSign γ a b) γ a b (fun x ↦ (1 / 2 : ℝ) • x) =
      |curveSignedArea γ a b| := by
  rw [curveBoundaryFlux_half_id_eq_mul_curveSignedArea, curveOrientationSign_mul_signedArea]
/-- Pointwise Cauchy–Schwarz bound on the boundary flux integrand: when `‖V (γ t)‖ ≤ 1` and
`|σ| ≤ 1`, `|⟪V (γ t), curveNormalVec σ γ t⟫_ℝ| ≤ ‖deriv γ t‖`. -/
theorem abs_inner_curveNormalVec_le {σ : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hσ : |σ| ≤ 1) (hV : ‖V (γ t)‖ ≤ 1) :
    |⟪V (γ t), curveNormalVec σ γ t⟫_ℝ| ≤ ‖deriv γ t‖ := by
  have h1 : ‖V (γ t)‖ * |σ| ≤ 1 := by nlinarith [norm_nonneg (V (γ t)), abs_nonneg σ]
  calc |⟪V (γ t), curveNormalVec σ γ t⟫_ℝ|
      ≤ ‖V (γ t)‖ * ‖curveNormalVec σ γ t‖ := abs_real_inner_le_norm _ _
    _ = (‖V (γ t)‖ * |σ|) * ‖deriv γ t‖ := by rw [norm_curveNormalVec]; ring
    _ ≤ 1 * ‖deriv γ t‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖deriv γ t‖ := one_mul _

/-- Integral bound on the oriented boundary flux when `‖V (γ t)‖ ≤ 1` and `|σ| ≤ 1`. -/
theorem abs_curveBoundaryFlux_le_integral_norm_deriv {σ : ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hσ : |σ| ≤ 1) (hV : ∀ t ∈ Icc a b, ‖V (γ t)‖ ≤ 1)
    (hint : IntegrableOn (fun t ↦ ‖deriv γ t‖) (Icc a b) volume) :
    |curveBoundaryFlux σ γ a b V| ≤ ∫ t in Icc a b, ‖deriv γ t‖ := by
  unfold curveBoundaryFlux
  refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ ↦ abs_nonneg _) hint ?_)
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun t ht ↦ abs_inner_curveNormalVec_le hσ (hV t ht)

/-- For an absolutely continuous curve `γ` on `[a, b]` (`a ≤ b`), the speed integral over `Icc a b`
equals `(eVariationOn γ (Icc a b)).toReal`. -/
theorem setIntegral_Icc_norm_deriv_eq_toReal_eVariationOn
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab : a ≤ b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    (∫ t in Icc a b, ‖deriv γ t‖) = (eVariationOn γ (Icc a b)).toReal := by
  rw [hγ.toReal_eVariationOn_eq_integral_norm_deriv hab,
    intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- For an absolutely continuous curve `γ` on `[a, b]` (`a ≤ b`), `‖deriv γ ·‖` is integrable on
`Icc a b`. -/
theorem integrableOn_Icc_norm_deriv_of_absolutelyContinuousOnInterval
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab : a ≤ b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntegrableOn (fun t ↦ ‖deriv γ t‖) (Icc a b) volume := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hγ.intervalIntegrable_norm_deriv

/-- Total-variation bound on `curveBoundaryFlux` for an absolutely continuous curve `γ`. -/
theorem abs_curveBoundaryFlux_le_toReal_eVariationOn {σ : ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab : a ≤ b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hσ : |σ| ≤ 1) (hV : ∀ t ∈ Icc a b, ‖V (γ t)‖ ≤ 1) :
    |curveBoundaryFlux σ γ a b V| ≤ (eVariationOn γ (Icc a b)).toReal := by
  rw [← setIntegral_Icc_norm_deriv_eq_toReal_eVariationOn hab hγ]
  exact abs_curveBoundaryFlux_le_integral_norm_deriv hσ hV
    (integrableOn_Icc_norm_deriv_of_absolutelyContinuousOnInterval hab hγ)

/-- Alias `ePerimeter` for the extended-real De Giorgi perimeter `perimeter`. -/
abbrev ePerimeter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E]
    (μ : Measure E := by volume_tac) (s : Set E) : ℝ≥0∞ := perimeter μ s

/-- Alias `FinitePerimeter` for `HasFinitePerimeter`. -/
abbrev FinitePerimeter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E]
    (μ : Measure E := by volume_tac) (s : Set E) : Prop := HasFinitePerimeter μ s

/-- Whole-space supremum representation of `perimeter μ s` for a measurable set `s`. -/
theorem perimeter_eq_iSup_of_measurableSet {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E]
    (μ : Measure E := by volume_tac) {s : Set E} (hs : MeasurableSet s) :
    perimeter μ s = ⨆ (φ : 𝓓(⊤, E)) (_ : ∀ x, ‖φ x‖ ≤ 1),
      ENNReal.ofReal (∫ x in s, divergence (φ : E → E) x ∂μ) := by
  simpa [perimeter] using relativePerimeter_eq_iSup_of_measurableSet (μ := μ) (Ω := ⊤) hs

/-- **Variational perimeter bound from the divergence–boundary-flux pairing**:
if a measurable planar region `Ω ⊆ EuclideanSpace ℝ (Fin 2)` satisfies
`∫ x in Ω, divergence φ x = curveBoundaryFlux σ γ a b φ` for all test vector fields `φ` with
`‖φ x‖ ≤ 1`, where `|σ| ≤ 1` and `‖deriv γ ·‖` is integrable on `Icc a b`, then
`perimeter volume Ω ≤ ENNReal.ofReal (∫ t in Icc a b, ‖deriv γ t‖)` and
`HasFinitePerimeter volume Ω`. -/
theorem perimeter_le_of_divergence_eq_curveBoundaryFlux
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : MeasurableSet Ω)
    {σ : ℝ} (hσ : |σ| ≤ 1) {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (hint : IntegrableOn (fun t ↦ ‖deriv γ t‖) (Icc a b) volume)
    (hgreen : ∀ φ : 𝓓(⊤, EuclideanSpace ℝ (Fin 2)), (∀ x, ‖φ x‖ ≤ 1) →
      (∫ x in Ω, divergence (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x) =
        curveBoundaryFlux σ γ a b φ) :
    perimeter volume Ω ≤ ENNReal.ofReal (∫ t in Icc a b, ‖deriv γ t‖) ∧
      HasFinitePerimeter volume Ω ∧
      ∀ φ : 𝓓(⊤, EuclideanSpace ℝ (Fin 2)), (∀ x, ‖φ x‖ ≤ 1) →
        (∫ x in Ω, divergence (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x) =
          curveBoundaryFlux (-σ) (reverseCurve γ a b) a b φ := by
  have hle : perimeter volume Ω ≤ ENNReal.ofReal (∫ t in Icc a b, ‖deriv γ t‖) := by
    rw [perimeter_eq_iSup_of_measurableSet volume hΩ]
    refine iSup₂_le fun φ hφ ↦ ENNReal.ofReal_le_ofReal ?_
    rw [hgreen φ hφ]
    exact (le_abs_self _).trans
      (abs_curveBoundaryFlux_le_integral_norm_deriv hσ (fun t _ ↦ hφ (γ t)) hint)
  refine ⟨hle, ⟨hΩ.nullMeasurableSet, hle.trans_lt ENNReal.ofReal_lt_top⟩, fun φ hφ ↦ ?_⟩
  rw [curveBoundaryFlux_reverseCurve, hgreen φ hφ]

/-- **Jordan region perimeter upper bound and finiteness from the boundary-flux pairing**:
for a simple closed absolutely continuous curve `γ : ℝ → EuclideanSpace ℝ (Fin 2)` on `[a, b]`
(`a < b`) with trace `C = γ '' Icc a b`, the divergence–boundary-flux pairing implies
`perimeter volume (filledHull C \ C) ≤ μHE[1] C` and
`HasFinitePerimeter volume (filledHull C \ C)`. -/
theorem perimeter_filledHull_diff_le_hausdorffMeasure_of_flux
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    {σ : ℝ} (hσ : |σ| ≤ 1)
    (hgreen : ∀ φ : 𝓓(⊤, EuclideanSpace ℝ (Fin 2)), (∀ x, ‖φ x‖ ≤ 1) →
      (∫ x in filledHull (γ '' Icc a b) \ γ '' Icc a b,
        divergence (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x) =
          curveBoundaryFlux σ γ a b φ) :
    perimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b) ≤ μHE[1] (γ '' Icc a b) ∧
      HasFinitePerimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b) := by
  have hc : ContinuousOn γ (Icc a b) := by simpa [uIcc_of_le hab.le] using hγ.continuousOn
  have hbv : BoundedVariationOn γ (Icc a b) := by
    simpa [uIcc_of_le hab.le] using hγ.boundedVariationOn
  have hC : IsJordanCurve (γ '' Icc a b) := isJordanCurve_image_Icc hab hc hclosed hinj
  have hmeas : MeasurableSet (filledHull (γ '' Icc a b) \ γ '' Icc a b) :=
    measurableSet_filledHull_diff_two hC
  have hint := integrableOn_Icc_norm_deriv_of_absolutelyContinuousOnInterval hab.le hγ
  obtain ⟨hle, hfp, _⟩ := perimeter_le_of_divergence_eq_curveBoundaryFlux hmeas hσ hint hgreen
  rw [setIntegral_Icc_norm_deriv_eq_toReal_eVariationOn hab.le hγ, ENNReal.ofReal_toReal hbv,
    ← euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hc hinj] at hle
  exact ⟨hle, hfp⟩

/-- **Exact Jordan perimeter equality `perimeter volume (filledHull C \ C) = μHE[1] C`**:
combining the divergence–boundary-flux upper bound with
`μHE[1] C ≤ perimeter volume (filledHull C \ C)` yields
`FinitePerimeter volume (filledHull C \ C)`, `ePerimeter volume (filledHull C \ C) = μHE[1] C`,
and `(perimeter volume (filledHull C \ C)).toReal = (μHE[1] C).toReal`. -/
theorem perimeter_filledHull_diff_eq_hausdorffMeasure_of_flux
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    {σ : ℝ} (hσ : |σ| ≤ 1)
    (hgreen : ∀ φ : 𝓓(⊤, EuclideanSpace ℝ (Fin 2)), (∀ x, ‖φ x‖ ≤ 1) →
      (∫ x in filledHull (γ '' Icc a b) \ γ '' Icc a b,
        divergence (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x) =
          curveBoundaryFlux σ γ a b φ)
    (hlower : μHE[1] (γ '' Icc a b) ≤
      perimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b)) :
    FinitePerimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b) ∧
      ePerimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b) = μHE[1] (γ '' Icc a b) ∧
      (perimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b)).toReal =
        (μHE[1] (γ '' Icc a b)).toReal := by
  obtain ⟨hupper, hfp⟩ :=
    perimeter_filledHull_diff_le_hausdorffMeasure_of_flux hab hγ hclosed hinj hσ hgreen
  have heq : perimeter volume (filledHull (γ '' Icc a b) \ γ '' Icc a b) =
      μHE[1] (γ '' Icc a b) := le_antisymm hupper hlower
  exact ⟨hfp, heq, congrArg ENNReal.toReal heq⟩

/-- **Unconditional exact perimeter and finite-perimeter package for the Jordan inside of a circle**
in `EuclideanSpace ℝ (Fin 2)` (`0 < r`). -/
theorem perimeter_filledHull_sphere_diff_eq_hausdorffMeasure_two
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    FinitePerimeter volume (filledHull (Metric.sphere c r) \ Metric.sphere c r) ∧
      ePerimeter volume (filledHull (Metric.sphere c r) \ Metric.sphere c r) =
        μHE[1] (Metric.sphere c r) ∧
      (perimeter volume (filledHull (Metric.sphere c r) \ Metric.sphere c r)).toReal =
        (μHE[1] (Metric.sphere c r)).toReal ∧
      ENNReal.ofReal (4 * Real.pi) * volume (filledHull (Metric.sphere c r) \ Metric.sphere c r) =
        ePerimeter volume (filledHull (Metric.sphere c r) \ Metric.sphere c r) ^ 2 := by
  rw [filledHull_sphere_diff c hr.le]
  have hfp : HasFinitePerimeter volume (Metric.ball c r) := hasFinitePerimeter_ball c r
  have hperim : perimeter volume (Metric.ball c r) = μHE[1] (Metric.sphere c r) := by
    rw [perimeter_ball c hr, finrank_euclideanSpace_fin, EuclideanSpace.volume_ball_fin_two,
      euclideanHausdorffMeasure_sphere_two c hr.le, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (sq_nonneg r), ← ENNReal.ofReal_mul (by positivity)]
    congr 1; push_cast; field_simp
  have hiso : ENNReal.ofReal (4 * Real.pi) * volume (Metric.ball c r) =
      perimeter volume (Metric.ball c r) ^ 2 := by
    rw [hperim, EuclideanSpace.volume_ball_fin_two, euclideanHausdorffMeasure_sphere_two c hr.le,
      ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (sq_nonneg r),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
    congr 1; ring
  exact ⟨hfp, hperim, congrArg ENNReal.toReal hperim, hiso⟩

/-- **Sharp Jordan isoperimetric inequality in `EuclideanSpace ℝ (Fin 2)` from perimeter**:
for any Jordan curve `C ⊆ EuclideanSpace ℝ (Fin 2)` with `perimeter volume (filledHull C \ C) =
μHE[1] C` and `isoperimetricBound (filledHull C \ C) ≤ perimeter volume (filledHull C \ C)`,
`ENNReal.ofReal (4 * Real.pi) * volume (filledHull C \ C) ≤
ePerimeter volume (filledHull C \ C) ^ 2` and
`4 * Real.pi * (volume (filledHull C \ C)).toReal ≤
(perimeter volume (filledHull C \ C)).toReal ^ 2`. -/
theorem jordan_isoperimetric_perimeter_two {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsJordanCurve C) (hrect : μHE[1] C < ⊤)
    (hiso : isoperimetricBound (filledHull C \ C) ≤ perimeter volume (filledHull C \ C))
    (hperim : perimeter volume (filledHull C \ C) = μHE[1] C) :
    ENNReal.ofReal (4 * Real.pi) * volume (filledHull C \ C) ≤
        ePerimeter volume (filledHull C \ C) ^ 2 ∧
      4 * Real.pi * (volume (filledHull C \ C)).toReal ≤
        (perimeter volume (filledHull C \ C)).toReal ^ 2 := by
  have hpow := pow_le_pow_left' hiso (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)))
  rw [isoperimetricBound_pow_finrank, finrank_euclideanSpace_fin,
    EuclideanSpace.volume_ball_fin_two] at hpow
  have h4 : ((2 : ℕ) : ℝ≥0∞) ^ 2 * (ENNReal.ofReal 1 ^ 2 * ENNReal.ofReal Real.pi) =
      ENNReal.ofReal (4 * Real.pi) := by
    rw [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.ofReal_mul (by positivity)]; norm_num
  simp only [Nat.add_one_sub_one, pow_one] at hpow
  rw [h4] at hpow
  refine ⟨hpow, ?_⟩
  have htop_r : perimeter volume (filledHull C \ C) ^ 2 ≠ ⊤ := by
    rw [hperim]; exact ENNReal.pow_ne_top hrect.ne
  have htop_l : ENNReal.ofReal (4 * Real.pi) * volume (filledHull C \ C) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_filledHull_diff_pos_and_lt_top_two hC).2.ne
  have hreal := (ENNReal.toReal_le_toReal htop_l htop_r).mpr hpow
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow] at hreal

end BoundaryFluxAndPerimeter

end TauCeti
