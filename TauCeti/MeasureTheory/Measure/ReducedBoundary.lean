/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.BallPerimeter
public import TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
public import TauCeti.MeasureTheory.Measure.HalfSpacePerimeter
import all TauCeti.MeasureTheory.Measure.EssentialBoundary
import all TauCeti.MeasureTheory.Measure.HalfSpacePerimeter
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport

/-!
# De Giorgi Blow-Ups, Reduced Boundary, Outward Unit Normal, and Boundary Examples

This file develops De Giorgi blow-ups, the De Giorgi reduced boundary `reducedBoundary`, and the
measure-theoretic outward unit normal `deGiorgiNormal` for sets in finite-dimensional real inner
product spaces, and verifies them on half-spaces, balls, ball exteriors, punctured balls, and
balls modified by null dense sets:

1. **De Giorgi blow-ups `deGiorgiBlowUp` and scaling laws**:
   `deGiorgiBlowUp`, `deGiorgiBlowUp_ball`, `deGiorgiBlowUp_halfSpaceLT`,
   `measure_deGiorgiBlowUp`, `volume_deGiorgiBlowUp_inter_ball`, and
   `relativePerimeter_deGiorgiBlowUp_ball`.
2. **De Giorgi outward unit normal and reduced boundary**:
   `HasDeGiorgiBlowUp`, `HasDeGiorgiNormal`, `reducedBoundary`, `deGiorgiNormal`,
   `reducedBoundary_congr_ae`, `deGiorgiNormal_congr_ae`, `HasDeGiorgiBlowUp.unique`,
   `HasDeGiorgiNormal.unique`, `HasDeGiorgiBlowUp.tendsto_density_one_half`,
   `HasDeGiorgiBlowUp.hasMeasureDensityAt`, `reducedBoundary_subset_essentialBoundary`,
   `reducedBoundary_subset_frontier`, `reducedBoundary_compl`, and `deGiorgiNormal_compl`.
3. **Explicit reduced boundary and normal of half-spaces, balls, and boundary examples**:
   half-spaces (`reducedBoundary_halfSpaceLT`, `deGiorgiNormal_halfSpaceLT`), balls
   (`hasDeGiorgiBlowUp_ball`, `essentialBoundary_ball`, `essentialInterior_ball`,
   `essentialExterior_ball`, `deGiorgiNormal_ball`), ball exteriors, punctured balls, and balls
   modified by null dense sets (`frontier_and_perimeter_ball_union_countable_dense`).
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
open TauCeti.MeasureTheory

namespace TauCeti

/-! ### Section 1: De Giorgi blow-ups and scaling laws -/

section DeGiorgiBlowUp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bundled open ball `⟨Metric.ball c r, Metric.isOpen_ball⟩` as an element of `Opens E`. -/
abbrev openBall (c : E) (r : ℝ) : Opens E := ⟨Metric.ball c r, Metric.isOpen_ball⟩

omit [NormedSpace ℝ E] in
@[simp] theorem coe_openBall (c : E) (r : ℝ) : (openBall c r : Set E) = Metric.ball c r := rfl

/-- **De Giorgi blow-up** of `s ⊆ E` at `x : E` at scale `r : ℝ`:
`deGiorgiBlowUp s x r = {z : E | x + r • z ∈ s}`. -/
@[expose] def deGiorgiBlowUp (s : Set E) (x : E) (r : ℝ) : Set E := {z : E | x + r • z ∈ s}

@[simp] theorem mem_deGiorgiBlowUp {s : Set E} {x z : E} {r : ℝ} :
    z ∈ deGiorgiBlowUp s x r ↔ x + r • z ∈ s := Iff.rfl

theorem deGiorgiBlowUp_eq_preimage (s : Set E) (x : E) (r : ℝ) :
    deGiorgiBlowUp s x r = (fun z : E ↦ x + r • z) ⁻¹' s := rfl

@[simp] theorem deGiorgiBlowUp_empty (x : E) (r : ℝ) : deGiorgiBlowUp (∅ : Set E) x r = ∅ := rfl
@[simp] theorem deGiorgiBlowUp_univ (x : E) (r : ℝ) : deGiorgiBlowUp (univ : Set E) x r = univ :=
  rfl
@[simp] theorem deGiorgiBlowUp_compl (s : Set E) (x : E) (r : ℝ) :
    deGiorgiBlowUp sᶜ x r = (deGiorgiBlowUp s x r)ᶜ := rfl
@[simp] theorem deGiorgiBlowUp_inter (s t : Set E) (x : E) (r : ℝ) :
    deGiorgiBlowUp (s ∩ t) x r = deGiorgiBlowUp s x r ∩ deGiorgiBlowUp t x r := rfl
@[simp] theorem deGiorgiBlowUp_union (s t : Set E) (x : E) (r : ℝ) :
    deGiorgiBlowUp (s ∪ t) x r = deGiorgiBlowUp s x r ∪ deGiorgiBlowUp t x r := rfl
@[simp] theorem deGiorgiBlowUp_sdiff (s t : Set E) (x : E) (r : ℝ) :
    deGiorgiBlowUp (s \ t) x r = deGiorgiBlowUp s x r \ deGiorgiBlowUp t x r := rfl
@[simp] theorem deGiorgiBlowUp_symmDiff (s t : Set E) (x : E) (r : ℝ) :
    deGiorgiBlowUp (s ∆ t) x r = deGiorgiBlowUp s x r ∆ deGiorgiBlowUp t x r :=
  preimage_symmDiff s t

@[simp] theorem deGiorgiBlowUp_mul (s : Set E) (x : E) (r₁ r₂ : ℝ) :
    deGiorgiBlowUp (deGiorgiBlowUp s x r₁) 0 r₂ = deGiorgiBlowUp s x (r₁ * r₂) := by
  ext z; simp [deGiorgiBlowUp, mul_smul]

theorem deGiorgiBlowUp_mono {s t : Set E} (hst : s ⊆ t) (x : E) (r : ℝ) :
    deGiorgiBlowUp s x r ⊆ deGiorgiBlowUp t x r := preimage_mono hst

/-- For `r ≠ 0`, `deGiorgiBlowUp s x r = r⁻¹ • ((x + ·) ⁻¹' s)`. -/
theorem deGiorgiBlowUp_eq_inv_smul_preimage (s : Set E) (x : E) {r : ℝ} (hr : r ≠ 0) :
    deGiorgiBlowUp s x r = r⁻¹ • ((fun w : E ↦ x + w) ⁻¹' s) := by
  ext z; simp [deGiorgiBlowUp, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr)]

/-- De Giorgi blow-up of `Metric.ball c R` at `x` with scale `r > 0`. -/
theorem deGiorgiBlowUp_ball_general (c x : E) (R : ℝ) {r : ℝ} (hr : 0 < r) :
    deGiorgiBlowUp (Metric.ball c R) x r = Metric.ball (r⁻¹ • (c - x)) (r⁻¹ * R) := by
  ext z; simp only [mem_deGiorgiBlowUp, Metric.mem_ball, dist_eq_norm]
  have heq : x + r • z - c = r • (z - r⁻¹ • (c - x)) := by
    rw [smul_sub, smul_inv_smul₀ hr.ne']; abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    ← mul_lt_mul_iff_right₀ (inv_pos.2 hr), inv_mul_cancel_left₀ hr.ne']

/-- De Giorgi blow-up of `Metric.ball x (r * R)` at `x` with scale `r > 0` is `Metric.ball 0 R`. -/
@[simp] theorem deGiorgiBlowUp_ball (x : E) (R : ℝ) {r : ℝ} (hr : 0 < r) :
    deGiorgiBlowUp (Metric.ball x (r * R)) x r = Metric.ball 0 R := by
  rw [deGiorgiBlowUp_ball_general x x (r * R) hr, sub_self, smul_zero, inv_mul_cancel_left₀ hr.ne']

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Haar measure scaling of `deGiorgiBlowUp s x r` for `r > 0`. -/
theorem measure_deGiorgiBlowUp (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (x : E)
    {r : ℝ} (hr : 0 < r) :
    μ (deGiorgiBlowUp s x r) = ENNReal.ofReal (r ^ (-(Module.finrank ℝ E : ℝ))) * μ s := by
  rw [deGiorgiBlowUp_eq_inv_smul_preimage s x hr.ne', Measure.addHaar_smul,
    measure_preimage_add, abs_of_pos (pow_pos (inv_pos.2 hr) _), inv_pow, ← Real.rpow_natCast,
    ← Real.rpow_neg hr.le]

/-- If `s =ᵐ[μ] t` and `r ≠ 0`, then `deGiorgiBlowUp s x r =ᵐ[μ] deGiorgiBlowUp t x r`. -/
theorem deGiorgiBlowUp_ae_eq {μ : Measure E} [μ.IsAddHaarMeasure] {s t : Set E}
    (hst : s =ᵐ[μ] t) (x : E) {r : ℝ} (hr : r ≠ 0) :
    deGiorgiBlowUp s x r =ᵐ[μ] deGiorgiBlowUp t x r := by
  rw [ae_eq_set] at hst ⊢
  constructor <;> rw [← deGiorgiBlowUp_sdiff, deGiorgiBlowUp_eq_inv_smul_preimage _ x hr,
    Measure.addHaar_smul, measure_preimage_add]
  · rw [hst.1, mul_zero]
  · rw [hst.2, mul_zero]

end DeGiorgiBlowUp

section InnerProductBlowUp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- De Giorgi blow-up of an open half-space `halfSpaceLT e a` at `x` with scale `r > 0`. -/
theorem deGiorgiBlowUp_halfSpaceLT (e x : E) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    deGiorgiBlowUp (halfSpaceLT e a) x r = halfSpaceLT e ((a - ⟪x, e⟫_ℝ) / r) := by
  ext z; simp only [mem_deGiorgiBlowUp, mem_halfSpaceLT, inner_add_left, inner_smul_left,
    RCLike.conj_to_real]
  rw [lt_div_iff₀' hr, lt_sub_iff_add_lt']

/-- De Giorgi blow-up of a closed half-space `halfSpaceLE e a` at `x` with scale `r > 0`. -/
theorem deGiorgiBlowUp_halfSpaceLE (e x : E) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    deGiorgiBlowUp (halfSpaceLE e a) x r = halfSpaceLE e ((a - ⟪x, e⟫_ℝ) / r) := by
  ext z; simp only [mem_deGiorgiBlowUp, mem_halfSpaceLE, inner_add_left, inner_smul_left,
    RCLike.conj_to_real]
  rw [le_div_iff₀' hr, le_sub_iff_add_le']

@[simp] theorem deGiorgiBlowUp_halfSpaceLT_of_mem_hyperplane {e x : E} {a : ℝ}
    (hx : x ∈ hyperplane e a) {r : ℝ} (hr : 0 < r) :
    deGiorgiBlowUp (halfSpaceLT e a) x r = halfSpaceLT e 0 := by
  rw [deGiorgiBlowUp_halfSpaceLT e x a hr, mem_hyperplane.1 hx, sub_self, zero_div]

@[simp] theorem deGiorgiBlowUp_halfSpaceLE_of_mem_hyperplane {e x : E} {a : ℝ}
    (hx : x ∈ hyperplane e a) {r : ℝ} (hr : 0 < r) :
    deGiorgiBlowUp (halfSpaceLE e a) x r = halfSpaceLE e 0 := by
  rw [deGiorgiBlowUp_halfSpaceLE e x a hr, mem_hyperplane.1 hx, sub_self, zero_div]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Volume scaling of `deGiorgiBlowUp` on balls** for `0 < r`. -/
theorem volume_deGiorgiBlowUp_inter_ball (s : Set E) (x : E) (R : ℝ) {r : ℝ} (hr : 0 < r) :
    volume (deGiorgiBlowUp s x r ∩ Metric.ball 0 R) =
      ENNReal.ofReal (r ^ (-(Module.finrank ℝ E : ℝ))) * volume (s ∩ Metric.ball x (r * R)) := by
  rw [← deGiorgiBlowUp_ball x R hr, ← deGiorgiBlowUp_inter, measure_deGiorgiBlowUp volume _ x hr]

/-- **Relative perimeter scaling of `deGiorgiBlowUp` on balls** for `0 < r`. -/
theorem relativePerimeter_deGiorgiBlowUp_ball (s : Set E) (x : E) (R : ℝ) {r : ℝ} (hr : 0 < r) :
    relativePerimeter volume (openBall 0 R) (deGiorgiBlowUp s x r) =
      ENNReal.ofReal (r ^ (1 - (Module.finrank ℝ E : ℝ))) *
        relativePerimeter volume (openBall x (r * R)) s := by
  have hcomap1 : openBall (0 : E) R =
      (openBall (0 : E) (r * R)).comap ⟨((r⁻¹)⁻¹ • ·), by fun_prop⟩ := by
    ext z; change dist z 0 < R ↔ dist ((r⁻¹)⁻¹ • z) 0 < r * R
    simp only [dist_zero_right, inv_inv, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_mul_iff_right₀ hr).symm
  have hcomap2 : openBall (0 : E) (r * R) =
      (openBall x (r * R)).comap ⟨(x + ·), by fun_prop⟩ := by ext z; simp [openBall, dist_eq_norm]
  have hexp : (r⁻¹) ^ Module.finrank ℝ E / r⁻¹ = r ^ (1 - (Module.finrank ℝ E : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one, Real.rpow_neg hr.le,
      Real.rpow_natCast, inv_pow, div_inv_eq_mul, mul_comm]
  rw [deGiorgiBlowUp_eq_inv_smul_preimage s x hr.ne', hcomap1,
    relativePerimeter_smul (openBall 0 (r * R)) (inv_pos.2 hr), hexp, hcomap2,
    relativePerimeter_preimage_add_left]

/-! ### Section 2: De Giorgi outward unit normal and reduced boundary -/

/-- A set `s ⊆ E` has **De Giorgi blow-up** equal to `halfSpaceLT ν 0` at `x : E` with unit normal
`ν : E` if `‖ν‖ = 1` and `volume ((deGiorgiBlowUp s x r ∆ halfSpaceLT ν 0) ∩ ball 0 1) → 0`. -/
def HasDeGiorgiBlowUp (s : Set E) (x : E) (ν : E) : Prop :=
  ‖ν‖ = 1 ∧ Tendsto
    (fun r : ℝ ↦ volume ((deGiorgiBlowUp s x r ∆ halfSpaceLT ν 0) ∩ Metric.ball 0 1))
    (𝓝[>] 0) (𝓝 0)

/-- A set `s ⊆ E` has **De Giorgi outward unit normal** `ν : E` at `x : E` if `HasDeGiorgiBlowUp`
holds and `relativePerimeter volume (openBall x r) s / volume (ball (0 : H_ν) r) → 1`. -/
def HasDeGiorgiNormal (s : Set E) (x : E) (ν : E) : Prop :=
  HasDeGiorgiBlowUp s x ν ∧ Tendsto
    (fun r : ℝ ↦ relativePerimeter volume (openBall x r) s /
      volume (Metric.ball (0 : orthogonalHyperplane ν) r))
    (𝓝[>] 0) (𝓝 1)

/-- The **De Giorgi reduced boundary** `∂*s` of `s ⊆ E`, consisting of all points `x : E` at
which `s` admits a De Giorgi outward unit normal `ν`. -/
def reducedBoundary (s : Set E) : Set E := {x : E | ∃ ν : E, HasDeGiorgiNormal s x ν}

/-- The **De Giorgi outward unit normal** `deGiorgiNormal s x` at `x : E`, equal to the unique `ν`
satisfying `HasDeGiorgiNormal s x ν` when `x ∈ reducedBoundary s`, and `0` otherwise. -/
def deGiorgiNormal (s : Set E) (x : E) : E :=
  open Classical in if hx : x ∈ reducedBoundary s then Classical.choose hx else 0

theorem HasDeGiorgiBlowUp.norm_eq_one {s : Set E} {x ν : E} (h : HasDeGiorgiBlowUp s x ν) :
    ‖ν‖ = 1 := h.1
theorem HasDeGiorgiBlowUp.ne_zero {s : Set E} {x ν : E} (h : HasDeGiorgiBlowUp s x ν) :
    ν ≠ 0 := by intro h0; have := h.1; simp [h0] at this
theorem HasDeGiorgiNormal.hasDeGiorgiBlowUp {s : Set E} {x ν : E} (h : HasDeGiorgiNormal s x ν) :
    HasDeGiorgiBlowUp s x ν := h.1
theorem HasDeGiorgiNormal.norm_eq_one {s : Set E} {x ν : E} (h : HasDeGiorgiNormal s x ν) :
    ‖ν‖ = 1 := h.1.1
theorem HasDeGiorgiNormal.mem_reducedBoundary {s : Set E} {x ν : E} (h : HasDeGiorgiNormal s x ν) :
    x ∈ reducedBoundary s := ⟨ν, h⟩

theorem hasDeGiorgiNormal_deGiorgiNormal {s : Set E} {x : E} (hx : x ∈ reducedBoundary s) :
    HasDeGiorgiNormal s x (deGiorgiNormal s x) := by
  classical simpa [deGiorgiNormal, hx] using Classical.choose_spec hx
theorem norm_deGiorgiNormal_of_mem {s : Set E} {x : E} (hx : x ∈ reducedBoundary s) :
    ‖deGiorgiNormal s x‖ = 1 := (hasDeGiorgiNormal_deGiorgiNormal hx).norm_eq_one
theorem deGiorgiNormal_of_notMem_reducedBoundary {s : Set E} {x : E}
    (hx : x ∉ reducedBoundary s) : deGiorgiNormal s x = 0 := by classical simp [deGiorgiNormal, hx]

theorem HasDeGiorgiBlowUp.congr_ae {s t : Set E} {x ν : E} (h : HasDeGiorgiBlowUp s x ν)
    (hst : s =ᵐ[volume] t) : HasDeGiorgiBlowUp t x ν := by
  refine ⟨h.1, h.2.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  exact measure_congr (EventuallyEqSet.inter
    (EventuallyEqSet.symmDiff (deGiorgiBlowUp_ae_eq hst x hr.ne') EventuallyEq.rfl)
    EventuallyEq.rfl)
theorem hasDeGiorgiBlowUp_congr_ae {s t : Set E} (hst : s =ᵐ[volume] t) {x ν : E} :
    HasDeGiorgiBlowUp s x ν ↔ HasDeGiorgiBlowUp t x ν :=
  ⟨fun h ↦ h.congr_ae hst, fun h ↦ h.congr_ae hst.symm⟩
theorem HasDeGiorgiNormal.congr_ae {s t : Set E} {x ν : E} (h : HasDeGiorgiNormal s x ν)
    (hst : s =ᵐ[volume] t) : HasDeGiorgiNormal t x ν := by
  refine ⟨h.1.congr_ae hst, h.2.congr fun r ↦ ?_⟩
  rw [relativePerimeter_congr_ae (ae_restrict_of_ae hst)]
theorem hasDeGiorgiNormal_congr_ae {s t : Set E} (hst : s =ᵐ[volume] t) {x ν : E} :
    HasDeGiorgiNormal s x ν ↔ HasDeGiorgiNormal t x ν :=
  ⟨fun h ↦ h.congr_ae hst, fun h ↦ h.congr_ae hst.symm⟩

/-- **A.e.-invariance of `reducedBoundary`**. -/
theorem reducedBoundary_congr_ae {s t : Set E} (hst : s =ᵐ[volume] t) :
    reducedBoundary s = reducedBoundary t := by
  ext x; simp [reducedBoundary, hasDeGiorgiNormal_congr_ae hst]

/-- **A.e.-invariance of `deGiorgiNormal`**. -/
theorem deGiorgiNormal_congr_ae {s t : Set E} (hst : s =ᵐ[volume] t) (x : E) :
    deGiorgiNormal s x = deGiorgiNormal t x := by
  have hrb := reducedBoundary_congr_ae hst
  by_cases hx : x ∈ reducedBoundary s
  · have hxt : x ∈ reducedBoundary t := hrb ▸ hx
    have h1 : ∀ ν, HasDeGiorgiNormal s x ν ↔ HasDeGiorgiNormal t x ν :=
      fun _ ↦ hasDeGiorgiNormal_congr_ae hst
    simp only [deGiorgiNormal, hx, hxt, dite_true]
    congr 1; ext ν; exact h1 ν
  · rw [deGiorgiNormal_of_notMem_reducedBoundary hx,
      deGiorgiNormal_of_notMem_reducedBoundary (hrb ▸ hx)]

/-- If two unit vectors `ν₁, ν₂` have
`volume ((halfSpaceLT ν₁ 0 ∆ halfSpaceLT ν₂ 0) ∩ ball 0 1) = 0`, then `ν₁ = ν₂`. -/
theorem eq_of_volume_symmDiff_halfSpaceLT_inter_ball_eq_zero {ν₁ ν₂ : E}
    (hν₁ : ‖ν₁‖ = 1) (hν₂ : ‖ν₂‖ = 1)
    (h0 : volume ((halfSpaceLT ν₁ 0 ∆ halfSpaceLT ν₂ 0) ∩ Metric.ball 0 1) = 0) :
    ν₁ = ν₂ := by
  by_contra hne
  let U : Set E := (halfSpaceLT ν₁ 0 ∩ Metric.ball 0 1) \ halfSpaceLE ν₂ 0
  have hU_open : IsOpen U :=
    ((isOpen_halfSpaceLT ν₁ 0).inter Metric.isOpen_ball).sdiff (isClosed_halfSpaceLE ν₂ 0)
  have hU_sub : U ⊆ (halfSpaceLT ν₁ 0 ∆ halfSpaceLT ν₂ 0) ∩ Metric.ball 0 1 :=
    fun z ⟨⟨hz₁, hzb⟩, hz₂⟩ ↦
      ⟨Or.inl ⟨hz₁, fun h ↦ hz₂ (halfSpaceLT_subset_halfSpaceLE ν₂ 0 h)⟩, hzb⟩
  let z : E := (1 / 3 : ℝ) • (ν₂ - ν₁)
  have hdiff_pos : 0 < ‖ν₂ - ν₁‖ ^ 2 := sq_pos_of_pos (norm_sub_pos_iff.2 (Ne.symm hne))
  have hsq : ‖ν₂ - ν₁‖ ^ 2 = 2 - 2 * ⟪ν₂, ν₁⟫_ℝ := by rw [norm_sub_sq_real, hν₂, hν₁]; ring
  have hlt1 : ⟪ν₂, ν₁⟫_ℝ < 1 := by linarith
  have hz_mem : z ∈ U := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [z, mem_halfSpaceLT, inner_smul_left, inner_sub_left, RCLike.conj_to_real,
        real_inner_self_eq_norm_mul_norm, hν₁]; linarith
    · rw [Metric.mem_ball, dist_zero_right]
      calc ‖(1 / 3 : ℝ) • (ν₂ - ν₁)‖
          = (1 / 3 : ℝ) * ‖ν₂ - ν₁‖ := by rw [norm_smul, Real.norm_eq_abs]; norm_num
        _ ≤ (1 / 3 : ℝ) * (‖ν₂‖ + ‖ν₁‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le ν₂ ν₁) (by positivity)
        _ < 1 := by linarith
    · simp only [z, mem_halfSpaceLE, not_le, inner_smul_left, inner_sub_left, RCLike.conj_to_real,
        real_inner_self_eq_norm_mul_norm, hν₂, real_inner_comm ν₂ ν₁]; linarith
  exact (hU_open.measure_pos volume ⟨z, hz_mem⟩).ne' (measure_mono_null hU_sub h0)

/-- **Uniqueness of the De Giorgi blow-up normal**. -/
theorem HasDeGiorgiBlowUp.unique {s : Set E} {x ν₁ ν₂ : E}
    (h₁ : HasDeGiorgiBlowUp s x ν₁) (h₂ : HasDeGiorgiBlowUp s x ν₂) : ν₁ = ν₂ := by
  refine eq_of_volume_symmDiff_halfSpaceLT_inter_ball_eq_zero h₁.1 h₂.1 (nonpos_iff_eq_zero.1 ?_)
  have hsum : Tendsto
      (fun r : ℝ ↦ volume ((deGiorgiBlowUp s x r ∆ halfSpaceLT ν₁ 0) ∩ Metric.ball 0 1) +
        volume ((deGiorgiBlowUp s x r ∆ halfSpaceLT ν₂ 0) ∩ Metric.ball 0 1))
      (𝓝[>] 0) (𝓝 0) := by simpa using h₁.2.add h₂.2
  refine ge_of_tendsto hsum (Eventually.of_forall fun r ↦ ?_)
  have hsub : (halfSpaceLT ν₁ 0 ∆ halfSpaceLT ν₂ 0) ∩ Metric.ball 0 1 ⊆
      ((deGiorgiBlowUp s x r ∆ halfSpaceLT ν₁ 0) ∩ Metric.ball 0 1) ∪
        ((deGiorgiBlowUp s x r ∆ halfSpaceLT ν₂ 0) ∩ Metric.ball 0 1) := by
    intro z ⟨hz_sd, hzb⟩; rw [symmDiff_comm _ (halfSpaceLT ν₁ 0)]
    rcases symmDiff_triangle (halfSpaceLT ν₁ 0) (deGiorgiBlowUp s x r) (halfSpaceLT ν₂ 0) hz_sd with
      h1 | h2
    · exact Or.inl ⟨h1, hzb⟩
    · exact Or.inr ⟨h2, hzb⟩
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- **Uniqueness of the De Giorgi outward unit normal**. -/
theorem HasDeGiorgiNormal.unique {s : Set E} {x ν₁ ν₂ : E}
    (h₁ : HasDeGiorgiNormal s x ν₁) (h₂ : HasDeGiorgiNormal s x ν₂) : ν₁ = ν₂ :=
  h₁.1.unique h₂.1

theorem HasDeGiorgiNormal.deGiorgiNormal_eq {s : Set E} {x ν : E}
    (h : HasDeGiorgiNormal s x ν) : deGiorgiNormal s x = ν :=
  (hasDeGiorgiNormal_deGiorgiNormal h.mem_reducedBoundary).unique h

/-- Any open ball `Metric.ball x r` centered on `hyperplane e a` (`e ≠ 0`) is bisected by
`halfSpaceLT e a`. -/
theorem volume_halfSpaceLT_inter_ball_of_mem_hyperplane [Nontrivial E] {e x : E} (he : e ≠ 0)
    {a : ℝ} (hx : x ∈ hyperplane e a) (r : ℝ) :
    2 * volume (halfSpaceLT e a ∩ Metric.ball x r) = volume (Metric.ball x r) := by
  have hae : (halfSpaceLT e a ∩ Metric.ball x r : Set E) =ᵐ[volume]
      halfSpaceLT e a ∩ Metric.closedBall x r :=
    EventuallyEqSet.inter EventuallyEq.rfl (closedBall_ae_eq_ball x r).symm
  rw [measure_congr hae, measure_congr (closedBall_ae_eq_ball x r).symm]
  exact volume_halfSpaceLT_inter_closedBall_of_mem_hyperplane he hx r

/-- **Measure-theoretic density `1 / 2` on balls** at any point admitting a De Giorgi blow-up. -/
theorem HasDeGiorgiBlowUp.tendsto_density_one_half {s : Set E} {x ν : E}
    (h : HasDeGiorgiBlowUp s x ν) :
    Tendsto (fun r : ℝ ↦ volume (s ∩ Metric.ball x r) / volume (Metric.ball x r))
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have : Nontrivial E := ⟨⟨ν, 0, h.ne_zero⟩⟩
  let B : Set E := Metric.ball (0 : E) 1
  let H : Set E := halfSpaceLT ν 0
  have hB_pos : 0 < volume B := Metric.measure_ball_pos volume 0 zero_lt_one
  have hB_fin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hHB : 2 * volume (H ∩ B) = volume B :=
    volume_halfSpaceLT_inter_ball_of_mem_hyperplane h.ne_zero (by simp [hyperplane]) 1
  have hHB_pos : volume (H ∩ B) ≠ 0 := fun h0 ↦ hB_pos.ne' (by rw [← hHB, h0, mul_zero])
  have hHB_fin : volume (H ∩ B) ≠ ⊤ :=
    fun htop ↦ hB_fin (by rw [← hHB, htop, ENNReal.mul_top two_ne_zero])
  have hratio_HB : volume (H ∩ B) / volume B = 1 / 2 := by
    rw [← hHB, ← ENNReal.mul_div_mul_right 1 2 hHB_pos hHB_fin, one_mul]
  have hvol_tendsto : Tendsto (fun r : ℝ ↦ volume (deGiorgiBlowUp s x r ∩ B))
      (𝓝[>] 0) (𝓝 (volume (H ∩ B))) := by
    have hlow : Tendsto (fun r : ℝ ↦ volume (H ∩ B) -
        volume ((deGiorgiBlowUp s x r ∆ H) ∩ B)) (𝓝[>] 0) (𝓝 (volume (H ∩ B) - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds h.2 (Or.inl hHB_fin)
    have hhigh : Tendsto (fun r : ℝ ↦ volume (H ∩ B) +
        volume ((deGiorgiBlowUp s x r ∆ H) ∩ B)) (𝓝[>] 0) (𝓝 (volume (H ∩ B) + 0)) :=
      tendsto_const_nhds.add h.2
    rw [tsub_zero] at hlow; rw [add_zero] at hhigh
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh (fun r ↦ ?_) (fun r ↦ ?_)
    · rw [tsub_le_iff_right]
      have hsub : H ∩ B ⊆ (deGiorgiBlowUp s x r ∩ B) ∪ ((deGiorgiBlowUp s x r ∆ H) ∩ B) :=
        fun z ⟨hzH, hzB⟩ ↦ (em (z ∈ deGiorgiBlowUp s x r)).elim
          (fun hzs ↦ Or.inl ⟨hzs, hzB⟩) (fun hzs ↦ Or.inr ⟨Or.inr ⟨hzH, hzs⟩, hzB⟩)
      exact (measure_mono hsub).trans (measure_union_le _ _)
    · have hsub : deGiorgiBlowUp s x r ∩ B ⊆ (H ∩ B) ∪ ((deGiorgiBlowUp s x r ∆ H) ∩ B) :=
        fun z ⟨hzs, hzB⟩ ↦ (em (z ∈ H)).elim
          (fun hzH ↦ Or.inl ⟨hzH, hzB⟩) (fun hzH ↦ Or.inr ⟨Or.inl ⟨hzs, hzH⟩, hzB⟩)
      exact (measure_mono hsub).trans (measure_union_le _ _)
  have hdiv : Tendsto (fun r : ℝ ↦ volume (deGiorgiBlowUp s x r ∩ B) / volume B)
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
    rw [← hratio_HB]; exact ENNReal.Tendsto.div_const hvol_tendsto (Or.inr hB_pos.ne')
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hscale1 := volume_deGiorgiBlowUp_inter_ball s x 1 hr
  have hscale2 := volume_deGiorgiBlowUp_inter_ball (Set.univ : Set E) x 1 hr
  rw [mul_one] at hscale1
  rw [deGiorgiBlowUp_univ, Set.univ_inter, Set.univ_inter, mul_one] at hscale2
  have hc0 : ENNReal.ofReal (r ^ (-(Module.finrank ℝ E : ℝ))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (Real.rpow_pos_of_pos hr _)
  dsimp only [B]; rw [hscale1, hscale2, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]

/-- Every point `x` with `HasDeGiorgiBlowUp s x ν` has `HasMeasureDensityAt volume s x (1 / 2)`. -/
theorem HasDeGiorgiBlowUp.hasMeasureDensityAt {s : Set E} {x ν : E}
    (h : HasDeGiorgiBlowUp s x ν) : HasMeasureDensityAt volume s x (1 / 2) :=
  hasMeasureDensityAt_iff_tendsto_ball_of_isAddHaarMeasure.2 h.tendsto_density_one_half

/-- Every point `x` with `HasDeGiorgiBlowUp s x ν` belongs to `essentialBoundary volume s`. -/
theorem HasDeGiorgiBlowUp.mem_essentialBoundary {s : Set E} {x ν : E}
    (h : HasDeGiorgiBlowUp s x ν) : x ∈ essentialBoundary volume s := by
  have hd := h.hasMeasureDensityAt
  rw [essentialBoundary_eq_compl_inter_compl]
  exact ⟨fun h1 ↦ by have := hd.unique h1; norm_num at this,
    fun h0 ↦ by have := hd.unique h0; norm_num at this⟩

/-- **The reduced boundary is contained in the Federer essential boundary**. -/
theorem reducedBoundary_subset_essentialBoundary (s : Set E) :
    reducedBoundary s ⊆ essentialBoundary volume s :=
  fun _ ⟨_, hν⟩ ↦ hν.1.mem_essentialBoundary

/-- **The reduced boundary is contained in the topological frontier**. -/
theorem reducedBoundary_subset_frontier (s : Set E) :
    reducedBoundary s ⊆ frontier s :=
  (reducedBoundary_subset_essentialBoundary s).trans (essentialBoundary_subset_frontier s)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem orthogonalHyperplane_neg (e : E) :
    orthogonalHyperplane (-e) = orthogonalHyperplane e := by
  ext y; simp [mem_orthogonalHyperplane_iff]

theorem volume_ball_orthogonalHyperplane_neg (e : E) (r : ℝ) :
    volume (Metric.ball (0 : orthogonalHyperplane (-e)) r) =
      volume (Metric.ball (0 : orthogonalHyperplane e) r) := by
  let L : orthogonalHyperplane (-e) ≃ₗᵢ[ℝ] orthogonalHyperplane e :=
    LinearIsometryEquiv.ofEq _ _ (orthogonalHyperplane_neg e)
  have hpre : L ⁻¹' Metric.ball (0 : orthogonalHyperplane e) r =
      Metric.ball (0 : orthogonalHyperplane (-e)) r := by
    ext y; simp [L, Metric.mem_ball, dist_zero_right]
  rw [← hpre, L.measurePreserving.measure_preimage_emb
    L.toHomeomorph.toMeasurableEquiv.measurableEmbedding]

/-- **Complement reversal for `HasDeGiorgiBlowUp`**. -/
theorem HasDeGiorgiBlowUp.compl {s : Set E} {x ν : E} (h : HasDeGiorgiBlowUp s x ν) :
    HasDeGiorgiBlowUp sᶜ x (-ν) := by
  refine ⟨by rw [norm_neg, h.1], h.2.congr fun r ↦ ?_⟩
  have hae : halfSpaceLT (-ν) 0 =ᵐ[volume] (halfSpaceLT ν 0)ᶜ := by
    rw [compl_halfSpaceLT, ← halfSpaceLE_neg, neg_zero]
    exact halfSpaceLT_ae_eq_halfSpaceLE (neg_ne_zero.2 h.ne_zero) 0
  have hsd : (deGiorgiBlowUp sᶜ x r ∆ halfSpaceLT (-ν) 0) ∩ Metric.ball 0 1 =ᵐ[volume]
      (deGiorgiBlowUp s x r ∆ halfSpaceLT ν 0) ∩ Metric.ball 0 1 := by
    rw [← compl_symmDiff_compl (deGiorgiBlowUp s x r) (halfSpaceLT ν 0), ← deGiorgiBlowUp_compl]
    exact EventuallyEqSet.inter (EventuallyEqSet.symmDiff EventuallyEq.rfl hae) EventuallyEq.rfl
  exact (measure_congr hsd).symm

@[simp] theorem hasDeGiorgiBlowUp_compl_iff {s : Set E} {x ν : E} :
    HasDeGiorgiBlowUp sᶜ x (-ν) ↔ HasDeGiorgiBlowUp s x ν :=
  ⟨fun h ↦ by simpa using h.compl, fun h ↦ h.compl⟩

/-- **Complement reversal for `HasDeGiorgiNormal`**. -/
theorem HasDeGiorgiNormal.compl {s : Set E} {x ν : E} (h : HasDeGiorgiNormal s x ν) :
    HasDeGiorgiNormal sᶜ x (-ν) := by
  refine ⟨h.1.compl, h.2.congr fun r ↦ ?_⟩
  rw [relativePerimeter_compl, volume_ball_orthogonalHyperplane_neg]

@[simp] theorem hasDeGiorgiNormal_compl_iff {s : Set E} {x ν : E} :
    HasDeGiorgiNormal sᶜ x (-ν) ↔ HasDeGiorgiNormal s x ν :=
  ⟨fun h ↦ by simpa using h.compl, fun h ↦ h.compl⟩

/-- **Complement invariance of `reducedBoundary`**: `reducedBoundary sᶜ = reducedBoundary s`. -/
@[simp] theorem reducedBoundary_compl (s : Set E) :
    reducedBoundary sᶜ = reducedBoundary s := by
  ext x; exact ⟨fun ⟨ν, hν⟩ ↦ ⟨-ν, by simpa using hν.compl⟩, fun ⟨ν, hν⟩ ↦ ⟨-ν, hν.compl⟩⟩

/-- **Complement reversal of `deGiorgiNormal`**: `deGiorgiNormal sᶜ x = -deGiorgiNormal s x`. -/
@[simp] theorem deGiorgiNormal_compl (s : Set E) (x : E) :
    deGiorgiNormal sᶜ x = -deGiorgiNormal s x := by
  by_cases hx : x ∈ reducedBoundary s
  · exact ((hasDeGiorgiNormal_deGiorgiNormal hx).compl).deGiorgiNormal_eq
  · have hxc : x ∉ reducedBoundary sᶜ := by rwa [reducedBoundary_compl]
    rw [deGiorgiNormal_of_notMem_reducedBoundary hx,
      deGiorgiNormal_of_notMem_reducedBoundary hxc, neg_zero]

/-! ### Section 3: Half-spaces, balls, ball exteriors, punctured balls, and dense modifications -/

/-- At every point `x ∈ hyperplane e a` (`‖e‖ = 1`), `halfSpaceLT e a` has De Giorgi blow-up
with unit normal `e`. -/
theorem hasDeGiorgiBlowUp_halfSpaceLT {e x : E} (he : ‖e‖ = 1) {a : ℝ}
    (hx : x ∈ hyperplane e a) : HasDeGiorgiBlowUp (halfSpaceLT e a) x e := by
  refine ⟨he, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp [deGiorgiBlowUp_halfSpaceLT_of_mem_hyperplane hx hr]

/-- **At every point `x ∈ hyperplane e a` (`‖e‖ = 1`), `halfSpaceLT e a` has De Giorgi outward
unit normal `e`**. -/
theorem hasDeGiorgiNormal_halfSpaceLT {e x : E} (he : ‖e‖ = 1) {a : ℝ}
    (hx : x ∈ hyperplane e a) : HasDeGiorgiNormal (halfSpaceLT e a) x e := by
  refine ⟨hasDeGiorgiBlowUp_halfSpaceLT he hx, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hperim : relativePerimeter volume (openBall x r) (halfSpaceLT e a) =
      volume (Metric.ball (0 : orthogonalHyperplane e) r) := by
    rw [← mem_hyperplane.1 hx]; exact relativePerimeter_halfSpaceLT_ball_inner he x r
  rw [hperim, ENNReal.div_self (Metric.measure_ball_pos volume 0 hr).ne' measure_ball_lt_top.ne]

/-- **The reduced boundary of `halfSpaceLT e a` (`‖e‖ = 1`) is `hyperplane e a`**. -/
@[simp] theorem reducedBoundary_halfSpaceLT {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    reducedBoundary (halfSpaceLT e a) = hyperplane e a := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  refine Subset.antisymm ?_ (fun x hx ↦ (hasDeGiorgiNormal_halfSpaceLT he hx).mem_reducedBoundary)
  rw [← essentialBoundary_halfSpaceLT he0 a]
  exact reducedBoundary_subset_essentialBoundary (halfSpaceLT e a)

theorem reducedBoundary_halfSpaceLT_eq_essentialBoundary {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    reducedBoundary (halfSpaceLT e a) = essentialBoundary volume (halfSpaceLT e a) := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  rw [reducedBoundary_halfSpaceLT he, essentialBoundary_halfSpaceLT he0]

/-- **Outward unit normal of `halfSpaceLT e a`** (`‖e‖ = 1`) on `hyperplane e a`. -/
theorem deGiorgiNormal_halfSpaceLT {e x : E} (he : ‖e‖ = 1) {a : ℝ}
    (hx : x ∈ hyperplane e a) : deGiorgiNormal (halfSpaceLT e a) x = e :=
  (hasDeGiorgiNormal_halfSpaceLT he hx).deGiorgiNormal_eq

@[simp] theorem reducedBoundary_halfSpaceLE {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    reducedBoundary (halfSpaceLE e a) = hyperplane e a := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  rw [← reducedBoundary_congr_ae (halfSpaceLT_ae_eq_halfSpaceLE he0 a),
    reducedBoundary_halfSpaceLT he]
theorem deGiorgiNormal_halfSpaceLE {e x : E} (he : ‖e‖ = 1) {a : ℝ}
    (hx : x ∈ hyperplane e a) : deGiorgiNormal (halfSpaceLE e a) x = e := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  rw [← deGiorgiNormal_congr_ae (halfSpaceLT_ae_eq_halfSpaceLE he0 a),
    deGiorgiNormal_halfSpaceLT he hx]
@[simp] theorem reducedBoundary_halfSpaceGE {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    reducedBoundary (halfSpaceGE e a) = hyperplane e a := by
  rw [← compl_halfSpaceLT, reducedBoundary_compl, reducedBoundary_halfSpaceLT he]
theorem deGiorgiNormal_halfSpaceGE {e x : E} (he : ‖e‖ = 1) {a : ℝ}
    (hx : x ∈ hyperplane e a) : deGiorgiNormal (halfSpaceGE e a) x = -e := by
  rw [← compl_halfSpaceLT, deGiorgiNormal_compl, deGiorgiNormal_halfSpaceLT he hx]
@[simp] theorem reducedBoundary_halfSpaceGT {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    reducedBoundary (halfSpaceGT e a) = hyperplane e a := by
  rw [← compl_halfSpaceLE, reducedBoundary_compl, reducedBoundary_halfSpaceLE he]
theorem deGiorgiNormal_halfSpaceGT {e x : E} (he : ‖e‖ = 1) {a : ℝ}
    (hx : x ∈ hyperplane e a) : deGiorgiNormal (halfSpaceGT e a) x = -e := by
  rw [← compl_halfSpaceLE, deGiorgiNormal_compl, deGiorgiNormal_halfSpaceLE he hx]

/-- Upper bound on `volume (slab e a b ∩ Metric.ball 0 r)` (`‖e‖ = 1`). -/
theorem volume_slab_inter_ball_le {e : E} (he : ‖e‖ = 1) (a b r : ℝ) :
    volume (slab e a b ∩ Metric.ball 0 r) ≤
      ENNReal.ofReal (b - a) * volume (Metric.ball (0 : orthogonalHyperplane e) r) := by
  have hmp := measurePreserving_orthogonalHyperplaneProdMeasurableEquiv_symm he
  have hsub : slab e a b ∩ Metric.ball 0 r ⊆
      (orthogonalHyperplaneProdMeasurableEquiv he).symm ⁻¹'
        (Metric.ball (0 : orthogonalHyperplane e) r ×ˢ Set.Icc a b) := by
    intro x ⟨hx_slab, hx_ball⟩
    rw [Set.mem_preimage, orthogonalHyperplaneProdMeasurableEquiv_symm_apply, Set.mem_prod]
    refine ⟨?_, hx_slab⟩
    rw [Metric.mem_ball, dist_zero_right] at hx_ball ⊢
    have hpyth : ‖x‖ ^ 2 =
        ‖(orthogonalHyperplane e).orthogonalProjectionOnto x‖ ^ 2 + ⟪x, e⟫_ℝ ^ 2 := by
      conv_lhs => rw [← orthogonalProjection_orthogonalHyperplane_add_inner_smul he x]
      exact norm_coe_add_smul_sq he _ _
    have hr_pos : 0 < r := (norm_nonneg x).trans_lt hx_ball
    rw [← sq_lt_sq₀ (norm_nonneg _) hr_pos.le]
    nlinarith [sq_nonneg ⟪x, e⟫_ℝ, sq_lt_sq₀ (norm_nonneg x) hr_pos.le |>.2 hx_ball]
  calc volume (slab e a b ∩ Metric.ball 0 r)
      ≤ volume ((orthogonalHyperplaneProdMeasurableEquiv he).symm ⁻¹'
          (Metric.ball (0 : orthogonalHyperplane e) r ×ˢ Set.Icc a b)) := measure_mono hsub
    _ = (volume.prod volume) (Metric.ball (0 : orthogonalHyperplane e) r ×ˢ Set.Icc a b) :=
        hmp.measure_preimage
          (Metric.isOpen_ball.measurableSet.prod measurableSet_Icc).nullMeasurableSet
    _ = ENNReal.ofReal (b - a) * volume (Metric.ball (0 : orthogonalHyperplane e) r) := by
        rw [Measure.prod_prod, Real.volume_Icc, mul_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Exact algebraic characterization of `deGiorgiBlowUp (Metric.ball c R) x r`** at a boundary
point `x ∈ Metric.sphere c R` (`R > 0`, `r > 0`) in terms of `ν = R⁻¹ • (x - c)`. -/
theorem mem_deGiorgiBlowUp_ball_iff_inner {c x z : E} {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hx : x ∈ Metric.sphere c R) :
    z ∈ deGiorgiBlowUp (Metric.ball c R) x r ↔
      ⟪z, R⁻¹ • (x - c)⟫_ℝ < -(r / (2 * R)) * ‖z‖ ^ 2 := by
  have hxR : ‖x - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hx
  rw [mem_deGiorgiBlowUp, Metric.mem_ball, dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) hR.le]
  have hsub : x + r • z - c = (x - c) + r • z := by abel
  have hnorm : ‖(x - c) + r • z‖ ^ 2 =
      R ^ 2 + 2 * r * R * ⟪z, R⁻¹ • (x - c)⟫_ℝ + r ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_add_sq_real, hxR, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      inner_smul_right, inner_smul_right, real_inner_comm (x - c) z, mul_pow]
    have : R ≠ 0 := hR.ne'; field_simp
  rw [hsub, hnorm]
  have heq : 2 * r * R * (-(r / (2 * R)) * ‖z‖ ^ 2) = -(r ^ 2 * ‖z‖ ^ 2) := by
    have : R ≠ 0 := hR.ne'; field_simp
  have h2rR : 0 < 2 * r * R := by positivity
  constructor <;> intro h <;> nlinarith

/-- **De Giorgi blow-up of `Metric.ball c R` at `x ∈ Metric.sphere c R`** (`R > 0`). -/
theorem hasDeGiorgiBlowUp_ball {c x : E} {R : ℝ} (hR : 0 < R) (hx : x ∈ Metric.sphere c R) :
    HasDeGiorgiBlowUp (Metric.ball c R) x (R⁻¹ • (x - c)) := by
  set ν : E := R⁻¹ • (x - c)
  have hxR : ‖x - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hx
  have hν : ‖ν‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), hxR, inv_mul_cancel₀ hR.ne']
  refine ⟨hν, ?_⟩
  let C : ℝ≥0∞ := volume (Metric.ball (0 : orthogonalHyperplane ν) 1)
  have hC_fin : C ≠ ⊤ := measure_ball_lt_top.ne
  have hlim : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (r / (2 * R)) * C) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ ↦ ENNReal.ofReal (r / (2 * R))) :=
      ENNReal.continuous_ofReal.comp (continuous_id.div_const (2 * R))
    have h0 : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (r / (2 * R))) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa [zero_mul] using ENNReal.Tendsto.mul_const h0 (Or.inr hC_fin)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hsub : (deGiorgiBlowUp (Metric.ball c R) x r ∆ halfSpaceLT ν 0) ∩ Metric.ball 0 1 ⊆
      slab ν (-(r / (2 * R))) 0 ∩ Metric.ball 0 1 := by
    intro z ⟨hz_sd, hzb⟩
    have hz_norm : ‖z‖ ^ 2 < 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hzb; nlinarith [norm_nonneg z]
    have hrR_pos : 0 < r / (2 * R) := by positivity
    rcases hz_sd with ⟨hz_in, hz_not⟩ | ⟨hz_in, hz_not⟩
    · rw [mem_deGiorgiBlowUp_ball_iff_inner hR hr hx] at hz_in
      exfalso; exact hz_not (by
        rw [mem_halfSpaceLT]; exact hz_in.trans_le (by nlinarith [sq_nonneg ‖z‖]))
    · rw [mem_deGiorgiBlowUp_ball_iff_inner hR hr hx, not_lt] at hz_not
      rw [mem_halfSpaceLT] at hz_in
      exact ⟨⟨by nlinarith, hz_in.le⟩, hzb⟩
  exact (measure_mono hsub).trans
    (by simpa [C] using volume_slab_inter_ball_le hν (-(r / (2 * R))) 0 1)

theorem hasMeasureDensityAt_ball_of_mem_sphere {c x : E} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ Metric.sphere c R) : HasMeasureDensityAt volume (Metric.ball c R) x (1 / 2) :=
  (hasDeGiorgiBlowUp_ball hR hx).hasMeasureDensityAt

/-- **The essential boundary of `Metric.ball c R` (`R > 0`) is `Metric.sphere c R`**. -/
@[simp] theorem essentialBoundary_ball (c : E) {R : ℝ} (hR : 0 < R) :
    essentialBoundary volume (Metric.ball c R) = Metric.sphere c R :=
  Subset.antisymm (essentialBoundary_ball_subset_sphere c hR.ne')
    (fun _ hx ↦ (hasDeGiorgiBlowUp_ball hR hx).mem_essentialBoundary)

/-- **The essential interior of `Metric.ball c R` (`R > 0`) is `Metric.ball c R`**. -/
@[simp] theorem essentialInterior_ball (c : E) {R : ℝ} (hR : 0 < R) :
    essentialInterior volume (Metric.ball c R) = Metric.ball c R := by
  refine Subset.antisymm (fun x hx ↦ ?_) (ball_subset_essentialInterior_ball c R)
  have hcl : x ∈ Metric.closedBall c R := by
    rw [← closure_ball c hR.ne']; exact essentialInterior_subset_closure (Metric.ball c R) hx
  rcases eq_or_lt_of_le (Metric.mem_closedBall.1 hcl) with heq | hlt
  · exfalso
    have hsp : x ∈ essentialBoundary volume (Metric.ball c R) := by
      rw [essentialBoundary_ball c hR]; exact heq
    exact disjoint_left.1
      (disjoint_essentialBoundary_essentialInterior volume (Metric.ball c R)) hsp hx
  · exact hlt

/-- **The essential exterior of `Metric.ball c R` (`R > 0`) is `(Metric.closedBall c R)ᶜ`**. -/
@[simp] theorem essentialExterior_ball (c : E) {R : ℝ} (hR : 0 < R) :
    essentialExterior volume (Metric.ball c R) = (Metric.closedBall c R)ᶜ := by
  refine Subset.antisymm (fun x hx hcl ↦ ?_)
    (compl_closedBall_subset_essentialExterior_ball c hR.ne')
  rcases eq_or_lt_of_le (Metric.mem_closedBall.1 hcl) with heq | hlt
  · have hsp : x ∈ essentialBoundary volume (Metric.ball c R) := by
      rw [essentialBoundary_ball c hR]; exact heq
    exact disjoint_left.1
      (disjoint_essentialBoundary_essentialExterior volume (Metric.ball c R)) hsp hx
  · exact disjoint_left.1
      (disjoint_essentialInterior_essentialExterior volume (Metric.ball c R))
      (ball_subset_essentialInterior_ball c R hlt) hx

/-- `reducedBoundary (Metric.ball c R) ⊆ Metric.sphere c R` for `R ≠ 0`. -/
theorem reducedBoundary_ball_subset_sphere (c : E) {R : ℝ} (hR : R ≠ 0) :
    reducedBoundary (Metric.ball c R) ⊆ Metric.sphere c R :=
  (reducedBoundary_subset_essentialBoundary _).trans (essentialBoundary_ball_subset_sphere c hR)

/-- At any `x ∈ reducedBoundary (Metric.ball c R)` (`R > 0`),
`deGiorgiNormal (Metric.ball c R) x = R⁻¹ • (x - c)`. -/
theorem deGiorgiNormal_ball {c x : E} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ reducedBoundary (Metric.ball c R)) :
    deGiorgiNormal (Metric.ball c R) x = R⁻¹ • (x - c) :=
  (hasDeGiorgiNormal_deGiorgiNormal hx).1.unique
    (hasDeGiorgiBlowUp_ball hR (reducedBoundary_ball_subset_sphere c hR.ne' hx))

/-- **Exterior of a ball**: `(Metric.ball c R)ᶜ` has infinite volume and finite perimeter. -/
theorem volume_compl_ball_eq_top [Nontrivial E] (c : E) (R : ℝ) :
    volume (Metric.ball c R)ᶜ = ⊤ := by
  have huniv : volume (Set.univ : Set E) = ⊤ := measure_univ_of_isAddLeftInvariant volume
  by_contra hne
  have htop : volume (Metric.ball c R ∪ (Metric.ball c R)ᶜ) < ⊤ :=
    (measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨measure_ball_lt_top, lt_top_iff_ne_top.2 hne⟩)
  rw [Set.union_compl_self, huniv] at htop; exact lt_irrefl ⊤ htop

theorem hasFinitePerimeter_compl_ball (c : E) (R : ℝ) :
    HasFinitePerimeter volume (Metric.ball c R)ᶜ := (hasFinitePerimeter_ball c R).compl

theorem reducedBoundary_compl_ball (c : E) (R : ℝ) :
    reducedBoundary (Metric.ball c R)ᶜ = reducedBoundary (Metric.ball c R) :=
  reducedBoundary_compl (Metric.ball c R)

theorem essentialBoundary_compl_ball (c : E) {R : ℝ} (hR : 0 < R) :
    essentialBoundary volume (Metric.ball c R)ᶜ = Metric.sphere c R := by
  rw [essentialBoundary_compl (Metric.isOpen_ball.measurableSet.nullMeasurableSet),
    essentialBoundary_ball c hR]

/-- **Punctured ball `Metric.ball c R \ {c}`**: `reducedBoundary`, `essentialBoundary`, and
`perimeter` agree with those of `Metric.ball c R`, whereas `c ∈ frontier \ reducedBoundary`. -/
theorem reducedBoundary_punctured_ball [Nontrivial E] (c : E) (R : ℝ) :
    reducedBoundary (Metric.ball c R \ {c}) = reducedBoundary (Metric.ball c R) :=
  reducedBoundary_congr_ae (punctured_ball_ae_eq_ball c R)

theorem deGiorgiNormal_punctured_ball [Nontrivial E] (c : E) (R : ℝ) (x : E) :
    deGiorgiNormal (Metric.ball c R \ {c}) x = deGiorgiNormal (Metric.ball c R) x :=
  deGiorgiNormal_congr_ae (punctured_ball_ae_eq_ball c R) x

@[simp] theorem essentialBoundary_punctured_ball_eq_sphere [Nontrivial E] (c : E) {R : ℝ}
    (hR : 0 < R) : essentialBoundary volume (Metric.ball c R \ {c}) = Metric.sphere c R := by
  rw [essentialBoundary_punctured_ball, essentialBoundary_ball c hR]

theorem center_mem_frontier_diff_reducedBoundary_punctured_ball [Nontrivial E] (c : E) {R : ℝ}
    (hR : 0 < R) :
    c ∈ frontier (Metric.ball c R \ {c}) \ reducedBoundary (Metric.ball c R \ {c}) :=
  ⟨center_mem_frontier_punctured_ball c hR, fun hc ↦
    center_notMem_essentialBoundary_punctured_ball c hR
      (reducedBoundary_subset_essentialBoundary _ hc)⟩

theorem reducedBoundary_punctured_ball_ssubset_frontier [Nontrivial E] (c : E) {R : ℝ}
    (hR : 0 < R) :
    reducedBoundary (Metric.ball c R \ {c}) ⊂ frontier (Metric.ball c R \ {c}) :=
  (reducedBoundary_subset_frontier _).ssubset_of_mem_notMem
    (center_mem_frontier_punctured_ball c hR)
    (center_mem_frontier_diff_reducedBoundary_punctured_ball c hR).2

/-- **Ball union a null set `Metric.ball c R ∪ D`** (`volume D = 0`). -/
theorem ball_union_null_ae_eq_ball (c : E) (R : ℝ) {D : Set E} (hD : volume D = 0) :
    (Metric.ball c R ∪ D : Set E) =ᵐ[volume] Metric.ball c R :=
  union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 hD)

theorem perimeter_ball_union_null (c : E) (R : ℝ) {D : Set E} (hD : volume D = 0) :
    perimeter volume (Metric.ball c R ∪ D) = perimeter volume (Metric.ball c R) :=
  perimeter_union_null (Metric.ball c R) hD

theorem hasFinitePerimeter_ball_union_null (c : E) (R : ℝ) {D : Set E} (hD : volume D = 0) :
    HasFinitePerimeter volume (Metric.ball c R ∪ D) := by
  refine ⟨Metric.isOpen_ball.measurableSet.nullMeasurableSet.union
    (NullMeasurableSet.of_null (by simpa using hD)), ?_⟩
  change perimeter volume (Metric.ball c R ∪ D) < ⊤
  rw [perimeter_ball_union_null c R hD]; exact perimeter_ball_lt_top c R

theorem reducedBoundary_ball_union_null (c : E) (R : ℝ) {D : Set E} (hD : volume D = 0) :
    reducedBoundary (Metric.ball c R ∪ D) = reducedBoundary (Metric.ball c R) :=
  reducedBoundary_congr_ae (ball_union_null_ae_eq_ball c R hD)

theorem deGiorgiNormal_ball_union_null (c : E) (R : ℝ) {D : Set E} (hD : volume D = 0) (x : E) :
    deGiorgiNormal (Metric.ball c R ∪ D) x = deGiorgiNormal (Metric.ball c R) x :=
  deGiorgiNormal_congr_ae (ball_union_null_ae_eq_ball c R hD) x

@[simp] theorem essentialBoundary_ball_union_null (c : E) {R : ℝ} (hR : 0 < R) {D : Set E}
    (hD : volume D = 0) :
    essentialBoundary volume (Metric.ball c R ∪ D) = Metric.sphere c R := by
  rw [essentialBoundary_union_null (Metric.ball c R) hD, essentialBoundary_ball c hR]

/-- **Exact topological interior and frontier of `Metric.ball c R ∪ D`** (`R > 0`, `volume D = 0`,
`Dense D`). -/
theorem interior_ball_union_of_null (c : E) {R : ℝ} (hR : 0 < R) {D : Set E}
    (hD : volume D = 0) : interior (Metric.ball c R ∪ D) = Metric.ball c R := by
  refine Subset.antisymm ?_ (Metric.isOpen_ball.subset_interior_iff.2 Set.subset_union_left)
  calc interior (Metric.ball c R ∪ D)
      ⊆ essentialInterior volume (Metric.ball c R ∪ D) :=
        interior_subset_essentialInterior (Metric.ball c R ∪ D)
    _ = essentialInterior volume (Metric.ball c R) :=
        essentialInterior_union_null (Metric.ball c R) hD
    _ = Metric.ball c R := essentialInterior_ball c hR

theorem frontier_ball_union_of_null_of_dense (c : E) {R : ℝ} (hR : 0 < R)
    {D : Set E} (hD : volume D = 0) (hdense : Dense D) :
    frontier (Metric.ball c R ∪ D) = (Metric.ball c R)ᶜ := by
  have hcl : closure (Metric.ball c R ∪ D) = Set.univ :=
    Set.eq_univ_of_univ_subset
      (by rw [← hdense.closure_eq]; exact closure_mono Set.subset_union_right)
  rw [frontier, hcl, interior_ball_union_of_null c hR hD, ← Set.compl_eq_univ_sdiff]

theorem volume_frontier_ball_union_eq_top_of_null_of_dense [Nontrivial E] (c : E) {R : ℝ}
    (hR : 0 < R) {D : Set E} (hD : volume D = 0) (hdense : Dense D) :
    volume (frontier (Metric.ball c R ∪ D)) = ⊤ := by
  rw [frontier_ball_union_of_null_of_dense c hR hD hdense, volume_compl_ball_eq_top]

theorem reducedBoundary_ball_union_ssubset_frontier_of_null_of_dense [Nontrivial E] (c : E)
    {R : ℝ} (hR : 0 < R) {D : Set E} (hD : volume D = 0) (hdense : Dense D) :
    reducedBoundary (Metric.ball c R ∪ D) ⊂ frontier (Metric.ball c R ∪ D) :=
  (reducedBoundary_subset_essentialBoundary _).trans_ssubset
    (essentialBoundary_ball_union_ssubset_frontier_of_null_of_dense c hR hD hdense)

/-- Specialization to a **countable dense set `D ⊆ E`**. -/
theorem frontier_and_perimeter_ball_union_countable_dense [Nontrivial E] (c : E) {R : ℝ}
    (hR : 0 < R) {D : Set E} (hD_count : D.Countable) (hD_dense : Dense D) :
    perimeter volume (Metric.ball c R ∪ D) = perimeter volume (Metric.ball c R) ∧
      reducedBoundary (Metric.ball c R ∪ D) = reducedBoundary (Metric.ball c R) ∧
      essentialBoundary volume (Metric.ball c R ∪ D) = Metric.sphere c R ∧
      frontier (Metric.ball c R ∪ D) = (Metric.ball c R)ᶜ ∧
      volume (frontier (Metric.ball c R ∪ D)) = ⊤ := by
  have hD0 : volume D = 0 := hD_count.measure_zero volume
  exact ⟨perimeter_ball_union_null c R hD0, reducedBoundary_ball_union_null c R hD0,
    essentialBoundary_ball_union_null c hR hD0,
    frontier_ball_union_of_null_of_dense c hR hD0 hD_dense,
    volume_frontier_ball_union_eq_top_of_null_of_dense c hR hD0 hD_dense⟩

end InnerProductBlowUp

end TauCeti
