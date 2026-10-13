/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
public import TauCeti.MeasureTheory.Measure.OneDimIsoperimetry
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterSlicing
import all TauCeti.MeasureTheory.Measure.OneDimIsoperimetry

/-!
# Geometric, Convex, Rearrangement, and Slice-Rigidity Properties of Steiner Symmetrization

For a unit vector `e` in a finite-dimensional real inner product space `E` and orthogonal complement
`orthogonalHyperplane e := (ℝ ∙ e)ᗮ`, this file develops four structural properties of
`steinerSymmetrization e s` and its fibers `steinerFiber e s y` (aliased as `steinerSlice e s y`):

1. **Translation, dilation, and orthogonal transport laws**:
   `symmetricInterval` is translation-invariant (`symmetricInterval_vadd`) and commutes with
   nonzero scalar multiplication (`symmetricInterval_smul_of_ne_zero`). `steinerSymmetrization e`
   is invariant under translations parallel to `e` (`steinerSymmetrization_vadd_smul_self`),
   commutes with translations in `orthogonalHyperplane e`
   (`steinerSymmetrization_vadd_coe_orthogonalHyperplane`, `steinerSymmetrization_vadd`), commutes
   with nonzero scalar dilations (`steinerSymmetrization_smul_of_ne_zero`), and is equivariant
   under linear isometry equivalences (`steinerSymmetrization_image_linearIsometryEquiv`).
2. **Preservation of convexity under Steiner symmetrization**:
   Every fiber of a convex set is convex (`Convex.steinerFiber`) and order-connected
   (`Convex.ordConnected_steinerFiber`), its 1D length is concave over nonempty finite-measure
   fibers (`Convex.add_mul_toReal_volume_steinerFiber_le`), and `steinerSymmetrization e s` is
   convex (`Convex.steinerSymmetrization_of_forall_volume_lt_top`, `Convex.steinerSymmetrization`).
3. **Two-set rearrangement, set-difference contraction, and `L¹` indicator contraction**:
   Centered open intervals satisfy `volume_inter_le_volume_Ioo_neg_toReal_div_two_inter`,
   `symmetricInterval` contracts set-difference volume (`volume_diff_symmetricInterval_le`), and
   `steinerSymmetrization e` contracts set differences (`volume_diff_steinerSymmetrization_le₀`)
   and `L¹` indicator distances (`lintegral_edist_indicator_steinerSymmetrization_le`).
4. **Directional slice perimeter and `OrdConnected` section rigidity along unit directions `e`**:
   Slicing test functions via `steinerFiberTestFunction` gives
   `directionalVariation_le_lintegral_steinerFiber` and
   `directionalPerimeter_le_lintegral_steinerFiber`. Active fibers of `steinerSymmetrization e s`
   have perimeter `2` (`lintegral_perimeter_steinerFiber_steinerSymmetrization`), yielding
   `directionalPerimeter_steinerSymmetrization_le`,
   `two_mul_volume_steinerFiber_pos_le_lintegral_perimeter`, and the equality rigidity theorems
   `volume_steinerFiber_perimeter_ge_four_eq_zero`, `ae_exists_ordConnected_ae_eq_steinerFiber`,
   and `ae_exists_Ioo_ae_eq_steinerFiber`.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Set Submodule TopologicalSpace
open TestFunction Pointwise
open scoped ENNReal NNReal symmDiff InnerProductSpace Distributions Topology

namespace TauCeti.MeasureTheory

/-! ### Section 1: Translation, dilation, and orthogonal transport laws -/

section TranslationDilationTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Alias for `steinerFiber`: the 1D slice `{t : ℝ | (y : E) + t • e ∈ s}` over `y`. -/
abbrev steinerSlice (e : E) (s : Set E) (y : orthogonalHyperplane e) : Set ℝ := steinerFiber e s y
/-- `symmetricInterval` is invariant under translation `c +ᵥ t` on `ℝ`. -/
@[simp] theorem symmetricInterval_vadd (c : ℝ) (t : Set ℝ) :
    symmetricInterval (c +ᵥ t) = symmetricInterval t :=
  symmetricInterval_congr_volume (measure_vadd volume c t)
/-- `symmetricInterval` is invariant under left-addition preimages `(c + ·) ⁻¹' t`. -/
@[simp] theorem symmetricInterval_preimage_add_left (c : ℝ) (t : Set ℝ) :
    symmetricInterval ((c + ·) ⁻¹' t) = symmetricInterval t :=
  symmetricInterval_congr_volume (measure_preimage_add volume c t)
/-- `symmetricInterval` is invariant under right-addition preimages `(· + c) ⁻¹' t`. -/
@[simp] theorem symmetricInterval_preimage_add_right (c : ℝ) (t : Set ℝ) :
    symmetricInterval ((· + c) ⁻¹' t) = symmetricInterval t :=
  symmetricInterval_congr_volume (measure_preimage_add_right volume c t)
/-- One-dimensional Lebesgue measure under scalar multiplication on `ℝ`. -/
theorem volume_smul_real (r : ℝ) (t : Set ℝ) :
    volume (r • t) = ENNReal.ofReal |r| * volume t := by
  simp [Measure.addHaar_smul, Module.finrank_self]
/-- `symmetricInterval` commutes with nonzero scalar multiplication on `ℝ`. -/
theorem symmetricInterval_smul_of_ne_zero {r : ℝ} (hr : r ≠ 0) (t : Set ℝ) :
    symmetricInterval (r • t) = r • symmetricInterval t := by
  have hr_pos : 0 < |r| := abs_pos.mpr hr
  have hof_ne_zero : ENNReal.ofReal |r| ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr_pos
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hr, smul_eq_mul, mem_symmetricInterval_iff,
    mem_symmetricInterval_iff, volume_smul_real]
  have hmul : ENNReal.ofReal (2 * |x|) =
      ENNReal.ofReal |r| * ENNReal.ofReal (2 * |r⁻¹ * x|) := by
    rw [← ENNReal.ofReal_mul hr_pos.le, abs_mul, abs_inv]; congr 1
    calc
      2 * |x| = |r| * (|r|⁻¹ * (2 * |x|)) := by rw [mul_inv_cancel_left₀ hr_pos.ne']
      _ = |r| * (2 * (|r|⁻¹ * |x|)) := by ring
  rw [hmul, ENNReal.mul_le_mul_iff_right hof_ne_zero ENNReal.ofReal_ne_top]
  exact and_congr_left' (mul_ne_zero_iff.trans (and_iff_right hof_ne_zero))
/-- `symmetricInterval` commutes with positive scalar multiplication on `ℝ`. -/
theorem symmetricInterval_smul_of_pos {r : ℝ} (hr : 0 < r) (t : Set ℝ) :
    symmetricInterval (r • t) = r • symmetricInterval t :=
  symmetricInterval_smul_of_ne_zero hr.ne' t
/-- Translating `s` by `c • e` shifts every fiber `steinerFiber e s y` by `c`. -/
@[simp] theorem steinerFiber_vadd_smul_self (e : E) (c : ℝ) (s : Set E)
    (y : orthogonalHyperplane e) : steinerFiber e ((c • e) +ᵥ s) y = c +ᵥ steinerFiber e s y := by
  ext t
  rw [mem_steinerFiber_iff, mem_vadd_set_iff_neg_vadd_mem, mem_vadd_set_iff_neg_vadd_mem,
    mem_steinerFiber_iff]
  simp only [vadd_eq_add]
  have heq : -(c • e) + ((y : E) + t • e) = (y : E) + (-c + t) • e := by
    rw [add_smul, neg_smul]; abel
  rw [heq]
/-- Translating `s` along `ℝ ∙ e` preserves the one-dimensional volume of every fiber. -/
theorem volume_steinerFiber_vadd_smul_self (e : E) (c : ℝ) (s : Set E)
    (y : orthogonalHyperplane e) :
    volume (steinerFiber e ((c • e) +ᵥ s) y) = volume (steinerFiber e s y) := by
  rw [steinerFiber_vadd_smul_self, measure_vadd]
/-- Steiner symmetrization in direction `e` is invariant under translations along `ℝ ∙ e`. -/
@[simp] theorem steinerSymmetrization_vadd_smul_self (e : E) (c : ℝ) (s : Set E) :
    steinerSymmetrization e ((c • e) +ᵥ s) = steinerSymmetrization e s := by
  ext x; simp [mem_steinerSymmetrization_iff]
/-- Translating `s` by `y₀ : orthogonalHyperplane e` shifts the fiber basepoint by `y₀`. -/
@[simp] theorem steinerFiber_vadd_coe_orthogonalHyperplane (e : E) (y₀ : orthogonalHyperplane e)
    (s : Set E) (y : orthogonalHyperplane e) :
    steinerFiber e ((y₀ : E) +ᵥ s) y = steinerFiber e s (y - y₀) := by
  ext t; rw [mem_steinerFiber_iff, mem_vadd_set_iff_neg_vadd_mem, mem_steinerFiber_iff]
  have heq : -(y₀ : E) +ᵥ ((y : E) + t • e) = ((y - y₀ : orthogonalHyperplane e) : E) + t • e := by
    rw [vadd_eq_add, Submodule.coe_sub]; abel
  rw [heq]
/-- `steinerSymmetrization e` commutes with translations in `orthogonalHyperplane e`. -/
@[simp] theorem steinerSymmetrization_vadd_coe_orthogonalHyperplane (e : E)
    (y₀ : orthogonalHyperplane e) (s : Set E) :
    steinerSymmetrization e ((y₀ : E) +ᵥ s) = (y₀ : E) +ᵥ steinerSymmetrization e s := by
  ext x
  rw [mem_steinerSymmetrization_iff, mem_vadd_set_iff_neg_vadd_mem, mem_steinerSymmetrization_iff,
    steinerFiber_vadd_coe_orthogonalHyperplane]
  have hinner : ⟪-(y₀ : E) +ᵥ x, e⟫_ℝ = ⟪x, e⟫_ℝ := by
    rw [vadd_eq_add, inner_add_left, inner_neg_left, coe_inner_orthogonalHyperplane_eq_zero,
      neg_zero, zero_add]
  have hproj : (orthogonalHyperplane e).orthogonalProjectionOnto (-(y₀ : E) +ᵥ x) =
      (orthogonalHyperplane e).orthogonalProjectionOnto x - y₀ := by
    rw [vadd_eq_add, map_add, map_neg, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      sub_eq_neg_add]
  rw [hinner, hproj]
/-- `steinerSymmetrization e` commutes with translation by vectors orthogonal to `e`. -/
theorem steinerSymmetrization_vadd_of_inner_eq_zero {e v : E} (hv : ⟪v, e⟫_ℝ = 0) (s : Set E) :
    steinerSymmetrization e (v +ᵥ s) = v +ᵥ steinerSymmetrization e s :=
  steinerSymmetrization_vadd_coe_orthogonalHyperplane e ⟨v, mem_orthogonalHyperplane_iff.mpr hv⟩ s
/-- General translation law for Steiner symmetrization: translating `s` by `v : E` translates
`steinerSymmetrization e s` by the orthogonal projection of `v` onto `orthogonalHyperplane e`. -/
theorem steinerSymmetrization_vadd {e : E} (he : ‖e‖ = 1) (v : E) (s : Set E) :
    steinerSymmetrization e (v +ᵥ s) =
      ((orthogonalHyperplane e).orthogonalProjectionOnto v : E) +ᵥ steinerSymmetrization e s := by
  have hv : v +ᵥ s =
      ((orthogonalHyperplane e).orthogonalProjectionOnto v : E) +ᵥ ((⟪v, e⟫_ℝ • e) +ᵥ s) := by
    rw [vadd_vadd, orthogonalProjection_orthogonalHyperplane_add_inner_smul he v]
  rw [hv, steinerSymmetrization_vadd_coe_orthogonalHyperplane,
    steinerSymmetrization_vadd_smul_self]
/-- Nonzero scalar multiplication on `E` rescales fibers and basepoints simultaneously. -/
theorem steinerFiber_smul_of_ne_zero {e : E} {r : ℝ} (hr : r ≠ 0) (s : Set E)
    (y : orthogonalHyperplane e) :
    steinerFiber e (r • s) y = r • steinerFiber e s (r⁻¹ • y) := by
  ext t
  rw [mem_steinerFiber_iff, mem_smul_set_iff_inv_smul_mem₀ hr, mem_smul_set_iff_inv_smul_mem₀ hr,
    mem_steinerFiber_iff]
  have heq : r⁻¹ • ((y : E) + t • e) =
      ((r⁻¹ • y : orthogonalHyperplane e) : E) + (r⁻¹ • t) • e := by
    rw [smul_add, SetLike.val_smul, smul_smul, smul_eq_mul]
  rw [heq]
/-- Steiner symmetrization commutes with nonzero scalar dilations on `E`. -/
theorem steinerSymmetrization_smul_of_ne_zero {e : E} {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    steinerSymmetrization e (r • s) = r • steinerSymmetrization e s := by
  ext x
  rw [mem_steinerSymmetrization_iff, mem_smul_set_iff_inv_smul_mem₀ hr,
    mem_steinerSymmetrization_iff, steinerFiber_smul_of_ne_zero hr,
    symmetricInterval_smul_of_ne_zero hr, mem_smul_set_iff_inv_smul_mem₀ hr,
    map_smul, real_inner_smul_left, smul_eq_mul]
/-- Steiner symmetrization commutes with positive scalar dilations on `E`. -/
theorem steinerSymmetrization_smul_of_pos {e : E} {r : ℝ} (hr : 0 < r) (s : Set E) :
    steinerSymmetrization e (r • s) = r • steinerSymmetrization e s :=
  steinerSymmetrization_smul_of_ne_zero hr.ne' s
/-- Orthogonal/isometric transport law for Steiner symmetrization under `U : E ≃ₗᵢ[ℝ] E`. -/
theorem steinerSymmetrization_image_linearIsometryEquiv {e : E} (he : ‖e‖ = 1)
    (U : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    steinerSymmetrization (U e) (U '' s) = U '' steinerSymmetrization e s := by
  have hUe : ‖U e‖ = 1 := by rw [U.norm_map, he]
  have hinner : ∀ x : E, ⟪x, U e⟫_ℝ = ⟪U.symm x, e⟫_ℝ := fun x ↦ by
    simpa using U.inner_map_map (U.symm x) e
  have hproj : ∀ x : E,
      ((orthogonalHyperplane (U e)).orthogonalProjectionOnto x : E) =
        U ((orthogonalHyperplane e).orthogonalProjectionOnto (U.symm x)) := fun x ↦ by
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.coe_orthogonalProjectionOnto_apply,
      starProjection_orthogonalHyperplane_apply hUe, starProjection_orthogonalHyperplane_apply he,
      map_sub, U.apply_symm_apply, map_smul, hinner]
  ext x
  have hfiber :
      steinerFiber (U e) (U '' s) ((orthogonalHyperplane (U e)).orthogonalProjectionOnto x) =
        steinerFiber e s ((orthogonalHyperplane e).orthogonalProjectionOnto (U.symm x)) := by
    ext t; rw [mem_steinerFiber_iff, mem_steinerFiber_iff, hproj x]
    have hpt :
        (U ((orthogonalHyperplane e).orthogonalProjectionOnto (U.symm x)) : E) + t • U e =
          U (((orthogonalHyperplane e).orthogonalProjectionOnto (U.symm x) : E) + t • e) := by
      rw [map_add, map_smul]
    rw [hpt, U.injective.mem_set_image]
  have hx : x ∈ U '' steinerSymmetrization e s ↔ U.symm x ∈ steinerSymmetrization e s :=
    ⟨fun ⟨y, hy, hyx⟩ ↦ by simpa [← hyx] using hy,
      fun h ↦ ⟨U.symm x, h, U.apply_symm_apply x⟩⟩
  rw [hx, mem_steinerSymmetrization_iff, mem_steinerSymmetrization_iff, hinner, hfiber]
/-- Preimage form of orthogonal/isometric transport for Steiner symmetrization. -/
theorem steinerSymmetrization_preimage_linearIsometryEquiv {e : E} (he : ‖e‖ = 1)
    (U : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    steinerSymmetrization e (U ⁻¹' s) = U ⁻¹' steinerSymmetrization (U e) s := by
  have hpre : ∀ t : Set E, U ⁻¹' t = U.symm '' t := fun t ↦ by
    ext x
    exact ⟨fun h ↦ ⟨U x, h, U.symm_apply_apply x⟩, fun ⟨y, hy, hyx⟩ ↦ by simpa [← hyx] using hy⟩
  have hUe : ‖U e‖ = 1 := by rw [U.norm_map, he]
  rw [hpre s, hpre (steinerSymmetrization (U e) s), ← U.symm_apply_apply e,
    steinerSymmetrization_image_linearIsometryEquiv hUe U.symm s, U.symm_apply_apply]
/-- If `U : E ≃ₗᵢ[ℝ] E` fixes `e`, then `steinerSymmetrization e` commutes with `U '' ·`. -/
theorem steinerSymmetrization_image_of_apply_eq_self {e : E} (he : ‖e‖ = 1)
    {U : E ≃ₗᵢ[ℝ] E} (hU : U e = e) (s : Set E) :
    steinerSymmetrization e (U '' s) = U '' steinerSymmetrization e s := by
  simpa [hU] using steinerSymmetrization_image_linearIsometryEquiv he U s

end TranslationDilationTransport

/-! ### Section 2: Preservation of convexity under Steiner symmetrization -/

section Convexity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every finite-measure `OrdConnected` subset `I : Set ℝ` has volume
`ENNReal.ofReal (sSup I - sInf I)`. -/
theorem _root_.Set.OrdConnected.volume_eq_ofReal_sSup_sub_sInf {I : Set ℝ} (hI : I.OrdConnected)
    (htop : volume I < ⊤) : volume I = ENNReal.ofReal (sSup I - sInf I) := by
  rw [measure_congr (hI.ae_eq_Ioo_sInf_sSup htop), Real.volume_Ioo]
/-- A finite-measure `OrdConnected` set `I : Set ℝ` has `(volume I).toReal = sSup I - sInf I`. -/
theorem _root_.Set.OrdConnected.toReal_volume_eq_sSup_sub_sInf {I : Set ℝ} (hI : I.OrdConnected)
    (htop : volume I < ⊤) : (volume I).toReal = sSup I - sInf I := by
  rcases I.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp [Real.sSup_empty, Real.sInf_empty]
  · have hle : sInf I ≤ sSup I :=
      (csInf_le (hI.bddBelow_of_volume_lt_top htop) hx).trans
        (le_csSup (hI.bddAbove_of_volume_lt_top htop) hx)
    rw [hI.volume_eq_ofReal_sSup_sub_sInf htop, ENNReal.toReal_ofReal (sub_nonneg.mpr hle)]

private lemma mul_csSup_le_of_forall_le {A : Set ℝ} (hA : A.Nonempty) {a M : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ A, a * x ≤ M) : a * sSup A ≤ M := by
  rcases ha.eq_or_lt with rfl | ha_pos
  · obtain ⟨x, hx⟩ := hA; linarith [h x hx]
  · rw [← le_div_iff₀' ha_pos]
    exact csSup_le hA fun x hx ↦ (le_div_iff₀' ha_pos).mpr (h x hx)
private lemma le_mul_csInf_of_forall_le {A : Set ℝ} (hA : A.Nonempty) {a m : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ A, m ≤ a * x) : m ≤ a * sInf A := by
  rcases ha.eq_or_lt with rfl | ha_pos
  · obtain ⟨x, hx⟩ := hA; linarith [h x hx]
  · rw [← div_le_iff₀' ha_pos]
    exact le_csInf hA fun x hx ↦ (div_le_iff₀' ha_pos).mpr (h x hx)

/-- Convexity of `s : Set E` implies that convex combinations of fiber elements belong to the
fiber over the convex combination of basepoints. -/
theorem add_mul_mem_steinerFiber_of_convex {e : E} {s : Set E} (hs : Convex ℝ s)
    {y₁ y₂ : orthogonalHyperplane e} {t₁ t₂ a b : ℝ}
    (ht₁ : t₁ ∈ steinerFiber e s y₁) (ht₂ : t₂ ∈ steinerFiber e s y₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * t₁ + b * t₂ ∈ steinerFiber e s (a • y₁ + b • y₂) := by
  rw [mem_steinerFiber_iff] at ht₁ ht₂ ⊢
  have heq : ((a • y₁ + b • y₂ : orthogonalHyperplane e) : E) + (a * t₁ + b * t₂) • e =
      a • ((y₁ : E) + t₁ • e) + b • ((y₂ : E) + t₂ • e) := by
    simp only [Submodule.coe_add, SetLike.val_smul, add_smul, mul_smul, smul_add]; abel
  rw [heq]; exact hs ht₁ ht₂ ha hb hab
/-- Every fiber `steinerFiber e s y` of a convex set `s : Set E` is convex in `ℝ`. -/
theorem _root_.Convex.steinerFiber {s : Set E} (hs : Convex ℝ s) (e : E)
    (y : orthogonalHyperplane e) : Convex ℝ (steinerFiber e s y) := by
  intro t₁ ht₁ t₂ ht₂ a b ha hb hab
  have hy : a • y + b • y = y := by rw [← add_smul, hab, one_smul]
  simpa [hy, smul_eq_mul] using add_mul_mem_steinerFiber_of_convex hs ht₁ ht₂ ha hb hab
/-- Every fiber `steinerFiber e s y` of a convex set `s : Set E` is order-connected in `ℝ`. -/
theorem _root_.Convex.ordConnected_steinerFiber {s : Set E} (hs : Convex ℝ s) (e : E)
    (y : orthogonalHyperplane e) : (steinerFiber e s y).OrdConnected :=
  (hs.steinerFiber e y).ordConnected
/-- Concavity of one-dimensional fiber lengths for a convex set `s : Set E` over nonempty fibers. -/
theorem _root_.Convex.add_mul_toReal_volume_steinerFiber_le {e : E} {s : Set E} (hs : Convex ℝ s)
    {y₁ y₂ : orthogonalHyperplane e} (hy₁ : (steinerFiber e s y₁).Nonempty)
    (hy₂ : (steinerFiber e s y₂).Nonempty) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (htop₁ : volume (steinerFiber e s y₁) < ⊤) (htop₂ : volume (steinerFiber e s y₂) < ⊤)
    (htop₃ : volume (steinerFiber e s (a • y₁ + b • y₂)) < ⊤) :
    a * (volume (steinerFiber e s y₁)).toReal + b * (volume (steinerFiber e s y₂)).toReal ≤
      (volume (steinerFiber e s (a • y₁ + b • y₂))).toReal := by
  set I₁ := steinerFiber e s y₁; set I₂ := steinerFiber e s y₂
  set I₃ := steinerFiber e s (a • y₁ + b • y₂)
  have hI₁ : I₁.OrdConnected := hs.ordConnected_steinerFiber e y₁
  have hI₂ : I₂.OrdConnected := hs.ordConnected_steinerFiber e y₂
  have hI₃ : I₃.OrdConnected := hs.ordConnected_steinerFiber e (a • y₁ + b • y₂)
  have hbddBelow₃ : BddBelow I₃ := hI₃.bddBelow_of_volume_lt_top htop₃
  have hbddAbove₃ : BddAbove I₃ := hI₃.bddAbove_of_volume_lt_top htop₃
  have hsup : a * sSup I₁ + b * sSup I₂ ≤ sSup I₃ := by
    have h1 : ∀ t₂ ∈ I₂, a * sSup I₁ ≤ sSup I₃ - b * t₂ := fun t₂ ht₂ ↦
      mul_csSup_le_of_forall_le hy₁ ha fun t₁ ht₁ ↦ by
        linarith [le_csSup hbddAbove₃ (add_mul_mem_steinerFiber_of_convex hs ht₁ ht₂ ha hb hab)]
    have h2 : b * sSup I₂ ≤ sSup I₃ - a * sSup I₁ :=
      mul_csSup_le_of_forall_le hy₂ hb fun t₂ ht₂ ↦ by linarith [h1 t₂ ht₂]
    linarith
  have hinf : sInf I₃ ≤ a * sInf I₁ + b * sInf I₂ := by
    have h1 : ∀ t₂ ∈ I₂, sInf I₃ - b * t₂ ≤ a * sInf I₁ := fun t₂ ht₂ ↦
      le_mul_csInf_of_forall_le hy₁ ha fun t₁ ht₁ ↦ by
        linarith [csInf_le hbddBelow₃ (add_mul_mem_steinerFiber_of_convex hs ht₁ ht₂ ha hb hab)]
    have h2 : sInf I₃ - a * sInf I₁ ≤ b * sInf I₂ :=
      le_mul_csInf_of_forall_le hy₂ hb fun t₂ ht₂ ↦ by linarith [h1 t₂ ht₂]
    linarith
  rw [hI₁.toReal_volume_eq_sSup_sub_sInf htop₁, hI₂.toReal_volume_eq_sSup_sub_sInf htop₂,
    hI₃.toReal_volume_eq_sSup_sub_sInf htop₃]
  linarith
/-- If `s : Set E` is convex and all of its fibers in direction `e` have finite 1D volume, then
`steinerSymmetrization e s` is convex. -/
theorem _root_.Convex.steinerSymmetrization_of_forall_volume_lt_top {e : E} {s : Set E}
    (hs : Convex ℝ s) (hfin : ∀ y : orthogonalHyperplane e, volume (steinerFiber e s y) < ⊤) :
    Convex ℝ (steinerSymmetrization e s) := by
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  rw [mem_steinerSymmetrization_iff_volume] at hx₁ hx₂ ⊢
  set y₁ := (orthogonalHyperplane e).orthogonalProjectionOnto x₁
  set y₂ := (orthogonalHyperplane e).orthogonalProjectionOnto x₂
  have hproj : (orthogonalHyperplane e).orthogonalProjectionOnto (a • x₁ + b • x₂) =
      a • y₁ + b • y₂ := by rw [map_add, map_smul, map_smul]
  have hinner : ⟪a • x₁ + b • x₂, e⟫_ℝ = a * ⟪x₁, e⟫_ℝ + b * ⟪x₂, e⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [hproj, hinner]
  have hy₁_ne : (steinerFiber e s y₁).Nonempty := nonempty_of_measure_ne_zero hx₁.1
  have hy₂_ne : (steinerFiber e s y₂).Nonempty := nonempty_of_measure_ne_zero hx₂.1
  have hconc := hs.add_mul_toReal_volume_steinerFiber_le hy₁_ne hy₂_ne ha hb hab
    (hfin y₁) (hfin y₂) (hfin (a • y₁ + b • y₂))
  have hv₁_pos : 0 < (volume (steinerFiber e s y₁)).toReal :=
    ENNReal.toReal_pos hx₁.1 (hfin y₁).ne
  have hv₂_pos : 0 < (volume (steinerFiber e s y₂)).toReal :=
    ENNReal.toReal_pos hx₂.1 (hfin y₂).ne
  have hv₃_pos : 0 < (volume (steinerFiber e s (a • y₁ + b • y₂))).toReal := by
    rcases ha.eq_or_lt with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      nlinarith
    · have : 0 ≤ b * (volume (steinerFiber e s y₂)).toReal := mul_nonneg hb hv₂_pos.le
      nlinarith
  have hv₃_ne : volume (steinerFiber e s (a • y₁ + b • y₂)) ≠ 0 := fun h0 ↦ by simp [h0] at hv₃_pos
  refine ⟨hv₃_ne, ?_⟩
  have ht₁ : 2 * |⟪x₁, e⟫_ℝ| ≤ (volume (steinerFiber e s y₁)).toReal := by
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hfin y₁).ne).mpr hx₁.2
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have ht₂ : 2 * |⟪x₂, e⟫_ℝ| ≤ (volume (steinerFiber e s y₂)).toReal := by
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hfin y₂).ne).mpr hx₂.2
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  rw [← ENNReal.ofReal_toReal (hfin (a • y₁ + b • y₂)).ne]
  refine ENNReal.ofReal_le_ofReal ?_
  have habs : |a * ⟪x₁, e⟫_ℝ + b * ⟪x₂, e⟫_ℝ| ≤ a * |⟪x₁, e⟫_ℝ| + b * |⟪x₂, e⟫_ℝ| := by
    calc
      |a * ⟪x₁, e⟫_ℝ + b * ⟪x₂, e⟫_ℝ| ≤ |a * ⟪x₁, e⟫_ℝ| + |b * ⟪x₂, e⟫_ℝ| := abs_add_le _ _
      _ = a * |⟪x₁, e⟫_ℝ| + b * |⟪x₂, e⟫_ℝ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  nlinarith
/-- **Steiner symmetrization preserves convexity** of bounded convex sets in any unit direction. -/
theorem _root_.Convex.steinerSymmetrization {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : Convex ℝ s) (hbdd : Bornology.IsBounded s) : Convex ℝ (steinerSymmetrization e s) :=
  hs.steinerSymmetrization_of_forall_volume_lt_top fun y ↦
    (isBounded_steinerFiber he hbdd y).measure_lt_top

end Convexity

/-! ### Section 3: Two-set intersection, set-difference, and `L¹` indicator contraction -/

section ContractionAndIntersection

/-- Intersection of centered open intervals `Ioo (-a / 2) (a / 2)` and `Ioo (-b / 2) (b / 2)`. -/
theorem Ioo_neg_div_two_inter (a b : ℝ) :
    Ioo (-a / 2) (a / 2) ∩ Ioo (-b / 2) (b / 2) = Ioo (-min a b / 2) (min a b / 2) := by
  ext x; simp only [mem_inter_iff, mem_Ioo, neg_div, ← abs_lt]
  rw [← min_div_div_right (zero_le_two : (0 : ℝ) ≤ 2), lt_min_iff]
/-- Volume of the intersection of centered open intervals for two finite-measure sets in `ℝ`. -/
theorem volume_Ioo_neg_toReal_div_two_inter {A B : Set ℝ} (hA : volume A < ⊤) (hB : volume B < ⊤) :
    volume (Ioo (-(volume A).toReal / 2) ((volume A).toReal / 2) ∩
        Ioo (-(volume B).toReal / 2) ((volume B).toReal / 2)) = min (volume A) (volume B) := by
  rw [Ioo_neg_div_two_inter, Real.volume_Ioo]
  have hsub : min (volume A).toReal (volume B).toReal / 2 -
      -min (volume A).toReal (volume B).toReal / 2 =
      min (volume A).toReal (volume B).toReal := by ring
  rw [hsub]
  rcases le_total (volume A) (volume B) with h | h
  · have htr : (volume A).toReal ≤ (volume B).toReal :=
      (ENNReal.toReal_le_toReal hA.ne hB.ne).mpr h
    rw [min_eq_left htr, min_eq_left h, ENNReal.ofReal_toReal hA.ne]
  · have htr : (volume B).toReal ≤ (volume A).toReal :=
      (ENNReal.toReal_le_toReal hB.ne hA.ne).mpr h
    rw [min_eq_right htr, min_eq_right h, ENNReal.ofReal_toReal hB.ne]
/-- One-dimensional rearrangement inequality for centered open intervals. -/
theorem volume_inter_le_volume_Ioo_neg_toReal_div_two_inter {A B : Set ℝ}
    (hA : volume A < ⊤) (hB : volume B < ⊤) :
    volume (A ∩ B) ≤ volume (Ioo (-(volume A).toReal / 2) ((volume A).toReal / 2) ∩
      Ioo (-(volume B).toReal / 2) ((volume B).toReal / 2)) := by
  rw [volume_Ioo_neg_toReal_div_two_inter hA hB]
  exact le_min (measure_mono inter_subset_left) (measure_mono inter_subset_right)
/-- For any finite-measure subset `A : Set ℝ`, `symmetricInterval A` is a.e. equal to
`Ioo (-(volume A).toReal / 2) ((volume A).toReal / 2)`. -/
theorem symmetricInterval_ae_eq_Ioo {A : Set ℝ} (hA : volume A < ⊤) :
    symmetricInterval A =ᵐ[volume] Ioo (-(volume A).toReal / 2) ((volume A).toReal / 2) := by
  by_cases h0 : volume A = 0
  · simp [symmetricInterval_of_volume_eq_zero h0, h0]
  · rw [symmetricInterval_of_volume_ne_zero_of_ne_top h0 hA.ne]; exact Ioo_ae_eq_Icc.symm
/-- One-dimensional set-difference contraction for `symmetricInterval`. -/
theorem volume_diff_symmetricInterval_le (A B : Set ℝ) :
    volume (symmetricInterval A \ symmetricInterval B) ≤ volume (A \ B) := by
  rcases le_or_gt (volume A) (volume B) with h | h
  · rw [sdiff_eq_empty.mpr (symmetricInterval_mono_volume h), measure_empty]; exact zero_le
  · have hB_top : volume B < ⊤ := lt_of_lt_of_le h le_top
    have hsub : symmetricInterval B ⊆ symmetricInterval A := symmetricInterval_mono_volume h.le
    rw [measure_sdiff hsub (measurableSet_symmetricInterval B).nullMeasurableSet
      (by rw [volume_symmetricInterval]; exact hB_top.ne),
      volume_symmetricInterval, volume_symmetricInterval]
    refine tsub_le_iff_right.mpr ?_
    calc
      volume A ≤ volume (A \ B ∪ B) := measure_mono (subset_sdiff_union A B)
      _ ≤ volume (A \ B) + volume B := measure_union_le (A \ B) B

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Two-set intersection inequality for Steiner symmetrization of null-measurable sets. -/
theorem volume_inter_le_steinerSymmetrization {e : E} (he : ‖e‖ = 1) {s t : Set E}
    (hs : NullMeasurableSet s volume) (ht : NullMeasurableSet t volume) :
    volume (s ∩ t) ≤ volume (steinerSymmetrization e s ∩ steinerSymmetrization e t) :=
  volume_inter_le_volume_steinerSymmetrization_inter₀ he hs ht
/-- Set-difference contraction under Steiner symmetrization for measurable sets. -/
theorem volume_diff_steinerSymmetrization_le {e : E} (he : ‖e‖ = 1) {s t : Set E}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    volume (steinerSymmetrization e s \ steinerSymmetrization e t) ≤ volume (s \ t) := by
  rw [volume_eq_lintegral_steinerFiber he
      ((measurableSet_steinerSymmetrization hs).diff (measurableSet_steinerSymmetrization ht)),
    volume_eq_lintegral_steinerFiber he (hs.diff ht)]
  refine lintegral_mono fun y ↦ ?_
  simp only [steinerFiber_sdiff, steinerFiber_steinerSymmetrization he]
  exact volume_diff_symmetricInterval_le _ _
/-- Set-difference contraction under Steiner symmetrization for null-measurable sets. -/
theorem volume_diff_steinerSymmetrization_le₀ {e : E} (he : ‖e‖ = 1) {s t : Set E}
    (hs : NullMeasurableSet s volume) (ht : NullMeasurableSet t volume) :
    volume (steinerSymmetrization e s \ steinerSymmetrization e t) ≤ volume (s \ t) := by
  rcases hs with ⟨s', hs'm, hss'⟩; rcases ht with ⟨t', ht'm, htt'⟩
  rw [measure_congr (hss'.diff htt'),
    measure_congr
      ((steinerSymmetrization_ae_eq he hss').diff (steinerSymmetrization_ae_eq he htt'))]
  exact volume_diff_steinerSymmetrization_le he hs'm ht'm
/-- Pointwise extended distance between indicator functions of `A` and `B` equals the indicator
of their symmetric difference `A ∆ B`. -/
theorem edist_indicator_one_apply {α : Type*} (A B : Set α) (x : α) :
    edist (A.indicator (1 : α → ℝ) x) (B.indicator (1 : α → ℝ) x) =
      (A ∆ B).indicator (1 : α → ℝ≥0∞) x := by
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB, Set.mem_symmDiff]
/-- The `L¹` distance `∫⁻ x, edist (A.indicator 1 x) (B.indicator 1 x) ∂μ` between indicator
functions of null-measurable sets equals the measure of their symmetric difference `μ (A ∆ B)`. -/
theorem lintegral_edist_indicator_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : Set α} (hA : NullMeasurableSet A μ) (hB : NullMeasurableSet B μ) :
    (∫⁻ x, edist (A.indicator (1 : α → ℝ) x) (B.indicator (1 : α → ℝ) x) ∂μ) = μ (A ∆ B) := by
  simp_rw [edist_indicator_one_apply]
  rcases hA.symmDiff hB with ⟨C, hCm, hC⟩
  have hae : (A ∆ B).indicator (1 : α → ℝ≥0∞) =ᵐ[μ] C.indicator (1 : α → ℝ≥0∞) :=
    indicator_ae_eq_of_ae_eq_set hC
  rw [lintegral_congr_ae hae, lintegral_indicator_one hCm, measure_congr hC]
/-- **`L¹` indicator contraction for Steiner symmetrization**: Steiner symmetrization does not
increase the `L¹` distance between indicator functions of null-measurable sets. -/
theorem lintegral_edist_indicator_steinerSymmetrization_le {e : E} (he : ‖e‖ = 1) {s t : Set E}
    (hs : NullMeasurableSet s volume) (ht : NullMeasurableSet t volume) :
    (∫⁻ x : E, edist ((steinerSymmetrization e s).indicator (1 : E → ℝ) x)
        ((steinerSymmetrization e t).indicator (1 : E → ℝ) x) ∂volume) ≤
      ∫⁻ x : E, edist (s.indicator (1 : E → ℝ) x) (t.indicator (1 : E → ℝ) x) ∂volume := by
  rw [lintegral_edist_indicator_one volume
      (nullMeasurableSet_steinerSymmetrization he hs)
      (nullMeasurableSet_steinerSymmetrization he ht),
    lintegral_edist_indicator_one volume hs ht]
  exact volume_symmDiff_steinerSymmetrization_le₀ he hs ht

end ContractionAndIntersection

/-! ### Section 4: Directional slice perimeter and `OrdConnected` section rigidity -/

section DirectionalSlicePerimeterAndRigidity

private lemma locallyIntegrable_indicator_one_of_nullMeasurableSet {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] {ν : Measure X} [IsLocallyFiniteMeasure ν]
    {s : Set X} (hs : NullMeasurableSet s ν) :
    LocallyIntegrable (s.indicator fun _ ↦ (1 : ℝ)) ν := by
  refine ((locallyIntegrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable ν s)).congr
    (hs.toMeasurable_ae_eq.mono fun x hx ↦ ?_)
  have hmem : x ∈ toMeasurable ν s ↔ x ∈ s := by simpa [eq_iff_iff] using hx
  by_cases hxs : x ∈ s <;> [simp [hxs, hmem.2 hxs]; simp [hxs, mt hmem.1 hxs]]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One-dimensional test function slice `t ↦ ψ ((y : E) + t • e)` along a Steiner fiber in a unit
direction `e : E`. -/
def steinerFiberTestFunction (ψ : 𝓓((⊤ : Opens E), ℝ)) {e : E} (he : ‖e‖ = 1)
    (y : orthogonalHyperplane e) : 𝓓((⊤ : Opens ℝ), ℝ) where
  toFun t := ψ ((y : E) + t • e)
  contDiff' := ψ.contDiff.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact
    (ψ.hasCompactSupport.isCompact.image (continuous_id.inner continuous_const)) fun t ht ↦
      ⟨(y : E) + t • e, subset_tsupport _ ht, inner_coe_add_smul_self he y t⟩
  tsupport_subset' := subset_univ _
/-- Evaluating `steinerFiberTestFunction ψ he y` at `t` gives `ψ ((y : E) + t • e)`. -/
@[simp] theorem steinerFiberTestFunction_apply (ψ : 𝓓((⊤ : Opens E), ℝ)) {e : E} (he : ‖e‖ = 1)
    (y : orthogonalHyperplane e) (t : ℝ) :
    steinerFiberTestFunction ψ he y t = ψ ((y : E) + t • e) := by rfl
/-- Derivative of `steinerFiberTestFunction ψ he y` at `t` in direction `e`. -/
theorem hasDerivAt_steinerFiberTestFunction (ψ : 𝓓((⊤ : Opens E), ℝ)) {e : E} (he : ‖e‖ = 1)
    (y : orthogonalHyperplane e) (t : ℝ) :
    HasDerivAt (steinerFiberTestFunction ψ he y : ℝ → ℝ)
      (fderiv ℝ (ψ : E → ℝ) ((y : E) + t • e) e) t := by
  have hd : HasFDerivAt (ψ : E → ℝ) (fderiv ℝ (ψ : E → ℝ) ((y : E) + t • e)) ((y : E) + t • e) :=
    (ψ.contDiff.differentiable (by simp) _).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ ↦ (y : E) + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add (y : E)
  exact hd.comp_hasDerivAt t hline
/-- One-dimensional divergence of `steinerFiberTestFunction ψ he y` at `t`. -/
theorem divergence_steinerFiberTestFunction (ψ : 𝓓((⊤ : Opens E), ℝ)) {e : E} (he : ‖e‖ = 1)
    (y : orthogonalHyperplane e) (t : ℝ) :
    divergence (steinerFiberTestFunction ψ he y : ℝ → ℝ) t =
      fderiv ℝ (ψ : E → ℝ) ((y : E) + t • e) e := by
  rw [divergence_eq_deriv, (hasDerivAt_steinerFiberTestFunction ψ he y t).deriv]
/-- Exact 1D perimeter of `symmetricInterval A` when `0 < volume A < ⊤`. -/
theorem perimeter_symmetricInterval_of_volume_pos {A : Set ℝ} (h0 : 0 < volume A)
    (htop : volume A < ⊤) : perimeter volume (symmetricInterval A) = 2 := by
  refine (ordConnected_symmetricInterval A).perimeter_eq_two ?_ ?_ <;>
    rwa [volume_symmetricInterval]
/-- Exact 1D perimeter of `symmetricInterval A` when `volume A = 0`. -/
@[simp] theorem perimeter_symmetricInterval_of_volume_eq_zero {A : Set ℝ} (h0 : volume A = 0) :
    perimeter volume (symmetricInterval A) = 0 := by
  rw [symmetricInterval_of_volume_eq_zero h0, perimeter_empty]
/-- Pointwise 1D perimeter formula for a Steiner-symmetrized fiber of finite 1D measure. -/
theorem perimeter_steinerFiber_steinerSymmetrization_eq_indicator {e : E} (he : ‖e‖ = 1)
    {s : Set E} {y : orthogonalHyperplane e} (htop : volume (steinerFiber e s y) < ⊤) :
    perimeter volume (steinerFiber e (steinerSymmetrization e s) y) =
      {y' : orthogonalHyperplane e | 0 < volume (steinerFiber e s y')}.indicator
        (fun _ ↦ (2 : ℝ≥0∞)) y := by
  rw [steinerFiber_steinerSymmetrization he]
  by_cases h0 : 0 < volume (steinerFiber e s y)
  · rw [indicator_of_mem (s := {y' | 0 < volume (steinerFiber e s y')}) h0,
      perimeter_symmetricInterval_of_volume_pos h0 htop]
  · rw [indicator_of_notMem (s := {y' | 0 < volume (steinerFiber e s y')}) h0,
      perimeter_symmetricInterval_of_volume_eq_zero (nonpos_iff_eq_zero.mp (not_lt.mp h0))]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Directional variation line-slicing inequality along a unit vector `e : E`**. -/
theorem directionalVariation_le_lintegral_steinerFiber {e : E} (he : ‖e‖ = 1)
    {u : E → ℝ} (hu : LocallyIntegrable u volume) :
    directionalVariation volume ⊤ e u ≤
      ∫⁻ y : orthogonalHyperplane e,
        distributionalVariation volume ⊤ (fun t : ℝ ↦ u ((y : E) + t • e)) ∂volume := by
  refine iSup₂_le fun ψ hψ ↦ ?_
  set F : E → ℝ := fun x ↦ u x * fderiv ℝ (ψ : E → ℝ) x e
  have hF_int : Integrable F volume :=
    integrable_mul_fderiv_of_locallyIntegrableOn (hu.locallyIntegrableOn ⊤) ψ e
  have hmp := measurePreserving_orthogonalHyperplaneProdMeasurableEquiv he
  have hF_prod : Integrable (F ∘ orthogonalHyperplaneProdMeasurableEquiv he)
      ((volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ)) :=
    (hmp.integrable_comp_emb (orthogonalHyperplaneProdMeasurableEquiv he).measurableEmbedding).2
      hF_int
  have hint_eq : ∫ x in ((⊤ : Opens E) : Set E), F x ∂volume =
      ∫ y : orthogonalHyperplane e, ∫ t : ℝ, F ((y : E) + t • e) := by
    rw [Opens.coe_top, Measure.restrict_univ,
      ← hmp.integral_comp (orthogonalHyperplaneProdMeasurableEquiv he).measurableEmbedding F]
    exact integral_prod (F ∘ orthogonalHyperplaneProdMeasurableEquiv he) hF_prod
  rw [hint_eq]; refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y ↦ ?_)
  rw [Real.enorm_eq_ofReal_abs]
  have hslice : (∫ t : ℝ, F ((y : E) + t • e)) =
      ∫ t in ((⊤ : Opens ℝ) : Set ℝ),
        u ((y : E) + t • e) * divergence (steinerFiberTestFunction ψ he y : ℝ → ℝ) t := by
    simp only [F, Opens.coe_top, Measure.restrict_univ, divergence_steinerFiberTestFunction]
  rw [hslice]
  exact abs_le_distributionalVariation (steinerFiberTestFunction ψ he y)
    (fun t ↦ hψ ((y : E) + t • e)) (fun t ↦ u ((y : E) + t • e))
/-- **Directional perimeter line-slicing inequality along a unit vector `e : E`**. -/
theorem directionalPerimeter_le_lintegral_steinerFiber {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) :
    directionalPerimeter volume ⊤ e s ≤
      ∫⁻ y : orthogonalHyperplane e, perimeter volume (steinerFiber e s y) ∂volume := by
  refine (directionalVariation_le_lintegral_steinerFiber he
    (locallyIntegrable_indicator_one_of_nullMeasurableSet hs)).trans (lintegral_mono fun y ↦ ?_)
  have heq : (fun t : ℝ ↦ s.indicator (fun _ ↦ (1 : ℝ)) ((y : E) + t • e)) =
      (steinerFiber e s y).indicator (fun _ ↦ (1 : ℝ)) := by
    ext t; by_cases h : (y : E) + t • e ∈ s <;> simp [mem_steinerFiber_iff, h]
  rw [perimeter, relativePerimeter, heq]
/-- If `s : Set E` is null-measurable, then a.e. fiber `steinerFiber e s y` is null-measurable. -/
theorem ae_nullMeasurableSet_steinerFiber {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume, NullMeasurableSet (steinerFiber e s y) volume := by
  rcases hs with ⟨t, htm, hst⟩
  filter_upwards [ae_steinerFiber_ae_eq he hst] with y hy using
    (measurableSet_steinerFiber htm y).nullMeasurableSet.congr hy.symm
/-- If `s : Set E` is null-measurable, then `y ↦ volume (steinerFiber e s y)` is a.e. measurable. -/
theorem aemeasurable_volume_steinerFiber₀ {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    AEMeasurable (fun y : orthogonalHyperplane e ↦ volume (steinerFiber e s y)) volume := by
  rcases hs with ⟨t, htm, hst⟩
  exact (measurable_volume_steinerFiber htm).aemeasurable.congr
    (EventuallyEq.symm (ae_volume_steinerFiber_eq he hst))
/-- If `s : Set E` is null-measurable and `volume s < ⊤`, then a.e. fiber has finite 1D measure. -/
theorem ae_volume_steinerFiber_lt_top {e : E} (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume, volume (steinerFiber e s y) < ⊤ := by
  refine ae_lt_top' (aemeasurable_volume_steinerFiber₀ he hs) ?_
  rw [← volume_eq_lintegral_steinerFiber₀ he hs]; exact htop.ne
/-- If `s =ᵐ[volume] t`, then a.e. fiber has the same 1D perimeter. -/
theorem ae_perimeter_steinerFiber_eq {e : E} (he : ‖e‖ = 1) {s t : Set E} (hst : s =ᵐ[volume] t) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume,
      perimeter volume (steinerFiber e s y) = perimeter volume (steinerFiber e t y) := by
  filter_upwards [ae_steinerFiber_ae_eq he hst] with y hy using perimeter_congr_ae hy
/-- Exact formula for the integrated fiber perimeter of `steinerSymmetrization e s`: each active
fiber contributes perimeter `2`. -/
theorem lintegral_perimeter_steinerFiber_steinerSymmetrization {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) :
    (∫⁻ y : orthogonalHyperplane e,
        perimeter volume (steinerFiber e (steinerSymmetrization e s) y) ∂volume) =
      2 * volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} := by
  rcases hs with ⟨t, htm, hst⟩
  have hfin := ae_volume_steinerFiber_lt_top he ⟨t, htm, hst⟩ htop
  have hvol_eq := ae_volume_steinerFiber_eq he hst
  let A_s : Set (orthogonalHyperplane e) := {y | 0 < volume (steinerFiber e s y)}
  let A_t : Set (orthogonalHyperplane e) := {y | 0 < volume (steinerFiber e t y)}
  have hA_meas : MeasurableSet A_t := measurable_volume_steinerFiber htm measurableSet_Ioi
  have hA_ae : A_s =ᵐ[volume] A_t := by
    filter_upwards [hvol_eq] with y hy; exact propext (by simp [A_s, A_t, hy])
  have hfun_ae :
      (fun y : orthogonalHyperplane e ↦
        perimeter volume (steinerFiber e (steinerSymmetrization e s) y)) =ᵐ[volume]
      A_t.indicator (fun _ ↦ (2 : ℝ≥0∞)) := by
    filter_upwards [hfin, hvol_eq] with y hy_fin hy_eq
    rw [perimeter_steinerFiber_steinerSymmetrization_eq_indicator he hy_fin]
    by_cases hy : 0 < volume (steinerFiber e t y)
    · have hys : 0 < volume (steinerFiber e s y) := hy_eq.symm ▸ hy; simp [A_t, hy, hys]
    · have hys : ¬ 0 < volume (steinerFiber e s y) := hy_eq.symm ▸ hy; simp [A_t, hy, hys]
  rw [lintegral_congr_ae hfun_ae, lintegral_indicator_const hA_meas 2, measure_congr hA_ae]
/-- **Directional perimeter upper bound for `steinerSymmetrization e s`**. -/
theorem directionalPerimeter_steinerSymmetrization_le {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) :
    directionalPerimeter volume ⊤ e (steinerSymmetrization e s) ≤
      2 * volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} := by
  calc
    directionalPerimeter volume ⊤ e (steinerSymmetrization e s)
      ≤ ∫⁻ y : orthogonalHyperplane e,
          perimeter volume (steinerFiber e (steinerSymmetrization e s) y) ∂volume :=
        directionalPerimeter_le_lintegral_steinerFiber he
          (nullMeasurableSet_steinerSymmetrization he hs)
    _ = 2 * volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} :=
        lintegral_perimeter_steinerFiber_steinerSymmetrization he hs htop
/-- **One-dimensional slice isoperimetric lower bound along unit direction `e`**. -/
theorem two_mul_volume_steinerFiber_pos_le_lintegral_perimeter {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) :
    2 * volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} ≤
      ∫⁻ y : orthogonalHyperplane e, perimeter volume (steinerFiber e s y) ∂volume := by
  rcases hs with ⟨t, htm, hst⟩
  have hmp := measurePreserving_orthogonalHyperplaneProdMeasurableEquiv he
  have hpre_meas : MeasurableSet (orthogonalHyperplaneProdMeasurableEquiv he ⁻¹' t) :=
    (orthogonalHyperplaneProdMeasurableEquiv he).measurable htm
  have hpre_top :
      ((volume : Measure (orthogonalHyperplane e)).prod (volume : Measure ℝ))
        (orthogonalHyperplaneProdMeasurableEquiv he ⁻¹' t) < ⊤ := by
    rw [hmp.measure_preimage_equiv t, ← measure_congr hst]; exact htop
  have hle := two_mul_measure_slice_pos_le_lintegral_perimeter_slice_of_measure_lt_top
    hpre_meas hpre_top
  have hA_ae : {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} =ᵐ[volume]
      {y : orthogonalHyperplane e | 0 < volume (steinerFiber e t y)} := by
    filter_upwards [ae_volume_steinerFiber_eq he hst] with y hy; exact propext (by simp [hy])
  rw [measure_congr hA_ae, lintegral_congr_ae (ae_perimeter_steinerFiber_eq he hst)]; exact hle
/-- Steiner symmetrization does not increase the integrated 1D fiber perimeter in direction `e`. -/
theorem lintegral_perimeter_steinerFiber_steinerSymmetrization_le {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) :
    (∫⁻ y : orthogonalHyperplane e,
        perimeter volume (steinerFiber e (steinerSymmetrization e s) y) ∂volume) ≤
      ∫⁻ y : orthogonalHyperplane e, perimeter volume (steinerFiber e s y) ∂volume := by
  rw [lintegral_perimeter_steinerFiber_steinerSymmetrization he hs htop]
  exact two_mul_volume_steinerFiber_pos_le_lintegral_perimeter he hs htop
/-- The directional perimeter of `steinerSymmetrization e s` in direction `e` is bounded above by
the integrated 1D fiber perimeter of `s`. -/
theorem directionalPerimeter_steinerSymmetrization_le_lintegral_perimeter {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤) :
    directionalPerimeter volume ⊤ e (steinerSymmetrization e s) ≤
      ∫⁻ y : orthogonalHyperplane e, perimeter volume (steinerFiber e s y) ∂volume :=
  (directionalPerimeter_steinerSymmetrization_le he hs htop).trans
    (two_mul_volume_steinerFiber_pos_le_lintegral_perimeter he hs htop)
/-- **Fiberwise interval rigidity below perimeter `4` along unit direction `e`**. -/
theorem ae_exists_ordConnected_ae_eq_steinerFiber_of_ae_perimeter_lt_four {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤)
    (hper : ∀ᵐ y : orthogonalHyperplane e ∂volume, perimeter volume (steinerFiber e s y) < 4) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ (steinerFiber e s y =ᵐ[volume] I) := by
  filter_upwards [ae_nullMeasurableSet_steinerFiber he hs,
    ae_volume_steinerFiber_lt_top he hs htop, hper] with y hnm hfin hpy
  exact exists_ordConnected_ae_eq_of_perimeter_lt_four hnm hfin hpy
/-- **Fiberwise open-interval rigidity below perimeter `4` along unit direction `e`**. -/
theorem ae_exists_Ioo_ae_eq_steinerFiber_of_ae_perimeter_lt_four {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤)
    (hper : ∀ᵐ y : orthogonalHyperplane e ∂volume, perimeter volume (steinerFiber e s y) < 4) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ a b : ℝ, a ≤ b ∧ (steinerFiber e s y =ᵐ[volume] Ioo a b) := by
  filter_upwards [ae_nullMeasurableSet_steinerFiber he hs,
    ae_volume_steinerFiber_lt_top he hs htop, hper] with y hnm hfin hpy
  exact exists_Ioo_ae_eq_of_perimeter_lt_four hnm hfin hpy
/-- **Slice isoperimetric equality rigidity along unit direction `e`**: if the integrated 1D fiber
perimeter of `s` is at most `2 * volume {y | 0 < volume (steinerFiber e s y)}`, then a.e. fiber
has perimeter `< 4`. -/
theorem ae_perimeter_steinerFiber_lt_four_of_lintegral_perimeter_le {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤)
    (hmeas_lt : volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} < ⊤)
    (hf_meas : AEMeasurable
      (fun y : orthogonalHyperplane e ↦ perimeter volume (steinerFiber e s y)) volume)
    (hle : (∫⁻ y : orthogonalHyperplane e, perimeter volume (steinerFiber e s y) ∂volume) ≤
      2 * volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)}) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume, perimeter volume (steinerFiber e s y) < 4 := by
  rcases hs with ⟨t, htm, hst⟩
  let A_s : Set (orthogonalHyperplane e) := {y | 0 < volume (steinerFiber e s y)}
  let A_t : Set (orthogonalHyperplane e) := {y | 0 < volume (steinerFiber e t y)}
  have hA_meas : MeasurableSet A_t := measurable_volume_steinerFiber htm measurableSet_Ioi
  have hvol_eq := ae_volume_steinerFiber_eq he hst
  have hA_ae : A_s =ᵐ[volume] A_t := by
    filter_upwards [hvol_eq] with y hy; exact propext (by simp [A_s, A_t, hy])
  let g : orthogonalHyperplane e → ℝ≥0∞ := A_t.indicator fun _ ↦ 2
  let f : orthogonalHyperplane e → ℝ≥0∞ := fun y ↦ perimeter volume (steinerFiber e s y)
  have h_ae_le : g ≤ᵐ[volume] f := by
    filter_upwards [ae_nullMeasurableSet_steinerFiber he ⟨t, htm, hst⟩,
      ae_volume_steinerFiber_lt_top he ⟨t, htm, hst⟩ htop, hvol_eq] with y hnm hfin hy_eq
    by_cases hyA : y ∈ A_t
    · simp only [g, indicator_of_mem hyA]
      exact two_le_perimeter_of_volume_pos hnm (hy_eq.symm ▸ hyA) hfin
    · simp [g, hyA]
  have hint_g : ∫⁻ y, g y ∂volume = 2 * volume A_s := by
    rw [lintegral_indicator_const hA_meas 2, measure_congr hA_ae]
  have hint_lt : (∫⁻ y, g y ∂volume) ≠ ⊤ :=
    hint_g ▸ ENNReal.mul_ne_top ENNReal.ofNat_ne_top hmeas_lt.ne
  have hae_eq : g =ᵐ[volume] f :=
    ae_eq_of_ae_le_of_lintegral_le h_ae_le hint_lt hf_meas (hint_g.symm ▸ hle)
  filter_upwards [hae_eq] with y hgf
  change f y < 4; rw [← hgf]; by_cases hyA : y ∈ A_t <;> simp [g, hyA]; norm_num
/-- Under the slice perimeter equality condition in direction `e`, the set of fibers with perimeter
at least `4` has `(n - 1)`-dimensional measure zero. -/
theorem volume_steinerFiber_perimeter_ge_four_eq_zero {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤)
    (hmeas_lt : volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} < ⊤)
    (hf_meas : AEMeasurable
      (fun y : orthogonalHyperplane e ↦ perimeter volume (steinerFiber e s y)) volume)
    (hle : (∫⁻ y : orthogonalHyperplane e, perimeter volume (steinerFiber e s y) ∂volume) ≤
      2 * volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)}) :
    volume {y : orthogonalHyperplane e | 4 ≤ perimeter volume (steinerFiber e s y)} = 0 := by
  have hae := ae_iff.mp (ae_perimeter_steinerFiber_lt_four_of_lintegral_perimeter_le
    he hs htop hmeas_lt hf_meas hle)
  simpa only [not_lt] using hae
/-- **Slice interval rigidity along unit direction `e` (`OrdConnected` sections)**. -/
theorem ae_exists_ordConnected_ae_eq_steinerFiber {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤)
    (hmeas_lt : volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} < ⊤)
    (hf_meas : AEMeasurable
      (fun y : orthogonalHyperplane e ↦ perimeter volume (steinerFiber e s y)) volume)
    (hle : (∫⁻ y : orthogonalHyperplane e, perimeter volume (steinerFiber e s y) ∂volume) ≤
      2 * volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)}) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ (steinerFiber e s y =ᵐ[volume] I) :=
  ae_exists_ordConnected_ae_eq_steinerFiber_of_ae_perimeter_lt_four he hs htop
    (ae_perimeter_steinerFiber_lt_four_of_lintegral_perimeter_le he hs htop hmeas_lt hf_meas hle)
/-- **Slice interval rigidity along unit direction `e` (open intervals `Ioo a b`)**. -/
theorem ae_exists_Ioo_ae_eq_steinerFiber {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (htop : volume s < ⊤)
    (hmeas_lt : volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} < ⊤)
    (hf_meas : AEMeasurable
      (fun y : orthogonalHyperplane e ↦ perimeter volume (steinerFiber e s y)) volume)
    (hle : (∫⁻ y : orthogonalHyperplane e, perimeter volume (steinerFiber e s y) ∂volume) ≤
      2 * volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)}) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ a b : ℝ, a ≤ b ∧ (steinerFiber e s y =ᵐ[volume] Ioo a b) :=
  ae_exists_Ioo_ae_eq_steinerFiber_of_ae_perimeter_lt_four he hs htop
    (ae_perimeter_steinerFiber_lt_four_of_lintegral_perimeter_le he hs htop hmeas_lt hf_meas hle)
/-- Having a.e. `OrdConnected` fibers in direction `e` is invariant under `=ᵐ[volume]` modification
of the ambient set `s : Set E`. -/
theorem ae_exists_ordConnected_ae_eq_steinerFiber_of_ae_eq {e : E} (he : ‖e‖ = 1)
    {s t : Set E} (hst : s =ᵐ[volume] t)
    (hs : ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ (steinerFiber e s y =ᵐ[volume] I)) :
    ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ (steinerFiber e t y =ᵐ[volume] I) := by
  filter_upwards [ae_steinerFiber_ae_eq he hst, hs] with y hyt ⟨I, hI, hyI⟩ using
    ⟨I, hI, hyt.symm.trans hyI⟩

end DirectionalSlicePerimeterAndRigidity

end TauCeti.MeasureTheory
