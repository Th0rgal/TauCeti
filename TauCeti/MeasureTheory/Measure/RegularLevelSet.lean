/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import TauCeti.Analysis.Calculus.Sard.OutermostStratum
public import TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
public import TauCeti.MeasureTheory.Measure.PerimeterCutoff
public import TauCeti.MeasureTheory.Measure.PerimeterSlicing
import all TauCeti.Analysis.Calculus.Sard.OutermostStratum
import all TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.PerimeterSlicing
import all TauCeti.MeasureTheory.Measure.PerimeterTransport

/-!
# Scalar Sard Theorem, Regular-Value Superlevel Topology, and Regular-Level Coarea Selection

This file develops the smooth scalar Morse–Sard theorem, the topological regularity of superlevel
and level sets at regular values, measurability and lower semicontinuity of the superlevel
perimeter profile, and the regular-level Chebyshev / mean-value selection principle for smooth
approximation of sets of finite perimeter:

1. **Scalar critical points, critical values, regular values, and smooth scalar Sard**:
   `scalarCriticalPoints`, `scalarCriticalValues`, `scalarRegularValues`,
   `surjective_continuousLinearMap_real_iff_ne_zero`, `mem_scalarCriticalPoints_iff`,
   `mem_scalarRegularValues_iff`, `volume_scalarCriticalValues_eq_zero`,
   `volume_criticalValues_eq_zero`, `ae_mem_scalarRegularValues`, and `dense_scalarRegularValues`.
2. **Regular-value superlevel topology and level-set boundary comparisons**:
   `superlevelSetLT`, `superlevelSetLE`, `levelSet`,
   `mem_closure_superlevelSetLT_of_fderiv_ne_zero`,
   `notMem_interior_superlevelSetLE_of_fderiv_ne_zero`,
   `closure_superlevelSetLT_eq_superlevelSetLE`, `interior_superlevelSetLE_eq_superlevelSetLT`,
   `isRegularOpen_superlevelSetLT`, `frontier_superlevelSetLT_eq_levelSet`,
   `frontier_superlevelSetLE_eq_levelSet`, and `ae_measure_levelSet_eq_zero`.
3. **Semicontinuity, Borel measurability, regular-level coarea, and regular-level selection**:
   `lowerSemicontinuousAt_relativePerimeter_superlevelSetLT`,
   `measurable_relativePerimeter_superlevelSetLT`,
   `setLIntegral_scalarRegularValues_relativePerimeter_superlevelSetLT`,
   `exists_regularValue_mem_Ioo_relativePerimeter_le`,
   `mul_measure_symmDiff_superlevelSetLT_le_lintegral_abs_sub`, and
   `exists_regularValue_mem_Ioo_symmDiff_and_relativePerimeter_le`.
-/

public section

open Filter Function MeasureTheory Set TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Distributions Topology ContDiff symmDiff Gradient

namespace TauCeti

/-! ### Section 1: Scalar Critical Points, Critical Values, Regular Values, and Smooth Sard -/

section ScalarCriticalAndSard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous linear functional `L : E →L[ℝ] ℝ` is surjective if and only if `L ≠ 0`. -/
theorem surjective_continuousLinearMap_real_iff_ne_zero (L : E →L[ℝ] ℝ) :
    Function.Surjective L ↔ L ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h y ↦ ?_⟩
  · rintro rfl; obtain ⟨x, hx⟩ := h 1; exact zero_ne_one hx
  · obtain ⟨x, hx⟩ : ∃ x, L x ≠ 0 := by by_contra! h0; exact h (ContinuousLinearMap.ext h0)
    exact ⟨(y / L x) • x, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]⟩
/-- A continuous linear functional `L : E →L[ℝ] ℝ` fails to be surjective if and only if `L = 0`. -/
@[simp] theorem not_surjective_continuousLinearMap_real_iff_eq_zero (L : E →L[ℝ] ℝ) :
    ¬ Function.Surjective L ↔ L = 0 := by
  rw [surjective_continuousLinearMap_real_iff_ne_zero, not_not]
/-- The **scalar critical points** `{x : E | ¬ Function.Surjective (fderiv ℝ f x)}`. -/
@[expose] def scalarCriticalPoints (f : E → ℝ) : Set E :=
  {x : E | ¬ Function.Surjective (fderiv ℝ f x)}
/-- The **scalar critical values** `f '' scalarCriticalPoints f` of `f : E → ℝ`. -/
@[expose] def scalarCriticalValues (f : E → ℝ) : Set ℝ := f '' scalarCriticalPoints f
/-- The **scalar regular values** `(scalarCriticalValues f)ᶜ` of `f : E → ℝ`. -/
@[expose] def scalarRegularValues (f : E → ℝ) : Set ℝ := (scalarCriticalValues f)ᶜ
theorem mem_scalarCriticalPoints {f : E → ℝ} {x : E} :
    x ∈ scalarCriticalPoints f ↔ ¬ Function.Surjective (fderiv ℝ f x) := Iff.rfl
/-- A point `x : E` is a scalar critical point of `f : E → ℝ` if and only if `fderiv ℝ f x = 0`. -/
@[simp] theorem mem_scalarCriticalPoints_iff {f : E → ℝ} {x : E} :
    x ∈ scalarCriticalPoints f ↔ fderiv ℝ f x = 0 :=
  not_surjective_continuousLinearMap_real_iff_eq_zero (fderiv ℝ f x)
/-- A point `x : E` is not a scalar critical point of `f : E → ℝ` iff `fderiv ℝ f x ≠ 0`. -/
theorem notMem_scalarCriticalPoints_iff {f : E → ℝ} {x : E} :
    x ∉ scalarCriticalPoints f ↔ fderiv ℝ f x ≠ 0 := not_congr mem_scalarCriticalPoints_iff
/-- Equivalently, `scalarCriticalPoints f = {x : E | fderiv ℝ f x = 0}`. -/
theorem scalarCriticalPoints_eq_setOf_fderiv_eq_zero (f : E → ℝ) :
    scalarCriticalPoints f = {x : E | fderiv ℝ f x = 0} := by
  ext x; exact mem_scalarCriticalPoints_iff
/-- A value `t : ℝ` is a scalar critical value of `f` iff `∃ x, fderiv ℝ f x = 0 ∧ f x = t`. -/
theorem mem_scalarCriticalValues_iff {f : E → ℝ} {t : ℝ} :
    t ∈ scalarCriticalValues f ↔ ∃ x, fderiv ℝ f x = 0 ∧ f x = t := by simp [scalarCriticalValues]
/-- `t ∈ scalarRegularValues f` iff `fderiv ℝ f x` is surjective whenever `f x = t`. -/
theorem mem_scalarRegularValues_iff_surjective {f : E → ℝ} {t : ℝ} :
    t ∈ scalarRegularValues f ↔ ∀ x, f x = t → Function.Surjective (fderiv ℝ f x) := by
  simp only [scalarRegularValues, mem_compl_iff, scalarCriticalValues, mem_image,
    mem_scalarCriticalPoints, not_exists, not_and]
  exact ⟨fun h x hx ↦ by_contra fun hns ↦ h x hns hx, fun h x hns hx ↦ hns (h x hx)⟩
/-- `t ∈ scalarRegularValues f` iff `fderiv ℝ f x ≠ 0` at every `x` with `f x = t`. -/
theorem mem_scalarRegularValues_iff {f : E → ℝ} {t : ℝ} :
    t ∈ scalarRegularValues f ↔ ∀ x, f x = t → fderiv ℝ f x ≠ 0 := by
  simp_rw [mem_scalarRegularValues_iff_surjective, surjective_continuousLinearMap_real_iff_ne_zero]
@[simp] theorem compl_scalarCriticalValues (f : E → ℝ) :
    (scalarCriticalValues f)ᶜ = scalarRegularValues f := rfl
@[simp] theorem compl_scalarRegularValues (f : E → ℝ) :
    (scalarRegularValues f)ᶜ = scalarCriticalValues f := compl_compl _
@[simp] theorem scalarCriticalPoints_neg (f : E → ℝ) :
    scalarCriticalPoints (-f) = scalarCriticalPoints f := by ext x; simp [fderiv_neg]
@[simp] theorem scalarCriticalPoints_add_const (f : E → ℝ) (c : ℝ) :
    scalarCriticalPoints (fun x ↦ f x + c) = scalarCriticalPoints f := by
  ext x; simp [fderiv_add_const]
@[simp] theorem scalarCriticalPoints_sub_const (f : E → ℝ) (c : ℝ) :
    scalarCriticalPoints (fun x ↦ f x - c) = scalarCriticalPoints f := by simp [sub_eq_add_neg]
/-- For a `C¹` function `f : E → ℝ`, the critical set `scalarCriticalPoints f` is closed. -/
theorem isClosed_scalarCriticalPoints_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    IsClosed (scalarCriticalPoints f) := by
  rw [scalarCriticalPoints_eq_setOf_fderiv_eq_zero]
  exact isClosed_eq (hf.continuous_fderiv one_ne_zero) continuous_const
/-- In a complete real inner product space, `x ∈ scalarCriticalPoints f ↔ ∇ f x = 0`. -/
theorem mem_scalarCriticalPoints_iff_gradient_eq_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {f : H → ℝ} {x : H} :
    x ∈ scalarCriticalPoints f ↔ ∇ f x = 0 := by
  rw [mem_scalarCriticalPoints_iff, gradient, LinearIsometryEquiv.map_eq_zero_iff]

variable [FiniteDimensional ℝ E]

/-- **Scalar Morse–Sard theorem for `Cⁿ` functions** with `(finrank ℝ E)^2 + 1 ≤ n`. -/
theorem volume_scalarCriticalValues_eq_zero_of_contDiff {n : ℕ∞ω} {f : E → ℝ}
    (hf : ContDiff ℝ n f) (hk : ((Module.finrank ℝ E * Module.finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n) :
    volume (scalarCriticalValues f) = 0 := hf.addHaar_image_criticalPoints_eq_zero (ν := volume) hk
/-- **Smooth scalar Morse–Sard theorem (`ContDiff ℝ ∞ f`)**. -/
theorem volume_scalarCriticalValues_eq_zero {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    volume (scalarCriticalValues f) = 0 :=
  hf.addHaar_image_criticalPoints_eq_zero (ν := volume) (WithTop.coe_le_coe.mpr le_top)
/-- Smooth scalar Morse–Sard theorem for analytic / `⊤`-smooth functions (`ContDiff ℝ ⊤ f`). -/
theorem volume_scalarCriticalValues_eq_zero_of_top {f : E → ℝ} (hf : ContDiff ℝ ⊤ f) :
    volume (scalarCriticalValues f) = 0 := volume_scalarCriticalValues_eq_zero (hf.of_le le_top)
/-- **Smooth scalar Morse–Sard theorem on `EuclideanSpace ℝ (Fin n)`**. -/
theorem volume_criticalValues_eq_zero {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
  hf.addHaar_image_criticalPoints_eq_zero (ν := volume) (WithTop.coe_le_coe.mpr le_top)
/-- **Almost every real number is a regular value** of a `C∞` function `f : E → ℝ`. -/
theorem ae_mem_scalarRegularValues {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ᵐ t : ℝ ∂volume, t ∈ scalarRegularValues f :=
  compl_mem_ae_iff.mpr (volume_scalarCriticalValues_eq_zero hf)
/-- `scalarRegularValues f` is `volume`-null-measurable for any `C∞` function `f : E → ℝ`. -/
theorem nullMeasurableSet_scalarRegularValues {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    NullMeasurableSet (scalarRegularValues f) volume :=
  (NullMeasurableSet.of_null (volume_scalarCriticalValues_eq_zero hf)).compl
/-- Intersecting any set `S : Set ℝ` with `scalarRegularValues f` preserves `volume S`. -/
@[simp] theorem volume_inter_scalarRegularValues {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (S : Set ℝ) :
    volume (S ∩ scalarRegularValues f) = volume S := by
  refine measure_congr ?_
  filter_upwards [ae_mem_scalarRegularValues hf] with t ht
  exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, ht⟩⟩
/-- Intersecting `scalarRegularValues f` on the left with `S : Set ℝ` preserves `volume S`. -/
@[simp] theorem volume_scalarRegularValues_inter {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (S : Set ℝ) :
    volume (scalarRegularValues f ∩ S) = volume S := by
  rw [Set.inter_comm, volume_inter_scalarRegularValues hf S]
/-- **The regular values of any `C∞` scalar function `f : E → ℝ` are dense in `ℝ`**. -/
theorem dense_scalarRegularValues {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Dense (scalarRegularValues f) :=
  hf.dense_compl_image_criticalPoints (WithTop.coe_le_coe.mpr le_top)
/-- Every `Set.Ioo a b` (`a < b`) contains a regular value of a `C∞` function `f : E → ℝ`. -/
theorem exists_mem_Ioo_inter_scalarRegularValues {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) : ∃ t ∈ Set.Ioo a b, t ∈ scalarRegularValues f := by
  obtain ⟨t, htIoo, htReg⟩ :=
    (dense_scalarRegularValues hf).inter_open_nonempty (Set.Ioo a b) isOpen_Ioo
      (Set.nonempty_Ioo.mpr hab)
  exact ⟨t, htIoo, htReg⟩

end ScalarCriticalAndSard

/-! ### Section 2: Regular-Value Superlevel Set Topology and Boundary Comparisons -/

section RegularLevelTopology

variable {E : Type*}

/-- The **strict superlevel set** `{x : E | t < f x}` of `f : E → ℝ` at level `t : ℝ`. -/
@[expose] def superlevelSetLT (f : E → ℝ) (t : ℝ) : Set E := {x : E | t < f x}

/-- The **weak superlevel set** `{x : E | t ≤ f x}` of `f : E → ℝ` at level `t : ℝ`. -/
@[expose] def superlevelSetLE (f : E → ℝ) (t : ℝ) : Set E := {x : E | t ≤ f x}

/-- The **level set** `{x : E | f x = t}` of `f : E → ℝ` at level `t : ℝ`. -/
@[expose] def levelSet (f : E → ℝ) (t : ℝ) : Set E := {x : E | f x = t}
@[simp] theorem mem_superlevelSetLT {f : E → ℝ} {t : ℝ} {x : E} :
    x ∈ superlevelSetLT f t ↔ t < f x := Iff.rfl
@[simp] theorem mem_superlevelSetLE {f : E → ℝ} {t : ℝ} {x : E} :
    x ∈ superlevelSetLE f t ↔ t ≤ f x := Iff.rfl
@[simp] theorem mem_levelSet {f : E → ℝ} {t : ℝ} {x : E} : x ∈ levelSet f t ↔ f x = t := Iff.rfl
theorem superlevelSetLT_eq_preimage (f : E → ℝ) (t : ℝ) :
    superlevelSetLT f t = f ⁻¹' Set.Ioi t := rfl
theorem superlevelSetLE_eq_preimage (f : E → ℝ) (t : ℝ) :
    superlevelSetLE f t = f ⁻¹' Set.Ici t := rfl
theorem levelSet_eq_preimage (f : E → ℝ) (t : ℝ) : levelSet f t = f ⁻¹' {t} := rfl
theorem superlevelSetLT_subset_superlevelSetLE (f : E → ℝ) (t : ℝ) :
    superlevelSetLT f t ⊆ superlevelSetLE f t := fun _ (hx : t < f _) ↦ le_of_lt hx
theorem levelSet_subset_superlevelSetLE (f : E → ℝ) (t : ℝ) :
    levelSet f t ⊆ superlevelSetLE f t := fun _ (hx : f _ = t) ↦ hx.symm.le
theorem disjoint_superlevelSetLT_levelSet (f : E → ℝ) (t : ℝ) :
    Disjoint (superlevelSetLT f t) (levelSet f t) :=
  Set.disjoint_left.mpr fun _ (hlt : t < f _) (heq : f _ = t) ↦ hlt.ne' heq
@[simp] theorem superlevelSetLT_union_levelSet (f : E → ℝ) (t : ℝ) :
    superlevelSetLT f t ∪ levelSet f t = superlevelSetLE f t := by
  ext x; simp only [mem_union, mem_superlevelSetLT, mem_levelSet, mem_superlevelSetLE]
  exact ⟨fun h ↦ h.elim le_of_lt (fun h' ↦ h'.symm.le), fun h ↦ h.lt_or_eq.imp id Eq.symm⟩
@[simp] theorem superlevelSetLE_diff_superlevelSetLT (f : E → ℝ) (t : ℝ) :
    superlevelSetLE f t \ superlevelSetLT f t = levelSet f t := by
  ext x; simp only [Set.mem_sdiff, mem_superlevelSetLE, mem_superlevelSetLT, mem_levelSet]
  exact ⟨fun ⟨hle, hnlt⟩ ↦ le_antisymm (not_lt.mp hnlt) hle,
    fun heq ↦ ⟨heq.symm.le, not_lt.mpr heq.le⟩⟩
@[simp] theorem superlevelSetLE_diff_levelSet (f : E → ℝ) (t : ℝ) :
    superlevelSetLE f t \ levelSet f t = superlevelSetLT f t := by
  ext x; simp only [Set.mem_sdiff, mem_superlevelSetLE, mem_levelSet, mem_superlevelSetLT]
  exact ⟨fun ⟨hle, hne⟩ ↦ lt_of_le_of_ne hle (Ne.symm hne), fun hlt ↦ ⟨hlt.le, hlt.ne'⟩⟩
theorem antitone_superlevelSetLT (f : E → ℝ) : Antitone (superlevelSetLT f) :=
  fun _ _ hst _ (hx : _ < f _) ↦ hst.trans_lt hx
theorem antitone_superlevelSetLE (f : E → ℝ) : Antitone (superlevelSetLE f) :=
  fun _ _ hst _ (hx : _ ≤ f _) ↦ hst.trans hx
theorem superlevelSetLE_subset_superlevelSetLT_of_lt (f : E → ℝ) {s t : ℝ} (hst : s < t) :
    superlevelSetLE f t ⊆ superlevelSetLT f s := fun _ (hx : t ≤ f _) ↦ hst.trans_le hx
/-- The level sets `levelSet f t` (`t : ℝ`) are pairwise disjoint. -/
theorem pairwiseDisjoint_levelSet (f : E → ℝ) : (Set.univ : Set ℝ).PairwiseDisjoint (levelSet f) :=
  fun _ _ _ _ hst ↦ Set.disjoint_left.mpr fun _ hx₁ hx₂ ↦ hst (hx₁.symm.trans hx₂)
/-- If `0 < t`, `superlevelSetLE f t ⊆ Function.support f`. -/
theorem superlevelSetLE_subset_support (f : E → ℝ) {t : ℝ} (ht : 0 < t) :
    superlevelSetLE f t ⊆ Function.support f := fun _ (hx : t ≤ f _) h0 ↦ (ht.trans_le hx).ne' h0
theorem superlevelSetLT_subset_support (f : E → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    superlevelSetLT f t ⊆ Function.support f := fun _ (hx : t < f _) h0 ↦ (ht.trans_lt hx).ne' h0

section TopologicalSpace

variable [TopologicalSpace E]

/-- For a continuous function `f : E → ℝ`, `superlevelSetLT f t` is open. -/
theorem isOpen_superlevelSetLT {f : E → ℝ} (hf : Continuous f) (t : ℝ) :
    IsOpen (superlevelSetLT f t) := isOpen_Ioi.preimage hf
/-- For a continuous function `f : E → ℝ`, `superlevelSetLE f t` is closed. -/
theorem isClosed_superlevelSetLE {f : E → ℝ} (hf : Continuous f) (t : ℝ) :
    IsClosed (superlevelSetLE f t) := isClosed_Ici.preimage hf
/-- For a continuous function `f : E → ℝ`, `levelSet f t` is closed. -/
theorem isClosed_levelSet {f : E → ℝ} (hf : Continuous f) (t : ℝ) :
    IsClosed (levelSet f t) := isClosed_singleton.preimage hf
theorem closure_superlevelSetLT_subset_superlevelSetLE {f : E → ℝ} (hf : Continuous f) (t : ℝ) :
    closure (superlevelSetLT f t) ⊆ superlevelSetLE f t :=
  closure_minimal (superlevelSetLT_subset_superlevelSetLE f t) (isClosed_superlevelSetLE hf t)
theorem superlevelSetLT_subset_interior_superlevelSetLE {f : E → ℝ} (hf : Continuous f) (t : ℝ) :
    superlevelSetLT f t ⊆ interior (superlevelSetLE f t) :=
  interior_maximal (superlevelSetLT_subset_superlevelSetLE f t) (isOpen_superlevelSetLT hf t)
theorem frontier_superlevelSetLT_subset_levelSet {f : E → ℝ} (hf : Continuous f) (t : ℝ) :
    frontier (superlevelSetLT f t) ⊆ levelSet f t := by
  rw [frontier, (isOpen_superlevelSetLT hf t).interior_eq, ← superlevelSetLE_diff_superlevelSetLT]
  exact Set.sdiff_subset_sdiff_left (closure_superlevelSetLT_subset_superlevelSetLE hf t)
theorem frontier_superlevelSetLE_subset_levelSet {f : E → ℝ} (hf : Continuous f) (t : ℝ) :
    frontier (superlevelSetLE f t) ⊆ levelSet f t := by
  rw [frontier, (isClosed_superlevelSetLE hf t).closure_eq, ← superlevelSetLE_diff_superlevelSetLT]
  exact Set.sdiff_subset_sdiff_right (superlevelSetLT_subset_interior_superlevelSetLE hf t)
theorem superlevelSetLE_subset_tsupport (f : E → ℝ) {t : ℝ} (ht : 0 < t) :
    superlevelSetLE f t ⊆ tsupport f :=
  (superlevelSetLE_subset_support f ht).trans (subset_tsupport f)
theorem superlevelSetLT_subset_tsupport (f : E → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    superlevelSetLT f t ⊆ tsupport f :=
  (superlevelSetLT_subset_support f ht).trans (subset_tsupport f)
/-- For continuous compactly supported `f`, `superlevelSetLE f t` is compact (`t > 0`). -/
theorem isCompact_superlevelSetLE_of_hasCompactSupport {f : E → ℝ} (hf : Continuous f)
    (hsupp : HasCompactSupport f) {t : ℝ} (ht : 0 < t) :
    IsCompact (superlevelSetLE f t) :=
  hsupp.of_isClosed_subset (isClosed_superlevelSetLE hf t) (superlevelSetLE_subset_tsupport f ht)
/-- If `f : E → ℝ` is continuous and compactly supported, `levelSet f t` is compact for `t > 0`. -/
theorem isCompact_levelSet_of_hasCompactSupport {f : E → ℝ} (hf : Continuous f)
    (hsupp : HasCompactSupport f) {t : ℝ} (ht : 0 < t) :
    IsCompact (levelSet f t) :=
  (isCompact_superlevelSetLE_of_hasCompactSupport hf hsupp ht).of_isClosed_subset
    (isClosed_levelSet hf t) (levelSet_subset_superlevelSetLE f t)

end TopologicalSpace

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Non-critical points lie in the closure of the strict superlevel set**. -/
theorem mem_closure_superlevelSetLT_of_fderiv_ne_zero {f : E → ℝ} {x : E}
    (hx : fderiv ℝ f x ≠ 0) : x ∈ closure (superlevelSetLT f (f x)) := by
  by_contra hcl
  have hint : x ∈ interior (superlevelSetLT f (f x))ᶜ := by rwa [interior_compl]
  have hmax : IsLocalMax f x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hint] with y hy; exact not_lt.mp hy
  exact hx hmax.fderiv_eq_zero
/-- **Non-critical points do not lie in the interior of the weak superlevel set**. -/
theorem notMem_interior_superlevelSetLE_of_fderiv_ne_zero {f : E → ℝ} {x : E}
    (hx : fderiv ℝ f x ≠ 0) : x ∉ interior (superlevelSetLE f (f x)) := by
  intro hint
  have hmin : IsLocalMin f x := mem_interior_iff_mem_nhds.mp hint
  exact hx hmin.fderiv_eq_zero
/-- **Non-critical points lie in the closure of the strict sublevel set**. -/
theorem mem_closure_sublevelSetLT_of_fderiv_ne_zero {f : E → ℝ} {x : E}
    (hx : fderiv ℝ f x ≠ 0) : x ∈ closure {y : E | f y < f x} := by
  have h := notMem_interior_superlevelSetLE_of_fderiv_ne_zero hx
  have hcompl : {y : E | f y < f x} = (superlevelSetLE f (f x))ᶜ := by ext y; simp [superlevelSetLE]
  rwa [hcompl, closure_compl]
/-- At a regular value `t`, `superlevelSetLE f t ⊆ closure (superlevelSetLT f t)`. -/
theorem superlevelSetLE_subset_closure_superlevelSetLT {f : E → ℝ} {t : ℝ}
    (ht : t ∈ scalarRegularValues f) :
    superlevelSetLE f t ⊆ closure (superlevelSetLT f t) := by
  intro x (hx : t ≤ f x)
  rcases hx.lt_or_eq with hlt | heq
  · exact subset_closure hlt
  · rw [heq]
    exact mem_closure_superlevelSetLT_of_fderiv_ne_zero
      (mem_scalarRegularValues_iff.mp ht x heq.symm)
/-- At a regular value `t`, `interior (superlevelSetLE f t) ⊆ superlevelSetLT f t`. -/
theorem interior_superlevelSetLE_subset_superlevelSetLT {f : E → ℝ} {t : ℝ}
    (ht : t ∈ scalarRegularValues f) :
    interior (superlevelSetLE f t) ⊆ superlevelSetLT f t := by
  intro x hx
  have hxle : t ≤ f x := mem_superlevelSetLE.mp (interior_subset hx)
  rcases hxle.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso; rw [heq] at hx
    exact notMem_interior_superlevelSetLE_of_fderiv_ne_zero
      (mem_scalarRegularValues_iff.mp ht x heq.symm) hx
/-- **Closure of a regular strict superlevel set**. -/
theorem closure_superlevelSetLT_eq_superlevelSetLE {f : E → ℝ} (hf : Continuous f) {t : ℝ}
    (ht : t ∈ scalarRegularValues f) :
    closure (superlevelSetLT f t) = superlevelSetLE f t :=
  Set.Subset.antisymm (closure_superlevelSetLT_subset_superlevelSetLE hf t)
    (superlevelSetLE_subset_closure_superlevelSetLT ht)
/-- **Interior of a regular weak superlevel set**. -/
theorem interior_superlevelSetLE_eq_superlevelSetLT {f : E → ℝ} (hf : Continuous f) {t : ℝ}
    (ht : t ∈ scalarRegularValues f) :
    interior (superlevelSetLE f t) = superlevelSetLT f t :=
  Set.Subset.antisymm (interior_superlevelSetLE_subset_superlevelSetLT ht)
    (superlevelSetLT_subset_interior_superlevelSetLE hf t)
/-- **Regular openness of strict superlevel sets at regular values**. -/
theorem isRegularOpen_superlevelSetLT {f : E → ℝ} (hf : Continuous f) {t : ℝ}
    (ht : t ∈ scalarRegularValues f) :
    IsRegularOpen (superlevelSetLT f t) :=
  ⟨isOpen_superlevelSetLT hf t, by
    rw [closure_superlevelSetLT_eq_superlevelSetLE hf ht,
      interior_superlevelSetLE_eq_superlevelSetLT hf ht]⟩
/-- **Exact boundary identity for strict superlevel sets at regular values**. -/
theorem frontier_superlevelSetLT_eq_levelSet {f : E → ℝ} (hf : Continuous f) {t : ℝ}
    (ht : t ∈ scalarRegularValues f) :
    frontier (superlevelSetLT f t) = levelSet f t := by
  rw [frontier, closure_superlevelSetLT_eq_superlevelSetLE hf ht,
    (isOpen_superlevelSetLT hf t).interior_eq, superlevelSetLE_diff_superlevelSetLT]
/-- **Exact boundary identity for weak superlevel sets at regular values**. -/
theorem frontier_superlevelSetLE_eq_levelSet {f : E → ℝ} (hf : Continuous f) {t : ℝ}
    (ht : t ∈ scalarRegularValues f) :
    frontier (superlevelSetLE f t) = levelSet f t := by
  rw [frontier, (isClosed_superlevelSetLE hf t).closure_eq,
    interior_superlevelSetLE_eq_superlevelSetLT hf ht, superlevelSetLE_diff_superlevelSetLT]
/-- At a regular value `t`, `frontier (superlevelSetLT f t) = frontier (superlevelSetLE f t)`. -/
theorem frontier_superlevelSetLT_eq_frontier_superlevelSetLE {f : E → ℝ} (hf : Continuous f)
    {t : ℝ} (ht : t ∈ scalarRegularValues f) :
    frontier (superlevelSetLT f t) = frontier (superlevelSetLE f t) := by
  rw [frontier_superlevelSetLT_eq_levelSet hf ht, frontier_superlevelSetLE_eq_levelSet hf ht]
omit [NormedSpace ℝ E] in
/-- If `f : E → ℝ` is compactly supported, `superlevelSetLT f t` is bounded for `t ≥ 0`. -/
theorem isBounded_superlevelSetLT_of_hasCompactSupport {f : E → ℝ}
    (hsupp : HasCompactSupport f) {t : ℝ} (ht : 0 ≤ t) :
    Bornology.IsBounded (superlevelSetLT f t) :=
  hsupp.isBounded.subset (superlevelSetLT_subset_tsupport f ht)

end NormedSpace

section MeasureLevelSets

variable [MeasurableSpace E] {μ : Measure E}

@[measurability] theorem measurableSet_superlevelSetLT {f : E → ℝ} (hf : Measurable f) (t : ℝ) :
    MeasurableSet (superlevelSetLT f t) := hf measurableSet_Ioi
@[measurability] theorem measurableSet_superlevelSetLE {f : E → ℝ} (hf : Measurable f) (t : ℝ) :
    MeasurableSet (superlevelSetLE f t) := hf measurableSet_Ici
@[measurability] theorem measurableSet_levelSet {f : E → ℝ} (hf : Measurable f) (t : ℝ) :
    MeasurableSet (levelSet f t) := hf (measurableSet_singleton t)
theorem nullMeasurableSet_superlevelSetLT {f : E → ℝ} (hf : NullMeasurable f μ) (t : ℝ) :
    NullMeasurableSet (superlevelSetLT f t) μ := hf measurableSet_Ioi
theorem nullMeasurableSet_superlevelSetLE {f : E → ℝ} (hf : NullMeasurable f μ) (t : ℝ) :
    NullMeasurableSet (superlevelSetLE f t) μ := hf measurableSet_Ici
theorem nullMeasurableSet_levelSet {f : E → ℝ} (hf : NullMeasurable f μ) (t : ℝ) :
    NullMeasurableSet (levelSet f t) μ := hf (measurableSet_singleton t)
/-- **Countability of positive-measure level sets**. -/
theorem countable_measure_levelSet_pos₀ [SFinite μ] {f : E → ℝ} (hf : NullMeasurable f μ) :
    Set.Countable {t : ℝ | 0 < μ (levelSet f t)} := Measure.countable_meas_level_set_pos₀ hf
/-- `{t : ℝ | μ (levelSet f t) ≠ 0}` is countable for `μ`-null-measurable `f : E → ℝ`. -/
theorem countable_measure_levelSet_ne_zero₀ [SFinite μ] {f : E → ℝ} (hf : NullMeasurable f μ) :
    Set.Countable {t : ℝ | μ (levelSet f t) ≠ 0} := by
  simpa only [pos_iff_ne_zero] using countable_measure_levelSet_pos₀ hf
theorem countable_measure_levelSet_ne_zero [SFinite μ] {f : E → ℝ} (hf : Measurable f) :
    Set.Countable {t : ℝ | μ (levelSet f t) ≠ 0} :=
  countable_measure_levelSet_ne_zero₀ hf.nullMeasurable
/-- **Almost all level sets have measure zero**. -/
theorem ae_measure_levelSet_eq_zero₀ [SFinite μ] {f : E → ℝ} (hf : NullMeasurable f μ) :
    ∀ᵐ t : ℝ ∂volume, μ (levelSet f t) = 0 :=
  (countable_measure_levelSet_ne_zero₀ hf).measure_zero volume
theorem ae_measure_levelSet_eq_zero [SFinite μ] {f : E → ℝ} (hf : Measurable f) :
    ∀ᵐ t : ℝ ∂volume, μ (levelSet f t) = 0 := ae_measure_levelSet_eq_zero₀ hf.nullMeasurable
/-- Whenever `μ (levelSet f t) = 0`, `superlevelSetLT f t =ᵐ[μ] superlevelSetLE f t`. -/
theorem superlevelSetLT_ae_eq_superlevelSetLE_of_measure_levelSet_eq_zero {f : E → ℝ} {t : ℝ}
    (h0 : μ (levelSet f t) = 0) :
    superlevelSetLT f t =ᵐ[μ] superlevelSetLE f t := by
  rw [← superlevelSetLT_union_levelSet]
  exact (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr h0)).symm
/-- For `volume`-almost every `t : ℝ`, `superlevelSetLT f t =ᵐ[μ] superlevelSetLE f t`. -/
theorem ae_superlevelSetLT_ae_eq_superlevelSetLE [SFinite μ] {f : E → ℝ}
    (hf : NullMeasurable f μ) :
    ∀ᵐ t : ℝ ∂volume, superlevelSetLT f t =ᵐ[μ] superlevelSetLE f t := by
  filter_upwards [ae_measure_levelSet_eq_zero₀ hf] with t ht
  exact superlevelSetLT_ae_eq_superlevelSetLE_of_measure_levelSet_eq_zero ht

end MeasureLevelSets

end RegularLevelTopology

/-! ### Section 3: Regular-Level Coarea, Mean-Value Selection, and Smooth Superlevel Bounds -/

section RegularLevelCoareaAndSelection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E} {Ω : Opens E}

/-- Equal relative perimeter of `{t < f}` and `{t ≤ f}` when `μ.restrict Ω (levelSet f t) = 0`. -/
theorem relativePerimeter_superlevelSetLT_eq_superlevelSetLE_of_measure_levelSet_eq_zero
    {f : E → ℝ} {t : ℝ} (h0 : μ.restrict Ω (levelSet f t) = 0) :
    relativePerimeter μ Ω (superlevelSetLT f t) =
      relativePerimeter μ Ω (superlevelSetLE f t) :=
  relativePerimeter_congr_ae (superlevelSetLT_ae_eq_superlevelSetLE_of_measure_levelSet_eq_zero h0)
/-- Equal perimeter of `superlevelSetLT` and `superlevelSetLE` when `μ (levelSet f t) = 0`. -/
theorem perimeter_superlevelSetLT_eq_superlevelSetLE_of_measure_levelSet_eq_zero
    {f : E → ℝ} {t : ℝ} (h0 : μ (levelSet f t) = 0) :
    perimeter μ (superlevelSetLT f t) = perimeter μ (superlevelSetLE f t) :=
  perimeter_congr_ae (superlevelSetLT_ae_eq_superlevelSetLE_of_measure_levelSet_eq_zero h0)
/-- Almost everywhere in `t`, `{t < f}` and `{t ≤ f}` have equal relative perimeter in `Ω`. -/
theorem ae_relativePerimeter_superlevelSetLT_eq_superlevelSetLE [SFinite μ] {f : E → ℝ}
    (hf : NullMeasurable f (μ.restrict Ω)) :
    ∀ᵐ t : ℝ ∂volume, relativePerimeter μ Ω (superlevelSetLT f t) =
      relativePerimeter μ Ω (superlevelSetLE f t) := by
  filter_upwards [ae_measure_levelSet_eq_zero₀ hf] with t ht
  exact relativePerimeter_superlevelSetLT_eq_superlevelSetLE_of_measure_levelSet_eq_zero ht
/-- Almost everywhere in `t`, `superlevelSetLT` and `superlevelSetLE` have equal perimeter. -/
theorem ae_perimeter_superlevelSetLT_eq_superlevelSetLE [SFinite μ] {f : E → ℝ}
    (hf : NullMeasurable f μ) :
    ∀ᵐ t : ℝ ∂volume, perimeter μ (superlevelSetLT f t) = perimeter μ (superlevelSetLE f t) := by
  filter_upwards [ae_measure_levelSet_eq_zero₀ hf] with t ht
  exact perimeter_superlevelSetLT_eq_superlevelSetLE_of_measure_levelSet_eq_zero ht
/-- Equal coarea integrals for `superlevelSetLT` and `superlevelSetLE`. -/
theorem lintegral_relativePerimeter_superlevelSetLT_eq_superlevelSetLE [SFinite μ] {f : E → ℝ}
    (hf : NullMeasurable f (μ.restrict Ω)) :
    ∫⁻ t : ℝ, relativePerimeter μ Ω (superlevelSetLT f t) =
      ∫⁻ t : ℝ, relativePerimeter μ Ω (superlevelSetLE f t) :=
  lintegral_congr_ae (ae_relativePerimeter_superlevelSetLT_eq_superlevelSetLE hf)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] in
/-- For `x ∉ levelSet f t`, `s ↦ (superlevelSetLT f s).indicator 1 x` is locally constant at `t`. -/
theorem eventuallyEq_indicator_superlevelSetLT_nhds_of_notMem_levelSet {f : E → ℝ} {t : ℝ}
    {x : E} (hx : x ∉ levelSet f t) :
    (fun s : ℝ ↦ (superlevelSetLT f s).indicator (fun _ ↦ (1 : ℝ)) x) =ᶠ[𝓝 t]
      fun _ ↦ (superlevelSetLT f t).indicator (fun _ ↦ (1 : ℝ)) x := by
  change f x ≠ t at hx
  rcases hx.lt_or_gt with hlt | hgt
  · filter_upwards [Ioi_mem_nhds hlt] with s (hs : f x < s)
    simp [superlevelSetLT, not_lt.mpr hlt.le, not_lt.mpr hs.le]
  · filter_upwards [Iio_mem_nhds hgt] with s (hs : s < f x)
    simp [superlevelSetLT, hgt, hs]
/-- Any `P : ℝ → ℝ≥0∞` lower semicontinuous outside a countable set `C` is Borel measurable. -/
theorem measurable_of_lowerSemicontinuousAt_compl_countable {P : ℝ → ℝ≥0∞} {C : Set ℝ}
    (hC : C.Countable) (hlsc : ∀ t ∉ C, LowerSemicontinuousAt P t) :
    Measurable P := by
  refine measurable_of_Ioi fun a ↦ ?_
  let U : Set ℝ := P ⁻¹' Set.Ioi a
  have hsub : U \ interior U ⊆ C := by
    intro t ⟨htU, htnint⟩; by_contra htC
    exact htnint (mem_interior_iff_mem_nhds.mpr (hlsc t htC a htU))
  change MeasurableSet U
  rw [← Set.union_sdiff_cancel (interior_subset (s := U))]
  exact isOpen_interior.measurableSet.union (hC.mono hsub).measurableSet

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- Continuity of `s ↦ ∫ x in Ω, (superlevelSetLT f s).indicator 1 x * divergence φ x ∂μ` at `t`. -/
theorem tendsto_integral_superlevelSetLT_mul_divergence [IsFiniteMeasureOnCompacts μ]
    {f : E → ℝ} (hf : NullMeasurable f (μ.restrict Ω)) {t : ℝ}
    (ht : μ.restrict Ω (levelSet f t) = 0) (φ : 𝓓(Ω, E)) :
    Tendsto
      (fun s : ℝ ↦ ∫ x in (Ω : Set E),
        (superlevelSetLT f s).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ)
      (𝓝 t)
      (𝓝 (∫ x in (Ω : Set E),
        (superlevelSetLT f t).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ)) := by
  have hdiv_int : IntegrableOn (fun x ↦ ‖divergence (φ : E → E) x‖) Ω μ :=
    (integrableOn_divergence_testFunction (μ := μ) φ).norm
  have hdiv_aesm : AEStronglyMeasurable (fun x ↦ divergence (φ : E → E) x) (μ.restrict Ω) :=
    (continuous_divergence_testFunction φ).aestronglyMeasurable
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ ‖divergence (φ : E → E) x‖) ?_ ?_ hdiv_int ?_
  · refine Eventually.of_forall fun s ↦ ?_
    have h_ind : AEStronglyMeasurable
        ((superlevelSetLT f s).indicator (fun _ ↦ (1 : ℝ))) (μ.restrict Ω) :=
      (aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀
        (nullMeasurableSet_superlevelSetLT hf s)
    exact h_ind.mul hdiv_aesm
  · refine Eventually.of_forall fun s ↦ ae_of_all _ fun x ↦ ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (by by_cases hx : x ∈ superlevelSetLT f s <;> simp [hx])
  · filter_upwards [compl_mem_ae_iff.mpr ht] with x hx
    exact ((eventuallyEq_indicator_superlevelSetLT_nhds_of_notMem_levelSet hx).fun_mul
      EventuallyEq.rfl).tendsto
/-- **Lower semicontinuity of the superlevel relative perimeter** at every level `t . -/
theorem lowerSemicontinuousAt_relativePerimeter_superlevelSetLT [IsFiniteMeasureOnCompacts μ]
    {f : E → ℝ} (hf : NullMeasurable f (μ.restrict Ω)) {t : ℝ}
    (ht : μ.restrict Ω (levelSet f t) = 0) :
    LowerSemicontinuousAt (fun s : ℝ ↦ relativePerimeter μ Ω (superlevelSetLT f s)) t := by
  intro y hy
  simp only [relativePerimeter, distributionalVariation, lt_iSup_iff] at hy
  obtain ⟨φ, hφ, hyφ⟩ := hy
  have hcont := (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_integral_superlevelSetLT_mul_divergence hf ht φ)
  filter_upwards [hcont.eventually (Ioi_mem_nhds hyφ)] with s hs
  exact hs.trans_le (le_distributionalVariation φ hφ _)
/-- **Unconditional Borel measurability of `t ↦ relativePerimeter μ Ω (superlevelSetLT f t)`**. -/
@[fun_prop] theorem measurable_relativePerimeter_superlevelSetLT
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] {f : E → ℝ}
    (hf : NullMeasurable f (μ.restrict Ω)) :
    Measurable (fun t : ℝ ↦ relativePerimeter μ Ω (superlevelSetLT f t)) :=
  measurable_of_lowerSemicontinuousAt_compl_countable
    (countable_measure_levelSet_ne_zero₀ hf)
    fun _ ht ↦ lowerSemicontinuousAt_relativePerimeter_superlevelSetLT hf (not_not.mp ht)
/-- **Unconditional Borel measurability of `t ↦ perimeter μ (superlevelSetLT f t)`**. -/
@[fun_prop] theorem measurable_perimeter_superlevelSetLT
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] {f : E → ℝ} (hf : NullMeasurable f μ) :
    Measurable (fun t : ℝ ↦ perimeter μ (superlevelSetLT f t)) :=
  measurable_relativePerimeter_superlevelSetLT (by simpa using hf)
/-- `t ↦ relativePerimeter μ Ω (superlevelSetLE f t)` is `volume`-a.e. measurable. -/
theorem aemeasurable_relativePerimeter_superlevelSetLE
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] {f : E → ℝ}
    (hf : NullMeasurable f (μ.restrict Ω)) :
    AEMeasurable (fun t : ℝ ↦ relativePerimeter μ Ω (superlevelSetLE f t)) volume :=
  (measurable_relativePerimeter_superlevelSetLT hf).aemeasurable.congr
    (ae_relativePerimeter_superlevelSetLT_eq_superlevelSetLE hf)
/-- Unconditional a.e. finite relative perimeter of `superlevelSetLT f t` from finite coarea. -/
theorem ae_hasFinitePerimeterIn_superlevelSetLT
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] {f : E → ℝ}
    (hf : NullMeasurable f (μ.restrict Ω))
    (hper : ∫⁻ t : ℝ, relativePerimeter μ Ω (superlevelSetLT f t) < ⊤) :
    ∀ᵐ t : ℝ ∂volume, HasFinitePerimeterIn μ Ω (superlevelSetLT f t) :=
  ae_hasFinitePerimeterIn_superlevel_real hf
    (measurable_relativePerimeter_superlevelSetLT hf).aemeasurable hper
/-- Whole-space specialization of `ae_hasFinitePerimeterIn_superlevelSetLT`. -/
theorem ae_hasFinitePerimeter_superlevelSetLT
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] {f : E → ℝ} (hf : NullMeasurable f μ)
    (hper : ∫⁻ t : ℝ, perimeter μ (superlevelSetLT f t) < ⊤) :
    ∀ᵐ t : ℝ ∂volume, HasFinitePerimeter μ (superlevelSetLT f t) :=
  ae_hasFinitePerimeterIn_superlevelSetLT (by simpa using hf) hper
omit [MeasurableSpace E] [BorelSpace E] in
/-- **Integrating over `scalarRegularValues f` equals integrating over `ℝ`** for `C∞` `f`. -/
theorem setLIntegral_scalarRegularValues_eq_lintegral {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in scalarRegularValues f, g t = ∫⁻ t : ℝ, g t := by
  have hrestrict : volume.restrict (scalarRegularValues f) = volume :=
    Measure.ext fun s hs ↦ by rw [Measure.restrict_apply hs, volume_inter_scalarRegularValues hf s]
  rw [hrestrict]
omit [MeasurableSpace E] [BorelSpace E] in
/-- Integrating over `S ∩ scalarRegularValues f` equals integrating over `S` for `C∞` `f`. -/
theorem setLIntegral_inter_scalarRegularValues_eq {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (S : Set ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in S ∩ scalarRegularValues f, g t = ∫⁻ t in S, g t := by
  have hrestrict : volume.restrict (S ∩ scalarRegularValues f) = volume.restrict S :=
    Measure.ext fun A hA ↦ by
      rw [Measure.restrict_apply hA, Measure.restrict_apply hA, ← Set.inter_assoc,
        volume_inter_scalarRegularValues hf (A ∩ S)]
  rw [hrestrict]
omit [BorelSpace E] in
/-- **Regular-level coarea identity for superlevel relative perimeter**. -/
theorem setLIntegral_scalarRegularValues_relativePerimeter_superlevelSetLT
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∫⁻ t in scalarRegularValues f, relativePerimeter μ Ω (superlevelSetLT f t) =
      ∫⁻ t : ℝ, relativePerimeter μ Ω (superlevelSetLT f t) :=
  setLIntegral_scalarRegularValues_eq_lintegral hf _
omit [BorelSpace E] in
/-- Whole-space specialization to `perimeter μ (superlevelSetLT f t)`. -/
theorem setLIntegral_scalarRegularValues_perimeter_superlevelSetLT
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∫⁻ t in scalarRegularValues f, perimeter μ (superlevelSetLT f t) =
      ∫⁻ t : ℝ, perimeter μ (superlevelSetLT f t) :=
  setLIntegral_scalarRegularValues_eq_lintegral hf _
/-- **Smooth BV coarea inequality restricted to regular values**. -/
theorem distributionalVariation_le_setLIntegral_scalarRegularValues_relativePerimeter
    [μ.IsAddHaarMeasure] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    distributionalVariation μ Ω f ≤
      ∫⁻ t in scalarRegularValues f, relativePerimeter μ Ω (superlevelSetLT f t) := by
  rw [setLIntegral_scalarRegularValues_relativePerimeter_superlevelSetLT hf]
  exact distributionalVariation_le_lintegral_relativePerimeter_real
    (hf.continuous.locallyIntegrable.locallyIntegrableOn Ω)
/-- **Truncated smooth BV coarea inequality restricted to regular values in `Set.Ioo a b`**. -/
theorem distributionalVariation_min_max_le_setLIntegral_Ioo_inter_scalarRegularValues
    [μ.IsAddHaarMeasure] {a b : ℝ} (hab : a ≤ b) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    distributionalVariation μ Ω (fun x ↦ min (max (f x) a) b) ≤
      ∫⁻ t in Set.Ioo a b ∩ scalarRegularValues f,
        relativePerimeter μ Ω (superlevelSetLT f t) := by
  rw [setLIntegral_inter_scalarRegularValues_eq hf]
  exact distributionalVariation_min_max_le_lintegral_relativePerimeter hab
    hf.continuous.aestronglyMeasurable
/-- **Mean-value / Chebyshev selection on `S` with a `ν`-a.e. side condition `P`**. -/
theorem exists_mul_le_setLIntegral_of_ae {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {S : Set α} (hSm : MeasurableSet S) (hS0 : 0 < ν S) (hStop : ν S ≠ ⊤)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g (ν.restrict S)) {P : α → Prop}
    (hP : ∀ᵐ t ∂ν, t ∈ S → P t) :
    ∃ t ∈ S, P t ∧ ν S * g t ≤ ∫⁻ s in S, g s ∂ν := by
  have hSP_ae : ({t ∈ S | P t} : Set α) =ᵐ[ν] S := by
    filter_upwards [hP] with t ht; exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, ht h⟩⟩
  have hSP_pos : 0 < ν {t ∈ S | P t} := by rwa [measure_congr hSP_ae]
  obtain ⟨t₀, ht₀S, ht₀P⟩ := nonempty_of_measure_ne_zero hSP_pos.ne'
  rcases eq_top_or_lt_top (∫⁻ s in S, g s ∂ν) with htop | hfin
  · exact ⟨t₀, ht₀S, ht₀P, htop ▸ le_top⟩
  · by_contra! hlt
    let c : ℝ≥0∞ := (∫⁻ s in S, g s ∂ν) / ν S
    have hc_mul : c * ν S = ∫⁻ s in S, g s ∂ν := ENNReal.div_mul_cancel hS0.ne' hStop
    have hc_int : ∫⁻ _ in S, c ∂ν = ∫⁻ s in S, g s ∂ν := by rw [setLIntegral_const, hc_mul]
    have hlt_ae : ∀ᵐ t ∂ν.restrict S, c < g t := by
      rw [ae_restrict_iff' hSm]
      filter_upwards [hP] with t ht htS
      have ht_ineq := hlt t htS (ht htS)
      rw [← hc_mul, mul_comm (ν S) (g t)] at ht_ineq
      exact lt_of_mul_lt_mul_right ht_ineq zero_le
    have hνS_ne : ν.restrict S ≠ 0 := by simp [hS0.ne']
    exact (lintegral_strict_mono hνS_ne hg (hc_int.trans_lt hfin).ne hlt_ae).ne hc_int
/-- **Regular-level mean-value selection theorem for relative perimeter**. -/
theorem exists_regularValue_mem_Ioo_relativePerimeter_le
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, t ∈ scalarRegularValues f ∧ μ (levelSet f t) = 0 ∧
      IsRegularOpen (superlevelSetLT f t) ∧ frontier (superlevelSetLT f t) = levelSet f t ∧
      ENNReal.ofReal (b - a) * relativePerimeter μ Ω (superlevelSetLT f t) ≤
        ∫⁻ s in Set.Ioo a b, relativePerimeter μ Ω (superlevelSetLT f s) := by
  have hIoo_pos : 0 < volume (Set.Ioo a b) := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  have hIoo_top : volume (Set.Ioo a b) ≠ ⊤ := by simp [Real.volume_Ioo]
  have hP : ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo a b →
      t ∈ scalarRegularValues f ∧ μ (levelSet f t) = 0 := by
    filter_upwards [ae_mem_scalarRegularValues hf,
      ae_measure_levelSet_eq_zero (μ := μ) hf.continuous.measurable] with t ht₁ ht₂ _
    exact ⟨ht₁, ht₂⟩
  have hg : AEMeasurable (fun s : ℝ ↦ relativePerimeter μ Ω (superlevelSetLT f s))
      (volume.restrict (Set.Ioo a b)) :=
    (measurable_relativePerimeter_superlevelSetLT
      hf.continuous.measurable.nullMeasurable).aemeasurable
  obtain ⟨t, htIoo, ⟨htReg, htNull⟩, htBound⟩ :=
    exists_mul_le_setLIntegral_of_ae measurableSet_Ioo hIoo_pos hIoo_top hg hP
  rw [Real.volume_Ioo] at htBound
  exact ⟨t, htIoo, htReg, htNull, isRegularOpen_superlevelSetLT hf.continuous htReg,
    frontier_superlevelSetLT_eq_levelSet hf.continuous htReg, htBound⟩
/-- **Regular-level mean-value selection theorem for whole-space perimeter**. -/
theorem exists_regularValue_mem_Ioo_perimeter_le
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, t ∈ scalarRegularValues f ∧ μ (levelSet f t) = 0 ∧
      IsRegularOpen (superlevelSetLT f t) ∧ frontier (superlevelSetLT f t) = levelSet f t ∧
      ENNReal.ofReal (b - a) * perimeter μ (superlevelSetLT f t) ≤
        ∫⁻ s in Set.Ioo a b, perimeter μ (superlevelSetLT f s) :=
  exists_regularValue_mem_Ioo_relativePerimeter_le (μ := μ) (Ω := ⊤) hf hab
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Pointwise symmetric-difference inclusion for superlevel sets**. -/
theorem symmDiff_superlevelSetLT_subset (s : Set E) (f : E → ℝ) (t : ℝ) : s ∆ superlevelSetLT f t ⊆
      {x : E | min t (1 - t) ≤ |f x - s.indicator (fun _ ↦ (1 : ℝ)) x|} := by
  intro x hx
  rcases hx with ⟨hxs, hxlt⟩ | ⟨hxlt, hxs⟩
  · have hle : f x ≤ t := not_lt.mp hxlt
    simp only [Set.mem_ofPred_eq, Set.indicator_of_mem hxs]
    exact (min_le_right t (1 - t)).trans (by linarith [neg_le_abs (f x - 1)])
  · have hgt : t < f x := hxlt
    simp only [Set.mem_ofPred_eq, Set.indicator_of_notMem hxs, sub_zero]
    exact (min_le_left t (1 - t)).trans (hgt.le.trans (le_abs_self (f x)))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Markov `L¹` bound on `μ (s ∆ superlevelSetLT f t)`**. -/
theorem mul_measure_symmDiff_superlevelSetLT_le_lintegral_abs_sub
    {s : Set E} (hs : NullMeasurableSet s μ) {f : E → ℝ} (hf : NullMeasurable f μ) (t : ℝ) :
    ENNReal.ofReal (min t (1 - t)) * μ (s ∆ superlevelSetLT f t) ≤
      ∫⁻ x, ENNReal.ofReal |f x - s.indicator (fun _ ↦ (1 : ℝ)) x| ∂μ := by
  have hae : AEMeasurable
      (fun x ↦ ENNReal.ofReal |f x - s.indicator (fun _ ↦ (1 : ℝ)) x|) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable
        (hf.aemeasurable.sub (measurable_const.aemeasurable.indicator₀ hs)))
  have hsub : s ∆ superlevelSetLT f t ⊆
      {x : E | ENNReal.ofReal (min t (1 - t)) ≤
        ENNReal.ofReal |f x - s.indicator (fun _ ↦ (1 : ℝ)) x|} :=
    fun x hx ↦ ENNReal.ofReal_le_ofReal (symmDiff_superlevelSetLT_subset s f t hx)
  exact (mul_le_mul' le_rfl (measure_mono (μ := μ) hsub)).trans (mul_meas_ge_le_lintegral₀ hae _)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Division form of `mul_measure_symmDiff_superlevelSetLT_le_lintegral_abs_sub` (`t ∈ Ioo 0 1`). -/
theorem measure_symmDiff_superlevelSetLT_le_lintegral_div
    {s : Set E} (hs : NullMeasurableSet s μ) {f : E → ℝ} (hf : NullMeasurable f μ)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    μ (s ∆ superlevelSetLT f t) ≤
      (∫⁻ x, ENNReal.ofReal |f x - s.indicator (fun _ ↦ (1 : ℝ)) x| ∂μ) /
        ENNReal.ofReal (min t (1 - t)) := by
  have hpos : 0 < min t (1 - t) := lt_min ht.1 (sub_pos.mpr ht.2)
  have hc0 : ENNReal.ofReal (min t (1 - t)) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpos
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact mul_measure_symmDiff_superlevelSetLT_le_lintegral_abs_sub hs hf t
/-- **Simultaneous regular-level selection for `L¹` distance and relative perimeter**. -/
theorem exists_regularValue_mem_Ioo_symmDiff_and_relativePerimeter_le
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] {s : Set E} (hs : NullMeasurableSet s μ)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, t ∈ scalarRegularValues f ∧ μ (levelSet f t) = 0 ∧
      IsRegularOpen (superlevelSetLT f t) ∧ frontier (superlevelSetLT f t) = levelSet f t ∧
      ENNReal.ofReal (min a (1 - b)) * μ (s ∆ superlevelSetLT f t) ≤
        ∫⁻ x, ENNReal.ofReal |f x - s.indicator (fun _ ↦ (1 : ℝ)) x| ∂μ ∧
      ENNReal.ofReal (b - a) * relativePerimeter μ Ω (superlevelSetLT f t) ≤
        ∫⁻ r in Set.Ioo a b, relativePerimeter μ Ω (superlevelSetLT f r) := by
  obtain ⟨t, htIoo, htReg, htNull, htOpen, htFront, htPer⟩ :=
    exists_regularValue_mem_Ioo_relativePerimeter_le (μ := μ) (Ω := Ω) hf hab
  have hmin : min a (1 - b) ≤ min t (1 - t) :=
    min_le_min htIoo.1.le (sub_le_sub_left htIoo.2.le 1)
  have hL1 : ENNReal.ofReal (min a (1 - b)) * μ (s ∆ superlevelSetLT f t) ≤
      ∫⁻ x, ENNReal.ofReal |f x - s.indicator (fun _ ↦ (1 : ℝ)) x| ∂μ :=
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hmin) le_rfl).trans
      (mul_measure_symmDiff_superlevelSetLT_le_lintegral_abs_sub
        hs hf.continuous.measurable.nullMeasurable t)
  exact ⟨t, htIoo, htReg, htNull, htOpen, htFront, hL1, htPer⟩
/-- Whole-space specialization to `perimeter μ (superlevelSetLT f t)`. -/
theorem exists_regularValue_mem_Ioo_symmDiff_and_perimeter_le
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] {s : Set E} (hs : NullMeasurableSet s μ)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, t ∈ scalarRegularValues f ∧ μ (levelSet f t) = 0 ∧
      IsRegularOpen (superlevelSetLT f t) ∧ frontier (superlevelSetLT f t) = levelSet f t ∧
      ENNReal.ofReal (min a (1 - b)) * μ (s ∆ superlevelSetLT f t) ≤
        ∫⁻ x, ENNReal.ofReal |f x - s.indicator (fun _ ↦ (1 : ℝ)) x| ∂μ ∧
      ENNReal.ofReal (b - a) * perimeter μ (superlevelSetLT f t) ≤
        ∫⁻ r in Set.Ioo a b, perimeter μ (superlevelSetLT f r) :=
  exists_regularValue_mem_Ioo_symmDiff_and_relativePerimeter_le (μ := μ) (Ω := ⊤) hs hf hab

end RegularLevelCoareaAndSelection

end TauCeti
