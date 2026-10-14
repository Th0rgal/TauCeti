/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IsoperimetricDomains
public import TauCeti.MeasureTheory.Measure.Lebesgue.SteinerProperties
import all TauCeti.MeasureTheory.Measure.ConvexIsoperimetry
import all TauCeti.MeasureTheory.Measure.EssentialBoundary
import all TauCeti.MeasureTheory.Measure.IsoperimetricDomains
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerProperties
import all TauCeti.MeasureTheory.Measure.Lebesgue.SteinerSymmetrization
import all TauCeti.MeasureTheory.Measure.OneDimIsoperimetry
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterSlicing

/-!
# Orthogonal Hyperplane Slice Transport, Interval Slices, and Essential Convexity

For a unit vector `e` in a finite-dimensional real inner product space `E`, this file connects the
measure-preserving orthogonal hyperplane decomposition `(ℝ ∙ e)ᗮ × ℝ ≃ᵐ E`, one-dimensional line
sections `lineSection e A y = {t : ℝ | (y : E) + t • e ∈ A}`, almost-everywhere order-connected
slices (`IsAEOrdConnected`, `HasIntervalSlicesInDirection`, `HasIntervalSlicesEverywhere`), and
essential convexity (`IsEssentiallyConvex`):
1. **Orthogonal hyperplane decomposition and Fubini slice transport**: Pythagorean norm identity,
   explicit orthogonal-projection inverse, measure-preserving splitting, Fubini volume and
   symmetric-difference identities for `lineSection`, and a.e. slice invariance under null changes.
2. **Almost-everywhere interval (`OrdConnected`) slices and Steiner perimeter equality**:
   `IsAEOrdConnected`, 1D perimeter characterization (`perimeter = 2` / `< 4`), `=ᵐ[volume]`
   invariance of `HasIntervalSlicesInDirection` and `HasIntervalSlicesEverywhere`, interval slices
   of convex sets, and deduction of interval slices from Steiner perimeter equality.
3. **Essential convexity, boundedness of finite-volume convex sets, and compact convex bodies**:
   segment density-1 propagation and convexity of `essentialInterior volume A`, equivalence between
   `IsEssentiallyConvex`, `HasIntervalSlicesEverywhere`, and `Convex ℝ (essentialInterior volume A)`
   for null-measurable sets, boundedness of positive-finite-volume convex sets, and reduction to a
   compact convex representative `K = closure C` with `(interior K).Nonempty`, `A =ᵐ[volume] K`,
   `volume K = volume A`, and `perimeter volume K = perimeter volume A`.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set Submodule
open TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal symmDiff InnerProductSpace Topology

namespace TauCeti

/-! ### Section 1: Orthogonal hyperplane decomposition and Fubini slice transport -/

section OrthogonalSliceTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Pythagorean norm-squared identity** for `(y : E) + t • e` with `y : (ℝ ∙ e)ᗮ` and `‖e‖ = 1`.
-/
theorem norm_coe_orthogonal_add_smul_sq {e : E} (he : ‖e‖ = 1) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    ‖(y : E) + t • e‖ ^ 2 = ‖(y : E)‖ ^ 2 + t ^ 2 :=
  norm_coe_add_smul_sq he y t

/-- **Pythagorean norm identity** `‖(y : E) + t • e‖ = √(‖y‖ ^ 2 + t ^ 2)` for `y : (ℝ ∙ e)ᗮ` and
`‖e‖ = 1`. -/
theorem norm_coe_orthogonal_add_smul {e : E} (he : ‖e‖ = 1) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    ‖(y : E) + t • e‖ = √(‖(y : E)‖ ^ 2 + t ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_coe_orthogonal_add_smul_sq he]

/-- **Orthogonal hyperplane decomposition reconstruction**
`((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x : E) + ⟪x, e⟫_ℝ • e = x` for a unit vector `e`. -/
theorem orthogonalProjectionOnto_add_inner_smul {e : E} (he : ‖e‖ = 1) (x : E) :
    ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x : E) + ⟪x, e⟫_ℝ • e = x :=
  orthogonalProjection_orthogonalHyperplane_add_inner_smul he x

/-- First coordinate recovery for `(y : E) + t • e` with `y : (ℝ ∙ e)ᗮ`. -/
@[simp] theorem orthogonalProjectionOnto_coe_add_smul (e : E) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    (ℝ ∙ e)ᗮ.orthogonalProjectionOnto ((y : E) + t • e) = y :=
  orthogonalProjectionOnto_orthogonalHyperplane_add_smul e y t

/-- Second coordinate recovery `⟪(y : E) + t • e, e⟫_ℝ = t` for `y : (ℝ ∙ e)ᗮ` and `‖e‖ = 1`. -/
@[simp] theorem inner_coe_orthogonal_add_smul_self {e : E} (he : ‖e‖ = 1) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    ⟪(y : E) + t • e, e⟫_ℝ = t :=
  inner_coe_add_smul_self he y t

/-- **One-dimensional line section** of `A : Set E` in direction `e : E` over `y : (ℝ ∙ e)ᗮ`:
`lineSection e A y = {t : ℝ | (y : E) + t • e ∈ A}`. -/
def lineSection (e : E) (A : Set E) (y : (ℝ ∙ e)ᗮ) : Set ℝ :=
  {t : ℝ | (y : E) + t • e ∈ A}

@[simp] theorem mem_lineSection_iff {e : E} {A : Set E} {y : (ℝ ∙ e)ᗮ} {t : ℝ} :
    t ∈ lineSection e A y ↔ (y : E) + t • e ∈ A := Iff.rfl
@[simp] theorem lineSection_empty (e : E) (y : (ℝ ∙ e)ᗮ) : lineSection e (∅ : Set E) y = ∅ := rfl
@[simp] theorem lineSection_univ (e : E) (y : (ℝ ∙ e)ᗮ) :
    lineSection e (Set.univ : Set E) y = Set.univ := rfl

theorem lineSection_mono {e : E} {A B : Set E} (hAB : A ⊆ B) (y : (ℝ ∙ e)ᗮ) :
    lineSection e A y ⊆ lineSection e B y := fun _ ht ↦ hAB ht

@[simp] theorem lineSection_inter (e : E) (A B : Set E) (y : (ℝ ∙ e)ᗮ) :
    lineSection e (A ∩ B) y = lineSection e A y ∩ lineSection e B y := rfl
@[simp] theorem lineSection_union (e : E) (A B : Set E) (y : (ℝ ∙ e)ᗮ) :
    lineSection e (A ∪ B) y = lineSection e A y ∪ lineSection e B y := rfl
@[simp] theorem lineSection_sdiff (e : E) (A B : Set E) (y : (ℝ ∙ e)ᗮ) :
    lineSection e (A \ B) y = lineSection e A y \ lineSection e B y := rfl
@[simp] theorem lineSection_compl (e : E) (A : Set E) (y : (ℝ ∙ e)ᗮ) :
    lineSection e Aᶜ y = (lineSection e A y)ᶜ := rfl
@[simp] theorem lineSection_symmDiff (e : E) (A B : Set E) (y : (ℝ ∙ e)ᗮ) :
    lineSection e (symmDiff A B) y = symmDiff (lineSection e A y) (lineSection e B y) := rfl

@[simp] theorem lineSection_steinerSymmetrization {e : E} (he : ‖e‖ = 1) (A : Set E)
    (y : (ℝ ∙ e)ᗮ) :
    lineSection e (steinerSymmetrization e A) y = symmetricInterval (lineSection e A y) :=
  steinerFiber_steinerSymmetrization he A y

theorem volume_lineSection_steinerSymmetrization {e : E} (he : ‖e‖ = 1) (A : Set E)
    (y : (ℝ ∙ e)ᗮ) :
    volume (lineSection e (steinerSymmetrization e A) y) = volume (lineSection e A y) :=
  volume_steinerFiber_steinerSymmetrization he A y

/-- **Every convex set `K ⊆ E` has order-connected 1D line sections in every direction**. -/
theorem _root_.Convex.ordConnected_lineSection {K : Set E} (hK : Convex ℝ K) (e : E)
    (y : (ℝ ∙ e)ᗮ) : (lineSection e K y).OrdConnected :=
  hK.ordConnected_steinerFiber e y

variable [MeasurableSpace E] [BorelSpace E]

@[measurability] theorem measurableSet_lineSection {e : E} {A : Set E} (hA : MeasurableSet A)
    (y : (ℝ ∙ e)ᗮ) : MeasurableSet (lineSection e A y) :=
  measurableSet_steinerFiber hA y

@[fun_prop] theorem measurable_volume_lineSection {e : E} {A : Set E} (hA : MeasurableSet A) :
    Measurable fun y : (ℝ ∙ e)ᗮ ↦ volume (lineSection e A y) :=
  measurable_volume_steinerFiber hA

variable [FiniteDimensional ℝ E]

/-- **Measure-preserving property of the orthogonal hyperplane splitting**
`(y, t) ↦ (y : E) + t • e` when `‖e‖ = 1`. -/
theorem measurePreserving_orthogonalSubmoduleProd {e : E} (he : ‖e‖ = 1) :
    MeasurePreserving (fun p : (ℝ ∙ e)ᗮ × ℝ ↦ (p.1 : E) + p.2 • e)
      ((volume : Measure (ℝ ∙ e)ᗮ).prod (volume : Measure ℝ)) (volume : Measure E) :=
  measurePreserving_orthogonalHyperplaneProd he

/-- **Fubini volume identity for `lineSection` on measurable sets**. -/
theorem volume_eq_lintegral_lineSection {e : E} (he : ‖e‖ = 1) {A : Set E} (hA : MeasurableSet A) :
    volume A = ∫⁻ y : (ℝ ∙ e)ᗮ, volume (lineSection e A y) ∂volume :=
  volume_eq_lintegral_steinerFiber he hA

/-- **Fubini volume identity for `lineSection` on null-measurable sets**. -/
theorem volume_eq_lintegral_lineSection₀ {e : E} (he : ‖e‖ = 1) {A : Set E}
    (hA : NullMeasurableSet A volume) :
    volume A = ∫⁻ y : (ℝ ∙ e)ᗮ, volume (lineSection e A y) ∂volume :=
  volume_eq_lintegral_steinerFiber₀ he hA

/-- **Fubini symmetric-difference identity for `lineSection`** on null-measurable sets `A, B`. -/
theorem volume_symmDiff_eq_lintegral_lineSection₀ {e : E} (he : ‖e‖ = 1) {A B : Set E}
    (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume) :
    volume (symmDiff A B) =
      ∫⁻ y : (ℝ ∙ e)ᗮ, volume (symmDiff (lineSection e A y) (lineSection e B y)) ∂volume :=
  volume_eq_lintegral_lineSection₀ he (hA.symmDiff hB)

/-- **Fubini a.e. slice invariance**: if `A =ᵐ[volume] B`, then `lineSection e A y =ᵐ[volume]
lineSection e B y` for a.e. `y : (ℝ ∙ e)ᗮ`. -/
theorem ae_lineSection_ae_eq {e : E} (he : ‖e‖ = 1) {A B : Set E} (hAB : A =ᵐ[volume] B) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, lineSection e A y =ᵐ[volume] lineSection e B y :=
  ae_steinerFiber_ae_eq he hAB

/-- Symmetric-difference formulation of Fubini a.e. slice invariance. -/
theorem ae_volume_lineSection_symmDiff_eq_zero {e : E} (he : ‖e‖ = 1) {A B : Set E}
    (hAB : volume (symmDiff A B) = 0) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, volume (symmDiff (lineSection e A y) (lineSection e B y)) = 0 := by
  have hAB' : A =ᵐ[volume] B := by rwa [ae_eq_set, ← measure_union_null_iff, ← Set.symmDiff_def]
  filter_upwards [ae_lineSection_ae_eq he hAB'] with y hy
  rwa [Set.symmDiff_def, measure_union_null_iff, ← ae_eq_set]

/-- If `A =ᵐ[volume] B`, then `volume (lineSection e A y) = volume (lineSection e B y)` for a.e.
`y : (ℝ ∙ e)ᗮ`. -/
theorem ae_volume_lineSection_eq {e : E} (he : ‖e‖ = 1) {A B : Set E} (hAB : A =ᵐ[volume] B) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, volume (lineSection e A y) = volume (lineSection e B y) :=
  ae_volume_steinerFiber_eq he hAB

/-- If `A =ᵐ[volume] B`, then `perimeter volume (lineSection e A y) =
perimeter volume (lineSection e B y)` for a.e. `y : (ℝ ∙ e)ᗮ`. -/
theorem ae_perimeter_lineSection_eq {e : E} (he : ‖e‖ = 1) {A B : Set E} (hAB : A =ᵐ[volume] B) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      perimeter volume (lineSection e A y) = perimeter volume (lineSection e B y) :=
  ae_perimeter_steinerFiber_eq he hAB

/-- If `A : Set E` is null-measurable, then a.e. slice `lineSection e A y` is null-measurable. -/
theorem ae_nullMeasurableSet_lineSection {e : E} (he : ‖e‖ = 1) {A : Set E}
    (hA : NullMeasurableSet A volume) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, NullMeasurableSet (lineSection e A y) volume :=
  ae_nullMeasurableSet_steinerFiber he hA

/-- If `A : Set E` is null-measurable and `volume A < ⊤`, then a.e. slice `lineSection e A y` has
finite 1D measure. -/
theorem ae_volume_lineSection_lt_top {e : E} (he : ‖e‖ = 1) {A : Set E}
    (hA : NullMeasurableSet A volume) (htop : volume A < ⊤) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, volume (lineSection e A y) < ⊤ :=
  ae_volume_steinerFiber_lt_top he hA htop

end OrthogonalSliceTransport

/-! ### Section 2: Almost-everywhere interval slices and Steiner perimeter equality -/

section IntervalSlicesAndSteinerEquality

/-- **Almost-everywhere order-connected subset of `ℝ`**: `S : Set ℝ` differs from an `OrdConnected`
set `I : Set ℝ` (an interval) by a Lebesgue-null set. -/
def IsAEOrdConnected (S : Set ℝ) : Prop :=
  ∃ I : Set ℝ, I.OrdConnected ∧ (S =ᵐ[volume] I)

theorem IsAEOrdConnected.of_ordConnected {I : Set ℝ} (hI : I.OrdConnected) :
    IsAEOrdConnected I := ⟨I, hI, EventuallyEq.rfl⟩
theorem _root_.Convex.isAEOrdConnected {I : Set ℝ} (hI : Convex ℝ I) : IsAEOrdConnected I :=
  IsAEOrdConnected.of_ordConnected hI.ordConnected

theorem IsAEOrdConnected.mono_ae {S T : Set ℝ} (hS : IsAEOrdConnected S) (hST : S =ᵐ[volume] T) :
    IsAEOrdConnected T := by
  rcases hS with ⟨I, hI, hSI⟩; exact ⟨I, hI, hST.symm.trans hSI⟩

theorem IsAEOrdConnected.congr_ae {S T : Set ℝ} (hST : S =ᵐ[volume] T) :
    IsAEOrdConnected S ↔ IsAEOrdConnected T :=
  ⟨fun h ↦ h.mono_ae hST, fun h ↦ h.mono_ae hST.symm⟩

@[simp] theorem isAEOrdConnected_empty : IsAEOrdConnected ∅ :=
  IsAEOrdConnected.of_ordConnected ordConnected_empty
theorem IsAEOrdConnected.empty : IsAEOrdConnected ∅ := isAEOrdConnected_empty
@[simp] theorem isAEOrdConnected_univ : IsAEOrdConnected Set.univ :=
  IsAEOrdConnected.of_ordConnected ordConnected_univ
theorem IsAEOrdConnected.of_measure_zero {S : Set ℝ} (hS : volume S = 0) : IsAEOrdConnected S :=
  ⟨∅, ordConnected_empty, ae_eq_empty.2 hS⟩
@[simp] theorem isAEOrdConnected_symmetricInterval (S : Set ℝ) :
    IsAEOrdConnected (symmetricInterval S) :=
  IsAEOrdConnected.of_ordConnected (ordConnected_symmetricInterval S)

/-- **1D perimeter `< 4` criterion for `IsAEOrdConnected`**. -/
theorem IsAEOrdConnected.of_perimeter_lt_four {S : Set ℝ} (hS : NullMeasurableSet S volume)
    (hfin : volume S < ⊤) (hper : perimeter volume S < 4) : IsAEOrdConnected S :=
  exists_ordConnected_ae_eq_of_perimeter_lt_four hS hfin hper

/-- **1D perimeter `≤ 2` criterion for `IsAEOrdConnected`**. -/
theorem IsAEOrdConnected.of_perimeter_le_two {S : Set ℝ} (hS : NullMeasurableSet S volume)
    (hfin : volume S < ⊤) (hper : perimeter volume S ≤ 2) : IsAEOrdConnected S :=
  IsAEOrdConnected.of_perimeter_lt_four hS hfin (hper.trans_lt (by norm_num))

/-- If `IsAEOrdConnected S` and `volume S < ⊤`, then `perimeter volume S ≤ 2`. -/
theorem IsAEOrdConnected.perimeter_le_two {S : Set ℝ} (hS : IsAEOrdConnected S)
    (hfin : volume S < ⊤) : perimeter volume S ≤ 2 := by
  rcases hS with ⟨I, hI, hSI⟩
  have hIfin : volume I < ⊤ := (measure_congr hSI).symm ▸ hfin
  rw [perimeter_congr_ae hSI, perimeter_congr_ae (hI.ae_eq_Ioo_sInf_sSup hIfin)]
  by_cases hlt : sInf I < sSup I
  · rw [perimeter_Ioo hlt]
  · rw [Ioo_eq_empty hlt, perimeter_empty]; exact zero_le

/-- **Sharp 1D perimeter `= 2` characterization of `IsAEOrdConnected`**. -/
theorem perimeter_eq_two_iff_isAEOrdConnected {S : Set ℝ} (hS : NullMeasurableSet S volume)
    (hpos : 0 < volume S) (hfin : volume S < ⊤) :
    perimeter volume S = 2 ↔ IsAEOrdConnected S :=
  perimeter_eq_two_iff_exists_ordConnected_ae_eq hS hpos hfin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Almost-everywhere interval slices in direction `e`**: for `volume`-a.e. `y : (ℝ ∙ e)ᗮ`,
`IsAEOrdConnected (lineSection e A y)` holds. -/
def HasIntervalSlicesInDirection (e : E) (A : Set E) : Prop :=
  ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, IsAEOrdConnected (lineSection e A y)

/-- **Almost-everywhere interval slices in every unit direction** (`‖e‖ = 1`). -/
def HasIntervalSlicesEverywhere (A : Set E) : Prop :=
  ∀ e : E, ‖e‖ = 1 → HasIntervalSlicesInDirection e A

@[simp] theorem hasIntervalSlicesInDirection_empty (e : E) :
    HasIntervalSlicesInDirection e (∅ : Set E) :=
  Eventually.of_forall fun _ ↦ isAEOrdConnected_empty
@[simp] theorem hasIntervalSlicesEverywhere_empty : HasIntervalSlicesEverywhere (∅ : Set E) :=
  fun e _ ↦ hasIntervalSlicesInDirection_empty e
@[simp] theorem hasIntervalSlicesInDirection_univ (e : E) :
    HasIntervalSlicesInDirection e (Set.univ : Set E) :=
  Eventually.of_forall fun _ ↦ isAEOrdConnected_univ
@[simp] theorem hasIntervalSlicesEverywhere_univ : HasIntervalSlicesEverywhere (Set.univ : Set E) :=
  fun e _ ↦ hasIntervalSlicesInDirection_univ e

/-- **Every convex set `K ⊆ E` has interval slices in every direction `e`**. -/
theorem _root_.Convex.hasIntervalSlicesInDirection {K : Set E} (hK : Convex ℝ K) (e : E) :
    HasIntervalSlicesInDirection e K :=
  Eventually.of_forall fun y ↦ IsAEOrdConnected.of_ordConnected (hK.ordConnected_lineSection e y)

/-- **Every convex set `K ⊆ E` satisfies `HasIntervalSlicesEverywhere K`**. -/
theorem _root_.Convex.hasIntervalSlicesEverywhere {K : Set E} (hK : Convex ℝ K) :
    HasIntervalSlicesEverywhere K :=
  fun e _ ↦ hK.hasIntervalSlicesInDirection e

/-- For any unit vector `e`, `steinerSymmetrization e A` has interval slices in direction `e`. -/
theorem hasIntervalSlicesInDirection_steinerSymmetrization {e : E} (he : ‖e‖ = 1) (A : Set E) :
    HasIntervalSlicesInDirection e (steinerSymmetrization e A) := by
  refine Eventually.of_forall fun y ↦ ?_
  rw [lineSection_steinerSymmetrization he]; exact isAEOrdConnected_symmetricInterval _

/-- **A.e. invariance of `HasIntervalSlicesInDirection`**. -/
theorem HasIntervalSlicesInDirection.congr_ae {e : E} (he : ‖e‖ = 1) {A B : Set E}
    (hA : HasIntervalSlicesInDirection e A) (hAB : A =ᵐ[volume] B) :
    HasIntervalSlicesInDirection e B := by
  filter_upwards [hA, ae_lineSection_ae_eq he hAB] with y hy hABy using hy.mono_ae hABy

/-- **Two-way `=ᵐ[volume]` invariance of `HasIntervalSlicesInDirection`**. -/
theorem hasIntervalSlicesInDirection_congr_ae {e : E} (he : ‖e‖ = 1) {A B : Set E}
    (hAB : A =ᵐ[volume] B) :
    HasIntervalSlicesInDirection e A ↔ HasIntervalSlicesInDirection e B :=
  ⟨fun h ↦ h.congr_ae he hAB, fun h ↦ h.congr_ae he hAB.symm⟩

/-- **A.e. invariance of `HasIntervalSlicesEverywhere`**. -/
theorem HasIntervalSlicesEverywhere.congr_ae {A B : Set E}
    (hA : HasIntervalSlicesEverywhere A) (hAB : A =ᵐ[volume] B) :
    HasIntervalSlicesEverywhere B :=
  fun e he ↦ (hA e he).congr_ae he hAB

/-- **Two-way `=ᵐ[volume]` invariance of `HasIntervalSlicesEverywhere`**. -/
theorem hasIntervalSlicesEverywhere_congr_ae {A B : Set E} (hAB : A =ᵐ[volume] B) :
    HasIntervalSlicesEverywhere A ↔ HasIntervalSlicesEverywhere B :=
  ⟨fun h ↦ h.congr_ae hAB, fun h ↦ h.congr_ae hAB.symm⟩

/-- Any Lebesgue-null set `A` satisfies `HasIntervalSlicesInDirection e A` for `‖e‖ = 1`. -/
theorem HasIntervalSlicesInDirection.of_measure_zero {e : E} (he : ‖e‖ = 1) {A : Set E}
    (hA : volume A = 0) : HasIntervalSlicesInDirection e A :=
  (hasIntervalSlicesInDirection_empty e).congr_ae he (ae_eq_empty.2 hA).symm

/-- Any Lebesgue-null set `A` satisfies `HasIntervalSlicesEverywhere A`. -/
theorem HasIntervalSlicesEverywhere.of_measure_zero {A : Set E} (hA : volume A = 0) :
    HasIntervalSlicesEverywhere A :=
  fun _ he ↦ HasIntervalSlicesInDirection.of_measure_zero he hA

/-- **Fiberwise 1D perimeter `< 4` implies `HasIntervalSlicesInDirection`**. -/
theorem hasIntervalSlicesInDirection_of_ae_perimeter_lt_four {e : E} (he : ‖e‖ = 1) {A : Set E}
    (hA : NullMeasurableSet A volume) (htop : volume A < ⊤)
    (hper : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, perimeter volume (lineSection e A y) < 4) :
    HasIntervalSlicesInDirection e A := by
  filter_upwards [ae_nullMeasurableSet_lineSection he hA,
    ae_volume_lineSection_lt_top he hA htop, hper] with y hnm hfin hpy
  exact IsAEOrdConnected.of_perimeter_lt_four hnm hfin hpy

/-- **Fiberwise 1D perimeter `≤ 2` implies `HasIntervalSlicesInDirection`**. -/
theorem hasIntervalSlicesInDirection_of_ae_perimeter_le_two {e : E} (he : ‖e‖ = 1) {A : Set E}
    (hA : NullMeasurableSet A volume) (htop : volume A < ⊤)
    (hper : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, perimeter volume (lineSection e A y) ≤ 2) :
    HasIntervalSlicesInDirection e A :=
  hasIntervalSlicesInDirection_of_ae_perimeter_lt_four he hA htop
    (hper.mono fun _ hy ↦ hy.trans_lt (by norm_num))

/-- **Steiner slice-perimeter equality implies `HasIntervalSlicesInDirection`**. -/
theorem hasIntervalSlicesInDirection_of_lintegral_perimeter_le {e : E} (he : ‖e‖ = 1) {A : Set E}
    (hA : NullMeasurableSet A volume) (htop : volume A < ⊤)
    (hmeas_lt : volume {y : (ℝ ∙ e)ᗮ | 0 < volume (lineSection e A y)} < ⊤)
    (hf_meas : AEMeasurable (fun y : (ℝ ∙ e)ᗮ ↦ perimeter volume (lineSection e A y)) volume)
    (hle : (∫⁻ y : (ℝ ∙ e)ᗮ, perimeter volume (lineSection e A y) ∂volume) ≤
      2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume (lineSection e A y)}) :
    HasIntervalSlicesInDirection e A :=
  hasIntervalSlicesInDirection_of_ae_perimeter_lt_four he hA htop
    (ae_perimeter_steinerFiber_lt_four_of_lintegral_perimeter_le he hA htop hmeas_lt hf_meas hle)

/-- **Steiner slice-perimeter equality in all unit directions implies
`HasIntervalSlicesEverywhere`**. -/
theorem hasIntervalSlicesEverywhere_of_lintegral_perimeter_le_forall {A : Set E}
    (hA : NullMeasurableSet A volume) (htop : volume A < ⊤)
    (hmeas_lt : ∀ e : E, ‖e‖ = 1 → volume {y : (ℝ ∙ e)ᗮ | 0 < volume (lineSection e A y)} < ⊤)
    (hf_meas : ∀ e : E, ‖e‖ = 1 →
      AEMeasurable (fun y : (ℝ ∙ e)ᗮ ↦ perimeter volume (lineSection e A y)) volume)
    (hle : ∀ e : E, ‖e‖ = 1 →
      (∫⁻ y : (ℝ ∙ e)ᗮ, perimeter volume (lineSection e A y) ∂volume) ≤
        2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume (lineSection e A y)}) :
    HasIntervalSlicesEverywhere A :=
  fun e he ↦ hasIntervalSlicesInDirection_of_lintegral_perimeter_le he hA htop
    (hmeas_lt e he) (hf_meas e he) (hle e he)

/-- **Steiner perimeter equality from Euclidean isoperimetric equality**. -/
theorem perimeter_steinerSymmetrization_eq_of_isoperimetricBound_eq {e : E} (he : ‖e‖ = 1)
    {A : Set E} (hA : NullMeasurableSet A volume)
    (hrec : perimeter volume (steinerSymmetrization e A) ≤ perimeter volume A)
    (hiso : isoperimetricBound (steinerSymmetrization e A) ≤
      perimeter volume (steinerSymmetrization e A))
    (heq : perimeter volume A = isoperimetricBound A) :
    perimeter volume (steinerSymmetrization e A) = perimeter volume A := by
  refine le_antisymm hrec ?_
  have hbound : isoperimetricBound (steinerSymmetrization e A) = isoperimetricBound A := by
    simp [isoperimetricBound, volume_steinerSymmetrization₀ he hA]
  rw [heq, ← hbound]; exact hiso

/-- Under the hypotheses of `perimeter_steinerSymmetrization_eq_of_isoperimetricBound_eq`,
`steinerSymmetrization e A` also has zero isoperimetric deficit. -/
theorem isoperimetricDeficit_steinerSymmetrization_eq_zero_of_isoperimetricBound_eq
    {e : E} (he : ‖e‖ = 1) {A : Set E} (hA : NullMeasurableSet A volume)
    (hrec : perimeter volume (steinerSymmetrization e A) ≤ perimeter volume A)
    (hiso : isoperimetricBound (steinerSymmetrization e A) ≤
      perimeter volume (steinerSymmetrization e A))
    (heq : perimeter volume A = isoperimetricBound A) :
    isoperimetricDeficit (steinerSymmetrization e A) = 0 := by
  have hbound : isoperimetricBound (steinerSymmetrization e A) = isoperimetricBound A := by
    simp [isoperimetricBound, volume_steinerSymmetrization₀ he hA]
  rw [isoperimetricDeficit,
    perimeter_steinerSymmetrization_eq_of_isoperimetricBound_eq he hA hrec hiso heq,
    hbound, heq, sub_self]

end IntervalSlicesAndSteinerEquality

/-! ### Section 3: Essential convexity, boundedness of convex sets, and compact convex reduction -/

section EssentialConvexityAndCompactReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Directional ball-complement subadditivity along a segment** under
`HasIntervalSlicesInDirection e A` with `h • e = x₂ - x₁`. -/
theorem volume_compl_inter_closedBall_combo_le_of_hasIntervalSlicesInDirection
    {e : E} (he : ‖e‖ = 1) {A : Set E} (hA : NullMeasurableSet A volume)
    (hdir : HasIntervalSlicesInDirection e A) {x₁ x₂ : E} {h : ℝ} (hhe : h • e = x₂ - x₁)
    (r : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    volume (Aᶜ ∩ Metric.closedBall (a • x₁ + b • x₂) r) ≤
      volume (Aᶜ ∩ Metric.closedBall x₁ r) + volume (Aᶜ ∩ Metric.closedBall x₂ r) := by
  let xb : E := a • x₁ + b • x₂
  have hxb : xb = x₁ + (b * h) • e := by
    rw [mul_smul, hhe]; dsimp only [xb]
    rw [eq_sub_of_add_eq hab, sub_smul, one_smul, smul_sub]; abel
  have hx2 : x₂ = x₁ + h • e := by rw [hhe, add_sub_cancel]
  let N : Set E := (A ∩ (fun x : E ↦ x + h • e) ⁻¹' A) \ (fun x : E ↦ x + (b * h) • e) ⁻¹' A
  have hN_pre : volume ((fun w : E ↦ x₁ + w) ⁻¹' N) = 0 := by
    rw [measure_preimage_add,
      volume_inter_preimage_add_smul_diff_eq_zero_of_ae_ordConnected_steinerFiber
        he hA (hdir.mono fun _ ⟨I, hI, hyI⟩ ↦ ⟨I, hI, hyI⟩) h ha hb hab]
  have htr (z : E) : volume (Aᶜ ∩ Metric.closedBall z r) =
      volume ((fun w : E ↦ z + w) ⁻¹' Aᶜ ∩ Metric.closedBall 0 r) := by
    rw [← measure_preimage_add volume z (Aᶜ ∩ Metric.closedBall z r)]
    congr 1; ext w; simp [Metric.mem_closedBall, dist_eq_norm]
  rw [htr xb, htr x₁, htr x₂]
  have hsub : (fun w : E ↦ xb + w) ⁻¹' Aᶜ ∩ Metric.closedBall 0 r ⊆
      ((fun w : E ↦ x₁ + w) ⁻¹' Aᶜ ∩ Metric.closedBall 0 r) ∪
        ((fun w : E ↦ x₂ + w) ⁻¹' Aᶜ ∩ Metric.closedBall 0 r) ∪
        (fun w : E ↦ x₁ + w) ⁻¹' N := by
    intro w ⟨hw_xb, hw_ball⟩
    by_cases hw1 : x₁ + w ∈ A
    · by_cases hw2 : x₂ + w ∈ A
      · refine Or.inr ⟨⟨hw1, ?_⟩, ?_⟩
        · have heq : x₁ + w + h • e = x₂ + w := by rw [hx2]; abel
          change x₁ + w + h • e ∈ A; rwa [heq]
        · have heq : x₁ + w + (b * h) • e = xb + w := by rw [hxb]; abel
          change x₁ + w + (b * h) • e ∉ A; rwa [heq]
      · exact Or.inl (Or.inr ⟨hw2, hw_ball⟩)
    · exact Or.inl (Or.inl ⟨hw1, hw_ball⟩)
  refine ((measure_mono hsub).trans (measure_union_le _ _)).trans ?_
  rw [hN_pre, add_zero]; exact measure_union_le _ _

/-- **Directional segment density-1 propagation for `essentialInterior`**. -/
theorem mem_essentialInterior_combo_of_hasIntervalSlicesInDirection {e : E} (he : ‖e‖ = 1)
    {A : Set E} (hA : NullMeasurableSet A volume) (hdir : HasIntervalSlicesInDirection e A)
    {x₁ x₂ : E} (hx₁ : x₁ ∈ essentialInterior volume A) (hx₂ : x₂ ∈ essentialInterior volume A)
    {h : ℝ} (hhe : h • e = x₂ - x₁) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x₁ + b • x₂ ∈ essentialInterior volume A := by
  rw [mem_essentialInterior_iff, ← hasMeasureDensityAt_compl_zero_iff hA] at hx₁ hx₂ ⊢
  have hsum : Tendsto
      (fun r : ℝ ↦ volume (Aᶜ ∩ Metric.closedBall x₁ r) / volume (Metric.closedBall x₁ r) +
        volume (Aᶜ ∩ Metric.closedBall x₂ r) / volume (Metric.closedBall x₂ r))
      (𝓝[>] 0) (𝓝 0) := by simpa using hx₁.add hx₂
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ _root_.zero_le) fun r ↦ ?_
  have hball (z : E) : volume (Metric.closedBall z r) = volume (Metric.closedBall (0 : E) r) :=
    Measure.addHaar_closedBall_center volume z r
  rw [hball (a • x₁ + b • x₂), hball x₁, hball x₂, ← ENNReal.add_div]
  exact ENNReal.div_le_div_right
    (volume_compl_inter_closedBall_combo_le_of_hasIntervalSlicesInDirection
      he hA hdir hhe r ha hb hab) _

/-- **Segment `[0, 1]` interpolation in `essentialInterior volume A`** from directional interval
slices along `e = ‖x₂ - x₁‖⁻¹ • (x₂ - x₁)`. -/
theorem mem_essentialInterior_lineMap_of_hasIntervalSlicesInDirection {A : Set E}
    (hA : NullMeasurableSet A volume) {x₁ x₂ : E} (hne : x₁ ≠ x₂)
    (hx₁ : x₁ ∈ essentialInterior volume A) (hx₂ : x₂ ∈ essentialInterior volume A)
    (hdir : HasIntervalSlicesInDirection (‖x₂ - x₁‖⁻¹ • (x₂ - x₁)) A)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) • x₁ + θ • x₂ ∈ essentialInterior volume A := by
  have hh : 0 < ‖x₂ - x₁‖ := norm_sub_pos_iff.2 hne.symm
  have he : ‖‖x₂ - x₁‖⁻¹ • (x₂ - x₁)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh, inv_mul_cancel₀ hh.ne']
  exact mem_essentialInterior_combo_of_hasIntervalSlicesInDirection he hA hdir hx₁ hx₂
    (smul_inv_smul₀ hh.ne' (x₂ - x₁)) (sub_nonneg.2 hθ₁) hθ₀ (sub_add_cancel 1 θ)

/-- **Convexity of `essentialInterior volume A` from `HasIntervalSlicesEverywhere A`**. -/
theorem HasIntervalSlicesEverywhere.convex_essentialInterior {A : Set E}
    (hA : NullMeasurableSet A volume) (h : HasIntervalSlicesEverywhere A) :
    Convex ℝ (essentialInterior volume A) :=
  convex_essentialInterior_of_ae_ordConnected_steinerFiber hA fun e he ↦
    (h e he).mono fun _ ⟨I, hI, hyI⟩ ↦ ⟨I, hI, hyI⟩

/-- **Essential convexity**: `A : Set E` is a.e. equal (with respect to `volume`) to a convex set
`C : Set E`. -/
def IsEssentiallyConvex (A : Set E) : Prop :=
  ∃ C : Set E, Convex ℝ C ∧ (A =ᵐ[volume] C)

theorem _root_.Convex.isEssentiallyConvex {C : Set E} (hC : Convex ℝ C) : IsEssentiallyConvex C :=
  ⟨C, hC, EventuallyEq.rfl⟩

theorem IsEssentiallyConvex.mono_ae {A B : Set E} (hA : IsEssentiallyConvex A)
    (hAB : A =ᵐ[volume] B) : IsEssentiallyConvex B := by
  rcases hA with ⟨C, hC, hAC⟩; exact ⟨C, hC, hAB.symm.trans hAC⟩

theorem isEssentiallyConvex_congr_ae {A B : Set E} (hAB : A =ᵐ[volume] B) :
    IsEssentiallyConvex A ↔ IsEssentiallyConvex B :=
  ⟨fun h ↦ h.mono_ae hAB, fun h ↦ h.mono_ae hAB.symm⟩

@[simp] theorem isEssentiallyConvex_empty : IsEssentiallyConvex (∅ : Set E) :=
  convex_empty.isEssentiallyConvex
@[simp] theorem isEssentiallyConvex_univ : IsEssentiallyConvex (Set.univ : Set E) :=
  convex_univ.isEssentiallyConvex

theorem IsEssentiallyConvex.of_measure_zero {A : Set E} (hA : volume A = 0) :
    IsEssentiallyConvex A :=
  isEssentiallyConvex_empty.mono_ae (ae_eq_empty.2 hA).symm

/-- Every essentially convex set satisfies `HasIntervalSlicesInDirection e A` for `‖e‖ = 1`. -/
theorem IsEssentiallyConvex.hasIntervalSlicesInDirection {A : Set E}
    (hA : IsEssentiallyConvex A) {e : E} (he : ‖e‖ = 1) :
    HasIntervalSlicesInDirection e A := by
  rcases hA with ⟨C, hC, hAC⟩; exact (hC.hasIntervalSlicesInDirection e).congr_ae he hAC.symm

/-- Every essentially convex set satisfies `HasIntervalSlicesEverywhere A`. -/
theorem IsEssentiallyConvex.hasIntervalSlicesEverywhere {A : Set E}
    (hA : IsEssentiallyConvex A) : HasIntervalSlicesEverywhere A :=
  fun _ he ↦ hA.hasIntervalSlicesInDirection he

/-- For any essentially convex set `A`, `essentialInterior volume A` is convex. -/
theorem IsEssentiallyConvex.convex_essentialInterior {A : Set E}
    (hA : IsEssentiallyConvex A) : Convex ℝ (essentialInterior volume A) := by
  rcases hA with ⟨C, hC, hAC⟩
  rw [essentialInterior_congr_ae hAC]
  have hC_nm : NullMeasurableSet C volume :=
    ⟨interior C, isOpen_interior.measurableSet, hC.interior_ae_eq.symm⟩
  exact hC.hasIntervalSlicesEverywhere.convex_essentialInterior hC_nm

/-- If `A` is null-measurable and `Convex ℝ (essentialInterior volume A)`, then `A` is essentially
convex (with convex representative `C = essentialInterior volume A`). -/
theorem IsEssentiallyConvex.of_convex_essentialInterior {A : Set E}
    (hA : NullMeasurableSet A volume) (hconv : Convex ℝ (essentialInterior volume A)) :
    IsEssentiallyConvex A :=
  ⟨essentialInterior volume A, hconv, (essentialInterior_ae_eq hA).symm⟩

/-- **Multi-directional interval slices imply essential convexity**. -/
theorem HasIntervalSlicesEverywhere.isEssentiallyConvex {A : Set E}
    (hA : NullMeasurableSet A volume) (h : HasIntervalSlicesEverywhere A) :
    IsEssentiallyConvex A :=
  IsEssentiallyConvex.of_convex_essentialInterior hA (h.convex_essentialInterior hA)

/-- **Equivalence between `IsEssentiallyConvex` and `HasIntervalSlicesEverywhere`**. -/
theorem isEssentiallyConvex_iff_hasIntervalSlicesEverywhere {A : Set E}
    (hA : NullMeasurableSet A volume) :
    IsEssentiallyConvex A ↔ HasIntervalSlicesEverywhere A :=
  ⟨IsEssentiallyConvex.hasIntervalSlicesEverywhere,
    HasIntervalSlicesEverywhere.isEssentiallyConvex hA⟩

/-- **Equivalence between `IsEssentiallyConvex` and `Convex ℝ (essentialInterior volume A)`**. -/
theorem isEssentiallyConvex_iff_convex_essentialInterior {A : Set E}
    (hA : NullMeasurableSet A volume) :
    IsEssentiallyConvex A ↔ Convex ℝ (essentialInterior volume A) :=
  ⟨IsEssentiallyConvex.convex_essentialInterior,
    IsEssentiallyConvex.of_convex_essentialInterior hA⟩

/-- **Equivalence between `HasIntervalSlicesEverywhere` and
`Convex ℝ (essentialInterior volume A)`**. -/
theorem hasIntervalSlicesEverywhere_iff_convex_essentialInterior {A : Set E}
    (hA : NullMeasurableSet A volume) :
    HasIntervalSlicesEverywhere A ↔ Convex ℝ (essentialInterior volume A) :=
  (isEssentiallyConvex_iff_hasIntervalSlicesEverywhere hA).symm.trans
    (isEssentiallyConvex_iff_convex_essentialInterior hA)

/-- **Steiner slice-perimeter equality criterion for `IsEssentiallyConvex`**. -/
theorem isEssentiallyConvex_of_lintegral_perimeter_le_forall {A : Set E}
    (hA : NullMeasurableSet A volume) (htop : volume A < ⊤)
    (hmeas_lt : ∀ e : E, ‖e‖ = 1 → volume {y : (ℝ ∙ e)ᗮ | 0 < volume (lineSection e A y)} < ⊤)
    (hf_meas : ∀ e : E, ‖e‖ = 1 →
      AEMeasurable (fun y : (ℝ ∙ e)ᗮ ↦ perimeter volume (lineSection e A y)) volume)
    (hle : ∀ e : E, ‖e‖ = 1 →
      (∫⁻ y : (ℝ ∙ e)ᗮ, perimeter volume (lineSection e A y) ∂volume) ≤
        2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume (lineSection e A y)}) :
    IsEssentiallyConvex A :=
  (hasIntervalSlicesEverywhere_of_lintegral_perimeter_le_forall hA htop hmeas_lt hf_meas hle)
    |>.isEssentiallyConvex hA

/-! #### Boundedness of positive-finite-volume convex sets and compact convex body reduction -/

section BoundednessAndCompactRepresentative

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- If `Convex ℝ C`, `Metric.ball x₀ r ⊆ C`, `y ∈ C`, and `t ∈ [0, 1 / 2]`, then the ball
`Metric.ball (x₀ + t • (y - x₀)) (r / 2)` of fixed radius `r / 2` is contained in `C`. -/
theorem ball_add_smul_sub_subset_of_convex {C : Set V} (hC : Convex ℝ C) {x₀ y : V} {r t : ℝ}
    (hball : Metric.ball x₀ r ⊆ C) (hy : y ∈ C) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1 / 2) :
    Metric.ball (x₀ + t • (y - x₀)) (r / 2) ⊆ C := by
  intro z hz
  have h1t : 1 / 2 ≤ 1 - t := by linarith
  have h1t_pos : 0 < 1 - t := by linarith
  let w : V := x₀ + (1 - t)⁻¹ • (z - (x₀ + t • (y - x₀)))
  have hw : w ∈ Metric.ball x₀ r := by
    rw [Metric.mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 h1t_pos), inv_mul_lt_iff₀ h1t_pos]
    have hz' : ‖z - (x₀ + t • (y - x₀))‖ < r / 2 := by simpa [dist_eq_norm] using hz
    have hr_pos : 0 < r := by linarith [norm_nonneg (z - (x₀ + t • (y - x₀)))]
    nlinarith
  have hcomb : (1 - t) • w + t • y = z := by
    dsimp [w]; rw [smul_add, smul_inv_smul₀ h1t_pos.ne', sub_smul, one_smul, smul_sub]; abel
  exact hcomb ▸ hC (hball hw) hy h1t_pos.le ht₀ (sub_add_cancel 1 t)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {μ : Measure V} [μ.IsAddHaarMeasure]

/-- **Every convex set `C ⊆ V` with `0 < μ C` and `μ C < ⊤` is bounded** (`Bornology.IsBounded C`).
-/
theorem _root_.Convex.isBounded_of_measure_pos_of_measure_lt_top {C : Set V} (hC : Convex ℝ C)
    (hpos : 0 < μ C) (htop : μ C < ⊤) : Bornology.IsBounded C := by
  obtain ⟨x₀, hx₀⟩ := hC.interior_nonempty_of_measure_pos hpos
  obtain ⟨r, hr, hball_int⟩ := Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx₀)
  have hball : Metric.ball x₀ r ⊆ C := hball_int.trans interior_subset
  let v : ℝ≥0∞ := μ (Metric.ball x₀ (r / 2))
  have hv_pos : 0 < v := measure_ball_pos μ x₀ (half_pos hr)
  have hv_top : v < ⊤ := measure_ball_lt_top
  obtain ⟨N, hN_gt⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top htop.ne hv_pos.ne')
  have hN_pos : 0 < N := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hN_gt
  have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.2 hN_pos
  have hC_lt : μ C < N * v := (ENNReal.div_lt_iff (Or.inl hv_pos.ne') (Or.inl hv_top.ne)).1 hN_gt
  refine (Metric.isBounded_closedBall (x := x₀) (r := 2 * (N : ℝ) * r)).subset fun y hy ↦ ?_
  rw [Metric.mem_closedBall, dist_eq_norm]; by_contra! hy_gt
  let c : Fin N → V := fun k ↦ x₀ + ((k : ℝ) / (2 * (N : ℝ))) • (y - x₀)
  let B : Fin N → Set V := fun k ↦ Metric.ball (c k) (r / 2)
  have hB_sub : ∀ k : Fin N, B k ⊆ C := fun k ↦ by
    refine ball_add_smul_sub_subset_of_convex hC hball hy (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) two_pos]
    have hk : (k : ℝ) ≤ N := by exact_mod_cast k.isLt.le
    linarith
  have hB_disj : Pairwise (Disjoint on B) := fun i j hij ↦ by
    refine Metric.ball_disjoint_ball ?_
    have hdiff : c i - c j = (((i : ℝ) - (j : ℝ)) / (2 * (N : ℝ))) • (y - x₀) := by
      dsimp [c]; rw [sub_div, sub_smul]; abel
    rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * (N : ℝ)), add_halves]
    have hij_one : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · have h1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
        rw [abs_of_neg (by linarith)]; linarith
      · have h1 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
        rw [abs_of_pos (by linarith)]; linarith
    have h1 : 1 / (2 * (N : ℝ)) * (2 * (N : ℝ) * r) ≤
        |(i : ℝ) - (j : ℝ)| / (2 * (N : ℝ)) * ‖y - x₀‖ :=
      mul_le_mul (div_le_div_of_nonneg_right hij_one (by positivity)) hy_gt.le
        (by positivity) (by positivity)
    have h2 : 1 / (2 * (N : ℝ)) * (2 * (N : ℝ) * r) = r := by field_simp
    linarith
  have hsum : (N : ℝ≥0∞) * v ≤ μ C := by
    calc (N : ℝ≥0∞) * v = ∑ k : Fin N, μ (B k) := by simp [v, B, Measure.addHaar_ball_center]
      _ = μ (⋃ k ∈ (Finset.univ : Finset (Fin N)), B k) :=
          (measure_biUnion_finset (fun i _ j _ hij ↦ hB_disj hij)
            (fun _ _ ↦ measurableSet_ball)).symm
      _ ≤ μ C := measure_mono (iUnion₂_subset fun k _ ↦ hB_sub k)
  exact hC_lt.not_ge hsum

/-- **For any convex set `C ⊆ V` with `0 < μ C` and `μ C < ⊤`, its closure `closure C` is a
compact convex set with nonempty interior and `closure C =ᵐ[μ] C`**. -/
theorem _root_.Convex.isCompact_closure_of_measure_pos_of_measure_lt_top {C : Set V}
    (hC : Convex ℝ C) (hpos : 0 < μ C) (htop : μ C < ⊤) :
    IsCompact (closure C) ∧ Convex ℝ (closure C) ∧ (interior (closure C)).Nonempty ∧
      μ (frontier C) = 0 ∧ (closure C =ᵐ[μ] C) ∧ μ (closure C) = μ C :=
  ⟨Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (hC.isBounded_of_measure_pos_of_measure_lt_top hpos htop).closure,
    hC.closure, (hC.interior_nonempty_of_measure_pos hpos).mono (interior_mono subset_closure),
    hC.addHaar_frontier μ, hC.closure_ae_eq, hC.measure_closure⟩

end BoundednessAndCompactRepresentative

/-- `relativePerimeter volume U (closure C) = relativePerimeter volume U C` for convex `C`. -/
theorem _root_.Convex.relativePerimeter_closure {C : Set E} (hC : Convex ℝ C) (U : Opens E) :
    relativePerimeter volume U (closure C) = relativePerimeter volume U C :=
  relativePerimeter_congr_ae (ae_restrict_of_ae (hC.closure_ae_eq (μ := volume)))

/-- `distributionalVariation volume U ((closure C).indicator 1) =
distributionalVariation volume U (C.indicator 1)` for convex `C`. -/
theorem _root_.Convex.distributionalVariation_closure {C : Set E} (hC : Convex ℝ C) (U : Opens E) :
    distributionalVariation volume U ((closure C).indicator fun _ ↦ (1 : ℝ)) =
      distributionalVariation volume U (C.indicator fun _ ↦ (1 : ℝ)) :=
  hC.relativePerimeter_closure U

/-- **Compact convex representative of a positive-finite-volume convex set**: `K := closure C` is
compact and convex with nonempty interior, `K =ᵐ[volume] C`, `volume K = volume C`, and
`perimeter volume K = perimeter volume C`. -/
theorem _root_.Convex.exists_isCompact_convex_ae_eq {C : Set E} (hC : Convex ℝ C)
    (hpos : 0 < volume C) (htop : volume C < ⊤) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      (K =ᵐ[volume] C) ∧ volume K = volume C ∧ perimeter volume K = perimeter volume C := by
  obtain ⟨hcomp, hconv, hint, _, hae, hvol⟩ :=
    hC.isCompact_closure_of_measure_pos_of_measure_lt_top hpos htop
  exact ⟨closure C, hcomp, hconv, hint, hae, hvol, hC.perimeter_closure volume⟩

/-- **Compact convex body reduction for essentially convex sets**. -/
theorem IsEssentiallyConvex.exists_isCompact_convex_ae_eq {A : Set E}
    (hA : IsEssentiallyConvex A) (hpos : 0 < volume A) (htop : volume A < ⊤) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      (A =ᵐ[volume] K) ∧ volume K = volume A ∧ perimeter volume K = perimeter volume A ∧
      isoperimetricBound K = isoperimetricBound A ∧
      isoperimetricDeficit K = isoperimetricDeficit A := by
  rcases hA with ⟨C, hC, hAC⟩
  obtain ⟨K, hK_comp, hK_conv, hK_int, hKC, _, _⟩ :=
    hC.exists_isCompact_convex_ae_eq ((measure_congr hAC) ▸ hpos) ((measure_congr hAC) ▸ htop)
  have hAK : A =ᵐ[volume] K := hAC.trans hKC.symm
  exact ⟨K, hK_comp, hK_conv, hK_int, hAK, measure_congr hAK.symm, perimeter_congr_ae hAK.symm,
    isoperimetricBound_congr_ae hAK.symm, isoperimetricDeficit_congr_ae hAK.symm⟩

/-- **Compact convex body reduction from `HasIntervalSlicesEverywhere`**. -/
theorem HasIntervalSlicesEverywhere.exists_isCompact_convex_ae_eq {A : Set E}
    (hA : NullMeasurableSet A volume) (h : HasIntervalSlicesEverywhere A)
    (hpos : 0 < volume A) (htop : volume A < ⊤) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      (A =ᵐ[volume] K) ∧ volume K = volume A ∧ perimeter volume K = perimeter volume A ∧
      isoperimetricBound K = isoperimetricBound A ∧
      isoperimetricDeficit K = isoperimetricDeficit A :=
  (h.isEssentiallyConvex hA).exists_isCompact_convex_ae_eq hpos htop

/-- **Explicit `closure (essentialInterior volume A)` compact convex representative**. -/
theorem HasIntervalSlicesEverywhere.isCompact_closure_essentialInterior {A : Set E}
    (hA : NullMeasurableSet A volume) (h : HasIntervalSlicesEverywhere A)
    (hpos : 0 < volume A) (htop : volume A < ⊤) :
    let K := closure (essentialInterior volume A)
    IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      (A =ᵐ[volume] K) ∧ volume K = volume A ∧ perimeter volume K = perimeter volume A := by
  dsimp only
  have hC : Convex ℝ (essentialInterior volume A) := h.convex_essentialInterior hA
  have hCA : (essentialInterior volume A : Set E) =ᵐ[volume] A := essentialInterior_ae_eq hA
  obtain ⟨hcomp, hconv, hint, _, hKC, _⟩ :=
    hC.isCompact_closure_of_measure_pos_of_measure_lt_top
      ((measure_congr hCA).symm ▸ hpos) ((measure_congr hCA).symm ▸ htop)
  have hAK : A =ᵐ[volume] closure (essentialInterior volume A) := hCA.symm.trans hKC.symm
  exact ⟨hcomp, hconv, hint, hAK, measure_congr hAK.symm, perimeter_congr_ae hAK.symm⟩

/-- **Steiner-equality-to-compact-convex-body reduction**. -/
theorem exists_isCompact_convex_ae_eq_of_lintegral_perimeter_le_forall {A : Set E}
    (hA : NullMeasurableSet A volume) (hpos : 0 < volume A) (htop : volume A < ⊤)
    (hmeas_lt : ∀ e : E, ‖e‖ = 1 → volume {y : (ℝ ∙ e)ᗮ | 0 < volume (lineSection e A y)} < ⊤)
    (hf_meas : ∀ e : E, ‖e‖ = 1 →
      AEMeasurable (fun y : (ℝ ∙ e)ᗮ ↦ perimeter volume (lineSection e A y)) volume)
    (hle : ∀ e : E, ‖e‖ = 1 →
      (∫⁻ y : (ℝ ∙ e)ᗮ, perimeter volume (lineSection e A y) ∂volume) ≤
        2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume (lineSection e A y)}) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      (A =ᵐ[volume] K) ∧ volume K = volume A ∧ perimeter volume K = perimeter volume A ∧
      isoperimetricBound K = isoperimetricBound A ∧
      isoperimetricDeficit K = isoperimetricDeficit A :=
  (isEssentiallyConvex_of_lintegral_perimeter_le_forall hA htop hmeas_lt hf_meas hle)
    |>.exists_isCompact_convex_ae_eq hpos htop

end EssentialConvexityAndCompactReduction

end TauCeti
