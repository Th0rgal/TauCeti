/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Hausdorff 1-measure of curve traces and total variation

This file relates the one-dimensional Hausdorff measure `μH[1]` (and its Euclidean-normalized
variant `μHE[1]`) of the trace `γ '' Set.Icc a b` of a continuous curve `γ : ℝ → X` to its total
variation `eVariationOn γ (Set.Icc a b)`.

## Main results

* `MeasureTheory.Measure.euclideanHausdorffMeasure_one`: on any Borel extended metric space `X`,
  the one-dimensional Euclidean Hausdorff measure `μHE[1]` coincides with `μH[1]`.
* `IsPreconnected.edist_le_hausdorffMeasure`, `IsPreconnected.ediam_le_hausdorffMeasure`: in a
  preconnected subset `s` of an extended metric space, the extended distance between any two points
  of `s` (and hence `EMetric.diam s`) is bounded above by `μH[1] s`.
* `TauCeti.hausdorffMeasure_one_image_Icc_le_eVariationOn`,
  `TauCeti.euclideanHausdorffMeasure_trace_le_eVariationOn`: for any curve `γ : ℝ → X` continuous on
  `[a, b]`, the one-dimensional Hausdorff measure of its trace is at most its total variation
  `eVariationOn γ (Set.Icc a b)`.
* `TauCeti.eVariationOn_le_hausdorffMeasure_one_image_Icc_of_injOn_Ico`: if `γ` is continuous on
  `[a, b]` and injective on `[a, b)`, then
  `eVariationOn γ (Set.Icc a b) ≤ μH[1] (γ '' Set.Icc a b)`.
* `TauCeti.hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn`,
  `TauCeti.euclideanHausdorffMeasure_trace_eq_eVariationOn`: for a continuous injective curve (arc)
  on `[a, b]`, the Hausdorff 1-measure of its trace equals its total variation.
* `TauCeti.hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico`,
  `TauCeti.hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_simpleClosed`: the same equality holds
  for simple closed curves (continuous on `[a, b]` and injective on `[a, b)`).
* `TauCeti.hausdorffMeasure_image_Icc_eq_zero_of_one_lt`,
  `TauCeti.volume_trace_eq_zero_of_two_le`, `TauCeti.volume_trace_eq_zero`: the trace of a
  rectifiable continuous curve has `d`-dimensional Hausdorff measure zero for all `d > 1`, and in
  particular has Lebesgue volume zero in `EuclideanSpace ℝ (Fin n)` for `n ≥ 2` and in `ℂ`.
-/

public section

open Filter Function Metric MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal Topology

/-! ### Normalization of the 1-dimensional Euclidean Hausdorff measure -/

namespace MeasureTheory.Measure

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

set_option backward.isDefEq.respectTransparency false in -- needed by simplifying `1 • _`
/-- In dimension `1`, the Euclidean-normalized Hausdorff measure `μHE[1]` coincides with the
standard Hausdorff measure `μH[1]`. -/
@[simp]
theorem euclideanHausdorffMeasure_one : (μHE[1] : Measure X) = (μH[1] : Measure X) := by
  have hR : (μHE[1] : Measure ℝ) = volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  have h : (μHE[1] : Measure ℝ) (Icc 0 1) = 1 := by
    rw [hR, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have h1 : (μH[(1 : ℕ)] : Measure ℝ) (Icc 0 1) = 1 := by simp [Real.volume_Icc]
  rw [euclideanHausdorffMeasure_def, smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one,
    ENNReal.coe_eq_one] at h
  rw [euclideanHausdorffMeasure_def, h]
  simp

end MeasureTheory.Measure

/-! ### Connected sets and Hausdorff 1-measure -/

section Connected

variable {X : Type*} [EMetricSpace X] {s : Set X} {a b : X}

/-- The points at finite extended distance from `a`. -/
def boundedComponent (a : X) : Set X := {x | edist a x ≠ ∞}

/-- In a preconnected subset of an extended metric space, any two points are at finite distance. -/
theorem IsPreconnected.edist_ne_top (hs : IsPreconnected s) (ha : a ∈ s) (hb : b ∈ s) :
    edist a b ≠ ∞ := by
  rw [edist_comm, ← lt_top_iff_ne_top, ← mem_eball]
  exact hs.subset_isClopen ⟨isClosed_eball_top, isOpen_eball⟩ ⟨a, ha, by simp⟩ hb

/-- A preconnected set lies in the bounded component of any of its points. -/
theorem IsPreconnected.subset_boundedComponent (hs : IsPreconnected s) (ha : a ∈ s) :
    s ⊆ boundedComponent a :=
  fun _ hb => hs.edist_ne_top ha hb

/-- The points at finite distance from `a` form a pseudometric space, with distance given by the
real part of the extended distance. -/
instance (a : X) : PseudoMetricSpace (boundedComponent a) :=
  PseudoEMetricSpace.toPseudoMetricSpace fun p q => by
    refine ((edist_triangle p.1 a q.1).trans_lt (ENNReal.add_lt_top.2 ⟨?_, q.2.lt_top⟩)).ne
    rw [edist_comm]
    exact p.2.lt_top

/-- The distance function `x ↦ (edist a x).toReal` is `1`-Lipschitz on any preconnected set `s`
that contains `a`. -/
theorem lipschitzOnWith_toReal_edist (hs : IsPreconnected s) (ha : a ∈ s) :
    LipschitzOnWith 1 (fun x => (edist a x).toReal) s := by
  intro x hx y hy
  exact LipschitzWith.dist_right (⟨a, by simp [boundedComponent]⟩ : boundedComponent a)
    ⟨x, hs.edist_ne_top ha hx⟩ ⟨y, hs.edist_ne_top ha hy⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- For any `a`, `b` in a preconnected set `s` and any `r ≤ edist a b`, the radius `r` is at most
the one-dimensional Hausdorff measure of the part of `s` lying in the open ball of radius `r`
around `a`. -/
theorem IsPreconnected.le_hausdorffMeasure_of_le_edist (hs : IsPreconnected s) (ha : a ∈ s)
    (hb : b ∈ s) {r : ℝ≥0∞} (hr : r ≤ edist a b) :
    r ≤ μH[1] (s ∩ eball a r) :=
  have hrne : r ≠ ∞ := ne_top_of_le_ne_top (hs.edist_ne_top ha hb) hr
  calc
    r = ENNReal.ofReal r.toReal := (ENNReal.ofReal_toReal hrne).symm
    _ = μH[1] (Ico 0 r.toReal) := by rw [hausdorffMeasure_real, Real.volume_Ico, sub_zero]
    _ ≤ μH[1] ((fun x => (edist a x).toReal) '' (s ∩ eball a r)) := by
      refine measure_mono fun c hc => ?_
      have hsub : Ico 0 r.toReal ⊆ (fun x => (edist a x).toReal) '' s := calc
        Ico 0 r.toReal ⊆ Icc 0 (edist a b).toReal :=
          Ico_subset_Icc_self.trans (Icc_subset_Icc_right
            (ENNReal.toReal_mono (hs.edist_ne_top ha hb) hr))
        _ ⊆ _ := (hs.image _ (lipschitzOnWith_toReal_edist hs ha).continuousOn).Icc_subset
          ⟨a, ha, by simp⟩ ⟨b, hb, rfl⟩
      obtain ⟨z, hz, hgz⟩ : c ∈ (fun x => (edist a x).toReal) '' s := hsub hc
      refine ⟨z, ⟨hz, ?_⟩, hgz⟩
      rw [mem_eball', ← ENNReal.toReal_lt_toReal (hs.edist_ne_top ha hz) hrne]
      exact hgz.le.trans_lt hc.2
    _ ≤ μH[1] (s ∩ eball a r) := by
      simpa using ((lipschitzOnWith_toReal_edist hs ha).mono
        inter_subset_left).hausdorffMeasure_image_le zero_le_one

/-- The extended distance between two points of a preconnected set `s` is at most the
one-dimensional Hausdorff measure of `s`. -/
theorem IsPreconnected.edist_le_hausdorffMeasure (hs : IsPreconnected s) (ha : a ∈ s)
    (hb : b ∈ s) : edist a b ≤ μH[1] s :=
  (hs.le_hausdorffMeasure_of_le_edist ha hb le_rfl).trans (measure_mono inter_subset_left)

/-- The extended diameter of a preconnected set is at most its one-dimensional Hausdorff measure. -/
theorem IsPreconnected.ediam_le_hausdorffMeasure (hs : IsPreconnected s) :
    ediam s ≤ μH[1] s :=
  ediam_le fun _ ha _ hb => hs.edist_le_hausdorffMeasure ha hb

/-- The extended distance between two points of a preconnected set `s` is at most the
one-dimensional Euclidean Hausdorff measure of `s`. -/
theorem IsPreconnected.edist_le_euclideanHausdorffMeasure (hs : IsPreconnected s) (ha : a ∈ s)
    (hb : b ∈ s) : edist a b ≤ μHE[1] s := by
  simpa using hs.edist_le_hausdorffMeasure ha hb

/-- The extended diameter of a preconnected set is at most its one-dimensional Euclidean Hausdorff
measure. -/
theorem IsPreconnected.ediam_le_euclideanHausdorffMeasure (hs : IsPreconnected s) :
    ediam s ≤ μHE[1] s := by
  simpa using hs.ediam_le_hausdorffMeasure

/-- A preconnected set with finite `d`-dimensional Hausdorff measure for some `d < 1` is a
subsingleton. -/
theorem IsPreconnected.subsingleton_of_hausdorffMeasure_lt_top (hs : IsPreconnected s) {d : ℝ}
    (hd : d < 1) (hle : μH[d] s < ∞) : s.Subsingleton := by
  rw [← ediam_eq_zero_iff, ← le_zero_iff]
  exact hs.ediam_le_hausdorffMeasure.trans_eq
    ((hausdorffMeasure_zero_or_top hd s).resolve_right hle.ne)

/-- A set with finite `d`-dimensional Hausdorff measure for some `d < 1` is totally disconnected. -/
theorem isTotallyDisconnected_of_hausdorffMeasure_lt_top {d : ℝ} (hd : d < 1)
    (hle : μH[d] s < ∞) : IsTotallyDisconnected s :=
  fun _ hts ht => ht.subsingleton_of_hausdorffMeasure_lt_top hd ((measure_mono hts).trans_lt hle)

end Connected

namespace TauCeti

/-! ### Upper bound: Hausdorff 1-measure of a curve trace is at most its total variation -/

section UpperBound

/-- The extended diameter of the image of a set `s` under `f` is bounded above by the total
variation `eVariationOn f s`. -/
theorem ediam_image_le_eVariationOn {α : Type*} [LinearOrder α] {X : Type*} [PseudoEMetricSpace X]
    (f : α → X) (s : Set α) :
    ediam (f '' s) ≤ eVariationOn f s :=
  ediam_image_le_iff.2 fun _ hx _ hy => eVariationOn.edist_le f hx hy

private lemma Icc_subset_iUnion_fin_Icc {α : Type*} [LinearOrder α] {I : ℕ → α} (hI : Monotone I)
    (n : ℕ) :
    Icc (I 0) (I (n + 1)) ⊆ ⋃ i : Fin (n + 1), Icc (I i) (I (i + 1)) := by
  induction n with
  | zero =>
    intro x hx
    exact mem_iUnion.2 ⟨0, hx⟩
  | succ n ih =>
    rw [← Icc_union_Icc_eq_Icc (hI (Nat.zero_le _)) (hI (Nat.le_succ _))]
    rintro x (hx | hx)
    · rcases mem_iUnion.1 (ih hx) with ⟨i, hi⟩
      exact mem_iUnion.2 ⟨i.castSucc, hi⟩
    · exact mem_iUnion.2 ⟨Fin.last (n + 1), hx⟩

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The one-dimensional Hausdorff measure of the trace of a continuous curve `γ : ℝ → X` on `[a, b]`
is bounded above by its total variation `eVariationOn γ (Icc a b)`. -/
theorem hausdorffMeasure_one_image_Icc_le_eVariationOn {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) :
    μH[1] (γ '' Icc a b) ≤ eVariationOn γ (Icc a b) := by
  rcases le_or_gt a b with hab | hba
  · let u : ℕ → ℕ → ℝ := fun n k => a + (k : ℝ) * ((b - a) / (n + 1 : ℝ))
    have hu_zero (n : ℕ) : u n 0 = a := by simp [u]
    have hu_last (n : ℕ) : u n (n + 1) = b := by
      have hne : (n + 1 : ℝ) ≠ 0 := by positivity
      dsimp [u]
      push_cast
      rw [mul_div_cancel₀ _ hne, add_sub_cancel]
    have hu_mono (n : ℕ) : Monotone (u n) := by
      intro i j hij
      dsimp [u]
      have hba : 0 ≤ (b - a) / (n + 1 : ℝ) := div_nonneg (sub_nonneg.2 hab) (by positivity)
      gcongr
    have hu_sub (n k : ℕ) : u n (k + 1) - u n k = (b - a) / (n + 1 : ℝ) := by
      dsimp [u]
      push_cast
      ring
    have hu_Icc (n : ℕ) (i : Fin (n + 1)) : Icc (u n i) (u n (i + 1)) ⊆ Icc a b := by
      refine Icc_subset_Icc ?_ ?_
      · rw [← hu_zero n]
        exact hu_mono n (Nat.zero_le _)
      · rw [← hu_last n]
        exact hu_mono n (Nat.succ_le_of_lt i.isLt)
    let t : ∀ n : ℕ, Fin (n + 1) → Set X := fun n i => γ '' Icc (u n i) (u n (i + 1))
    let r : ℕ → ℝ≥0∞ := fun n => ⨆ i : Fin (n + 1), ediam (t n i)
    have ht : ∀ᶠ n in atTop, ∀ i : Fin (n + 1), ediam (t n i) ≤ r n :=
      Eventually.of_forall fun n i => le_iSup (fun j : Fin (n + 1) => ediam (t n j)) i
    have hst : ∀ᶠ n in atTop, γ '' Icc a b ⊆ ⋃ i : Fin (n + 1), t n i := by
      refine Eventually.of_forall fun n => ?_
      rw [← image_iUnion]
      refine image_mono ?_
      have hcov := Icc_subset_iUnion_fin_Icc (hu_mono n) n
      rwa [hu_zero n, hu_last n] at hcov
    have hr : Tendsto r atTop (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      obtain ⟨δ, hδ, huc⟩ :=
        EMetric.uniformContinuousOn_iff.1 (isCompact_Icc.uniformContinuousOn_of_continuous hγ) ε hε
      have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((b - a) / (n + 1 : ℝ))) atTop (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        refine ENNReal.tendsto_ofReal ?_
        have h0 := (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp (tendsto_add_atTop_nat 1)
        simpa [Function.comp_def] using h0
      filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
      refine iSup_le fun i => ediam_image_le_iff.2 fun x hx y hy => ?_
      refine (huc (hu_Icc n i hx) (hu_Icc n i hy) ?_).le
      rw [edist_dist]
      refine (ENNReal.ofReal_le_ofReal (Real.dist_le_of_mem_Icc hx hy)).trans_lt ?_
      rwa [hu_sub]
    have hsum (n : ℕ) :
        (∑ i : Fin (n + 1), ediam (t n i) ^ (1 : ℝ)) ≤ eVariationOn γ (Icc a b) := by
      simp only [ENNReal.rpow_one]
      rw [Fin.sum_univ_eq_sum_range (fun k => ediam (γ '' Icc (u n k) (u n (k + 1)))) (n + 1)]
      calc
        ∑ k ∈ Finset.range (n + 1), ediam (γ '' Icc (u n k) (u n (k + 1)))
          ≤ ∑ k ∈ Finset.range (n + 1), eVariationOn γ (Icc (u n k) (u n (k + 1))) :=
            Finset.sum_le_sum fun k _ => ediam_image_le_eVariationOn γ _
        _ = eVariationOn γ (Icc (u n 0) (u n (n + 1))) := eVariationOn.sum' γ (hu_mono n)
        _ = eVariationOn γ (Icc a b) := by rw [hu_zero n, hu_last n]
    calc
      μH[1] (γ '' Icc a b)
        ≤ liminf (fun n => ∑ i : Fin (n + 1), ediam (t n i) ^ (1 : ℝ)) atTop :=
          hausdorffMeasure_le_liminf_sum 1 (γ '' Icc a b) r hr t ht hst
      _ ≤ liminf (fun _ : ℕ => eVariationOn γ (Icc a b)) atTop :=
          liminf_le_liminf (Eventually.of_forall hsum)
      _ = eVariationOn γ (Icc a b) := liminf_const _
  · simp [Icc_eq_empty hba.not_ge]

/-- The one-dimensional Euclidean Hausdorff measure of the trace of a continuous curve `γ : ℝ → X`
on `[a, b]` is bounded above by its total variation `eVariationOn γ (Icc a b)`. -/
theorem euclideanHausdorffMeasure_one_image_Icc_le_eVariationOn {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) :
    μHE[1] (γ '' Icc a b) ≤ eVariationOn γ (Icc a b) := by
  simpa using hausdorffMeasure_one_image_Icc_le_eVariationOn hγ

/-- For a continuous curve `γ : ℝ → EuclideanSpace ℝ (Fin n)` of bounded variation on `[a, b]`,
the one-dimensional Euclidean Hausdorff measure of its trace is at most its total variation. -/
theorem euclideanHausdorffMeasure_trace_le_eVariationOn
    {n : ℕ} {γ : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ} (_hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (_hrect : BoundedVariationOn γ (Icc a b)) :
    μHE[1] (γ '' Icc a b) ≤ eVariationOn γ (Icc a b) :=
  euclideanHausdorffMeasure_one_image_Icc_le_eVariationOn hγ

end UpperBound

/-! ### Lower bound and equality for injective arcs and simple closed curves -/

section InjectiveAndSimpleClosed

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- If a curve `γ : ℝ → X` is continuous on `[a, b]` and injective on `[a, b)` (which covers both
injective arcs and simple closed curves), then its total variation on `[a, b]` is bounded above by
the one-dimensional Hausdorff measure of its trace `γ '' Icc a b`. -/
theorem eVariationOn_le_hausdorffMeasure_one_image_Icc_of_injOn_Ico {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    eVariationOn γ (Icc a b) ≤ μH[1] (γ '' Icc a b) := by
  have := nullSingletonClass_hausdorff X one_pos
  refine iSup_le ?_
  rintro ⟨n, u, hu, hus⟩
  let A : ℕ → Set X := fun i => γ '' Icc (u i) (u (i + 1)) \ {γ (u (i + 1))}
  have hIcc_sub (i : ℕ) : Icc (u i) (u (i + 1)) ⊆ Icc a b :=
    Icc_subset_Icc (hus i).1 (hus (i + 1)).2
  have hIco_sub (i : ℕ) : Ico (u i) (u (i + 1)) ⊆ Ico a b :=
    fun x hx => ⟨(hus i).1.trans hx.1, hx.2.trans_le (hus (i + 1)).2⟩
  have hA_sub_Ico (i : ℕ) : A i ⊆ γ '' Ico (u i) (u (i + 1)) := by
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, ⟨hx.1, hx.2.lt_of_ne ?_⟩, rfl⟩
    rintro rfl
    exact hy rfl
  have hA_meas (i : ℕ) : MeasurableSet (A i) :=
    (isCompact_Icc.image_of_continuousOn (hγ.mono (hIcc_sub i))).isClosed.measurableSet.diff
      (measurableSet_singleton _)
  have hle_A (i : ℕ) : edist (γ (u (i + 1))) (γ (u i)) ≤ μH[1] (A i) := by
    rw [measure_sdiff_null (measure_singleton _)]
    have hprec : IsPreconnected (γ '' Icc (u i) (u (i + 1))) :=
      isPreconnected_Icc.image γ (hγ.mono (hIcc_sub i))
    have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    exact hprec.edist_le_hausdorffMeasure
      (mem_image_of_mem γ (right_mem_Icc.2 hui))
      (mem_image_of_mem γ (left_mem_Icc.2 hui))
  calc
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
      ≤ ∑ i ∈ Finset.range n, μH[1] (A i) := Finset.sum_le_sum fun i _ => hle_A i
    _ = μH[1] (⋃ i ∈ Finset.range n, A i) := by
      refine (measure_biUnion_finset (fun i _ j _ hij => ?_) fun i _ => hA_meas i).symm
      have hIco_disj : Disjoint (Ico (u i) (u (i + 1))) (Ico (u j) (u (j + 1))) := by
        rcases lt_or_gt_of_ne hij with hlt | hlt
        · exact Set.disjoint_left.2 fun x hxi hxj =>
            (lt_of_lt_of_le hxi.2 (hu (Nat.succ_le_of_lt hlt))).not_ge hxj.1
        · exact Set.disjoint_left.2 fun x hxi hxj =>
            (lt_of_lt_of_le hxj.2 (hu (Nat.succ_le_of_lt hlt))).not_ge hxi.1
      refine Disjoint.mono (hA_sub_Ico i) (hA_sub_Ico j) ?_
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
      exact Set.disjoint_left.1 hIco_disj hx (hinj (hIco_sub j hy) (hIco_sub i hx) hyx ▸ hy)
    _ ≤ μH[1] (γ '' Icc a b) := by
      refine measure_mono (iUnion₂_subset fun i _ => ?_)
      exact sdiff_subset.trans (image_mono (hIcc_sub i))

/-- If a curve `γ : ℝ → X` is continuous on `[a, b]` and injective on `[a, b)`, then its total
variation on `[a, b]` is bounded above by the one-dimensional Euclidean Hausdorff measure of its
trace. -/
theorem eVariationOn_le_euclideanHausdorffMeasure_one_image_Icc_of_injOn_Ico {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    eVariationOn γ (Icc a b) ≤ μHE[1] (γ '' Icc a b) := by
  simpa using eVariationOn_le_hausdorffMeasure_one_image_Icc_of_injOn_Ico hγ hinj

/-- If a curve `γ : ℝ → X` is continuous and injective on `[a, b]`, then its total variation on
`[a, b]` is bounded above by the one-dimensional Hausdorff measure of its trace. -/
theorem eVariationOn_le_hausdorffMeasure_one_image_Icc_of_injOn {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    eVariationOn γ (Icc a b) ≤ μH[1] (γ '' Icc a b) :=
  eVariationOn_le_hausdorffMeasure_one_image_Icc_of_injOn_Ico hγ (hinj.mono Ico_subset_Icc_self)

/-- If a curve `γ : ℝ → X` is continuous and injective on `[a, b]`, then its total variation on
`[a, b]` is bounded above by the one-dimensional Euclidean Hausdorff measure of its trace. -/
theorem eVariationOn_le_euclideanHausdorffMeasure_one_image_Icc_of_injOn {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    eVariationOn γ (Icc a b) ≤ μHE[1] (γ '' Icc a b) := by
  simpa using eVariationOn_le_hausdorffMeasure_one_image_Icc_of_injOn hγ hinj

/-- For a curve `γ : ℝ → X` that is continuous on `[a, b]` and injective on `[a, b)`, the
one-dimensional Hausdorff measure of its trace equals its total variation on `[a, b]`. -/
theorem hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    μH[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) :=
  le_antisymm (hausdorffMeasure_one_image_Icc_le_eVariationOn hγ)
    (eVariationOn_le_hausdorffMeasure_one_image_Icc_of_injOn_Ico hγ hinj)

/-- For a curve `γ : ℝ → X` that is continuous on `[a, b]` and injective on `[a, b)`, the
one-dimensional Euclidean Hausdorff measure of its trace equals its total variation on `[a, b]`. -/
theorem euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    μHE[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) := by
  simpa using hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ hinj

/-- For a continuous injective curve (arc) `γ : ℝ → X` on `[a, b]`, the one-dimensional Hausdorff
measure of its trace equals its total variation on `[a, b]`. -/
theorem hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    μH[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) :=
  hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ (hinj.mono Ico_subset_Icc_self)

/-- For a continuous injective curve (arc) `γ : ℝ → X` on `[a, b]`, the one-dimensional Euclidean
Hausdorff measure of its trace equals its total variation on `[a, b]`. -/
theorem euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    μHE[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) := by
  simpa using hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn hγ hinj

/-- For an injective continuous curve `γ : ℝ → EuclideanSpace ℝ (Fin n)` of bounded variation on
`[a, b]`, the one-dimensional Euclidean Hausdorff measure of its trace equals its total variation
on `[a, b]`. -/
theorem euclideanHausdorffMeasure_trace_eq_eVariationOn
    {n : ℕ} {γ : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ} (_hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (_hrect : BoundedVariationOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) :
    μHE[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) :=
  euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn hγ hinj

/-- For a simple closed curve `γ : ℝ → X` on `[a, b]` (continuous on `[a, b]`, closed with
`γ a = γ b`, and injective on `[a, b)`), the one-dimensional Hausdorff measure of its trace equals
its total variation on `[a, b]`. -/
theorem hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_simpleClosed {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (_hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    μH[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) :=
  hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ hinj

/-- For a simple closed curve `γ : ℝ → X` on `[a, b]` (continuous on `[a, b]`, closed with
`γ a = γ b`, and injective on `[a, b)`), the one-dimensional Euclidean Hausdorff measure of its
trace equals its total variation on `[a, b]`. -/
theorem euclideanHausdorffMeasure_one_image_Icc_eq_eVariationOn_of_simpleClosed {γ : ℝ → X}
    {a b : ℝ} (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    μHE[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) := by
  simpa using hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_simpleClosed hγ hclosed hinj

/-- A curve `γ : ℝ → X` continuous on `[a, b]` and injective on `[a, b)` has bounded variation on
`[a, b]` if and only if its trace has finite one-dimensional Hausdorff measure. -/
theorem boundedVariationOn_iff_hausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico {γ : ℝ → X}
    {a b : ℝ} (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    BoundedVariationOn γ (Icc a b) ↔ μH[1] (γ '' Icc a b) < ⊤ := by
  rw [BoundedVariationOn, hausdorffMeasure_one_image_Icc_eq_eVariationOn_of_injOn_Ico hγ hinj,
    lt_top_iff_ne_top]

/-- A curve `γ : ℝ → X` continuous on `[a, b]` and injective on `[a, b)` has bounded variation on
`[a, b]` if and only if its trace has finite one-dimensional Euclidean Hausdorff measure. -/
theorem boundedVariationOn_iff_euclideanHausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico
    {γ : ℝ → X} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    BoundedVariationOn γ (Icc a b) ↔ μHE[1] (γ '' Icc a b) < ⊤ := by
  simpa using boundedVariationOn_iff_hausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico hγ hinj

/-- A continuous injective curve `γ : ℝ → X` on `[a, b]` has bounded variation on `[a, b]` if and
only if its trace has finite one-dimensional Hausdorff measure. -/
theorem boundedVariationOn_iff_hausdorffMeasure_one_image_Icc_lt_top {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    BoundedVariationOn γ (Icc a b) ↔ μH[1] (γ '' Icc a b) < ⊤ :=
  boundedVariationOn_iff_hausdorffMeasure_one_image_Icc_lt_top_of_injOn_Ico hγ
    (hinj.mono Ico_subset_Icc_self)

/-- A continuous injective curve `γ : ℝ → X` on `[a, b]` has bounded variation on `[a, b]` if and
only if its trace has finite one-dimensional Euclidean Hausdorff measure. -/
theorem boundedVariationOn_iff_euclideanHausdorffMeasure_one_image_Icc_lt_top {γ : ℝ → X}
    {a b : ℝ} (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    BoundedVariationOn γ (Icc a b) ↔ μHE[1] (γ '' Icc a b) < ⊤ := by
  simpa using boundedVariationOn_iff_hausdorffMeasure_one_image_Icc_lt_top hγ hinj

end InjectiveAndSimpleClosed

/-! ### Higher-dimensional Hausdorff measure and planar volume nullity of rectifiable curves -/

section Nullity

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The trace of a rectifiable continuous curve has `d`-dimensional Hausdorff measure zero for
every `d > 1`. -/
theorem hausdorffMeasure_image_Icc_eq_zero_of_one_lt {γ : ℝ → X} {a b d : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hrect : BoundedVariationOn γ (Icc a b)) (hd : 1 < d) :
    μH[d] (γ '' Icc a b) = 0 := by
  have h1 : μH[1] (γ '' Icc a b) ≠ ⊤ :=
    ((hausdorffMeasure_one_image_Icc_le_eVariationOn hγ).trans_lt hrect.lt_top).ne
  exact (hausdorffMeasure_zero_or_top hd (γ '' Icc a b)).resolve_right h1

/-- The trace of a rectifiable continuous curve has `d`-dimensional Euclidean Hausdorff measure
zero for every `d > 1`. -/
theorem euclideanHausdorffMeasure_image_Icc_eq_zero_of_one_lt {γ : ℝ → X} {a b : ℝ} {d : ℕ}
    (hγ : ContinuousOn γ (Icc a b)) (hrect : BoundedVariationOn γ (Icc a b)) (hd : 1 < d) :
    μHE[d] (γ '' Icc a b) = 0 := by
  have h1 : μHE[1] (γ '' Icc a b) ≠ ⊤ :=
    ((euclideanHausdorffMeasure_one_image_Icc_le_eVariationOn hγ).trans_lt hrect.lt_top).ne
  exact (euclideanHausdorffMeasure_zero_or_top hd (γ '' Icc a b)).resolve_right h1

/-- In any finite-dimensional real inner product space of dimension at least `2`, the trace of a
rectifiable continuous curve has Lebesgue volume zero. -/
theorem volume_image_Icc_eq_zero_of_two_le_finrank {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {γ : ℝ → E} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b))
    (hrect : BoundedVariationOn γ (Icc a b)) (hdim : 2 ≤ Module.finrank ℝ E) :
    volume (γ '' Icc a b) = 0 := by
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact euclideanHausdorffMeasure_image_Icc_eq_zero_of_one_lt hγ hrect hdim

/-- In `EuclideanSpace ℝ (Fin n)` with `2 ≤ n`, the trace of a rectifiable continuous curve has
Lebesgue volume zero. -/
theorem volume_trace_eq_zero_of_two_le {n : ℕ} (hn : 2 ≤ n) {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    {a b : ℝ} (_hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hrect : BoundedVariationOn γ (Icc a b)) :
    volume (γ '' Icc a b) = 0 :=
  volume_image_Icc_eq_zero_of_two_le_finrank hγ hrect (by simpa using hn)

/-- The trace of a rectifiable continuous curve in `ℂ` has planar Lebesgue measure zero. -/
theorem volume_trace_eq_zero {γ : ℝ → ℂ} {a b : ℝ} (_hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hrect : BoundedVariationOn γ (Icc a b)) :
    volume (γ '' Icc a b) = 0 :=
  volume_image_Icc_eq_zero_of_two_le_finrank hγ hrect
    (by simp [Complex.finrank_real_complex])

end Nullity

end TauCeti
