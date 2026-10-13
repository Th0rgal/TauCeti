/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# One-dimensional Brunn–Minkowski and Prékopa–Leindler inequalities

This file establishes the one-dimensional **Brunn–Minkowski inequality** and the one-dimensional
**Prékopa–Leindler inequality** on `ℝ`, together with the associated dilation laws, continuity of
Lebesgue measure along decreasing sequences of compact sets, and the equality characterization for
compact convex sets in `ℝ`.

## Main results

* `Real.volume_add_volume_le_of_isCompact`, `Real.volume_add_volume_le`, and
  `Real.volume_add_volume_le_of_nullMeasurableSet`: for nonempty sets `A, B ⊆ ℝ` (compact,
  Borel-measurable, or Lebesgue-measurable), `volume A + volume B ≤ volume (A + B)`.
* `Real.volume_smul_add_smul_le_of_isCompact`, `Real.volume_smul_add_smul_le`, and
  `Real.volume_smul_add_smul_le_of_nullMeasurableSet`: for `0 ≤ θ ≤ 1` and nonempty sets
  `A, B ⊆ ℝ`, `ENNReal.ofReal (1 - θ) * volume A + ENNReal.ofReal θ * volume B ≤
  volume ((1 - θ) • A + θ • B)`.
* `Convex.volume_add_eq_of_isCompact` and `Convex.volume_smul_add_smul_eq_of_isCompact`: equality
  in the one-dimensional Brunn–Minkowski inequality for nonempty compact convex sets, together with
  the positive-volume homothety-and-translation characterizations
  `Convex.exists_singleton_add_pos_smul_of_isCompact_of_volume_pos`,
  `Convex.volume_add_eq_iff_of_isCompact`, and `Convex.volume_smul_add_smul_eq_iff_of_isCompact`.
* `Real.lintegral_prekopa_leindler`, `Real.lintegral_ofReal_prekopa_leindler`, and
  `Real.integral_prekopa_leindler`: the one-dimensional Prékopa–Leindler inequality in extended
  (`ℝ≥0∞`) and real-valued Bochner (`ℝ`) forms.

## References

* H. Brunn, *Über Ovale und Eiflächen*, Dissertation, München, 1887.
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

/-! ### Elementary volume laws and measurable cores in one dimension -/

namespace MeasureTheory

/-- Every nonempty Lebesgue-measurable subset of `ℝ` contains a nonempty Borel-measurable subset
of the same volume. -/
theorem NullMeasurableSet.exists_nonempty_measurable_subset_volume_eq {A : Set ℝ}
    (hAn : A.Nonempty) (hAm : NullMeasurableSet A volume) :
    ∃ A' ⊆ A, A'.Nonempty ∧ MeasurableSet A' ∧ volume A' = volume A := by
  obtain ⟨t, hts, htm, htae⟩ := hAm.exists_measurable_subset_ae_eq
  obtain ⟨a, ha⟩ := hAn
  refine ⟨t ∪ {a}, union_subset hts (singleton_subset_iff.2 ha), by simp,
    htm.union (measurableSet_singleton a), ?_⟩
  exact le_antisymm (measure_mono (union_subset hts (singleton_subset_iff.2 ha)))
    ((measure_congr htae).symm.trans_le (measure_mono subset_union_left))

end MeasureTheory

/-- Continuity from above of Lebesgue measure on `ℝ` for an antitone sequence of compact sets. -/
theorem IsCompact.volume_iInter_of_antitone {K : ℕ → Set ℝ} (hK : ∀ n, IsCompact (K n))
    (hant : Antitone K) : volume (⋂ n, K n) = ⨅ n, volume (K n) :=
  hant.measure_iInter (fun n ↦ (hK n).nullMeasurableSet) ⟨0, (hK 0).measure_lt_top.ne⟩

namespace Real

/-- Scaling law for Lebesgue outer measure on `ℝ`. -/
theorem volume_smul (r : ℝ) (A : Set ℝ) :
    volume (r • A) = ENNReal.ofReal |r| * volume A := by
  simp [Measure.addHaar_smul]

/-- Scaling law for Lebesgue outer measure on `ℝ` by a nonnegative scalar. -/
theorem volume_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (A : Set ℝ) :
    volume (r • A) = ENNReal.ofReal r * volume A := by
  simpa using Measure.addHaar_smul_of_nonneg volume hr A

/-- Translation invariance of Lebesgue outer measure on `ℝ` under `+ᵥ`. -/
theorem volume_vadd (c : ℝ) (A : Set ℝ) : volume (c +ᵥ A) = volume A :=
  measure_vadd volume c A

/-! ### One-dimensional Brunn–Minkowski inequality -/

/-- One-dimensional **Brunn–Minkowski theorem** for compact sets. -/
theorem volume_add_volume_le_of_isCompact {A B : Set ℝ} (hAn : A.Nonempty) (hAc : IsCompact A)
    (hBn : B.Nonempty) (hBc : IsCompact B) : volume A + volume B ≤ volume (A + B) :=
  calc
    _ = volume (A + {-sSup A}) + volume (B + {-sInf B}) := by simp
    _ = volume ((A + {-sSup A}) ∪ (B + {-sInf B})) +
        volume ((A + {-sSup A}) ∩ (B + {-sInf B})) := by
      rw [measure_union_add_inter _ (hBc.add isCompact_singleton).measurableSet]
    _ ≤ volume ((A + {-sSup A}) ∪ (B + {-sInf B})) := by
      suffices (A + {-sSup A}) ∩ (B + {-sInf B}) ⊆ {0} by
        grw [this]
        simp
      refine fun x ⟨hA, hB⟩ ↦ le_antisymm ?_ ?_
      · exact nonpos_of_add_le_left <| le_csSup hAc.bddAbove <| by simpa using hA
      · exact nonneg_of_le_add_left <| csInf_le hBc.bddBelow <| by simpa using hB
    _ ≤ volume ((A + {-sSup A}) + (B + {-sInf B})) := by
      refine measure_mono <| Set.union_subset_iff.mpr ⟨?_, ?_⟩
      · exact Set.subset_add_left _ (by simpa using hBc.sInf_mem hBn)
      · exact Set.subset_add_right _ (by simpa using hAc.sSup_mem hAn)
    _ = _ := by
      rw [add_add_add_comm]
      simp

/-- One-dimensional **Brunn–Minkowski theorem** for Borel-measurable sets. -/
theorem volume_add_volume_le {A B : Set ℝ} (hAn : A.Nonempty) (hAm : MeasurableSet A)
    (hBn : B.Nonempty) (hBm : MeasurableSet B) : volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a, ha⟩ := hAn
  obtain ⟨b, hb⟩ := hBn
  by_cases hA : volume A = ∞
  · trans volume (A + {b})
    · simp [hA]
    · gcongr
      simpa using hb
  by_cases hB : volume B = ∞
  · trans volume ({a} + B)
    · simp [hB]
    · gcongr
      simpa using ha
  calc
    _ = (⨆ (K) (_ : K ⊆ A) (_ : IsCompact K), volume K) +
        (⨆ (K) (_ : K ⊆ B) (_ : IsCompact K), volume K) := by
      rw [hAm.measure_eq_iSup_isCompact_of_ne_top hA, hBm.measure_eq_iSup_isCompact_of_ne_top hB]
    _ ≤ ⨆ (K) (_ : K ⊆ A) (_ : IsCompact K) (L) (_ : L ⊆ B) (_ : IsCompact L),
        volume K + volume L := by
      simp_rw [iSup_and']
      refine ENNReal.biSup_add_biSup_le' ⟨∅, by simp⟩ ⟨∅, by simp⟩ fun K hK L hL ↦ ?_
      aesop (add safe [le_iSup_of_le])
    _ ≤ _ := by
      refine iSup₂_le fun K hKA ↦ iSup₂_le fun hK L ↦ iSup₂_le fun hLB hL ↦ ?_
      trans volume (K ∪ {a}) + volume (L ∪ {b})
      · exact add_le_add (measure_mono subset_union_left) (measure_mono subset_union_left)
      grw [volume_add_volume_le_of_isCompact (by simp) (hK.union isCompact_singleton)
        (by simp) (hL.union isCompact_singleton), Set.union_subset hKA (by simpa using ha),
        Set.union_subset hLB (by simpa using hb)]

/-- One-dimensional **Brunn–Minkowski theorem** for Lebesgue-measurable (`NullMeasurableSet`) sets,
formulated with outer measure on `A + B` without assuming `A + B` is measurable. -/
theorem volume_add_volume_le_of_nullMeasurableSet {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty) (hBm : NullMeasurableSet B volume) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨A', hA'sub, hA'n, hA'm, hA'vol⟩ := hAm.exists_nonempty_measurable_subset_volume_eq hAn
  obtain ⟨B', hB'sub, hB'n, hB'm, hB'vol⟩ := hBm.exists_nonempty_measurable_subset_volume_eq hBn
  rw [← hA'vol, ← hB'vol]
  exact (volume_add_volume_le hA'n hA'm hB'n hB'm).trans
    (measure_mono (add_subset_add hA'sub hB'sub))

/-- Real-valued one-dimensional **Brunn–Minkowski inequality** for finite-measure sets. -/
theorem measureReal_add_measureReal_le {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty) (hBm : NullMeasurableSet B volume)
    (hAB : volume (A + B) ≠ ∞) :
    volume.real A + volume.real B ≤ volume.real (A + B) := by
  have hle := volume_add_volume_le_of_nullMeasurableSet hAn hAm hBn hBm
  have hfin : volume A + volume B ≠ ∞ := ne_top_of_le_ne_top hAB hle
  have hA : volume A ≠ ∞ := (ENNReal.add_ne_top.1 hfin).1
  have hB : volume B ≠ ∞ := (ENNReal.add_ne_top.1 hfin).2
  simp only [Measure.real, ← ENNReal.toReal_add hA hB]
  exact ENNReal.toReal_mono hAB hle

/-- Scaling-and-addition form of the one-dimensional **Brunn–Minkowski inequality** for arbitrary
scalars `a, b : ℝ` and nonempty Borel-measurable sets `A, B ⊆ ℝ`. -/
theorem volume_smul_add_smul_le' {A B : Set ℝ} (a b : ℝ) (hAn : A.Nonempty)
    (hAm : MeasurableSet A) (hBn : B.Nonempty) (hBm : MeasurableSet B) :
    ENNReal.ofReal |a| * volume A + ENNReal.ofReal |b| * volume B ≤ volume (a • A + b • B) := by
  rw [← volume_smul a A, ← volume_smul b B]
  exact volume_add_volume_le hAn.smul_set (hAm.const_smul₀ a) hBn.smul_set (hBm.const_smul₀ b)

/-- Weighted one-dimensional **Brunn–Minkowski inequality** for Borel-measurable sets and
`0 ≤ θ ≤ 1`. -/
theorem volume_smul_add_smul_le {A B : Set ℝ} {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hAn : A.Nonempty) (hAm : MeasurableSet A) (hBn : B.Nonempty) (hBm : MeasurableSet B) :
    ENNReal.ofReal (1 - θ) * volume A + ENNReal.ofReal θ * volume B ≤
      volume ((1 - θ) • A + θ • B) := by
  have h1 : |1 - θ| = 1 - θ := abs_of_nonneg (sub_nonneg.2 hθ₁)
  have h2 : |θ| = θ := abs_of_nonneg hθ₀
  simpa [h1, h2] using volume_smul_add_smul_le' (1 - θ) θ hAn hAm hBn hBm

/-- Weighted one-dimensional **Brunn–Minkowski inequality** for compact sets and `0 ≤ θ ≤ 1`. -/
theorem volume_smul_add_smul_le_of_isCompact {A B : Set ℝ} {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hAn : A.Nonempty) (hAc : IsCompact A) (hBn : B.Nonempty) (hBc : IsCompact B) :
    ENNReal.ofReal (1 - θ) * volume A + ENNReal.ofReal θ * volume B ≤
      volume ((1 - θ) • A + θ • B) :=
  volume_smul_add_smul_le hθ₀ hθ₁ hAn hAc.measurableSet hBn hBc.measurableSet

/-- Weighted one-dimensional **Brunn–Minkowski inequality** for Lebesgue-measurable
(`NullMeasurableSet`) sets and `0 ≤ θ ≤ 1`, using outer measure on `(1 - θ) • A + θ • B`. -/
theorem volume_smul_add_smul_le_of_nullMeasurableSet {A B : Set ℝ} {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) (hAn : A.Nonempty) (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) :
    ENNReal.ofReal (1 - θ) * volume A + ENNReal.ofReal θ * volume B ≤
      volume ((1 - θ) • A + θ • B) := by
  obtain ⟨A', hA'sub, hA'n, hA'm, hA'vol⟩ := hAm.exists_nonempty_measurable_subset_volume_eq hAn
  obtain ⟨B', hB'sub, hB'n, hB'm, hB'vol⟩ := hBm.exists_nonempty_measurable_subset_volume_eq hBn
  rw [← hA'vol, ← hB'vol]
  exact (volume_smul_add_smul_le hθ₀ hθ₁ hA'n hA'm hB'n hB'm).trans
    (measure_mono (add_subset_add (smul_set_mono hA'sub) (smul_set_mono hB'sub)))

/-- Real-valued weighted one-dimensional **Brunn–Minkowski inequality** for `0 ≤ θ ≤ 1`. -/
theorem measureReal_smul_add_smul_le {A B : Set ℝ} {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hAn : A.Nonempty) (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) (hA : volume A ≠ ∞) (hB : volume B ≠ ∞)
    (hAB : volume ((1 - θ) • A + θ • B) ≠ ∞) :
    (1 - θ) * volume.real A + θ * volume.real B ≤ volume.real ((1 - θ) • A + θ • B) := by
  have hle := volume_smul_add_smul_le_of_nullMeasurableSet hθ₀ hθ₁ hAn hAm hBn hBm
  have h1 : ENNReal.ofReal (1 - θ) * volume A ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  have h2 : ENNReal.ofReal θ * volume B ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  have htr := ENNReal.toReal_mono hAB hle
  rwa [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.2 hθ₁), ENNReal.toReal_ofReal hθ₀] at htr

end Real

/-- Dot-notation alias for `Real.volume_add_volume_le_of_isCompact`. -/
theorem IsCompact.volume_add_volume_le {A B : Set ℝ} (hAc : IsCompact A) (hAn : A.Nonempty)
    (hBc : IsCompact B) (hBn : B.Nonempty) : volume A + volume B ≤ volume (A + B) :=
  Real.volume_add_volume_le_of_isCompact hAn hAc hBn hBc

/-! ### Compact convex sets and equality in one-dimensional Brunn–Minkowski -/

/-- Every nonempty compact convex subset of `ℝ` is the closed interval `[sInf A, sSup A]`. -/
theorem Convex.eq_Icc_of_isCompact {A : Set ℝ} (hAn : A.Nonempty) (hAc : IsCompact A)
    (hAconv : Convex ℝ A) : A = Icc (sInf A) (sSup A) := by
  refine Subset.antisymm (fun x hx ↦ ⟨csInf_le hAc.bddBelow hx, le_csSup hAc.bddAbove hx⟩) ?_
  exact hAconv.ordConnected.out (hAc.sInf_mem hAn) (hAc.sSup_mem hAn)

/-- The volume of a nonempty compact convex subset of `ℝ` is `sSup A - sInf A`. -/
theorem Convex.volume_eq_of_isCompact {A : Set ℝ} (hAn : A.Nonempty) (hAc : IsCompact A)
    (hAconv : Convex ℝ A) : volume A = ENNReal.ofReal (sSup A - sInf A) := by
  conv_lhs => rw [hAconv.eq_Icc_of_isCompact hAn hAc, Real.volume_Icc]

/-- A compact convex subset of `ℝ` has nonempty interior if and only if it has positive volume. -/
theorem Convex.nonempty_interior_iff_volume_pos_of_isCompact {A : Set ℝ} (hAc : IsCompact A)
    (hAconv : Convex ℝ A) : (interior A).Nonempty ↔ 0 < volume A := by
  rcases A.eq_empty_or_nonempty with rfl | hAn
  · simp
  · rw [hAconv.eq_Icc_of_isCompact hAn hAc, interior_Icc, nonempty_Ioo, Real.volume_Icc,
      ENNReal.ofReal_pos, sub_pos]

/-- For nonempty compact convex subsets of `ℝ`, equality always holds in the one-dimensional
Brunn–Minkowski inequality. -/
theorem Convex.volume_add_eq_of_isCompact {A B : Set ℝ} (hAn : A.Nonempty) (hAc : IsCompact A)
    (hAconv : Convex ℝ A) (hBn : B.Nonempty) (hBc : IsCompact B) (hBconv : Convex ℝ B) :
    volume (A + B) = volume A + volume B := by
  have hA_le : sInf A ≤ sSup A := csInf_le hAc.bddBelow (hAc.sSup_mem hAn)
  have hB_le : sInf B ≤ sSup B := csInf_le hBc.bddBelow (hBc.sSup_mem hBn)
  rw [hAconv.eq_Icc_of_isCompact hAn hAc, hBconv.eq_Icc_of_isCompact hBn hBc,
    Set.Icc_add_Icc hA_le hB_le, Real.volume_Icc, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_add (sub_nonneg.2 hA_le) (sub_nonneg.2 hB_le)]
  congr 1
  ring

/-- For nonempty compact convex subsets of `ℝ` and `0 ≤ θ ≤ 1`, equality always holds in the
weighted one-dimensional Brunn–Minkowski inequality. -/
theorem Convex.volume_smul_add_smul_eq_of_isCompact {A B : Set ℝ} {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) (hAn : A.Nonempty) (hAc : IsCompact A) (hAconv : Convex ℝ A)
    (hBn : B.Nonempty) (hBc : IsCompact B) (hBconv : Convex ℝ B) :
    volume ((1 - θ) • A + θ • B) =
      ENNReal.ofReal (1 - θ) * volume A + ENNReal.ofReal θ * volume B := by
  rw [(hAconv.smul (1 - θ)).volume_add_eq_of_isCompact hAn.smul_set
    (hAc.smul (1 - θ)) hBn.smul_set (hBc.smul θ) (hBconv.smul θ),
    Real.volume_smul_of_nonneg (sub_nonneg.2 hθ₁), Real.volume_smul_of_nonneg hθ₀]

/-- Any two positive-volume compact convex subsets of `ℝ` are related by a positive homothety and
translation `B = {c} + r • A`. -/
theorem Convex.exists_singleton_add_pos_smul_of_isCompact_of_volume_pos {A B : Set ℝ}
    (hAc : IsCompact A) (hAconv : Convex ℝ A) (hApos : 0 < volume A)
    (hBc : IsCompact B) (hBconv : Convex ℝ B) (hBpos : 0 < volume B) :
    ∃ c r : ℝ, 0 < r ∧ B = {c} + r • A := by
  have hAn : A.Nonempty := nonempty_of_measure_ne_zero hApos.ne'
  have hBn : B.Nonempty := nonempty_of_measure_ne_zero hBpos.ne'
  have hA_lt : sInf A < sSup A := by
    rwa [hAconv.volume_eq_of_isCompact hAn hAc, ENNReal.ofReal_pos, sub_pos] at hApos
  have hB_lt : sInf B < sSup B := by
    rwa [hBconv.volume_eq_of_isCompact hBn hBc, ENNReal.ofReal_pos, sub_pos] at hBpos
  set r : ℝ := (sSup B - sInf B) / (sSup A - sInf A)
  have hr : 0 < r := div_pos (sub_pos.2 hB_lt) (sub_pos.2 hA_lt)
  set c : ℝ := sInf B - r * sInf A
  refine ⟨c, r, hr, ?_⟩
  rw [hAconv.eq_Icc_of_isCompact hAn hAc, hBconv.eq_Icc_of_isCompact hBn hBc]
  ext x
  simp only [singleton_add, mem_image, mem_smul_set, smul_eq_mul]
  refine ⟨fun ⟨hx₁, hx₂⟩ ↦ ?_, ?_⟩
  · refine ⟨x - c, ⟨(x - c) / r, ⟨?_, ?_⟩, mul_div_cancel₀ _ hr.ne'⟩, add_sub_cancel c x⟩
    · rw [le_div_iff₀ hr]
      linarith [c]
    · rw [div_le_iff₀ hr]
      have hrA : sSup A * r = sSup B - sInf B + sInf A * r := by
        dsimp [r]
        field_simp [(sub_pos.2 hA_lt).ne']
        ring
      linarith [c, hrA]
  · rintro ⟨_, ⟨y, ⟨hy₁, hy₂⟩, rfl⟩, rfl⟩
    have hrA : r * sSup A = sSup B - sInf B + r * sInf A := by
      dsimp [r]
      field_simp [(sub_pos.2 hA_lt).ne']
      ring
    constructor
    · nlinarith [c]
    · nlinarith [c, hrA]

/-- For positive-volume compact convex subsets `A, B ⊆ ℝ`, equality in the one-dimensional
Brunn–Minkowski inequality holds if and only if `B = {c} + r • A` for some `c : ℝ` and `r > 0`. -/
theorem Convex.volume_add_eq_iff_of_isCompact {A B : Set ℝ}
    (hAc : IsCompact A) (hAconv : Convex ℝ A) (hApos : 0 < volume A)
    (hBc : IsCompact B) (hBconv : Convex ℝ B) (hBpos : 0 < volume B) :
    volume (A + B) = volume A + volume B ↔ ∃ c r : ℝ, 0 < r ∧ B = {c} + r • A :=
  ⟨fun _ ↦ hAconv.exists_singleton_add_pos_smul_of_isCompact_of_volume_pos
    hAc hApos hBc hBconv hBpos,
   fun _ ↦ hAconv.volume_add_eq_of_isCompact (nonempty_of_measure_ne_zero hApos.ne') hAc
    (nonempty_of_measure_ne_zero hBpos.ne') hBc hBconv⟩

/-- For positive-volume compact convex subsets `A, B ⊆ ℝ` and `0 ≤ θ ≤ 1`, equality in the weighted
one-dimensional Brunn–Minkowski inequality holds if and only if `B = {c} + r • A` for some `c : ℝ`
and `r > 0`. -/
theorem Convex.volume_smul_add_smul_eq_iff_of_isCompact {A B : Set ℝ} {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hAc : IsCompact A) (hAconv : Convex ℝ A) (hApos : 0 < volume A)
    (hBc : IsCompact B) (hBconv : Convex ℝ B) (hBpos : 0 < volume B) :
    volume ((1 - θ) • A + θ • B) =
      ENNReal.ofReal (1 - θ) * volume A + ENNReal.ofReal θ * volume B ↔
      ∃ c r : ℝ, 0 < r ∧ B = {c} + r • A :=
  ⟨fun _ ↦ hAconv.exists_singleton_add_pos_smul_of_isCompact_of_volume_pos
    hAc hApos hBc hBconv hBpos,
   fun _ ↦ hAconv.volume_smul_add_smul_eq_of_isCompact hθ₀ hθ₁
    (nonempty_of_measure_ne_zero hApos.ne') hAc (nonempty_of_measure_ne_zero hBpos.ne') hBc hBconv⟩

/-! ### One-dimensional Prékopa–Leindler inequality -/

namespace ENNReal

/-- Weighted arithmetic-geometric mean inequality for two extended nonnegative real numbers. -/
theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw : w₁ + w₂ = 1) (p₁ p₂ : ℝ≥0∞) :
    p₁ ^ w₁ * p₂ ^ w₂ ≤ ENNReal.ofReal w₁ * p₁ + ENNReal.ofReal w₂ * p₂ := by
  rcases eq_or_ne w₁ 0 with rfl | hw₁₀
  · have hw₂₁ : w₂ = 1 := by linarith
    subst hw₂₁
    simp
  rcases eq_or_ne w₂ 0 with rfl | hw₂₀
  · have hw₁₁ : w₁ = 1 := by linarith
    subst hw₁₁
    simp
  have hw₁_pos : 0 < w₁ := lt_of_le_of_ne hw₁ (Ne.symm hw₁₀)
  have hw₂_pos : 0 < w₂ := lt_of_le_of_ne hw₂ (Ne.symm hw₂₀)
  rcases eq_or_ne p₁ 0 with rfl | hp₁₀
  · simp [ENNReal.zero_rpow_of_pos hw₁_pos]
  rcases eq_or_ne p₂ 0 with rfl | hp₂₀
  · simp [ENNReal.zero_rpow_of_pos hw₂_pos]
  rcases eq_or_ne p₁ ⊤ with rfl | hp₁_top
  · have : ENNReal.ofReal w₁ * ⊤ = ⊤ := ENNReal.mul_top (by simpa using hw₁_pos)
    simp [this]
  rcases eq_or_ne p₂ ⊤ with rfl | hp₂_top
  · have : ENNReal.ofReal w₂ * ⊤ = ⊤ := ENNReal.mul_top (by simpa using hw₂_pos)
    simp [this]
  lift p₁ to ℝ≥0 using hp₁_top
  lift p₂ to ℝ≥0 using hp₂_top
  rw [← ENNReal.coe_rpow_of_nonneg _ hw₁, ← ENNReal.coe_rpow_of_nonneg _ hw₂,
    ← ENNReal.coe_mul, ENNReal.ofReal_eq_coe_nnreal hw₁, ENNReal.ofReal_eq_coe_nnreal hw₂,
    ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  push_cast
  exact Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂ p₁.coe_nonneg p₂.coe_nonneg hw

end ENNReal

namespace Real

private theorem lintegral_eq_lintegral_meas_lt_of_ne_top {u : ℝ → ℝ≥0∞}
    (hu : AEMeasurable u volume) (hfin : ∀ x, u x ≠ ⊤) :
    ∫⁻ x, u x = ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < u x} := by
  have h1 : ∫⁻ x, u x = ∫⁻ x, ENNReal.ofReal (u x).toReal :=
    lintegral_congr fun x ↦ (ENNReal.ofReal_toReal (hfin x)).symm
  rw [h1, lintegral_eq_lintegral_meas_lt volume
    (Eventually.of_forall fun x ↦ ENNReal.toReal_nonneg) hu.ennreal_toReal]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  congr 1; ext x
  exact (ENNReal.ofReal_lt_iff_lt_toReal (mem_Ioi.mp ht).le (hfin x)).symm

private theorem lintegral_prekopa_leindler_of_iSup_eq_one {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hh : AEMeasurable h volume) (hf_le : ∀ x, f x ≤ 1) (hg_le : ∀ y, g y ≤ 1)
    (hh_le : ∀ z, h z ≤ 1) (hf_sup : ⨆ x, f x = 1) (hg_sup : ⨆ y, g y = 1)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) * x + θ * y)) :
    (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ y, g y) ^ θ ≤ ∫⁻ z, h z := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  have hlevel (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (1 - θ) * volume {x | ENNReal.ofReal t < f x} +
        ENNReal.ofReal θ * volume {y | ENNReal.ofReal t < g y} ≤
        volume {z | ENNReal.ofReal t < h z} := by
    rcases lt_or_ge t 1 with ht₁ | ht₁
    · have ht_lt_one : ENNReal.ofReal t < 1 := by
        rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
      have hAn : {x | ENNReal.ofReal t < f x}.Nonempty := by
        obtain ⟨x, hx⟩ := lt_iSup_iff.1 (ht_lt_one.trans_eq hf_sup.symm)
        exact ⟨x, hx⟩
      have hBn : {y | ENNReal.ofReal t < g y}.Nonempty := by
        obtain ⟨y, hy⟩ := lt_iSup_iff.1 (ht_lt_one.trans_eq hg_sup.symm)
        exact ⟨y, hy⟩
      have hAm : NullMeasurableSet {x | ENNReal.ofReal t < f x} volume :=
        hf.nullMeasurable measurableSet_Ioi
      have hBm : NullMeasurableSet {y | ENNReal.ofReal t < g y} volume :=
        hg.nullMeasurable measurableSet_Ioi
      have hsub :
          (1 - θ) • {x | ENNReal.ofReal t < f x} + θ • {y | ENNReal.ofReal t < g y} ⊆
            {z | ENNReal.ofReal t < h z} := by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
        simp only [mem_ofPred] at hx hy ⊢
        have hx' : ENNReal.ofReal t ^ (1 - θ) < f x ^ (1 - θ) :=
          (ENNReal.orderIsoRpow (1 - θ) h1θ).lt_iff_lt.2 hx
        have hy' : ENNReal.ofReal t ^ θ ≤ g y ^ θ :=
          ENNReal.rpow_le_rpow hy.le hθ₀.le
        have ht_pos : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
        have ht_rpow_pos : ENNReal.ofReal t ^ θ ≠ 0 :=
          (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 ht) ENNReal.ofReal_ne_top).ne'
        have ht_rpow_top : ENNReal.ofReal t ^ θ ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg hθ₀.le ENNReal.ofReal_ne_top
        calc ENNReal.ofReal t
            = ENNReal.ofReal t ^ (1 - θ + θ) := by simp
          _ = ENNReal.ofReal t ^ (1 - θ) * ENNReal.ofReal t ^ θ :=
              ENNReal.rpow_add (1 - θ) θ ht_pos ENNReal.ofReal_ne_top
          _ < f x ^ (1 - θ) * ENNReal.ofReal t ^ θ := by
              rw [mul_comm, mul_comm (f x ^ (1 - θ))]
              exact ENNReal.mul_lt_mul_right ht_rpow_pos ht_rpow_top hx'
          _ ≤ f x ^ (1 - θ) * g y ^ θ := mul_le_mul' le_rfl hy'
          _ ≤ h ((1 - θ) * x + θ * y) := hle x y
      exact (volume_smul_add_smul_le_of_nullMeasurableSet hθ₀.le hθ₁.le hAn hAm hBn hBm).trans
        (measure_mono hsub)
    · have ht_ge_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal t := by
        rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff ht.le]
      have hA_empty : {x | ENNReal.ofReal t < f x} = ∅ :=
        eq_empty_of_forall_notMem fun x hx ↦ not_le_of_gt hx ((hf_le x).trans ht_ge_one)
      have hB_empty : {y | ENNReal.ofReal t < g y} = ∅ :=
        eq_empty_of_forall_notMem fun y hy ↦ not_le_of_gt hy ((hg_le y).trans ht_ge_one)
      simp [hA_empty, hB_empty]
  have hmeas_f : Measurable (fun t : ℝ ↦ volume {x | ENNReal.ofReal t < f x}) :=
    Antitone.measurable fun t₁ t₂ h ↦ measure_mono fun x hx ↦
      (ENNReal.ofReal_le_ofReal h).trans_lt hx
  have hmeas_g : Measurable (fun t : ℝ ↦ volume {y | ENNReal.ofReal t < g y}) :=
    Antitone.measurable fun t₁ t₂ h ↦ measure_mono fun y hy ↦
      (ENNReal.ofReal_le_ofReal h).trans_lt hy
  have hint_le :
      ENNReal.ofReal (1 - θ) * (∫⁻ x, f x) + ENNReal.ofReal θ * (∫⁻ y, g y) ≤ ∫⁻ z, h z := by
    rw [lintegral_eq_lintegral_meas_lt_of_ne_top hf
        (fun x ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hf_le x)),
      lintegral_eq_lintegral_meas_lt_of_ne_top hg
        (fun y ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hg_le y)),
      lintegral_eq_lintegral_meas_lt_of_ne_top hh
        (fun z ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hh_le z)),
      ← lintegral_const_mul _ hmeas_f, ← lintegral_const_mul _ hmeas_g,
      ← lintegral_add_left (hmeas_f.const_mul _)]
    exact setLIntegral_mono' measurableSet_Ioi fun t ht ↦ hlevel t ht
  exact (ENNReal.geom_mean_le_arith_mean2_weighted h1θ.le hθ₀.le (sub_add_cancel 1 θ)
    (∫⁻ x, f x) (∫⁻ y, g y)).trans hint_le

private theorem lintegral_prekopa_leindler_of_iSup_ne_top {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hh : AEMeasurable h volume) (hM_top : ⨆ x, f x ≠ ⊤) (hN_top : ⨆ y, g y ≠ ⊤)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) * x + θ * y)) :
    (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ y, g y) ^ θ ≤ ∫⁻ z, h z := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  set M := ⨆ x, f x
  set N := ⨆ y, g y
  rcases eq_or_ne M 0 with hM₀ | hM₀
  · have hf₀ : ∀ x, f x = 0 := ENNReal.iSup_eq_zero.1 hM₀
    simp [hf₀, ENNReal.zero_rpow_of_pos h1θ]
  rcases eq_or_ne N 0 with hN₀ | hN₀
  · have hg₀ : ∀ y, g y = 0 := ENNReal.iSup_eq_zero.1 hN₀
    simp [hg₀, ENNReal.zero_rpow_of_pos hθ₀]
  set K := M ^ (1 - θ) * N ^ θ
  have hM_rpow_pos : M ^ (1 - θ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hM₀) hM_top).ne'
  have hM_rpow_top : M ^ (1 - θ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg h1θ.le hM_top
  have hN_rpow_pos : N ^ θ ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hN₀) hN_top).ne'
  have hN_rpow_top : N ^ θ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hθ₀.le hN_top
  have hK₀ : K ≠ 0 := mul_ne_zero hM_rpow_pos hN_rpow_pos
  have hK_top : K ≠ ⊤ := ENNReal.mul_ne_top hM_rpow_top hN_rpow_top
  set f₁ : ℝ → ℝ≥0∞ := fun x ↦ M⁻¹ * f x
  set g₁ : ℝ → ℝ≥0∞ := fun y ↦ N⁻¹ * g y
  set h₁ : ℝ → ℝ≥0∞ := fun z ↦ min (K⁻¹ * h z) 1
  have hf₁_le (x : ℝ) : f₁ x ≤ 1 := by
    calc M⁻¹ * f x ≤ M⁻¹ * M := mul_le_mul' le_rfl (le_iSup f x)
      _ = 1 := ENNReal.inv_mul_cancel hM₀ hM_top
  have hg₁_le (y : ℝ) : g₁ y ≤ 1 := by
    calc N⁻¹ * g y ≤ N⁻¹ * N := mul_le_mul' le_rfl (le_iSup g y)
      _ = 1 := ENNReal.inv_mul_cancel hN₀ hN_top
  have hh₁_le (z : ℝ) : h₁ z ≤ 1 := min_le_right _ _
  have hf₁_sup : ⨆ x, f₁ x = 1 := by
    rw [← ENNReal.mul_iSup, ENNReal.inv_mul_cancel hM₀ hM_top]
  have hg₁_sup : ⨆ y, g₁ y = 1 := by
    rw [← ENNReal.mul_iSup, ENNReal.inv_mul_cancel hN₀ hN_top]
  have hK_inv : K⁻¹ = (M⁻¹) ^ (1 - θ) * (N⁻¹) ^ θ := by
    rw [ENNReal.mul_inv (Or.inl hM_rpow_pos) (Or.inl hM_rpow_top),
      ENNReal.inv_rpow, ENNReal.inv_rpow]
  have hle₁ (x y : ℝ) : f₁ x ^ (1 - θ) * g₁ y ^ θ ≤ h₁ ((1 - θ) * x + θ * y) := by
    refine le_min ?_ ?_
    · rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ.le, ENNReal.mul_rpow_of_nonneg _ _ hθ₀.le,
        mul_mul_mul_comm, ← hK_inv]
      exact mul_le_mul' le_rfl (hle x y)
    · calc f₁ x ^ (1 - θ) * g₁ y ^ θ
          ≤ 1 ^ (1 - θ) * 1 ^ θ :=
            mul_le_mul' (ENNReal.rpow_le_rpow (hf₁_le x) h1θ.le)
              (ENNReal.rpow_le_rpow (hg₁_le y) hθ₀.le)
        _ = 1 := by simp
  have hmain := lintegral_prekopa_leindler_of_iSup_eq_one hθ₀ hθ₁
    (hf.const_mul M⁻¹) (hg.const_mul N⁻¹) ((hh.const_mul K⁻¹).min aemeasurable_const)
    hf₁_le hg₁_le hh₁_le hf₁_sup hg₁_sup hle₁
  have hmain' :
      K⁻¹ * ((∫⁻ x, f x) ^ (1 - θ) * (∫⁻ y, g y) ^ θ) ≤ K⁻¹ * ∫⁻ z, h z := by
    calc K⁻¹ * ((∫⁻ x, f x) ^ (1 - θ) * (∫⁻ y, g y) ^ θ)
        = (∫⁻ x, f₁ x) ^ (1 - θ) * (∫⁻ y, g₁ y) ^ θ := by
          rw [lintegral_const_mul'' M⁻¹ hf, lintegral_const_mul'' N⁻¹ hg,
            ENNReal.mul_rpow_of_nonneg _ _ h1θ.le, ENNReal.mul_rpow_of_nonneg _ _ hθ₀.le,
            mul_mul_mul_comm, ← hK_inv]
      _ ≤ ∫⁻ z, h₁ z := hmain
      _ ≤ ∫⁻ z, K⁻¹ * h z := lintegral_mono fun z ↦ min_le_left _ _
      _ = K⁻¹ * ∫⁻ z, h z := lintegral_const_mul'' K⁻¹ hh
  have hmul := mul_le_mul' (le_refl K) hmain'
  simp only [← mul_assoc, ENNReal.mul_inv_cancel hK₀ hK_top, one_mul] at hmul
  exact hmul

private theorem iSup_min_natCast (a : ℝ≥0∞) : (⨆ n : ℕ, min a n) = a := by
  refine le_antisymm (iSup_le fun n ↦ min_le_left _ _) ?_
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [ENNReal.iSup_natCast]
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (by simp [hn.le])

/-- **One-dimensional Prékopa–Leindler inequality** in extended nonnegative form: if `0 < θ < 1`
and `f, g, h : ℝ → ℝ≥0∞` are a.e.-measurable functions satisfying
`f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) * x + θ * y)` for all `x, y : ℝ`, then
`(∫⁻ x, f x) ^ (1 - θ) * (∫⁻ y, g y) ^ θ ≤ ∫⁻ z, h z`. -/
theorem lintegral_prekopa_leindler {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hh : AEMeasurable h volume)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) * x + θ * y)) :
    (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ y, g y) ^ θ ≤ ∫⁻ z, h z := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  set fn : ℕ → ℝ → ℝ≥0∞ := fun n x ↦ min (f x) n
  set gn : ℕ → ℝ → ℝ≥0∞ := fun n y ↦ min (g y) n
  have hfn_m (n : ℕ) : AEMeasurable (fn n) volume := hf.min aemeasurable_const
  have hgn_m (n : ℕ) : AEMeasurable (gn n) volume := hg.min aemeasurable_const
  have hfn_mono : Monotone fn := fun m n hmn x ↦ min_le_min_left (f x) (Nat.cast_le.2 hmn)
  have hgn_mono : Monotone gn := fun m n hmn y ↦ min_le_min_left (g y) (Nat.cast_le.2 hmn)
  have hfn_sup (x : ℝ) : ⨆ n : ℕ, fn n x = f x := iSup_min_natCast (f x)
  have hgn_sup (y : ℝ) : ⨆ n : ℕ, gn n y = g y := iSup_min_natCast (g y)
  have hn_ineq (n : ℕ) :
      (∫⁻ x, fn n x) ^ (1 - θ) * (∫⁻ y, gn n y) ^ θ ≤ ∫⁻ z, h z := by
    have hM : ⨆ x, fn n x ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (iSup_le fun x ↦ min_le_right _ _)
    have hN : ⨆ y, gn n y ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (iSup_le fun y ↦ min_le_right _ _)
    refine lintegral_prekopa_leindler_of_iSup_ne_top hθ₀ hθ₁ (hfn_m n) (hgn_m n) hh hM hN
      fun x y ↦ ?_
    exact (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) h1θ.le)
      (ENNReal.rpow_le_rpow (min_le_left _ _) hθ₀.le)).trans (hle x y)
  have hint_f : ∫⁻ x, f x = ⨆ n, ∫⁻ x, fn n x := by
    rw [← lintegral_iSup' hfn_m (Eventually.of_forall fun x m n hmn ↦ hfn_mono hmn x)]
    exact lintegral_congr fun x ↦ (hfn_sup x).symm
  have hint_g : ∫⁻ y, g y = ⨆ n, ∫⁻ y, gn n y := by
    rw [← lintegral_iSup' hgn_m (Eventually.of_forall fun y m n hmn ↦ hgn_mono hmn y)]
    exact lintegral_congr fun y ↦ (hgn_sup y).symm
  have hrpow_f : (∫⁻ x, f x) ^ (1 - θ) = ⨆ n, (∫⁻ x, fn n x) ^ (1 - θ) := by
    rw [hint_f]
    exact (ENNReal.orderIsoRpow (1 - θ) h1θ).map_iSup _
  have hrpow_g : (∫⁻ y, g y) ^ θ = ⨆ n, (∫⁻ y, gn n y) ^ θ := by
    rw [hint_g]
    exact (ENNReal.orderIsoRpow θ hθ₀).map_iSup _
  rw [hrpow_f, hrpow_g, ENNReal.iSup_mul]
  refine iSup_le fun i ↦ ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j ↦ ?_
  have hi : (∫⁻ x, fn i x) ^ (1 - θ) ≤ (∫⁻ x, fn (max i j) x) ^ (1 - θ) :=
    ENNReal.rpow_le_rpow (lintegral_mono (hfn_mono (le_max_left i j))) h1θ.le
  have hj : (∫⁻ y, gn j y) ^ θ ≤ (∫⁻ y, gn (max i j) y) ^ θ :=
    ENNReal.rpow_le_rpow (lintegral_mono (hgn_mono (le_max_right i j))) hθ₀.le
  exact (mul_le_mul' hi hj).trans (hn_ineq (max i j))

/-- **One-dimensional Prékopa–Leindler inequality** for real-valued nonnegative functions via
`ENNReal.ofReal`. -/
theorem lintegral_ofReal_prekopa_leindler {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : ℝ → ℝ} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hh : AEMeasurable h volume) (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ y, 0 ≤ g y)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) * x + θ * y)) :
    (∫⁻ x, ENNReal.ofReal (f x)) ^ (1 - θ) * (∫⁻ y, ENNReal.ofReal (g y)) ^ θ ≤
      ∫⁻ z, ENNReal.ofReal (h z) := by
  refine lintegral_prekopa_leindler hθ₀ hθ₁ hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal
    fun x y ↦ ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (hf_nn x) (sub_pos.2 hθ₁).le,
    ENNReal.ofReal_rpow_of_nonneg (hg_nn y) hθ₀.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf_nn x) _)]
  exact ENNReal.ofReal_le_ofReal (hle x y)

/-- **One-dimensional Prékopa–Leindler inequality** for Bochner-integrable nonnegative real-valued
functions. -/
theorem integral_prekopa_leindler {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : ℝ → ℝ} (hf : Integrable f volume) (hg : Integrable g volume)
    (hh : Integrable h volume) (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ y, 0 ≤ g y)
    (hle : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) * x + θ * y)) :
    (∫ x, f x) ^ (1 - θ) * (∫ y, g y) ^ θ ≤ ∫ z, h z := by
  have h1θ : 0 ≤ 1 - θ := (sub_pos.2 hθ₁).le
  have hh_nn (z : ℝ) : 0 ≤ h z := by
    have hz : (1 - θ) * z + θ * z = z := by ring
    rw [← hz]
    exact (mul_nonneg (Real.rpow_nonneg (hf_nn z) _) (Real.rpow_nonneg (hg_nn z) _)).trans
      (hle z z)
  have hf_int : 0 ≤ ∫ x, f x := integral_nonneg hf_nn
  have hg_int : 0 ≤ ∫ y, g y := integral_nonneg hg_nn
  have hh_int : 0 ≤ ∫ z, h z := integral_nonneg hh_nn
  have h_enn := lintegral_ofReal_prekopa_leindler hθ₀ hθ₁
    hf.aemeasurable hg.aemeasurable hh.aemeasurable hf_nn hg_nn hle
  rw [← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf_nn),
    ← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg_nn),
    ← ofReal_integral_eq_lintegral_ofReal hh (Eventually.of_forall hh_nn),
    ENNReal.ofReal_rpow_of_nonneg hf_int h1θ,
    ENNReal.ofReal_rpow_of_nonneg hg_int hθ₀.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hf_int _)] at h_enn
  exact (ENNReal.ofReal_le_ofReal_iff hh_int).1 h_enn

end Real
