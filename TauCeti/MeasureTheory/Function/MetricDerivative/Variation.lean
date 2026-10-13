/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MetricDerivative.Basic

/-!
# Total variation and the integral of the metric derivative

For any curve `γ : ℝ → X` in an extended pseudometric space, the lower Lebesgue integral of its
metric derivative over `[a, b]` is bounded above by its total variation `eVariationOn γ (Icc a b)`.
When `γ` has finite variation on `[a, b]`, its signed variation function
`V(t) = variationOnFromTo γ (uIcc a b) a t` is monotone on `[a, b]` and dominates the distances
along `γ`, so `metricDerivative γ t ≤ ‖deriv V t‖ₑ` almost everywhere on `[a, b]`; integrating
this inequality and bounding the integral of the derivative of a monotone function by its total
increment yields `∫⁻ t in Icc a b, metricDerivative γ t ≤ eVariationOn γ (Icc a b)`.

For an absolutely continuous curve `γ : ℝ → X` in a pseudometric space, summing the fundamental
theorem bound `edist (γ s) (γ u) ≤ ∫⁻ t in Ι s u, metricDerivative γ t` over finite partitions
gives the reverse inequality. Consequently:

* the total variation `eVariationOn γ (Icc a b)` equals `∫⁻ t in Icc a b, metricDerivative γ t`;
* the signed variation function `t ↦ variationOnFromTo γ (uIcc a b) c t` is itself absolutely
  continuous on `uIcc a b`, with
  `metricDerivative γ t = ‖deriv (variationOnFromTo γ (uIcc a b) a) t‖ₑ` almost everywhere on
  `uIcc a b`, and `deriv (variationOnFromTo γ (Icc a b) a) t = (metricDerivative γ t).toReal`
  almost everywhere on `Icc a b` when `a ≤ b`;
* the real-valued speed `t ↦ (metricDerivative γ t).toReal` is interval integrable on `a..b` and
  its interval integral recovers `variationOnFromTo γ (uIcc a b) a b` (and
  `(eVariationOn γ (Icc a b)).toReal` when `a ≤ b`).

In a real normed space, the metric derivative coincides with `‖deriv γ t‖ₑ` at every point where `γ`
is differentiable. For curves in a finite-dimensional real normed space, bounded variation implies
almost everywhere differentiability on the interval, so the metric derivative equals `‖deriv γ t‖ₑ`
almost everywhere and the total variation of an absolutely continuous curve equals
`∫⁻ t in Icc a b, ‖deriv γ t‖ₑ` (and `∫ t in a..b, ‖deriv γ t‖` in real-valued form).

## Main results

* `TauCeti.lintegral_metricDerivative_le_eVariationOn` and
  `TauCeti.lintegral_metricDerivative_uIoc_le_eVariationOn_uIcc`: the integral of the metric
  derivative is at most the total variation, on `Icc a b` and `uIcc a b`.
* `AbsolutelyContinuousOnInterval.eVariationOn_eq_lintegral_metricDerivative` and
  `AbsolutelyContinuousOnInterval.eVariationOn_uIcc_eq_lintegral_metricDerivative`: for an
  absolutely continuous curve, total variation equals the integral of the metric derivative.
* `AbsolutelyContinuousOnInterval.edist_variationOnFromTo_eq_lintegral_metricDerivative` and
  `AbsolutelyContinuousOnInterval.variationOnFromTo`: the signed variation function of an
  absolutely continuous curve is absolutely continuous, with increments given by the integral of
  the metric derivative.
* `AbsolutelyContinuousOnInterval.ae_metricDerivative_eq_enorm_deriv_variationOnFromTo` and
  `AbsolutelyContinuousOnInterval.ae_deriv_variationOnFromTo_eq_toReal_metricDerivative`: the
  metric derivative of an absolutely continuous curve agrees almost everywhere with the derivative
  of its variation function.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_toReal_metricDerivative`,
  `AbsolutelyContinuousOnInterval.variationOnFromTo_eq_integral_toReal_metricDerivative`,
  `AbsolutelyContinuousOnInterval.toReal_eVariationOn_eq_integral_toReal_metricDerivative`, and
  `AbsolutelyContinuousOnInterval.eVariationOn_eq_ofReal_integral_toReal_metricDerivative`:
  interval integrability and interval-integral formulas for the real-valued metric derivative.
* `BoundedVariationOn.ae_metricDerivative_eq_enorm_deriv`,
  `TauCeti.lintegral_enorm_deriv_le_eVariationOn`,
  `AbsolutelyContinuousOnInterval.eVariationOn_eq_lintegral_enorm_deriv`, and
  `AbsolutelyContinuousOnInterval.toReal_eVariationOn_eq_integral_norm_deriv`: specialization to
  curves in finite-dimensional real normed spaces.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 1.1.2.
* G. Leoni, *A First Course in Sobolev Spaces*, 2nd ed., American Mathematical Society 2017,
  Chapter 3.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Interval

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- For any curve in an extended pseudometric space, the lower Lebesgue integral of its metric
derivative over `[a, b]` is at most its total variation on `[a, b]`. -/
theorem lintegral_metricDerivative_le_eVariationOn (γ : ℝ → X) (a b : ℝ) :
    ∫⁻ t in Icc a b, metricDerivative γ t ≤ eVariationOn γ (Icc a b) := by
  by_cases hab : a ≤ b
  · by_cases hγ : BoundedVariationOn γ (Icc a b)
    · have hγ' : BoundedVariationOn γ (uIcc a b) := by rwa [uIcc_of_le hab]
      set V := variationOnFromTo γ (uIcc a b) a
      have hVmono : MonotoneOn V (Icc a b) := by
        simpa [V, uIcc_of_le hab] using
          variationOnFromTo.monotoneOn hγ'.locallyBoundedVariationOn left_mem_uIcc
      obtain ⟨G, hGf, hG, hG'⟩ := hVmono.exists_tendsto_deriv_liminf_lintegral_enorm_le hab
      have hle₁ : ∫⁻ t in Icc a b, metricDerivative γ t ≤ ∫⁻ t in Icc a b, ‖deriv V t‖ₑ := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 ?_)
        filter_upwards [hγ'.ae_metricDerivative_le_enorm_deriv_variationOnFromTo] with t ht hmem
        exact ht (by rwa [uIcc_of_le hab])
      have hle₂ : ∫⁻ t in Icc a b, ‖deriv V t‖ₑ ≤ ENNReal.ofReal (V b - V a) :=
        (lintegral_enorm_le_liminf_of_tendsto hGf fun n ↦ (hG n).aemeasurable.enorm).trans hG'
      have hVa : V a = 0 := variationOnFromTo.self _ _ _
      have hVb : V b = (eVariationOn γ (Icc a b)).toReal := by
        simp [V, variationOnFromTo.eq_of_le _ _ hab, uIcc_of_le hab]
      calc
        ∫⁻ t in Icc a b, metricDerivative γ t ≤ ∫⁻ t in Icc a b, ‖deriv V t‖ₑ := hle₁
        _ ≤ ENNReal.ofReal (V b - V a) := hle₂
        _ = eVariationOn γ (Icc a b) := by
          rw [hVa, hVb, sub_zero, ENNReal.ofReal_toReal hγ]
    · rw [BoundedVariationOn, not_ne_iff] at hγ
      exact hγ ▸ le_top
  · simp [Icc_eq_empty hab]

/-- For any curve in an extended pseudometric space, the lower Lebesgue integral of its metric
derivative over the unordered interval `Ι a b` is at most its total variation on `uIcc a b`. -/
theorem lintegral_metricDerivative_uIoc_le_eVariationOn_uIcc (γ : ℝ → X) (a b : ℝ) :
    ∫⁻ t in Ι a b, metricDerivative γ t ≤ eVariationOn γ (uIcc a b) := by
  rw [uIoc, uIcc, restrict_Ioc_eq_restrict_Icc]
  exact lintegral_metricDerivative_le_eVariationOn γ (min a b) (max a b)

end PseudoEMetricSpace

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b c s u : ℝ}

/-- The total variation of an absolutely continuous curve on `[a, b]` is at most the lower Lebesgue
integral of its metric derivative over `[a, b]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_le_lintegral_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (Icc a b) ≤ ∫⁻ t in Icc a b, metricDerivative γ t := by
  let L : ℝ → ℝ → ℝ≥0∞ := fun c d ↦ ∫⁻ t in Ioc c d, metricDerivative γ t
  have hL_add {c d e : ℝ} (hcd : c ≤ d) (hde : d ≤ e) : L c d + L d e = L c e := by
    simp only [L, ← Ioc_union_Ioc_eq_Ioc hcd hde]
    exact (lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)).symm
  have htelescoping {u : ℕ → ℝ} (hu : Monotone u) :
      ∀ m, ∑ i ∈ Finset.range m, L (u i) (u (i + 1)) = L (u 0) (u m) := by
    intro m
    induction m with
    | zero => simp [L]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hL_add (hu (Nat.zero_le k)) (hu (Nat.le_succ k))]
  refine iSup_le ?_
  rintro ⟨n, u, hu, hus⟩
  have hseg (i : ℕ) : edist (γ (u (i + 1))) (γ (u i)) ≤ L (u i) (u (i + 1)) := by
    rw [edist_comm]
    refine (hγ.edist_le_lintegral_metricDerivative (Icc_subset_uIcc (hus i))
      (Icc_subset_uIcc (hus (i + 1)))).trans_eq ?_
    simp [L, uIoc_of_le (hu (Nat.le_succ i))]
  calc
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
        ≤ ∑ i ∈ Finset.range n, L (u i) (u (i + 1)) := Finset.sum_le_sum fun i _ ↦ hseg i
    _ = L (u 0) (u n) := htelescoping hu n
    _ ≤ ∫⁻ t in Icc a b, metricDerivative γ t :=
      lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (hus 0).1 (hus n).2))

/-- **Length of an absolutely continuous curve.** The total variation of an absolutely continuous
curve on `[a, b]` equals the lower Lebesgue integral of its metric derivative over `[a, b]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_eq_lintegral_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (Icc a b) = ∫⁻ t in Icc a b, metricDerivative γ t :=
  le_antisymm hγ.eVariationOn_le_lintegral_metricDerivative
    (lintegral_metricDerivative_le_eVariationOn γ a b)

/-- The total variation of an absolutely continuous curve on `uIcc a b` is at most the lower
Lebesgue integral of its metric derivative over `Ι a b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_uIcc_le_lintegral_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (uIcc a b) ≤ ∫⁻ t in Ι a b, metricDerivative γ t := by
  rw [uIcc, uIoc, restrict_Ioc_eq_restrict_Icc]
  exact (hγ.mono (by simp [uIcc])).eVariationOn_le_lintegral_metricDerivative

/-- The total variation of an absolutely continuous curve on `uIcc a b` equals the lower Lebesgue
integral of its metric derivative over `Ι a b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_uIcc_eq_lintegral_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (uIcc a b) = ∫⁻ t in Ι a b, metricDerivative γ t :=
  le_antisymm hγ.eVariationOn_uIcc_le_lintegral_metricDerivative
    (lintegral_metricDerivative_uIoc_le_eVariationOn_uIcc γ a b)

/-- Along an absolutely continuous curve on `uIcc a b`, the distance between two values of the
signed variation function `variationOnFromTo γ (uIcc a b) c` equals the integral of the metric
derivative between those times. -/
theorem _root_.AbsolutelyContinuousOnInterval.edist_variationOnFromTo_eq_lintegral_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hc : c ∈ uIcc a b)
    (hs : s ∈ uIcc a b) (hu : u ∈ uIcc a b) :
    edist (variationOnFromTo γ (uIcc a b) c s) (variationOnFromTo γ (uIcc a b) c u) =
      ∫⁻ t in Ι s u, metricDerivative γ t := by
  have hbv := hγ.boundedVariationOn'
  have hsub : uIcc s u ⊆ uIcc a b := uIcc_subset_uIcc hs hu
  have hγsu : AbsolutelyContinuousOnInterval γ s u := hγ.mono hsub
  rw [edist_dist, Real.dist_eq,
    variationOnFromTo.sub_right hbv.locallyBoundedVariationOn hc hs hu]
  rcases le_total u s with hus | hsu
  · rw [variationOnFromTo.eq_of_le _ _ hus, abs_of_nonneg ENNReal.toReal_nonneg,
      inter_eq_self_of_subset_right (uIcc_of_le hus ▸ uIcc_subset_uIcc hu hs),
      ← uIcc_of_le hus, uIcc_comm, hγsu.eVariationOn_uIcc_eq_lintegral_metricDerivative,
      ENNReal.ofReal_toReal hγsu.lintegral_metricDerivative_lt_top.ne]
  · rw [variationOnFromTo.eq_neg_swap, variationOnFromTo.eq_of_le _ _ hsu, abs_neg,
      abs_of_nonneg ENNReal.toReal_nonneg,
      inter_eq_self_of_subset_right (uIcc_of_le hsu ▸ hsub),
      ← uIcc_of_le hsu, hγsu.eVariationOn_uIcc_eq_lintegral_metricDerivative,
      ENNReal.ofReal_toReal hγsu.lintegral_metricDerivative_lt_top.ne]

/-- The signed variation function `t ↦ variationOnFromTo γ (uIcc a b) c t` of an absolutely
continuous curve on `uIcc a b` is itself absolutely continuous on `uIcc a b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.variationOnFromTo
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (variationOnFromTo γ (uIcc a b) c) a b :=
  absolutelyContinuousOnInterval_of_edist_le_lintegral hγ.lintegral_metricDerivative_lt_top.ne
    fun _ hs _ hu ↦ (hγ.edist_variationOnFromTo_eq_lintegral_metricDerivative hc hs hu).le

/-- For an absolutely continuous curve on `uIcc a b`, its metric derivative agrees almost
everywhere on `uIcc a b` with the extended norm of the derivative of its signed variation
function. -/
theorem _root_.AbsolutelyContinuousOnInterval.ae_metricDerivative_eq_enorm_deriv_variationOnFromTo
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∀ᵐ t, t ∈ uIcc a b →
      metricDerivative γ t = ‖deriv (variationOnFromTo γ (uIcc a b) a) t‖ₑ := by
  set V := variationOnFromTo γ (uIcc a b) a
  have hVac : AbsolutelyContinuousOnInterval V a b := hγ.variationOnFromTo left_mem_uIcc
  have hVle : ∀ᵐ t, t ∈ uIcc a b → metricDerivative V t ≤ metricDerivative γ t :=
    ae_metricDerivative_le hγ.aemeasurable_metricDerivative
      hγ.lintegral_metricDerivative_lt_top.ne fun _ hs _ hu ↦
        (hγ.edist_variationOnFromTo_eq_lintegral_metricDerivative left_mem_uIcc hs hu).le
  filter_upwards [hγ.boundedVariationOn'.ae_metricDerivative_le_enorm_deriv_variationOnFromTo,
    hVle, hVac.ae_differentiableAt] with t hle hge hdiff hmem
  have hVeq : metricDerivative V t = ‖deriv V t‖ₑ := (hdiff hmem).hasDerivAt.metricDerivative_eq
  exact le_antisymm (hle hmem) (hVeq ▸ hge hmem)

/-- For `a ≤ b` and an absolutely continuous curve on `[a, b]`, the derivative of the variation
function `variationOnFromTo γ (Icc a b) a` equals `(metricDerivative γ t).toReal` almost everywhere
on `[a, b]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.ae_deriv_variationOnFromTo_eq_toReal_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    ∀ᵐ t, t ∈ Icc a b →
      deriv (variationOnFromTo γ (Icc a b) a) t = (metricDerivative γ t).toReal := by
  have hVmono : MonotoneOn (variationOnFromTo γ (Icc a b) a) (Icc a b) := by
    simpa [uIcc_of_le hab] using
      variationOnFromTo.monotoneOn hγ.boundedVariationOn'.locallyBoundedVariationOn left_mem_uIcc
  filter_upwards [hγ.ae_metricDerivative_eq_enorm_deriv_variationOnFromTo,
    volume.ae_ne a, volume.ae_ne b] with t ht hta htb hmem
  have hmem' : t ∈ uIcc a b := by rwa [uIcc_of_le hab]
  have hnhds : Icc a b ∈ 𝓝 t :=
    Icc_mem_nhds (lt_of_le_of_ne hmem.1 hta.symm) (lt_of_le_of_ne hmem.2 htb)
  have hnonneg : 0 ≤ deriv (variationOnFromTo γ (Icc a b) a) t := by
    rw [← derivWithin_of_mem_nhds hnhds]
    exact hVmono.derivWithin_nonneg
  have hteq : metricDerivative γ t = ‖deriv (variationOnFromTo γ (Icc a b) a) t‖ₑ := by
    simpa [uIcc_of_le hab] using ht hmem'
  rw [hteq, toReal_enorm, Real.norm_of_nonneg hnonneg]

/-- The real-valued metric derivative `t ↦ (metricDerivative γ t).toReal` of an absolutely
continuous curve on `uIcc a b` is interval integrable on `a..b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.intervalIntegrable_toReal_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntervalIntegrable (fun t ↦ (metricDerivative γ t).toReal) volume a b :=
  intervalIntegrable_iff.2 <|
    integrable_toReal_of_lintegral_ne_top hγ.aemeasurable_metricDerivative
      hγ.lintegral_metricDerivative_lt_top.ne

/-- For `a ≤ b`, the real total variation `(eVariationOn γ (Icc a b)).toReal` of an absolutely
continuous curve on `[a, b]` equals the interval integral of its real-valued metric derivative. -/
theorem
    _root_.AbsolutelyContinuousOnInterval.toReal_eVariationOn_eq_integral_toReal_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    (eVariationOn γ (Icc a b)).toReal = ∫ t in a..b, (metricDerivative γ t).toReal := by
  have hm : AEMeasurable (metricDerivative γ) (volume.restrict (Ioc a b)) := by
    simpa [uIoc_of_le hab] using hγ.aemeasurable_metricDerivative
  have hfin : ∫⁻ t in Ioc a b, metricDerivative γ t ≠ ∞ := by
    simpa [uIoc_of_le hab] using hγ.lintegral_metricDerivative_lt_top.ne
  rw [hγ.eVariationOn_eq_lintegral_metricDerivative, ← restrict_Ioc_eq_restrict_Icc,
    intervalIntegral.integral_of_le hab,
    integral_toReal hm (ae_lt_top' hm hfin)]

/-- For `a ≤ b`, the total variation `eVariationOn γ (Icc a b)` of an absolutely continuous curve
on `[a, b]` equals `ENNReal.ofReal (∫ t in a..b, (metricDerivative γ t).toReal)`. -/
theorem
    _root_.AbsolutelyContinuousOnInterval.eVariationOn_eq_ofReal_integral_toReal_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    eVariationOn γ (Icc a b) = ENNReal.ofReal (∫ t in a..b, (metricDerivative γ t).toReal) := by
  have hfin : eVariationOn γ (Icc a b) ≠ ∞ := by
    simpa [BoundedVariationOn, uIcc_of_le hab] using hγ.boundedVariationOn'
  rw [← hγ.toReal_eVariationOn_eq_integral_toReal_metricDerivative hab,
    ENNReal.ofReal_toReal hfin]

/-- The signed variation of an absolutely continuous curve from `a` to `b` equals the interval
integral of its real-valued metric derivative. -/
theorem
    _root_.AbsolutelyContinuousOnInterval.variationOnFromTo_eq_integral_toReal_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    variationOnFromTo γ (uIcc a b) a b = ∫ t in a..b, (metricDerivative γ t).toReal := by
  rcases le_total a b with hab | hba
  · rw [variationOnFromTo.eq_of_le _ _ hab, uIcc_of_le hab, inter_self,
      hγ.toReal_eVariationOn_eq_integral_toReal_metricDerivative hab]
  · rw [variationOnFromTo.eq_of_ge _ _ hba, uIcc_of_ge hba, inter_self,
      hγ.symm.toReal_eVariationOn_eq_integral_toReal_metricDerivative hba,
      intervalIntegral.integral_symm, neg_neg]

end PseudoMetricSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E} {a b : ℝ}

/-- On a normed space, the metric derivative of a curve at a point of differentiability is the
extended norm of its derivative. -/
theorem _root_.DifferentiableAt.metricDerivative_eq {t : ℝ} (h : DifferentiableAt ℝ γ t) :
    metricDerivative γ t = ‖deriv γ t‖ₑ :=
  h.hasDerivAt.metricDerivative_eq

/-- If a curve in a real normed space is differentiable almost everywhere on `(a, b)`, the lower
Lebesgue integral of the extended norm of its derivative over `[a, b]` is at most its total
variation on `[a, b]`. -/
theorem lintegral_enorm_deriv_le_eVariationOn_of_ae_differentiableAt
    (hd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ γ t) :
    ∫⁻ t in Icc a b, ‖deriv γ t‖ₑ ≤ eVariationOn γ (Icc a b) := by
  have heq : ∫⁻ t in Icc a b, ‖deriv γ t‖ₑ = ∫⁻ t in Icc a b, metricDerivative γ t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    refine setLIntegral_congr_fun_ae measurableSet_Ioo ?_
    filter_upwards [hd] with t ht hmem using (ht hmem).metricDerivative_eq.symm
  exact heq.trans_le (lintegral_metricDerivative_le_eVariationOn γ a b)

/-- If an absolutely continuous curve in a real normed space is differentiable almost everywhere
on `(a, b)`, its total variation on `[a, b]` equals the lower Lebesgue integral of the extended
norm of its derivative over `[a, b]`. -/
theorem
    _root_.AbsolutelyContinuousOnInterval.eVariationOn_eq_lintegral_enorm_deriv_of_differentiableAt
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ γ t) :
    eVariationOn γ (Icc a b) = ∫⁻ t in Icc a b, ‖deriv γ t‖ₑ := by
  rw [hγ.eVariationOn_eq_lintegral_metricDerivative, ← restrict_Ioo_eq_restrict_Icc]
  refine setLIntegral_congr_fun_ae measurableSet_Ioo ?_
  filter_upwards [hd] with t ht hmem using (ht hmem).metricDerivative_eq

variable [FiniteDimensional ℝ E]

/-- A curve of bounded variation on `uIcc a b` in a finite-dimensional real normed space has
metric derivative equal to `‖deriv γ t‖ₑ` at almost every `t ∈ uIcc a b`. -/
theorem _root_.BoundedVariationOn.ae_metricDerivative_eq_enorm_deriv
    (hγ : BoundedVariationOn γ (uIcc a b)) :
    ∀ᵐ t, t ∈ uIcc a b → metricDerivative γ t = ‖deriv γ t‖ₑ := by
  filter_upwards [hγ.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact (ht hmem).metricDerivative_eq

/-- For any curve in a finite-dimensional real normed space, the lower Lebesgue integral of the
extended norm of its derivative over `[a, b]` is at most its total variation on `[a, b]`. -/
theorem lintegral_enorm_deriv_le_eVariationOn (γ : ℝ → E) (a b : ℝ) :
    ∫⁻ t in Icc a b, ‖deriv γ t‖ₑ ≤ eVariationOn γ (Icc a b) := by
  by_cases hab : a ≤ b
  · by_cases hγ : BoundedVariationOn γ (Icc a b)
    · have hγ' : BoundedVariationOn γ (uIcc a b) := by rwa [uIcc_of_le hab]
      refine lintegral_enorm_deriv_le_eVariationOn_of_ae_differentiableAt ?_
      filter_upwards [hγ'.ae_differentiableAt_of_mem_uIcc] with t ht hmem
      exact ht (uIcc_of_le hab ▸ Ioo_subset_Icc_self hmem)
    · rw [BoundedVariationOn, not_ne_iff] at hγ
      exact hγ ▸ le_top
  · simp [Icc_eq_empty hab]

/-- For any curve in a finite-dimensional real normed space, the lower Lebesgue integral of the
extended norm of its derivative over `Ι a b` is at most its total variation on `uIcc a b`. -/
theorem lintegral_enorm_deriv_uIoc_le_eVariationOn_uIcc (γ : ℝ → E) (a b : ℝ) :
    ∫⁻ t in Ι a b, ‖deriv γ t‖ₑ ≤ eVariationOn γ (uIcc a b) := by
  rw [uIoc, uIcc, restrict_Ioc_eq_restrict_Icc]
  exact lintegral_enorm_deriv_le_eVariationOn γ (min a b) (max a b)

/-- An absolutely continuous curve on `uIcc a b` in a finite-dimensional real normed space has
metric derivative equal to `‖deriv γ t‖ₑ` at almost every `t ∈ uIcc a b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.ae_metricDerivative_eq_enorm_deriv
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∀ᵐ t, t ∈ uIcc a b → metricDerivative γ t = ‖deriv γ t‖ₑ :=
  hγ.boundedVariationOn.ae_metricDerivative_eq_enorm_deriv

/-- For `a ≤ b` and an absolutely continuous curve on `[a, b]` in a finite-dimensional real normed
space, the derivative of the variation function `variationOnFromTo γ (Icc a b) a` equals
`‖deriv γ t‖` almost everywhere on `[a, b]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.ae_deriv_variationOnFromTo_eq_norm_deriv
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    ∀ᵐ t, t ∈ Icc a b → deriv (variationOnFromTo γ (Icc a b) a) t = ‖deriv γ t‖ := by
  filter_upwards [hγ.ae_deriv_variationOnFromTo_eq_toReal_metricDerivative hab,
    hγ.ae_metricDerivative_eq_enorm_deriv] with t ht₁ ht₂ hmem
  rw [ht₁ hmem, ht₂ (uIcc_of_le hab ▸ hmem), toReal_enorm]

/-- **Length of an absolutely continuous curve in a finite-dimensional normed space.** The total
variation of an absolutely continuous curve on `[a, b]` in a finite-dimensional real normed space
equals the lower Lebesgue integral of the extended norm of its derivative over `[a, b]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_eq_lintegral_enorm_deriv
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (Icc a b) = ∫⁻ t in Icc a b, ‖deriv γ t‖ₑ := by
  refine hγ.eVariationOn_eq_lintegral_enorm_deriv_of_differentiableAt ?_
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact ht (Icc_subset_uIcc (Ioo_subset_Icc_self hmem))

/-- The total variation of an absolutely continuous curve on `uIcc a b` in a finite-dimensional
real normed space equals the lower Lebesgue integral of the extended norm of its derivative over
`Ι a b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_uIcc_eq_lintegral_enorm_deriv
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (uIcc a b) = ∫⁻ t in Ι a b, ‖deriv γ t‖ₑ := by
  rw [uIcc, uIoc, restrict_Ioc_eq_restrict_Icc]
  exact (hγ.mono (by simp [uIcc])).eVariationOn_eq_lintegral_enorm_deriv

/-- For an absolutely continuous curve on `uIcc a b` in a finite-dimensional real normed space,
`t ↦ ‖deriv γ t‖` is interval integrable on `a..b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.intervalIntegrable_norm_deriv
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntervalIntegrable (fun t ↦ ‖deriv γ t‖) volume a b := by
  refine hγ.intervalIntegrable_toReal_metricDerivative.congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hγ.ae_metricDerivative_eq_enorm_deriv] with t ht hmem
  rw [ht (uIoc_subset_uIcc hmem), toReal_enorm]

/-- The signed variation from `a` to `b` of an absolutely continuous curve in a
finite-dimensional real normed space equals `∫ t in a..b, ‖deriv γ t‖`. -/
theorem _root_.AbsolutelyContinuousOnInterval.variationOnFromTo_eq_integral_norm_deriv
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    variationOnFromTo γ (uIcc a b) a b = ∫ t in a..b, ‖deriv γ t‖ := by
  rw [hγ.variationOnFromTo_eq_integral_toReal_metricDerivative]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hγ.ae_metricDerivative_eq_enorm_deriv] with t ht hmem
  rw [ht (uIoc_subset_uIcc hmem), toReal_enorm]

/-- For `a ≤ b`, the real total variation `(eVariationOn γ (Icc a b)).toReal` of an absolutely
continuous curve on `[a, b]` in a finite-dimensional real normed space equals
`∫ t in a..b, ‖deriv γ t‖`. -/
theorem _root_.AbsolutelyContinuousOnInterval.toReal_eVariationOn_eq_integral_norm_deriv
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    (eVariationOn γ (Icc a b)).toReal = ∫ t in a..b, ‖deriv γ t‖ := by
  rw [hγ.toReal_eVariationOn_eq_integral_toReal_metricDerivative hab]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hγ.ae_metricDerivative_eq_enorm_deriv] with t ht hmem
  rw [ht (uIoc_subset_uIcc hmem), toReal_enorm]

/-- For `a ≤ b`, the total variation `eVariationOn γ (Icc a b)` of an absolutely continuous curve
on `[a, b]` in a finite-dimensional real normed space equals
`ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖)`. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_eq_ofReal_integral_norm_deriv
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    eVariationOn γ (Icc a b) = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  rw [hγ.eVariationOn_eq_ofReal_integral_toReal_metricDerivative hab,
    ← hγ.toReal_eVariationOn_eq_integral_toReal_metricDerivative hab,
    hγ.toReal_eVariationOn_eq_integral_norm_deriv hab]

end NormedSpace

end TauCeti
