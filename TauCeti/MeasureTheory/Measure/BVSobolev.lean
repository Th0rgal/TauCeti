/-
Copyright (c) 2026 General Intelligence, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module
public import TauCeti.MeasureTheory.Measure.BallPerimeter
public import TauCeti.Analysis.SpecialFunctions.Pow.Integral
public import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.BoxPerimeter
import all TauCeti.MeasureTheory.Measure.BallPerimeter
/-!
# Sharp Endpoint BV Sobolev Inequality and Ball-Indicator Rigidity
This file proves the 1D Lorentz–Minkowski layer-cake inequality with step-function rigidity for
`1 < p`, the `L^{p,1} ↪ L^p` layer-cake inequality with single-indicator equality classification,
the sharp endpoint BV Sobolev inequality `‖u‖_{n/(n-1)} ≤ (n ω_n^(1/n))⁻¹ |Du|(ℝⁿ)` with
ball-indicator equality classification, and smooth radial near-extremizers (`radialCubicCutoff`).
-/

open Filter Function MeasureTheory Pointwise Set TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Distributions Topology Interval
public section
namespace TauCeti
/-- Any function `Φ : ℝ → ℝ≥0∞` that is antitone on `Ioi 0` is measurable on `Ioi 0`. -/
theorem aemeasurable_of_antitoneOn_Ioi_ennreal {Φ : ℝ → ℝ≥0∞} (hΦ : AntitoneOn Φ (Ioi 0)) :
    AEMeasurable Φ (volume.restrict (Ioi (0 : ℝ))) := by
  have hanti : Antitone (fun t ↦ if 0 < t then Φ t else ⊤) := (fun a b hab ↦ by
    dsimp; split_ifs with hb ha ha; exacts [hΦ ha hb hab, le_top, False.elim (hb (ha.trans_le hab)),
      le_top]); exact hanti.measurable.aemeasurable.congr ((ae_restrict_mem measurableSet_Ioi).mono
        fun t ht ↦ ite_eq_left_iff.2 fun h ↦ (h ht).elim)
/-- Fundamental theorem of calculus for the `p`-th power of `t ↦ ∫ s in 0..t, g s`. -/
theorem integral_rpow_primitive_mul {p T : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ} (hg : IntervalIntegrable g
    volume 0 T) : ∫ t in (0 : ℝ)..T, p * (∫ s in (0 : ℝ)..t, g s) ^ (p - 1) * g t = (∫ s in (0 :
    ℝ)..T, g s) ^ p := by
  let I : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, g s; have hcd : ContDiff ℝ 1 (fun x : ℝ ↦ x ^ p) :=
    (by
    rw [contDiff_one_iff_deriv]; refine ⟨fun x ↦ (Real.hasDerivAt_rpow_const (Or.inr
      hp)).differentiableAt, ?_⟩; rw [deriv_eq fun x ↦ Real.hasDerivAt_rpow_const (Or.inr hp)];
      exact continuous_const.mul (continuous_id.rpow_const fun _ ↦ Or.inr (by linarith))); have hId
        := hg.ae_hasDerivAt_integral.mono fun t ht ht_mem ↦ ht (uIoc_subset_uIcc ht_mem) 0
        (by simp); have hftc := (hg.absolutelyContinuousOnInterval_intervalIntegral (by simp))
        |>.integral_fderiv_apply_eq_sub hId hcd; rw [show I 0 ^ p = 0
        by simp [I, Real.zero_rpow (by linarith : p ≠ 0)], sub_zero] at hftc; rw [← hftc]; refine
        intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ ↦ ?_); rw
        [(Real.hasDerivAt_rpow_const (Or.inr hp)).hasFDerivAt.fderiv]; simp [smul_eq_mul, mul_comm
        (g t), mul_assoc]
/-- Two-step lower bound for the primitive of an antitone function `ψ` on `Ioi 0`. -/
theorem add_mul_le_intervalIntegral_of_antitoneOn {ψ : ℝ → ℝ} (hψ_anti : AntitoneOn ψ (Ioi 0)) {s t
    : ℝ} (hs : 0 < s) (hst : s ≤ t) (hint : IntervalIntegrable ψ volume 0 t) : s * ψ s + (t - s) * ψ
    t ≤ ∫ u in (0 : ℝ)..t, ψ u := by
  have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le (hs.le.trans hst)).1 hint; rw [←
    intervalIntegral.integral_add_adjacent_intervals ((intervalIntegrable_iff_integrableOn_Ioc_of_le
    hs.le).2 (hIoc.mono_set (Ioc_subset_Ioc_right hst)))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 (hIoc.mono_set (Ioc_subset_Ioc_left
    hs.le))), intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_of_le hst]; have hc1
    : s * ψ s = ∫ _ in Ioc 0 s, ψ s :=
    (by simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hs.le, smul_eq_mul]); have h1 : s
    * ψ s ≤ ∫ u in Ioc 0 s, ψ u := hc1 ▸ setIntegral_mono_on (integrableOn_const (by simp))
    (hIoc.mono_set (Ioc_subset_Ioc_right hst)) measurableSet_Ioc fun u hu ↦ hψ_anti hu.1 hs hu.2;
    have hc2 : (t - s) * ψ t = ∫ _ in Ioc s t, ψ t := (by
    simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hst), smul_eq_mul]);
      have h2 : (t - s) * ψ t ≤ ∫ u in Ioc s t, ψ u := hc2 ▸ setIntegral_mono_on (integrableOn_const
      (by simp)) (hIoc.mono_set (Ioc_subset_Ioc_left hs.le)) measurableSet_Ioc fun u hu ↦ hψ_anti
      (hs.trans hu.1) (hs.trans_le hst) hu.2; linarith
/-- Pointwise differential Lorentz–Minkowski bound for a nonnegative antitone function `φ`. -/
theorem mul_rpow_sub_one_le_primitive_rpow {φ : ℝ → ℝ} (hφ_anti : AntitoneOn φ (Ioi 0)) (hφ_nn : ∀ t
    ∈ Ioi (0 : ℝ), 0 ≤ φ t) {p t : ℝ} (hp : 1 ≤ p) (ht : 0 < t) (hint : IntervalIntegrable (fun s ↦
    φ s ^ (1 / p)) volume 0 t) : t ^ (p - 1) * φ t ≤ (∫ s in (0 : ℝ)..t, φ s ^ (1 / p)) ^ (p - 1) *
    φ t ^ (1 / p) := by
  have hp0 : 0 < p := (by linarith); have hψ_anti : AntitoneOn (fun s ↦ φ s ^ (1 / p)) (Ioi 0) :=
    fun a ha b hb hab ↦ Real.rpow_le_rpow (hφ_nn b hb) (hφ_anti ha hb hab) (by positivity); have
    hψ_nn := Real.rpow_nonneg (hφ_nn t ht) (1 / p); have hle : t * φ t ^ (1 / p) ≤ ∫ u in (0 :
    ℝ)..t, φ u ^ (1 / p) :=
    (by simpa using add_mul_le_intervalIntegral_of_antitoneOn hψ_anti ht le_rfl hint); have hpow :
    (t * φ t ^ (1 / p)) ^ (p - 1) ≤ (∫ u in (0 : ℝ)..t, φ u ^ (1 / p)) ^ (p - 1) :=
    Real.rpow_le_rpow (mul_nonneg ht.le hψ_nn) hle (by linarith); have hmul :=
    mul_le_mul_of_nonneg_right hpow hψ_nn; rwa [Real.mul_rpow ht.le hψ_nn, mul_assoc, ←
    Real.rpow_add_one' hψ_nn (by linarith), sub_add_cancel, ← Real.rpow_mul (hφ_nn t ht),
    one_div_mul_cancel hp0.ne', Real.rpow_one] at hmul
/-- Half-line primitive power identity on `Ioi 0` for a nonnegative integrable function `g`. -/
theorem integrableOn_and_setIntegral_Ioi_rpow_primitive_mul {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ} (hg_nn
    : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g t) (hg : IntegrableOn g (Ioi (0 : ℝ)) volume) : IntegrableOn (fun t ↦
    p * (∫ s in (0 : ℝ)..t, g s) ^ (p - 1) * g t) (Ioi (0 : ℝ)) volume ∧ ∫ t in Ioi (0 : ℝ), p * (∫
    s in (0 : ℝ)..t, g s) ^ (p - 1) * g t = (∫ s in Ioi (0 : ℝ), g s) ^ p := by
  have hp0 : 0 < p := (by linarith); have hp1 : 0 ≤ p - 1 := (by linarith); let I : ℝ → ℝ := fun t ↦
    ∫ s in (0 : ℝ)..t, g s; have hI_nn : ∀ t ≥ 0, 0 ≤ I t := (fun t ht ↦ by
    dsimp [I]; rw [intervalIntegral.integral_of_le ht]; exact setIntegral_nonneg measurableSet_Ioc
      fun s hs ↦ hg_nn s hs.1); have hI_le : ∀ t ≥ 0, I t ≤ ∫ s in Ioi (0 : ℝ), g s := (fun t ht ↦
        by
    dsimp [I]; rw [intervalIntegral.integral_of_le ht]; exact setIntegral_mono_set hg
      (ae_restrict_of_forall_mem measurableSet_Ioi hg_nn) (Eventually.of_forall
        Ioc_subset_Ioi_self)); have hIc : ContinuousOn I (Ioi (0 : ℝ)) := (fun t ht ↦ by
    have ht1 : 0 ≤ t + 1 := (by linarith [mem_Ioi.1 ht]); have hc :=
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le ht1).2 (hg.mono_set
      Ioc_subset_Ioi_self)).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc).continuousOn; rw [uIcc_of_le ht1] at hc; exact (hc.continuousAt (Icc_mem_nhds
      ht (by linarith))).continuousWithinAt); have hint_R : IntegrableOn (fun t ↦ p * I t ^ (p - 1)
        * g t) (Ioi (0 : ℝ)) volume := (by
    refine (hg.const_mul (p * (∫ s in Ioi (0 : ℝ), g s) ^ (p - 1))).mono' (((continuousOn_const.mul
      (hIc.rpow_const fun _ _ ↦ Or.inr hp1)).aestronglyMeasurable measurableSet_Ioi).mul
      hg.aestronglyMeasurable) ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦ ?_); have ht0 :=
      (mem_Ioi.1 ht).le; rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hp0.le (Real.rpow_nonneg
      (hI_nn t ht0) _)) (hg_nn t ht))]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hI_nn t ht0) (hI_le t ht0) hp1) hp0.le) (hg_nn t ht)); refine ⟨hint_R,
        ?_⟩; have hmono : Monotone (fun n : ℕ ↦ Ioc (0 : ℝ) (n : ℝ)) := fun _ _ hmn ↦
        Ioc_subset_Ioc_right (Nat.cast_le.2 hmn); have hunion : (⋃ n : ℕ, Ioc (0 : ℝ) (n : ℝ)) = Ioi
        (0 : ℝ) := (by
    ext t; simp only [mem_iUnion, mem_Ioc, mem_Ioi]; exact ⟨fun ⟨_, ht0, _⟩ ↦ ht0, fun ht0 ↦ ⟨⌈t⌉₊,
      ht0, Nat.le_ceil t⟩⟩); have hlim_L := hunion ▸ MeasureTheory.tendsto_setIntegral_of_monotone
        (fun _ ↦ measurableSet_Ioc) hmono (hunion.symm ▸ hint_R); have hlim_I : Tendsto (fun n : ℕ ↦
        I (n : ℝ)) atTop (𝓝 (∫ s in Ioi (0 : ℝ), g s)) := (by
    rw [show (fun n : ℕ ↦ I (n : ℝ)) = fun n : ℕ ↦ ∫ s in Ioc (0 : ℝ) (n : ℝ), g s from funext fun n
      ↦ intervalIntegral.integral_of_le (Nat.cast_nonneg n), ← hunion]; exact
      MeasureTheory.tendsto_setIntegral_of_monotone (fun _ ↦ measurableSet_Ioc) hmono (hunion.symm ▸
      hg)); have h_eq : ∀ n : ℕ, (∫ t in Ioc (0 : ℝ) n, p * I t ^ (p - 1) * g t) = I n ^ p := (fun n
        ↦ by
    rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg n)]; exact integral_rpow_primitive_mul hp
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).2 (hg.mono_set
      Ioc_subset_Ioi_self))); simp_rw [h_eq] at hlim_L; exact tendsto_nhds_unique hlim_L
        ((Real.continuous_rpow_const hp0.le).tendsto _ |>.comp hlim_I)
/-- Integrability of `t ↦ t ^ (p - 1) * φ t` on `Ioi 0` from integrability of `φ ^ (1 / p)`. -/
theorem integrableOn_Ioi_rpow_sub_one_mul {φ : ℝ → ℝ} (hφ_anti : AntitoneOn φ (Ioi 0)) (hφ_nn : ∀ t
    ∈ Ioi (0 : ℝ), 0 ≤ φ t) {p : ℝ} (hp : 1 ≤ p) (hint : IntegrableOn (fun s ↦ φ s ^ (1 / p)) (Ioi
    (0 : ℝ)) volume) : IntegrableOn (fun t ↦ t ^ (p - 1) * φ t) (Ioi (0 : ℝ)) volume := by
  have hp0 : 0 < p := (by linarith); have hφ_meas : AEStronglyMeasurable φ (volume.restrict (Ioi (0
    : ℝ))) := (aemeasurable_of_antitoneOn_Ioi_ennreal fun a ha b hb hab ↦ ENNReal.ofReal_le_ofReal
    (hφ_anti ha hb hab)).ennreal_toReal.aestronglyMeasurable.congr ((ae_restrict_mem
    measurableSet_Ioi).mono fun t ht ↦ ENNReal.toReal_ofReal (hφ_nn t ht)); have hR :=
    (integrableOn_and_setIntegral_Ioi_rpow_primitive_mul hp (fun t ht ↦ Real.rpow_nonneg (hφ_nn t
    ht) _) hint).1; refine (hR.const_mul p⁻¹).mono' ((Measurable.aestronglyMeasurable
    (by fun_prop)).mul hφ_meas) ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦ ?_); have ht0 :
    0 < t := mem_Ioi.1 ht; rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (hφ_nn t
    ht))]; exact (mul_rpow_sub_one_le_primitive_rpow hφ_anti hφ_nn hp ht0
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).2 (hint.mono_set
    Ioc_subset_Ioi_self))).trans_eq (by have := hp0.ne'; field_simp)
/-- Half-line **1D Lorentz–Minkowski integral inequality** for `1 ≤ p` and antitone `φ ≥ 0`. -/
theorem mul_setIntegral_Ioi_rpow_sub_one_le {φ : ℝ → ℝ} (hφ_anti : AntitoneOn φ (Ioi 0)) (hφ_nn : ∀
    t ∈ Ioi (0 : ℝ), 0 ≤ φ t) {p : ℝ} (hp : 1 ≤ p) (hint : IntegrableOn (fun s ↦ φ s ^ (1 / p)) (Ioi
    (0 : ℝ)) volume) : p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * φ t ≤ (∫ t in Ioi (0 : ℝ), φ t ^ (1 /
    p)) ^ p := by
  have hp0 : 0 < p := (by linarith); obtain ⟨hR_int, hR_eq⟩ :=
    integrableOn_and_setIntegral_Ioi_rpow_primitive_mul hp (fun t ht ↦ Real.rpow_nonneg (hφ_nn t ht)
    _) hint; rw [← integral_const_mul, ← hR_eq]; refine setIntegral_mono_on
    ((integrableOn_Ioi_rpow_sub_one_mul hφ_anti hφ_nn hp hint).const_mul p) hR_int measurableSet_Ioi
    fun t ht ↦ ?_; have ht0 : 0 < t := mem_Ioi.1 ht; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
    (mul_rpow_sub_one_le_primitive_rpow hφ_anti hφ_nn hp ht0
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).2 (hint.mono_set Ioc_subset_Ioi_self)))
    hp0.le
/-- **Step-function classification for equality in the 1D Lorentz–Minkowski inequality**. -/
theorem eq_step_of_lorentz_layerCake_eq {φ : ℝ → ℝ} (hφ_anti : AntitoneOn φ (Ioi 0)) (hφ_nn : ∀ t ∈
    Ioi (0 : ℝ), 0 ≤ φ t) {p : ℝ} (hp : 1 < p) (hint : IntegrableOn (fun s ↦ φ s ^ (1 / p)) (Ioi (0
    : ℝ)) volume) (heq : p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * φ t = (∫ t in Ioi (0 : ℝ), φ t ^ (1 /
    p)) ^ p) : ∃ c ≥ 0, ∃ M ≥ 0, (∀ t ∈ Ioo 0 c, φ t = M) ∧ ∀ t ∈ Ioi c, φ t = 0 := by
  have hp0 : 0 < p := (by linarith); have hp1 : 0 < p - 1 := (by linarith); let g : ℝ → ℝ := fun s ↦
    φ s ^ (1 / p); let I : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, g s; have hg_nn : ∀ t ∈ Ioi (0 : ℝ),
    0 ≤ g t := fun t ht ↦ Real.rpow_nonneg (hφ_nn t ht) _; have hψ_anti : AntitoneOn g (Ioi 0) :=
    fun a ha b hb hab ↦ Real.rpow_le_rpow (hφ_nn b hb) (hφ_anti ha hb hab) (by positivity); obtain
    ⟨hR_int, hR_eq⟩ := integrableOn_and_setIntegral_Ioi_rpow_primitive_mul hp.le hg_nn hint; have
    hL_int := (integrableOn_Ioi_rpow_sub_one_mul hφ_anti hφ_nn hp.le hint).const_mul p; have hae_le
    : (fun t ↦ p * (t ^ (p - 1) * φ t)) ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t ↦ p * I t ^ (p - 1)
    * g t := (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; have ht0 : 0 < t := mem_Ioi.1 ht;
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_rpow_sub_one_le_primitive_rpow hφ_anti
      hφ_nn hp.le ht0 ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).2 (hint.mono_set
      Ioc_subset_Ioi_self))) hp0.le); have hae_eq := (integral_eq_iff_of_ae_le hL_int hR_int
        hae_le).1 (by rw [integral_const_mul, heq, hR_eq]); have hflat : ∀ {s₁ s₂ s₃ : ℝ}, 0 < s₁ →
        s₁ ≤ s₂ → s₂ < s₃ → 0 < φ s₃ → φ s₁ = φ s₂ ∧ s₂ * g s₁ ≤ ∫ s in Ioi (0 : ℝ), g s := (fun {s₁
        s₂ s₃} hs₁ hs₁₂ hs₂₃ hφ₃ ↦ by
    have hs₂ : 0 < s₂ := hs₁.trans_le hs₁₂; have hae_Ioo := ae_mono (Measure.restrict_mono (fun _
      (ht : _ ∈ Ioo s₂ s₃) ↦ hs₂.trans ht.1) le_rfl) hae_eq; have hne : NeBot (ae (volume.restrict
      (Ioo s₂ s₃))) := (by
      rw [ae_neBot]; intro h0; apply (ENNReal.ofReal_pos.2 (sub_pos.2 hs₂₃)).ne'; simpa
        [Measure.restrict_apply_self, Real.volume_Ioo] using congrArg (fun μ ↦ μ (Ioo s₂ s₃)) h0);
          obtain ⟨t, ht_mem, ht_eq⟩ := ((ae_restrict_mem measurableSet_Ioo).and hae_Ioo).exists;
          have ht0 : 0 < t := hs₂.trans ht_mem.1; have hφt : 0 < φ t := hφ₃.trans_le (hφ_anti ht0
          (hs₂.trans hs₂₃) ht_mem.2.le); have hgt : 0 < g t := Real.rpow_pos_of_pos hφt _; have hrew
          : p * (t ^ (p - 1) * φ t) = p * (t * g t) ^ (p - 1) * g t := (by
      rw [Real.mul_rpow ht0.le hgt.le, mul_assoc, mul_assoc, ← Real.rpow_add_one' hgt.le
        (by linarith), sub_add_cancel, ← Real.rpow_mul hφt.le, one_div_mul_cancel hp0.ne',
        Real.rpow_one]); change p * (t ^ (p - 1) * φ t) = p * I t ^ (p - 1) * g t at ht_eq; rw
          [hrew] at ht_eq; have hpe := mul_left_cancel₀ hp0.ne' (mul_right_cancel₀ hgt.ne' ht_eq);
          have hint_t := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).2 (hint.mono_set
          Ioc_subset_Ioi_self); have hItn : 0 ≤ I t := (mul_nonneg ht0.le hgt.le).trans
          (by simpa [I] using add_mul_le_intervalIntegral_of_antitoneOn hψ_anti ht0 le_rfl hint_t);
          have hI_eq : t * g t = I t := (by
      have h1 := congrArg (fun x : ℝ ↦ x ^ (1 / (p - 1))) hpe; rwa [← Real.rpow_mul (mul_nonneg
        ht0.le hgt.le), ← Real.rpow_mul hItn, mul_one_div_cancel hp1.ne', Real.rpow_one,
        Real.rpow_one] at h1); have hadd := add_mul_le_intervalIntegral_of_antitoneOn hψ_anti hs₁
          (hs₁₂.trans ht_mem.1.le) hint_t; change s₁ * g s₁ + (t - s₁) * g t ≤ I t at hadd; rw [←
          hI_eq] at hadd; have hgsl : g s₁ ≤ g t := le_of_mul_le_mul_left (by linarith) hs₁; have
          hφ_le : φ s₁ ≤ φ t := (by
      have h1 := Real.rpow_le_rpow (hg_nn s₁ hs₁) hgsl hp0.le; rwa [← Real.rpow_mul (hφ_nn s₁ hs₁),
        ← Real.rpow_mul hφt.le, one_div_mul_cancel hp0.ne', Real.rpow_one, Real.rpow_one] at h1);
          have hItl : I t ≤ ∫ s in Ioi (0 : ℝ), g s := (by
      dsimp [I]; rw [intervalIntegral.integral_of_le ht0.le]; exact setIntegral_mono_set hint
        (ae_restrict_of_forall_mem measurableSet_Ioi hg_nn) (Eventually.of_forall
        Ioc_subset_Ioi_self)); exact ⟨le_antisymm (hφ_le.trans (hφ_anti hs₂ ht0 ht_mem.1.le))
          (hφ_anti hs₁ hs₂ hs₁₂), (mul_le_mul ht_mem.1.le hgsl (hg_nn s₁ hs₁) ht0.le).trans
          (hI_eq.trans_le hItl)⟩); let S : Set ℝ := {t : ℝ | 0 < t ∧ 0 < φ t}; rcases
            S.eq_empty_or_nonempty with hS_empty | ⟨t₀, ht₀_pos, hφ₀_pos⟩
  · refine ⟨0, le_rfl, 0, le_rfl, fun t ht ↦ False.elim (lt_irrefl 0 (ht.1.trans ht.2)), fun t ht ↦
      le_antisymm ?_ (hφ_nn t ht)⟩; by_contra hpos; exact Set.notMem_empty t (hS_empty ▸ ⟨ht,
      lt_of_not_ge hpos⟩)
  · have hbdd : BddAbove S := (by
      refine ⟨max t₀ (2 * (∫ s in Ioi (0 : ℝ), g s) / g t₀), fun t ⟨_, hφt⟩ ↦ ?_⟩
      rcases le_or_gt t t₀ with htt₀ | ht₀t; · exact htt₀.trans (le_max_left _ _)
      have hle := (hflat (s₁ := t₀) (s₂ := (t₀ + t) / 2) ht₀_pos (by linarith) (by linarith) hφt).2;
        exact ((le_div_iff₀ (Real.rpow_pos_of_pos hφ₀_pos _)).2
        (by nlinarith [Real.rpow_pos_of_pos hφ₀_pos (1 / p)])).trans (le_max_right _ _)); let c :=
          sSup S; have hc_pos : 0 < c := lt_of_lt_of_le ht₀_pos (le_csSup hbdd ⟨ht₀_pos, hφ₀_pos⟩);
          refine ⟨c, hc_pos.le, φ (c / 2), hφ_nn (c / 2) (by change (0 : ℝ) < c / 2; linarith), fun
          t ht ↦ ?_, fun t ht ↦ ?_⟩
    · obtain ⟨s₃, ⟨_, hφ₃_pos⟩, hs₃_gt⟩ := (lt_csSup_iff hbdd ⟨t₀, ht₀_pos, hφ₀_pos⟩).1 (max_lt ht.2
        (by linarith : c / 2 < c)); exact (hflat (lt_min ht.1 (by linarith)) (min_le_left t (c / 2))
        ((le_max_left t (c / 2)).trans_lt hs₃_gt) hφ₃_pos).1.symm.trans (hflat (lt_min ht.1
        (by linarith)) (min_le_right t (c / 2)) ((le_max_right t (c / 2)).trans_lt hs₃_gt)
        hφ₃_pos).1
    · refine le_antisymm ?_ (hφ_nn t (hc_pos.trans ht)); by_contra hpos; exact ht.not_ge (le_csSup
        hbdd ⟨hc_pos.trans ht, lt_of_not_ge hpos⟩)
/-- Bridge from finite `ℝ≥0∞` lower integrals of `Φ` on `Ioi 0` to `ℝ` Bochner integrals. -/
theorem toReal_integrableOn_and_setLIntegral_eq_of_antitoneOn {Φ : ℝ → ℝ≥0∞} (hΦ_anti : AntitoneOn Φ
    (Ioi 0)) {p : ℝ} (hp : 1 ≤ p) (hfin : ∫⁻ t in Ioi (0 : ℝ), Φ t ^ (1 / p) ≠ ⊤) : (∀ t ∈ Ioi (0 :
    ℝ), Φ t ≠ ⊤) ∧ IntegrableOn (fun s ↦ (Φ s).toReal ^ (1 / p)) (Ioi (0 : ℝ)) volume ∧
    ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1)) * Φ t = ENNReal.ofReal (p *
    ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * (Φ t).toReal) ∧ (∫⁻ s in Ioi (0 : ℝ), Φ s ^ (1 / p)) ^ p =
    ENNReal.ofReal ((∫ s in Ioi (0 : ℝ), (Φ s).toReal ^ (1 / p)) ^ p) := by
  have hp0 : 0 < p := (by linarith); have hΦ : ∀ t ∈ Ioi (0 : ℝ), Φ t ≠ ⊤ := (fun t ht ↦ by
    have ht0 : 0 < t := mem_Ioi.1 ht; have hc : ENNReal.ofReal t * Φ t ^ (1 / p) = ∫⁻ _ in Ioc (0 :
      ℝ) t, Φ t ^ (1 / p) := (by rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]); have
      hle : ENNReal.ofReal t * Φ t ^ (1 / p) ≤ ∫⁻ s in Ioi (0 : ℝ), Φ s ^ (1 / p) := hc ▸
      (setLIntegral_mono' measurableSet_Ioc fun s hs ↦ ENNReal.rpow_le_rpow (hΦ_anti hs.1 ht hs.2)
      (by positivity)).trans (lintegral_mono_set Ioc_subset_Ioi_self); intro htop; exact
      (lt_of_le_of_lt hle hfin.lt_top).ne (by rw [htop, ENNReal.top_rpow_of_pos (by positivity),
      ENNReal.mul_top (ENNReal.ofReal_pos.2 ht0).ne'])); let φ : ℝ → ℝ := fun t ↦ (Φ t).toReal; have
        hφ_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ φ t := fun _ _ ↦ ENNReal.toReal_nonneg; have hφ_anti :
        AntitoneOn φ (Ioi 0) := fun a ha b hb hab ↦ ENNReal.toReal_mono (hΦ a ha) (hΦ_anti ha hb
        hab); have hψm : AEStronglyMeasurable (fun s ↦ φ s ^ (1 / p)) (volume.restrict (Ioi (0 :
        ℝ))) := ((aemeasurable_of_antitoneOn_Ioi_ennreal hΦ_anti).pow_const (1 /
        p)).ennreal_toReal.aestronglyMeasurable.congr ((ae_restrict_mem measurableSet_Ioi).mono fun
        s _ ↦ (ENNReal.toReal_rpow (Φ s) (1 / p)).symm); have hψl : ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (φ s ^ (1 / p)) = ∫⁻ s in Ioi (0 : ℝ), Φ s ^ (1 / p) :=
        (setLIntegral_congr_fun measurableSet_Ioi fun s hs ↦ by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal
      (hΦ s hs)]); have hnn_R : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s ↦ φ s ^ (1 / p) :=
        (ae_restrict_mem measurableSet_Ioi).mono fun _ _ ↦ Real.rpow_nonneg ENNReal.toReal_nonneg _;
        have hint : IntegrableOn (fun s ↦ φ s ^ (1 / p)) (Ioi (0 : ℝ)) volume := ⟨hψm,
        (hasFiniteIntegral_iff_ofReal hnn_R).2 (hψl.symm ▸ hfin.lt_top)⟩; have hL_lint : ∫⁻ t in Ioi
        (0 : ℝ), ENNReal.ofReal (t ^ (p - 1)) * Φ t = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), t ^ (p -
        1) * φ t) := (by
    rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_sub_one_mul hφ_anti hφ_nn hp
      hint) ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦ mul_nonneg (Real.rpow_nonneg
      (mem_Ioi.1 ht).le _) ENNReal.toReal_nonneg)]; exact setLIntegral_congr_fun measurableSet_Ioi
      fun t ht ↦ (by rw [ENNReal.ofReal_mul (Real.rpow_nonneg (mem_Ioi.1 ht).le _),
      ENNReal.ofReal_toReal (hΦ t ht)])); have hR_lint : ∫⁻ s in Ioi (0 : ℝ), Φ s ^ (1 / p) =
        ENNReal.ofReal (∫ s in Ioi (0 : ℝ), φ s ^ (1 / p)) := hψl.symm.trans
        (ofReal_integral_eq_lintegral_ofReal hint hnn_R).symm; have hint_nn : 0 ≤ ∫ s in Ioi (0 :
        ℝ), φ s ^ (1 / p) := setIntegral_nonneg measurableSet_Ioi fun _ _ ↦ Real.rpow_nonneg
        ENNReal.toReal_nonneg _; exact ⟨hΦ, hint, by rw [hL_lint, ENNReal.ofReal_mul hp0.le],
        by rw [hR_lint, ← ENNReal.ofReal_rpow_of_nonneg hint_nn hp0.le]⟩
/-- Extended-nonnegative **1D Lorentz–Minkowski integral inequality** (`1 ≤ p`, antitone `Φ`). -/
theorem mul_setLIntegral_Ioi_rpow_sub_one_le {Φ : ℝ → ℝ≥0∞} (hΦ_anti : AntitoneOn Φ (Ioi 0)) {p : ℝ}
    (hp : 1 ≤ p) : ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1)) * Φ t ≤ (∫⁻
    t in Ioi (0 : ℝ), Φ t ^ (1 / p)) ^ p := by
  have hp0 : 0 < p := (by linarith); refine (eq_or_ne (∫⁻ t in Ioi (0 : ℝ), Φ t ^ (1 / p)) ⊤).elim
    (fun htop ↦ by rw [htop, ENNReal.top_rpow_of_pos hp0]; exact le_top) fun hfin ↦ ?_; obtain ⟨hΦ,
    hint, hL_eq, hR_eq⟩ := toReal_integrableOn_and_setLIntegral_eq_of_antitoneOn hΦ_anti hp hfin; rw
    [hL_eq, hR_eq]; exact ENNReal.ofReal_le_ofReal (mul_setIntegral_Ioi_rpow_sub_one_le (fun a ha b
    hb hab ↦ ENNReal.toReal_mono (hΦ a ha) (hΦ_anti ha hb hab)) (fun _ _ ↦ ENNReal.toReal_nonneg) hp
    hint)
/-- Extended-nonnegative **1D Lorentz–Minkowski step-function rigidity (`1 < p`)**. -/
theorem eq_step_of_mul_setLIntegral_Ioi_rpow_sub_one_eq {Φ : ℝ → ℝ≥0∞} (hΦ_anti : AntitoneOn Φ (Ioi
    0)) {p : ℝ} (hp : 1 < p) (hfin : ∫⁻ t in Ioi (0 : ℝ), Φ t ^ (1 / p) ≠ ⊤) (heq : ENNReal.ofReal p
    * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1)) * Φ t = (∫⁻ t in Ioi (0 : ℝ), Φ t ^ (1 / p))
    ^ p) : ∃ c ≥ 0, ∃ M ≠ (⊤ : ℝ≥0∞), (∀ t ∈ Ioo 0 c, Φ t = M) ∧ ∀ t ∈ Ioi c, Φ t = 0 := by
  have hp0 : 0 < p := (by linarith); obtain ⟨hΦ, hint, hL_eq, hR_eq⟩ :=
    toReal_integrableOn_and_setLIntegral_eq_of_antitoneOn hΦ_anti hp.le hfin; rw [hL_eq,
    hR_eq] at heq; have hL_nn : 0 ≤ p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * (Φ t).toReal := mul_nonneg
    hp0.le (setIntegral_nonneg measurableSet_Ioi fun t ht ↦ mul_nonneg (Real.rpow_nonneg (mem_Ioi.1
    ht).le _) ENNReal.toReal_nonneg); have hR_nn : 0 ≤ (∫ s in Ioi (0 : ℝ), (Φ s).toReal ^ (1 / p))
    ^ p := Real.rpow_nonneg (setIntegral_nonneg measurableSet_Ioi fun _ _ ↦ Real.rpow_nonneg
    ENNReal.toReal_nonneg _) _; have heq_real : p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * (Φ t).toReal =
    (∫ s in Ioi (0 : ℝ), (Φ s).toReal ^ (1 / p)) ^ p := (by
    have h1 := congrArg ENNReal.toReal heq; rwa [ENNReal.toReal_ofReal hL_nn, ENNReal.toReal_ofReal
      hR_nn] at h1); obtain ⟨c, hc_nn, M, _, hIoo, hIoi⟩ := eq_step_of_lorentz_layerCake_eq (fun a
        ha b hb hab ↦ ENNReal.toReal_mono (hΦ a ha) (hΦ_anti ha hb hab)) (fun _ _ ↦
        ENNReal.toReal_nonneg) hp hint heq_real; exact ⟨c, hc_nn, ENNReal.ofReal M,
        ENNReal.ofReal_ne_top, fun t ht ↦ by rw [← ENNReal.ofReal_toReal (hΦ t ht.1), hIoo t ht],
        fun t ht ↦
        by rw [← ENNReal.ofReal_toReal (hΦ t (hc_nn.trans_lt ht)), hIoi t ht, ENNReal.ofReal_zero]⟩
section LayerCakeLp1
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
omit [MeasurableSpace α] in
/-- Strict superlevel sets `{x | a < g x}` as countable unions of `{x | a + 1/(n+1) < g x}`. -/
theorem setOf_lt_eq_iUnion_add_one_div (g : α → ℝ) (a : ℝ) : {x | a < g x} = ⋃ n : ℕ, {x | a + 1 /
    (n + 1 : ℝ) < g x} := by
  ext x; simp only [Set.mem_ofPred_eq, mem_iUnion]; refine ⟨fun hx ↦ ?_, fun ⟨n, hn⟩ ↦
    (lt_add_of_pos_right a (by positivity)).trans hn⟩; obtain ⟨n, hn⟩ := exists_nat_one_div_lt
    (sub_pos.2 hx); exact ⟨n, by linarith⟩
/-- Strict `ℝ≥0∞` subadditivity `(a + b) ^ (1 / p) < a ^ (1 / p) + b ^ (1 / p)` (`1 < p`). -/
theorem ennreal_rpow_inv_add_lt {a b : ℝ≥0∞} {p : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : a ≠ ⊤) (hb :
    b ≠ ⊤) (hp : 1 < p) : (a + b) ^ (1 / p) < a ^ (1 / p) + b ^ (1 / p) := by
  have hp0 : 0 < p := (by linarith); have hp1 : 0 < p - 1 := (by linarith); have ha_pos :=
    ENNReal.toReal_pos ha0 ha; have hb_pos := ENNReal.toReal_pos hb0 hb; set x := a.toReal ^ (1 /
    p); set y := b.toReal ^ (1 / p); have hx := Real.rpow_pos_of_pos ha_pos (1 / p); have hy :=
    Real.rpow_pos_of_pos hb_pos (1 / p); have hx_lt : x ^ p < x * (x + y) ^ (p - 1) := (by
    (conv_lhs => rw [← add_sub_cancel 1 p, Real.rpow_one_add' hx.le (by linarith)]); exact
      mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hx.le (lt_add_of_pos_right x hy) hp1) hx); have
        hy_lt : y ^ p < y * (x + y) ^ (p - 1) := (by
    (conv_lhs => rw [← add_sub_cancel 1 p, Real.rpow_one_add' hy.le (by linarith)]); exact
      mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hy.le (lt_add_of_pos_left y hx) hp1) hy); have hsum
        : a.toReal + b.toReal < (x + y) ^ p := (by
    have hL : a.toReal + b.toReal = x ^ p + y ^ p := (by
      rw [← Real.rpow_mul ha_pos.le, ← Real.rpow_mul hb_pos.le, one_div_mul_cancel hp0.ne',
        Real.rpow_one, Real.rpow_one]); have hR : x * (x + y) ^ (p - 1) + y * (x + y) ^ (p - 1) = (x
          + y) ^ p := (by
      rw [← add_mul, ← Real.rpow_one_add' (add_pos hx hy).le (by linarith), add_sub_cancel]); rw
        [hL, ← hR]; exact add_lt_add hx_lt hy_lt); have hrpow := Real.rpow_lt_rpow (add_pos ha_pos
          hb_pos).le hsum (one_div_pos.2 hp0); rw [← Real.rpow_mul (add_pos hx hy).le,
          mul_one_div_cancel hp0.ne', Real.rpow_one] at hrpow; rw [← ENNReal.ofReal_toReal ha, ←
          ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_add ha_pos.le hb_pos.le,
          ENNReal.ofReal_rpow_of_nonneg (add_pos ha_pos hb_pos).le (by positivity),
          ENNReal.ofReal_rpow_of_nonneg ha_pos.le (by positivity), ENNReal.ofReal_rpow_of_nonneg
          hb_pos.le (by positivity), ← ENNReal.ofReal_add hx.le hy.le]; exact
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.rpow_nonneg (add_pos ha_pos hb_pos).le _)
          |>.2 hrpow
/-- Extended-nonnegative subadditivity `(a + b) ^ (1 / p) ≤ a ^ (1 / p) + b ^ (1 / p)` (`1 ≤ p`). -/
theorem ennreal_rpow_inv_add_le {a b : ℝ≥0∞} {p : ℝ} (hp : 1 ≤ p) : (a + b) ^ (1 / p) ≤ a ^ (1 / p)
    + b ^ (1 / p) := by
  exact (eq_or_ne a 0).elim (fun h ↦ by simp [h]) fun ha0 ↦ (eq_or_ne b 0).elim (fun h ↦
    by simp [h]) fun hb0 ↦ (eq_or_ne a ⊤).elim (fun h ↦ by simp [h]) fun ha ↦ (eq_or_ne b ⊤).elim
    (fun h ↦ by simp [h]) fun hb ↦ hp.eq_or_lt.elim (fun h ↦ by simp [← h]) fun hp_gt ↦
    (ennreal_rpow_inv_add_lt ha0 hb0 ha hb hp_gt).le
/-- **Layer-cake `L^{p,1} ↪ L^p` seminorm embedding** for `f : α → ℝ≥0∞` and `1 ≤ p`. -/
theorem eLpNorm_le_lintegral_meas_lt_rpow_inv {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp : 1
    ≤ p) : eLpNorm f (ENNReal.ofReal p) μ ≤ ∫⁻ t in Ioi (0 : ℝ), (μ {x | ENNReal.ofReal t < f x}) ^
    (1 / p) := by
  have hp0 : 0 < p := (by linarith); have h := eLpNorm_rpow_eq_lintegral (ENNReal.ofReal_pos.2
    hp0).ne' ENNReal.ofReal_ne_top hf; rw [ENNReal.toReal_ofReal hp0.le] at h; rw [←
    ENNReal.rpow_le_rpow_iff hp0, h, lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul μ hf hp0,
    setLIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ mul_comm _ _]; exact
    mul_setLIntegral_Ioi_rpow_sub_one_le (Φ := fun t ↦ μ {x | ENNReal.ofReal t < f x}) (fun a _ b _
    hab ↦ measure_mono fun _ hx ↦ (ENNReal.ofReal_le_ofReal hab).trans_lt hx) hp
/-- Equality of `eLpNorm u` and `eLpNorm (fun x ↦ ENNReal.ofReal |u x|)` for `0 < p`. -/
theorem eLpNorm_eq_eLpNorm_ofReal_abs {u : α → ℝ} (hu : AEStronglyMeasurable u μ) {p : ℝ} (hp0 : 0 <
    p) : eLpNorm u (ENNReal.ofReal p) μ = eLpNorm (fun x ↦ ENNReal.ofReal |u x|) (ENNReal.ofReal p)
    μ := by
  have h1 := eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne'
    ENNReal.ofReal_ne_top hu; have h2 := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top
    hu.aemeasurable.norm.ennreal_ofReal.aestronglyMeasurable; simp_rw [Real.norm_eq_abs] at h2; rw
    [h1, h2]; simp [Real.enorm_eq_ofReal_abs]
/-- **Layer-cake `L^{p,1} ↪ L^p` seminorm embedding** for `u : α → ℝ` and `1 ≤ p`. -/
theorem eLpNorm_le_lintegral_meas_abs_lt_rpow_inv {u : α → ℝ} (hu : AEStronglyMeasurable u μ) {p :
    ℝ} (hp : 1 ≤ p) : eLpNorm u (ENNReal.ofReal p) μ ≤ ∫⁻ t in Ioi (0 : ℝ), (μ {x | t < |u x|}) ^ (1
    / p) := by
  rw [eLpNorm_eq_eLpNorm_ofReal_abs hu (by linarith)]; refine (eLpNorm_le_lintegral_meas_lt_rpow_inv
    hu.aemeasurable.norm.ennreal_ofReal hp).trans_eq (setLIntegral_congr_fun measurableSet_Ioi fun t
    ht ↦ ?_); congr 2; ext x; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mem_Ioi.1 ht).le
/-- Pointwise subadditivity of `(μ {x | t < |u x|}) ^ (1 / p)` into signed superlevel parts. -/
theorem measure_abs_lt_rpow_inv_le {u : α → ℝ} (hu : AEStronglyMeasurable u μ) {p t : ℝ} (hp : 1 ≤
    p) (ht : 0 < t) : (μ {x | t < |u x|}) ^ (1 / p) ≤ (μ {x | t < u x}) ^ (1 / p) + (μ {x | u x <
    -t}) ^ (1 / p) := by
  have hset : {x | t < |u x|} = {x | t < u x} ∪ {x | u x < -t} := (by ext x; simp [lt_abs, lt_neg]);
    have hdisj : Disjoint {x | t < u x} {x | u x < -t} := Set.disjoint_left.2 fun x (hx₁ : t < u x)
    (hx₂ : u x < -t) ↦ (by linarith); have hnm : NullMeasurableSet {x | u x < -t} μ :=
    hu.aemeasurable.nullMeasurable measurableSet_Iio; rw [hset, measure_union₀ hnm
    hdisj.aedisjoint]; exact ennreal_rpow_inv_add_le hp
/-- Two-sided **signed layer-cake `L^{p,1} ↪ L^p` seminorm inequality** for `u : α → ℝ`. -/
theorem eLpNorm_le_add_lintegral_meas_lt_rpow_inv {u : α → ℝ} (hu : AEStronglyMeasurable u μ) {p :
    ℝ} (hp : 1 ≤ p) : eLpNorm u (ENNReal.ofReal p) μ ≤ (∫⁻ t in Ioi (0 : ℝ), (μ {x | t < u x}) ^ (1
    / p)) + ∫⁻ t in Ioi (0 : ℝ), (μ {x | u x < -t}) ^ (1 / p) := by
  have hanti₁ : AntitoneOn (fun t : ℝ ↦ (μ {x | t < u x}) ^ (1 / p)) (Ioi 0) := fun a _ b _ hab ↦
    ENNReal.rpow_le_rpow (measure_mono fun x hx ↦ hab.trans_lt hx) (by positivity); rw [←
    lintegral_add_left' (aemeasurable_of_antitoneOn_Ioi_ennreal hanti₁)]; exact
    (eLpNorm_le_lintegral_meas_abs_lt_rpow_inv hu hp).trans (setLIntegral_mono_ae' measurableSet_Ioi
    (Eventually.of_forall fun _ ht ↦ measure_abs_lt_rpow_inv_le hu hp (mem_Ioi.1 ht)))
/-- **Absence of sign cancellation at equality**: either `0 ≤ᵐ[μ] u` or `u ≤ᵐ[μ] 0`. -/
theorem ae_nonneg_or_ae_nonpos_of_eLpNorm_eq_add_lintegral {u : α → ℝ} (hu : AEStronglyMeasurable u
    μ) {p : ℝ} (hp : 1 < p) (hfin : eLpNorm u (ENNReal.ofReal p) μ ≠ ⊤) (heq : eLpNorm u
    (ENNReal.ofReal p) μ = (∫⁻ t in Ioi (0 : ℝ), (μ {x | t < u x}) ^ (1 / p)) + ∫⁻ t in Ioi (0 : ℝ),
    (μ {x | u x < -t}) ^ (1 / p)) : (∀ᵐ x ∂μ, 0 ≤ u x) ∨ (∀ᵐ x ∂μ, u x ≤ 0) := by
  by_contra hcontra; rw [not_or] at hcontra; rcases hcontra with ⟨hnnn, hnnp⟩; have hpn : μ {x | 0 <
    -u x} ≠ 0 := (by rw [ae_iff] at hnnn; simpa using hnnn); have hpp : μ {x | 0 < u x} ≠ 0 :=
    (by rw [ae_iff] at hnnp; simpa using hnnp); rw [setOf_lt_eq_iUnion_add_one_div u 0, Ne,
    measure_iUnion_null_iff, not_forall] at hpp; rw [setOf_lt_eq_iUnion_add_one_div (fun x ↦ -u x)
    0, Ne, measure_iUnion_null_iff, not_forall] at hpn; obtain ⟨n₁, hn₁⟩ := hpp; obtain ⟨n₂, hn₂⟩ :=
    hpn; let t₀ : ℝ := min (1 / (n₁ + 1 : ℝ)) (1 / (n₂ + 1 : ℝ)); have ht₀_pos : 0 < t₀ := lt_min
    (by positivity) (by positivity); let A : ℝ → ℝ≥0∞ := fun t ↦ (μ {x | t < |u x|}) ^ (1 / p); let
    B₁ : ℝ → ℝ≥0∞ := fun t ↦ (μ {x | t < u x}) ^ (1 / p); let B₂ : ℝ → ℝ≥0∞ := fun t ↦ (μ {x | u x <
    -t}) ^ (1 / p); have hAm := aemeasurable_of_antitoneOn_Ioi_ennreal (Φ := A) fun a _ b _ hab ↦
    ENNReal.rpow_le_rpow (measure_mono fun x hx ↦ hab.trans_lt hx) (by positivity); have hB1m :=
    aemeasurable_of_antitoneOn_Ioi_ennreal (Φ := B₁) fun a _ b _ hab ↦ ENNReal.rpow_le_rpow
    (measure_mono fun x hx ↦ hab.trans_lt hx) (by positivity); have hB2m :=
    aemeasurable_of_antitoneOn_Ioi_ennreal (Φ := B₂) fun a _ b _ hab ↦ ENNReal.rpow_le_rpow
    (measure_mono fun x hx ↦ hx.trans_le (neg_le_neg hab)) (by positivity); have hAB_le : ∀ t ∈ Ioi
    (0 : ℝ), A t ≤ B₁ t + B₂ t := fun t ht ↦ measure_abs_lt_rpow_inv_le hu hp.le (mem_Ioi.1 ht);
    have hlte : ∫⁻ t in Ioi (0 : ℝ), A t = ∫⁻ t in Ioi (0 : ℝ), (B₁ t + B₂ t) := (by
    refine le_antisymm (setLIntegral_mono_ae' measurableSet_Ioi (Eventually.of_forall hAB_le)) ?_;
      rw [lintegral_add_left' hB1m, ← heq]; exact eLpNorm_le_lintegral_meas_abs_lt_rpow_inv hu
        hp.le); have hB_fin : ∫⁻ t in Ioi (0 : ℝ), (B₁ t + B₂ t) ≠ ⊤ :=
        (by rw [lintegral_add_left' hB1m, ← heq]; exact hfin); have hsub_zero : ∫⁻ t in Ioi (0 : ℝ),
        ((B₁ t + B₂ t) - A t) = 0 := (by
    rw [lintegral_sub' hAm (hlte ▸ hB_fin) (ae_restrict_of_forall_mem measurableSet_Ioi hAB_le),
      hlte, tsub_self]); have hae_sub := (lintegral_eq_zero_iff' ((hB1m.add hB2m).sub hAm)).1
        hsub_zero; have haeB := ae_lt_top' (hB1m.add hB2m) hB_fin; have hae_eq : ∀ᵐ t
        ∂volume.restrict (Ioi (0 : ℝ)), A t = B₁ t + B₂ t ∧ B₁ t + B₂ t ≠ ⊤ := (by
    filter_upwards [hae_sub, haeB, ae_restrict_mem measurableSet_Ioi] with t ht₁ ht₂ ht₃ using
      ⟨le_antisymm (hAB_le t ht₃) (tsub_eq_zero_iff_le.1 ht₁), ht₂.ne⟩); have hae_Ioo := ae_mono
        (Measure.restrict_mono (Ioo_subset_Ioi_self : Ioo 0 t₀ ⊆ Ioi 0) le_rfl) hae_eq; have hne :
        NeBot (ae (volume.restrict (Ioo 0 t₀))) := (by
    rw [ae_neBot]; intro h0; apply (ENNReal.ofReal_pos.2 ht₀_pos).ne'; simpa
      [Measure.restrict_apply_self, Real.volume_Ioo] using congrArg (fun ν ↦ ν (Ioo 0 t₀)) h0);
        obtain ⟨t, ht_mem, ht_AB, ht_fin⟩ := ((ae_restrict_mem measurableSet_Ioo).and
        hae_Ioo).exists; have h1_ne0 : μ {x | t < u x} ≠ 0 := fun h0 ↦ hn₁ <| measure_mono_null (fun
        x (hx : 0 + 1 / (n₁ + 1 : ℝ) < u x) ↦ lt_trans (ht_mem.2.trans_le (min_le_left _ _))
        (by simpa using hx)) h0; have h2_ne0 : μ {x | u x < -t} ≠ 0 := fun h0 ↦ hn₂ <|
        measure_mono_null (fun x (hx : 0 + 1 / (n₂ + 1 : ℝ) < -u x) ↦ lt_neg_of_lt_neg (lt_trans
        (ht_mem.2.trans_le (min_le_right _ _)) (by simpa using hx))) h0; have h1_fin : μ {x | t < u
        x} ≠ ⊤ := (fun htop ↦ ht_fin <| by
    dsimp [B₁]; rw [htop, ENNReal.top_rpow_of_pos (by positivity), top_add]); have h2_fin : μ {x | u
      x < -t} ≠ ⊤ := (fun htop ↦ ht_fin <| by
    dsimp [B₂]; rw [htop, ENNReal.top_rpow_of_pos (by positivity), add_top]); have hset : {x | t <
      |u x|} = {x | t < u x} ∪ {x | u x < -t} := (by ext x; simp [lt_abs, lt_neg]); have hdisj :
      Disjoint {x | t < u x} {x | u x < -t} := Set.disjoint_left.2 fun x (hx₁ : t < u x) (hx₂ : u x
      < -t) ↦ (by linarith [ht_mem.1]); have hnm : NullMeasurableSet {x | u x < -t} μ :=
      hu.aemeasurable.nullMeasurable measurableSet_Iio; have hlt := ennreal_rpow_inv_add_lt h1_ne0
      h2_ne0 h1_fin h2_fin hp; rw [← measure_union₀ hnm hdisj.aedisjoint, ← hset] at hlt; exact
      hlt.ne ht_AB
/-- **Superlevel set nesting and single-indicator rigidity**: `u =ᵐ[μ] c • χ_{u ≠ 0}` (`c ≠ 0`). -/
theorem ae_eq_const_indicator_of_eLpNorm_eq_lintegral_rpow_distribution {u : α → ℝ} (hu :
    AEStronglyMeasurable u μ) {p : ℝ} (hp : 1 < p) (hpos : 0 < eLpNorm u (ENNReal.ofReal p) μ) (hfin
    : eLpNorm u (ENNReal.ofReal p) μ ≠ ⊤) (heq : eLpNorm u (ENNReal.ofReal p) μ = (∫⁻ t in Ioi (0 :
    ℝ), (μ {x | t < u x}) ^ (1 / p)) + ∫⁻ t in Ioi (0 : ℝ), (μ {x | u x < -t}) ^ (1 / p)) : ∃ c ≠ (0
    : ℝ), 0 < μ {x | u x ≠ 0} ∧ μ {x | u x ≠ 0} ≠ ⊤ ∧ (∀ t ∈ Ioo 0 |c|, {x | t < |u x|} =ᵐ[μ] {x | u
    x ≠ 0}) ∧ u =ᵐ[μ] {x | u x ≠ 0}.indicator (fun _ ↦ c) := by
  have hp0 : 0 < p := (by linarith); have hf : AEMeasurable (fun x ↦ ENNReal.ofReal |u x|) μ :=
    hu.aemeasurable.norm.ennreal_ofReal; have habs_eq : eLpNorm u (ENNReal.ofReal p) μ = ∫⁻ t in Ioi
    (0 : ℝ), (μ {x | t < |u x|}) ^ (1 / p) := (le_antisymm
    (eLpNorm_le_lintegral_meas_abs_lt_rpow_inv hu hp.le) <| by
    rw [heq]; have hanti₁ : AntitoneOn (fun t : ℝ ↦ (μ {x | t < u x}) ^ (1 / p)) (Ioi 0) := fun a _
      b _ hab ↦ ENNReal.rpow_le_rpow (measure_mono fun x hx ↦ hab.trans_lt hx) (by positivity); rw
      [← lintegral_add_left' (aemeasurable_of_antitoneOn_Ioi_ennreal hanti₁)]; exact
      setLIntegral_mono_ae' measurableSet_Ioi (Eventually.of_forall fun _ ht ↦
      measure_abs_lt_rpow_inv_le hu hp.le (mem_Ioi.1 ht))); let Φ : ℝ → ℝ≥0∞ := fun t ↦ μ {x | t <
        |u x|}; have hΦ_anti : AntitoneOn Φ (Ioi 0) := fun a _ b _ hab ↦ measure_mono fun x hx ↦
        hab.trans_lt hx; have hΦ_eq : ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p
        - 1)) * Φ t = (∫⁻ t in Ioi (0 : ℝ), Φ t ^ (1 / p)) ^ p := (by
    have h1 := eLpNorm_rpow_eq_lintegral (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hf; rw
      [ENNReal.toReal_ofReal hp0.le, ← eLpNorm_eq_eLpNorm_ofReal_abs hu hp0, habs_eq,
      lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul μ hf hp0] at h1; dsimp [Φ]; rw [h1]; congr 1;
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_; rw [mul_comm]; congr 2; ext x;
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mem_Ioi.1 ht).le).symm); obtain ⟨c₀, hc₀_nn, M,
        hM_fin, hIoo, hIoi⟩ := eq_step_of_mul_setLIntegral_Ioi_rpow_sub_one_eq hΦ_anti hp (habs_eq ▸
        hfin) hΦ_eq; have hc₀_pos : 0 < c₀ := (by
    refine hc₀_nn.lt_of_ne fun h0 ↦ hpos.ne' (habs_eq.trans <| ?_); refine (setLIntegral_congr_fun
      measurableSet_Ioi (g := fun _ ↦ 0) fun t ht ↦ ?_).trans lintegral_zero; change Φ t ^ (1 / p) =
      0; rw [hIoi t (h0 ▸ ht), ENNReal.zero_rpow_of_pos (by positivity)]); have hse : {x | u x ≠ 0}
        = ⋃ n : ℕ, {x | min (c₀ / 2) (1 / (n + 1 : ℝ)) < |u x|} := (by
    ext x; simp only [Set.mem_ofPred_eq, mem_iUnion, ← abs_pos, min_lt_iff]; exact ⟨fun hx ↦
      (exists_nat_one_div_lt hx).imp fun _ ↦ Or.inr, fun ⟨n, hn⟩ ↦ hn.elim (fun h ↦ (half_pos
      hc₀_pos).trans h) (fun h ↦ (div_pos zero_lt_one (Nat.cast_add_one_pos n)).trans h)⟩); have hms
        : Monotone (fun n : ℕ ↦ {x | min (c₀ / 2) (1 / (n + 1 : ℝ)) < |u x|}) := fun m n hmn _ hx ↦
        (min_le_min le_rfl (one_div_le_one_div_of_le (Nat.cast_add_one_pos m)
        (by exact_mod_cast Nat.add_le_add_right hmn 1 : (m : ℝ) + 1 ≤ n + 1))).trans_lt hx; have
        hμ_supp : μ {x | u x ≠ 0} = M := (by
    have hconst : (fun n : ℕ ↦ μ {x | min (c₀ / 2) (1 / (n + 1 : ℝ)) < |u x|}) = fun _ ↦ M := funext
      fun n ↦ hIoo _ ⟨lt_min (by linarith) (by positivity), (min_le_left _ _).trans_lt
      (by linarith)⟩; rw [hse, hms.measure_iUnion, hconst, ciSup_const]); have hM_pos : 0 < M := (by
    rw [← hμ_supp, pos_iff_ne_zero]; intro h0; have hae0 : u =ᵐ[μ] 0 :=
      (by rw [Filter.EventuallyEq, ae_iff]; simpa using h0); exact hpos.ne'
      (by rw [eLpNorm_congr_ae hae0, eLpNorm_zero])); have hsa : ∀ t ∈ Ioo 0 c₀, {x | t < |u x|}
        =ᵐ[μ] {x | u x ≠ 0} := fun t ht ↦ ae_eq_of_subset_of_measure_ge (fun _ (hx : t < |u _|) ↦
        abs_pos.1 (ht.1.trans hx)) (by rw [hμ_supp, ← hIoo t ht])
        (hu.aemeasurable.norm.nullMeasurable measurableSet_Ioi) (hμ_supp ▸ hM_fin); have hgn : μ {x
        | c₀ < |u x|} = 0 := setOf_lt_eq_iUnion_add_one_div (fun x ↦ |u x|) c₀ ▸
        measure_iUnion_null_iff.2 fun n ↦ hIoi (c₀ + 1 / (n + 1 : ℝ)) (lt_add_of_pos_right c₀
        (by positivity)); have hln : μ {x | u x ≠ 0 ∧ |u x| < c₀} = 0 := (by
    refine measure_mono_null (t := ⋃ n : ℕ, ({x | u x ≠ 0} \ {x | max (c₀ / 2) (c₀ - 1 / (n + 1 :
      ℝ)) < |u x|})) (fun x ⟨hx0, hxc⟩ ↦ ?_) (measure_iUnion_null_iff.2 fun n ↦ (ae_eq_set.1 (hsa _
      ⟨lt_max_of_lt_left (by linarith), max_lt (by linarith) (sub_lt_self c₀ (by positivity))⟩)).2);
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hxc); exact mem_iUnion.2 ⟨n, hx0, not_lt.2
      ((by linarith : |u x| ≤ c₀ - 1 / (n + 1 : ℝ)).trans (le_max_right _ _))⟩); have hae_abs : (fun
        x ↦ |u x|) =ᵐ[μ] {x | u x ≠ 0}.indicator (fun _ ↦ c₀) := (by
    have h1 : ∀ᵐ x ∂μ, x ∉ {x | c₀ < |u x|} := (by rw [ae_iff]; simpa using hgn); have h2 : ∀ᵐ x ∂μ,
      x ∉ {x | u x ≠ 0 ∧ |u x| < c₀} := (by rw [ae_iff]; simpa using hln); filter_upwards [h1, h2]
      with x hx1 hx2; refine (em (u x = 0)).elim (fun hx0 ↦ by simp [hx0]) fun hx0 ↦ ?_; rw
      [indicator_of_mem hx0]; exact le_antisymm (not_lt.1 hx1) (not_lt.1 fun h ↦ hx2 ⟨hx0, h⟩));
        refine (ae_nonneg_or_ae_nonpos_of_eLpNorm_eq_add_lintegral hu hp hfin heq).elim (fun hnn ↦
        ⟨c₀, hc₀_pos.ne', hμ_supp ▸ hM_pos, hμ_supp ▸ hM_fin, by rwa [abs_of_pos hc₀_pos], (hnn.and
        hae_abs).mono fun x ⟨hx_nn, hx_abs⟩ ↦
        by change |u x| = _ at hx_abs; rwa [abs_of_nonneg hx_nn] at hx_abs⟩) fun hnp ↦ ⟨-c₀,
        neg_ne_zero.2 hc₀_pos.ne', hμ_supp ▸ hM_pos, hμ_supp ▸ hM_fin,
        by rwa [abs_neg, abs_of_pos hc₀_pos], (hnp.and hae_abs).mono fun x ⟨hx_np, hx_abs⟩ ↦ ?_⟩;
        change |u x| = _ at hx_abs; rw [abs_of_nonpos hx_np] at hx_abs; refine (em (u x = 0)).elim
        (fun hx0 ↦ by simp [hx0]) fun hx0 ↦ ?_; rw [indicator_of_mem hx0] at hx_abs ⊢; linarith
end LayerCakeLp1
/-- The critical Sobolev–Gagliardo–Nirenberg exponent `n / (n - 1)` in dimension `n`. -/
noncomputable def bvSobolevExponent (n : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) - 1)
/-- For `2 ≤ n`, the BV Sobolev exponent `n / (n - 1)` is strictly greater than `1`. -/
theorem one_lt_bvSobolevExponent {n : ℕ} (hn : 2 ≤ n) : 1 < bvSobolevExponent n := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := (by exact_mod_cast hn); rw [bvSobolevExponent, one_lt_div
    (by linarith)]; linarith
/-- The reciprocal of `bvSobolevExponent n` is `(n - 1) / n`. -/
theorem inv_bvSobolevExponent (n : ℕ) : 1 / bvSobolevExponent n = ((n : ℝ) - 1) / (n : ℝ) :=
  one_div_div (n : ℝ) ((n : ℝ) - 1)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
/-- The sharp endpoint BV Sobolev constant `(n * μ(B(0, 1)) ^ (1 / n))⁻¹` on `E`. -/
noncomputable def bvSobolevConstant (μ : Measure E := by volume_tac) : ℝ≥0∞ := ((Module.finrank ℝ E
  : ℝ≥0∞) * (μ (Metric.ball (0 : E) 1)) ^ (1 / (Module.finrank ℝ E : ℝ)))⁻¹
omit [BorelSpace E] in
/-- In a nontrivial space `E`, `bvSobolevConstant μ ≠ 0`. -/
theorem bvSobolevConstant_ne_zero : bvSobolevConstant μ ≠ 0 := by
  rw [bvSobolevConstant, ENNReal.inv_ne_zero]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) measure_ball_lt_top.ne).ne
omit [BorelSpace E] in
/-- In a nontrivial space `E`, `bvSobolevConstant μ ≠ ⊤`. -/
theorem bvSobolevConstant_ne_top [Nontrivial E] : bvSobolevConstant μ ≠ ⊤ := by
  rw [bvSobolevConstant, ENNReal.inv_ne_top]; exact mul_ne_zero (Nat.cast_ne_zero.2
    (Module.finrank_pos (R := ℝ) (M := E)).ne') (ENNReal.rpow_pos (Metric.measure_ball_pos μ (0 : E)
    zero_lt_one) measure_ball_lt_top.ne).ne'
omit [BorelSpace E] in
/-- Cancellation identity `bvSobolevConstant μ * ((bvSobolevConstant μ)⁻¹ * x) = x`. -/
@[simp]
theorem bvSobolevConstant_mul_inv_cancel [Nontrivial E] (x : ℝ≥0∞) : bvSobolevConstant μ *
    ((bvSobolevConstant μ)⁻¹ * x) = x := by
  rw [← mul_assoc, ENNReal.mul_inv_cancel bvSobolevConstant_ne_zero bvSobolevConstant_ne_top,
    one_mul]
omit [BorelSpace E] in
/-- Cancellation identity `(bvSobolevConstant μ)⁻¹ * (bvSobolevConstant μ * x) = x`. -/
@[simp]
theorem inv_bvSobolevConstant_mul_cancel [Nontrivial E] (x : ℝ≥0∞) : (bvSobolevConstant μ)⁻¹ *
    (bvSobolevConstant μ * x) = x := by
  rw [← mul_assoc, ENNReal.inv_mul_cancel bvSobolevConstant_ne_zero bvSobolevConstant_ne_top,
    one_mul]
/-- Exact isoperimetric identity for an open ball `B(a, r)` (`r > 0`) in `1 / p` power form. -/
theorem perimeter_ball_eq_inv_bvSobolevConstant_mul_rpow [Nontrivial E] (a : E) {r : ℝ} (hr : 0 < r)
    : perimeter μ (Metric.ball a r) = (bvSobolevConstant μ)⁻¹ * (μ (Metric.ball a r)) ^ (1 /
    bvSobolevExponent (Module.finrank ℝ E)) := by
  set n := Module.finrank ℝ E; have hn_pos : 0 < n := Module.finrank_pos; have hn_real : 0 < (n : ℝ)
    := Nat.cast_pos.2 hn_pos; have hpow := congrArg (fun x : ℝ≥0∞ ↦ x ^ (1 / (n : ℝ)))
    (perimeter_ball_pow_finrank (μ := μ) a hr); rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    mul_one_div_cancel hn_real.ne', ENNReal.rpow_one, ENNReal.mul_rpow_of_nonneg _ _
    (by positivity), ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_natCast, ←
    ENNReal.rpow_mul, mul_one_div_cancel hn_real.ne', ENNReal.rpow_one, ← ENNReal.rpow_natCast, ←
    ENNReal.rpow_mul, Nat.cast_sub hn_pos, Nat.cast_one, ← div_eq_mul_one_div] at hpow; rw [hpow,
    bvSobolevConstant, inv_inv, inv_bvSobolevExponent]
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The whole-space distributional variation of `s.indicator (fun _ ↦ c)` is `|c| * perimeter`. -/
theorem distributionalVariation_top_const_indicator (c : ℝ) (s : Set E) : distributionalVariation μ
    ⊤ (s.indicator (fun _ ↦ c)) = ENNReal.ofReal |c| * perimeter μ s := by
  have heq : s.indicator (fun _ : E ↦ c) = c • s.indicator (fun _ ↦ (1 : ℝ)) :=
    (by ext x; by_cases hx : x ∈ s <;> simp [hx]); rw [heq, distributionalVariation_smul, perimeter,
    relativePerimeter]
/-- **Exact equality in the sharp BV Sobolev inequality for open ball indicators**. -/
theorem eLpNorm_ball_indicator_eq_bvSobolevConstant_mul_distributionalVariation (hn : 2 ≤
    Module.finrank ℝ E) (a : E) {r : ℝ} (hr : 0 < r) (c : ℝ) : eLpNorm ((Metric.ball a r).indicator
    (fun _ ↦ c)) (ENNReal.ofReal (bvSobolevExponent (Module.finrank ℝ E))) μ = bvSobolevConstant μ *
    distributionalVariation μ ⊤ ((Metric.ball a r).indicator (fun _ ↦ c)) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (Nat.zero_lt_of_lt hn); have hp0
    := zero_lt_one.trans (one_lt_bvSobolevExponent hn); rw [eLpNorm_indicator_const
    measurableSet_ball.nullMeasurableSet (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, Real.enorm_eq_ofReal_abs,
    distributionalVariation_top_const_indicator, perimeter_ball_eq_inv_bvSobolevConstant_mul_rpow a
    hr, ← mul_assoc, mul_comm (bvSobolevConstant μ), mul_assoc, bvSobolevConstant_mul_inv_cancel]
/-- **Exact equality in the sharp BV Sobolev inequality for closed ball indicators**. -/
theorem eLpNorm_closedBall_indicator_eq_bvSobolevConstant_mul_distributionalVariation (hn : 2 ≤
    Module.finrank ℝ E) (a : E) {r : ℝ} (hr : 0 < r) (c : ℝ) : eLpNorm ((Metric.closedBall a
    r).indicator (fun _ ↦ c)) (ENNReal.ofReal (bvSobolevExponent (Module.finrank ℝ E))) μ =
    bvSobolevConstant μ * distributionalVariation μ ⊤ ((Metric.closedBall a r).indicator (fun _ ↦
    c)) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (Nat.zero_lt_of_lt hn); have hp0
    := zero_lt_one.trans (one_lt_bvSobolevExponent hn); rw [eLpNorm_indicator_const
    measurableSet_closedBall.nullMeasurableSet (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, Real.enorm_eq_ofReal_abs, Measure.addHaar_closedBall μ a hr.le, ←
    Measure.addHaar_ball μ a hr.le, distributionalVariation_top_const_indicator,
    perimeter_closedBall_eq_ball, perimeter_ball_eq_inv_bvSobolevConstant_mul_rpow a hr, ←
    mul_assoc, mul_comm (bvSobolevConstant μ), mul_assoc, bvSobolevConstant_mul_inv_cancel]
/-- Superlevel isoperimetric condition for `u : E → ℝ` on signed superlevel sets. -/
def HasSuperlevelIsoperimetry (μ : Measure E) (u : E → ℝ) : Prop := (∀ᵐ t ∂volume.restrict (Ioi (0 :
  ℝ)), (bvSobolevConstant μ)⁻¹ * (μ {x | t < u x}) ^ (1 / bvSobolevExponent (Module.finrank ℝ E)) ≤
  perimeter μ {x | t < u x}) ∧ (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), (bvSobolevConstant μ)⁻¹ * (μ {x
  | u x < -t}) ^ (1 / bvSobolevExponent (Module.finrank ℝ E)) ≤ perimeter μ {x | u x < -t})
omit [BorelSpace E] in
/-- Superlevel isoperimetry and coarea bound the signed `L^{p,1}` layer-cake functional. -/
theorem add_lintegral_meas_lt_rpow_inv_le_bvSobolevConstant_mul_distributionalVariation (hn : 2 ≤
    Module.finrank ℝ E) {u : E → ℝ} (hcoarea : (∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | t < u x}) + ∫⁻
    t in Ioi (0 : ℝ), perimeter μ {x | u x < -t} ≤ distributionalVariation μ ⊤ u) (hisop :
    HasSuperlevelIsoperimetry μ u) : (∫⁻ t in Ioi (0 : ℝ), (μ {x | t < u x}) ^ (1 /
    bvSobolevExponent (Module.finrank ℝ E))) + ∫⁻ t in Ioi (0 : ℝ), (μ {x | u x < -t}) ^ (1 /
    bvSobolevExponent (Module.finrank ℝ E)) ≤ bvSobolevConstant μ * distributionalVariation μ ⊤ u :=
    by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (Nat.zero_lt_of_lt hn); set p :=
    bvSobolevExponent (Module.finrank ℝ E); have hpos_le : ∫⁻ t in Ioi (0 : ℝ), (μ {x | t < u x}) ^
    (1 / p) ≤ bvSobolevConstant μ * ∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | t < u x} := (by
    rw [← lintegral_const_mul' _ _ bvSobolevConstant_ne_top]; refine lintegral_mono_ae ?_;
      filter_upwards [hisop.1] with t ht; rw [← bvSobolevConstant_mul_inv_cancel (μ := μ) ((μ {x | t
      < u x}) ^ (1 / p))]; gcongr); have hneg_le : ∫⁻ t in Ioi (0 : ℝ), (μ {x | u x < -t}) ^ (1 / p)
        ≤ bvSobolevConstant μ * ∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | u x < -t} := (by
    rw [← lintegral_const_mul' _ _ bvSobolevConstant_ne_top]; refine lintegral_mono_ae ?_;
      filter_upwards [hisop.2] with t ht; rw [← bvSobolevConstant_mul_inv_cancel (μ := μ) ((μ {x | u
      x < -t}) ^ (1 / p))]; gcongr); exact (add_le_add hpos_le hneg_le).trans ((mul_add _ _
        _).symm.trans_le (by gcongr))
omit [BorelSpace E] in
/-- **Sharp Endpoint BV Sobolev Inequality**: `‖u‖_{n/(n-1)} ≤ C_n * |Du|(E)`. -/
theorem eLpNorm_le_bvSobolevConstant_mul_distributionalVariation (hn : 2 ≤ Module.finrank ℝ E) {u :
  E → ℝ} (hu : AEStronglyMeasurable u μ) (hcoarea : (∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | t < u x})
  + ∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | u x < -t} ≤ distributionalVariation μ ⊤ u) (hisop :
  HasSuperlevelIsoperimetry μ u) : eLpNorm u (ENNReal.ofReal (bvSobolevExponent (Module.finrank ℝ
  E))) μ ≤ bvSobolevConstant μ * distributionalVariation μ ⊤ u :=
  (eLpNorm_le_add_lintegral_meas_lt_rpow_inv hu (one_lt_bvSobolevExponent hn).le).trans
  (add_lintegral_meas_lt_rpow_inv_le_bvSobolevConstant_mul_distributionalVariation hn hcoarea hisop)
omit [BorelSpace E] in
/-- Every `BV` function on `E` with superlevel coarea and isoperimetry lies in `L^{n/(n-1)}(E)`. -/
theorem eLpNorm_bvSobolevExponent_lt_top_of_isBVOn (hn : 2 ≤ Module.finrank ℝ E) {u : E → ℝ} (hu :
    IsBVOn μ ⊤ u) (hcoarea : (∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | t < u x}) + ∫⁻ t in Ioi (0 : ℝ),
    perimeter μ {x | u x < -t} ≤ distributionalVariation μ ⊤ u) (hisop : HasSuperlevelIsoperimetry μ
    u) : eLpNorm u (ENNReal.ofReal (bvSobolevExponent (Module.finrank ℝ E))) μ < ⊤ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (Nat.zero_lt_of_lt hn); have
    hmeas : AEStronglyMeasurable u μ :=
    (by have h := hu.1.aestronglyMeasurable; rwa [Opens.coe_top, Measure.restrict_univ] at h); exact
    (eLpNorm_le_bvSobolevConstant_mul_distributionalVariation hn hmeas hcoarea hisop).trans_lt
    (ENNReal.mul_lt_top bvSobolevConstant_ne_top.lt_top hu.2)
omit [BorelSpace E] in
/-- **Ball-Indicator Equality Classification**: at equality, `u =ᵐ[μ] c • χ_{B(a, r)}`. -/
theorem ae_eq_ball_indicator_of_bvSobolev_eq (hn : 2 ≤ Module.finrank ℝ E) {u : E → ℝ} (hu :
    AEStronglyMeasurable u μ) (hpos : 0 < eLpNorm u (ENNReal.ofReal (bvSobolevExponent
    (Module.finrank ℝ E))) μ) (hfin : distributionalVariation μ ⊤ u ≠ ⊤) (hcoarea : (∫⁻ t in Ioi (0
    : ℝ), perimeter μ {x | t < u x}) + ∫⁻ t in Ioi (0 : ℝ), perimeter μ {x | u x < -t} ≤
    distributionalVariation μ ⊤ u) (hisop : HasSuperlevelIsoperimetry μ u) (hrigid : ∀ s : Set E, 0
    < μ s → μ s ≠ ⊤ → perimeter μ s = (bvSobolevConstant μ)⁻¹ * (μ s) ^ (1 / bvSobolevExponent
    (Module.finrank ℝ E)) → ∃ (a : E) (r : ℝ), 0 < r ∧ s =ᵐ[μ] Metric.ball a r) (heq : eLpNorm u
    (ENNReal.ofReal (bvSobolevExponent (Module.finrank ℝ E))) μ = bvSobolevConstant μ *
    distributionalVariation μ ⊤ u) : ∃ (c : ℝ) (a : E) (r : ℝ), c ≠ 0 ∧ 0 < r ∧ (∀ t ∈ Ioo 0 |c|, {x
    | t < |u x|} =ᵐ[μ] Metric.ball a r) ∧ {x | u x ≠ 0} =ᵐ[μ] Metric.ball a r ∧ u =ᵐ[μ] (Metric.ball
    a r).indicator (fun _ ↦ c) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (Nat.zero_lt_of_lt hn); set p :=
    bvSobolevExponent (Module.finrank ℝ E); have hp := one_lt_bvSobolevExponent hn; have hp0 :=
    zero_lt_one.trans hp; have hnf : eLpNorm u (ENNReal.ofReal p) μ ≠ ⊤ := heq ▸ ENNReal.mul_ne_top
    bvSobolevConstant_ne_top hfin; have hle := le_antisymm
    (eLpNorm_le_add_lintegral_meas_lt_rpow_inv hu hp.le) (heq ▸
    add_lintegral_meas_lt_rpow_inv_le_bvSobolevConstant_mul_distributionalVariation hn hcoarea
    hisop); obtain ⟨c, hc0, hS_pos, hS_fin, hsuper, hu_ind⟩ :=
    ae_eq_const_indicator_of_eLpNorm_eq_lintegral_rpow_distribution hu hp hpos hnf hle; let S : Set
    E := {x | u x ≠ 0}; have hS_meas : NullMeasurableSet S μ := hu.aemeasurable.nullMeasurable
    isOpen_ne.measurableSet; have hisS : perimeter μ S = (bvSobolevConstant μ)⁻¹ * (μ S) ^ (1 / p)
    := (by
    have h1 : ENNReal.ofReal |c| * (bvSobolevConstant μ * perimeter μ S) = ENNReal.ofReal |c| * (μ
      S) ^ (1 / p) := (by
      rw [← mul_assoc, mul_comm (ENNReal.ofReal |c|), mul_assoc, ←
        distributionalVariation_top_const_indicator, ← distributionalVariation_congr_ae
        (by simpa [Opens.coe_top] using hu_ind), ← heq, eLpNorm_congr_ae hu_ind,
        eLpNorm_indicator_const hS_meas (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp0.le, Real.enorm_eq_ofReal_abs]); rw [← ENNReal.mul_right_inj
          (ENNReal.ofReal_pos.2 (abs_pos.2 hc0)).ne' ENNReal.ofReal_ne_top |>.1 h1,
          inv_bvSobolevConstant_mul_cancel]); obtain ⟨a, r, hr, hSb⟩ := hrigid S hS_pos hS_fin hisS;
            refine ⟨c, a, r, hc0, hr, fun t ht ↦ (hsuper t ht).trans hSb, hSb, hu_ind.trans
            (hSb.mono fun x hx ↦ ?_)⟩; have hmem : x ∈ S ↔ x ∈ Metric.ball a r :=
            (by simpa [eq_iff_iff] using hx); exact (em (x ∈ Metric.ball a r)).elim (fun hxb ↦
            by rw [indicator_of_mem (hmem.2 hxb), indicator_of_mem hxb]) (fun hxb ↦
            by rw [indicator_of_notMem (mt hmem.1 hxb), indicator_of_notMem hxb])
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- no continuous `u` agrees `μ`-a.e. with `c • χ_{B(a, r)}`. -/
theorem not_ae_eq_ball_indicator_of_continuous [Nontrivial E] {u : E → ℝ} (hu : Continuous u) (a :
    E) {r c : ℝ} (hr : 0 < r) (hc : c ≠ 0) : ¬ (u =ᵐ[μ] (Metric.ball a r).indicator (fun _ ↦ c)) :=
    by
  intro hae; have h_in : ∀ x ∈ Metric.ball a r, u x = c := (fun x hx ↦ by
    by_contra hne; exact ((Metric.isOpen_ball.inter (isOpen_ne_fun hu continuous_const)).measure_pos
      μ ⟨x, hx, hne⟩).ne' (measure_mono_null (fun y ⟨hyb, hyn⟩ ↦ by simpa [hyb] using hyn) (ae_iff.1
      hae))); have h_out : ∀ x ∈ (Metric.closedBall a r)ᶜ, u x = 0 := (fun x hx ↦ by
    by_contra hne; exact ((Metric.isClosed_closedBall.isOpen_compl.inter (isOpen_ne_fun hu
      continuous_const)).measure_pos μ ⟨x, hx, hne⟩).ne' (measure_mono_null (fun y ⟨hyc, hyn⟩ ↦ by
      have hyb : y ∉ Metric.ball a r := fun h ↦ hyc (Metric.ball_subset_closedBall h); simpa [hyb]
      using hyn) (ae_iff.1 hae))); obtain ⟨v, hv⟩ := exists_norm_eq E zero_le_one; let g : ℝ → E :=
        fun s ↦ a + s • v; have hg : Continuous (u ∘ g) := hu.comp (by fun_prop); have h_ic : r ∈ {s
        : ℝ | (u ∘ g) s = c} := (by
    have hr_mem : r ∈ closure (Ioo 0 r) := (by rw [closure_Ioo hr.ne]; exact right_mem_Icc.2 hr.le);
      refine closure_minimal (fun s hs ↦ h_in (g s) ?_) (isClosed_eq hg continuous_const) hr_mem; rw
      [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one,
      Real.norm_of_nonneg hs.1.le]; exact hs.2); have h_io : r ∈ {s : ℝ | (u ∘ g) s = 0} := (by
    have hr_mem : r ∈ closure (Ioi r) := (by rw [closure_Ioi]; exact self_mem_Ici); refine
      closure_minimal (fun s (hs : r < s) ↦ h_out (g s) ?_) (isClosed_eq hg continuous_const)
      hr_mem; rw [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      norm_smul, hv, mul_one, Real.norm_of_nonneg (hr.trans hs).le, not_le]; exact hs); exact hc
        (h_ic.symm.trans h_io)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise sandwich for `radialCubicCutoff a r ε` between open ball indicators. -/
theorem indicator_ball_le_radialCubicCutoff_and_le_indicator_ball (a : E) {r ε : ℝ} (hε : 0 < ε)
    (hεr : ε < r) (x : E) : (Metric.ball a (r - ε)).indicator (fun _ ↦ (1 : ℝ)) x ≤
    radialCubicCutoff a r ε x ∧ radialCubicCutoff a r ε x ≤ (Metric.ball a r).indicator (fun _ ↦ (1
    : ℝ)) x := by
  refine ⟨(em (x ∈ Metric.ball a (r - ε))).elim (fun hx ↦ ?_) (fun hx ↦
    by rw [indicator_of_notMem hx]; exact cubicCutoff_nonneg _), (em (x ∈ Metric.ball a r)).elim
    (fun hx ↦ by rw [indicator_of_mem hx]; exact cubicCutoff_le_one _) (fun hx ↦
    by rw [indicator_of_notMem hx, radialCubicCutoff_of_notMem_ball a hε hεr hx])⟩; have hrx : ‖x -
    a‖ ≤ r - ε :=
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using Metric.ball_subset_closedBall hx); rw
    [indicator_of_mem hx, radialCubicCutoff, cubicCutoff_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (by nlinarith [norm_nonneg (x - a)]) (by nlinarith))]
omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- Two-sided `L^p` norm bounds for the smooth radial cutoff `radialCubicCutoff a r ε`. -/
theorem eLpNorm_radialCubicCutoff_bounds (a : E) {r ε p : ℝ} (hε : 0 < ε) (hεr : ε < r) (hp : 0 < p)
    : (μ (Metric.ball a (r - ε))) ^ (1 / p) ≤ eLpNorm (radialCubicCutoff a r ε) (ENNReal.ofReal p) μ
    ∧ eLpNorm (radialCubicCutoff a r ε) (ENNReal.ofReal p) μ ≤ (μ (Metric.ball a r)) ^ (1 / p) := by
  have hp0 := (ENNReal.ofReal_pos.2 hp).ne'; have hind (s : ℝ) : (μ (Metric.ball a s)) ^ (1 / p) =
    eLpNorm ((Metric.ball a s).indicator (fun _ ↦ (1 : ℝ))) (ENNReal.ofReal p) μ := (by
    rw [eLpNorm_indicator_const measurableSet_ball.nullMeasurableSet hp0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le, enorm_one, one_mul]); rw [hind (r - ε), hind r]; exact
        ⟨eLpNorm_mono_real (aestronglyMeasurable_const.indicator measurableSet_ball) fun x ↦
        (Real.norm_of_nonneg (indicator_nonneg (fun _ _ ↦ zero_le_one) x)).le.trans
        (indicator_ball_le_radialCubicCutoff_and_le_indicator_ball a hε hεr x).1, eLpNorm_mono_real
        (contDiff_radialCubicCutoff a r ε).continuous.aestronglyMeasurable fun x ↦
        (Real.norm_of_nonneg (show 0 ≤ radialCubicCutoff a r ε x from cubicCutoff_nonneg
        _)).le.trans (indicator_ball_le_radialCubicCutoff_and_le_indicator_ball a hε hεr x).2⟩
/-- Lower bound on the total variation of `radialCubicCutoff a r ε` for `0 < ε < r`. -/
theorem distributionalVariation_radialCubicCutoff_ge (a : E) {r ε : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / (r + ε)) * μ (Metric.ball a (r - ε)) ≤
    distributionalVariation μ ⊤ (radialCubicCutoff a r ε) := by
  let R : ℝ := r + ε; let R' : ℝ := r + ε / 2; have hr : 0 < r := hε.trans hεr; have hRpos : 0 < R
    := (by dsimp [R]; linarith); have hR'R : R' < R := (by dsimp [R']; linarith)
  let χ : ContDiffBump a := ⟨r, R', hr, by dsimp [R']; linarith⟩
  let φ : 𝓓((⊤ : Opens E), E) := ⟨fun x ↦ R⁻¹ • (χ x • (x - a)), contDiff_const.smul
    (χ.contDiff.smul (contDiff_id.sub contDiff_const)), (χ.hasCompactSupport.smul_right).smul_left,
    subset_univ _⟩; have hφ_norm (x) : ‖φ x‖ ≤ 1 := (by
    change ‖R⁻¹ • (χ x • (x - a))‖ ≤ 1; rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2
      hRpos.le), Real.norm_of_nonneg χ.nonneg]; exact (em (x ∈ Metric.ball a R')).elim (fun hx ↦
      (mul_le_mul_of_nonneg_left (mul_le_mul χ.le_one ((mem_ball_iff_norm.1 hx).le.trans hR'R.le)
      (norm_nonneg _) zero_le_one) (inv_nonneg.2 hRpos.le)).trans_eq
      (by rw [one_mul, inv_mul_cancel₀ hRpos.ne'])) fun hx ↦
      (by simp [Function.notMem_support.1 (by rwa [χ.support_eq])])); have hdb : ∀ x ∈ Metric.ball a
        r, divergence (φ : E → E) x = (Module.finrank ℝ E : ℝ) / R := (fun x hx ↦ by
    have hev : (φ : E → E) =ᶠ[𝓝 x] fun y ↦ R⁻¹ • (y - a) := (by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy; change R⁻¹ • (χ y • (y - a)) = R⁻¹
        • (y - a); rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_smul]); rw
          [divergence, hev.fderiv_eq, ← divergence, divergence_smul_sub_const, div_eq_inv_mul]);
            have hsupp : HasCompactSupport (radialCubicCutoff a r ε) := (by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall a r) fun x hx ↦ ?_;
      by_contra hxr; exact hx (radialCubicCutoff_of_notMem_ball a hε hεr fun h ↦ hxr
      (Metric.ball_subset_closedBall h))); have hic := (contDiff_radialCubicCutoff a r
        ε).continuous.integrable_of_hasCompactSupport hsupp (μ := μ); have hii : Integrable
        ((Metric.ball a (r - ε)).indicator (fun _ ↦ (1 : ℝ))) μ := (integrable_indicator_iff
        measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne); have hc : (μ (Metric.ball
        a (r - ε))).toReal = ∫ x, (Metric.ball a (r - ε)).indicator (fun _ ↦ (1 : ℝ)) x ∂μ := (by
    rw [integral_indicator measurableSet_ball, setIntegral_const, Measure.real, smul_eq_mul,
      mul_one]); have hli : (μ (Metric.ball a (r - ε))).toReal ≤ ∫ x, radialCubicCutoff a r ε x ∂μ
        := hc ▸ integral_mono hii hic fun x ↦
        (indicator_ball_le_radialCubicCutoff_and_le_indicator_ball a hε hεr x).1; have hie : ∫ x in
        ((⊤ : Opens E) : Set E), radialCubicCutoff a r ε x * divergence (φ : E → E) x ∂μ =
        ((Module.finrank ℝ E : ℝ) / R) * ∫ x, radialCubicCutoff a r ε x ∂μ := (by
    rw [Opens.coe_top, Measure.restrict_univ, ← integral_const_mul]; refine integral_congr_ae
      (Eventually.of_forall fun x ↦ ?_); dsimp; exact (em (x ∈ Metric.ball a r)).elim (fun hx ↦
      by rw [hdb x hx, mul_comm]) fun hx ↦
        (by simp [radialCubicCutoff_of_notMem_ball a hε hεr hx])); have hlv :=
        le_distributionalVariation (μ := μ) φ hφ_norm (radialCubicCutoff a r ε); rw [hie] at hlv;
        refine (le_trans ?_ (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hli
        (by positivity)))).trans hlv; rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal
        measure_ball_lt_top.ne]
/-- As `ε → 0⁺`, `radialCubicCutoff a r ε` converges in `L^p` and variation to `χ_{B(a, r)}`. -/
theorem tendsto_eLpNorm_and_distributionalVariation_radialCubicCutoff (a : E) {r p : ℝ} (hr : 0 < r)
    (hp : 0 < p) : Tendsto (fun ε ↦ eLpNorm (radialCubicCutoff a r ε) (ENNReal.ofReal p) μ) (𝓝[>] 0)
    (𝓝 ((μ (Metric.ball a r)) ^ (1 / p))) ∧ Tendsto (fun ε ↦ distributionalVariation μ ⊤
    (radialCubicCutoff a r ε)) (𝓝[>] 0) (𝓝 (perimeter μ (Metric.ball a r))) := by
  have hsub : Tendsto (fun ε : ℝ ↦ r - ε) (𝓝 0) (𝓝 (r - 0)) := tendsto_const_nhds.sub tendsto_id; rw
    [sub_zero] at hsub; have hsl : Tendsto (fun ε : ℝ ↦ r - ε) (𝓝[>] 0) (𝓝 r) :=
    tendsto_nhdsWithin_of_tendsto_nhds hsub; have hadd : Tendsto (fun ε : ℝ ↦ r + ε) (𝓝 0) (𝓝 (r +
    0)) := tendsto_const_nhds.add tendsto_id; rw [add_zero] at hadd; have hal : Tendsto (fun ε : ℝ ↦
    r + ε) (𝓝[>] 0) (𝓝 r) := tendsto_nhdsWithin_of_tendsto_nhds hadd; have hbl : Tendsto (fun ε : ℝ
    ↦ μ (Metric.ball a (r - ε))) (𝓝[>] 0) (𝓝 (μ (Metric.ball a r))) := (by
    refine (subsingleton_or_nontrivial E).elim (fun hE ↦ tendsto_const_nhds.congr' <| by
      filter_upwards [Ioo_mem_nhdsGT hr] with ε hε; rw [Subsingleton.eq_univ_of_nonempty
      (Metric.nonempty_ball.2 (sub_pos.2 hε.2)), Subsingleton.eq_univ_of_nonempty
      (Metric.nonempty_ball.2 hr)]) fun hE ↦ ?_; have hpl : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ((r
      - ε) ^ Module.finrank ℝ E)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (r ^ Module.finrank ℝ E))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_id.pow _)).tendsto r).comp hsl; have h1_fin : μ
      (Metric.ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne; have hlim := ENNReal.Tendsto.mul_const
      hpl (Or.inr h1_fin); rw [← Measure.addHaar_ball μ a hr.le] at hlim; exact hlim.congr'
      (eventually_of_mem (Ioo_mem_nhdsGT hr) fun ε hε ↦ (Measure.addHaar_ball μ a (sub_pos.2
      hε.2).le).symm)); have h1 := (ENNReal.continuous_ofReal.tendsto ((Module.finrank ℝ E : ℝ) /
        r)).comp (tendsto_const_nhds.div hal hr.ne'); have h2 := (ENNReal.continuous_ofReal.tendsto
        ((Module.finrank ℝ E : ℝ) / r)).comp (tendsto_const_nhds.div hsl hr.ne'); exact
        ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' ((ENNReal.continuous_rpow_const.tendsto _).comp
        hbl) tendsto_const_nhds (eventually_of_mem (Ioo_mem_nhdsGT hr) fun ε hε ↦
        (eLpNorm_radialCubicCutoff_bounds a hε.1 hε.2 hp).1) (eventually_of_mem (Ioo_mem_nhdsGT hr)
        fun ε hε ↦ (eLpNorm_radialCubicCutoff_bounds a hε.1 hε.2 hp).2), (perimeter_ball (μ := μ) a
        hr).symm ▸ tendsto_of_tendsto_of_tendsto_of_le_of_le' (ENNReal.Tendsto.mul h1 (Or.inr
        measure_ball_lt_top.ne) hbl (Or.inr ENNReal.ofReal_ne_top)) (ENNReal.Tendsto.mul_const h2
        (Or.inr measure_ball_lt_top.ne)) (eventually_of_mem (Ioo_mem_nhdsGT hr) fun ε hε ↦
        distributionalVariation_radialCubicCutoff_ge (μ := μ) a hε.1 hε.2) (eventually_of_mem
        (Ioo_mem_nhdsGT hr) fun ε hε ↦ (distributionalVariation_mono le_top _).trans
        (distributionalVariation_radialCubicCutoff_le (μ := μ) a hε.1 hε.2))⟩
end TauCeti
