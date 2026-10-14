/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import TauCeti.Analysis.Sobolev.W1p.ChainRule
public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
public import TauCeti.MeasureTheory.Measure.PerimeterSlicing
import all TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.PerimeterSlicing

/-!
# Space of Functions of Bounded Variation, Banach Completeness, and Weak-Gradient Identity

This file develops the normed space `BV(U)` of functions of bounded variation on an open subset
`U` of a finite-dimensional real inner product space `E`, proves its Banach completeness, and
establishes the exact weak-gradient variation identity `|Du|(U) = ∫⁻ x in U, ‖g x‖ₑ`:
1. **Unbundled `MemBV` / `MemBVLoc` predicates and `eBVNorm` / `bvNorm`**: algebraic closure,
   smooth cutoffs, affine/isometric transport, dilation scaling, and indicator specialization.
2. **Weak-gradient integration by parts and exact variation identity**: `HasWeakGradientOn μ U u g`
   and `distributionalVariation μ U u = ∫⁻ x in U, ‖g x‖ₑ ∂μ`, with `C¹` and `W1p` specializations.
3. **Normed quotient `BVSpace μ U` (`BVQuotient`) and Banach completeness**: `NormedAddCommGroup`,
   `NormedSpace ℝ`, and `CompleteSpace (BVSpace μ U)`.
-/

@[expose] public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter Function MeasureTheory Metric Set TopologicalSpace TestFunction
open scoped ContDiff Convolution Distributions ENNReal Gradient InnerProductSpace NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : Measure E} {U V : Opens E}

/-! ### Section 1: Unbundled `MemBV` and `MemBVLoc` predicates and `eBVNorm` / `bvNorm` -/

/-- A function `u : E → ℝ` has **locally bounded variation** on `U : Opens E` if its variational
total variation is finite on every relatively compact open subset `V` with `closure V ⊆ U`. -/
def HasLocallyBoundedVariationOn (μ : Measure E := by volume_tac) (U : Opens E) (u : E → ℝ) :
    Prop := ∀ V : Opens E, IsCompact (closure (V : Set E)) → closure (V : Set E) ⊆ U →
      distributionalVariation μ V u < ⊤

/-- A function `u : E → ℝ` belongs to `BV(U)` (`MemBV μ U u`) if it is integrable on `U` and its
variational total variation `distributionalVariation μ U u` is finite. -/
def MemBV (μ : Measure E := by volume_tac) (U : Opens E) (u : E → ℝ) : Prop :=
  IntegrableOn u U μ ∧ distributionalVariation μ U u < ⊤
theorem memBV_iff_isBVOn {u : E → ℝ} : MemBV μ U u ↔ IsBVOn μ U u := Iff.rfl
theorem MemBV.integrableOn {u : E → ℝ} (h : MemBV μ U u) : IntegrableOn u U μ := h.1
theorem MemBV.distributionalVariation_lt_top {u : E → ℝ} (h : MemBV μ U u) :
    distributionalVariation μ U u < ⊤ := h.2
theorem MemBV.locallyIntegrableOn {u : E → ℝ} (h : MemBV μ U u) :
    LocallyIntegrableOn u U μ := h.1.locallyIntegrableOn

/-- A function `u : E → ℝ` belongs to `BV_loc(U)` (`MemBVLoc μ U u`) if it is locally integrable on
`U` and has locally bounded variation on `U`. -/
def MemBVLoc (μ : Measure E := by volume_tac) (U : Opens E) (u : E → ℝ) : Prop :=
  LocallyIntegrableOn u U μ ∧ HasLocallyBoundedVariationOn μ U u
theorem memBVLoc_iff_isLocallyBVOn {u : E → ℝ} : MemBVLoc μ U u ↔ IsLocallyBVOn μ U u := Iff.rfl
theorem MemBVLoc.locallyIntegrableOn {u : E → ℝ} (h : MemBVLoc μ U u) :
    LocallyIntegrableOn u U μ := h.1
theorem MemBVLoc.hasLocallyBoundedVariationOn {u : E → ℝ} (h : MemBVLoc μ U u) :
    HasLocallyBoundedVariationOn μ U u := h.2
theorem MemBVLoc.memBV_of_isCompact_closure {u : E → ℝ} (hu : MemBVLoc μ U u)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) : MemBV μ V u :=
  IsLocallyBVOn.isBVOn_of_isCompact_closure hu hV hVU

/-- The extended `ℝ≥0∞`-valued **BV norm** `eBVNorm μ U u = ‖u‖_{L¹(U)} + |Du|(U)`. -/
def eBVNorm (μ : Measure E := by volume_tac) (U : Opens E) (u : E → ℝ) : ℝ≥0∞ :=
  eLpNorm u 1 (μ.restrict U) + distributionalVariation μ U u

/-- The real-valued **BV norm** `bvNorm μ U u = (eBVNorm μ U u).toReal`. -/
def bvNorm (μ : Measure E := by volume_tac) (U : Opens E) (u : E → ℝ) : ℝ := (eBVNorm μ U u).toReal
theorem eLpNorm_le_eBVNorm (u : E → ℝ) : eLpNorm u 1 (μ.restrict U) ≤ eBVNorm μ U u := le_self_add
theorem distributionalVariation_le_eBVNorm (u : E → ℝ) :
    distributionalVariation μ U u ≤ eBVNorm μ U u := le_add_self
theorem memBV_iff_eBVNorm_lt_top {u : E → ℝ} (hu : AEStronglyMeasurable u (μ.restrict U)) :
    MemBV μ U u ↔ eBVNorm μ U u < ⊤ := by
  rw [MemBV, eBVNorm, ENNReal.add_lt_top, eLpNorm_one_eq_lintegral_enorm hu, IntegrableOn,
    Integrable, hasFiniteIntegral_iff_enorm, and_iff_right hu]
theorem MemBV.eBVNorm_lt_top {u : E → ℝ} (hu : MemBV μ U u) : eBVNorm μ U u < ⊤ :=
  (memBV_iff_eBVNorm_lt_top hu.1.aestronglyMeasurable).1 hu
theorem MemBV.bvNorm_eq_add {u : E → ℝ} (hu : MemBV μ U u) : bvNorm μ U u =
    (eLpNorm u 1 (μ.restrict U)).toReal + (distributionalVariation μ U u).toReal :=
  ENNReal.toReal_add (memLp_one_iff_integrable.2 hu.1).eLpNorm_lt_top.ne hu.2.ne
theorem MemBV.congr_ae {u v : E → ℝ} (hu : MemBV μ U u) (huv : u =ᵐ[μ.restrict U] v) :
    MemBV μ U v := IsBVOn.congr_ae hu huv
theorem eBVNorm_congr_ae {u v : E → ℝ} (huv : u =ᵐ[μ.restrict U] v) :
    eBVNorm μ U u = eBVNorm μ U v := by
  rw [eBVNorm, eBVNorm, eLpNorm_congr_ae huv, distributionalVariation_congr_ae huv]
theorem bvNorm_congr_ae {u v : E → ℝ} (huv : u =ᵐ[μ.restrict U] v) :
    bvNorm μ U u = bvNorm μ U v := by rw [bvNorm, bvNorm, eBVNorm_congr_ae huv]
@[simp] theorem memBV_zero : MemBV μ U 0 := ⟨integrableOn_zero, by simp⟩
@[simp] theorem memBVLoc_zero : MemBVLoc μ U 0 := ⟨locallyIntegrableOn_zero, fun _ _ _ ↦ by simp⟩
@[simp] theorem eBVNorm_zero : eBVNorm μ U 0 = 0 := by simp [eBVNorm]
@[simp] theorem bvNorm_zero : bvNorm μ U 0 = 0 := by simp [bvNorm]
theorem bvNorm_nonneg (u : E → ℝ) : 0 ≤ bvNorm μ U u := ENNReal.toReal_nonneg
theorem eBVNorm_eq_zero_iff {u : E → ℝ} : eBVNorm μ U u = 0 ↔ u =ᵐ[μ.restrict U] 0 := by
  rw [eBVNorm, add_eq_zero, eLpNorm_eq_zero_iff one_ne_zero, and_iff_left_iff_imp]
  intro h0; rw [distributionalVariation_congr_ae h0, distributionalVariation_zero]
theorem bvNorm_eq_zero_iff {u : E → ℝ} (hu : MemBV μ U u) :
    bvNorm μ U u = 0 ↔ u =ᵐ[μ.restrict U] 0 := by
  rw [bvNorm, ENNReal.toReal_eq_zero_iff, or_iff_left hu.eBVNorm_lt_top.ne, eBVNorm_eq_zero_iff]
theorem eBVNorm_mono_open (hUV : U ≤ V) (u : E → ℝ) : eBVNorm μ U u ≤ eBVNorm μ V u :=
  add_le_add (eLpNorm_mono_measure u (Measure.restrict_mono hUV le_rfl))
    (distributionalVariation_mono hUV u)
theorem MemBV.mono_open {u : E → ℝ} (hUV : U ≤ V) (hu : MemBV μ V u) : MemBV μ U u :=
  ⟨hu.1.mono_set hUV, (distributionalVariation_mono hUV u).trans_lt hu.2⟩
theorem MemBVLoc.mono_open {u : E → ℝ} (hUV : U ≤ V) (hu : MemBVLoc μ V u) : MemBVLoc μ U u :=
  ⟨hu.1.mono_set hUV, fun W hWc hWU ↦ hu.2 W hWc (hWU.trans hUV)⟩
theorem bvNorm_mono_open {u : E → ℝ} (hUV : U ≤ V) (hu : MemBV μ V u) :
    bvNorm μ U u ≤ bvNorm μ V u :=
  ENNReal.toReal_mono hu.eBVNorm_lt_top.ne (eBVNorm_mono_open hUV u)
theorem MemBV.memBVLoc {u : E → ℝ} (hu : MemBV μ U u) : MemBVLoc μ U u := IsBVOn.isLocallyBVOn hu
theorem MemBV.neg {u : E → ℝ} (hu : MemBV μ U u) : MemBV μ U (-u) := IsBVOn.neg hu
theorem MemBVLoc.neg {u : E → ℝ} (hu : MemBVLoc μ U u) : MemBVLoc μ U (-u) :=
  ⟨hu.1.neg, fun V hVc hVU ↦ by simpa using hu.2 V hVc hVU⟩
@[simp] theorem eBVNorm_neg (u : E → ℝ) : eBVNorm μ U (-u) = eBVNorm μ U u := by simp [eBVNorm]
@[simp] theorem bvNorm_neg (u : E → ℝ) : bvNorm μ U (-u) = bvNorm μ U u := by simp [bvNorm]
theorem MemBV.smul {u : E → ℝ} (hu : MemBV μ U u) (c : ℝ) : MemBV μ U (c • u) := IsBVOn.smul hu c
theorem MemBVLoc.smul {u : E → ℝ} (hu : MemBVLoc μ U u) (c : ℝ) : MemBVLoc μ U (c • u) :=
  ⟨hu.1.smul c, fun V hVc hVU ↦ (distributionalVariation_smul c u).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hu.2 V hVc hVU))⟩
theorem eBVNorm_smul (c : ℝ) (u : E → ℝ) :
    eBVNorm μ U (c • u) = ENNReal.ofReal |c| * eBVNorm μ U u := by
  rw [eBVNorm, eBVNorm, mul_add, eLpNorm_const_smul, distributionalVariation_smul,
    Real.enorm_eq_ofReal_abs]
theorem bvNorm_smul (c : ℝ) (u : E → ℝ) : bvNorm μ U (c • u) = |c| * bvNorm μ U u := by
  rw [bvNorm, eBVNorm_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg c), bvNorm]
theorem eBVNorm_add_le [FiniteDimensional ℝ E] [BorelSpace E] {u v : E → ℝ}
    (hu : LocallyIntegrableOn u U μ) (hv : LocallyIntegrableOn v U μ) :
    eBVNorm μ U (u + v) ≤ eBVNorm μ U u + eBVNorm μ U v := by
  rw [eBVNorm, eBVNorm, eBVNorm, add_add_add_comm]
  exact add_le_add (eLpNorm_add_le le_rfl) (distributionalVariation_add_le hu hv)
theorem MemBV.add [FiniteDimensional ℝ E] [BorelSpace E] {u v : E → ℝ}
    (hu : MemBV μ U u) (hv : MemBV μ U v) : MemBV μ U (u + v) := IsBVOn.add hu hv
theorem MemBVLoc.add [FiniteDimensional ℝ E] [BorelSpace E] {u v : E → ℝ}
    (hu : MemBVLoc μ U u) (hv : MemBVLoc μ U v) : MemBVLoc μ U (u + v) :=
  ⟨hu.1.add hv.1, fun _ hVc hVU ↦
    ((hu.memBV_of_isCompact_closure hVc hVU).add (hv.memBV_of_isCompact_closure hVc hVU)).2⟩
theorem bvNorm_add_le [FiniteDimensional ℝ E] [BorelSpace E] {u v : E → ℝ}
    (hu : MemBV μ U u) (hv : MemBV μ U v) :
    bvNorm μ U (u + v) ≤ bvNorm μ U u + bvNorm μ U v := by
  rw [bvNorm, bvNorm, bvNorm, ← ENNReal.toReal_add hu.eBVNorm_lt_top.ne hv.eBVNorm_lt_top.ne]
  exact ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨hu.eBVNorm_lt_top, hv.eBVNorm_lt_top⟩).ne
    (eBVNorm_add_le hu.locallyIntegrableOn hv.locallyIntegrableOn)
theorem eBVNorm_sub_le [FiniteDimensional ℝ E] [BorelSpace E] {u v : E → ℝ}
    (hu : LocallyIntegrableOn u U μ) (hv : LocallyIntegrableOn v U μ) :
    eBVNorm μ U (u - v) ≤ eBVNorm μ U u + eBVNorm μ U v := by
  rw [sub_eq_add_neg, ← eBVNorm_neg v]; exact eBVNorm_add_le hu hv.neg
theorem MemBV.sub [FiniteDimensional ℝ E] [BorelSpace E] {u v : E → ℝ}
    (hu : MemBV μ U u) (hv : MemBV μ U v) : MemBV μ U (u - v) := sub_eq_add_neg u v ▸ hu.add hv.neg
theorem MemBVLoc.sub [FiniteDimensional ℝ E] [BorelSpace E] {u v : E → ℝ}
    (hu : MemBVLoc μ U u) (hv : MemBVLoc μ U v) : MemBVLoc μ U (u - v) :=
  sub_eq_add_neg u v ▸ hu.add hv.neg
theorem bvNorm_sub_le [FiniteDimensional ℝ E] [BorelSpace E] {u v : E → ℝ}
    (hu : MemBV μ U u) (hv : MemBV μ U v) :
    bvNorm μ U (u - v) ≤ bvNorm μ U u + bvNorm μ U v := by
  rw [sub_eq_add_neg, ← bvNorm_neg v]; exact bvNorm_add_le hu hv.neg

/-! #### Smooth cutoffs, affine transport, dilation scaling, and indicators -/

theorem MemBV.mul_smooth_of_bounded [FiniteDimensional ℝ E] [BorelSpace E]
    {u η : E → ℝ} {M L : ℝ} (hu : MemBV μ U u) (hη : ContDiff ℝ (⊤ : ℕ∞ω) η)
    (hM : 0 ≤ M) (hηM : ∀ x ∈ (U : Set E), ‖η x‖ ≤ M)
    (hηL : ∀ x ∈ (U : Set E), ‖fderiv ℝ η x‖ ≤ L) : MemBV μ U (fun x ↦ η x * u x) :=
  IsBVOn.mul_smooth_of_bounded hu hη hM hηM hηL

theorem MemBVLoc.smul_testFunction [FiniteDimensional ℝ E] [BorelSpace E]
    {u : E → ℝ} (hu : MemBVLoc μ U u) (η : 𝓓(U, ℝ)) : MemBV μ U (fun x ↦ η x * u x) := by
  obtain ⟨V_set, hVo, hηV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure η.hasCompactSupport U.isOpen η.tsupport_subset
  let V : Opens E := ⟨V_set, hVo⟩; have hBV : MemBV μ V u := hu.memBV_of_isCompact_closure hVc hVU
  obtain ⟨M₀, hM₀⟩ := η.continuous.norm.bddAbove_range_of_hasCompactSupport η.hasCompactSupport.norm
  obtain ⟨L₀, hL₀⟩ := hVc.exists_bound_of_continuousOn
    (η.contDiff.continuous_fderiv (by simp)).continuousOn
  let M : ℝ := max M₀ 0 + 1; have hM_pos : 0 < M := by positivity
  have hηM : ∀ x, ‖η x‖ ≤ M := fun x ↦ (hM₀ ⟨x, rfl⟩).trans ((le_max_left M₀ 0).trans (by linarith))
  let L : ℝ := max L₀ 0; have hηL : ∀ x ∈ (V : Set E), ‖fderiv ℝ (η : E → ℝ) x‖ ≤ L := fun x hx ↦
    (hL₀ x (subset_closure hx)).trans (le_max_left L₀ 0)
  have hsupp : support (fun x ↦ η x * u x) ⊆ (V : Set E) :=
    (support_mul_subset_left _ _).trans ((subset_tsupport _).trans hηV)
  refine ⟨((integrableOn_iff_integrable_of_support_subset hsupp).1 (hBV.1.bdd_mul
    (η.continuous.continuousOn.aestronglyMeasurable V.isOpen.measurableSet)
    (Eventually.of_forall hηM))).integrableOn, ?_⟩
  refine (iSup₂_le fun φ hφ ↦ ENNReal.ofReal_le_ofReal ?_).trans_lt (ENNReal.ofReal_lt_top (r :=
    M * (distributionalVariation μ V u).toReal + L * ∫ x in (V : Set E), ‖u x‖ ∂μ))
  let ψ : 𝓓(V, E) := ⟨fun x ↦ M⁻¹ • (η x • φ x),
    (η.contDiff.smul φ.contDiff).const_smul M⁻¹, (η.hasCompactSupport.smul_right).smul_left,
    ((tsupport_smul_subset_right _ _).trans (tsupport_smul_subset_left _ _)).trans hηV⟩
  have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
    change ‖M⁻¹ • (η x • φ x)‖ ≤ 1
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hM_pos.le)]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul (hηM x) (hφ x) (norm_nonneg _) hM_pos.le)
      (inv_nonneg.2 hM_pos.le)).trans_eq (by rw [mul_one, inv_mul_cancel₀ hM_pos.ne'])
  have h_ident : ∀ x, (η x * u x) * divergence (φ : E → E) x =
      M * (u x * divergence (ψ : E → E) x) - u x * fderiv ℝ (η : E → ℝ) x (φ x) := fun x ↦ by
    rw [show divergence (ψ : E → E) x = M⁻¹ * divergence (fun y ↦ η y • φ y) x from
      divergence_const_smul M⁻¹ _ x, divergence_smul (η.contDiff.differentiable (by simp) x)
      (φ.contDiff.differentiable (by simp) x), mul_left_comm M (u x), ← mul_assoc M M⁻¹,
      mul_inv_cancel₀ hM_pos.ne', one_mul]; ring
  have h_eq_V : ∫ x in (U : Set E), (η x * u x) * divergence (φ : E → E) x ∂μ =
      ∫ x in (V : Set E), (η x * u x) * divergence (φ : E → E) x ∂μ := by
    rw [setIntegral_mul_divergence_eq_integral, ← setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hηV h))]]
  have h1 : IntegrableOn (fun x ↦ M * (u x * divergence (ψ : E → E) x)) V μ :=
    (integrableOn_mul_divergence_of_locallyIntegrableOn hBV.1.locallyIntegrableOn ψ).const_mul M
  have h_bd : ∀ x ∈ (V : Set E), ‖u x * fderiv ℝ (η : E → ℝ) x (φ x)‖ ≤ L * ‖u x‖ := fun x hx ↦ by
    rw [norm_mul, mul_comm L]
    exact mul_le_mul_of_nonneg_left (((fderiv ℝ (η : E → ℝ) x).le_opNorm (φ x)).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (hφ x)).trans (hηL x hx))) (norm_nonneg _)
  have h2 : IntegrableOn (fun x ↦ u x * fderiv ℝ (η : E → ℝ) x (φ x)) V μ :=
    (hBV.1.norm.const_mul L).mono' (hBV.1.aestronglyMeasurable.mul
      (((η.contDiff.continuous_fderiv (by simp)).clm_apply φ.continuous).aestronglyMeasurable))
      (ae_restrict_of_forall_mem V.isOpen.measurableSet h_bd)
  rw [h_eq_V, setIntegral_congr_fun V.isOpen.measurableSet (fun x _ ↦ h_ident x),
    integral_sub h1 h2, integral_const_mul]
  have ha := (ENNReal.ofReal_le_iff_le_toReal hBV.2.ne).1 (le_distributionalVariation ψ hψ_norm u)
  have h_le2 : -(∫ x in (V : Set E), u x * fderiv ℝ (η : E → ℝ) x (φ x) ∂μ) ≤
      L * ∫ x in (V : Set E), ‖u x‖ ∂μ := by
    rw [← integral_const_mul]; exact (neg_le_abs _).trans (abs_integral_le_integral_abs.trans
      (setIntegral_mono_on h2.norm (hBV.1.norm.const_mul L) V.isOpen.measurableSet h_bd))
  linarith [mul_le_mul_of_nonneg_left ha hM_pos.le]

theorem MemBV.smul_testFunction [FiniteDimensional ℝ E] [BorelSpace E]
    {u : E → ℝ} (hu : MemBV μ U u) (η : 𝓓(U, ℝ)) : MemBV μ U (fun x ↦ η x * u x) :=
  hu.memBVLoc.smul_testFunction η

private lemma eLpNorm_comp_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ₁ : Measure α} {μ₂ : Measure β} (h : α ≃ᵐ β) (hmp : MeasurePreserving h μ₁ μ₂)
    (u : β → ℝ) : eLpNorm (u ∘ h) 1 μ₁ = eLpNorm u 1 μ₂ := by
  by_cases hu : AEStronglyMeasurable u μ₂
  · exact eLpNorm_comp_measurePreserving hu hmp
  · rw [eLpNorm_of_not_aestronglyMeasurable hu, eLpNorm_of_not_aestronglyMeasurable]
    rwa [← h.measurableEmbedding.aestronglyMeasurable_map_iff, hmp.map_eq]
theorem eBVNorm_comp_add_right [BorelSpace E] [μ.IsAddRightInvariant] (U : Opens E)
    (u : E → ℝ) (a : E) :
    eBVNorm μ (U.comap ⟨(· + a), by fun_prop⟩) (fun x ↦ u (x + a)) = eBVNorm μ U u := by
  let h := (Homeomorph.addRight a).toMeasurableEquiv
  have hmp := (measurePreserving_add_right μ a).restrict_preimage_emb h.measurableEmbedding U
  rw [eBVNorm, eBVNorm, distributionalVariation_comp_add_right U u a]
  exact congrArg (· + _) (eLpNorm_comp_measurableEquiv h hmp u)
theorem MemBV.comp_add_right [BorelSpace E] [μ.IsAddRightInvariant] {u : E → ℝ}
    (hu : MemBV μ U u) (a : E) :
    MemBV μ (U.comap ⟨(· + a), by fun_prop⟩) (fun x ↦ u (x + a)) := by
  let h := (Homeomorph.addRight a).toMeasurableEquiv
  have hmp := (measurePreserving_add_right μ a).restrict_preimage_emb h.measurableEmbedding U
  exact ⟨(hmp.integrable_comp_emb h.measurableEmbedding).2 hu.1,
    (distributionalVariation_comp_add_right U u a).trans_lt hu.2⟩
theorem eBVNorm_comp_linearIsometryEquiv {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ E] [BorelSpace E] [FiniteDimensional ℝ F]
    [BorelSpace F] (L : E ≃ₗᵢ[ℝ] F) (Ω : Opens F) (u : F → ℝ) :
    eBVNorm volume (Ω.comap ⟨L, L.continuous⟩) (u ∘ L) = eBVNorm volume Ω u := by
  let h := L.toHomeomorph.toMeasurableEquiv
  have hmp := L.measurePreserving.restrict_preimage_emb h.measurableEmbedding Ω
  rw [eBVNorm, eBVNorm, distributionalVariation_comp_linearIsometryEquiv L Ω u]
  exact congrArg (· + _) (eLpNorm_comp_measurableEquiv h hmp u)
theorem MemBV.comp_linearIsometryEquiv {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ E] [BorelSpace E] [FiniteDimensional ℝ F]
    [BorelSpace F] (L : E ≃ₗᵢ[ℝ] F) {Ω : Opens F} {u : F → ℝ} (hu : MemBV volume Ω u) :
    MemBV volume (Ω.comap ⟨L, L.continuous⟩) (u ∘ L) := by
  let h := L.toHomeomorph.toMeasurableEquiv
  have hmp := L.measurePreserving.restrict_preimage_emb h.measurableEmbedding Ω
  exact ⟨(hmp.integrable_comp_emb h.measurableEmbedding).2 hu.1,
    (distributionalVariation_comp_linearIsometryEquiv L Ω u).trans_lt hu.2⟩
theorem MemBV.comp_inv_smul [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    {u : E → ℝ} (hu : MemBV μ U u) {r : ℝ} (hr : 0 < r) :
    MemBV μ (U.comap ⟨(r⁻¹ • ·), by fun_prop⟩) (fun x ↦ u (r⁻¹ • x)) := by
  let h : E ≃ᵐ E := (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne') : E ≃ₜ E).toMeasurableEquiv
  refine ⟨?_, (distributionalVariation_comp_inv_smul U u hr).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2)⟩
  change IntegrableOn (u ∘ h) (h ⁻¹' (U : Set E)) μ; rw [← integrableOn_map_equiv h]
  change IntegrableOn u (U : Set E) (Measure.map (r⁻¹ • ·) μ)
  rw [μ.map_addHaar_smul (inv_ne_zero hr.ne'), IntegrableOn, Measure.restrict_smul]
  exact hu.1.smul_measure ENNReal.ofReal_ne_top
theorem MemBV.comp_smul [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    {u : E → ℝ} (hu : MemBV μ U u) {r : ℝ} (hr : 0 < r) :
    MemBV μ (U.comap ⟨(r • ·), by fun_prop⟩) (fun x ↦ u (r • x)) := by
  simpa [inv_inv] using hu.comp_inv_smul (inv_pos.2 hr)
theorem eBVNorm_indicator_one {s : Set E} (hs : MeasurableSet s) :
    eBVNorm μ U (s.indicator fun _ ↦ (1 : ℝ)) = μ (s ∩ U) + relativePerimeter μ U s := by
  rw [eBVNorm, relativePerimeter,
    eLpNorm_indicator_const hs.nullMeasurableSet one_ne_zero ENNReal.one_ne_top,
    Measure.restrict_apply hs]; simp
theorem memBV_indicator_one_iff {s : Set E} (hs : MeasurableSet s) :
    MemBV μ U (s.indicator fun _ ↦ (1 : ℝ)) ↔ μ (s ∩ U) < ⊤ ∧ HasFinitePerimeterIn μ U s := by
  rw [memBV_iff_eBVNorm_lt_top (aestronglyMeasurable_const.indicator hs),
    eBVNorm_indicator_one hs, ENNReal.add_lt_top, HasFinitePerimeterIn,
    and_iff_right hs.nullMeasurableSet]

/-! ### Section 2: Weak-gradient integration by parts and exact variation identity -/

/-- A function `u : E → ℝ` has **weak gradient** `g : E → E` on `U : Opens E` (`HasWeakGradientOn`)
if `u` and `g` are locally integrable on `U` and satisfy the integration-by-parts identity
`∫ x, u x * divergence φ x ∂μ = -∫ x, ⟪g x, φ x⟫_ℝ ∂μ` for every test vector field `φ : 𝓓(U, E)`.
-/
def HasWeakGradientOn (μ : Measure E := by volume_tac) (U : Opens E) (u : E → ℝ) (g : E → E) :
    Prop := LocallyIntegrableOn u U μ ∧ LocallyIntegrableOn g U μ ∧
      ∀ φ : 𝓓(U, E), ∫ x, u x * divergence (φ : E → E) x ∂μ = -∫ x, ⟪g x, φ x⟫_ℝ ∂μ
theorem HasWeakGradientOn.setIntegral_mul_divergence_eq_neg {u : E → ℝ} {g : E → E}
    (h : HasWeakGradientOn μ U u g) (φ : 𝓓(U, E)) :
    ∫ x in (U : Set E), u x * divergence (φ : E → E) x ∂μ =
      -∫ x in (U : Set E), ⟪g x, φ x⟫_ℝ ∂μ := by
  rw [setIntegral_mul_divergence_eq_integral, h.2.2 φ, neg_inj]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    simp [φ.zero_on_compl hx]).symm
theorem HasWeakFDerivOn.hasWeakGradientOn [FiniteDimensional ℝ E] [BorelSpace E]
    {u : E → ℝ} {g : E → E} (hu : LocallyIntegrableOn u U μ) (hg : LocallyIntegrableOn g U μ)
    (h : HasWeakFDerivOn μ U u (fun x ↦ innerSL ℝ (g x))) : HasWeakGradientOn μ U u g := by
  refine ⟨hu, hg, fun φ ↦ ?_⟩
  rw [← setIntegral_mul_divergence_eq_integral, h.integral_mul_divergence_eq_neg φ, neg_inj]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by simp [φ.zero_on_compl hx]
theorem HasWeakGradientOn.hasWeakFDerivOn [FiniteDimensional ℝ E] {u : E → ℝ} {g : E → E}
    (h : HasWeakGradientOn μ U u g) :
    HasWeakFDerivOn μ U u (fun x ↦ innerSL ℝ (g x)) := fun v ↦ by
  refine ⟨inferInstance, h.1, ((innerSL ℝ).flip v).locallyIntegrableOn_comp h.2.1, fun ψ ↦ ?_⟩
  let φ : 𝓓(U, E) := constSmulTestFunction ψ v
  have hdiv : (fun x ↦ lineDeriv ℝ (ψ : E → ℝ) x v • u x) =
      fun x ↦ u x * divergence (φ : E → E) x := funext fun x ↦ by
    rw [smul_eq_mul, mul_comm, divergence_constSmulTestFunction, HasLineDerivAt.lineDeriv]
    exact ((ψ.contDiff.differentiable (by simp)) x).hasFDerivAt.hasLineDerivAt v
  have hinner : (fun x ↦ (ψ : E → ℝ) x • (innerSL ℝ (g x) v)) = fun x ↦ ⟪g x, φ x⟫_ℝ :=
    funext fun x ↦ by simp [φ, constSmulTestFunction, inner_smul_right, mul_comm]
  simp_rw [hdiv, hinner, h.2.2 φ]
theorem HasWeakGradientOn.of_contDiffOn [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    {u : E → ℝ} (hu : ContDiffOn ℝ 1 u U) : HasWeakGradientOn μ U u (∇ u) :=
  (hasWeakFDerivOn_gradient_of_contDiffOn hu).hasWeakGradientOn
    (hu.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
    (((InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
      (hu.continuousOn_fderiv_of_isOpen U.isOpen le_rfl)).locallyIntegrableOn
      U.isOpen.measurableSet)
theorem HasWeakGradientOn.of_contDiff [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) : HasWeakGradientOn μ U u (∇ u) :=
  HasWeakGradientOn.of_contDiffOn hu.contDiffOn
theorem HasWeakGradientOn.distributionalVariation_le_lintegral_enorm
    [FiniteDimensional ℝ E] [BorelSpace E] {u : E → ℝ} {g : E → E}
    (h : HasWeakGradientOn μ U u g) :
    distributionalVariation μ U u ≤ ∫⁻ x in (U : Set E), ‖g x‖ₑ ∂μ :=
  h.hasWeakFDerivOn.distributionalVariation_le_lintegral_enorm.trans_eq
    (lintegral_congr fun x ↦ by rw [← ofReal_norm, ← ofReal_norm, innerSL_apply_norm])
theorem HasWeakGradientOn.memBV [FiniteDimensional ℝ E] [BorelSpace E]
    {u : E → ℝ} {g : E → E} (h : HasWeakGradientOn μ U u g)
    (hu : IntegrableOn u U μ) (hg : IntegrableOn g U μ) : MemBV μ U u :=
  ⟨hu, h.distributionalVariation_le_lintegral_enorm.trans_lt hg.2⟩
alias MemBV.of_hasWeakGradientOn := HasWeakGradientOn.memBV
omit [MeasurableSpace E] [InnerProductSpace ℝ E] in
private lemma norm_sub_eps_le_norm_sq_div_sqrt (v : E) {ε : ℝ} (hε : 0 < ε) :
    ‖v‖ - ε ≤ ‖v‖ ^ 2 / Real.sqrt (‖v‖ ^ 2 + ε ^ 2) := by
  have hpos : 0 < Real.sqrt (‖v‖ ^ 2 + ε ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [le_div_iff₀ hpos]; rcases le_or_gt (‖v‖ - ε) 0 with hle | hgt
  · exact (mul_nonpos_of_nonpos_of_nonneg hle hpos.le).trans (sq_nonneg ‖v‖)
  · have hsqrt : Real.sqrt (‖v‖ ^ 2 + ε ^ 2) ≤ ‖v‖ + ε := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ ‖v‖ + ε)]
      exact Real.sqrt_le_sqrt (by linarith [add_sq ‖v‖ ε, mul_nonneg (norm_nonneg v) hε.le])
    exact (mul_le_mul_of_nonneg_left hsqrt hgt.le).trans (by linarith [sq_nonneg ε])
private lemma setIntegral_norm_sub_le_distributionalVariation_of_contDiff
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    {u : E → ℝ} {g : E → E} (h : HasWeakGradientOn μ U u g)
    {K : Set E} (hK : IsCompact K) {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (hχK : ∀ x ∈ K, χ x = 1)
    (hχ_cpt : HasCompactSupport χ) (hχ_ts : tsupport χ ⊆ (U : Set E))
    {w : E → E} (hw : ContDiff ℝ ∞ w) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ((∫ x in K, ‖w x‖ ∂μ) - ε * μ.real K - ∫ x in tsupport χ, ‖w x - g x‖ ∂μ) ≤
      distributionalVariation μ U u := by
  let d : E → ℝ := fun x ↦ Real.sqrt (⟪w x, w x⟫_ℝ + ε ^ 2)
  have hd_eq : ∀ x, d x = Real.sqrt (‖w x‖ ^ 2 + ε ^ 2) := fun x ↦ by simp [d]
  have hd_pos : ∀ x, 0 < d x := fun x ↦ (hd_eq x).symm ▸ Real.sqrt_pos.2 (by positivity)
  have hd_smooth : ContDiff ℝ ∞ d :=
    ((hw.inner ℝ hw).add contDiff_const).sqrt fun x ↦ by rw [real_inner_self_eq_norm_sq]; positivity
  let φ_fun : E → E := -((χ * d⁻¹) • w); have hφ_supp : support φ_fun ⊆ support χ := fun x hx ↦
    mt (fun hχx : χ x = 0 ↦ by simp [φ_fun, hχx]) hx
  have hφ_ts : tsupport φ_fun ⊆ tsupport χ := closure_mono hφ_supp
  let φ : 𝓓(U, E) := ⟨φ_fun, ((hχ.mul (hd_smooth.inv fun x ↦ (hd_pos x).ne')).smul hw).neg,
    hχ_cpt.mono hφ_supp, hφ_ts.trans hχ_ts⟩
  have hφ_coe : ∀ x, (φ : E → E) x = -((χ x * (d x)⁻¹) • w x) := fun _ ↦ rfl
  have hφ_norm : ∀ x, ‖φ x‖ ≤ 1 := fun x ↦ by
    rw [hφ_coe x, norm_neg, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ0 x),
      abs_of_pos (inv_pos.2 (hd_pos x))]
    have hle : ‖w x‖ ≤ d x := Real.sqrt_sq (norm_nonneg (w x)) ▸ (hd_eq x).symm ▸
      Real.sqrt_le_sqrt (by linarith [sq_nonneg ε])
    exact (mul_le_mul (mul_le_mul_of_nonneg_right (hχ1 x) (inv_nonneg.2 (hd_pos x).le))
      hle (norm_nonneg _) (by positivity)).trans_eq (by simp [(hd_pos x).ne'])
  refine (ENNReal.ofReal_le_ofReal ?_).trans (le_distributionalVariation φ hφ_norm u)
  rw [setIntegral_mul_divergence_eq_integral, h.2.2 φ]
  have h_w_nonneg : ∀ x, 0 ≤ -⟪w x, φ x⟫_ℝ := fun x ↦ by
    rw [hφ_coe x, inner_neg_right, neg_neg, inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_nonneg (mul_nonneg (hχ0 x) (inv_nonneg.2 (hd_pos x).le)) (sq_nonneg _)
  have h_w_K : ∀ x ∈ K, ‖w x‖ - ε ≤ -⟪w x, φ x⟫_ℝ := fun x hx ↦ by
    rw [hφ_coe x, inner_neg_right, neg_neg, inner_smul_right, real_inner_self_eq_norm_sq,
      hχK x hx, one_mul, hd_eq, inv_mul_eq_div]
    exact norm_sub_eps_le_norm_sq_div_sqrt (w x) hε
  have hφ_int : Integrable (fun x ↦ -⟪w x, φ x⟫_ℝ) μ :=
    (hw.continuous.inner φ.continuous).neg.integrable_of_hasCompactSupport
      (φ.hasCompactSupport.mono fun x hx ↦ mt (fun h0 : (φ : E → E) x = 0 ↦ by simp [h0]) hx)
  have hK_int : IntegrableOn (fun x ↦ ‖w x‖) K μ :=
    hw.continuous.norm.continuousOn.integrableOn_compact hK
  have hε_int : IntegrableOn (fun _ : E ↦ ε) K μ := integrableOn_const hK.measure_lt_top.ne
  have h_int_w : (∫ x in K, ‖w x‖ ∂μ) - ε * μ.real K ≤ ∫ x, -⟪w x, φ x⟫_ℝ ∂μ := by
    calc (∫ x in K, ‖w x‖ ∂μ) - ε * μ.real K = ∫ x in K, (‖w x‖ - ε) ∂μ := by
          rw [integral_sub hK_int hε_int, setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in K, -⟪w x, φ x⟫_ℝ ∂μ :=
          setIntegral_mono_on (hK_int.sub hε_int) hφ_int.integrableOn hK.measurableSet h_w_K
      _ ≤ ∫ x, -⟪w x, φ x⟫_ℝ ∂μ := setIntegral_le_integral hφ_int (Eventually.of_forall h_w_nonneg)
  have hgL : IntegrableOn g (tsupport χ) μ :=
    (locallyIntegrableOn_iff U.isOpen.isLocallyClosed).1 h.2.1 (tsupport χ) hχ_ts hχ_cpt
  have hwL : IntegrableOn w (tsupport χ) μ := hw.continuous.continuousOn.integrableOn_compact hχ_cpt
  have h_compl : ∀ (v : E → E) (x : E), x ∉ tsupport χ → ⟪v x, φ x⟫_ℝ = 0 := fun v x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport (f := (φ : E → E)) (fun h ↦ hx (hφ_ts h)),
      inner_zero_right]
  have hint_inner : ∀ {v : E → E}, IntegrableOn v (tsupport χ) μ →
      IntegrableOn (fun x ↦ ⟪v x, φ x⟫_ℝ) (tsupport χ) μ := fun hv ↦
    (hv.norm.const_mul 1).mono' (hv.aestronglyMeasurable.inner φ.continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, one_mul]; exact (abs_real_inner_le_norm _ _).trans
          (mul_le_of_le_one_right (norm_nonneg _) (hφ_norm x)))
  have h_diff : ∫ x, -⟪w x, φ x⟫_ℝ ∂μ - (-∫ x, ⟪g x, φ x⟫_ℝ ∂μ) ≤
      ∫ x in tsupport χ, ‖w x - g x‖ ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by simp [h_compl w x hx]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (h_compl g), sub_neg_eq_add,
      ← integral_add hφ_int.integrableOn (hint_inner hgL),
      setIntegral_congr_fun hχ_cpt.measurableSet (fun x _ ↦ by rw [inner_sub_left]; ring :
        ∀ x ∈ tsupport χ, -⟪w x, φ x⟫_ℝ + ⟪g x, φ x⟫_ℝ = ⟪g x - w x, φ x⟫_ℝ)]
    exact setIntegral_mono_on (hint_inner (hgL.sub hwL)) (hwL.sub hgL).norm hχ_cpt.measurableSet
      fun x _ ↦ (real_inner_le_norm _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) (hφ_norm x)).trans_eq (norm_sub_rev _ _))
  linarith
private lemma tendsto_setIntegral_norm_convolution_normed_sub {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ E]
    [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → F} {K W : Set E}
    (huW : IntegrableOn u W μ) (hK : IsCompact K) (hW : IsCompact W) (hKW : K ⊆ W)
    {ρ : ℕ → ContDiffBump (0 : E)} (hρ : Tendsto (fun n ↦ (ρ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x in K, ‖((ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] W.indicator u) x - u x‖ ∂μ)
      atTop (𝓝 0) := by
  let u_n : ℕ → E → F := fun n ↦ (ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] W.indicator u
  have hu_ind : Integrable (W.indicator u) μ := huW.integrable_indicator hW.measurableSet
  have he := tendsto_eLpNorm_normed_convolution_sub ENNReal.one_ne_top hρ
    (memLp_one_iff_integrable.2 hu_ind)
  have h_le : ∀ n, ENNReal.ofReal (∫ x in K, ‖u_n n x - u x‖ ∂μ) ≤
      eLpNorm (u_n n - W.indicator u) 1 μ := fun n ↦ by
    have hsm : ContDiff ℝ ∞ (u_n n) := HasCompactSupport.contDiff_convolution_left (lsmul ℝ ℝ)
      (ρ n).hasCompactSupport_normed (ρ n).contDiff_normed hu_ind.locallyIntegrable
    have hint : IntegrableOn (u_n n - u) K μ :=
      (hsm.continuous.continuousOn.integrableOn_compact hK).sub (huW.mono_set hKW)
    have hae : u_n n - u =ᵐ[μ.restrict K] u_n n - W.indicator u :=
      (ae_restrict_mem hK.measurableSet).mono fun x hx ↦ by
        simp [Pi.sub_apply, indicator_of_mem (hKW hx)]
    change ENNReal.ofReal (∫ x in K, ‖(u_n n - u) x‖ ∂μ) ≤ _
    rw [ofReal_integral_norm_eq_lintegral_enorm hint,
      ← eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable, eLpNorm_congr_ae hae]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have h_toReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun _ ↦ zero_le) h_le)
  rw [ENNReal.toReal_zero] at h_toReal
  exact h_toReal.congr fun n ↦ ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)

/-- **Exact weak-gradient variation identity**: if `u` has weak gradient `g` on `U`, then
`distributionalVariation μ U u = ∫⁻ x in (U : Set E), ‖g x‖ₑ ∂μ`. -/
theorem HasWeakGradientOn.distributionalVariation_eq_lintegral_enorm
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → ℝ} {g : E → E}
    (h : HasWeakGradientOn μ U u g) :
    distributionalVariation μ U u = ∫⁻ x in (U : Set E), ‖g x‖ₑ ∂μ := by
  refine le_antisymm h.distributionalVariation_le_lintegral_enorm ?_
  have hK_le : ∀ K : Set E, IsCompact K → K ⊆ (U : Set E) →
      ∫⁻ x in K, ‖g x‖ₑ ∂μ ≤ distributionalVariation μ U u := fun K hK hKU ↦ by
    obtain ⟨χ, hχ, hχ_range, hχK_int, hχ_cpt, hχ_ts⟩ := hK.exists_contDiff_cutoff U.isOpen hKU
    have hχ0 : ∀ x, 0 ≤ χ x := fun x ↦ (hχ_range (mem_range_self x)).1
    have hχ1 : ∀ x, χ x ≤ 1 := fun x ↦ (hχ_range (mem_range_self x)).2
    have hχK : ∀ x ∈ K, χ x = 1 := fun x hx ↦
      mem_singleton_iff.1 (interior_subset (s := χ ⁻¹' {1}) (hχK_int hx))
    let L := tsupport χ; have hKL : K ⊆ L := fun x hx ↦
      subset_tsupport χ (by rw [mem_support, hχK x hx]; exact one_ne_zero)
    have hgL : IntegrableOn g L μ :=
      (locallyIntegrableOn_iff U.isOpen.isLocallyClosed).1 h.2.1 L hχ_ts hχ_cpt
    have hgK : IntegrableOn g K μ := hgL.mono_set hKL; let ρ : ℕ → ContDiffBump (0 : E) := fun n ↦
      ⟨((n : ℝ) + 2)⁻¹, ((n : ℝ) + 1)⁻¹, by positivity,
        inv_strictAnti₀ (by positivity) (by linarith)⟩
    have hρ_tendsto : Tendsto (fun n ↦ (ρ n).rOut) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    let w : ℕ → E → E := fun n ↦ (ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] L.indicator g
    have hw_smooth : ∀ n, ContDiff ℝ ∞ (w n) := fun n ↦
      HasCompactSupport.contDiff_convolution_left (lsmul ℝ ℝ)
        (ρ n).hasCompactSupport_normed (ρ n).contDiff_normed
        (hgL.integrable_indicator hχ_cpt.measurableSet).locallyIntegrable
    have hL_tendsto :=
      tendsto_setIntegral_norm_convolution_normed_sub hgL hχ_cpt hχ_cpt Subset.rfl hρ_tendsto
    have hK_tendsto : Tendsto (fun n ↦ ∫ x in K, ‖w n x‖ ∂μ) atTop (𝓝 (∫ x in K, ‖g x‖ ∂μ)) := by
      rw [Metric.tendsto_nhds]; intro δ hδ
      filter_upwards [hL_tendsto.eventually (Metric.ball_mem_nhds 0 hδ)] with n hn
      rw [Real.dist_0_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)] at hn
      have hwL : IntegrableOn (w n) L μ :=
        (hw_smooth n).continuous.continuousOn.integrableOn_compact hχ_cpt
      have hwK : IntegrableOn (fun x ↦ ‖w n x‖) K μ := (hwL.mono_set hKL).norm
      rw [Real.dist_eq, ← integral_sub hwK hgK.norm]; exact (abs_integral_le_integral_abs.trans
        (setIntegral_mono_on (hwK.sub hgK.norm).abs ((hwL.mono_set hKL).sub hgK).norm
          hK.measurableSet fun x _ ↦ abs_norm_sub_norm_le _ _)).trans_lt
        ((setIntegral_mono_set (hwL.sub hgL).norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
          hKL.eventuallyLE).trans_lt hn)
    have h_comb : Tendsto (fun n : ℕ ↦ (∫ x in K, ‖w n x‖ ∂μ) - ((n : ℝ) + 1)⁻¹ * μ.real K -
          ∫ x in L, ‖w n x - g x‖ ∂μ) atTop (𝓝 (∫ x in K, ‖g x‖ ∂μ)) := by
      simpa using (hK_tendsto.sub (hρ_tendsto.mul_const (μ.real K))).sub hL_tendsto
    rw [← ofReal_integral_norm_eq_lintegral_enorm hgK]
    exact le_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp h_comb) fun n ↦
      setIntegral_norm_sub_le_distributionalVariation_of_contDiff h hK hχ hχ0 hχ1 hχK hχ_cpt
        hχ_ts (hw_smooth n) (by positivity)
  have : LocallyCompactSpace U := IsOpen.locallyCompactSpace U.isOpen
  let K : CompactExhaustion U := CompactExhaustion.choice U
  let S : ℕ → Set E := fun n ↦ (Subtype.val : U → E) '' K n
  have hS_cpt : ∀ n, IsCompact (S n) := fun n ↦ (K.isCompact n).image continuous_subtype_val
  have hS_sub : ∀ n, S n ⊆ (U : Set E) := fun n ↦ by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hS_union : ⋃ n, S n = (U : Set E) := by
    rw [← image_iUnion, K.iUnion_eq, image_univ, Subtype.range_coe]
  rw [← hS_union, ← lintegral_indicator (MeasurableSet.iUnion fun n ↦ (hS_cpt n).measurableSet)]
  have hind : (⋃ n, S n).indicator (fun x ↦ ‖g x‖ₑ) =
      fun x ↦ ⨆ n, (S n).indicator (fun y ↦ ‖g y‖ₑ) x := funext fun x ↦ by
    by_cases hx : x ∈ ⋃ n, S n
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hx; rw [indicator_of_mem hx]
      exact le_antisymm (le_iSup_of_le m (by simp [hm])) (iSup_le fun n ↦ indicator_le_self _ _ x)
    · rw [indicator_of_notMem hx, eq_comm, ENNReal.iSup_eq_zero]
      exact fun n ↦ indicator_of_notMem (fun hn ↦ hx (mem_iUnion.2 ⟨n, hn⟩)) _
  rw [hind, lintegral_iSup' (fun n ↦ (aemeasurable_indicator_iff (hS_cpt n).measurableSet).2
      ((h.2.1.mono_set (hS_sub n)).aestronglyMeasurable.enorm))
    (Eventually.of_forall fun x m n hmn ↦ indicator_le_indicator_of_subset
      (image_mono (K.subset hmn)) (fun _ ↦ zero_le) x)]
  exact iSup_le fun n ↦ (lintegral_indicator (hS_cpt n).measurableSet _).trans_le
    (hK_le (S n) (hS_cpt n) (hS_sub n))

theorem distributionalVariation_eq_lintegral_enorm_gradient
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → ℝ}
    (hu : ContDiffOn ℝ 1 u U) :
    distributionalVariation μ U u = ∫⁻ x in (U : Set E), ‖∇ u x‖ₑ ∂μ :=
  (HasWeakGradientOn.of_contDiffOn hu).distributionalVariation_eq_lintegral_enorm
theorem distributionalVariation_eq_lintegral_enorm_gradient_of_contDiff
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {u : E → ℝ}
    (hu : ContDiff ℝ 1 u) :
    distributionalVariation μ U u = ∫⁻ x in (U : Set E), ‖∇ u x‖ₑ ∂μ :=
  distributionalVariation_eq_lintegral_enorm_gradient hu.contDiffOn
theorem W1p.hasWeakGradientOn [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : W1p μ U p) :
    HasWeakGradientOn μ U (W1p.value u) (W1p.gradient u) :=
  (W1p.hasWeakFDerivOn u).hasWeakGradientOn
    (W1p.hasWeakFDerivOn u).locallyIntegrableOn (W1p.locallyIntegrableOn_gradient u)
theorem W1p.distributionalVariation_eq_lintegral_enorm_gradient
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : W1p μ U p) :
    distributionalVariation μ U (W1p.value u) = ∫⁻ x in (U : Set E), ‖W1p.gradient u x‖ₑ ∂μ :=
  (W1p.hasWeakGradientOn u).distributionalVariation_eq_lintegral_enorm
theorem W1p.memBV [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    (u : W1p μ U 1) : MemBV μ U (W1p.value u) :=
  (W1p.hasWeakGradientOn u).memBV
    (memLp_one_iff_integrable.1 (Lp.memLp (W1p.value u)))
    (memLp_one_iff_integrable.1 (Lp.memLp (W1p.gradient u)))
theorem W1p.eBVNorm_value_eq [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    (u : W1p μ U 1) : eBVNorm μ U (W1p.value u) =
      eLpNorm (W1p.value u) 1 (μ.restrict U) + eLpNorm (W1p.gradient u) 1 (μ.restrict U) := by
  rw [eBVNorm, W1p.distributionalVariation_eq_lintegral_enorm_gradient,
    eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable (W1p.gradient u))]

/-! ### Section 3: Normed quotient `BVSpace μ U` (`BVQuotient`) and Banach completeness -/

/-- The **BV space** `BVSpace μ U` of a.e. equivalence classes of `L¹(U)` functions whose
variational total variation on `U` is finite. -/
def BVSpace (μ : Measure E := by volume_tac) (U : Opens E) : Type _ :=
  {f : Lp ℝ 1 (μ.restrict U) // distributionalVariation μ U f < ⊤}

/-- Alias for `BVSpace` emphasizing the a.e.-quotient construction over `Lp ℝ 1 (μ.restrict U)`. -/
abbrev BVQuotient (μ : Measure E := by volume_tac) (U : Opens E) := BVSpace μ U

namespace BVSpace

/-- Coercion from `BVSpace μ U` to the underlying `Lp ℝ 1 (μ.restrict U)` element. -/
@[coe] def toLp (f : BVSpace μ U) : Lp ℝ 1 (μ.restrict U) := f.1
instance : CoeOut (BVSpace μ U) (Lp ℝ 1 (μ.restrict U)) := ⟨toLp⟩
instance : CoeFun (BVSpace μ U) (fun _ ↦ E → ℝ) := ⟨fun f ↦ (f.toLp : E → ℝ)⟩
theorem toLp_injective : Function.Injective (toLp (μ := μ) (U := U)) := Subtype.val_injective
@[ext] theorem ext {f g : BVSpace μ U} (h : (f : Lp ℝ 1 (μ.restrict U)) = g) : f = g :=
  toLp_injective h
theorem memBV_coe (f : BVSpace μ U) : MemBV μ U f :=
  ⟨memLp_one_iff_integrable.1 (Lp.memLp f.toLp), f.2⟩
theorem eBVNorm_coe_lt_top (f : BVSpace μ U) : eBVNorm μ U f < ⊤ := (memBV_coe f).eBVNorm_lt_top
instance : Zero (BVSpace μ U) :=
  ⟨⟨0, by rw [distributionalVariation_congr_ae (Lp.coeFn_zero ℝ 1 (μ.restrict U))]; simp⟩⟩
instance : Neg (BVSpace μ U) :=
  ⟨fun f ↦ ⟨-f.1, (distributionalVariation_congr_ae (Lp.coeFn_neg f.1)).trans_lt
    ((distributionalVariation_neg _).trans_lt f.2)⟩⟩
instance [FiniteDimensional ℝ E] [BorelSpace E] : Add (BVSpace μ U) :=
  ⟨fun f g ↦ ⟨f.1 + g.1, (distributionalVariation_congr_ae (Lp.coeFn_add f.1 g.1)).trans_lt
    ((memBV_coe f).add (memBV_coe g)).2⟩⟩
instance [FiniteDimensional ℝ E] [BorelSpace E] : Sub (BVSpace μ U) :=
  ⟨fun f g ↦ ⟨f.1 - g.1, (distributionalVariation_congr_ae (Lp.coeFn_sub f.1 g.1)).trans_lt
    ((memBV_coe f).sub (memBV_coe g)).2⟩⟩
instance : SMul ℝ (BVSpace μ U) :=
  ⟨fun c f ↦ ⟨c • f.1, (distributionalVariation_congr_ae (Lp.coeFn_smul c f.1)).trans_lt
    ((memBV_coe f).smul c).2⟩⟩
instance : SMul ℕ (BVSpace μ U) := ⟨fun n f ↦ ⟨n • f.1, by
    rw [← Nat.cast_smul_eq_nsmul ℝ n f.1,
      distributionalVariation_congr_ae (Lp.coeFn_smul (n : ℝ) f.1)]
    exact ((memBV_coe f).smul (n : ℝ)).2⟩⟩
instance : SMul ℤ (BVSpace μ U) := ⟨fun n f ↦ ⟨n • f.1, by
    rw [← Int.cast_smul_eq_zsmul ℝ n f.1,
      distributionalVariation_congr_ae (Lp.coeFn_smul (n : ℝ) f.1)]
    exact ((memBV_coe f).smul (n : ℝ)).2⟩⟩
@[simp, norm_cast] theorem coe_zero : ((0 : BVSpace μ U) : Lp ℝ 1 (μ.restrict U)) = 0 := rfl
@[simp, norm_cast] theorem coe_neg (f : BVSpace μ U) :
    ((-f : BVSpace μ U) : Lp ℝ 1 (μ.restrict U)) = -f := rfl
@[simp, norm_cast] theorem coe_add [FiniteDimensional ℝ E] [BorelSpace E] (f g : BVSpace μ U) :
    ((f + g : BVSpace μ U) : Lp ℝ 1 (μ.restrict U)) = f + g := rfl
@[simp, norm_cast] theorem coe_sub [FiniteDimensional ℝ E] [BorelSpace E] (f g : BVSpace μ U) :
    ((f - g : BVSpace μ U) : Lp ℝ 1 (μ.restrict U)) = f - g := rfl
@[simp, norm_cast] theorem coe_smul (c : ℝ) (f : BVSpace μ U) :
    ((c • f : BVSpace μ U) : Lp ℝ 1 (μ.restrict U)) = c • f := rfl
instance [FiniteDimensional ℝ E] [BorelSpace E] : AddCommGroup (BVSpace μ U) :=
  toLp_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
instance [FiniteDimensional ℝ E] [BorelSpace E] : Module ℝ (BVSpace μ U) :=
  toLp_injective.module ℝ ⟨⟨toLp, rfl⟩, fun _ _ ↦ rfl⟩ (fun _ _ ↦ rfl)
instance : Norm (BVSpace μ U) :=
  ⟨fun f ↦ ‖(f : Lp ℝ 1 (μ.restrict U))‖ + (distributionalVariation μ U f).toReal⟩
instance [FiniteDimensional ℝ E] [BorelSpace E] : Dist (BVSpace μ U) := ⟨fun f g ↦ ‖f - g‖⟩
theorem norm_def (f : BVSpace μ U) :
    ‖f‖ = ‖(f : Lp ℝ 1 (μ.restrict U))‖ + (distributionalVariation μ U f).toReal := rfl
theorem norm_eq_bvNorm (f : BVSpace μ U) : ‖f‖ = bvNorm μ U f := by
  rw [norm_def, (memBV_coe f).bvNorm_eq_add, Lp.norm_def]
theorem norm_coe_le_norm (f : BVSpace μ U) : ‖(f : Lp ℝ 1 (μ.restrict U))‖ ≤ ‖f‖ :=
  le_add_of_nonneg_right ENNReal.toReal_nonneg
instance [FiniteDimensional ℝ E] [BorelSpace E] : NormedAddCommGroup (BVSpace μ U) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := norm
      map_zero' := (norm_eq_bvNorm 0).trans
        ((bvNorm_congr_ae (Lp.coeFn_zero ℝ 1 (μ.restrict U))).trans bvNorm_zero)
      neg' := fun f ↦ by
        rw [norm_eq_bvNorm, norm_eq_bvNorm]
        exact (bvNorm_congr_ae (Lp.coeFn_neg f.toLp)).trans (bvNorm_neg _)
      add_le' := fun f g ↦ by
        rw [norm_eq_bvNorm, norm_eq_bvNorm, norm_eq_bvNorm]
        exact (bvNorm_congr_ae (Lp.coeFn_add f.toLp g.toLp)).trans_le
          (bvNorm_add_le (memBV_coe f) (memBV_coe g))
      eq_zero_of_map_eq_zero' := fun f hf ↦ ext <| Lp.ext <|
        ((bvNorm_eq_zero_iff (memBV_coe f)).1 ((norm_eq_bvNorm f).symm.trans hf)).trans
          (Lp.coeFn_zero ℝ 1 (μ.restrict U)).symm }
instance [FiniteDimensional ℝ E] [BorelSpace E] : NormedSpace ℝ (BVSpace μ U) where
  norm_smul_le c f := by
    rw [norm_eq_bvNorm, norm_eq_bvNorm, Real.norm_eq_abs]
    exact ((bvNorm_congr_ae (Lp.coeFn_smul c f.toLp)).trans (bvNorm_smul c f)).le

end BVSpace

/-- Construct an element of `BVSpace μ U` from an unbundled `MemBV μ U u` function. -/
def MemBV.toBVSpace {u : E → ℝ} (hu : MemBV μ U u) : BVSpace μ U :=
  ⟨(memLp_one_iff_integrable.2 hu.1).toLp u,
    (distributionalVariation_congr_ae (MemLp.coeFn_toLp _)).trans_lt hu.2⟩
@[simp] theorem MemBV.coeFn_toBVSpace {u : E → ℝ} (hu : MemBV μ U u) :
    (hu.toBVSpace : E → ℝ) =ᵐ[μ.restrict U] u :=
  MemLp.coeFn_toLp (memLp_one_iff_integrable.2 hu.1)
@[simp] theorem MemBV.norm_toBVSpace {u : E → ℝ} (hu : MemBV μ U u) :
    ‖hu.toBVSpace‖ = bvNorm μ U u := by
  rw [BVSpace.norm_eq_bvNorm, bvNorm_congr_ae hu.coeFn_toBVSpace]

private lemma distributionalVariation_sub_le_liminf_of_tendsto_eLpNorm
    [FiniteDimensional ℝ E] [BorelSpace E] {u : ℕ → E → ℝ} {u_lim : E → ℝ}
    (hu : ∀ n, IntegrableOn (u n) U μ) (hlim : IntegrableOn u_lim U μ)
    (hL1 : Tendsto (fun n ↦ eLpNorm (u n - u_lim) 1 (μ.restrict U)) atTop (𝓝 0)) (m : ℕ) :
    distributionalVariation μ U (u m - u_lim) ≤
      liminf (fun n ↦ distributionalVariation μ U (u m - u n)) atTop := by
  refine distributionalVariation_le_liminf fun φ ↦ ?_
  obtain ⟨M, hM⟩ := (continuous_divergence_testFunction φ).norm.bddAbove_range_of_hasCompactSupport
    (hasCompactSupport_divergence_testFunction φ).norm
  have h_toReal : Tendsto
      (fun n ↦ max M 0 * (eLpNorm (u n - u_lim) 1 (μ.restrict U)).toReal) atTop (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1).const_mul (max M 0)
  rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero_norm'
    (a := fun n ↦ max M 0 * (eLpNorm (u n - u_lim) 1 (μ.restrict U)).toReal)
    (Eventually.of_forall fun n ↦ ?_) h_toReal
  rw [norm_norm, ← integral_sub
    (integrableOn_mul_divergence_of_locallyIntegrableOn ((hu m).sub (hu n)).locallyIntegrableOn φ)
    (integrableOn_mul_divergence_of_locallyIntegrableOn ((hu m).sub hlim).locallyIntegrableOn φ)]
  have hsub : (fun x ↦ (u m - u n) x * divergence (φ : E → E) x -
      (u m - u_lim) x * divergence (φ : E → E) x) =
      fun x ↦ (u_lim x - u n x) * divergence (φ : E → E) x :=
    funext fun x ↦ by simp only [Pi.sub_apply]; ring
  have hint_diff : IntegrableOn (u n - u_lim) U μ := (hu n).sub hlim
  have h_eq_norm : (eLpNorm (u n - u_lim) 1 (μ.restrict U)).toReal =
      ∫ x in (U : Set E), ‖(u n - u_lim) x‖ ∂μ := by
    rw [eLpNorm_one_eq_lintegral_enorm hint_diff.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hint_diff,
      ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]
  rw [hsub, h_eq_norm, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ ↦ norm_nonneg _) (hint_diff.norm.const_mul (max M 0))
    (Eventually.of_forall fun x ↦ ?_))
  dsimp only [Pi.sub_apply]; rw [norm_mul, norm_sub_rev, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hM ⟨x, rfl⟩).trans (le_max_left M 0)) (norm_nonneg _)

/-- **Banach completeness of `MemBV` under `eBVNorm`**: every `eBVNorm`-Cauchy sequence in
`MemBV μ U` converges in `eBVNorm μ U` to a limit in `MemBV μ U`. -/
theorem exists_memBV_tendsto_eBVNorm_of_cauchy [FiniteDimensional ℝ E] [BorelSpace E]
    {u : ℕ → E → ℝ} (hu : ∀ n, MemBV μ U (u n))
    (hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, eBVNorm μ U (u m - u n) < ε) :
    ∃ u_lim : E → ℝ, MemBV μ U u_lim ∧ Tendsto (fun n ↦ eBVNorm μ U (u n - u_lim)) atTop (𝓝 0) := by
  let f : ℕ → Lp ℝ 1 (μ.restrict U) := fun n ↦ (hu n).toBVSpace
  have hf_ae : ∀ n, (f n : E → ℝ) =ᵐ[μ.restrict U] u n := fun n ↦ (hu n).coeFn_toBVSpace
  have hf_cauchy : CauchySeq f := by
    rw [Metric.cauchySeq_iff]; intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩; rw [dist_eq_norm, Lp.norm_def,
      eLpNorm_congr_ae ((Lp.coeFn_sub (f m) (f n)).trans ((hf_ae m).sub (hf_ae n)))]
    have hlt := (eLpNorm_le_eBVNorm (u m - u n)).trans_lt (hN m hm n hn)
    simpa [ENNReal.toReal_ofReal hε.le] using
      (ENNReal.toReal_lt_toReal hlt.ne_top ENNReal.ofReal_ne_top).2 hlt
  obtain ⟨f_lim, hf_lim⟩ := cauchySeq_tendsto_of_complete hf_cauchy; let u_lim : E → ℝ := f_lim
  have hlim_int : IntegrableOn u_lim U μ := memLp_one_iff_integrable.1 (Lp.memLp f_lim)
  have hL1 : Tendsto (fun n ↦ eLpNorm (u n - u_lim) 1 (μ.restrict U)) atTop (𝓝 0) := by
    have h_ofReal := (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_iff_norm_sub_tendsto_zero.1 hf_lim)
    rw [ENNReal.ofReal_zero] at h_ofReal; refine h_ofReal.congr fun n ↦ ?_
    dsimp only [Function.comp_apply]
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
    exact eLpNorm_congr_ae ((Lp.coeFn_sub (f n) f_lim).trans ((hf_ae n).sub EventuallyEq.rfl))
  have h_tendsto : Tendsto (fun m ↦ eBVNorm μ U (u m - u_lim)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]; intro ε hε; rcases eq_or_ne ε ⊤ with rfl | hε_top
    · exact ⟨0, fun _ _ ↦ le_top⟩
    · have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top
      obtain ⟨N, hN⟩ := hcauchy (ε / 2) hε2
      obtain ⟨M, hM⟩ := (ENNReal.tendsto_atTop_zero.1 hL1) (ε / 2) hε2
      refine ⟨max N M, fun m hm ↦ ?_⟩; rw [eBVNorm, ← ENNReal.add_halves ε]
      refine add_le_add (hM m ((le_max_right N M).trans hm))
        ((distributionalVariation_sub_le_liminf_of_tendsto_eLpNorm
          (fun n ↦ (hu n).1) hlim_int hL1 m).trans
          (liminf_le_of_frequently_le' (Eventually.frequently ?_)))
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (distributionalVariation_le_eBVNorm _).trans (hN m ((le_max_left N M).trans hm) n hn).le
  refine ⟨u_lim, ⟨hlim_int, ?_⟩, h_tendsto⟩
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 h_tendsto) 1 one_pos
  have hsub : u_lim = (u N) - (u N - u_lim) := funext fun x ↦ by simp only [Pi.sub_apply]; ring
  rw [hsub]; exact ((hu N).sub ⟨(hu N).1.sub hlim_int,
    (distributionalVariation_le_eBVNorm _).trans_lt ((hN N le_rfl).trans_lt ENNReal.one_lt_top)⟩).2

/-- `BVSpace μ U` is a complete Banach space. -/
instance instCompleteSpaceBVSpace [FiniteDimensional ℝ E] [BorelSpace E] :
    CompleteSpace (BVSpace μ U) := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf ↦ ?_
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, eBVNorm μ U ((f m : E → ℝ) - f n) < ε := by
    intro ε hε; let δ : ℝ := (min ε 1).toReal
    have hδ : 0 < δ := ENNReal.toReal_pos (lt_min hε one_pos).ne'
      (min_le_right ε 1 |>.trans_lt ENNReal.one_lt_top).ne
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hf δ hδ; refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hdist : ‖f m - f n‖ < δ := by simpa [dist_eq_norm] using hN m hm n hn
    have hbv : ‖f m - f n‖ = bvNorm μ U ((f m : E → ℝ) - f n) :=
      (BVSpace.norm_eq_bvNorm (f m - f n)).trans
        (bvNorm_congr_ae (Lp.coeFn_sub (f m).toLp (f n).toLp))
    rw [hbv, bvNorm] at hdist; have hlt := (ENNReal.ofReal_lt_ofReal_iff hδ).2 hdist
    rw [ENNReal.ofReal_toReal (((f m).memBV_coe.sub (f n).memBV_coe).eBVNorm_lt_top.ne),
      ENNReal.ofReal_toReal (min_le_right ε 1 |>.trans_lt ENNReal.one_lt_top).ne] at hlt
    exact hlt.trans_le (min_le_left ε 1)
  obtain ⟨u_lim, hu_lim, h_tendsto⟩ :=
    exists_memBV_tendsto_eBVNorm_of_cauchy (fun n ↦ (f n).memBV_coe) hcauchy
  refine ⟨hu_lim.toBVSpace, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  have h_toReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_tendsto
  rw [ENNReal.toReal_zero] at h_toReal; refine h_toReal.congr fun n ↦ ?_
  dsimp only [Function.comp_apply]; exact ((BVSpace.norm_eq_bvNorm (f n - hu_lim.toBVSpace)).trans
    (bvNorm_congr_ae ((Lp.coeFn_sub (f n).toLp hu_lim.toBVSpace.toLp).trans
      (EventuallyEq.rfl.sub hu_lim.coeFn_toBVSpace)))).symm

end TauCeti
