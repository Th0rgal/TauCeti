/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Connected.Basic

/-!
# Curve reparametrization invariance, length--energy inequality, and constant-speed rigidity

This file develops the reparametrization and energy toolkit for parameterized curves on closed
intervals:

1. **Trace and complement invariance under monotone and antitone continuous onto
   reparametrizations**: if `φ : ℝ → ℝ` is continuous on `Icc c d` (`c ≤ d`) and either monotone
   with `φ c = a`, `φ d = b` or antitone with `φ c = b`, `φ d = a`, then `φ '' Icc c d = Icc a b`.
   Consequently, `(γ ∘ φ) '' Icc c d = γ '' Icc a b`, the complement `((γ ∘ φ) '' Icc c d)ᶜ` is
   preserved, and every connected component of the complement (`connectedComponentIn`) is
   invariant.
2. **Total and signed variation invariance under continuous onto reparametrizations**: for a curve
   `γ : ℝ → X` in a pseudo-emetric space `X`, monotone and antitone continuous onto
   reparametrizations `φ : Icc c d → Icc a b` possess right-inverse partition lifts and preserve
   `eVariationOn` and `BoundedVariationOn`. For the real-valued signed variation
   `variationOnFromTo`, monotone reparametrizations preserve `variationOnFromTo` between arbitrary
   parameter pairs `s, t ∈ Icc c d`, while antitone reparametrizations reverse its sign:
   `variationOnFromTo (γ ∘ φ) (Icc c d) s t = - variationOnFromTo γ (Icc a b) (φ s) (φ t)`.
3. **Length--energy inequality and constant-speed energy identity**: for a curve `γ : ℝ → E` in a
   real normed space with `MemLp (deriv γ) 2 (volume.restrict (Icc a b))`, the exact variance
   identity
   `(b - a) * (∫ t in a..b, ‖deriv γ t‖ ^ 2) - (∫ t in a..b, ‖deriv γ t‖) ^ 2 =
     (b - a) * ∫ t in a..b, (‖deriv γ t‖ - avgSpeed γ a b) ^ 2`
   yields the Cauchy--Schwarz length--energy inequality
   `(∫ t in a..b, ‖deriv γ t‖) ^ 2 ≤ (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2`, the constant-speed
   energy identity, and the complete equality characterization (`‖deriv γ t‖ = avgSpeed γ a b`
   almost everywhere on `Icc a b`).

## Main definitions

* `TauCeti.avgSpeed`: the average speed `(b - a)⁻¹ * ∫ t in a..b, ‖deriv γ t‖` of a curve `γ` on
  `[a, b]`.

## Main results

* `TauCeti.image_Icc_of_monotoneOn_continuousOn`,
  `TauCeti.image_comp_Icc_of_monotoneOn_continuousOn`,
  `TauCeti.connectedComponentIn_compl_image_comp_Icc_of_monotoneOn_continuousOn`: trace and
  complement component invariance under monotone continuous onto reparametrizations.
* `TauCeti.image_Icc_of_antitoneOn_continuousOn`,
  `TauCeti.image_comp_Icc_of_antitoneOn_continuousOn`,
  `TauCeti.connectedComponentIn_compl_image_comp_Icc_of_antitoneOn_continuousOn`: trace and
  complement component invariance under antitone continuous onto reparametrizations.
* `TauCeti.exists_monotone_Icc_comp_eq_of_monotoneOn_continuousOn`: partition-lifting lemma
  producing a monotone tuple in `Icc c d` lifting any monotone tuple in `Icc a b`.
* `TauCeti.eVariationOn_comp_eq_of_monotoneOn_continuousOn`,
  `TauCeti.eVariationOn_comp_eq_of_antitoneOn_continuousOn`,
  `TauCeti.variationOnFromTo_comp_eq_of_monotoneOn_continuousOn`,
  `TauCeti.variationOnFromTo_comp_pts_eq_neg_of_antitoneOn_continuousOn`: total and signed
  variation behavior under monotone and antitone continuous onto reparametrizations.
* `TauCeti.norm_deriv_energy_deficiency_identity`,
  `TauCeti.sq_intervalIntegral_norm_deriv_le_sub_mul_intervalIntegral_norm_deriv_sq`,
  `TauCeti.sub_mul_intervalIntegral_norm_deriv_sq_eq_sq_of_ae_norm_deriv_eq_const`,
  `TauCeti.sq_intervalIntegral_norm_deriv_eq_iff_ae_norm_deriv_eq_avgSpeed`: variance identity,
  length--energy inequality, constant-speed energy identity, and constant-speed rigidity.
-/

public section

open Filter MeasureTheory Set intervalIntegral
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {a b c d : ℝ} {X Y E : Type*}

/-! ### Trace and complement invariance under monotone and antitone reparametrizations -/

/-- If `φ` is monotone on `Icc c d` (`c ≤ d`) with `φ c = a` and `φ d = b`, then `a ≤ b`. -/
theorem le_of_monotoneOn_Icc (hcd : c ≤ d) {φ : ℝ → ℝ} (hφ : MonotoneOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) : a ≤ b :=
  hφc ▸ hφd ▸ hφ (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd

/-- If `φ` is antitone on `Icc c d` (`c ≤ d`) with `φ c = b` and `φ d = a`, then `a ≤ b`. -/
theorem le_of_antitoneOn_Icc (hcd : c ≤ d) {φ : ℝ → ℝ} (hφ : AntitoneOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) : a ≤ b :=
  hφd ▸ hφc ▸ hφ (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd

/-- A function `φ` that is monotone on `Icc c d` with `φ c = a` and `φ d = b` maps `Icc c d` into
`Icc a b`. -/
theorem mapsTo_Icc_of_monotoneOn {φ : ℝ → ℝ} (hφ : MonotoneOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) : MapsTo φ (Icc c d) (Icc a b) := by
  intro t ht
  have hcd : c ≤ d := ht.1.trans ht.2
  exact ⟨hφc ▸ hφ (left_mem_Icc.2 hcd) ht ht.1, hφd ▸ hφ ht (right_mem_Icc.2 hcd) ht.2⟩

/-- A continuous function `φ` on `Icc c d` (`c ≤ d`) with `φ c = a` and `φ d = b` is surjective
from `Icc c d` onto `Icc a b`. -/
theorem surjOn_Icc_of_continuousOn (hcd : c ≤ d) {φ : ℝ → ℝ} (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) : SurjOn φ (Icc c d) (Icc a b) :=
  hφc ▸ hφd ▸ intermediate_value_Icc hcd hcont

/-- If `φ` is monotone and continuous on `Icc c d` (`c ≤ d`) with `φ c = a` and `φ d = b`, then
`φ '' Icc c d = Icc a b`. -/
theorem image_Icc_of_monotoneOn_continuousOn (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) : φ '' Icc c d = Icc a b :=
  Subset.antisymm (mapsTo_iff_image_subset.1 (mapsTo_Icc_of_monotoneOn hφ hφc hφd))
    (surjOn_Icc_of_continuousOn hcd hcont hφc hφd)

/-- **Trace invariance under monotone continuous onto reparametrization**: if `φ` is monotone and
continuous on `Icc c d` (`c ≤ d`) with `φ c = a` and `φ d = b`, then `γ ∘ φ` has the same trace on
`Icc c d` as `γ` on `Icc a b`. -/
theorem image_comp_Icc_of_monotoneOn_continuousOn (γ : ℝ → Y) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) : (γ ∘ φ) '' Icc c d = γ '' Icc a b := by
  rw [Set.image_comp, image_Icc_of_monotoneOn_continuousOn hcd hφ hcont hφc hφd]

/-- Complement invariance of the trace under a monotone continuous onto reparametrization. -/
theorem compl_image_comp_Icc_of_monotoneOn_continuousOn (γ : ℝ → Y) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) : ((γ ∘ φ) '' Icc c d)ᶜ = (γ '' Icc a b)ᶜ := by
  rw [image_comp_Icc_of_monotoneOn_continuousOn γ hcd hφ hcont hφc hφd]

/-- Connected components of the trace complement (such as the inside and outside of a closed curve)
are invariant under monotone continuous onto reparametrizations. -/
theorem connectedComponentIn_compl_image_comp_Icc_of_monotoneOn_continuousOn [TopologicalSpace Y]
    (γ : ℝ → Y) (z : Y) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) :
    connectedComponentIn (((γ ∘ φ) '' Icc c d)ᶜ) z = connectedComponentIn ((γ '' Icc a b)ᶜ) z := by
  rw [compl_image_comp_Icc_of_monotoneOn_continuousOn γ hcd hφ hcont hφc hφd]

/-- A function `φ` that is antitone on `Icc c d` with `φ c = b` and `φ d = a` maps `Icc c d` into
`Icc a b`. -/
theorem mapsTo_Icc_of_antitoneOn {φ : ℝ → ℝ} (hφ : AntitoneOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) : MapsTo φ (Icc c d) (Icc a b) := by
  intro t ht
  have hcd : c ≤ d := ht.1.trans ht.2
  exact ⟨hφd ▸ hφ ht (right_mem_Icc.2 hcd) ht.2, hφc ▸ hφ (left_mem_Icc.2 hcd) ht ht.1⟩

/-- A continuous function `φ` on `Icc c d` (`c ≤ d`) with `φ c = b` and `φ d = a` is surjective
from `Icc c d` onto `Icc a b`. -/
theorem surjOn_Icc_of_continuousOn_swap (hcd : c ≤ d) {φ : ℝ → ℝ} (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) : SurjOn φ (Icc c d) (Icc a b) :=
  hφd ▸ hφc ▸ intermediate_value_Icc' hcd hcont

/-- If `φ` is antitone and continuous on `Icc c d` (`c ≤ d`) with `φ c = b` and `φ d = a`, then
`φ '' Icc c d = Icc a b`. -/
theorem image_Icc_of_antitoneOn_continuousOn (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) : φ '' Icc c d = Icc a b :=
  Subset.antisymm (mapsTo_iff_image_subset.1 (mapsTo_Icc_of_antitoneOn hφ hφc hφd))
    (surjOn_Icc_of_continuousOn_swap hcd hcont hφc hφd)

/-- **Trace invariance under antitone continuous onto reparametrization**: if `φ` is antitone and
continuous on `Icc c d` (`c ≤ d`) with `φ c = b` and `φ d = a`, then `γ ∘ φ` has the same trace on
`Icc c d` as `γ` on `Icc a b`. -/
theorem image_comp_Icc_of_antitoneOn_continuousOn (γ : ℝ → Y) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) : (γ ∘ φ) '' Icc c d = γ '' Icc a b := by
  rw [Set.image_comp, image_Icc_of_antitoneOn_continuousOn hcd hφ hcont hφc hφd]

/-- Complement invariance of the trace under an antitone continuous onto reparametrization. -/
theorem compl_image_comp_Icc_of_antitoneOn_continuousOn (γ : ℝ → Y) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) : ((γ ∘ φ) '' Icc c d)ᶜ = (γ '' Icc a b)ᶜ := by
  rw [image_comp_Icc_of_antitoneOn_continuousOn γ hcd hφ hcont hφc hφd]

/-- Connected components of the trace complement are invariant under antitone continuous onto
reparametrizations. -/
theorem connectedComponentIn_compl_image_comp_Icc_of_antitoneOn_continuousOn [TopologicalSpace Y]
    (γ : ℝ → Y) (z : Y) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) :
    connectedComponentIn (((γ ∘ φ) '' Icc c d)ᶜ) z = connectedComponentIn ((γ '' Icc a b)ᶜ) z := by
  rw [compl_image_comp_Icc_of_antitoneOn_continuousOn γ hcd hφ hcont hφc hφd]

/-- The affine time-reversal `t ↦ a + b - t` is antitone on `Icc a b`. -/
theorem antitoneOn_add_sub_Icc (a b : ℝ) : AntitoneOn (fun t ↦ a + b - t) (Icc a b) :=
  fun _ _ _ _ hst ↦ sub_le_sub_left hst (a + b)

/-- The affine time-reversal `t ↦ a + b - t` maps `Icc a b` onto `Icc a b`. -/
@[simp]
theorem image_add_sub_Icc (a b : ℝ) : (fun t ↦ a + b - t) '' Icc a b = Icc a b := by
  rcases le_or_gt a b with hab | hab
  · exact image_Icc_of_antitoneOn_continuousOn hab (antitoneOn_add_sub_Icc a b)
      (continuousOn_const.sub continuousOn_id) (by ring) (by ring)
  · simp [Icc_eq_empty_of_lt hab]

/-- Reversing a curve on `Icc a b` via `t ↦ a + b - t` preserves its trace. -/
@[simp]
theorem image_comp_add_sub_Icc (γ : ℝ → Y) (a b : ℝ) :
    (fun t ↦ γ (a + b - t)) '' Icc a b = γ '' Icc a b := by
  change (γ ∘ fun t ↦ a + b - t) '' Icc a b = γ '' Icc a b
  rw [Set.image_comp, image_add_sub_Icc]

/-- Reversing a curve on `Icc a b` via `t ↦ a + b - t` preserves the complement of its trace. -/
@[simp]
theorem compl_image_comp_add_sub_Icc (γ : ℝ → Y) (a b : ℝ) :
    ((fun t ↦ γ (a + b - t)) '' Icc a b)ᶜ = (γ '' Icc a b)ᶜ := by
  rw [image_comp_add_sub_Icc]

/-- Reversing a curve on `Icc a b` via `t ↦ a + b - t` preserves connected components of the
complement of its trace. -/
@[simp]
theorem connectedComponentIn_compl_image_comp_add_sub_Icc [TopologicalSpace Y]
    (γ : ℝ → Y) (a b : ℝ) (z : Y) :
    connectedComponentIn (((fun t ↦ γ (a + b - t)) '' Icc a b)ᶜ) z =
      connectedComponentIn ((γ '' Icc a b)ᶜ) z := by
  rw [compl_image_comp_add_sub_Icc]

/-- Positive affine rescaling `t ↦ a + (b - a) / (d - c) * (t - c)` (`c < d`, `a ≤ b`) is monotone
on `Icc c d`. -/
theorem monotoneOn_affine_Icc (hcd : c < d) (hab : a ≤ b) :
    MonotoneOn (fun t ↦ a + (b - a) / (d - c) * (t - c)) (Icc c d) := by
  intro s _ t _ hst
  dsimp only
  have hnonneg : 0 ≤ (b - a) / (d - c) := div_nonneg (sub_nonneg.2 hab) (sub_pos.2 hcd).le
  gcongr

/-- Positive affine rescaling `t ↦ a + (b - a) / (d - c) * (t - c)` (`c < d`, `a ≤ b`) maps
`Icc c d` onto `Icc a b`. -/
theorem image_affine_Icc (hcd : c < d) (hab : a ≤ b) :
    (fun t ↦ a + (b - a) / (d - c) * (t - c)) '' Icc c d = Icc a b := by
  have hne : d - c ≠ 0 := sub_ne_zero.2 hcd.ne'
  refine image_Icc_of_monotoneOn_continuousOn hcd.le (monotoneOn_affine_Icc hcd hab)
    (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    (by ring) ?_
  calc a + (b - a) / (d - c) * (d - c) = a + (b - a) := by rw [div_mul_cancel₀ _ hne]
    _ = b := by ring

/-- Positive affine rescaling `t ↦ a + (b - a) / (d - c) * (t - c)` (`c < d`, `a ≤ b`) preserves
the trace of a curve on `Icc c d`. -/
theorem image_comp_affine_Icc (γ : ℝ → Y) (hcd : c < d) (hab : a ≤ b) :
    (fun t ↦ γ (a + (b - a) / (d - c) * (t - c))) '' Icc c d = γ '' Icc a b := by
  change (γ ∘ fun t ↦ a + (b - a) / (d - c) * (t - c)) '' Icc c d = γ '' Icc a b
  rw [Set.image_comp, image_affine_Icc hcd hab]

/-! ### Partition lifting and total/signed variation under reparametrizations -/

/-- **Monotone partition-lifting lemma**: if `φ : ℝ → ℝ` is monotone and continuous on `Icc c d`
(`c ≤ d`) with `φ c = a` and `φ d = b`, then any monotone family `u : ι → ℝ` in `Icc a b` lifts to
a monotone family `v : ι → ℝ` in `Icc c d` such that `φ (v i) = u i` for all `i`. -/
theorem exists_monotone_Icc_comp_eq_of_monotoneOn_continuousOn {ι : Type*} [Preorder ι]
    (hcd : c ≤ d) {φ : ℝ → ℝ} (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) {u : ι → ℝ} (hu : Monotone u)
    (hu_mem : ∀ i, u i ∈ Icc a b) :
    ∃ v : ι → ℝ, Monotone v ∧ (∀ i, v i ∈ Icc c d) ∧ ∀ i, φ (v i) = u i := by
  have hsurj : SurjOn φ (Icc c d) (Icc a b) := surjOn_Icc_of_continuousOn hcd hcont hφc hφd
  let ψ := Function.invFunOn φ (Icc c d)
  have hψ_inv : EqOn (φ ∘ ψ) id (Icc a b) := hsurj.rightInvOn_invFunOn
  have hψ_maps : MapsTo ψ (Icc a b) (Icc c d) := hsurj.mapsTo_invFunOn
  have hψ_mono : MonotoneOn ψ (Icc a b) :=
    Function.monotoneOn_of_rightInvOn_of_mapsTo hφ hψ_inv hψ_maps
  refine ⟨ψ ∘ u, fun i j hij ↦ hψ_mono (hu_mem i) (hu_mem j) (hu hij),
    fun i ↦ hψ_maps (hu_mem i), fun i ↦ hψ_inv (hu_mem i)⟩

/-- **Antitone partition-lifting lemma**: if `φ : ℝ → ℝ` is antitone and continuous on `Icc c d`
(`c ≤ d`) with `φ c = b` and `φ d = a`, then any monotone family `u : ι → ℝ` in `Icc a b` lifts to
an antitone family `v : ι → ℝ` in `Icc c d` such that `φ (v i) = u i` for all `i`. -/
theorem exists_antitone_Icc_comp_eq_of_antitoneOn_continuousOn {ι : Type*} [Preorder ι]
    (hcd : c ≤ d) {φ : ℝ → ℝ} (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) {u : ι → ℝ} (hu : Monotone u)
    (hu_mem : ∀ i, u i ∈ Icc a b) :
    ∃ v : ι → ℝ, Antitone v ∧ (∀ i, v i ∈ Icc c d) ∧ ∀ i, φ (v i) = u i := by
  have hsurj : SurjOn φ (Icc c d) (Icc a b) := surjOn_Icc_of_continuousOn_swap hcd hcont hφc hφd
  let ψ := Function.invFunOn φ (Icc c d)
  have hψ_inv : EqOn (φ ∘ ψ) id (Icc a b) := hsurj.rightInvOn_invFunOn
  have hψ_maps : MapsTo ψ (Icc a b) (Icc c d) := hsurj.mapsTo_invFunOn
  have hψ_anti : AntitoneOn ψ (Icc a b) :=
    Function.antitoneOn_of_rightInvOn_of_mapsTo hφ hψ_inv hψ_maps
  refine ⟨ψ ∘ u, fun i j hij ↦ hψ_anti (hu_mem i) (hu_mem j) (hu hij),
    fun i ↦ hψ_maps (hu_mem i), fun i ↦ hψ_inv (hu_mem i)⟩

section Variation

variable [PseudoEMetricSpace X]

/-- Lower bound `eVariationOn γ (Icc a b) ≤ eVariationOn (γ ∘ φ) (Icc c d)` under a monotone
continuous onto reparametrization, proved by lifting monotone partitions of `Icc a b` to
`Icc c d`. -/
theorem le_eVariationOn_comp_of_monotoneOn_continuousOn (γ : ℝ → X) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) :
    eVariationOn γ (Icc a b) ≤ eVariationOn (γ ∘ φ) (Icc c d) := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, hu_mem⟩
  obtain ⟨v, hv_mono, hv_mem, hv_eq⟩ :=
    exists_monotone_Icc_comp_eq_of_monotoneOn_continuousOn hcd hφ hcont hφc hφd hu hu_mem
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans_le
    (le_iSup_of_le ⟨n, v, hv_mono, hv_mem⟩ le_rfl)
  simp [hv_eq]

/-- **Total variation invariance under monotone continuous onto reparametrization**: if `φ` is
monotone and continuous on `Icc c d` (`c ≤ d`) with `φ c = a` and `φ d = b`, then
`eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b)`. -/
theorem eVariationOn_comp_eq_of_monotoneOn_continuousOn (γ : ℝ → X) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) :
    eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b) :=
  le_antisymm
    (eVariationOn.comp_le_of_monotoneOn γ φ hφ (mapsTo_Icc_of_monotoneOn hφ hφc hφd))
    (le_eVariationOn_comp_of_monotoneOn_continuousOn γ hcd hφ hcont hφc hφd)

/-- `BoundedVariationOn` is invariant under monotone continuous onto reparametrizations. -/
theorem boundedVariationOn_comp_iff_of_monotoneOn_continuousOn (γ : ℝ → X) (hcd : c ≤ d)
    {φ : ℝ → ℝ} (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) :
    BoundedVariationOn (γ ∘ φ) (Icc c d) ↔ BoundedVariationOn γ (Icc a b) := by
  simp only [BoundedVariationOn, eVariationOn_comp_eq_of_monotoneOn_continuousOn γ hcd hφ hcont
    hφc hφd]

/-- **Signed variation invariance under monotone continuous onto reparametrization**: for any
`s, t ∈ Icc c d`, `variationOnFromTo (γ ∘ φ) (Icc c d) s t =
variationOnFromTo γ (Icc a b) (φ s) (φ t)`. -/
theorem variationOnFromTo_comp_pts_eq_of_monotoneOn_continuousOn (γ : ℝ → X) {φ : ℝ → ℝ}
    (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) {s t : ℝ} (hs : s ∈ Icc c d) (ht : t ∈ Icc c d) :
    variationOnFromTo (γ ∘ φ) (Icc c d) s t =
      variationOnFromTo γ (Icc a b) (φ s) (φ t) := by
  have hmaps : MapsTo φ (Icc c d) (Icc a b) := mapsTo_Icc_of_monotoneOn hφ hφc hφd
  have hφs : φ s ∈ Icc a b := hmaps hs
  have hφt : φ t ∈ Icc a b := hmaps ht
  rcases le_total s t with hst | hts
  · have hφst : φ s ≤ φ t := hφ hs ht hst
    have hsub₁ : Icc c d ∩ Icc s t = Icc s t :=
      inter_eq_self_of_subset_right (Icc_subset_Icc hs.1 ht.2)
    have hsub₂ : Icc a b ∩ Icc (φ s) (φ t) = Icc (φ s) (φ t) :=
      inter_eq_self_of_subset_right (Icc_subset_Icc hφs.1 hφt.2)
    rw [variationOnFromTo.eq_of_le _ _ hst, variationOnFromTo.eq_of_le _ _ hφst, hsub₁, hsub₂,
      eVariationOn_comp_eq_of_monotoneOn_continuousOn γ hst
        (hφ.mono (Icc_subset_Icc hs.1 ht.2)) (hcont.mono (Icc_subset_Icc hs.1 ht.2)) rfl rfl]
  · have hφts : φ t ≤ φ s := hφ ht hs hts
    have hsub₁ : Icc c d ∩ Icc t s = Icc t s :=
      inter_eq_self_of_subset_right (Icc_subset_Icc ht.1 hs.2)
    have hsub₂ : Icc a b ∩ Icc (φ t) (φ s) = Icc (φ t) (φ s) :=
      inter_eq_self_of_subset_right (Icc_subset_Icc hφt.1 hφs.2)
    rw [variationOnFromTo.eq_of_ge _ _ hts, variationOnFromTo.eq_of_ge _ _ hφts, hsub₁, hsub₂,
      eVariationOn_comp_eq_of_monotoneOn_continuousOn γ hts
        (hφ.mono (Icc_subset_Icc ht.1 hs.2)) (hcont.mono (Icc_subset_Icc ht.1 hs.2)) rfl rfl]

/-- **Endpoint signed variation invariance under monotone continuous onto reparametrization**:
`variationOnFromTo (γ ∘ φ) (Icc c d) c d = variationOnFromTo γ (Icc a b) a b`. -/
theorem variationOnFromTo_comp_eq_of_monotoneOn_continuousOn (γ : ℝ → X) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : MonotoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) :
    variationOnFromTo (γ ∘ φ) (Icc c d) c d = variationOnFromTo γ (Icc a b) a b := by
  simpa [hφc, hφd] using variationOnFromTo_comp_pts_eq_of_monotoneOn_continuousOn γ hφ hcont
    hφc hφd (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd)

/-- **Total variation invariance under antitone continuous onto reparametrization**: if `φ` is
antitone and continuous on `Icc c d` (`c ≤ d`) with `φ c = b` and `φ d = a`, then
`eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b)`. -/
theorem eVariationOn_comp_eq_of_antitoneOn_continuousOn (γ : ℝ → X) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) :
    eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b) := by
  rw [eVariationOn.comp_eq_of_antitoneOn γ φ hφ,
    image_Icc_of_antitoneOn_continuousOn hcd hφ hcont hφc hφd]

/-- Lower bound `eVariationOn γ (Icc a b) ≤ eVariationOn (γ ∘ φ) (Icc c d)` under an antitone
continuous onto reparametrization. -/
theorem le_eVariationOn_comp_of_antitoneOn_continuousOn (γ : ℝ → X) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) :
    eVariationOn γ (Icc a b) ≤ eVariationOn (γ ∘ φ) (Icc c d) :=
  (eVariationOn_comp_eq_of_antitoneOn_continuousOn γ hcd hφ hcont hφc hφd).ge

/-- `BoundedVariationOn` is invariant under antitone continuous onto reparametrizations. -/
theorem boundedVariationOn_comp_iff_of_antitoneOn_continuousOn (γ : ℝ → X) (hcd : c ≤ d)
    {φ : ℝ → ℝ} (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) :
    BoundedVariationOn (γ ∘ φ) (Icc c d) ↔ BoundedVariationOn γ (Icc a b) := by
  simp only [BoundedVariationOn, eVariationOn_comp_eq_of_antitoneOn_continuousOn γ hcd hφ hcont
    hφc hφd]

/-- **Sign reversal of signed variation under antitone continuous onto reparametrization**: for any
`s, t ∈ Icc c d`,
`variationOnFromTo (γ ∘ φ) (Icc c d) s t = - variationOnFromTo γ (Icc a b) (φ s) (φ t)`. -/
theorem variationOnFromTo_comp_pts_eq_neg_of_antitoneOn_continuousOn (γ : ℝ → X) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) {s t : ℝ} (hs : s ∈ Icc c d) (ht : t ∈ Icc c d) :
    variationOnFromTo (γ ∘ φ) (Icc c d) s t =
      -variationOnFromTo γ (Icc a b) (φ s) (φ t) := by
  have hmaps : MapsTo φ (Icc c d) (Icc a b) := mapsTo_Icc_of_antitoneOn hφ hφc hφd
  have hφs : φ s ∈ Icc a b := hmaps hs
  have hφt : φ t ∈ Icc a b := hmaps ht
  rcases le_total s t with hst | hts
  · have hφts : φ t ≤ φ s := hφ hs ht hst
    have hsub₁ : Icc c d ∩ Icc s t = Icc s t :=
      inter_eq_self_of_subset_right (Icc_subset_Icc hs.1 ht.2)
    have hsub₂ : Icc a b ∩ Icc (φ t) (φ s) = Icc (φ t) (φ s) :=
      inter_eq_self_of_subset_right (Icc_subset_Icc hφt.1 hφs.2)
    rw [variationOnFromTo.eq_of_le _ _ hst, variationOnFromTo.eq_of_ge _ _ hφts, neg_neg,
      hsub₁, hsub₂, eVariationOn_comp_eq_of_antitoneOn_continuousOn γ hst
        (hφ.mono (Icc_subset_Icc hs.1 ht.2)) (hcont.mono (Icc_subset_Icc hs.1 ht.2)) rfl rfl]
  · have hφst : φ s ≤ φ t := hφ ht hs hts
    have hsub₁ : Icc c d ∩ Icc t s = Icc t s :=
      inter_eq_self_of_subset_right (Icc_subset_Icc ht.1 hs.2)
    have hsub₂ : Icc a b ∩ Icc (φ s) (φ t) = Icc (φ s) (φ t) :=
      inter_eq_self_of_subset_right (Icc_subset_Icc hφs.1 hφt.2)
    rw [variationOnFromTo.eq_of_ge _ _ hts, variationOnFromTo.eq_of_le _ _ hφst,
      hsub₁, hsub₂, eVariationOn_comp_eq_of_antitoneOn_continuousOn γ hts
        (hφ.mono (Icc_subset_Icc ht.1 hs.2)) (hcont.mono (Icc_subset_Icc ht.1 hs.2)) rfl rfl]

/-- Under an antitone continuous onto reparametrization `φ : Icc c d → Icc a b` (`c ≤ d`,
`φ c = b`, `φ d = a`), the forward signed variation from `c` to `d` equals the forward signed
variation of `γ` from `a` to `b` (and the negation of the signed variation from `φ c = b` to
`φ d = a`). -/
theorem variationOnFromTo_comp_eq_of_antitoneOn_continuousOn (γ : ℝ → X) (hcd : c ≤ d) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) :
    variationOnFromTo (γ ∘ φ) (Icc c d) c d = variationOnFromTo γ (Icc a b) a b := by
  have h := variationOnFromTo_comp_pts_eq_neg_of_antitoneOn_continuousOn γ hφ hcont hφc hφd
    (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd)
  rw [hφc, hφd, variationOnFromTo.eq_neg_swap γ (Icc a b) b a, neg_neg] at h
  exact h

/-- Under an antitone continuous onto reparametrization `φ : Icc c d → Icc a b` (`c ≤ d`,
`φ c = b`, `φ d = a`), reversing the endpoints from `(c, d)` to `(d, c)` negates the signed
variation of `γ` from `a` to `b`. -/
theorem variationOnFromTo_comp_swap_eq_neg_of_antitoneOn_continuousOn (γ : ℝ → X) (hcd : c ≤ d)
    {φ : ℝ → ℝ} (hφ : AntitoneOn φ (Icc c d)) (hcont : ContinuousOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) :
    variationOnFromTo (γ ∘ φ) (Icc c d) d c = -variationOnFromTo γ (Icc a b) a b := by
  rw [variationOnFromTo.eq_neg_swap,
    variationOnFromTo_comp_eq_of_antitoneOn_continuousOn γ hcd hφ hcont hφc hφd]

/-- Time reversal `t ↦ a + b - t` on `Icc a b` preserves `eVariationOn`. -/
@[simp]
theorem eVariationOn_sub_Icc (γ : ℝ → X) (a b : ℝ) :
    eVariationOn (fun t ↦ γ (a + b - t)) (Icc a b) = eVariationOn γ (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  · exact eVariationOn_comp_eq_of_antitoneOn_continuousOn γ hab (antitoneOn_add_sub_Icc a b)
      (continuousOn_const.sub continuousOn_id) (by ring) (by ring)
  · simp [Icc_eq_empty_of_lt hab]

/-- Time reversal `t ↦ a + b - t` on `Icc a b` preserves `BoundedVariationOn`. -/
@[simp]
theorem boundedVariationOn_sub_Icc (γ : ℝ → X) (a b : ℝ) :
    BoundedVariationOn (fun t ↦ γ (a + b - t)) (Icc a b) ↔ BoundedVariationOn γ (Icc a b) := by
  simp only [BoundedVariationOn, eVariationOn_sub_Icc]

/-- Time reversal `t ↦ a + b - t` on `Icc a b` preserves `variationOnFromTo` from `a` to `b`. -/
@[simp]
theorem variationOnFromTo_sub_Icc (γ : ℝ → X) (a b : ℝ) :
    variationOnFromTo (fun t ↦ γ (a + b - t)) (Icc a b) a b =
      variationOnFromTo γ (Icc a b) a b := by
  by_cases hab : a ≤ b
  · simp [variationOnFromTo.eq_of_le _ _ hab]
  · have hba : b ≤ a := le_of_not_ge hab
    simp [variationOnFromTo.eq_of_ge _ _ hba, Icc_eq_empty hab]

/-- Time reversal `t ↦ a + b - t` on `Icc a b` negates `variationOnFromTo` when evaluated from `b`
to `a`. -/
@[simp]
theorem variationOnFromTo_sub_Icc_swap (γ : ℝ → X) (a b : ℝ) :
    variationOnFromTo (fun t ↦ γ (a + b - t)) (Icc a b) b a =
      -variationOnFromTo γ (Icc a b) a b := by
  rw [variationOnFromTo.eq_neg_swap, variationOnFromTo_sub_Icc]

/-- For `s, t ∈ Icc a b`, time reversal `u ↦ a + b - u` negates `variationOnFromTo` between the
reflected points `a + b - s` and `a + b - t`. -/
theorem variationOnFromTo_sub_Icc_pts (γ : ℝ → X) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    variationOnFromTo (fun u ↦ γ (a + b - u)) (Icc a b) s t =
      -variationOnFromTo γ (Icc a b) (a + b - s) (a + b - t) :=
  variationOnFromTo_comp_pts_eq_neg_of_antitoneOn_continuousOn γ (antitoneOn_add_sub_Icc a b)
    (continuousOn_const.sub continuousOn_id) (by ring) (by ring) hs ht

/-- Positive affine rescaling `t ↦ a + (b - a) / (d - c) * (t - c)` (`c < d`, `a ≤ b`) preserves
`eVariationOn`. -/
theorem eVariationOn_comp_affine_Icc (γ : ℝ → X) (hcd : c < d) (hab : a ≤ b) :
    eVariationOn (fun t ↦ γ (a + (b - a) / (d - c) * (t - c))) (Icc c d) =
      eVariationOn γ (Icc a b) := by
  have hne : d - c ≠ 0 := sub_ne_zero.2 hcd.ne'
  refine eVariationOn_comp_eq_of_monotoneOn_continuousOn γ hcd.le (monotoneOn_affine_Icc hcd hab)
    (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    (by ring) ?_
  calc a + (b - a) / (d - c) * (d - c) = a + (b - a) := by rw [div_mul_cancel₀ _ hne]
    _ = b := by ring

/-- Positive affine rescaling `t ↦ a + (b - a) / (d - c) * (t - c)` (`c < d`, `a ≤ b`) preserves
`variationOnFromTo`. -/
theorem variationOnFromTo_comp_affine_Icc (γ : ℝ → X) (hcd : c < d) (hab : a ≤ b) :
    variationOnFromTo (fun t ↦ γ (a + (b - a) / (d - c) * (t - c))) (Icc c d) c d =
      variationOnFromTo γ (Icc a b) a b := by
  have hne : d - c ≠ 0 := sub_ne_zero.2 hcd.ne'
  refine variationOnFromTo_comp_eq_of_monotoneOn_continuousOn γ hcd.le
    (monotoneOn_affine_Icc hcd hab)
    (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    (by ring) ?_
  calc a + (b - a) / (d - c) * (d - c) = a + (b - a) := by rw [div_mul_cancel₀ _ hne]
    _ = b := by ring

end Variation

/-! ### Constant-speed energy identity and Cauchy--Schwarz length--energy inequality -/

section Energy

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **average speed** `(b - a)⁻¹ * ∫ t in a..b, ‖deriv γ t‖` of a curve `γ : ℝ → E` on
`[a, b]`. -/
noncomputable def avgSpeed (γ : ℝ → E) (a b : ℝ) : ℝ :=
  (b - a)⁻¹ * ∫ t in a..b, ‖deriv γ t‖

/-- On a degenerate interval `[a, a]`, the average speed is `0`. -/
@[simp]
theorem avgSpeed_self (γ : ℝ → E) (a : ℝ) : avgSpeed γ a a = 0 := by
  simp [avgSpeed]

/-- If `a ≤ b`, the average speed `avgSpeed γ a b` is nonnegative. -/
theorem avgSpeed_nonneg (γ : ℝ → E) (hab : a ≤ b) : 0 ≤ avgSpeed γ a b := by
  unfold avgSpeed
  refine mul_nonneg (inv_nonneg.2 (sub_nonneg.2 hab)) ?_
  exact intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _

/-- For `a < b`, multiplying `avgSpeed γ a b` by `b - a` recovers the speed integral
`∫ t in a..b, ‖deriv γ t‖`. -/
theorem sub_mul_avgSpeed (γ : ℝ → E) (hab : a < b) :
    (b - a) * avgSpeed γ a b = ∫ t in a..b, ‖deriv γ t‖ := by
  unfold avgSpeed
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  exact mul_inv_cancel_left₀ hne _

/-- Square-integrability of `deriv γ` on `Icc a b` (`a ≤ b`) implies interval integrability of
`‖deriv γ ·‖` on `a..b`. -/
theorem intervalIntegrable_norm_deriv_of_memLp_two (hab : a ≤ b) {γ : ℝ → E}
    (hγ' : MemLp (deriv γ) 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t ↦ ‖deriv γ t‖) volume a b := by
  have : Fact (volume (Icc a b) < ∞) := ⟨measure_Icc_lt_top⟩
  have hint : IntegrableOn (fun t ↦ ‖deriv γ t‖) (Icc a b) volume :=
    (hγ'.integrable one_le_two).norm
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact hint.mono_set Ioc_subset_Icc_self

/-- Square-integrability of `deriv γ` on `Icc a b` (`a ≤ b`) implies interval integrability of
`‖deriv γ ·‖ ^ 2` on `a..b`. -/
theorem intervalIntegrable_norm_deriv_sq_of_memLp_two (hab : a ≤ b) {γ : ℝ → E}
    (hγ' : MemLp (deriv γ) 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t ↦ ‖deriv γ t‖ ^ 2) volume a b := by
  have hint : IntegrableOn (fun t ↦ ‖deriv γ t‖ ^ 2) (Icc a b) volume := by
    simpa [IntegrableOn] using (memLp_two_iff_integrable_sq_norm hγ'.aestronglyMeasurable).1 hγ'
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact hint.mono_set Ioc_subset_Icc_self

/-- **Exact variance / Cauchy--Schwarz deficiency identity** for the speed of a curve: for
`a ≤ b` and `MemLp (deriv γ) 2 (volume.restrict (Icc a b))`,
`(b - a) * (∫ t in a..b, ‖deriv γ t‖ ^ 2) - (∫ t in a..b, ‖deriv γ t‖) ^ 2 =
  (b - a) * ∫ t in a..b, (‖deriv γ t‖ - avgSpeed γ a b) ^ 2`. -/
theorem norm_deriv_energy_deficiency_identity (hab : a ≤ b) {γ : ℝ → E}
    (hγ' : MemLp (deriv γ) 2 (volume.restrict (Icc a b))) :
    (b - a) * (∫ t in a..b, ‖deriv γ t‖ ^ 2) - (∫ t in a..b, ‖deriv γ t‖) ^ 2 =
      (b - a) * ∫ t in a..b, (‖deriv γ t‖ - avgSpeed γ a b) ^ 2 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  set v := avgSpeed γ a b
  have hv : (b - a) * v = ∫ t in a..b, ‖deriv γ t‖ := sub_mul_avgSpeed γ hlt
  have hint₁ : IntervalIntegrable (fun t ↦ ‖deriv γ t‖) volume a b :=
    intervalIntegrable_norm_deriv_of_memLp_two hab hγ'
  have hint₂ : IntervalIntegrable (fun t ↦ ‖deriv γ t‖ ^ 2) volume a b :=
    intervalIntegrable_norm_deriv_sq_of_memLp_two hab hγ'
  have hexpand : (fun t ↦ (‖deriv γ t‖ - v) ^ 2) =
      fun t ↦ (‖deriv γ t‖ ^ 2 - (2 * v) * ‖deriv γ t‖) + v ^ 2 := by
    ext t; ring
  rw [hexpand, intervalIntegral.integral_add (hint₂.sub (hint₁.const_mul (2 * v)))
    intervalIntegrable_const, intervalIntegral.integral_sub hint₂ (hint₁.const_mul (2 * v)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, ← hv]
  ring

/-- **Cauchy--Schwarz length--energy inequality**: for `a ≤ b` and
`MemLp (deriv γ) 2 (volume.restrict (Icc a b))`,
`(∫ t in a..b, ‖deriv γ t‖) ^ 2 ≤ (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2`. -/
theorem sq_intervalIntegral_norm_deriv_le_sub_mul_intervalIntegral_norm_deriv_sq (hab : a ≤ b)
    {γ : ℝ → E} (hγ' : MemLp (deriv γ) 2 (volume.restrict (Icc a b))) :
    (∫ t in a..b, ‖deriv γ t‖) ^ 2 ≤ (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2 := by
  have hid := norm_deriv_energy_deficiency_identity hab hγ'
  have hnonneg : 0 ≤ (b - a) * ∫ t in a..b, (‖deriv γ t‖ - avgSpeed γ a b) ^ 2 :=
    mul_nonneg (sub_nonneg.2 hab)
      (intervalIntegral.integral_nonneg hab fun _ _ ↦ sq_nonneg _)
  linarith

/-- If `‖deriv γ t‖ = v` for `volume`-almost every `t ∈ Icc a b` (`a ≤ b`), then
`∫ t in a..b, ‖deriv γ t‖ = (b - a) * v`. -/
theorem intervalIntegral_norm_deriv_eq_of_ae_eq_const (hab : a ≤ b) {γ : ℝ → E} {v : ℝ}
    (hae : ∀ᵐ t ∂(volume.restrict (Icc a b)), ‖deriv γ t‖ = v) :
    ∫ t in a..b, ‖deriv γ t‖ = (b - a) * v := by
  have hae_Icc := (ae_restrict_iff' measurableSet_Icc).1 hae
  have hcongr : ∫ t in a..b, ‖deriv γ t‖ = ∫ _ in a..b, v := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [hae_Icc] with t ht ht_mem
    exact ht (Ioc_subset_Icc_self ht_mem)
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]

/-- If `‖deriv γ t‖ = v` for `volume`-almost every `t ∈ Icc a b` (`a ≤ b`), then
`∫ t in a..b, ‖deriv γ t‖ ^ 2 = (b - a) * v ^ 2`. -/
theorem intervalIntegral_norm_deriv_sq_eq_of_ae_eq_const (hab : a ≤ b) {γ : ℝ → E} {v : ℝ}
    (hae : ∀ᵐ t ∂(volume.restrict (Icc a b)), ‖deriv γ t‖ = v) :
    ∫ t in a..b, ‖deriv γ t‖ ^ 2 = (b - a) * v ^ 2 := by
  have hae_Icc := (ae_restrict_iff' measurableSet_Icc).1 hae
  have hcongr : ∫ t in a..b, ‖deriv γ t‖ ^ 2 = ∫ _ in a..b, v ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [hae_Icc] with t ht ht_mem
    rw [ht (Ioc_subset_Icc_self ht_mem)]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]

/-- If `‖deriv γ t‖ = v` for `volume`-almost every `t ∈ Icc a b` (`a < b`), then
`avgSpeed γ a b = v`. -/
theorem avgSpeed_eq_of_ae_norm_deriv_eq_const (hab : a < b) {γ : ℝ → E} {v : ℝ}
    (hae : ∀ᵐ t ∂(volume.restrict (Icc a b)), ‖deriv γ t‖ = v) :
    avgSpeed γ a b = v := by
  unfold avgSpeed
  rw [intervalIntegral_norm_deriv_eq_of_ae_eq_const hab.le hae]
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  exact inv_mul_cancel_left₀ hne v

/-- **Constant-speed energy identity**: if `‖deriv γ t‖ = v` for `volume`-almost every
`t ∈ Icc a b` (`a ≤ b`), then `(b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2 =
(∫ t in a..b, ‖deriv γ t‖) ^ 2`. -/
theorem sub_mul_intervalIntegral_norm_deriv_sq_eq_sq_of_ae_norm_deriv_eq_const (hab : a ≤ b)
    {γ : ℝ → E} {v : ℝ} (hae : ∀ᵐ t ∂(volume.restrict (Icc a b)), ‖deriv γ t‖ = v) :
    (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2 = (∫ t in a..b, ‖deriv γ t‖) ^ 2 := by
  rw [intervalIntegral_norm_deriv_eq_of_ae_eq_const hab hae,
    intervalIntegral_norm_deriv_sq_eq_of_ae_eq_const hab hae]
  ring

/-- **Constant-speed equality characterization**: for `a < b` and
`MemLp (deriv γ) 2 (volume.restrict (Icc a b))`, equality
`(∫ t in a..b, ‖deriv γ t‖) ^ 2 = (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2` holds in the
length--energy inequality if and only if `‖deriv γ t‖ = avgSpeed γ a b` for `volume`-almost every
`t ∈ Icc a b`. -/
theorem sq_intervalIntegral_norm_deriv_eq_iff_ae_norm_deriv_eq_avgSpeed (hab : a < b) {γ : ℝ → E}
    (hγ' : MemLp (deriv γ) 2 (volume.restrict (Icc a b))) :
    (∫ t in a..b, ‖deriv γ t‖) ^ 2 = (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2 ↔
      ∀ᵐ t ∂(volume.restrict (Icc a b)), ‖deriv γ t‖ = avgSpeed γ a b := by
  refine ⟨fun heq ↦ ?_, fun hae ↦
    (sub_mul_intervalIntegral_norm_deriv_sq_eq_sq_of_ae_norm_deriv_eq_const hab.le hae).symm⟩
  set v := avgSpeed γ a b
  have hid := norm_deriv_energy_deficiency_identity hab.le hγ'
  have hpos : 0 < b - a := sub_pos.2 hab
  have hzero : ∫ t in a..b, (‖deriv γ t‖ - v) ^ 2 = 0 := by nlinarith [hid, heq, hpos]
  have hint₁ : IntervalIntegrable (fun t ↦ ‖deriv γ t‖) volume a b :=
    intervalIntegrable_norm_deriv_of_memLp_two hab.le hγ'
  have hint₂ : IntervalIntegrable (fun t ↦ ‖deriv γ t‖ ^ 2) volume a b :=
    intervalIntegrable_norm_deriv_sq_of_memLp_two hab.le hγ'
  have hint_sq : IntervalIntegrable (fun t ↦ (‖deriv γ t‖ - v) ^ 2) volume a b := by
    have hexpand : (fun t ↦ (‖deriv γ t‖ - v) ^ 2) =
        fun t ↦ (‖deriv γ t‖ ^ 2 - (2 * v) * ‖deriv γ t‖) + v ^ 2 := by
      ext t; ring
    rw [hexpand]
    exact (hint₂.sub (hint₁.const_mul (2 * v))).add intervalIntegrable_const
  have hae_Ioc : (fun t ↦ (‖deriv γ t‖ - v) ^ 2) =ᵐ[volume.restrict (Ioc a b)] 0 :=
    (integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
      (Eventually.of_forall fun _ ↦ sq_nonneg _) hint_sq).1 hzero
  have hae_Icc : (fun t ↦ (‖deriv γ t‖ - v) ^ 2) =ᵐ[volume.restrict (Icc a b)] 0 :=
    ae_restrict_of_ae_eq_of_ae_restrict Ioc_ae_eq_Icc hae_Ioc
  filter_upwards [hae_Icc] with t ht
  exact sub_eq_zero.1 (sq_eq_zero_iff.1 ht)

/-- Existential constant-speed characterization of equality in the length--energy inequality on
`[a, b]` (`a < b`). -/
theorem sq_intervalIntegral_norm_deriv_eq_iff_exists_ae_norm_deriv_eq_const (hab : a < b)
    {γ : ℝ → E} (hγ' : MemLp (deriv γ) 2 (volume.restrict (Icc a b))) :
    (∫ t in a..b, ‖deriv γ t‖) ^ 2 = (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2 ↔
      ∃ v : ℝ, ∀ᵐ t ∂(volume.restrict (Icc a b)), ‖deriv γ t‖ = v := by
  refine ⟨fun heq ↦ ⟨avgSpeed γ a b,
    (sq_intervalIntegral_norm_deriv_eq_iff_ae_norm_deriv_eq_avgSpeed hab hγ').1 heq⟩, ?_⟩
  rintro ⟨v, hv⟩
  exact (sub_mul_intervalIntegral_norm_deriv_sq_eq_sq_of_ae_norm_deriv_eq_const hab.le hv).symm

end Energy

end TauCeti
