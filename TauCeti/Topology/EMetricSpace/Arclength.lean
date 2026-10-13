/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Cumulative arclength and unit-speed Lipschitz factorization of rectifiable curves

For a curve `γ : α → X` of bounded variation on a closed interval `Icc a b`, the cumulative
signed variation `variationOnFromTo γ (Icc a b) a` and the cumulative extended variation
`fun t ↦ eVariationOn γ (Icc a t)` record the arclength along `γ` from `a`. When `γ` is continuous
on `Icc a b`, both cumulative arclength functions are continuous and monotone on `Icc a b`, and
in an extended metric space `γ` is constant on any subinterval where cumulative arclength is
constant.

For a continuous curve `γ : ℝ → X` of bounded variation on `Icc a b` (`a ≤ b`), we construct the
canonical generalized inverse `TauCeti.arcLengthInv γ a b : ℝ → ℝ` of cumulative arclength and
the associated arclength reparametrization `TauCeti.arcLengthReparam γ a b : ℝ → X`, proving that
`arcLengthReparam γ a b` is `1`-Lipschitz, factors `γ` via
`arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a t) = γ t` for all `t ∈ Icc a b`, has
unit-speed variation `ENNReal.ofReal (s₂ - s₁)` on every subinterval of
`Icc 0 (variationOnFromTo γ (Icc a b) a b)`, and preserves injectivity for injective arcs and
simple closed curves.

## Main definitions

* `TauCeti.arcLengthInv`: generalized right-inverse of `variationOnFromTo γ (Icc a b) a` on
  `Icc 0 (variationOnFromTo γ (Icc a b) a b)`, clamped to `Icc a b`.
* `TauCeti.arcLengthReparam`: unit-speed `1`-Lipschitz arclength reparametrization
  `γ ∘ arcLengthInv γ a b`.
* `TauCeti.arcLengthOrderIso`, `TauCeti.arcLengthHomeomorph`: order isomorphism and homeomorphism
  `Icc a b ≃ₜ Icc 0 (variationOnFromTo γ (Icc a b) a b)` induced by cumulative arclength when
  `InjOn γ (Ioo a b)`.

## Main results

* `BoundedVariationOn.continuousOn_variationOnFromTo_iff`,
  `BoundedVariationOn.continuousOn_eVariationOn_Icc`: continuity of cumulative arclength.
* `BoundedVariationOn.image_variationOnFromTo_Icc`: surjectivity of cumulative arclength onto
  `Icc 0 (variationOnFromTo γ (Icc a b) a b)`.
* `BoundedVariationOn.variationOnFromTo_Icc_eq_iff`: constancy of `γ` on zero-variation
  subintervals.
* `TauCeti.lipschitzWith_arcLengthReparam`, `TauCeti.arcLengthReparam_variationOnFromTo`,
  `TauCeti.eVariationOn_arcLengthReparam_Icc`: unit-speed `1`-Lipschitz factorization.
* `TauCeti.injOn_arcLengthReparam_Icc`, `TauCeti.injOn_arcLengthReparam_Ico`: injectivity of the
  arclength reparametrization for injective arcs and simple closed curves.
-/

public section

open Filter Set
open scoped ENNReal Topology

namespace TauCeti

/-! ### Concatenation and interval identities for variation -/

section WeakPseudoEMetricSpace

variable {α X : Type*} [LinearOrder α] [TopologicalSpace X] [WeakPseudoEMetricSpace X]
  {γ γ₁ γ₂ : α → X} {a b c t : α}

/-- The total variation on `Icc a c` of the concatenation at `b` of two curves `γ₁` and `γ₂`
with `γ₁ b = γ₂ b` is `eVariationOn γ₁ (Icc a b) + eVariationOn γ₂ (Icc b c)`. -/
theorem eVariationOn_ite_le_Icc (hab : a ≤ b) (hbc : b ≤ c) (hb : γ₁ b = γ₂ b) :
    eVariationOn (fun x ↦ if x ≤ b then γ₁ x else γ₂ x) (Icc a c) =
      eVariationOn γ₁ (Icc a b) + eVariationOn γ₂ (Icc b c) := by
  let g := fun x ↦ if x ≤ b then γ₁ x else γ₂ x
  have h1 : EqOn g γ₁ (Icc a b) := fun x hx ↦ ite_eq_left hx.2
  have h2 : EqOn g γ₂ (Icc b c) := fun x hx ↦ by
    rcases eq_or_lt_of_le hx.1 with rfl | hbx
    · simp [g, hb]
    · exact ite_eq_right hbx.not_ge
  have hadd := eVariationOn.Icc_add_Icc g (s := univ) hab hbc (mem_univ b)
  simp only [univ_inter] at hadd
  rw [← hadd, eVariationOn.congr h1, eVariationOn.congr h2]

/-- On `Icc a b`, cumulative signed variation at `t` is `(eVariationOn γ (Icc a t)).toReal`. -/
theorem variationOnFromTo_Icc_eq_toReal (ht : t ∈ Icc a b) :
    variationOnFromTo γ (Icc a b) a t = (eVariationOn γ (Icc a t)).toReal := by
  rw [variationOnFromTo.eq_of_le _ _ ht.1,
    inter_eq_self_of_subset_right (Icc_subset_Icc_right ht.2)]

/-- Cumulative signed variation from `a` to `b` on `Icc a b` (`a ≤ b`) is
`(eVariationOn γ (Icc a b)).toReal`. -/
theorem variationOnFromTo_Icc_self_right (hab : a ≤ b) :
    variationOnFromTo γ (Icc a b) a b = (eVariationOn γ (Icc a b)).toReal :=
  variationOnFromTo_Icc_eq_toReal (right_mem_Icc.2 hab)

end WeakPseudoEMetricSpace

/-! ### Cumulative arclength and continuity -/

section PseudoEMetricSpace

variable {α X : Type*} [LinearOrder α] [PseudoEMetricSpace X]
  {γ : α → X} {s : Set α} {a b t t₁ t₂ : α}

/-- If `γ` has bounded variation on `Icc a b`, then `ENNReal.ofReal` of the cumulative signed
variation at `t ∈ Icc a b` recovers `eVariationOn γ (Icc a t)`. -/
theorem _root_.BoundedVariationOn.ofReal_variationOnFromTo_Icc
    (hγ : BoundedVariationOn γ (Icc a b)) (ht : t ∈ Icc a b) :
    ENNReal.ofReal (variationOnFromTo γ (Icc a b) a t) = eVariationOn γ (Icc a t) := by
  rw [variationOnFromTo_Icc_eq_toReal ht,
    ENNReal.ofReal_toReal (hγ.mono (Icc_subset_Icc_right ht.2))]

/-- For `t₁, t₂ ∈ Icc a b` with `t₁ ≤ t₂`, the increment of cumulative signed variation equals
`(eVariationOn γ (Icc t₁ t₂)).toReal`. -/
theorem _root_.BoundedVariationOn.variationOnFromTo_Icc_sub
    (hγ : BoundedVariationOn γ (Icc a b)) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) (ht : t₁ ≤ t₂) :
    variationOnFromTo γ (Icc a b) a t₂ - variationOnFromTo γ (Icc a b) a t₁ =
      (eVariationOn γ (Icc t₁ t₂)).toReal := by
  rw [variationOnFromTo.sub_right hγ.locallyBoundedVariationOn ⟨le_rfl, ht₁.1.trans ht₁.2⟩ ht₂ ht₁,
    variationOnFromTo.eq_of_le _ _ ht, inter_eq_self_of_subset_right (Icc_subset_Icc ht₁.1 ht₂.2)]

/-- For `t₁, t₂ ∈ Icc a b` with `t₁ ≤ t₂`, `ENNReal.ofReal` of the increment of cumulative signed
variation equals `eVariationOn γ (Icc t₁ t₂)`. -/
theorem _root_.BoundedVariationOn.ofReal_variationOnFromTo_Icc_sub
    (hγ : BoundedVariationOn γ (Icc a b)) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) (ht : t₁ ≤ t₂) :
    ENNReal.ofReal (variationOnFromTo γ (Icc a b) a t₂ - variationOnFromTo γ (Icc a b) a t₁) =
      eVariationOn γ (Icc t₁ t₂) := by
  rw [hγ.variationOnFromTo_Icc_sub ht₁ ht₂ ht,
    ENNReal.ofReal_toReal (hγ.mono (Icc_subset_Icc ht₁.1 ht₂.2))]

/-- A curve of bounded variation on `Icc a b` is `1`-Lipschitz with respect to its cumulative
arclength parameter on `Icc a b`. -/
theorem _root_.BoundedVariationOn.edist_le_edist_variationOnFromTo_Icc
    (hγ : BoundedVariationOn γ (Icc a b)) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    edist (γ t₁) (γ t₂) ≤
      edist (variationOnFromTo γ (Icc a b) a t₁) (variationOnFromTo γ (Icc a b) a t₂) := by
  wlog hle : t₁ ≤ t₂ generalizing t₁ t₂
  · rw [edist_comm (γ t₁), edist_comm (variationOnFromTo _ _ _ t₁)]
    exact this ht₂ ht₁ (le_of_not_ge hle)
  have hmono := variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn
    ⟨le_rfl, ht₁.1.trans ht₁.2⟩ ht₁ ht₂ hle
  rw [edist_comm (variationOnFromTo _ _ _ t₁), edist_eq_enorm_sub,
    Real.enorm_eq_ofReal (sub_nonneg.2 hmono), hγ.ofReal_variationOnFromTo_Icc_sub ht₁ ht₂ hle]
  exact eVariationOn.edist_le γ ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩

/-- Cumulative signed variation `variationOnFromTo γ (Icc a b) a` maps `Icc a b` into
`Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem _root_.BoundedVariationOn.mapsTo_variationOnFromTo_Icc
    (hγ : BoundedVariationOn γ (Icc a b)) :
    MapsTo (variationOnFromTo γ (Icc a b) a) (Icc a b)
      (Icc 0 (variationOnFromTo γ (Icc a b) a b)) := fun _ ht ↦
  ⟨variationOnFromTo.nonneg_of_le γ (Icc a b) ht.1,
    variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn ⟨le_rfl, ht.1.trans ht.2⟩
      ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2⟩

variable [TopologicalSpace α] [OrderTopology α]

/-- If `γ` has bounded variation on `s` and `a ∈ s`, then `variationOnFromTo γ s a` is continuous
on `s` if and only if `γ` is continuous on `s`. -/
theorem _root_.BoundedVariationOn.continuousOn_variationOnFromTo_iff
    (hγ : BoundedVariationOn γ s) (ha : a ∈ s) :
    ContinuousOn (variationOnFromTo γ s a) s ↔ ContinuousOn γ s :=
  forall₂_congr fun _ hx ↦ hγ.continuousWithinAt_variationOnFromTo_iff ha hx

/-- If `γ` has bounded variation and is continuous on `s`, then `variationOnFromTo γ s a` is
continuous on `s` for any basepoint `a ∈ s`. -/
theorem _root_.BoundedVariationOn.continuousOn_variationOnFromTo
    (hγ : BoundedVariationOn γ s) (ha : a ∈ s) (hc : ContinuousOn γ s) :
    ContinuousOn (variationOnFromTo γ s a) s :=
  (hγ.continuousOn_variationOnFromTo_iff ha).2 hc

/-- If `γ` has bounded variation and is continuous on `Icc a b`, then cumulative signed variation
`variationOnFromTo γ (Icc a b) a` is continuous on `Icc a b`. -/
theorem _root_.BoundedVariationOn.continuousOn_variationOnFromTo_Icc
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    ContinuousOn (variationOnFromTo γ (Icc a b) a) (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  · exact hγ.continuousOn_variationOnFromTo (left_mem_Icc.2 hab) hc
  · rw [Icc_eq_empty hab.not_ge]; exact continuousOn_empty _

/-- If `γ` has bounded variation and is continuous on `Icc a b`, then cumulative extended variation
`fun t ↦ eVariationOn γ (Icc a t)` is continuous on `Icc a b`. -/
theorem _root_.BoundedVariationOn.continuousOn_eVariationOn_Icc
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    ContinuousOn (fun t ↦ eVariationOn γ (Icc a t)) (Icc a b) :=
  (ENNReal.continuous_ofReal.comp_continuousOn
    (hγ.continuousOn_variationOnFromTo_Icc hc)).congr
    fun _ ht ↦ (hγ.ofReal_variationOnFromTo_Icc ht).symm

end PseudoEMetricSpace

section PseudoMetricSpace

variable {α X : Type*} [LinearOrder α] [PseudoMetricSpace X] {γ : α → X} {a b t₁ t₂ : α}

/-- Metric form of `BoundedVariationOn.edist_le_edist_variationOnFromTo_Icc`. -/
theorem _root_.BoundedVariationOn.dist_le_dist_variationOnFromTo_Icc
    (hγ : BoundedVariationOn γ (Icc a b)) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    dist (γ t₁) (γ t₂) ≤
      dist (variationOnFromTo γ (Icc a b) a t₁) (variationOnFromTo γ (Icc a b) a t₂) := by
  rw [dist_edist, dist_edist]
  exact ENNReal.toReal_mono (edist_ne_top _ _) (hγ.edist_le_edist_variationOnFromTo_Icc ht₁ ht₂)

end PseudoMetricSpace

/-! ### Constancy on zero-variation subintervals -/

section EMetricSpace

variable {α X : Type*} [LinearOrder α] [EMetricSpace X] {γ : α → X} {s : Set α}
  {a b x y t₁ t₂ : α}

/-- In an extended metric space, `eVariationOn γ s = 0` if and only if `γ` is constant on `s`,
taking the value `γ x` at any basepoint `x ∈ s`. -/
theorem _root_.eVariationOn.eq_zero_iff_const_on (hx : x ∈ s) :
    eVariationOn γ s = 0 ↔ ∀ t ∈ s, γ t = γ x := by
  rw [eVariationOn.eq_zero_iff]
  refine ⟨fun h t ht ↦ edist_eq_zero.1 (h t ht x hx), fun h u hu v hv ↦ ?_⟩
  rw [h u hu, h v hv, edist_self]

/-- On `Icc a b` (`a ≤ b`), `eVariationOn γ (Icc a b) = 0` iff `γ` is constant on `Icc a b`. -/
theorem eVariationOn_Icc_eq_zero_iff (hab : a ≤ b) :
    eVariationOn γ (Icc a b) = 0 ↔ ∀ t ∈ Icc a b, γ t = γ a :=
  eVariationOn.eq_zero_iff_const_on (left_mem_Icc.2 hab)

/-- For `γ` of locally bounded variation on `s`, `variationOnFromTo γ s x y = 0` (`x, y ∈ s`)
if and only if `γ` is constant on `s ∩ uIcc x y`. -/
theorem _root_.LocallyBoundedVariationOn.variationOnFromTo_eq_zero_iff
    (hγ : LocallyBoundedVariationOn γ s) (hx : x ∈ s) (hy : y ∈ s) :
    variationOnFromTo γ s x y = 0 ↔ ∀ t ∈ s ∩ uIcc x y, γ t = γ x := by
  rw [variationOnFromTo.eq_zero_iff hγ hx hy]
  refine ⟨fun h t ht ↦ edist_eq_zero.1 (h ht ⟨hx, left_mem_uIcc⟩), fun h u hu v hv ↦ ?_⟩
  rw [h u hu, h v hv, edist_self]

/-- For `γ` of locally bounded variation on `s`, cumulative signed variation from `a ∈ s` takes
equal values at `x, y ∈ s` if and only if `γ` is constant on `s ∩ uIcc x y`. -/
theorem _root_.LocallyBoundedVariationOn.variationOnFromTo_eq_iff
    (hγ : LocallyBoundedVariationOn γ s) (ha : a ∈ s) (hx : x ∈ s) (hy : y ∈ s) :
    variationOnFromTo γ s a x = variationOnFromTo γ s a y ↔ ∀ t ∈ s ∩ uIcc x y, γ t = γ x := by
  rw [variationOnFromTo.eq_left_iff hγ ha hx hy, hγ.variationOnFromTo_eq_zero_iff hx hy]

/-- For `γ` of bounded variation on `Icc a b`, cumulative signed variation takes equal values
at `t₁, t₂ ∈ Icc a b` (`t₁ ≤ t₂`) if and only if `γ` is constant on `Icc t₁ t₂`. -/
theorem _root_.BoundedVariationOn.variationOnFromTo_Icc_eq_iff
    (hγ : BoundedVariationOn γ (Icc a b)) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) (ht : t₁ ≤ t₂) :
    variationOnFromTo γ (Icc a b) a t₁ = variationOnFromTo γ (Icc a b) a t₂ ↔
      ∀ t ∈ Icc t₁ t₂, γ t = γ t₁ := by
  rw [hγ.locallyBoundedVariationOn.variationOnFromTo_eq_iff ⟨le_rfl, ht₁.1.trans ht₁.2⟩ ht₁ ht₂,
    uIcc_of_le ht, inter_eq_self_of_subset_right (Icc_subset_Icc ht₁.1 ht₂.2)]

/-- On `Icc a b` (`a ≤ b`), `variationOnFromTo γ (Icc a b) a b = 0` for `γ` of bounded variation
if and only if `γ` is constant on `Icc a b`. -/
theorem _root_.BoundedVariationOn.variationOnFromTo_Icc_eq_zero_iff
    (hγ : BoundedVariationOn γ (Icc a b)) (hab : a ≤ b) :
    variationOnFromTo γ (Icc a b) a b = 0 ↔ ∀ t ∈ Icc a b, γ t = γ a := by
  rw [← variationOnFromTo.self γ (Icc a b) a, eq_comm]
  exact hγ.variationOnFromTo_Icc_eq_iff (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

end EMetricSpace

/-! ### Surjectivity of cumulative arclength on `Icc a b` -/

section SurjOn

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- For a continuous curve `γ : ℝ → X` of bounded variation on `Icc a b` (`a ≤ b`), cumulative
arclength maps `Icc a b` onto `Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem _root_.BoundedVariationOn.surjOn_variationOnFromTo_Icc
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    SurjOn (variationOnFromTo γ (Icc a b) a) (Icc a b)
      (Icc 0 (variationOnFromTo γ (Icc a b) a b)) := by
  change Icc 0 _ ⊆ _
  simpa only [variationOnFromTo.self] using
    intermediate_value_Icc hab (hγ.continuousOn_variationOnFromTo_Icc hc)

/-- For a continuous curve `γ : ℝ → X` of bounded variation on `Icc a b` (`a ≤ b`), the image of
`Icc a b` under cumulative arclength is `Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem _root_.BoundedVariationOn.image_variationOnFromTo_Icc
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    variationOnFromTo γ (Icc a b) a '' Icc a b = Icc 0 (variationOnFromTo γ (Icc a b) a b) :=
  hγ.mapsTo_variationOnFromTo_Icc.image_subset.antisymm (hγ.surjOn_variationOnFromTo_Icc hab hc)

/-- For a continuous curve `γ : ℝ → X` of bounded variation on `Icc a b` (`a ≤ b`), the image of
`Icc a b` under `fun t ↦ eVariationOn γ (Icc a t)` is `Icc 0 (eVariationOn γ (Icc a b))`. -/
theorem _root_.BoundedVariationOn.image_eVariationOn_Icc
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    (fun t ↦ eVariationOn γ (Icc a t)) '' Icc a b = Icc 0 (eVariationOn γ (Icc a b)) := by
  have heq : EqOn (fun t ↦ eVariationOn γ (Icc a t))
      (ENNReal.ofReal ∘ variationOnFromTo γ (Icc a b) a) (Icc a b) :=
    fun t ht ↦ (hγ.ofReal_variationOnFromTo_Icc ht).symm
  rw [image_congr heq, image_comp, hγ.image_variationOnFromTo_Icc hab hc]
  ext x
  simp only [mem_image, mem_Icc, ← hγ.ofReal_variationOnFromTo_Icc (right_mem_Icc.2 hab),
    zero_le, true_and]
  refine ⟨fun ⟨_, ⟨_, hy⟩, h⟩ ↦ h ▸ ENNReal.ofReal_le_ofReal hy, fun hx ↦ ⟨x.toReal,
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal
      (variationOnFromTo.nonneg_of_le γ (Icc a b) hab) hx⟩,
    ENNReal.ofReal_toReal (hx.trans_lt (by simp)).ne⟩⟩

end SurjOn

/-! ### Unit-speed `1`-Lipschitz arclength factorization -/

section Reparam

variable {X : Type*}

section Defs

variable [TopologicalSpace X] [WeakPseudoEMetricSpace X] (γ : ℝ → X) (a b : ℝ)

/-- Generalized right-inverse of `variationOnFromTo γ (Icc a b) a` on `Icc a b`, clamped to `a` on
`(-∞, 0]` and to `b` on `[variationOnFromTo γ (Icc a b) a b, ∞)`. -/
noncomputable def arcLengthInv (s : ℝ) : ℝ :=
  if s ≤ 0 then a
  else if variationOnFromTo γ (Icc a b) a b ≤ s then b
  else Function.invFunOn (variationOnFromTo γ (Icc a b) a) (Icc a b) s

/-- Canonical arclength reparametrization of `γ : ℝ → X` on `Icc a b`, defined on `ℝ` by
composing `γ` with `arcLengthInv γ a b`. -/
noncomputable def arcLengthReparam (s : ℝ) : X := γ (arcLengthInv γ a b s)

variable {γ a b}

/-- Evaluation of `arcLengthReparam` in terms of `arcLengthInv`. -/
theorem arcLengthReparam_apply (s : ℝ) : arcLengthReparam γ a b s = γ (arcLengthInv γ a b s) := by
  rfl

/-- On `(-∞, 0]`, `arcLengthInv γ a b` is clamped to `a`. -/
theorem arcLengthInv_of_nonpos {s : ℝ} (hs : s ≤ 0) : arcLengthInv γ a b s = a := ite_eq_left hs

/-- At `0`, `arcLengthInv γ a b 0 = a`. -/
@[simp]
theorem arcLengthInv_zero : arcLengthInv γ a b 0 = a := arcLengthInv_of_nonpos le_rfl

/-- For `s > 0` with `variationOnFromTo γ (Icc a b) a b ≤ s`, `arcLengthInv γ a b s = b`. -/
theorem arcLengthInv_of_le {s : ℝ} (hs₀ : 0 < s) (hs : variationOnFromTo γ (Icc a b) a b ≤ s) :
    arcLengthInv γ a b s = b := by
  rw [arcLengthInv, ite_eq_right hs₀.not_ge, ite_eq_left hs]

/-- At `0`, `arcLengthReparam γ a b 0 = γ a`. -/
@[simp]
theorem arcLengthReparam_zero : arcLengthReparam γ a b 0 = γ a := by
  rw [arcLengthReparam_apply, arcLengthInv_zero]

end Defs

section PseudoEMetric

variable [PseudoEMetricSpace X] {γ : ℝ → X} {a b s s₁ s₂ t : ℝ}

/-- For a continuous curve of bounded variation on `Icc a b` (`a ≤ b`), `arcLengthInv γ a b` takes
values in `Icc a b` for all `s : ℝ`. -/
theorem arcLengthInv_mem_Icc (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (s : ℝ) : arcLengthInv γ a b s ∈ Icc a b := by
  by_cases hs₀ : s ≤ 0
  · rw [arcLengthInv_of_nonpos hs₀]; exact left_mem_Icc.2 hab
  by_cases hsL : variationOnFromTo γ (Icc a b) a b ≤ s
  · rw [arcLengthInv_of_le (lt_of_not_ge hs₀) hsL]; exact right_mem_Icc.2 hab
  rw [arcLengthInv, ite_eq_right hs₀, ite_eq_right hsL]
  have hs_mem : s ∈ variationOnFromTo γ (Icc a b) a '' Icc a b := by
    rw [hγ.image_variationOnFromTo_Icc hab hc]; exact ⟨le_of_not_ge hs₀, le_of_not_ge hsL⟩
  exact Function.invFunOn_mem hs_mem

/-- Cumulative arclength is a left-inverse to `arcLengthInv γ a b` on
`Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem variationOnFromTo_arcLengthInv_of_mem_Icc (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hs : s ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b)) :
    variationOnFromTo γ (Icc a b) a (arcLengthInv γ a b s) = s := by
  rcases eq_or_lt_of_le hs.1 with rfl | hs₀
  · simp [variationOnFromTo.self]
  rcases eq_or_lt_of_le hs.2 with rfl | hsL
  · rw [arcLengthInv_of_le hs₀ le_rfl]
  rw [arcLengthInv, ite_eq_right hs₀.not_ge, ite_eq_right hsL.not_ge]
  have hs_mem : s ∈ variationOnFromTo γ (Icc a b) a '' Icc a b := by
    rw [hγ.image_variationOnFromTo_Icc hab hc]; exact hs
  exact Function.invFunOn_eq hs_mem

/-- For any `s : ℝ`, `variationOnFromTo γ (Icc a b) a (arcLengthInv γ a b s)` is `s` clamped to
`Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem variationOnFromTo_arcLengthInv (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (s : ℝ) :
    variationOnFromTo γ (Icc a b) a (arcLengthInv γ a b s) =
      max 0 (min (variationOnFromTo γ (Icc a b) a b) s) := by
  have hL := variationOnFromTo.nonneg_of_le γ (Icc a b) hab
  by_cases hs₀ : s ≤ 0
  · rw [arcLengthInv_of_nonpos hs₀, variationOnFromTo.self,
      min_eq_right (hs₀.trans hL), max_eq_left hs₀]
  by_cases hsL : variationOnFromTo γ (Icc a b) a b ≤ s
  · rw [arcLengthInv_of_le (lt_of_not_ge hs₀) hsL, min_eq_left hsL, max_eq_right hL]
  have hs : s ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b) := ⟨le_of_not_ge hs₀, le_of_not_ge hsL⟩
  rw [variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc hs, min_eq_right hs.2, max_eq_right hs.1]

/-- `arcLengthInv γ a b` is strictly increasing on `Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem strictMonoOn_arcLengthInv (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    StrictMonoOn (arcLengthInv γ a b) (Icc 0 (variationOnFromTo γ (Icc a b) a b)) := by
  intro s₁ hs₁ s₂ hs₂ hlt
  by_contra! hge
  have hle := variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn (left_mem_Icc.2 hab)
    (arcLengthInv_mem_Icc hab hγ hc s₂) (arcLengthInv_mem_Icc hab hγ hc s₁) hge
  rw [variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc hs₁,
    variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc hs₂] at hle
  exact hlt.not_ge hle

/-- `arcLengthInv γ a b` is globally monotone on `ℝ`. -/
theorem monotone_arcLengthInv (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) : Monotone (arcLengthInv γ a b) := by
  intro s₁ s₂ hle
  by_cases hs₁ : s₁ ≤ 0
  · rw [arcLengthInv_of_nonpos hs₁]; exact (arcLengthInv_mem_Icc hab hγ hc s₂).1
  by_cases hs₂ : variationOnFromTo γ (Icc a b) a b ≤ s₂
  · rw [arcLengthInv_of_le ((lt_of_not_ge hs₁).trans_le hle) hs₂]
    exact (arcLengthInv_mem_Icc hab hγ hc s₁).2
  exact (strictMonoOn_arcLengthInv hab hγ hc).monotoneOn
    ⟨le_of_not_ge hs₁, hle.trans (le_of_not_ge hs₂)⟩
    ⟨(le_of_not_ge hs₁).trans hle, le_of_not_ge hs₂⟩ hle

/-- `arcLengthInv γ a b` maps `Ico 0 (variationOnFromTo γ (Icc a b) a b)` into `Ico a b`. -/
theorem mapsTo_arcLengthInv_Ico (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    MapsTo (arcLengthInv γ a b) (Ico 0 (variationOnFromTo γ (Icc a b) a b)) (Ico a b) := by
  intro s hs
  have hmem := arcLengthInv_mem_Icc hab hγ hc s
  refine ⟨hmem.1, hmem.2.lt_of_ne fun heq ↦ hs.2.ne ?_⟩
  simpa [heq] using (variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc
    (Ico_subset_Icc_self hs)).symm

/-- In a pseudo-extended metric space, `arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a t)`
is at zero extended distance from `γ t` for all `t ∈ Icc a b`. -/
theorem edist_arcLengthReparam_variationOnFromTo_eq_zero (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (ht : t ∈ Icc a b) :
    edist (arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a t)) (γ t) = 0 := by
  rw [arcLengthReparam_apply, ← nonpos_iff_eq_zero]
  refine (hγ.edist_le_edist_variationOnFromTo_Icc
    (arcLengthInv_mem_Icc hab hγ hc _) ht).trans_eq ?_
  rw [variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc
    (hγ.mapsTo_variationOnFromTo_Icc ht), edist_self]

/-- The arclength reparametrization `arcLengthReparam γ a b` is globally `1`-Lipschitz on `ℝ`. -/
theorem lipschitzWith_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) : LipschitzWith 1 (arcLengthReparam γ a b) := by
  intro s₁ s₂
  rw [ENNReal.coe_one, one_mul, arcLengthReparam_apply, arcLengthReparam_apply]
  refine (hγ.edist_le_edist_variationOnFromTo_Icc
    (arcLengthInv_mem_Icc hab hγ hc s₁) (arcLengthInv_mem_Icc hab hγ hc s₂)).trans ?_
  rw [variationOnFromTo_arcLengthInv hab hγ hc s₁, variationOnFromTo_arcLengthInv hab hγ hc s₂,
    edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (by grind)

/-- The arclength reparametrization `arcLengthReparam γ a b` is `1`-Lipschitz on
`Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem lipschitzOnWith_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    LipschitzOnWith 1 (arcLengthReparam γ a b) (Icc 0 (variationOnFromTo γ (Icc a b) a b)) :=
  (lipschitzWith_arcLengthReparam hab hγ hc).lipschitzOnWith

/-- `arcLengthReparam γ a b` is continuous on `ℝ`. -/
theorem continuous_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) : Continuous (arcLengthReparam γ a b) :=
  (lipschitzWith_arcLengthReparam hab hγ hc).continuous

/-- `arcLengthReparam γ a b` is continuous on `Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem continuousOn_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    ContinuousOn (arcLengthReparam γ a b) (Icc 0 (variationOnFromTo γ (Icc a b) a b)) :=
  (continuous_arcLengthReparam hab hγ hc).continuousOn

/-- Pointwise zero-edist congruence for `eVariationOn`. -/
private theorem eVariationOn_congr_edist_zero {α : Type*} [LinearOrder α] {f g : α → X}
    {s : Set α} (h : ∀ x ∈ s, edist (f x) (g x) = 0) : eVariationOn f s = eVariationOn g s := by
  have hle {f g : α → X} (h : ∀ x ∈ s, edist (f x) (g x) = 0) {x y} (hx : x ∈ s) (hy : y ∈ s) :
      edist (f x) (f y) ≤ edist (g x) (g y) := by
    simpa [h x hx, edist_comm (g y), h y hy] using edist_triangle4 (f x) (g x) (g y) (f y)
  simp only [eVariationOn]
  congr! 3 with ⟨n, u, hu, hus⟩ i hi
  exact le_antisymm (hle h (hus _) (hus _))
    (hle (fun z hz ↦ by rw [edist_comm, h z hz]) (hus _) (hus _))

/-- Unit-speed variation property of `arcLengthReparam γ a b` on subintervals of
`Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem eVariationOn_arcLengthReparam_Icc (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hs₁ : s₁ ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b))
    (hs₂ : s₂ ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b)) :
    eVariationOn (arcLengthReparam γ a b) (Icc s₁ s₂) = ENNReal.ofReal (s₂ - s₁) := by
  rcases le_or_gt s₁ s₂ with hle | hgt
  · let V := variationOnFromTo γ (Icc a b) a
    let t₁ := arcLengthInv γ a b s₁
    let t₂ := arcLengthInv γ a b s₂
    have ht₁ := arcLengthInv_mem_Icc hab hγ hc s₁
    have ht₂ := arcLengthInv_mem_Icc hab hγ hc s₂
    have ht := monotone_arcLengthInv hab hγ hc hle
    have hsub : Icc t₁ t₂ ⊆ Icc a b := Icc_subset_Icc ht₁.1 ht₂.2
    have hV₁ : V t₁ = s₁ := variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc hs₁
    have hV₂ : V t₂ = s₂ := variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc hs₂
    have hV_mono : MonotoneOn V (Icc t₁ t₂) :=
      (variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn (left_mem_Icc.2 hab)).mono hsub
    have himg : V '' Icc t₁ t₂ = Icc s₁ s₂ := by
      refine subset_antisymm ?_ (hV₁ ▸ hV₂ ▸
        intermediate_value_Icc ht ((hγ.continuousOn_variationOnFromTo_Icc hc).mono hsub))
      rintro _ ⟨t, ht', rfl⟩
      exact ⟨hV₁ ▸ hV_mono (left_mem_Icc.2 ht) ht' ht'.1,
        hV₂ ▸ hV_mono ht' (right_mem_Icc.2 ht) ht'.2⟩
    rw [← himg, ← eVariationOn.comp_eq_of_monotoneOn (arcLengthReparam γ a b) V hV_mono,
      eVariationOn_congr_edist_zero (f := arcLengthReparam γ a b ∘ V) fun t ht' ↦
        edist_arcLengthReparam_variationOnFromTo_eq_zero hab hγ hc (hsub ht'),
      ← hγ.ofReal_variationOnFromTo_Icc_sub ht₁ ht₂ ht,
      variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc hs₂,
      variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc hs₁]
  · rw [Icc_eq_empty hgt.not_ge, eVariationOn.subsingleton _ subsingleton_empty,
      ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 hgt.le)]

/-- For `s ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b)`, the cumulative variation of
`arcLengthReparam γ a b` on `Icc 0 s` equals `ENNReal.ofReal s`. -/
theorem eVariationOn_arcLengthReparam_Icc_zero (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hs : s ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b)) :
    eVariationOn (arcLengthReparam γ a b) (Icc 0 s) = ENNReal.ofReal s := by
  simpa using eVariationOn_arcLengthReparam_Icc hab hγ hc
    (left_mem_Icc.2 (variationOnFromTo.nonneg_of_le γ (Icc a b) hab)) hs

/-- The total variation of `arcLengthReparam γ a b` on its length interval equals
`eVariationOn γ (Icc a b)`. -/
theorem eVariationOn_arcLengthReparam_Icc_self (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    eVariationOn (arcLengthReparam γ a b) (Icc 0 (variationOnFromTo γ (Icc a b) a b)) =
      eVariationOn γ (Icc a b) := by
  rw [eVariationOn_arcLengthReparam_Icc_zero hab hγ hc
    (right_mem_Icc.2 (variationOnFromTo.nonneg_of_le γ (Icc a b) hab)),
    hγ.ofReal_variationOnFromTo_Icc (right_mem_Icc.2 hab)]

/-- `arcLengthReparam γ a b` has bounded variation on its length interval
`Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem boundedVariationOn_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    BoundedVariationOn (arcLengthReparam γ a b) (Icc 0 (variationOnFromTo γ (Icc a b) a b)) := by
  rw [BoundedVariationOn, eVariationOn_arcLengthReparam_Icc_self hab hγ hc]; exact hγ

/-- For `s₁, s₂ ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b)`, the signed variation of
`arcLengthReparam γ a b` between `s₁` and `s₂` is `s₂ - s₁`. -/
theorem variationOnFromTo_arcLengthReparam (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hs₁ : s₁ ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b))
    (hs₂ : s₂ ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b)) :
    variationOnFromTo (arcLengthReparam γ a b)
        (Icc 0 (variationOnFromTo γ (Icc a b) a b)) s₁ s₂ = s₂ - s₁ := by
  rcases le_total s₁ s₂ with hle | hge
  · rw [variationOnFromTo.eq_of_le _ _ hle,
      inter_eq_self_of_subset_right (Icc_subset_Icc hs₁.1 hs₂.2),
      eVariationOn_arcLengthReparam_Icc hab hγ hc hs₁ hs₂,
      ENNReal.toReal_ofReal (sub_nonneg.2 hle)]
  · rw [variationOnFromTo.eq_of_ge _ _ hge,
      inter_eq_self_of_subset_right (Icc_subset_Icc hs₂.1 hs₁.2),
      eVariationOn_arcLengthReparam_Icc hab hγ hc hs₂ hs₁,
      ENNReal.toReal_ofReal (sub_nonneg.2 hge), neg_sub]

/-- For `s ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b)`, cumulative signed variation of
`arcLengthReparam γ a b` from `0` to `s` is `s`. -/
theorem variationOnFromTo_arcLengthReparam_zero (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hs : s ∈ Icc 0 (variationOnFromTo γ (Icc a b) a b)) :
    variationOnFromTo (arcLengthReparam γ a b)
        (Icc 0 (variationOnFromTo γ (Icc a b) a b)) 0 s = s := by
  simpa using variationOnFromTo_arcLengthReparam hab hγ hc
    (left_mem_Icc.2 (variationOnFromTo.nonneg_of_le γ (Icc a b) hab)) hs

end PseudoEMetric

section PseudoMetric

variable [PseudoMetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- In a pseudometric space, `arcLengthReparam γ a b` is `1`-Lipschitz in metric distance. -/
theorem dist_arcLengthReparam_le (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (s₁ s₂ : ℝ) :
    dist (arcLengthReparam γ a b s₁) (arcLengthReparam γ a b s₂) ≤ dist s₁ s₂ := by
  rw [dist_edist, dist_edist]
  exact ENNReal.toReal_mono (edist_ne_top _ _)
    (by simpa using lipschitzWith_arcLengthReparam hab hγ hc s₁ s₂)

end PseudoMetric

section EMetric

variable [EMetricSpace X] {γ : ℝ → X} {a b t : ℝ}

/-- Factorization of a continuous rectifiable curve through its unit-speed arclength
reparametrization: `arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a t) = γ t`. -/
theorem arcLengthReparam_variationOnFromTo (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (ht : t ∈ Icc a b) :
    arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a t) = γ t :=
  edist_eq_zero.1 (edist_arcLengthReparam_variationOnFromTo_eq_zero hab hγ hc ht)

/-- At `variationOnFromTo γ (Icc a b) a b`, `arcLengthReparam γ a b` takes the value `γ b`. -/
theorem arcLengthReparam_variationOnFromTo_right (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a b) = γ b :=
  arcLengthReparam_variationOnFromTo hab hγ hc (right_mem_Icc.2 hab)

/-- The trace of `arcLengthReparam γ a b` on `Icc 0 (variationOnFromTo γ (Icc a b) a b)` equals
the trace of `γ` on `Icc a b`. -/
theorem image_arcLengthReparam_Icc (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    arcLengthReparam γ a b '' Icc 0 (variationOnFromTo γ (Icc a b) a b) = γ '' Icc a b := by
  rw [← hγ.image_variationOnFromTo_Icc hab hc, ← image_comp]
  exact image_congr fun _ ht ↦ arcLengthReparam_variationOnFromTo hab hγ hc ht

/-- Zero-length case: if `variationOnFromTo γ (Icc a b) a b = 0`, then `arcLengthReparam γ a b` is
the constant curve at `γ a`. -/
theorem arcLengthReparam_eq_const_of_variationOnFromTo_eq_zero (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (h0 : variationOnFromTo γ (Icc a b) a b = 0) : arcLengthReparam γ a b = fun _ ↦ γ a := by
  ext s
  exact (hγ.variationOnFromTo_Icc_eq_zero_iff hab).1 h0
    (arcLengthInv γ a b s) (arcLengthInv_mem_Icc hab hγ hc s)

/-- Zero-length case: if `eVariationOn γ (Icc a b) = 0`, then `arcLengthReparam γ a b` is the
constant curve at `γ a`. -/
theorem arcLengthReparam_eq_const_of_eVariationOn_eq_zero (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (h0 : eVariationOn γ (Icc a b) = 0) :
    arcLengthReparam γ a b = fun _ ↦ γ a := by
  have hγ : BoundedVariationOn γ (Icc a b) := by simp [BoundedVariationOn, h0]
  apply arcLengthReparam_eq_const_of_variationOnFromTo_eq_zero hab hγ hc
  rw [variationOnFromTo_Icc_self_right hab, h0, ENNReal.toReal_zero]

/-! ### Injective arcs and simple closed curves -/

/-- If `γ` has bounded variation on `Icc a b` and is injective on `Ioo a b`, then cumulative signed
variation `variationOnFromTo γ (Icc a b) a` is strictly increasing on `Icc a b`. -/
theorem _root_.BoundedVariationOn.strictMonoOn_variationOnFromTo_of_injOn_Ioo
    (hγ : BoundedVariationOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) :
    StrictMonoOn (variationOnFromTo γ (Icc a b) a) (Icc a b) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have hle := variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn
    ⟨le_rfl, ht₁.1.trans ht₁.2⟩ ht₁ ht₂ hlt.le
  refine hle.lt_of_ne fun heq ↦ ?_
  have hconst := (hγ.variationOnFromTo_Icc_eq_iff ht₁ ht₂ hlt.le).1 heq
  have h1 : (2 * t₁ + t₂) / 3 ∈ Ioo a b := ⟨by linarith [ht₁.1], by linarith [ht₂.2]⟩
  have h2 : (t₁ + 2 * t₂) / 3 ∈ Ioo a b := ⟨by linarith [ht₁.1], by linarith [ht₂.2]⟩
  have hγu : γ ((2 * t₁ + t₂) / 3) = γ ((t₁ + 2 * t₂) / 3) :=
    (hconst _ ⟨by linarith, by linarith⟩).trans (hconst _ ⟨by linarith, by linarith⟩).symm
  linarith [hinj h1 h2 hγu]

/-- If `γ` has bounded variation on `Icc a b` and is injective on `Ico a b` (in particular for
simple closed curves), then cumulative signed variation is strictly increasing on `Icc a b`. -/
theorem _root_.BoundedVariationOn.strictMonoOn_variationOnFromTo_of_injOn_Ico
    (hγ : BoundedVariationOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    StrictMonoOn (variationOnFromTo γ (Icc a b) a) (Icc a b) :=
  hγ.strictMonoOn_variationOnFromTo_of_injOn_Ioo (hinj.mono Ioo_subset_Ico_self)

/-- If `γ` has bounded variation on `Icc a b` and is injective on `Icc a b`, then cumulative
signed variation is strictly increasing on `Icc a b`. -/
theorem _root_.BoundedVariationOn.strictMonoOn_variationOnFromTo_of_injOn
    (hγ : BoundedVariationOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    StrictMonoOn (variationOnFromTo γ (Icc a b) a) (Icc a b) :=
  hγ.strictMonoOn_variationOnFromTo_of_injOn_Ioo (hinj.mono Ioo_subset_Icc_self)

/-- If `γ` has bounded variation on `Icc a b` and is injective on `Icc a b`, then cumulative
extended variation `fun t ↦ eVariationOn γ (Icc a t)` is strictly increasing on `Icc a b`. -/
theorem _root_.BoundedVariationOn.strictMonoOn_eVariationOn_Icc_of_injOn
    (hγ : BoundedVariationOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    StrictMonoOn (fun t ↦ eVariationOn γ (Icc a t)) (Icc a b) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  dsimp only
  rw [← hγ.ofReal_variationOnFromTo_Icc ht₁, ← hγ.ofReal_variationOnFromTo_Icc ht₂]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (variationOnFromTo.nonneg_of_le γ (Icc a b) ht₁.1)).2
    (hγ.strictMonoOn_variationOnFromTo_of_injOn hinj ht₁ ht₂ hlt)

/-- When `InjOn γ (Ioo a b)`, `arcLengthInv γ a b` is a left-inverse to cumulative arclength on
`Icc a b`. -/
theorem arcLengthInv_variationOnFromTo (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) (ht : t ∈ Icc a b) :
    arcLengthInv γ a b (variationOnFromTo γ (Icc a b) a t) = t :=
  (hγ.strictMonoOn_variationOnFromTo_of_injOn_Ioo hinj).injOn
    (arcLengthInv_mem_Icc hab hγ hc _) ht
    (variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc (hγ.mapsTo_variationOnFromTo_Icc ht))

/-- Order isomorphism `Icc a b ≃o Icc 0 (variationOnFromTo γ (Icc a b) a b)` given by cumulative
arclength when `InjOn γ (Ioo a b)`. -/
noncomputable def arcLengthOrderIso (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) :
    Icc a b ≃o Icc 0 (variationOnFromTo γ (Icc a b) a b) where
  toFun t := ⟨variationOnFromTo γ (Icc a b) a t.1, hγ.mapsTo_variationOnFromTo_Icc t.2⟩
  invFun s := ⟨arcLengthInv γ a b s.1, arcLengthInv_mem_Icc hab hγ hc s.1⟩
  left_inv t := Subtype.ext (arcLengthInv_variationOnFromTo hab hγ hc hinj t.2)
  right_inv s := Subtype.ext (variationOnFromTo_arcLengthInv_of_mem_Icc hab hγ hc s.2)
  map_rel_iff' {t₁ t₂} :=
    (hγ.strictMonoOn_variationOnFromTo_of_injOn_Ioo hinj).le_iff_le t₁.2 t₂.2

/-- Underlying value of `arcLengthOrderIso`. -/
@[simp]
theorem coe_arcLengthOrderIso_apply (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) (t : Icc a b) :
    (arcLengthOrderIso hab hγ hc hinj t : ℝ) = variationOnFromTo γ (Icc a b) a t := by rfl

/-- Underlying value of `(arcLengthOrderIso hab hγ hc hinj).symm`. -/
@[simp]
theorem coe_arcLengthOrderIso_symm_apply (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b))
    (s : Icc 0 (variationOnFromTo γ (Icc a b) a b)) :
    ((arcLengthOrderIso hab hγ hc hinj).symm s : ℝ) = arcLengthInv γ a b s := by rfl

/-- Homeomorphism `Icc a b ≃ₜ Icc 0 (variationOnFromTo γ (Icc a b) a b)` given by cumulative
arclength when `InjOn γ (Ioo a b)`. -/
noncomputable def arcLengthHomeomorph (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) :
    Icc a b ≃ₜ Icc 0 (variationOnFromTo γ (Icc a b) a b) :=
  (arcLengthOrderIso hab hγ hc hinj).toHomeomorph

/-- Underlying value of `arcLengthHomeomorph`. -/
@[simp]
theorem coe_arcLengthHomeomorph_apply (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) (t : Icc a b) :
    (arcLengthHomeomorph hab hγ hc hinj t : ℝ) = variationOnFromTo γ (Icc a b) a t := by rfl

/-- Underlying value of `(arcLengthHomeomorph hab hγ hc hinj).symm`. -/
@[simp]
theorem coe_arcLengthHomeomorph_symm_apply (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b))
    (s : Icc 0 (variationOnFromTo γ (Icc a b) a b)) :
    ((arcLengthHomeomorph hab hγ hc hinj).symm s : ℝ) = arcLengthInv γ a b s := by rfl

/-- When `InjOn γ (Ioo a b)`, `arcLengthInv γ a b` is continuous on
`Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem continuousOn_arcLengthInv (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) :
    ContinuousOn (arcLengthInv γ a b) (Icc 0 (variationOnFromTo γ (Icc a b) a b)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp (arcLengthHomeomorph hab hγ hc hinj).symm.continuous

/-- For an injective rectifiable arc (`InjOn γ (Icc a b)`), `arcLengthReparam γ a b` is injective
on `Icc 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem injOn_arcLengthReparam_Icc (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    InjOn (arcLengthReparam γ a b) (Icc 0 (variationOnFromTo γ (Icc a b) a b)) :=
  hinj.comp (strictMonoOn_arcLengthInv hab hγ hc).injOn
    fun s _ ↦ arcLengthInv_mem_Icc hab hγ hc s

/-- For a curve injective on `Ico a b` (in particular a simple closed curve with `γ a = γ b`),
`arcLengthReparam γ a b` is injective on `Ico 0 (variationOnFromTo γ (Icc a b) a b)`. -/
theorem injOn_arcLengthReparam_Ico (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b)) :
    InjOn (arcLengthReparam γ a b) (Ico 0 (variationOnFromTo γ (Icc a b) a b)) :=
  hinj.comp ((strictMonoOn_arcLengthInv hab hγ hc).injOn.mono Ico_subset_Icc_self)
    (mapsTo_arcLengthInv_Ico hab hγ hc)

/-- For a closed curve (`γ a = γ b`), the arclength reparametrization is also closed on its
length interval:
`arcLengthReparam γ a b 0 = arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a b)`. -/
theorem arcLengthReparam_closed (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) :
    arcLengthReparam γ a b 0 = arcLengthReparam γ a b (variationOnFromTo γ (Icc a b) a b) := by
  rw [arcLengthReparam_zero, arcLengthReparam_variationOnFromTo_right hab hγ hc, hclosed]

end EMetric

end Reparam

end TauCeti
