/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Geometry.Lie.IntegralCurve
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.CompactSupport
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.VectorField.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Complete vector fields, naturality of flows, and time-dependent flows

A vector field `v` on a manifold `M` is complete (`TauCeti.IsCompleteVectorField v`) when its
maximal-flow domain `flowDomain v` is all of `ℝ × M`, equivalently when every maximal integral
curve interval `maximalIntegralCurveInterval v x` equals `univ`. On a separated boundaryless `C¹`
Banach manifold, a `C¹` vector field is complete whenever each trajectory stays in a compact set,
in particular when `v` vanishes outside a compact set or when `M` is compact.

In finite dimensions, the maximal flow of a complete `C¹` vector field packages as a dynamical
`Flow ℝ M` (`TauCeti.toFlow`) whose time-`t` maps are `C^n` diffeomorphisms (`toFlowDiffeomorph`)
when `v` is `C^n`. Left-invariant vector fields on real Lie groups modeled on complete spaces are
complete and flow via `mulInvariantIntegralCurve`. Constant fields on normed spaces flow by
translation, and the planar rotation field `(-y, x)` on `ℝ × ℝ` flows by rotation.

For `f`-related `C¹` vector fields along `f : M → N`, `f` maps `flowDomain v` into `flowDomain w`
and intertwines `flowOf v` with `flowOf w` (`TauCeti.flowOf_comp_of_related`). Finally, a
time-dependent `C¹` field `v : ℝ → (x : M) → TangentSpace I x` induces an autonomous suspension
`(1, v)` on `ℝ × M` whose spatial projection defines the nonautonomous flow `timeDependentFlowOf v`
and proves `exists_timeDependentFlow`.

## Main declarations

* `TauCeti.IsCompleteVectorField`, `TauCeti.isCompleteVectorField_of_isCompact`,
  `TauCeti.exists_isMIntegralCurve_of_compactSpace`, `TauCeti.isCompleteVectorField_of_compactSpace`
* `TauCeti.toFlow`, `TauCeti.toFlow_apply`, `TauCeti.toFlowDiffeomorph`
* `TauCeti.flowOf_mulInvariantVectorField`, `TauCeti.flowOf_const`,
  `TauCeti.flowOf_rotationVectorField`
* `TauCeti.flowOf_comp_of_related`, `TauCeti.timeDependentFlowOf`,
  `TauCeti.exists_timeDependentFlow`

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 9.
-/

public section

noncomputable section

open Bundle Function Manifold Set VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti

/-! ### Complete vector fields and global integral curves -/

section Complete

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {v : (x : M) → TangentSpace I x}

/-- The time-slice `{t | (t, x) ∈ flowDomain v}` of the maximal-flow domain at `x` is open. -/
theorem isOpen_flowDomain_slice (x : M) : IsOpen {t | (t, x) ∈ flowDomain v} := by
  simp only [mem_flowDomain]
  exact isOpen_maximalIntegralCurveInterval

/-- A vector field is complete when its maximal flow is defined for all times and initial points. -/
def IsCompleteVectorField (v : (x : M) → TangentSpace I x) : Prop :=
  flowDomain v = univ

/-- Unfolding lemma for `IsCompleteVectorField`. -/
theorem isCompleteVectorField_def : IsCompleteVectorField v ↔ flowDomain v = univ :=
  Iff.rfl

/-- Every pair `(t, x)` belongs to the flow domain of a complete vector field. -/
theorem IsCompleteVectorField.mem_flowDomain (hc : IsCompleteVectorField v) (t : ℝ) (x : M) :
    (t, x) ∈ flowDomain v := by
  rw [isCompleteVectorField_def.mp hc]
  exact mem_univ (t, x)

/-- Every maximal integral curve interval of a complete vector field is all of `ℝ`. -/
theorem IsCompleteVectorField.maximalIntegralCurveInterval_eq_univ
    (hc : IsCompleteVectorField v) (x : M) :
    maximalIntegralCurveInterval v x = univ :=
  eq_univ_of_forall fun t ↦ TauCeti.mem_flowDomain.mp (hc.mem_flowDomain t x)

/-- At time `0`, the maximal flow of a complete vector field is the identity. -/
theorem IsCompleteVectorField.flowOf_zero (hc : IsCompleteVectorField v) (x : M) :
    flowOf v 0 x = x := by
  rw [flowOf_apply, maximalIntegralCurve_zero (TauCeti.mem_flowDomain.mp (hc.mem_flowDomain 0 x))]

/-- A vector field is complete if and only if every maximal integral curve interval is `univ`. -/
theorem isCompleteVectorField_iff_forall_maximalIntegralCurveInterval_eq_univ :
    IsCompleteVectorField v ↔ ∀ x, maximalIntegralCurveInterval v x = univ := by
  refine ⟨fun hc x ↦ hc.maximalIntegralCurveInterval_eq_univ x, fun h ↦ ?_⟩
  ext ⟨t, x⟩
  simp [h x]

/-- A vector field is complete if and only if `maximalIntegralCurveFlowDomain v = univ`. -/
theorem isCompleteVectorField_iff_maximalIntegralCurveFlowDomain_eq_univ :
    IsCompleteVectorField v ↔ maximalIntegralCurveFlowDomain v = univ := by
  rw [isCompleteVectorField_iff_forall_maximalIntegralCurveInterval_eq_univ]
  refine ⟨maximalIntegralCurveFlowDomain_eq_univ, fun h x ↦ eq_univ_of_forall fun t ↦ ?_⟩
  have hmem : (x, t) ∈ maximalIntegralCurveFlowDomain v := h ▸ mem_univ (x, t)
  exact mem_maximalIntegralCurveFlowDomain.mp hmem

/-- A global integral curve of `v` puts every time `t` into `flowDomain v` at its initial point. -/
theorem mem_flowDomain_of_isMIntegralCurve {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    (t, γ 0) ∈ flowDomain v := by
  rw [mem_flowDomain]
  have habs := abs_nonneg t
  exact (hγ.isMIntegralCurveOn (Ioo (-(|t| + 1)) (|t| + 1))).subset_maximalIntegralCurveInterval
    ⟨by linarith, by linarith⟩ rfl ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

/-- If every point is the initial value of a global integral curve of `v`, then `v` is complete. -/
theorem isCompleteVectorField_of_forall_isMIntegralCurve
    (h : ∀ x, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) :
    IsCompleteVectorField v := by
  refine eq_univ_of_forall fun ⟨t, x⟩ ↦ ?_
  obtain ⟨γ, rfl, hγ⟩ := h x
  exact mem_flowDomain_of_isMIntegralCurve hγ t

variable [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]

/-- Every global integral curve of a `C¹` vector field `v` is an orbit of `flowOf v`. -/
theorem flowOf_eq_of_isMIntegralCurve
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    flowOf v t (γ 0) = γ t := by
  rw [flowOf_apply]
  have habs := abs_nonneg t
  exact (hγ.isMIntegralCurveOn (Ioo (-(|t| + 1)) (|t| + 1))).eqOn_maximalIntegralCurve hv
    ⟨by linarith, by linarith⟩ rfl ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

/-- A global integral curve of a `C¹` vector field `v` with `γ 0 = x` agrees with `flowOf v · x`. -/
theorem flowOf_eq_of_isMIntegralCurve_of_eq
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {γ : ℝ → M} {x : M}
    (hγ : IsMIntegralCurve γ v) (h0 : γ 0 = x) (t : ℝ) :
    flowOf v t x = γ t := by
  rw [← h0, flowOf_eq_of_isMIntegralCurve hv hγ t]

/-- For a complete `C¹` vector field, every trajectory `t ↦ flowOf v t x` is a global integral
curve. -/
theorem IsCompleteVectorField.isMIntegralCurve_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (x : M) :
    IsMIntegralCurve (fun t ↦ flowOf v t x) v := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn]
  have hdom : {t | (t, x) ∈ flowDomain v} = univ := eq_univ_of_forall fun t ↦ hc.mem_flowDomain t x
  rw [← hdom]
  exact isMIntegralCurveOn_flowOf hv x

/-- A `C¹` vector field is complete if and only if through every point there is a global integral
curve. -/
theorem isCompleteVectorField_iff_forall_exists_isMIntegralCurve
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    IsCompleteVectorField v ↔ ∀ x, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  rw [isCompleteVectorField_iff_forall_maximalIntegralCurveInterval_eq_univ]
  exact forall_congr' fun _ ↦ maximalIntegralCurveInterval_eq_univ_iff hv

/-- For a complete `C¹` vector field, the flow group law holds unconditionally for all times. -/
theorem IsCompleteVectorField.flowOf_add
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (s t : ℝ) (x : M) :
    flowOf v t (flowOf v s x) = flowOf v (s + t) x :=
  (TauCeti.flowOf_add hv (hc.mem_flowDomain s x) (hc.mem_flowDomain t (flowOf v s x))).2

/-- Flowing by `t` and then by `-t` along a complete `C¹` vector field returns to `x`. -/
theorem IsCompleteVectorField.flowOf_neg_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) (x : M) :
    flowOf v (-t) (flowOf v t x) = x := by
  rw [hc.flowOf_add hv t (-t) x, add_neg_cancel, hc.flowOf_zero x]

/-- Flowing by `-t` and then by `t` along a complete `C¹` vector field returns to `x`. -/
theorem IsCompleteVectorField.flowOf_flowOf_neg
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) (x : M) :
    flowOf v t (flowOf v (-t) x) = x := by
  rw [hc.flowOf_add hv (-t) t x, neg_add_cancel, hc.flowOf_zero x]

/-- The time-`t` bijection of a complete `C¹` vector field, with inverse `flowOf v (-t)`. -/
def IsCompleteVectorField.flowOfEquiv
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) : M ≃ M where
  toFun := flowOf v t
  invFun := flowOf v (-t)
  left_inv := hc.flowOf_neg_flowOf hv t
  right_inv := hc.flowOf_flowOf_neg hv t

@[simp]
theorem IsCompleteVectorField.flowOfEquiv_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) (x : M) :
    hc.flowOfEquiv hv t x = flowOf v t x :=
  (rfl)

@[simp]
theorem IsCompleteVectorField.flowOfEquiv_symm_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) (x : M) :
    (hc.flowOfEquiv hv t).symm x = flowOf v (-t) x :=
  (rfl)

/-- For a complete `C¹` vector field, every time-`t` map `flowOf v t` is bijective. -/
theorem IsCompleteVectorField.bijective_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) :
    Bijective (flowOf v t) :=
  (hc.flowOfEquiv hv t).bijective

/-- If every trajectory of a `C¹` vector field stays in some compact set, then the field is
complete. -/
theorem isCompleteVectorField_of_isCompact_of_mapsTo [CompleteSpace E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {K : M → Set M} (hK : ∀ x, IsCompact (K x))
    (hmaps : ∀ x, MapsTo (fun t ↦ flowOf v t x) {t | (t, x) ∈ flowDomain v} (K x)) :
    IsCompleteVectorField v := by
  rw [isCompleteVectorField_iff_forall_maximalIntegralCurveInterval_eq_univ]
  intro x
  refine maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
    (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt) (hK x) fun t ht ↦ ?_
  simpa only [flowOf_apply] using hmaps x (mem_flowDomain.mpr ht)

/-- Compactly supported `C¹` vector fields on boundaryless Banach manifolds are complete. -/
theorem isCompleteVectorField_of_isCompact [CompleteSpace E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {K : Set M}
    (hK : IsCompact K) (hvK : ∀ x ∉ K, v x = 0) : IsCompleteVectorField v := by
  rw [isCompleteVectorField_iff_forall_maximalIntegralCurveInterval_eq_univ]
  exact fun _ ↦ maximalIntegralCurveInterval_eq_univ_of_isCompact_of_eq_zero_off hv hK hvK

/-- Every `C¹` vector field on a compact boundaryless manifold admits a global integral curve
through every point. -/
theorem exists_isMIntegralCurve_of_compactSpace [CompleteSpace E] [CompactSpace M]
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ∃ γ : ℝ → M, γ 0 = x₀ ∧ IsMIntegralCurve γ v :=
  ⟨maximalIntegralCurve v x₀,
    maximalIntegralCurve_zero (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt),
    isMIntegralCurve_maximalIntegralCurve hv⟩

/-- Every `C¹` vector field on a compact boundaryless manifold is complete. -/
theorem isCompleteVectorField_of_compactSpace [CompleteSpace E] [CompactSpace M]
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    IsCompleteVectorField v := by
  rw [isCompleteVectorField_iff_forall_maximalIntegralCurveInterval_eq_univ]
  exact fun _ ↦ maximalIntegralCurveInterval_eq_univ_of_compactSpace hv

/-! ### Packaging complete flows as `Flow ℝ M` and diffeomorphisms -/

variable [FiniteDimensional ℝ E]

/-- In finite dimensions, the flow of a complete `C¹` vector field packaged as a `Flow ℝ M`. -/
def toFlow (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) : Flow ℝ M :=
  globalFlow v hv hc.maximalIntegralCurveInterval_eq_univ

/-- Evaluating `toFlow` at time `t` and initial point `x` gives `flowOf v t x`. -/
@[simp]
theorem toFlow_apply (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) (x : M) :
    toFlow hv hc t x = flowOf v t x := by
  rw [toFlow, globalFlow_apply, flowOf_apply]

/-- Every orbit of `toFlow` is a global integral curve of `v`. -/
theorem isMIntegralCurve_toFlow (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (x : M) :
    IsMIntegralCurve (fun t ↦ toFlow hv hc t x) v :=
  isMIntegralCurve_globalFlow hv hc.maximalIntegralCurveInterval_eq_univ x

/-- Every global integral curve of `v` is an orbit of `toFlow`. -/
theorem toFlow_eq_of_isMIntegralCurve (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    toFlow hv hc t (γ 0) = γ t :=
  globalFlow_eq_of_isMIntegralCurve hv hc.maximalIntegralCurveInterval_eq_univ hγ t

/-- In finite dimensions, `toFlow` of a complete `C^n` vector field (`1 ≤ n`) is jointly `C^n` in
time and space. -/
theorem contMDiff_toFlow_uncurry {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I n
      (fun p : ℝ × M ↦ toFlow (hvn.of_le (by exact_mod_cast hn)) hc p.1 p.2) :=
  contMDiff_globalFlow_uncurry hc.maximalIntegralCurveInterval_eq_univ hn hvn

/-- In finite dimensions, each time-`t` map of `toFlow` for a complete `C^n` vector field (`1 ≤ n`)
is `C^n`. -/
theorem contMDiff_toFlow_apply {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) :
    ContMDiff I I n (toFlow (hvn.of_le (by exact_mod_cast hn)) hc t) :=
  contMDiff_globalFlow_apply hc.maximalIntegralCurveInterval_eq_univ hn hvn t

/-- The time-`t` map of a complete `C^n` vector field (`1 ≤ n`) in finite dimensions, packaged as a
`C^n` diffeomorphism of `M`. -/
def toFlowDiffeomorph {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) :
    M ≃ₘ^n⟮I, I⟯ M :=
  globalFlowDiffeomorph hc.maximalIntegralCurveInterval_eq_univ hn hvn t

@[simp]
theorem toFlowDiffeomorph_apply {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) (x : M) :
    toFlowDiffeomorph hn hvn hc t x = flowOf v t x := by
  rw [toFlowDiffeomorph, globalFlowDiffeomorph_apply, globalFlow_apply, flowOf_apply]

@[simp]
theorem toFlowDiffeomorph_symm_apply {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField v) (t : ℝ) (x : M) :
    (toFlowDiffeomorph hn hvn hc t).symm x = flowOf v (-t) x := by
  rw [toFlowDiffeomorph, globalFlowDiffeomorph_symm_apply, globalFlow_apply, flowOf_apply]

end Complete

/-! ### Lie-group invariant flows and explicit model-space flows -/

section LieAndModelFlows

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

section LieGroup

variable [CompleteSpace E] {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
  [Group G] [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
  [BoundarylessManifold I G] (v : GroupLieAlgebra I G)

/-- Left-invariant vector fields on real Lie groups modeled on complete spaces are complete. -/
theorem isCompleteVectorField_mulInvariantVectorField :
    IsCompleteVectorField (mulInvariantVectorField v) :=
  isCompleteVectorField_of_forall_isMIntegralCurve
    (exists_isMIntegralCurve_mulInvariantVectorField v)

/-- The maximal flow of a left-invariant vector field on a Lie group agrees with
`mulInvariantIntegralCurve`. -/
theorem flowOf_mulInvariantVectorField (t : ℝ) (g : G) :
    flowOf (mulInvariantVectorField v) t g = mulInvariantIntegralCurve v g t := by
  have hV : CMDiff 1 (fun x ↦ (⟨x, mulInvariantVectorField v x⟩ : TangentBundle I G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by simp)
  exact flowOf_eq_of_isMIntegralCurve_of_eq hV (isMIntegralCurve_mulInvariantIntegralCurve v g)
    (mulInvariantIntegralCurve_zero v g) t

/-- At the identity element of a Lie group, the flow of a left-invariant vector field evaluates the
associated one-parameter subgroup. -/
theorem flowOf_mulInvariantVectorField_one (t : ℝ) :
    flowOf (mulInvariantVectorField v) t (1 : G) =
      mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd t) := by
  rw [flowOf_mulInvariantVectorField, mulInvariantOneParameterSubgroup_apply]

/-- The flow of a left-invariant vector field is left translation of its trajectory through `1`. -/
theorem flowOf_mulInvariantVectorField_eq_mul_one (t : ℝ) (g : G) :
    flowOf (mulInvariantVectorField v) t g = g * flowOf (mulInvariantVectorField v) t 1 := by
  rw [flowOf_mulInvariantVectorField, flowOf_mulInvariantVectorField,
    congrFun (mulInvariantIntegralCurve_eq_const_mul v g) t]

end LieGroup

/-- A curve in a normed space satisfying `HasDerivAt γ (v (γ t)) t` everywhere is a global manifold
integral curve over `𝓘(ℝ, E)`. -/
theorem isMIntegralCurve_of_hasDerivAt {γ : ℝ → E} {v : (x : E) → TangentSpace 𝓘(ℝ, E) x}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) γ v := by
  intro t
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  exact (hγ t).hasFDerivAt.hasMFDerivAt

/-- A constant tangent-space section on a normed model space `E` is smooth of any order. -/
theorem contMDiff_const_modelSpace {n : ℕ∞ω} (c : E) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent n
      (fun x : E ↦ (⟨x, (show TangentSpace 𝓘(ℝ, E) x from c)⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
  (contMDiff_vectorSpace_iff_contDiff
    (V := fun x : E ↦ (show TangentSpace 𝓘(ℝ, E) x from c))).2 contDiff_const

/-- The affine line `t ↦ x + t • c` is a global integral curve of the constant vector field `c`. -/
theorem isMIntegralCurve_add_smul_const (c x : E) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (fun t : ℝ ↦ x + t • c)
      (fun y : E ↦ (show TangentSpace 𝓘(ℝ, E) y from c)) :=
  isMIntegralCurve_of_hasDerivAt fun t ↦ by
    simpa using ((hasDerivAt_id t).smul_const c).const_add x

/-- Every constant vector field on a normed space is complete. -/
theorem isCompleteVectorField_const (c : E) :
    IsCompleteVectorField (I := 𝓘(ℝ, E)) (fun y : E ↦ (show TangentSpace 𝓘(ℝ, E) y from c)) :=
  isCompleteVectorField_of_forall_isMIntegralCurve fun x ↦
    ⟨fun t ↦ x + t • c, by simp, isMIntegralCurve_add_smul_const c x⟩

/-- The maximal flow of a constant vector field `c` on a normed space acts by translation. -/
@[simp]
theorem flowOf_const (c : E) (t : ℝ) (x : E) :
    flowOf (I := 𝓘(ℝ, E)) (fun y : E ↦ (show TangentSpace 𝓘(ℝ, E) y from c)) t x =
      x + t • c :=
  flowOf_eq_of_isMIntegralCurve_of_eq (contMDiff_const_modelSpace c)
    (isMIntegralCurve_add_smul_const c x) (by simp) t

/-- The planar rotation vector field `(-y, x)` on `ℝ × ℝ`. -/
def rotationVectorField (p : ℝ × ℝ) : TangentSpace 𝓘(ℝ, ℝ × ℝ) p :=
  (-p.2, p.1)

/-- The planar rotation trajectory through `p = (x, y)` at angle `t`. -/
def rotationCurve (p : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (Real.cos t * p.1 - Real.sin t * p.2, Real.sin t * p.1 + Real.cos t * p.2)

@[simp]
theorem rotationCurve_zero (p : ℝ × ℝ) : rotationCurve p 0 = p := by
  ext <;> simp [rotationCurve]

/-- The planar rotation trajectories satisfy the angle-addition group law. -/
theorem rotationCurve_add (p : ℝ × ℝ) (s t : ℝ) :
    rotationCurve (rotationCurve p s) t = rotationCurve p (s + t) := by
  ext <;> simp only [rotationCurve, Real.cos_add, Real.sin_add] <;> ring

/-- The planar rotation vector field is smooth of any order. -/
theorem contMDiff_rotationVectorField {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent n
      (fun p : ℝ × ℝ ↦ (⟨p, rotationVectorField p⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
  (contMDiff_vectorSpace_iff_contDiff (V := rotationVectorField)).2
    (contDiff_snd.neg.prodMk contDiff_fst)

/-- For every initial point `p : ℝ × ℝ`, `rotationCurve p` is a global integral curve of
`rotationVectorField`. -/
theorem isMIntegralCurve_rotationCurve (p : ℝ × ℝ) :
    IsMIntegralCurve (I := 𝓘(ℝ, ℝ × ℝ)) (rotationCurve p) rotationVectorField := by
  refine isMIntegralCurve_of_hasDerivAt fun t ↦ HasDerivAt.prodMk ?_ ?_
  · convert ((Real.hasDerivAt_cos t).mul_const p.1).sub
      ((Real.hasDerivAt_sin t).mul_const p.2) using 1
    simp only [rotationCurve]
    ring
  · convert ((Real.hasDerivAt_sin t).mul_const p.1).add
      ((Real.hasDerivAt_cos t).mul_const p.2) using 1
    simp only [rotationCurve]
    ring

/-- The planar rotation vector field on `ℝ × ℝ` is complete. -/
theorem isCompleteVectorField_rotationVectorField :
    IsCompleteVectorField (I := 𝓘(ℝ, ℝ × ℝ)) rotationVectorField :=
  isCompleteVectorField_of_forall_isMIntegralCurve fun p ↦
    ⟨rotationCurve p, rotationCurve_zero p, isMIntegralCurve_rotationCurve p⟩

/-- The maximal flow of the planar rotation vector field `(-y, x)` on `ℝ × ℝ` is planar rotation. -/
theorem flowOf_rotationVectorField (t : ℝ) (p : ℝ × ℝ) :
    flowOf (I := 𝓘(ℝ, ℝ × ℝ)) rotationVectorField t p = rotationCurve p t :=
  flowOf_eq_of_isMIntegralCurve_of_eq contMDiff_rotationVectorField
    (isMIntegralCurve_rotationCurve p) (rotationCurve_zero p) t

end LieAndModelFlows

/-! ### Naturality of flows for related vector fields -/

section Naturality

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]
  {v : (x : M) → TangentSpace I x} {w : (y : N) → TangentSpace J y} {f : M → N}

/-- If `v` and `w` are `f`-related along a differentiable map `f : M → N`, then
`(t, x) ∈ flowDomain v` implies `(t, f x) ∈ flowDomain w`. -/
theorem mem_flowDomain_of_related (hf : MDiff f) (hrel : ∀ x, mfderiv I J f x (v x) = w (f x))
    {t : ℝ} {x : M} (ht : (t, x) ∈ flowDomain v) :
    (t, f x) ∈ flowDomain w := by
  obtain ⟨γ, a, b, hγ, hγ0, h0, htab, -⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq (mem_flowDomain.mp ht)
  have hfγ : IsMIntegralCurveOn (f ∘ γ) w (Ioo a b) :=
    hγ.map_of_mfderiv_eq (fun s _ ↦ hf (γ s)) (fun s _ ↦ hrel (γ s))
  exact mem_flowDomain.mpr (hfγ.subset_maximalIntegralCurveInterval h0 (congrArg f hγ0) htab)

/-- If a complete vector field `v` is `f`-related to `w` along a surjective differentiable map `f`,
then `w` is also complete. -/
theorem IsCompleteVectorField.of_related_surjective (hc : IsCompleteVectorField v)
    (hf : MDiff f) (hsurj : Surjective f) (hrel : ∀ x, mfderiv I J f x (v x) = w (f x)) :
    IsCompleteVectorField w := by
  refine eq_univ_of_forall fun ⟨t, y⟩ ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj y
  exact mem_flowDomain_of_related hf hrel (hc.mem_flowDomain t x)

variable [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
  [T2Space N] [BoundarylessManifold J N] [IsManifold J 1 N]

/-- If `v` and `w` are `f`-related `C¹` vector fields along a `C¹` map `f : M → N`, then `f` sends
the maximal-flow domain of `v` into that of `w` and intertwines their maximal flows. -/
theorem flowOf_comp_of_related
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle J N)))
    (hf : CMDiff 1 f) (hrel : ∀ x, mfderiv I J f x (v x) = w (f x))
    {t : ℝ} {x : M} (ht : (t, x) ∈ flowDomain v) :
    (t, f x) ∈ flowDomain w ∧ f (flowOf v t x) = flowOf w t (f x) := by
  obtain ⟨γ, a, b, hγ, hγ0, h0, htab, -⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq (mem_flowDomain.mp ht)
  have hfγ : IsMIntegralCurveOn (f ∘ γ) w (Ioo a b) :=
    hγ.map_of_mfderiv_eq (fun s _ ↦ (hf.mdifferentiable one_ne_zero) (γ s))
      (fun s _ ↦ hrel (γ s))
  have hf0 : (f ∘ γ) 0 = f x := congrArg f hγ0
  refine ⟨mem_flowDomain.mpr (hfγ.subset_maximalIntegralCurveInterval h0 hf0 htab), ?_⟩
  rw [flowOf_apply, flowOf_apply, hγ.eqOn_maximalIntegralCurve hv h0 hγ0 htab,
    hfγ.eqOn_maximalIntegralCurve hw h0 hf0 htab]
  rfl

/-- If `v` is complete and `f`-related to `w`, then `f` semiconjugates `flowOf v` to `flowOf w` for
all times and initial points. -/
theorem IsCompleteVectorField.flowOf_comp_of_related
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle J N)))
    (hc : IsCompleteVectorField v) (hf : CMDiff 1 f)
    (hrel : ∀ x, mfderiv I J f x (v x) = w (f x)) (t : ℝ) (x : M) :
    f (flowOf v t x) = flowOf w t (f x) :=
  (TauCeti.flowOf_comp_of_related hv hw hf hrel (hc.mem_flowDomain t x)).2

/-- In finite dimensions, `f`-related complete `C¹` vector fields have `f`-semiconjugate `Flow`s. -/
theorem toFlow_comp_of_related [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle J N)))
    (hcv : IsCompleteVectorField v) (hcw : IsCompleteVectorField w)
    (hf : CMDiff 1 f) (hrel : ∀ x, mfderiv I J f x (v x) = w (f x))
    (t : ℝ) (x : M) :
    f (toFlow hv hcv t x) = toFlow hw hcw t (f x) := by
  simp only [toFlow_apply]
  exact hcv.flowOf_comp_of_related hv hw hf hrel t x

end Naturality

/-! ### Time-dependent vector fields and nonautonomous flows -/

section TimeDependent

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {v : ℝ → (x : M) → TangentSpace I x}

/-- The autonomous suspension vector field `(1, v(t, x))` on `ℝ × M` associated with a
time-dependent vector field `v` on `M`. -/
def timeDependentSuspension (v : ℝ → (x : M) → TangentSpace I x)
    (p : ℝ × M) : TangentSpace (𝓘(ℝ, ℝ).prod I) p :=
  (show TangentSpace 𝓘(ℝ, ℝ) p.1 from (1 : ℝ), v p.1 p.2)

/-- If a time-dependent vector field `v` is jointly `C^n` on `ℝ × M`, then its autonomous
suspension field `(1, v)` is `C^n` on `ℝ × M`. -/
theorem contMDiff_timeDependentSuspension {n : ℕ∞ω} [IsManifold I 1 M]
    (hv : CMDiff n (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M))) :
    CMDiff n (fun p : ℝ × M ↦
      (⟨p, timeDependentSuspension v p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
  (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I) (M' := M)
    (n := n)).comp (((contMDiff_const_modelSpace (1 : ℝ)).comp contMDiff_fst).prodMk hv)

/-- The domain of the two-parameter nonautonomous flow of `v`: triples `(t, t₀, x)` such that the
autonomous suspension flow starting at `(t₀, x)` is defined at elapsed time `t - t₀`. -/
def timeDependentFlowDomain (v : ℝ → (x : M) → TangentSpace I x) : Set (ℝ × ℝ × M) :=
  {q | (q.1 - q.2.1, q.2) ∈ flowDomain (timeDependentSuspension v)}

@[simp]
theorem mem_timeDependentFlowDomain {t : ℝ} {p : ℝ × M} :
    (t, p) ∈ timeDependentFlowDomain v ↔
      (t - p.1, p) ∈ flowDomain (timeDependentSuspension v) :=
  Iff.rfl

/-- The two-parameter nonautonomous flow `Ψ(t, (t₀, x))` of a time-dependent vector field `v`,
defined by projecting the autonomous suspension flow on `ℝ × M` at elapsed time `t - t₀`. -/
def timeDependentFlowOf (v : ℝ → (x : M) → TangentSpace I x) (t : ℝ) (p : ℝ × M) : M :=
  (flowOf (timeDependentSuspension v) (t - p.1) p).2

@[simp]
theorem timeDependentFlowOf_apply (v : ℝ → (x : M) → TangentSpace I x) (t : ℝ) (p : ℝ × M) :
    timeDependentFlowOf v t p = (flowOf (timeDependentSuspension v) (t - p.1) p).2 :=
  (rfl)

variable [BoundarylessManifold I M] [IsManifold I 1 M]

/-- For every initial pair `p = (t₀, x₀)`, the initial time `t₀` belongs to the domain of the
nonautonomous flow starting at `p`. -/
theorem mem_timeDependentFlowDomain_self [CompleteSpace E]
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M))) (p : ℝ × M) :
    (p.1, p) ∈ timeDependentFlowDomain v := by
  rw [mem_timeDependentFlowDomain, sub_self]
  exact mem_flowDomain_zero (contMDiff_timeDependentSuspension hv) p

/-- At the initial time `p.1`, the nonautonomous flow `timeDependentFlowOf v` takes the initial
value `p.2`. -/
theorem timeDependentFlowOf_self [CompleteSpace E]
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M))) (p : ℝ × M) :
    timeDependentFlowOf v p.1 p = p.2 := by
  rw [timeDependentFlowOf_apply, sub_self, flowOf_zero (contMDiff_timeDependentSuspension hv) p]

variable [T2Space M]

/-- The time coordinate of the autonomous suspension flow advances linearly:
`(flowOf (timeDependentSuspension v) r p).1 = p.1 + r`. -/
theorem flowOf_timeDependentSuspension_fst
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M)))
    {r : ℝ} {p : ℝ × M} (hr : (r, p) ∈ flowDomain (timeDependentSuspension v)) :
    (flowOf (timeDependentSuspension v) r p).1 = p.1 + r := by
  have hrel : ∀ q : ℝ × M,
      mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) Prod.fst q (timeDependentSuspension v q) =
        (show TangentSpace 𝓘(ℝ, ℝ) q.1 from (1 : ℝ)) := by
    intro q
    rw [(hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) q).mfderiv]
    rfl
  have hcomp := (flowOf_comp_of_related (contMDiff_timeDependentSuspension hv)
    (contMDiff_const_modelSpace (1 : ℝ)) contMDiff_fst hrel hr).2
  simpa only [flowOf_const, smul_eq_mul, mul_one] using hcomp

/-- On `timeDependentFlowDomain v`, the autonomous suspension flow at elapsed time `t - p.1` is
`(t, timeDependentFlowOf v t p)`. -/
theorem flowOf_timeDependentSuspension_eq_mk
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M)))
    {t : ℝ} {p : ℝ × M} (ht : (t, p) ∈ timeDependentFlowDomain v) :
    flowOf (timeDependentSuspension v) (t - p.1) p = (t, timeDependentFlowOf v t p) := by
  ext
  · rw [flowOf_timeDependentSuspension_fst hv (mem_timeDependentFlowDomain.mp ht), add_sub_cancel]
  · rfl

/-- The two-parameter nonautonomous cocycle law: flowing from `(t₀, x)` to time `s` and then from
`s` to time `t` agrees with flowing directly from `(t₀, x)` to time `t`. -/
theorem timeDependentFlowOf_trans
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M)))
    {s t : ℝ} {p : ℝ × M} (hs : (s, p) ∈ timeDependentFlowDomain v)
    (ht : (t, (s, timeDependentFlowOf v s p)) ∈ timeDependentFlowDomain v) :
    (t, p) ∈ timeDependentFlowDomain v ∧
      timeDependentFlowOf v t (s, timeDependentFlowOf v s p) = timeDependentFlowOf v t p := by
  have hs' : (s - p.1, p) ∈ flowDomain (timeDependentSuspension v) :=
    mem_timeDependentFlowDomain.mp hs
  have ht' : (t - s, flowOf (timeDependentSuspension v) (s - p.1) p) ∈
      flowDomain (timeDependentSuspension v) := by
    rw [flowOf_timeDependentSuspension_eq_mk hv hs]
    exact mem_timeDependentFlowDomain.mp ht
  have hadd := flowOf_add (contMDiff_timeDependentSuspension hv) hs' ht'
  have hsum : s - p.1 + (t - s) = t - p.1 := by ring
  rw [hsum, flowOf_timeDependentSuspension_eq_mk hv hs] at hadd
  exact ⟨mem_timeDependentFlowDomain.mpr hadd.1, congrArg Prod.snd hadd.2⟩

/-- The spatial projection of the autonomous suspension flow satisfies the nonautonomous
differential equation at elapsed time `r`. -/
theorem hasMFDerivAt_flowOf_timeDependentSuspension_snd
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M)))
    {r : ℝ} {p : ℝ × M} (hr : (r, p) ∈ flowDomain (timeDependentSuspension v)) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ (flowOf (timeDependentSuspension v) u p).2) r
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (v (p.1 + r) (flowOf (timeDependentSuspension v) r p).2)) := by
  have hcurve := isMIntegralCurveOn_flowOf (contMDiff_timeDependentSuspension hv) p r hr
  have hopen := isOpen_flowDomain_slice (v := timeDependentSuspension v) p
  have hmfd := hcurve.hasMFDerivAt (hopen.mem_nhds hr)
  have hcomp := (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I)
    (flowOf (timeDependentSuspension v) r p)).comp r hmfd
  have hfst : (flowOf (timeDependentSuspension v) r p).1 = p.1 + r :=
    flowOf_timeDependentSuspension_fst hv hr
  refine hcomp.congr_mfderiv (ContinuousLinearMap.ext fun c ↦ ?_)
  change ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (v (flowOf (timeDependentSuspension v) r p).1 (flowOf (timeDependentSuspension v) r p).2) c =
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (v (p.1 + r) (flowOf (timeDependentSuspension v) r p).2) c
  rw [hfst]

/-- At every `(t, p) ∈ timeDependentFlowDomain v`, the trajectory `s ↦ timeDependentFlowOf v s p`
has manifold derivative `v t (timeDependentFlowOf v t p)` at `t`. -/
theorem hasMFDerivAt_timeDependentFlowOf
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M)))
    {t : ℝ} {p : ℝ × M} (ht : (t, p) ∈ timeDependentFlowDomain v) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ timeDependentFlowOf v s p) t
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v t (timeDependentFlowOf v t p))) := by
  have hsub : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ s - p.1) t
      (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t)) :=
    ((hasFDerivAt_id t).sub_const p.1).hasMFDerivAt
  have hsnd := hasMFDerivAt_flowOf_timeDependentSuspension_snd hv
    (mem_timeDependentFlowDomain.mp ht)
  have hcomp := hsnd.comp t hsub
  refine hcomp.congr_mfderiv (ContinuousLinearMap.ext fun c ↦ ?_)
  change ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (v (p.1 + (t - p.1)) (timeDependentFlowOf v t p)) c =
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v t (timeDependentFlowOf v t p)) c
  rw [add_sub_cancel]

/-- For every initial condition `p = (t₀, x₀)`, the trajectory `s ↦ timeDependentFlowOf v s p`
solves the nonautonomous ODE on a neighborhood of `p.1`. -/
theorem eventually_hasMFDerivAt_timeDependentFlowOf [CompleteSpace E]
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M))) (p : ℝ × M) :
    ∀ᶠ t in 𝓝 p.1, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ timeDependentFlowOf v s p) t
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v t (timeDependentFlowOf v t p))) := by
  have hopen : IsOpen {t : ℝ | (t, p) ∈ timeDependentFlowDomain v} :=
    (isOpen_flowDomain_slice (v := timeDependentSuspension v) p).preimage (continuous_sub_right p.1)
  filter_upwards [hopen.mem_nhds (mem_timeDependentFlowDomain_self hv p)] with t ht
  exact hasMFDerivAt_timeDependentFlowOf hv ht

/-- In finite dimensions, `timeDependentFlowDomain v` is jointly open in `(t, t₀, x)`. -/
theorem isOpen_timeDependentFlowDomain [FiniteDimensional ℝ E]
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M))) :
    IsOpen (timeDependentFlowDomain v) :=
  (isOpen_flowDomain (contMDiff_timeDependentSuspension hv)).preimage
    ((continuous_fst.sub (continuous_fst.comp continuous_snd)).prodMk continuous_snd)

/-- In finite dimensions, the two-parameter nonautonomous flow of a `C^n` time-dependent vector
field (`1 ≤ n`) is jointly `C^n` on `timeDependentFlowDomain v`. -/
theorem contMDiffOn_timeDependentFlowOf [FiniteDimensional ℝ E] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M]
    (hv : CMDiff n (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) I n
      (fun q : ℝ × ℝ × M ↦ timeDependentFlowOf v q.1 q.2) (timeDependentFlowDomain v) := by
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) n
      (fun q : ℝ × ℝ × M ↦ (q.1 - q.2.1, q.2)) :=
    (contMDiff_fst.sub (contMDiff_fst.comp contMDiff_snd)).prodMk contMDiff_snd
  exact contMDiff_snd.comp_contMDiffOn
    ((contMDiffOn_flowOf hn (contMDiff_timeDependentSuspension hv)).comp hmap.contMDiffOn
      fun _ hq ↦ hq)

/-- Existence of a local nonautonomous flow around `(t₀, x₀)` for a `C¹` time-dependent vector
field `v` on a boundaryless Banach manifold. -/
theorem exists_timeDependentFlow [CompleteSpace E]
    (hv : CMDiff 1 (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M))) (t₀ : ℝ) (x₀ : M) :
    ∃ (U : Set (ℝ × M)) (Ψ : ℝ → ℝ × M → M), IsOpen U ∧ (t₀, x₀) ∈ U ∧
      (∀ p ∈ U, Ψ p.1 p = p.2) ∧
      ∀ p ∈ U, ∀ᶠ t in 𝓝 p.1, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ Ψ s p) t
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v t (Ψ t p))) :=
  ⟨univ, timeDependentFlowOf v, isOpen_univ, mem_univ (t₀, x₀),
    fun p _ ↦ timeDependentFlowOf_self hv p,
    fun p _ ↦ eventually_hasMFDerivAt_timeDependentFlowOf hv p⟩

end TimeDependent

end TauCeti
