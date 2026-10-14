/-
Copyright (c) 2026 General Intelligence, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Covering.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth Structure of a Covering Space

Given a covering map `p : X → M` onto a charted space `M` modelled on `H`, this file constructs
the induced charted space structure `IsCoveringMap.inducedChartedSpace H hp` on the total space `X`
by lifting the charts of `M` through the local homeomorphism slices of `p`. Because a topological
space `X` may admit multiple inequivalent covering maps to `M`, this constructor is marked
`@[instance_reducible]` rather than registered as a global instance.

When `M` is a `C^n` manifold modelled on `I : ModelWithCorners 𝕜 E H`, we prove that:
* the induced charted space structure makes `X` a `C^n` manifold
  (`IsCoveringMap.induced_isManifold`);
* the covering projection `p` is a `C^n` local diffeomorphism
  (`IsCoveringMap.induced_isLocalDiffeomorph`);
* the induced `C^n` structure is unique: any `C^n` manifold structure on `X` for which `p` is a
  `C^n` local diffeomorphism is `C^n`-compatible with the induced atlas
  (`IsCoveringMap.induced_unique`);
* a continuous map `f : N → X` is `C^n` if and only if its projection `p ∘ f : N → M` is `C^n`
  (`ContMDiff.of_comp_isCoveringMap`).

## Main definitions and results

* `IsCoveringMap.inducedChartedSpace`: the charted space structure on `X` induced by `hp`.
* `IsCoveringMap.inducedChartedSpace_chartAt`: on its source, the induced chart at `x` equals
  `chartAt H (p x) ∘ p`.
* `IsCoveringMap.induced_isManifold`: the induced charted space on `X` is a `C^n` manifold.
* `IsCoveringMap.induced_isLocalDiffeomorph`: `p` is a `C^n` local diffeomorphism for the induced
  manifold structure on `X`.
* `IsCoveringMap.induced_unique`: atlas compatibility of any `C^n` manifold structure on `X` making
  `p` a `C^n` local diffeomorphism with the induced atlas.
* `ContMDiff.of_comp_isCoveringMap`: smoothness of continuous lifts through a covering map.
-/

open Set Filter Topology Function
open scoped Manifold

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {X : Type*} [TopologicalSpace X] {n : WithTop ℕ∞}

namespace IsCoveringMap

variable (H) in
/-- The local chart on `X` at `x` induced by a covering map `p : X → M`, obtained by composing the
local homeomorphism slice of `p` at `x` with `chartAt H (p x)`. -/
def inducedChartAt {p : X → M} (hp : IsCoveringMap p) (x : X) : OpenPartialHomeomorph X H :=
  (hp.isLocalHomeomorph.localInverseAt x).symm.trans (chartAt H (p x))

@[simp]
theorem inducedChartAt_apply {p : X → M} (hp : IsCoveringMap p) (x y : X) :
    hp.inducedChartAt H x y = chartAt H (p x) (p y) := by
  simp [inducedChartAt, hp.isLocalHomeomorph.localInverseAt_symm]

theorem inducedChartAt_source {p : X → M} (hp : IsCoveringMap p) (x : X) :
    (hp.inducedChartAt H x).source =
      (hp.isLocalHomeomorph.localInverseAt x).target ∩ p ⁻¹' (chartAt H (p x)).source := by
  simp [inducedChartAt, hp.isLocalHomeomorph.localInverseAt_symm]

theorem mem_inducedChartAt_source {p : X → M} (hp : IsCoveringMap p) (x : X) :
    x ∈ (hp.inducedChartAt H x).source := by
  rw [inducedChartAt_source]
  exact ⟨hp.isLocalHomeomorph.self_mem_localInverseAt_target, mem_chart_source H (p x)⟩

theorem inducedChartAt_target {p : X → M} (hp : IsCoveringMap p) (x : X) :
    (hp.inducedChartAt H x).target =
      (chartAt H (p x)).target ∩
        (chartAt H (p x)).symm ⁻¹' (hp.isLocalHomeomorph.localInverseAt x).source := by
  simp [inducedChartAt]

theorem inducedChartAt_symm_apply {p : X → M} (hp : IsCoveringMap p) (x : X) (z : H) :
    (hp.inducedChartAt H x).symm z =
      hp.isLocalHomeomorph.localInverseAt x ((chartAt H (p x)).symm z) :=
  rfl

theorem p_inducedChartAt_symm {p : X → M} (hp : IsCoveringMap p) {x : X} {z : H}
    (hz : z ∈ (hp.inducedChartAt H x).target) :
    p ((hp.inducedChartAt H x).symm z) = (chartAt H (p x)).symm z := by
  rw [inducedChartAt_target] at hz
  exact hp.isLocalHomeomorph.apply_localInverseAt_of_mem hz.2

variable (H) in
/-- The charted structure on the total space `X` of a covering map `p : X → M`, obtained by lifting
the charts of `M` along the local homeomorphism branches of `p`. Marked `@[instance_reducible]`
because `X` may admit distinct covering maps; activate locally via `letI` or `haveI` when needed. -/
@[instance_reducible]
noncomputable def inducedChartedSpace {p : X → M} (hp : IsCoveringMap p) :
    ChartedSpace H X where
  atlas := range (hp.inducedChartAt H)
  chartAt := hp.inducedChartAt H
  mem_chart_source := hp.mem_inducedChartAt_source
  chart_mem_atlas x := mem_range_self x

theorem chartAt_eq_inducedChartAt {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] (hc : c = IsCoveringMap.inducedChartedSpace H hp) (x : X) :
    @chartAt H _ X _ c x = hp.inducedChartAt H x := by
  subst hc
  rfl

/-- The induced chart at `x` reads a point through the chart of `M` at `p x` after `p`: on its
source, `chartAt H x` agrees with `chartAt H (p x) ∘ p`. -/
theorem inducedChartedSpace_chartAt {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] (hc : c = IsCoveringMap.inducedChartedSpace H hp) (x : X) :
    EqOn (chartAt H x) (chartAt H (p x) ∘ p) (chartAt H x).source := by
  subst hc
  intro y _
  exact hp.inducedChartAt_apply x y

theorem inducedChartedSpace_chartAt_apply {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] (hc : c = IsCoveringMap.inducedChartedSpace H hp) (x y : X) :
    chartAt H x y = chartAt H (p x) (p y) := by
  subst hc
  exact hp.inducedChartAt_apply x y

theorem inducedChartedSpace_extChartAt_apply {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] (hc : c = IsCoveringMap.inducedChartedSpace H hp) (x y : X) :
    extChartAt I x y = extChartAt I (p x) (p y) := by
  simp [extChartAt, hp.inducedChartedSpace_chartAt_apply hc]

/-- Any transition map between two induced charts of `X` is a restriction of the corresponding
transition map on the base manifold `M`, hence belongs to `contDiffGroupoid n I`. -/
theorem inducedChartAt_symm_trans_mem_contDiffGroupoid [IsManifold I n M]
    {p : X → M} (hp : IsCoveringMap p) (x x' : X) :
    (hp.inducedChartAt H x).symm ≫ₕ hp.inducedChartAt H x' ∈ contDiffGroupoid n I := by
  set e := hp.inducedChartAt H x
  set e' := hp.inducedChartAt H x'
  set B := (chartAt H (p x)).symm ≫ₕ chartAt H (p x')
  have hB : B ∈ contDiffGroupoid n I :=
    (contDiffGroupoid n I).compatible (chart_mem_atlas H (p x)) (chart_mem_atlas H (p x'))
  have hsub : (e.symm ≫ₕ e').source ⊆ B.source := by
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz ⊢
    rcases hz with ⟨hz1, hz2⟩
    have h1 : z ∈ (chartAt H (p x)).target := by
      rw [e.symm_source, hp.inducedChartAt_target] at hz1
      exact hz1.1
    have h2 : (chartAt H (p x)).symm z ∈ (chartAt H (p x')).source := by
      rw [hp.inducedChartAt_source] at hz2
      rw [← hp.p_inducedChartAt_symm (by simpa [e] using hz1)]
      exact hz2.2
    exact ⟨h1, h2⟩
  have hrestr : B.restr (e.symm ≫ₕ e').source ∈ contDiffGroupoid n I :=
    closedUnderRestriction' hB (e.symm ≫ₕ e').open_source
  refine (contDiffGroupoid n I).mem_of_eqOnSource hrestr ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.restr_source,
      (e.symm ≫ₕ e').open_source.interior_eq, inter_eq_right.mpr hsub]
  · intro z hz
    have hz1 : z ∈ e.target := hz.1
    simp only [OpenPartialHomeomorph.restr_apply, OpenPartialHomeomorph.trans_apply, B, e, e',
      hp.inducedChartAt_apply, hp.p_inducedChartAt_symm hz1]

/-- The charted space structure on `X` induced by a covering map `p : X → M` onto a `C^n` manifold
`M` makes `X` a `C^n` manifold. -/
theorem induced_isManifold [IsManifold I n M] {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] (hc : c = IsCoveringMap.inducedChartedSpace H hp) :
    IsManifold I n X := by
  subst hc
  let _ : ChartedSpace H X := IsCoveringMap.inducedChartedSpace H hp
  have : HasGroupoid X (contDiffGroupoid n I) := ⟨by
    rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
    exact hp.inducedChartAt_symm_trans_mem_contDiffGroupoid x x'⟩
  exact IsManifold.mk' (I := I) (n := n) (M := X)

/-- With the manifold structure induced by a covering map `p : X → M`, the projection `p` is a
`C^n` local diffeomorphism. -/
theorem induced_isLocalDiffeomorph [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X]
    (hc : c = IsCoveringMap.inducedChartedSpace H hp) :
    IsLocalDiffeomorph I I n p := by
  have : IsManifold I n X := hp.induced_isManifold hc
  intro x
  let φ : PartialDiffeomorph I I X M n :=
    { (chartAt H x).trans (chartAt H (p x)).symm with
      contMDiffOn_toFun := by
        have hchart : ContMDiffOn I I n (chartAt H x) (chartAt H x).source := contMDiffOn_chart
        have hsymm : ContMDiffOn I I n (chartAt H (p x)).symm (chartAt H (p x)).target :=
          contMDiffOn_chart_symm
        exact hsymm.comp (hchart.mono inter_subset_left) inter_subset_right
      contMDiffOn_invFun := by
        have hchart : ContMDiffOn I I n (chartAt H (p x)) (chartAt H (p x)).source :=
          contMDiffOn_chart
        have hsymm : ContMDiffOn I I n (chartAt H x).symm (chartAt H x).target :=
          contMDiffOn_chart_symm
        change ContMDiffOn I I n ((chartAt H x).symm ∘ chartAt H (p x))
          ((chartAt H x ≫ₕ (chartAt H (p x)).symm).target)
        exact hsymm.comp (hchart.mono inter_subset_left) inter_subset_right }
  have hxφ : x ∈ φ.source := by
    refine ⟨mem_chart_source H x, ?_⟩
    change chartAt H x x ∈ (chartAt H (p x)).target
    rw [hp.inducedChartedSpace_chartAt_apply hc]
    exact mem_chart_target H (p x)
  have heq : EqOn p φ φ.source := by
    intro y hy
    have hy_src : y ∈ (chartAt H x).source := hy.1
    have hpy_src : p y ∈ (chartAt H (p x)).source := by
      subst hc
      exact (hp.inducedChartAt_source (H := H) x ▸ hy_src).2
    change p y = (chartAt H (p x)).symm (chartAt H x y)
    rw [hp.inducedChartedSpace_chartAt_apply hc x y, (chartAt H (p x)).left_inv hpy_src]
  exact ⟨φ, hxφ, heq⟩

/-- With the manifold structure induced by a covering map `p : X → M`, the projection `p` is
`C^n`-smooth. -/
theorem induced_contMDiff [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X]
    (hc : c = IsCoveringMap.inducedChartedSpace H hp) :
    ContMDiff I I n p :=
  (hp.induced_isLocalDiffeomorph hc).contMDiff

/-- With the manifold structure induced by a covering map `p : X → M` onto a `C^1` manifold `M`,
the projection `p` is differentiable everywhere. -/
theorem induced_mdifferentiable [IsManifold I 1 M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X]
    (hc : c = IsCoveringMap.inducedChartedSpace H hp) :
    MDifferentiable I I p :=
  have : IsManifold I 1 X := hp.induced_isManifold hc
  (hp.induced_contMDiff (n := 1) hc).mdifferentiable one_ne_zero

/-- Any charted structure on `X` making it a `C^n` manifold and `p` a `C^n` local diffeomorphism
is compatible with the induced one: the union of the two atlases is still a `C^n` atlas. -/
theorem induced_unique [IsManifold I n M] {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] [IsManifold I n X] (hpc : IsLocalDiffeomorph I I n p) :
    ∀ e ∈ c.atlas, ∀ e' ∈ (IsCoveringMap.inducedChartedSpace H hp).atlas,
      e.symm ≫ₕ e' ∈ contDiffGroupoid n I := by
  intro e he e' he'
  rcases he' with ⟨x, rfl⟩
  suffices hmem : hp.inducedChartAt H x ∈ IsManifold.maximalAtlas I n X from
    IsManifold.compatible_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hmem
  refine (hp.inducedChartAt H x).mem_maximalAtlas_of_contMDiffOn ?_ ?_
  · have hchart : ContMDiffOn I I n (chartAt H (p x)) (chartAt H (p x)).source :=
      contMDiffOn_chart
    have hp_smooth : ContMDiff I I n p := hpc.contMDiff
    have hcomp : ContMDiffOn I I n (chartAt H (p x) ∘ p) (hp.inducedChartAt H x).source := by
      refine hchart.comp hp_smooth.contMDiffOn ?_
      intro y hy
      rw [hp.inducedChartAt_source] at hy
      exact hy.2
    refine hcomp.congr ?_
    intro _ _
    exact hp.inducedChartAt_apply x _
  · intro z hz
    set y := (hp.inducedChartAt H x).symm z
    have hy_mem : y ∈ (hp.inducedChartAt H x).source := (hp.inducedChartAt H x).map_target hz
    have hy_tgt : y ∈ (hp.isLocalHomeomorph.localInverseAt x).target :=
      (hp.inducedChartAt_source (H := H) x ▸ hy_mem).1
    have hz_tgt : z ∈ (chartAt H (p x)).target := (hp.inducedChartAt_target (H := H) x ▸ hz).1
    have hpy : p y = (chartAt H (p x)).symm z := hp.p_inducedChartAt_symm (H := H) hz
    rcases hpc y with ⟨ψ, hyψ, heqψ⟩
    have hpy_eq : p y = ψ y := heqψ hyψ
    have hpyψ : p y ∈ ψ.target := hpy_eq ▸ ψ.map_source hyψ
    have hψ_smooth : ContMDiffAt I I n ψ.symm (p y) :=
      ψ.symm.contMDiffOn.contMDiffAt (ψ.open_target.mem_nhds hpyψ)
    have hchart_symm : ContMDiffAt I I n (chartAt H (p x)).symm z :=
      contMDiffOn_chart_symm.contMDiffAt ((chartAt H (p x)).open_target.mem_nhds hz_tgt)
    have hcomp : ContMDiffAt I I n (ψ.symm ∘ (chartAt H (p x)).symm) z := by
      refine ContMDiffAt.comp z ?_ hchart_symm
      simpa [hpy] using hψ_smooth
    have hev : (hp.inducedChartAt H x).symm =ᶠ[𝓝 z] ψ.symm ∘ (chartAt H (p x)).symm := by
      let ψh := ψ.toOpenPartialHomeomorph
      have hU : IsOpen (ψh.source ∩ (hp.isLocalHomeomorph.localInverseAt x).target) :=
        ψh.open_source.inter (hp.isLocalHomeomorph.localInverseAt x).open_target
      have hyU : y ∈ ψh.source ∩ (hp.isLocalHomeomorph.localInverseAt x).target := ⟨hyψ, hy_tgt⟩
      have hV1 : (hp.inducedChartAt H x).symm ⁻¹'
          (ψh.source ∩ (hp.isLocalHomeomorph.localInverseAt x).target) ∈ 𝓝 z := by
        refine (hp.inducedChartAt H x).continuousOn_symm.continuousAt
          ((hp.inducedChartAt H x).open_target.mem_nhds hz) |>.preimage_mem_nhds (hU.mem_nhds hyU)
      have hV2 : (chartAt H (p x)).symm ⁻¹'
          (ψh.target ∩ (ψh.symm ⁻¹' (ψh.source ∩
            (hp.isLocalHomeomorph.localInverseAt x).target))) ∈ 𝓝 z := by
        have hopen_tgt : IsOpen (ψh.target ∩ (ψh.symm ⁻¹' (ψh.source ∩
            (hp.isLocalHomeomorph.localInverseAt x).target))) :=
          ψh.isOpen_inter_preimage_symm hU
        have hmem_tgt : (chartAt H (p x)).symm z ∈ ψh.target ∩ (ψh.symm ⁻¹' (ψh.source ∩
            (hp.isLocalHomeomorph.localInverseAt x).target)) := by
          rw [← hpy]
          refine ⟨hpyψ, ?_⟩
          simp only [mem_preimage]
          have hleft : ψh.symm (p y) = y := by
            rw [hpy_eq]
            exact ψh.left_inv hyψ
          rwa [hleft]
        exact (chartAt H (p x)).continuousOn_symm.continuousAt
          ((chartAt H (p x)).open_target.mem_nhds hz_tgt) |>.preimage_mem_nhds
          (hopen_tgt.mem_nhds hmem_tgt)
      filter_upwards [(hp.inducedChartAt H x).open_target.mem_nhds hz, hV1, hV2] with w hw hw1 hw2
      simp only [Function.comp_apply]
      have hw_left : (hp.inducedChartAt H x).symm w ∈
          (hp.isLocalHomeomorph.localInverseAt x).target := hw1.2
      have hw_right : ψ.symm ((chartAt H (p x)).symm w) ∈
          (hp.isLocalHomeomorph.localInverseAt x).target := hw2.2.2
      refine hp.isLocalHomeomorph.injOn_localInverseAt_target hw_left hw_right ?_
      have hp_right : p (ψ.symm ((chartAt H (p x)).symm w)) = (chartAt H (p x)).symm w :=
        (heqψ hw2.2.1).trans (ψh.right_inv hw2.1)
      rw [hp.p_inducedChartAt_symm (H := H) hw]
      exact hp_right.symm
    exact (hcomp.congr_of_eventuallyEq hev).contMDiffWithinAt

end IsCoveringMap

/-- A continuous-within-`s` lift of a `C^n`-within-`s` map through a covering map is
`C^n`-within-`s` at `y` for the induced manifold structure on the covering space. -/
theorem ContMDiffWithinAt.of_comp_isCoveringMap [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X]
    (hc : c = IsCoveringMap.inducedChartedSpace H hp)
    {f : N → X} {s : Set N} {y : N} (hf : ContinuousWithinAt f s y)
    (hpf : ContMDiffWithinAt J I n (p ∘ f) s y) :
    ContMDiffWithinAt J I n f s y := by
  have : IsManifold I n X := hp.induced_isManifold hc
  set x := f y
  have hchart_M : ContMDiffAt I I n (chartAt H (p x)) ((p ∘ f) y) :=
    contMDiffOn_chart.contMDiffAt
      ((chartAt H (p x)).open_source.mem_nhds (mem_chart_source H (p x)))
  have hchart_X : ContMDiffAt I I n (chartAt H x).symm (chartAt H (p x) ((p ∘ f) y)) := by
    have hmem : chartAt H (p x) ((p ∘ f) y) ∈ (chartAt H x).target := by
      change chartAt H (p x) (p x) ∈ (chartAt H x).target
      rw [← hp.inducedChartedSpace_chartAt_apply hc x x]
      exact mem_chart_target H x
    exact contMDiffOn_chart_symm.contMDiffAt ((chartAt H x).open_target.mem_nhds hmem)
  have hcomp : ContMDiffWithinAt J I n ((chartAt H x).symm ∘ chartAt H (p x) ∘ (p ∘ f)) s y :=
    hchart_X.comp_contMDiffWithinAt y (hchart_M.comp_contMDiffWithinAt y hpf)
  have hnhds : f ⁻¹' (chartAt H x).source ∈ 𝓝[s] y := by
    have hopen : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    exact hf.preimage_mem_nhdsWithin hopen
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hnhds] with z hz
    simp only [Function.comp_apply, ← hp.inducedChartedSpace_chartAt_apply hc x (f z)]
    exact ((chartAt H x).left_inv hz).symm
  · change x = (chartAt H x).symm (chartAt H (p x) (p x))
    rw [← hp.inducedChartedSpace_chartAt_apply hc x x]
    exact ((chartAt H x).left_inv (mem_chart_source H x)).symm

/-- A continuous lift of a `C^n` map through a covering map is `C^n` at `y` for the induced
manifold structure on the covering space. -/
theorem ContMDiffAt.of_comp_isCoveringMap [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X]
    (hc : c = IsCoveringMap.inducedChartedSpace H hp)
    {f : N → X} {y : N} (hf : ContinuousAt f y) (hpf : ContMDiffAt J I n (p ∘ f) y) :
    ContMDiffAt J I n f y := by
  rw [← contMDiffWithinAt_univ] at hpf ⊢
  exact ContMDiffWithinAt.of_comp_isCoveringMap hp hc hf.continuousWithinAt hpf

/-- A continuous-on-`s` lift of a `C^n`-on-`s` map through a covering map is `C^n` on `s` for the
induced manifold structure on the covering space. -/
theorem ContMDiffOn.of_comp_isCoveringMap [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X]
    (hc : c = IsCoveringMap.inducedChartedSpace H hp)
    {f : N → X} {s : Set N} (hf : ContinuousOn f s) (hpf : ContMDiffOn J I n (p ∘ f) s) :
    ContMDiffOn J I n f s :=
  fun y hy ↦ ContMDiffWithinAt.of_comp_isCoveringMap hp hc (hf y hy) (hpf y hy)

/-- A continuous lift of a `C^n` map through a covering map is `C^n` for the induced structure. -/
theorem ContMDiff.of_comp_isCoveringMap [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X]
    (hc : c = IsCoveringMap.inducedChartedSpace H hp)
    {f : N → X} (hf : Continuous f) (hpf : ContMDiff J I n (p ∘ f)) : ContMDiff J I n f :=
  fun _ ↦ ContMDiffAt.of_comp_isCoveringMap hp hc hf.continuousAt hpf.contMDiffAt

/-- For a continuous map `f : N → X` into a covering space with its induced manifold structure,
`p ∘ f` is `C^n` if and only if `f` is `C^n`. -/
theorem ContMDiff.comp_isCoveringMap_iff [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X]
    (hc : c = IsCoveringMap.inducedChartedSpace H hp)
    {f : N → X} (hf : Continuous f) :
    ContMDiff J I n (p ∘ f) ↔ ContMDiff J I n f :=
  have : IsManifold I n X := hp.induced_isManifold hc
  ⟨ContMDiff.of_comp_isCoveringMap hp hc hf, (hp.induced_contMDiff hc).comp⟩

end
