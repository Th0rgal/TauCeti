/-
Copyright (c) 2026 General Intelligence, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Orientation
import TauCeti.Geometry.Manifold.LocalDiffeomorph

/-!
# Manifold Orientations and Pullback Along Local Diffeomorphisms

This file defines orientations of finite-dimensional real manifolds (possibly with boundary or
corners) via chart signs and constructs the pullback of a manifold orientation along a `C^n` local
diffeomorphism (`1 ≤ n`).

An `OrientationLift I M ι` consists of a model orientation `modelOrientation : Orientation ℝ E ι`
with `card_eq : Fintype.card ι = Module.finrank ℝ E`, continuous chart signs
`sign x : (chartAt H x).source → ℤˣ`, and the transition compatibility `sign_mul_sign` on chart
overlaps (with transition derivatives taken within `range I`). A manifold orientation
`Manifold.Orientation I M ι` is the quotient of `OrientationLift I M ι` by the diagonal `ℤˣ`-action
flipping both `modelOrientation` and `sign` (`OrientationLift.setoid`).

## Main definitions and results

* `OrientationLift`, `OrientationLift.signAt`, `OrientationLift.setoid`: chart-sign orientation
  lifts and their equivalence relation.
* `Manifold.Orientation`, `Manifold.Orientation.neg`, `orientationAt`: manifold orientations,
  opposite orientation, and induced tangent-space orientation.
* `orientationAt_mk`, `orientationAt_neg`, `Manifold.Orientation.ext`,
  `Manifold.Orientation.eq_or_eq_neg`, `Manifold.Orientation.neg_ne`: basic API and classification
  of orientations on preconnected manifolds.
* `Orientable`: orientability with respect to `Fin (Module.finrank ℝ E)`.
* `IsOrientationPreservingAt`, `IsOrientationReversingAt`: pointwise orientation preservation and
  reversal.
* `Manifold.Orientation.pullback`, `isOrientationPreservingAt_pullback`: pullback of a manifold
  orientation along a `C^n` local diffeomorphism (`1 ≤ n`).
-/

open Set Filter Topology Function
open scoped Manifold

noncomputable section

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {ι : Type*} {n : WithTop ℕ∞}

/-! ### Sign helpers in `ℤˣ` and action on module orientations -/

section SignHelpers

variable {U V W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The unit sign `1` or `-1` of a real number, defaulting to `1` when `0 ≤ r`. -/
def realSign (r : ℝ) : ℤˣ :=
  if 0 ≤ r then 1 else -1

@[simp] theorem realSign_of_pos {r : ℝ} (hr : 0 < r) : realSign r = 1 :=
  ite_eq_left_iff.mpr fun h ↦ (h hr.le).elim

@[simp] theorem realSign_of_neg {r : ℝ} (hr : r < 0) : realSign r = -1 :=
  ite_eq_right_iff.mpr fun h ↦ (not_le.mpr hr h).elim

theorem coe_realSign_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    ((realSign r : ℤˣ) : ℤ) = (SignType.sign r : ℤ) := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · rw [realSign_of_neg hneg, sign_neg hneg]; rfl
  · rw [realSign_of_pos hpos, sign_pos hpos]; rfl

theorem realSign_mul {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    realSign (r * s) = realSign r * realSign s := by
  rcases lt_or_gt_of_ne hr with hr' | hr' <;> rcases lt_or_gt_of_ne hs with hs' | hs'
  · simp [realSign_of_pos (mul_pos_of_neg_of_neg hr' hs'), hr', hs']
  · simp [realSign_of_neg (mul_neg_of_neg_of_pos hr' hs'), hr', hs']
  · simp [realSign_of_neg (mul_neg_of_pos_of_neg hr' hs'), hr', hs']
  · simp [hr', hs']

theorem eventually_realSign_eq {X : Type*} [TopologicalSpace X] {f : X → ℝ} {x : X}
    (hf : ContinuousAt f x) (hx : f x ≠ 0) :
    ∀ᶠ y in 𝓝 x, realSign (f y) = realSign (f x) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · filter_upwards [hf.eventually (gt_mem_nhds hneg)] with y hy
    rw [realSign_of_neg hy, realSign_of_neg hneg]
  · filter_upwards [hf.eventually (lt_mem_nhds hpos)] with y hy
    rw [realSign_of_pos hy, realSign_of_pos hpos]

@[simp] theorem Orientation.neg_neg_self (o : _root_.Orientation ℝ V ι) : - -o = o :=
  InvolutiveNeg.neg_neg o

/-- Twist a module orientation by a unit sign `s : ℤˣ`. -/
def zsmulOrientation (s : ℤˣ) (o : _root_.Orientation ℝ V ι) : _root_.Orientation ℝ V ι :=
  if s = 1 then o else -o

@[simp] theorem zsmulOrientation_one (o : _root_.Orientation ℝ V ι) : zsmulOrientation 1 o = o :=
  rfl

@[simp] theorem zsmulOrientation_neg_one (o : _root_.Orientation ℝ V ι) :
    zsmulOrientation (-1) o = -o :=
  ite_eq_right_iff.mpr fun h ↦ by cases h

theorem zsmulOrientation_neg_left (s : ℤˣ) (o : _root_.Orientation ℝ V ι) :
    zsmulOrientation (-s) o = -zsmulOrientation s o := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [zsmulOrientation]

theorem zsmulOrientation_neg_right (s : ℤˣ) (o : _root_.Orientation ℝ V ι) :
    zsmulOrientation s (-o) = -zsmulOrientation s o := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [zsmulOrientation]

theorem zsmulOrientation_neg_neg (s : ℤˣ) (o : _root_.Orientation ℝ V ι) :
    zsmulOrientation (-s) (-o) = zsmulOrientation s o := by
  rw [zsmulOrientation_neg_left, zsmulOrientation_neg_right, Orientation.neg_neg_self]

theorem zsmulOrientation_mul (s₁ s₂ : ℤˣ) (o : _root_.Orientation ℝ V ι) :
    zsmulOrientation (s₁ * s₂) o = zsmulOrientation s₁ (zsmulOrientation s₂ o) := by
  rcases Int.units_eq_one_or s₁ with rfl | rfl <;>
    rcases Int.units_eq_one_or s₂ with rfl | rfl <;> simp [zsmulOrientation]

theorem zsmulOrientation_inj {s₁ s₂ : ℤˣ} (o : _root_.Orientation ℝ V ι)
    (h : zsmulOrientation s₁ o = zsmulOrientation s₂ o) : s₁ = s₂ := by
  rcases Int.units_eq_one_or s₁ with rfl | rfl <;> rcases Int.units_eq_one_or s₂ with rfl | rfl
  · rfl
  · exact (Module.Ray.ne_neg_self o (by simpa using h)).elim
  · exact (Module.Ray.ne_neg_self o (by simpa using h.symm)).elim
  · rfl

theorem Orientation.map_zsmulOrientation (e : V ≃ₗ[ℝ] W) (s : ℤˣ) (o : _root_.Orientation ℝ V ι) :
    _root_.Orientation.map ι e (zsmulOrientation s o) =
      zsmulOrientation s (_root_.Orientation.map ι e o) := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [zsmulOrientation]

theorem Orientation.map_trans_apply (e₁ : U ≃ₗ[ℝ] V) (e₂ : V ≃ₗ[ℝ] W)
    (o : _root_.Orientation ℝ U ι) :
    _root_.Orientation.map ι (e₁.trans e₂) o =
      _root_.Orientation.map ι e₂ (_root_.Orientation.map ι e₁ o) := by
  induction o using Module.Ray.ind with
  | _ v hv => rfl

theorem Orientation.map_eq_zsmulOrientation_realSign_det [Fintype ι] [FiniteDimensional ℝ V]
    (e : V ≃ₗ[ℝ] V) (o : _root_.Orientation ℝ V ι) (hcard : Fintype.card ι = Module.finrank ℝ V) :
    _root_.Orientation.map ι e o =
      zsmulOrientation (realSign (LinearMap.det (e : V →ₗ[ℝ] V))) o := by
  have hne : LinearMap.det (e : V →ₗ[ℝ] V) ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact (LinearEquiv.det e).ne_zero
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · rw [realSign_of_neg hneg, zsmulOrientation_neg_one,
      _root_.Orientation.map_eq_neg_iff_det_neg o e hcard]
    exact hneg
  · rw [realSign_of_pos hpos, zsmulOrientation_one,
      _root_.Orientation.map_eq_iff_det_pos o e hcard]
    exact hpos

end SignHelpers

/-! ### Orientation lifts and manifold orientations -/

variable [Fintype ι]

/-- An orientation lift on a manifold `M` modelled on `(E, H, I)` is a model orientation on `E`
together with chart signs `sign x : (chartAt H x).source → ℤˣ` that are continuous on each chart
source and compatible with the sign of the transition Jacobian within `range I` on overlaps. -/
structure OrientationLift (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (ι : Type*) [Fintype ι] [FiniteDimensional ℝ E] where
  /-- The orientation of the model space. -/
  modelOrientation : _root_.Orientation ℝ E ι
  /-- `card_eq` makes the model orientation a genuine orientation of `E`. -/
  card_eq : Fintype.card ι = Module.finrank ℝ E
  /-- `sign x y` is the sign of the preferred chart at `x`, at a point `y` of its source. -/
  sign : (x : M) → (chartAt H x).source → ℤˣ
  /-- Signs are locally constant on the chart source. -/
  continuous_sign : ∀ x, Continuous (sign x)
  /-- Compatibility: two charts at a common point differ by the sign of their transition
  Jacobian. -/
  sign_mul_sign : ∀ x x' y (hy : y ∈ (chartAt H x).source) (hy' : y ∈ (chartAt H x').source),
    ((sign x ⟨y, hy⟩ * sign x' ⟨y, hy'⟩ : ℤˣ) : ℤ) =
      (SignType.sign (LinearMap.det
        (fderivWithin ℝ (extChartAt I x' ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x y) : E →ₗ[ℝ] E)) : ℤ)

open Classical in
/-- The chart sign as a total function, for statements that range over a whole chart target:
`l.sign x` on the source of the chart at `x`, the junk value `1` off it. -/
noncomputable def OrientationLift.signAt [FiniteDimensional ℝ E] (l : OrientationLift I M ι)
    (x y : M) : ℤˣ :=
  if hy : y ∈ (chartAt H x).source then l.sign x ⟨y, hy⟩ else 1

variable [FiniteDimensional ℝ E]

@[ext]
theorem OrientationLift.ext {l l' : OrientationLift I M ι}
    (hmod : l.modelOrientation = l'.modelOrientation)
    (hsign : ∀ x y, l.sign x y = l'.sign x y) : l = l' := by
  cases l; cases l'; congr; funext x y; exact hsign x y

open Classical in
@[simp]
theorem OrientationLift.signAt_of_mem (l : OrientationLift I M ι) {x y : M}
    (hy : y ∈ (chartAt H x).source) : l.signAt x y = l.sign x ⟨y, hy⟩ := by
  simp [OrientationLift.signAt, hy]

open Classical in
theorem OrientationLift.signAt_of_notMem (l : OrientationLift I M ι) {x y : M}
    (hy : y ∉ (chartAt H x).source) : l.signAt x y = 1 := by
  simp [OrientationLift.signAt, hy]

/-- Because `ℤˣ` is discrete and `(chartAt H x).source` is open in `M`, the chart sign `l.sign x`
is locally constant around any point `y₀` in the source of `chartAt H x`. -/
theorem OrientationLift.eventually_sign_eq (l : OrientationLift I M ι) {x y₀ : M}
    (hy₀ : y₀ ∈ (chartAt H x).source) :
    ∀ᶠ y in 𝓝 y₀, ∃ hy : y ∈ (chartAt H x).source,
      l.sign x ⟨y, hy⟩ = l.sign x ⟨y₀, hy₀⟩ := by
  have hopen_sub : IsOpen (l.sign x ⁻¹' {l.sign x ⟨y₀, hy₀⟩}) :=
    (l.continuous_sign x).isOpen_preimage _ (isOpen_discrete _)
  have hopen_M : IsOpen (Subtype.val '' (l.sign x ⁻¹' {l.sign x ⟨y₀, hy₀⟩})) :=
    (chartAt H x).open_source.isOpenMap_subtype_val _ hopen_sub
  filter_upwards [hopen_M.mem_nhds ⟨⟨y₀, hy₀⟩, rfl, rfl⟩] with y ⟨⟨z, hz⟩, hsign, hzy⟩
  exact hzy ▸ ⟨hz, hsign⟩

/-- Two lifts define the same orientation exactly when they are equal or both flipped by the
diagonal `ℤˣ`-action. -/
@[instance_reducible]
def OrientationLift.setoid : Setoid (OrientationLift I M ι) where
  r l l' := l' = l ∨
    (l'.modelOrientation = -l.modelOrientation ∧ l'.sign = fun x y ↦ -l.sign x y)
  iseqv :=
    { refl := fun _ ↦ Or.inl rfl
      symm := by
        rintro l l' (rfl | ⟨hmod, hsign⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨by rw [hmod, Orientation.neg_neg_self], by funext x y; simp [hsign]⟩
      trans := by
        rintro l₁ l₂ l₃ (rfl | ⟨hmod₁, hsign₁⟩) (rfl | ⟨hmod₂, hsign₂⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨hmod₂, hsign₂⟩
        · exact Or.inr ⟨hmod₁, hsign₁⟩
        · exact Or.inl (OrientationLift.ext (by rw [hmod₂, hmod₁, Orientation.neg_neg_self])
            fun x y ↦ by simp [hsign₂, hsign₁]) }

attribute [local instance] OrientationLift.setoid

/-- Negate the model orientation of an `OrientationLift` while keeping its chart signs. -/
def OrientationLift.negModel (l : OrientationLift I M ι) : OrientationLift I M ι :=
  { l with modelOrientation := -l.modelOrientation }

variable (I M ι) in
/-- A manifold orientation: an orientation lift modulo the diagonal flip. -/
def Manifold.Orientation : Type _ :=
  Quotient (OrientationLift.setoid (I := I) (M := M) (ι := ι))

/-- The opposite orientation: flip the model orientation, keep the signs. -/
noncomputable def Manifold.Orientation.neg (o : Manifold.Orientation I M ι) :
    Manifold.Orientation I M ι :=
  Quotient.map OrientationLift.negModel
    (by
      rintro l l' (rfl | ⟨hmod, hsign⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [OrientationLift.negModel, hmod], hsign⟩) o

@[simp] theorem Manifold.Orientation.neg_neg (o : Manifold.Orientation I M ι) :
    o.neg.neg = o := by
  induction o using Quotient.ind with
  | _ l =>
    exact Quotient.sound (Or.inl (OrientationLift.ext (by simp [OrientationLift.negModel])
      fun _ _ ↦ rfl))

/-- A manifold orientation witnesses `Fintype.card ι = Module.finrank ℝ E`. -/
theorem Manifold.Orientation.card_eq (o : Manifold.Orientation I M ι) :
    Fintype.card ι = Module.finrank ℝ E :=
  Quotient.liftOn o OrientationLift.card_eq fun _ _ _ ↦ rfl

/-- The orientation of a tangent space induced by a manifold orientation. -/
noncomputable def orientationAt (o : Manifold.Orientation I M ι) (x : M) :
    _root_.Orientation ℝ (TangentSpace I x) ι :=
  Quotient.liftOn o
    (fun l ↦ (if l.sign x ⟨x, mem_chart_source H x⟩ = 1 then l.modelOrientation
      else -l.modelOrientation : _root_.Orientation ℝ E ι))
    (by
      rintro l l' (rfl | ⟨hmod, hsign⟩)
      · rfl
      · change zsmulOrientation (l.sign x ⟨x, mem_chart_source H x⟩) l.modelOrientation =
          zsmulOrientation (l'.sign x ⟨x, mem_chart_source H x⟩) l'.modelOrientation
        rw [hmod, hsign, zsmulOrientation_neg_neg])

/-- At the base point of its own chart, a lift's orientation is its model orientation twisted by
the chart sign there (`TangentSpace I x` is `E` through that chart). -/
theorem orientationAt_mk (l : OrientationLift I M ι) (x : M) :
    orientationAt (Quotient.mk _ l) x =
      (if l.sign x ⟨x, mem_chart_source H x⟩ = 1 then l.modelOrientation
        else -l.modelOrientation : _root_.Orientation ℝ E ι) :=
  rfl

@[simp] theorem orientationAt_neg (o : Manifold.Orientation I M ι) (x : M) :
    orientationAt o.neg x = -orientationAt o x := by
  induction o using Quotient.ind with
  | _ l => exact zsmulOrientation_neg_right (l.sign x ⟨x, mem_chart_source H x⟩) l.modelOrientation

/-- For any two lifts `l` and `l'`, on the overlap of two chart sources the product of chart signs
is independent of the lift. -/
theorem OrientationLift.sign_mul_sign_eq (l l' : OrientationLift I M ι)
    (x x' y : M) (hy : y ∈ (chartAt H x).source) (hy' : y ∈ (chartAt H x').source) :
    l.sign x ⟨y, hy⟩ * l.sign x' ⟨y, hy'⟩ = l'.sign x ⟨y, hy⟩ * l'.sign x' ⟨y, hy'⟩ := by
  apply Units.ext
  rw [l.sign_mul_sign x x' y hy hy', l'.sign_mul_sign x x' y hy hy']

/-- The chart sign of `l'` at `(x, y)` is determined by that of `l` together with the ratio of
their basepoint signs at `y`. -/
theorem OrientationLift.sign_eq_mul_diag (l l' : OrientationLift I M ι)
    (x y : M) (hy : y ∈ (chartAt H x).source) :
    l'.sign x ⟨y, hy⟩ =
      l.sign x ⟨y, hy⟩ * (l.sign y ⟨y, mem_chart_source H y⟩ *
        l'.sign y ⟨y, mem_chart_source H y⟩) := by
  rw [← mul_assoc, l.sign_mul_sign_eq l' x y y hy (mem_chart_source H y),
    mul_assoc, Int.units_mul_self, mul_one]

/-- An orientation is determined by its tangent orientations. -/
theorem Manifold.Orientation.ext {o o' : Manifold.Orientation I M ι}
    (h : ∀ x, orientationAt o x = orientationAt o' x) : o = o' := by
  induction o using Quotient.ind with
  | _ l =>
    induction o' using Quotient.ind with
    | _ l' =>
      apply Quotient.sound
      rcases _root_.Orientation.eq_or_eq_neg l'.modelOrientation l.modelOrientation l.card_eq with
        hmod | hmod
      · refine Or.inl (OrientationLift.ext hmod fun x ⟨y, hy⟩ ↦ ?_)
        have hy_eq : zsmulOrientation (l.sign y ⟨y, mem_chart_source H y⟩) l.modelOrientation =
            zsmulOrientation (l'.sign y ⟨y, mem_chart_source H y⟩) l'.modelOrientation := h y
        rw [hmod] at hy_eq
        rw [l.sign_eq_mul_diag l' x y hy, ← zsmulOrientation_inj l.modelOrientation hy_eq,
          Int.units_mul_self, mul_one]
      · refine Or.inr ⟨hmod, ?_⟩
        funext x ⟨y, hy⟩
        have hy_eq : zsmulOrientation (l.sign y ⟨y, mem_chart_source H y⟩) l.modelOrientation =
            zsmulOrientation (l'.sign y ⟨y, mem_chart_source H y⟩) l'.modelOrientation := h y
        rw [hmod, zsmulOrientation_neg_right, ← zsmulOrientation_neg_left] at hy_eq
        rw [l.sign_eq_mul_diag l' x y hy, zsmulOrientation_inj l.modelOrientation hy_eq,
          neg_mul, Int.units_mul_self, mul_neg_one]

/-- On a preconnected manifold there are at most two orientations. -/
theorem Manifold.Orientation.eq_or_eq_neg [PreconnectedSpace M]
    (o o' : Manifold.Orientation I M ι) : o' = o ∨ o' = o.neg := by
  by_cases hM : Nonempty M
  · induction o using Quotient.ind with
    | _ l =>
      induction o' using Quotient.ind with
      | _ l' =>
        let r : M → ℤˣ := fun y ↦
          l.sign y ⟨y, mem_chart_source H y⟩ * l'.sign y ⟨y, mem_chart_source H y⟩
        have hr_eq : ∀ (x y : M) (hy : y ∈ (chartAt H x).source),
            r y = l.sign x ⟨y, hy⟩ * l'.sign x ⟨y, hy⟩ := fun x y hy ↦ by
          rw [l.sign_eq_mul_diag l' x y hy, ← mul_assoc, Int.units_mul_self, one_mul]
        have hr_cont : Continuous r := by
          rw [continuous_iff_continuousAt]
          intro x
          have hev : r =ᶠ[𝓝 x] fun _ ↦ r x := by
            filter_upwards [l.eventually_sign_eq (mem_chart_source H x),
              l'.eventually_sign_eq (mem_chart_source H x)] with y ⟨hy, hly⟩ ⟨_, hl'y⟩
            rw [hr_eq x y hy, hly, hl'y, ← hr_eq x x (mem_chart_source H x)]
          exact continuousAt_const.congr hev.symm
        rcases hM with ⟨x₀⟩
        have hr_const : ∀ y : M, r y = r x₀ := fun y ↦
          (isPreconnected_range hr_cont).subsingleton (mem_range_self y) (mem_range_self x₀)
        have hsign_or : l'.sign = l.sign ∨ l'.sign = fun x y ↦ -l.sign x y := by
          rcases Int.units_eq_one_or (r x₀) with h1 | hneg1
          · refine Or.inl (funext fun x ↦ funext fun ⟨y, hy⟩ ↦ ?_)
            rw [l.sign_eq_mul_diag l' x y hy]
            change l.sign x ⟨y, hy⟩ * r y = l.sign x ⟨y, hy⟩
            rw [(hr_const y).trans h1, mul_one]
          · refine Or.inr (funext fun x ↦ funext fun ⟨y, hy⟩ ↦ ?_)
            rw [l.sign_eq_mul_diag l' x y hy]
            change l.sign x ⟨y, hy⟩ * r y = -l.sign x ⟨y, hy⟩
            rw [(hr_const y).trans hneg1, mul_neg_one]
        rcases _root_.Orientation.eq_or_eq_neg l'.modelOrientation l.modelOrientation l.card_eq with
          hmod | hmod <;> rcases hsign_or with hsign | hsign
        · exact Or.inl (Quotient.sound (Setoid.symm (Or.inl
            (OrientationLift.ext hmod fun x y ↦ congrFun (congrFun hsign x) y))))
        · refine Or.inr (Quotient.sound (Setoid.symm (Or.inr ⟨?_, hsign⟩)))
          simp [OrientationLift.negModel, hmod]
        · exact Or.inr (Quotient.sound (Setoid.symm (Or.inl
            (OrientationLift.ext hmod fun x y ↦ congrFun (congrFun hsign x) y))))
        · exact Or.inl (Quotient.sound (Setoid.symm (Or.inr ⟨hmod, hsign⟩)))
  · exact Or.inl (Manifold.Orientation.ext fun x ↦ (hM ⟨x⟩).elim)

theorem Manifold.Orientation.neg_ne [Nonempty M] (o : Manifold.Orientation I M ι) :
    o.neg ≠ o := fun h ↦ by
  obtain ⟨x⟩ := ‹Nonempty M›
  exact Module.Ray.ne_neg_self (orientationAt o x)
    (by simpa using (congrArg (orientationAt · x) h).symm)

variable (I M) in
/-- Orientability, with the canonical index type `Fin (finrank ℝ E)`. -/
def Orientable : Prop :=
  Nonempty (Manifold.Orientation I M (Fin (Module.finrank ℝ E)))

/-! ### Orientation-preserving and orientation-reversing maps -/

/-- A map is orientation-preserving at `x` when its differential is invertible there and carries
`orientationAt o x` to `orientationAt o' (f x)`. -/
def IsOrientationPreservingAt [FiniteDimensional ℝ E'] (o : Manifold.Orientation I M ι)
    (o' : Manifold.Orientation I' M' ι) (f : M → M') (x : M) : Prop :=
  ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
    (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
      _root_.Orientation.map ι e.toLinearEquiv (orientationAt o x) = orientationAt o' (f x)

/-- A map is orientation-reversing at `x` when its differential is invertible there and carries
`orientationAt o x` to `-orientationAt o' (f x)`. -/
def IsOrientationReversingAt [FiniteDimensional ℝ E'] (o : Manifold.Orientation I M ι)
    (o' : Manifold.Orientation I' M' ι) (f : M → M') (x : M) : Prop :=
  ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
    (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
      _root_.Orientation.map ι e.toLinearEquiv (orientationAt o x) = -orientationAt o' (f x)

@[simp] theorem isOrientationPreservingAt_id (o : Manifold.Orientation I M ι) (x : M) :
    IsOrientationPreservingAt o o id x :=
  ⟨ContinuousLinearEquiv.refl ℝ (TangentSpace I x), mfderiv_id.symm,
    (_root_.Orientation.map_eq_iff_det_pos _ _ o.card_eq).mpr
      (show 0 < LinearMap.det (LinearMap.id : TangentSpace I x →ₗ[ℝ] _) by simp)⟩

@[simp] theorem isOrientationReversingAt_iff_neg_right [FiniteDimensional ℝ E']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationReversingAt o o' f x ↔ IsOrientationPreservingAt o o'.neg f x := by
  simp only [IsOrientationReversingAt, IsOrientationPreservingAt, orientationAt_neg]

theorem isOrientationReversingAt_iff_neg_left [FiniteDimensional ℝ E']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationReversingAt o o' f x ↔ IsOrientationPreservingAt o.neg o' f x := by
  refine ⟨fun ⟨e, he, hmap⟩ ↦ ⟨e, he, ?_⟩, fun ⟨e, he, hmap⟩ ↦ ⟨e, he, ?_⟩⟩
  · rw [orientationAt_neg, _root_.Orientation.map_neg, hmap, Orientation.neg_neg_self]
  · rw [orientationAt_neg, _root_.Orientation.map_neg] at hmap
    rw [← hmap, Orientation.neg_neg_self]

/-! ### Transition Jacobian properties and pullback along local diffeomorphisms -/

section Pullback

/-- The coordinate change derivative within `range I` from the chart at `x` to the chart at `x'`
evaluated at `y`. -/
def coordChangeDeriv (I : ModelWithCorners ℝ E H) (x x' y : M) : E →L[ℝ] E :=
  fderivWithin ℝ (extChartAt I x' ∘ (extChartAt I x).symm) (range I) (extChartAt I x y)

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem tangentCoordChange_self_eq_id [IsManifold I 1 M] (x : M) {z : M}
    (hz : z ∈ (chartAt H x).source) :
    tangentCoordChange I x x z = ContinuousLinearMap.id ℝ E := by
  ext v; exact tangentCoordChange_self (by rwa [extChartAt_source])

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem tangentCoordChange_comp_eq [IsManifold I 1 M] (w x y : M) {z : M}
    (hw : z ∈ (chartAt H w).source) (hx : z ∈ (chartAt H x).source)
    (hy : z ∈ (chartAt H y).source) :
    (tangentCoordChange I x y z).comp (tangentCoordChange I w x z) =
      tangentCoordChange I w y z := by
  ext v; refine tangentCoordChange_comp ⟨⟨?_, ?_⟩, ?_⟩ <;> rwa [extChartAt_source]

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem det_tangentCoordChange_mul_self (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]
    (x y : M) {z : M} (hx : z ∈ (chartAt H x).source) (hy : z ∈ (chartAt H y).source) :
    (tangentCoordChange I y x z).det * (tangentCoordChange I x y z).det = 1 := by
  have hcomp := tangentCoordChange_comp_eq (I := I) x y x hx hy hx
  rw [tangentCoordChange_self_eq_id x hx] at hcomp
  simpa [ContinuousLinearMap.det, LinearMap.det_comp] using
    congrArg ContinuousLinearMap.det hcomp

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem det_tangentCoordChange_ne_zero (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]
    (x y : M) {z : M} (hx : z ∈ (chartAt H x).source) (hy : z ∈ (chartAt H y).source) :
    (tangentCoordChange I x y z).det ≠ 0 :=
  right_ne_zero_of_mul_eq_one (det_tangentCoordChange_mul_self I x y hx hy)

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem realSign_det_tangentCoordChange_symm (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]
    (x y : M) {z : M} (hx : z ∈ (chartAt H x).source) (hy : z ∈ (chartAt H y).source) :
    realSign (tangentCoordChange I y x z).det = realSign (tangentCoordChange I x y z).det := by
  have hrs := congrArg realSign (det_tangentCoordChange_mul_self I x y hx hy)
  rw [realSign_mul (det_tangentCoordChange_ne_zero I y x hy hx)
    (det_tangentCoordChange_ne_zero I x y hx hy), realSign_of_pos zero_lt_one] at hrs
  rw [← one_mul (realSign (tangentCoordChange I x y z).det), ← hrs, mul_assoc,
    Int.units_mul_self, mul_one]

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem realSign_det_tangentCoordChange_comp (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]
    (w x y : M) {z : M} (hw : z ∈ (chartAt H w).source) (hx : z ∈ (chartAt H x).source)
    (hy : z ∈ (chartAt H y).source) :
    realSign (tangentCoordChange I w y z).det =
      realSign (tangentCoordChange I x y z).det * realSign (tangentCoordChange I w x z).det := by
  have hdet : (tangentCoordChange I w y z).det =
      (tangentCoordChange I x y z).det * (tangentCoordChange I w x z).det := by
    simpa [ContinuousLinearMap.det, LinearMap.det_comp] using
      congrArg ContinuousLinearMap.det (tangentCoordChange_comp_eq (I := I) w x y hw hx hy).symm
  rw [hdet, realSign_mul (det_tangentCoordChange_ne_zero I x y hx hy)
    (det_tangentCoordChange_ne_zero I w x hw hx)]

theorem OrientationLift.sign_mul_sign_eq_realSign [IsManifold I 1 M]
    (l : OrientationLift I M ι) (x x' y : M)
    (hy : y ∈ (chartAt H x).source) (hy' : y ∈ (chartAt H x').source) :
    l.sign x ⟨y, hy⟩ * l.sign x' ⟨y, hy'⟩ = realSign (tangentCoordChange I x x' y).det := by
  apply Units.ext
  rw [l.sign_mul_sign x x' y hy hy',
    coe_realSign_of_ne_zero (det_tangentCoordChange_ne_zero I x x' hy hy'),
    tangentCoordChange_def]

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem det_comp_three (e : E ≃ₗ[ℝ] E')
    (A : E' →L[ℝ] E') (B : E ≃L[ℝ] E') (C : E →L[ℝ] E) :
    LinearMap.det ((e.symm : E' →ₗ[ℝ] E).comp (A.comp ((B : E →L[ℝ] E').comp C)).toLinearMap) =
      A.det * LinearMap.det ((e.symm.trans B.toLinearEquiv) : E' →ₗ[ℝ] E') * C.det := by
  let g : E' →ₗ[ℝ] E' := (e.symm.trans B.toLinearEquiv : E' ≃ₗ[ℝ] E').toLinearMap
  have h : (e.symm : E' →ₗ[ℝ] E).comp (A.comp ((B : E →L[ℝ] E').comp C)).toLinearMap =
      ((e.symm : E' →ₗ[ℝ] E).comp ((A.toLinearMap.comp g).comp (e.symm.symm : E →ₗ[ℝ] E'))).comp
        C.toLinearMap := by
    ext v; simp [g]
  rw [h, LinearMap.det_comp, LinearMap.det_conj _ e.symm, LinearMap.det_comp]

/-- The chart sign of the pullback orientation lift along a local diffeomorphism `f`. -/
def OrientationLift.pullbackSign [FiniteDimensional ℝ E']
    {f : M → M'} (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ E')
    (l' : OrientationLift I' M' ι) (x : M) (y : (chartAt H x).source) : ℤˣ :=
  let e₀ : E ≃ₗ[ℝ] E' := LinearEquiv.ofFinrankEq E E' hfinrank
  let hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  let df : E ≃L[ℝ] E' := (hf y.1).mfderivToContinuousLinearEquiv hn0
  l'.sign (f y.1) ⟨f y.1, mem_chart_source H' (f y.1)⟩ *
    realSign (LinearMap.det ((e₀.symm.trans df.toLinearEquiv) : E' →ₗ[ℝ] E')) *
    realSign (coordChangeDeriv I x y.1 y.1).det

theorem OrientationLift.continuous_pullbackSign [FiniteDimensional ℝ E']
    [IsManifold I n M] [IsManifold I' n M'] {f : M → M'}
    (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ E')
    (l' : OrientationLift I' M' ι) (x : M) :
    Continuous (l'.pullbackSign hf hn hfinrank x) := by
  have : IsManifold I 1 M := IsManifold.of_le hn
  have : IsManifold I' 1 M' := IsManifold.of_le hn
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  let e₀ : E ≃ₗ[ℝ] E' := LinearEquiv.ofFinrankEq E E' hfinrank
  let df : (y : M) → E ≃L[ℝ] E' := fun y ↦ (hf y).mfderivToContinuousLinearEquiv hn0
  let jacSign : M → ℤˣ := fun y ↦
    realSign (LinearMap.det ((e₀.symm.trans (df y).toLinearEquiv) : E' →ₗ[ℝ] E'))
  have hjac_ne : ∀ y, LinearMap.det ((e₀.symm.trans (df y).toLinearEquiv) : E' →ₗ[ℝ] E') ≠ 0 :=
    fun y ↦ by
      rw [← LinearEquiv.coe_det]
      exact (LinearEquiv.det (e₀.symm.trans (df y).toLinearEquiv)).ne_zero
  rw [continuous_iff_continuousAt]
  rintro ⟨y₀, hy₀⟩
  let ec : E' →L[ℝ] E := e₀.symm.toLinearMap.toContinuousLinearMap
  have hM_smooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') 0
      (inTangentCoordinates I I' id f (mfderiv% f) y₀) y₀ :=
    (hf y₀).contMDiffAt.mfderiv_const (by simpa using hn)
  have hdet_M_cont : ContinuousAt (fun y : M ↦
      LinearMap.det ((e₀.symm : E' →ₗ[ℝ] E).comp
        (inTangentCoordinates I I' id f (mfderiv% f) y₀ y).toLinearMap)) y₀ := by
    have hcomp_cont : Continuous (fun A : E →L[ℝ] E' ↦ (ec.comp A).det) :=
      ContinuousLinearMap.continuous_det.comp (ec.compL ℝ E E' E).continuous
    exact hcomp_cont.continuousAt.comp hM_smooth.continuousAt
  have hM_y₀ : inTangentCoordinates I I' id f (mfderiv% f) y₀ y₀ =
      (tangentCoordChange I' (f y₀) (f y₀) (f y₀)).comp
        ((df y₀ : E →L[ℝ] E').comp (tangentCoordChange I y₀ y₀ y₀)) :=
    inTangentCoordinates_eq id f (mfderiv% f) (mem_chart_source H y₀) (mem_chart_source H' (f y₀))
  have hdet_M_ne : LinearMap.det ((e₀.symm : E' →ₗ[ℝ] E).comp
      (inTangentCoordinates I I' id f (mfderiv% f) y₀ y₀).toLinearMap) ≠ 0 := by
    rw [hM_y₀, det_comp_three e₀ _ (df y₀) _]
    exact mul_ne_zero (mul_ne_zero
      (det_tangentCoordChange_ne_zero I' (f y₀) (f y₀)
        (mem_chart_source H' (f y₀)) (mem_chart_source H' (f y₀)))
      (hjac_ne y₀))
      (det_tangentCoordChange_ne_zero I y₀ y₀ (mem_chart_source H y₀) (mem_chart_source H y₀))
  have hev_M := eventually_realSign_eq hdet_M_cont hdet_M_ne
  have htc_cont : ContinuousAt (tangentCoordChange I x y₀) y₀ := by
    refine (continuousOn_tangentCoordChange (I := I) x y₀).continuousAt ?_
    refine IsOpen.mem_nhds
      ((isOpen_extChartAt_source x).inter (isOpen_extChartAt_source y₀)) ⟨?_, ?_⟩
    · rwa [extChartAt_source]
    · exact mem_extChartAt_source y₀
  have hdet_tc_cont : ContinuousAt (fun y : M ↦ (tangentCoordChange I x y₀ y).det) y₀ :=
    ContinuousLinearMap.continuous_det.continuousAt.comp htc_cont
  have hev_tc := eventually_realSign_eq hdet_tc_cont
    (det_tangentCoordChange_ne_zero I x y₀ hy₀ (mem_chart_source H y₀))
  have hev_l' := hf.contMDiff.continuous.continuousAt.eventually
    (l'.eventually_sign_eq (mem_chart_source H' (f y₀)))
  have hy₀_mem : (chartAt H y₀).source ∈ 𝓝 y₀ :=
    (chartAt H y₀).open_source.mem_nhds (mem_chart_source H y₀)
  let c₀ : ℤˣ :=
    l'.sign (f y₀) ⟨f y₀, mem_chart_source H' (f y₀)⟩ *
      realSign (LinearMap.det ((e₀.symm : E' →ₗ[ℝ] E).comp
        (inTangentCoordinates I I' id f (mfderiv% f) y₀ y₀).toLinearMap)) *
      realSign (tangentCoordChange I x y₀ y₀).det
  have hev_M_eq : ∀ᶠ y in 𝓝 y₀, ∀ hy : y ∈ (chartAt H x).source,
      l'.pullbackSign hf hn hfinrank x ⟨y, hy⟩ = c₀ := by
    filter_upwards [hy₀_mem, hev_l', hev_M, hev_tc] with y hy_y₀ ⟨hfy_y₀, hl'_eq⟩ hM_eq0 htc_eq0 hy
    have hl' : l'.sign (f y) ⟨f y, mem_chart_source H' (f y)⟩ =
        l'.sign (f y₀) ⟨f y, hfy_y₀⟩ * realSign (tangentCoordChange I' (f y₀) (f y) (f y)).det := by
      rw [← l'.sign_mul_sign_eq_realSign (f y₀) (f y) (f y) hfy_y₀ (mem_chart_source H' (f y)),
        ← mul_assoc, Int.units_mul_self, one_mul]
    have htc_split := realSign_det_tangentCoordChange_comp I x y₀ y hy hy_y₀ (mem_chart_source H y)
    have hdet_M_eq : LinearMap.det ((e₀.symm : E' →ₗ[ℝ] E).comp
          (inTangentCoordinates I I' id f (mfderiv% f) y₀ y).toLinearMap) =
        (tangentCoordChange I' (f y) (f y₀) (f y)).det *
          LinearMap.det ((e₀.symm.trans (df y).toLinearEquiv) : E' →ₗ[ℝ] E') *
          (tangentCoordChange I y₀ y y).det := by
      rw [inTangentCoordinates_eq id f (mfderiv% f) hy_y₀ hfy_y₀]
      exact det_comp_three e₀ _ (df y) _
    have htc'_ne := det_tangentCoordChange_ne_zero I' (f y) (f y₀)
      (mem_chart_source H' (f y)) hfy_y₀
    have htc_y₀_ne := det_tangentCoordChange_ne_zero I y₀ y hy_y₀ (mem_chart_source H y)
    have hsign_M_split :
        realSign (LinearMap.det ((e₀.symm : E' →ₗ[ℝ] E).comp
          (inTangentCoordinates I I' id f (mfderiv% f) y₀ y).toLinearMap)) =
          realSign (tangentCoordChange I' (f y₀) (f y) (f y)).det *
            jacSign y * realSign (tangentCoordChange I y₀ y y).det := by
      rw [hdet_M_eq, realSign_mul (mul_ne_zero htc'_ne (hjac_ne y)) htc_y₀_ne,
        realSign_mul htc'_ne (hjac_ne y),
        realSign_det_tangentCoordChange_symm I' (f y₀) (f y) hfy_y₀ (mem_chart_source H' (f y))]
    change l'.sign (f y) ⟨f y, mem_chart_source H' (f y)⟩ * jacSign y *
      realSign (tangentCoordChange I x y y).det = c₀
    dsimp only [c₀]
    rw [← hl'_eq, ← hM_eq0, ← htc_eq0, hl', htc_split, hsign_M_split]
    ac_rfl
  refine (continuousAt_const (y := c₀)).congr ?_
  filter_upwards [continuousAt_subtype_val.eventually hev_M_eq] with z hz_eq
  exact (hz_eq z.2).symm

theorem OrientationLift.pullbackSign_mul_pullbackSign [FiniteDimensional ℝ E']
    [IsManifold I n M] {f : M → M'}
    (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ E')
    (l' : OrientationLift I' M' ι) (x x' y : M)
    (hy : y ∈ (chartAt H x).source) (hy' : y ∈ (chartAt H x').source) :
    ((l'.pullbackSign hf hn hfinrank x ⟨y, hy⟩ *
      l'.pullbackSign hf hn hfinrank x' ⟨y, hy'⟩ : ℤˣ) : ℤ) =
      (SignType.sign (LinearMap.det
        (fderivWithin ℝ (extChartAt I x' ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x y) : E →ₗ[ℝ] E)) : ℤ) := by
  have : IsManifold I 1 M := IsManifold.of_le hn
  let e₀ : E ≃ₗ[ℝ] E' := LinearEquiv.ofFinrankEq E E' hfinrank
  let hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  let df : E ≃L[ℝ] E' := (hf y).mfderivToContinuousLinearEquiv hn0
  set u := l'.sign (f y) ⟨f y, mem_chart_source H' (f y)⟩ *
    realSign (LinearMap.det ((e₀.symm.trans df.toLinearEquiv) : E' →ₗ[ℝ] E'))
  let sx := realSign (tangentCoordChange I x y y).det
  let sx' := realSign (tangentCoordChange I x' y y).det
  have hprod : l'.pullbackSign hf hn hfinrank x ⟨y, hy⟩ *
      l'.pullbackSign hf hn hfinrank x' ⟨y, hy'⟩ =
      realSign (tangentCoordChange I x x' y).det := by
    change (u * sx) * (u * sx') = _
    rw [show (u * sx) * (u * sx') = (u * u) * (sx * sx') by ac_rfl,
      Int.units_mul_self, one_mul]
    dsimp only [sx, sx']
    rw [realSign_det_tangentCoordChange_comp I x x' y hy hy' (mem_chart_source H y),
      mul_right_comm, Int.units_mul_self, one_mul]
  rw [hprod, coe_realSign_of_ne_zero (det_tangentCoordChange_ne_zero I x x' hy hy'),
    tangentCoordChange_def]

/-- Pullback of an `OrientationLift` along a `C^n` local diffeomorphism (`1 ≤ n`), given an
equality of model-space dimensions. -/
noncomputable def OrientationLift.pullback [FiniteDimensional ℝ E'] [IsManifold I n M]
    [IsManifold I' n M'] {f : M → M'} (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ E')
    (l' : OrientationLift I' M' ι) : OrientationLift I M ι where
  modelOrientation :=
    _root_.Orientation.map ι (LinearEquiv.ofFinrankEq E E' hfinrank).symm l'.modelOrientation
  card_eq := l'.card_eq.trans hfinrank.symm
  sign := l'.pullbackSign hf hn hfinrank
  continuous_sign := l'.continuous_pullbackSign hf hn hfinrank
  sign_mul_sign := l'.pullbackSign_mul_pullbackSign hf hn hfinrank

/-- The pullback orientation along a local diffeomorphism, characterized by making `f`
orientation-preserving everywhere. -/
noncomputable def Manifold.Orientation.pullback [FiniteDimensional ℝ E'] [IsManifold I n M]
    [IsManifold I' n M'] {f : M → M'} (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n)
    (o' : Manifold.Orientation I' M' ι)
    (hdim : Nonempty M ∨ Module.finrank ℝ E = Module.finrank ℝ E' := by
      first | exact Or.inr rfl | exact Or.inl inferInstance | (left; constructor; assumption)) :
    Manifold.Orientation I M ι :=
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hfinrank : Module.finrank ℝ E = Module.finrank ℝ E' :=
    hdim.elim (fun ⟨x₀⟩ ↦ ((hf x₀).mfderivToContinuousLinearEquiv hn0).toLinearEquiv.finrank_eq) id
  Quotient.map (OrientationLift.pullback hf hn hfinrank)
    (by
      rintro l₁ l₂ (rfl | ⟨hmod, hsign⟩)
      · exact Or.inl rfl
      · refine Or.inr ⟨by simp [OrientationLift.pullback, hmod], ?_⟩
        funext x y
        simp [OrientationLift.pullback, OrientationLift.pullbackSign, hsign, neg_mul]) o'

theorem isOrientationPreservingAt_pullback [FiniteDimensional ℝ E'] [IsManifold I n M]
    [IsManifold I' n M'] {f : M → M'} (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n)
    (o' : Manifold.Orientation I' M' ι) (x : M) :
    IsOrientationPreservingAt (o'.pullback hf hn) o' f x := by
  have : IsManifold I 1 M := IsManifold.of_le hn
  have : IsManifold I' 1 M' := IsManifold.of_le hn
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hfinrank : Module.finrank ℝ E = Module.finrank ℝ E' :=
    ((hf x).mfderivToContinuousLinearEquiv hn0).toLinearEquiv.finrank_eq
  induction o' using Quotient.ind with
  | _ l' =>
    refine ⟨(hf x).mfderivToContinuousLinearEquiv hn0, rfl, ?_⟩
    let e₀ : E ≃ₗ[ℝ] E' := LinearEquiv.ofFinrankEq E E' hfinrank
    let dfx : E ≃L[ℝ] E' := (hf x).mfderivToContinuousLinearEquiv hn0
    let jacSignx : ℤˣ :=
      realSign (LinearMap.det ((e₀.symm.trans dfx.toLinearEquiv) : E' →ₗ[ℝ] E'))
    have htc_id : realSign (coordChangeDeriv I x x x).det = 1 := by
      change realSign (tangentCoordChange I x x x).det = 1
      rw [tangentCoordChange_self_eq_id x (mem_chart_source H x)]
      simp [ContinuousLinearMap.det]
    change _root_.Orientation.map ι dfx.toLinearEquiv
        (zsmulOrientation
          (l'.sign (f x) ⟨f x, mem_chart_source H' (f x)⟩ * jacSignx *
            realSign (coordChangeDeriv I x x x).det)
          (_root_.Orientation.map ι e₀.symm l'.modelOrientation)) =
      zsmulOrientation (l'.sign (f x) ⟨f x, mem_chart_source H' (f x)⟩) l'.modelOrientation
    rw [htc_id, mul_one, Orientation.map_zsmulOrientation,
      ← Orientation.map_trans_apply e₀.symm dfx.toLinearEquiv,
      Orientation.map_eq_zsmulOrientation_realSign_det
        (e₀.symm.trans dfx.toLinearEquiv) l'.modelOrientation l'.card_eq,
      ← zsmulOrientation_mul, mul_assoc, Int.units_mul_self, mul_one]

@[simp] theorem Manifold.Orientation.pullback_neg [FiniteDimensional ℝ E'] [IsManifold I n M]
    [IsManifold I' n M'] {f : M → M'} (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n)
    (o' : Manifold.Orientation I' M' ι)
    (hdim : Nonempty M ∨ Module.finrank ℝ E = Module.finrank ℝ E' := by
      first | exact Or.inr rfl | exact Or.inl inferInstance | (left; constructor; assumption)) :
    o'.neg.pullback hf hn hdim = (o'.pullback hf hn hdim).neg := by
  induction o' using Quotient.ind with
  | _ l' =>
    exact Quotient.sound (Or.inl (OrientationLift.ext
      (by simp [OrientationLift.pullback, OrientationLift.negModel]) fun _ _ ↦ rfl))

/-- Pullback of orientability along a `C^n` local diffeomorphism (`1 ≤ n`). -/
theorem Orientable.of_isLocalDiffeomorph [FiniteDimensional ℝ E'] [IsManifold I n M]
    [IsManifold I' n M'] {f : M → M'} (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n)
    (h : Orientable I' M')
    (hdim : Nonempty M ∨ Module.finrank ℝ E = Module.finrank ℝ E' := by
      first | exact Or.inr rfl | exact Or.inl inferInstance | (left; constructor; assumption)) :
    Orientable I M := by
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hfinrank : Module.finrank ℝ E = Module.finrank ℝ E' :=
    hdim.elim (fun ⟨x₀⟩ ↦ ((hf x₀).mfderivToContinuousLinearEquiv hn0).toLinearEquiv.finrank_eq) id
  rcases h with ⟨o'⟩
  exact ⟨hfinrank ▸ o'.pullback hf hn (Or.inr hfinrank)⟩

end Pullback

end
