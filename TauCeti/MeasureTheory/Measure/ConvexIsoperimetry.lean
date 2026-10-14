/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import TauCeti.MeasureTheory.Measure.HalfSpacePerimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski
public import TauCeti.MeasureTheory.Measure.Lebesgue.PrekopaLeindler
public import TauCeti.MeasureTheory.Measure.MinkowskiContent
import all TauCeti.MeasureTheory.Measure.EssentialBoundary
import all TauCeti.MeasureTheory.Measure.MinkowskiContent

/-!
# Convex Parallel-Volume Concavity, Tangent Rigidity, Steiner Reduction, and Ball Rigidity

This file develops the convex-geometric and measure-theoretic rigidity machinery connecting
Minkowski sums, outer parallel volumes, Steiner symmetrization, and regular open sets:

1. **Minkowski-sum convex interpolation & convex body regularity**:
   `Convex.combo_minkowskiSum`, `Convex.combo_add_smul`, `combo_outerParallel`,
   `Convex.interior_nonempty_of_measure_pos`, `Convex.interior_ae_eq`, `Convex.closure_ae_eq`,
   `Convex.perimeter_interior`, and `Convex.perimeter_closure`.
2. **Concavity of the parallel-volume root `t ↦ |K + t • B|^(1/n)` & concave tangent rigidity**:
   `outerParallelRoot`, `parallelVolumeRoot`, `concaveOn_outerParallelRoot`,
   `concaveOn_parallelVolumeRoot`, `outerParallelRoot_ge_linear`, `parallelVolumeRoot_ge_linear`,
   `eq_linear_of_concaveOn_of_ge_linear_of_hasDerivWithinAt`,
   `isoperimetric_minkowskiContent_of_convex`, and
   `parallelVolumeRoot_eq_linear_of_minkowskiContent_eq`.
3. **Steiner-to-convex rigidity reduction**:
   `perimeter_steinerSymmetrization_eq_of_isoperimetric_eq`,
   `convex_essentialInterior_of_ae_ordConnected_steinerFiber`,
   `exists_convex_ae_eq_of_ae_ordConnected_steinerFiber`, and
   `exists_convex_ae_eq_of_perimeter_steinerSymmetrization_eq_forall`.
4. **Topological frontier nullity & regular open point-set ball rigidity**:
   `measure_frontier_eq_zero_of_hausdorffMeasure_sub_one_ne_top`, `IsRegularOpen`,
   `isRegularOpen_ball`, `eq_of_isRegularOpen_of_ae_eq`, `eq_ball_of_isRegularOpen_of_ae_eq_ball`,
   and `frontier_eq_sphere_of_isRegularOpen_of_ae_eq_ball`.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Pointwise Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology
open TauCeti.MeasureTheory

namespace TauCeti

/-! ### Section 1: Minkowski-sum convex interpolation & convex body regularity -/

section MinkowskiConvexInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Minkowski-sum convex interpolation identity** (`a, b ≥ 0`, `a + b = 1`, `s, t ≥ 0`):
`a • (K + s • B) + b • (K + t • B) = K + (a * s + b * t) • B`. -/
theorem _root_.Convex.combo_minkowskiSum {K B : Set E} (hK : Convex ℝ K) (hB : Convex ℝ B)
    {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    a • (K + s • B) + b • (K + t • B) = K + (a * s + b * t) • B := by
  rw [smul_add, smul_add, add_add_add_comm, ← hK.add_smul ha hb, hab, one_smul,
    smul_smul, smul_smul, ← hB.add_smul (mul_nonneg ha hs) (mul_nonneg hb ht)]

/-- **Minkowski-sum convex interpolation identity** for `0 ≤ θ ≤ 1` and `s, t ≥ 0`:
`(1 - θ) • (K + s • B) + θ • (K + t • B) = K + ((1 - θ) * s + θ * t) • B`. -/
theorem _root_.Convex.combo_add_smul {K B : Set E} (hK : Convex ℝ K) (hB : Convex ℝ B)
    {θ s t : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (1 - θ) • (K + s • B) + θ • (K + t • B) = K + ((1 - θ) * s + θ * t) • B :=
  hK.combo_minkowskiSum hB (sub_nonneg.2 hθ₁) hθ₀ (sub_add_cancel 1 θ) hs ht
/-- Minkowski-sum convex interpolation for `B = Metric.closedBall (0 : E) 1`. -/
theorem combo_add_smul_closedBall {K : Set E} (hK : Convex ℝ K)
    {θ s t : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (1 - θ) • (K + s • Metric.closedBall (0 : E) 1) +
        θ • (K + t • Metric.closedBall (0 : E) 1) =
      K + ((1 - θ) * s + θ * t) • Metric.closedBall (0 : E) 1 :=
  hK.combo_add_smul (convex_closedBall (0 : E) 1) hθ₀ hθ₁ hs ht
/-- Minkowski-sum convex interpolation for `B = Metric.ball (0 : E) 1`. -/
theorem combo_add_smul_ball {K : Set E} (hK : Convex ℝ K)
    {θ s t : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (1 - θ) • (K + s • Metric.ball (0 : E) 1) + θ • (K + t • Metric.ball (0 : E) 1) =
      K + ((1 - θ) * s + θ * t) • Metric.ball (0 : E) 1 :=
  hK.combo_add_smul (convex_ball (0 : E) 1) hθ₀ hθ₁ hs ht
/-- Minkowski-sum convex interpolation for `outerParallel K` (`a, b ≥ 0`, `a + b = 1`). -/
theorem _root_.Convex.smul_outerParallel_add_smul_outerParallel {K : Set E} (hK : Convex ℝ K)
    {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    a • outerParallel K s + b • outerParallel K t = outerParallel K (a * s + b * t) :=
  hK.combo_minkowskiSum (convex_closedBall (0 : E) 1) ha hb hab hs ht
/-- Minkowski-sum convex interpolation for `outerParallel K` with `0 ≤ θ ≤ 1` and `s, t ≥ 0`. -/
theorem combo_outerParallel {K : Set E} (hK : Convex ℝ K)
    {θ s t : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (1 - θ) • outerParallel K s + θ • outerParallel K t =
      outerParallel K ((1 - θ) * s + θ * t) :=
  hK.smul_outerParallel_add_smul_outerParallel (sub_nonneg.2 hθ₁) hθ₀ (sub_add_cancel 1 θ) hs ht
/-- For a convex set `K`, `K + t • Metric.closedBall (0 : E) 1` is convex for every `t : ℝ`. -/
theorem _root_.Convex.add_smul_closedBall {K : Set E} (hK : Convex ℝ K) (t : ℝ) :
    Convex ℝ (K + t • Metric.closedBall (0 : E) 1) := hK.add ((convex_closedBall (0 : E) 1).smul t)
/-- For a convex set `K`, `K + t • Metric.ball (0 : E) 1` is convex for every `t : ℝ`. -/
theorem _root_.Convex.add_smul_ball {K : Set E} (hK : Convex ℝ K) (t : ℝ) :
    Convex ℝ (K + t • Metric.ball (0 : E) 1) := hK.add ((convex_ball (0 : E) 1).smul t)
/-- For a convex set `K`, `outerParallel K t` is convex for every `t : ℝ`. -/
theorem _root_.Convex.outerParallel {K : Set E} (hK : Convex ℝ K) (t : ℝ) :
    Convex ℝ (outerParallel K t) := hK.add_smul_closedBall t

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **A convex set of positive Haar measure has nonempty topological interior**. -/
theorem _root_.Convex.interior_nonempty_of_measure_pos {K : Set E} (hK : Convex ℝ K)
    (hpos : 0 < μ K) : (interior K).Nonempty := by
  rw [Convex.interior_nonempty_iff_affineSpan_eq_top hK]; by_contra hne
  exact hpos.ne' (measure_mono_null (subset_affineSpan ℝ K)
    (Measure.addHaar_affineSubspace μ _ hne))

/-- For any convex set `K ⊆ E`, `interior K =ᵐ[μ] K`. -/
theorem _root_.Convex.interior_ae_eq {K : Set E} (hK : Convex ℝ K) : interior K =ᵐ[μ] K :=
  interior_ae_eq_of_null_frontier (hK.addHaar_frontier μ)
/-- For any convex set `K ⊆ E`, `closure K =ᵐ[μ] K`. -/
theorem _root_.Convex.closure_ae_eq {K : Set E} (hK : Convex ℝ K) : closure K =ᵐ[μ] K :=
  closure_ae_eq_of_null_frontier (hK.addHaar_frontier μ)
/-- For any convex set `K ⊆ E`, `μ (interior K) = μ K`. -/
theorem _root_.Convex.measure_interior {K : Set E} (hK : Convex ℝ K) : μ (interior K) = μ K :=
  measure_congr hK.interior_ae_eq
/-- For any convex set `K ⊆ E`, `μ (closure K) = μ K`. -/
theorem _root_.Convex.measure_closure {K : Set E} (hK : Convex ℝ K) : μ (closure K) = μ K :=
  measure_congr hK.closure_ae_eq

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure]

/-- For any convex set `K`, `perimeter ν (interior K) = perimeter ν K`. -/
theorem _root_.Convex.perimeter_interior {K : Set V} (hK : Convex ℝ K) :
    perimeter ν (interior K) = perimeter ν K := perimeter_congr_ae (hK.interior_ae_eq (μ := ν))
/-- For any convex set `K`, `perimeter ν (closure K) = perimeter ν K`. -/
theorem _root_.Convex.perimeter_closure {K : Set V} (hK : Convex ℝ K) :
    perimeter ν (closure K) = perimeter ν K := perimeter_congr_ae (hK.closure_ae_eq (μ := ν))

end MinkowskiConvexInterpolation

/-! ### Section 2: Concavity of the parallel-volume root & concave tangent rigidity -/

section ParallelVolumeConcavityAndRigidity

/-- For a concave function `f : ℝ → ℝ` on `Set.Ici 0`, `t ↦ (f t - f 0) / t` is antitone on
`Set.Ioi 0`. -/
theorem antitoneOn_slope_Ioi_of_concaveOn {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) :
    AntitoneOn (fun t : ℝ ↦ (f t - f 0) / t) (Set.Ioi 0) := by
  intro s (hs : 0 < s) t (ht : 0 < t) hst
  have hb : 0 ≤ s / t := div_nonneg hs.le ht.le
  have ha : 0 ≤ 1 - s / t := sub_nonneg.2 ((div_le_one ht).2 hst)
  have hcomb := hf.2 (le_rfl : (0 : ℝ) ∈ Set.Ici 0) ht.le ha hb (sub_add_cancel 1 (s / t))
  have hs_eq : (1 - s / t) • (0 : ℝ) + (s / t) • t = s := by
    simp [smul_eq_mul, div_mul_cancel₀ s ht.ne']
  rw [hs_eq] at hcomb; simp only [smul_eq_mul] at hcomb; rw [div_le_div_iff₀ ht hs]
  have hring : ((1 - s / t) * f 0 + s / t * f t) * t = t * f 0 - s * f 0 + s * f t := by
    linear_combination (f t - f 0) * div_mul_cancel₀ s ht.ne'
  nlinarith [mul_le_mul_of_nonneg_right hcomb ht.le]

/-- If `f 0 + c * t ≤ f t` for all `t ≥ 0`, then `c ≤ (f t - f 0) / t` for all `t > 0`. -/
theorem le_slope_of_concaveOn_of_ge_linear {f : ℝ → ℝ} (_hf : ConcaveOn ℝ (Set.Ici 0) f) {c : ℝ}
    (hlin : ∀ t ≥ 0, f 0 + c * t ≤ f t) {t : ℝ} (ht : 0 < t) : c ≤ (f t - f 0) / t := by
  rw [le_div_iff₀ ht]; linarith [hlin t ht.le]
/-- `HasDerivWithinAt f d (Set.Ioi 0) 0` implies `(f s - f 0) / s → d` as `s → 0+`. -/
theorem tendsto_slope_zero_of_hasDerivWithinAt_Ioi {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivWithinAt f d (Set.Ioi 0) 0) :
    Tendsto (fun s : ℝ ↦ (f s - f 0) / s) (𝓝[>] 0) (𝓝 d) := by
  have hIoi : Set.Ioi (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext x; simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact ne_of_gt
  have h := hasDerivWithinAt_iff_tendsto_slope.1 hd; rw [hIoi] at h
  exact h.congr fun s ↦ by simp [slope_def_field]
/-- **Concave secant upper bound from right derivative at `0`**. -/
theorem slope_le_of_concaveOn_of_hasDerivWithinAt_Ioi {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) {d : ℝ} (hd : HasDerivWithinAt f d (Set.Ioi 0) 0)
    {t : ℝ} (ht : 0 < t) : (f t - f 0) / t ≤ d := by
  refine ge_of_tendsto (tendsto_slope_zero_of_hasDerivWithinAt_Ioi hd) ?_
  filter_upwards [Ioo_mem_nhdsGT ht] with s hs
  exact antitoneOn_slope_Ioi_of_concaveOn hf hs.1 ht hs.2.le
/-- **Concave tangent upper bound on `[0, ∞)`** from `HasDerivWithinAt f d (Set.Ioi 0) 0`. -/
theorem le_tangent_of_concaveOn_of_hasDerivWithinAt_Ioi {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) {d : ℝ} (hd : HasDerivWithinAt f d (Set.Ioi 0) 0)
    {t : ℝ} (ht : 0 ≤ t) : f t ≤ f 0 + d * t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp
  · linarith [(div_le_iff₀ hpos).1 (slope_le_of_concaveOn_of_hasDerivWithinAt_Ioi hf hd hpos)]
/-- **Concave tangent upper bound on `[0, ∞)`** from `HasDerivWithinAt f d (Set.Ici 0) 0`. -/
theorem le_tangent_of_concaveOn_of_hasDerivWithinAt {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) {d : ℝ} (hd : HasDerivWithinAt f d (Set.Ici 0) 0)
    {t : ℝ} (ht : 0 ≤ t) : f t ≤ f 0 + d * t :=
  le_tangent_of_concaveOn_of_hasDerivWithinAt_Ioi hf (hd.mono Set.Ioi_subset_Ici_self) ht
/-- If `f 0 + c * t ≤ f t` for `t ≥ 0` and `HasDerivWithinAt f d (Set.Ioi 0) 0`, then `c ≤ d`. -/
theorem le_deriv_of_ge_linear_of_hasDerivWithinAt_Ioi {f : ℝ → ℝ} {c d : ℝ}
    (hlin : ∀ t ≥ 0, f 0 + c * t ≤ f t) (hd : HasDerivWithinAt f d (Set.Ioi 0) 0) : c ≤ d := by
  refine ge_of_tendsto (tendsto_slope_zero_of_hasDerivWithinAt_Ioi hd) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [le_div_iff₀ hs]; linarith [hlin s hs.le]
/-- **Concave tangent linear rigidity theorem (`Set.Ioi 0` derivative form)**. -/
theorem eq_linear_of_concaveOn_of_ge_linear_of_hasDerivWithinAt_Ioi {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) {c d : ℝ} (hlin : ∀ t ≥ 0, f 0 + c * t ≤ f t)
    (hd : HasDerivWithinAt f d (Set.Ioi 0) 0) (hdc : d ≤ c) :
    d = c ∧ ∀ t ≥ 0, f t = f 0 + c * t := by
  have heq : d = c := le_antisymm hdc (le_deriv_of_ge_linear_of_hasDerivWithinAt_Ioi hlin hd)
  refine ⟨heq, fun t ht ↦ le_antisymm ?_ (hlin t ht)⟩
  simpa [heq] using le_tangent_of_concaveOn_of_hasDerivWithinAt_Ioi hf hd ht
/-- **Concave tangent linear rigidity theorem (`Set.Ici 0` derivative form)**. -/
theorem eq_linear_of_concaveOn_of_ge_linear_of_hasDerivWithinAt {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) {c d : ℝ} (hlin : ∀ t ≥ 0, f 0 + c * t ≤ f t)
    (hd : HasDerivWithinAt f d (Set.Ici 0) 0) (hdc : d ≤ c) :
    d = c ∧ ∀ t ≥ 0, f t = f 0 + c * t :=
  eq_linear_of_concaveOn_of_ge_linear_of_hasDerivWithinAt_Ioi hf hlin
    (hd.mono Set.Ioi_subset_Ici_self) hdc
/-- **Derivative-free concave linear rigidity theorem** from small secant slopes. -/
theorem eq_linear_of_concaveOn_of_ge_linear_of_forall_pos_exists_slope_le {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) {c : ℝ} (hlin : ∀ t ≥ 0, f 0 + c * t ≤ f t)
    (h_eps : ∀ ε > 0, ∀ δ > 0, ∃ s ∈ Set.Ioo 0 δ, (f s - f 0) / s ≤ c + ε) {t : ℝ}
    (ht : 0 ≤ t) : f t = f 0 + c * t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp
  · refine le_antisymm ?_ (hlin t ht)
    suffices (f t - f 0) / t ≤ c by linarith [(div_le_iff₀ hpos).1 this]
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨s, ⟨hs0, hst⟩, hs_le⟩ := h_eps ε hε t hpos
    exact (antitoneOn_slope_Ioi_of_concaveOn hf hs0 hpos hst.le).trans hs_le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- The `1 / dim E`-th root of the outer parallel measure:
`outerParallelRoot μ K t = (μ (outerParallel K t)).toReal ^ (1 / (Module.finrank ℝ E : ℝ))`. -/
def outerParallelRoot (μ : Measure E := by volume_tac) (K : Set E) (t : ℝ) : ℝ :=
  (μ (outerParallel K t)).toReal ^ (1 / (Module.finrank ℝ E : ℝ))
/-- The `1 / n`-th root of the parallel volume on `EuclideanSpace ℝ (Fin n)`:
`parallelVolumeRoot n K t = (volume (K + t • closedBall 0 1)).toReal ^ (1 / (n : ℝ))`. -/
def parallelVolumeRoot (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) : ℝ :=
  (volume (K + t • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ))
@[simp] theorem outerParallelRoot_zero (μ : Measure E) (K : Set E) :
    outerParallelRoot μ K 0 = (μ K).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  simp [outerParallelRoot]
@[simp] theorem parallelVolumeRoot_zero (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) :
    parallelVolumeRoot n K 0 = (volume K).toReal ^ (1 / (n : ℝ)) := by
  have h0 : (0 : ℝ) • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 = {0} :=
    zero_smul_set (Metric.nonempty_closedBall.2 zero_le_one)
  simp [parallelVolumeRoot, h0]
theorem outerParallelRoot_nonneg (μ : Measure E) (K : Set E) (t : ℝ) :
    0 ≤ outerParallelRoot μ K t := Real.rpow_nonneg ENNReal.toReal_nonneg _
theorem parallelVolumeRoot_nonneg (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    0 ≤ parallelVolumeRoot n K t := Real.rpow_nonneg ENNReal.toReal_nonneg _
/-- `parallelVolumeRoot n K t` agrees with `outerParallelRoot volume K t`. -/
theorem parallelVolumeRoot_eq_outerParallelRoot (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (t : ℝ) : parallelVolumeRoot n K t = outerParallelRoot volume K t := by
  simp [parallelVolumeRoot, outerParallelRoot, outerParallel]
private theorem nontrivial_eucl {n : ℕ} (hn : 1 ≤ n) :
    Nontrivial (EuclideanSpace ℝ (Fin n)) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using Nat.pos_of_ne_zero (by omega))

variable [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]

/-- **Extended-real concavity of `t ↦ μ (outerParallel K t) ^ (1 / dim E)`** for convex `K`. -/
theorem _root_.Convex.measure_outerParallel_combo_rpow_inv_finrank_ge {K : Set E}
    (hK_ne : K.Nonempty) (hK : Convex ℝ K) {a b s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ENNReal.ofReal a * μ (outerParallel K s) ^ (1 / (Module.finrank ℝ E : ℝ)) +
        ENNReal.ofReal b * μ (outerParallel K t) ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      μ (outerParallel K (a * s + b * t)) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rw [← hK.smul_outerParallel_add_smul_outerParallel ha hb hab hs ht, eq_sub_of_add_eq hab]
  exact measure_smul_add_smul_rpow_inv_finrank_ge_of_nullMeasurableSet μ Module.finrank_pos
    hb (by linarith) (Nonempty.outerParallel hK_ne s) ((hK.outerParallel s).nullMeasurableSet μ)
    (Nonempty.outerParallel hK_ne t) ((hK.outerParallel t).nullMeasurableSet μ)

/-- **Concavity of `outerParallelRoot μ K` on `[0, ∞)`** for nonempty bounded convex `K ⊆ E`. -/
theorem concaveOn_outerParallelRoot {K : Set E} (hK_ne : K.Nonempty) (hK : Convex ℝ K)
    (hK_bdd : Bornology.IsBounded K) :
    ConcaveOn ℝ (Set.Ici 0) (outerParallelRoot μ K) := by
  refine ⟨convex_Ici 0, fun s (hs : 0 ≤ s) t (ht : 0 ≤ t) a b ha hb hab ↦ ?_⟩
  have hp : 0 ≤ 1 / (Module.finrank ℝ E : ℝ) := by positivity
  have hrpow_fin (r : ℝ) : μ (outerParallel K r) ^ (1 / (Module.finrank ℝ E : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp (isBounded_outerParallel hK_bdd r).measure_lt_top.ne
  have h1 := ENNReal.mul_ne_top (a := ENNReal.ofReal a) ENNReal.ofReal_ne_top (hrpow_fin s)
  have h2 := ENNReal.mul_ne_top (a := ENNReal.ofReal b) ENNReal.ofReal_ne_top (hrpow_fin t)
  have htr := ENNReal.toReal_mono (hrpow_fin (a * s + b * t))
    (hK.measure_outerParallel_combo_rpow_inv_finrank_ge (μ := μ) hK_ne ha hb hab hs ht)
  rw [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at htr
  simpa [outerParallelRoot, smul_eq_mul] using htr

/-- **Brunn–Minkowski linear lower bound for `outerParallelRoot μ K`** with `closedBall 0 1`. -/
theorem outerParallelRoot_ge_linear_closedBall {K : Set E} (hK_ne : K.Nonempty)
    (hK_m : NullMeasurableSet K μ) (hK_bdd : Bornology.IsBounded K) {t : ℝ} (ht : 0 ≤ t) :
    outerParallelRoot μ K 0 +
        t * (μ (Metric.closedBall (0 : E) 1)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      outerParallelRoot μ K t := by
  have hp : 0 ≤ 1 / (Module.finrank ℝ E : ℝ) := by positivity
  have ht_fin : μ (outerParallel K t) ^ (1 / (Module.finrank ℝ E : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp (isBounded_outerParallel hK_bdd t).measure_lt_top.ne
  have hK_fin : μ K ^ (1 / (Module.finrank ℝ E : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp hK_bdd.measure_lt_top.ne
  have hB_fin : ENNReal.ofReal t *
      μ (Metric.closedBall (0 : E) 1) ^ (1 / (Module.finrank ℝ E : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp (isCompact_closedBall (0 : E) 1).measure_lt_top.ne)
  have htr := ENNReal.toReal_mono ht_fin
    (measure_outerParallel_rpow_inv_finrank_ge (μ := μ) hK_ne hK_m ht)
  rw [ENNReal.toReal_add hK_fin hB_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at htr
  simpa [outerParallelRoot] using htr
/-- **Brunn–Minkowski linear lower bound for `outerParallelRoot μ K`** with `Metric.ball 0 1`. -/
theorem outerParallelRoot_ge_linear {K : Set E} (hK_ne : K.Nonempty)
    (hK_m : NullMeasurableSet K μ) (hK_bdd : Bornology.IsBounded K) {t : ℝ} (ht : 0 ≤ t) :
    outerParallelRoot μ K 0 +
        t * (μ (Metric.ball (0 : E) 1)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      outerParallelRoot μ K t := by
  rw [← measure_closedBall_unit_eq_ball]
  exact outerParallelRoot_ge_linear_closedBall hK_ne hK_m hK_bdd ht
/-- **Concavity of `parallelVolumeRoot n K` on `Set.Ici 0`** (`1 ≤ n`). -/
theorem concaveOn_parallelVolumeRoot {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_ne : K.Nonempty) (hK : Convex ℝ K)
    (hK_bdd : Bornology.IsBounded K) :
    ConcaveOn ℝ (Set.Ici 0) (parallelVolumeRoot n K) := by
  have := nontrivial_eucl hn
  refine (concaveOn_outerParallelRoot (μ := volume) hK_ne hK hK_bdd).congr ?_
  intro t _; exact (parallelVolumeRoot_eq_outerParallelRoot n K t).symm
/-- **Brunn–Minkowski linear lower bound for `parallelVolumeRoot n K`** with `closedBall 0 1`. -/
theorem parallelVolumeRoot_ge_linear {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_ne : K.Nonempty)
    (hK_m : NullMeasurableSet K volume) (hK_bdd : Bornology.IsBounded K) {t : ℝ} (ht : 0 ≤ t) :
    parallelVolumeRoot n K 0 +
        t * (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) ≤
      parallelVolumeRoot n K t := by
  have := nontrivial_eucl hn
  rw [parallelVolumeRoot_zero, parallelVolumeRoot_eq_outerParallelRoot n K t]
  simpa using outerParallelRoot_ge_linear_closedBall (μ := volume) hK_ne hK_m hK_bdd ht
/-- **Brunn–Minkowski linear lower bound for `parallelVolumeRoot n K`** with `Metric.ball 0 1`. -/
theorem parallelVolumeRoot_ge_linear_ball {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_ne : K.Nonempty)
    (hK_m : NullMeasurableSet K volume) (hK_bdd : Bornology.IsBounded K) {t : ℝ} (ht : 0 ≤ t) :
    parallelVolumeRoot n K 0 +
        t * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) ≤
      parallelVolumeRoot n K t := by
  rw [← measure_closedBall_unit_eq_ball]
  exact parallelVolumeRoot_ge_linear hn hK_ne hK_m hK_bdd ht
omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- **Right derivative of `outerParallelRoot μ K` at `t = 0+`**. -/
theorem hasDerivWithinAt_outerParallelRoot {K : Set E} (hK_pos : 0 < (μ K).toReal) {S : ℝ}
    (hderiv : HasDerivWithinAt (fun t : ℝ ↦ (μ (outerParallel K t)).toReal) S (Set.Ici 0) 0) :
    HasDerivWithinAt (outerParallelRoot μ K)
      (S / ((Module.finrank ℝ E : ℝ) *
        (μ K).toReal ^ (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ))))
      (Set.Ici 0) 0 := by
  set n : ℝ := (Module.finrank ℝ E : ℝ); have hn : 0 < n := Nat.cast_pos.2 Module.finrank_pos
  have hrpow := hderiv.rpow_const (p := 1 / n) (Or.inl (by simpa using hK_pos.ne'))
  have h_eq : S * (1 / n) * (μ (outerParallel K 0)).toReal ^ (1 / n - 1) =
      S / (n * (μ K).toReal ^ ((n - 1) / n)) := by
    have hexp : 1 / n - 1 = -((n - 1) / n) := by field_simp; ring
    rw [outerParallel_zero, hexp, Real.rpow_neg hK_pos.le]; field_simp
  rwa [h_eq] at hrpow
/-- **Right derivative of `parallelVolumeRoot n K` at `t = 0+`** on `EuclideanSpace ℝ (Fin n)`. -/
theorem hasDerivWithinAt_parallelVolumeRoot {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_pos : 0 < (volume K).toReal) {S : ℝ}
    (hderiv : HasDerivWithinAt (fun t : ℝ ↦ (volume (outerParallel K t)).toReal) S (Set.Ici 0) 0) :
    HasDerivWithinAt (parallelVolumeRoot n K)
      (S / ((n : ℝ) * (volume K).toReal ^ (((n : ℝ) - 1) / (n : ℝ)))) (Set.Ici 0) 0 := by
  have := nontrivial_eucl hn
  have hd := hasDerivWithinAt_outerParallelRoot (μ := volume) hK_pos hderiv
  simp only [finrank_euclideanSpace_fin] at hd
  exact hd.congr (fun t _ ↦ parallelVolumeRoot_eq_outerParallelRoot n K t)
    (parallelVolumeRoot_eq_outerParallelRoot n K 0)
/-- **Minkowski-content isoperimetric inequality for convex bodies (real-valued form)**. -/
theorem isoperimetric_minkowskiContent_of_convex {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_ne : K.Nonempty) (hK : Convex ℝ K)
    (hK_fin : volume K ≠ ⊤) (hM_fin : lowerMinkowskiContent volume K ≠ ⊤) :
    (n : ℝ) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) *
        (volume K).toReal ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      (lowerMinkowskiContent volume K).toReal := by
  have := nontrivial_eucl hn
  have htr := ENNReal.toReal_mono hM_fin
    (lowerMinkowskiContent_ge_isoperimetric (μ := volume) hK_ne
      (hK.nullMeasurableSet volume) hK_fin)
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simp [Nat.cast_sub hn]
  simp only [finrank_euclideanSpace_fin] at htr
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, hsub] at htr

/-- **Concave tangent linear rigidity for `outerParallelRoot μ K` under isoperimetric equality**. -/
theorem outerParallelRoot_eq_linear_of_hasDerivWithinAt {K : Set E} (hK : Convex ℝ K)
    (hK_bdd : Bornology.IsBounded K) (hK_pos : 0 < (μ K).toReal) {S : ℝ}
    (hderiv : HasDerivWithinAt (fun t : ℝ ↦ (μ (outerParallel K t)).toReal) S (Set.Ici 0) 0)
    (hS : S ≤ (Module.finrank ℝ E : ℝ) *
      (μ (Metric.ball (0 : E) 1)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) *
      (μ K).toReal ^ (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ))) :
    S = (Module.finrank ℝ E : ℝ) *
        (μ (Metric.ball (0 : E) 1)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) *
        (μ K).toReal ^ (((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ)) ∧
      ∀ t ≥ 0, outerParallelRoot μ K t = outerParallelRoot μ K 0 +
        t * (μ (Metric.ball (0 : E) 1)).toReal ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have hK_ne : K.Nonempty := nonempty_of_measure_ne_zero (ENNReal.toReal_pos_iff.1 hK_pos).1.ne'
  set n : ℝ := (Module.finrank ℝ E : ℝ); set c : ℝ := (μ (Metric.ball (0 : E) 1)).toReal ^ (1 / n)
  set denom : ℝ := n * (μ K).toReal ^ ((n - 1) / n)
  have hdenom_pos : 0 < denom :=
    mul_pos (Nat.cast_pos.2 Module.finrank_pos) (Real.rpow_pos_of_pos hK_pos _)
  have hdc : S / denom ≤ c := (div_le_iff₀ hdenom_pos).2 (by linarith)
  have hlin : ∀ t ≥ 0, outerParallelRoot μ K 0 + c * t ≤ outerParallelRoot μ K t := fun t ht ↦ by
    simpa [c, n, mul_comm] using
      outerParallelRoot_ge_linear hK_ne (hK.nullMeasurableSet μ) hK_bdd ht
  obtain ⟨hd_eq, hfun_eq⟩ := eq_linear_of_concaveOn_of_ge_linear_of_hasDerivWithinAt
    (concaveOn_outerParallelRoot hK_ne hK hK_bdd) hlin
    (hasDerivWithinAt_outerParallelRoot hK_pos hderiv) hdc
  refine ⟨?_, fun t ht ↦ by simpa [c, n, mul_comm] using hfun_eq t ht⟩
  have h1 := (div_eq_iff hdenom_pos.ne').1 hd_eq; linarith

/-- **Concave tangent linear rigidity for `parallelVolumeRoot n K` under Minkowski-content
isoperimetric equality**: `parallelVolumeRoot n K t = parallelVolumeRoot n K 0 + t * ω_n^(1/n)`. -/
theorem parallelVolumeRoot_eq_linear_of_minkowskiContent_eq {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hK_bdd : Bornology.IsBounded K) (hK_pos : 0 < (volume K).toReal) {S : ℝ}
    (hderiv : HasDerivWithinAt (fun t : ℝ ↦ (volume (outerParallel K t)).toReal) S (Set.Ici 0) 0)
    (hM_eq : (lowerMinkowskiContent volume K).toReal ≤
      (n : ℝ) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) *
        (volume K).toReal ^ (((n : ℝ) - 1) / (n : ℝ))) {t : ℝ} (ht : 0 ≤ t) :
    parallelVolumeRoot n K t = parallelVolumeRoot n K 0 +
      t * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) := by
  have := nontrivial_eucl hn
  have h0 : ∀ r ≥ 0, (volume (outerParallel K 0)).toReal + 0 * r ≤
      (volume (outerParallel K r)).toReal := fun r _ ↦ by
    simpa using ENNReal.toReal_mono (isBounded_outerParallel hK_bdd r).measure_lt_top.ne
      (measure_mono (self_subset_outerParallel K r))
  have hS_nonneg : 0 ≤ S :=
    le_deriv_of_ge_linear_of_hasDerivWithinAt_Ioi h0 (hderiv.mono Set.Ioi_subset_Ici_self)
  have hM_S : (lowerMinkowskiContent volume K).toReal = S := by
    rw [lowerMinkowskiContent_eq_of_hasDerivWithinAt_of_isBounded hK_bdd hderiv,
      ENNReal.toReal_ofReal hS_nonneg]
  have hS_le : S ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^
        (1 / (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)) *
      (volume K).toReal ^ (((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) /
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)) := by
    simpa [finrank_euclideanSpace_fin, hM_S] using hM_eq
  have h := (outerParallelRoot_eq_linear_of_hasDerivWithinAt hK hK_bdd hK_pos hderiv hS_le).2 t ht
  rw [parallelVolumeRoot_eq_outerParallelRoot n K t, h, outerParallelRoot_zero,
    parallelVolumeRoot_zero, finrank_euclideanSpace_fin]

/-- Exact linearity of `parallelVolumeRoot n (Metric.closedBall c r)` on `t ≥ 0` for `r > 0`. -/
theorem parallelVolumeRoot_closedBall {n : ℕ} (hn : 1 ≤ n)
    (c : EuclideanSpace ℝ (Fin n)) {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    parallelVolumeRoot n (Metric.closedBall c r) t =
      parallelVolumeRoot n (Metric.closedBall c r) 0 +
        t * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 hn; have hrt : 0 ≤ r + t := by linarith
  rw [parallelVolumeRoot_eq_outerParallelRoot n _ t, outerParallelRoot,
    outerParallel_closedBall c hr.le ht, parallelVolumeRoot_zero,
    Measure.addHaar_closedBall volume c hrt, Measure.addHaar_closedBall volume c hr.le,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hrt n), ENNReal.toReal_ofReal (pow_nonneg hr.le n),
    Real.mul_rpow (pow_nonneg hrt n) ENNReal.toReal_nonneg,
    Real.mul_rpow (pow_nonneg hr.le n) ENNReal.toReal_nonneg,
    ← Real.rpow_natCast, ← Real.rpow_mul hrt, ← Real.rpow_natCast, ← Real.rpow_mul hr.le,
    mul_one_div_cancel hn_pos.ne', Real.rpow_one, Real.rpow_one, add_mul]

/-- Exact linearity of `parallelVolumeRoot n (Metric.ball c r)` on `t ≥ 0` for `r > 0`. -/
theorem parallelVolumeRoot_ball {n : ℕ} (hn : 1 ≤ n)
    (c : EuclideanSpace ℝ (Fin n)) {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    parallelVolumeRoot n (Metric.ball c r) t =
      parallelVolumeRoot n (Metric.ball c r) 0 +
        t * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (1 / (n : ℝ)) := by
  have := nontrivial_eucl hn
  have h_eq : parallelVolumeRoot n (Metric.ball c r) t =
      parallelVolumeRoot n (Metric.closedBall c r) t := by
    rw [parallelVolumeRoot_eq_outerParallelRoot, parallelVolumeRoot_eq_outerParallelRoot,
      outerParallelRoot, outerParallelRoot, outerParallel_ball c hr ht,
      outerParallel_closedBall c hr.le ht,
      measure_congr (closedBall_ae_eq_ball (μ := volume) c (r + t))]
  have h0_eq : parallelVolumeRoot n (Metric.ball c r) 0 =
      parallelVolumeRoot n (Metric.closedBall c r) 0 := by
    rw [parallelVolumeRoot_zero, parallelVolumeRoot_zero,
      measure_congr (closedBall_ae_eq_ball (μ := volume) c r)]
  rw [h_eq, h0_eq, parallelVolumeRoot_closedBall hn c hr ht]
/-- Any set `s =ᵐ[ν] Metric.ball c r` has the same `ν`-measure as `Metric.ball c r`. -/
theorem volume_eq_of_ae_eq_ball {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V]
    {ν : Measure V} {s : Set V} {c : V} {r : ℝ} (hs : s =ᵐ[ν] Metric.ball c r) :
    ν s = ν (Metric.ball c r) := measure_congr hs
/-- Any set `s =ᵐ[ν] Metric.ball c r` has the same Caccioppoli perimeter as `Metric.ball c r`. -/
theorem perimeter_eq_of_ae_eq_ball {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] {ν : Measure V} {s : Set V} {c : V} {r : ℝ}
    (hs : s =ᵐ[ν] Metric.ball c r) : perimeter ν s = perimeter ν (Metric.ball c r) :=
  perimeter_congr_ae hs
/-- **Converse isoperimetric equality for sets a.e.-equal to an open ball** (`r > 0`). -/
theorem isoperimetric_equality_of_ae_eq_ball {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {ν : Measure V} [ν.IsAddHaarMeasure] [Nontrivial V] {s : Set V} {c : V} {r : ℝ}
    (hr : 0 < r) (hs : s =ᵐ[ν] Metric.ball c r) :
    perimeter ν s ^ Module.finrank ℝ V =
      (Module.finrank ℝ V : ℝ≥0∞) ^ Module.finrank ℝ V * ν (Metric.ball (0 : V) 1) *
        ν s ^ (Module.finrank ℝ V - 1) := by
  rw [perimeter_eq_of_ae_eq_ball hs, volume_eq_of_ae_eq_ball hs, perimeter_ball_pow_finrank c hr]

end ParallelVolumeConcavityAndRigidity

/-! ### Section 3: Steiner-to-convex rigidity reduction -/

section SteinerToConvexReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Steiner symmetrization perimeter equality forcing**. -/
theorem perimeter_steinerSymmetrization_eq_of_isoperimetric_eq {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) {C : ℝ≥0∞} {p : ℝ}
    (hrec : perimeter volume (steinerSymmetrization e s) ≤ perimeter volume s)
    (hiso : C * volume (steinerSymmetrization e s) ^ p ≤
      perimeter volume (steinerSymmetrization e s))
    (heq : perimeter volume s = C * volume s ^ p) :
    perimeter volume (steinerSymmetrization e s) = perimeter volume s := by
  refine le_antisymm hrec ?_; rw [heq, ← volume_steinerSymmetrization₀ he hs]; exact hiso
/-- **Dimensional `n`-th power form of Steiner perimeter equality forcing**. -/
theorem perimeter_steinerSymmetrization_eq_of_pow_finrank_eq [Nontrivial E] {e : E} (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume)
    (hrec : perimeter volume (steinerSymmetrization e s) ≤ perimeter volume s)
    (hiso : (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * volume (Metric.ball (0 : E) 1) *
        volume (steinerSymmetrization e s) ^ (Module.finrank ℝ E - 1) ≤
      perimeter volume (steinerSymmetrization e s) ^ Module.finrank ℝ E)
    (heq : perimeter volume s ^ Module.finrank ℝ E =
      (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * volume (Metric.ball (0 : E) 1) *
        volume s ^ (Module.finrank ℝ E - 1)) :
    perimeter volume (steinerSymmetrization e s) = perimeter volume s := by
  set n := Module.finrank ℝ E; have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 Module.finrank_pos
  refine le_antisymm hrec ?_
  have hpow : perimeter volume s ^ n ≤ perimeter volume (steinerSymmetrization e s) ^ n := by
    rw [heq, ← volume_steinerSymmetrization₀ he hs]; exact hiso
  have h1 := ENNReal.rpow_le_rpow hpow (by positivity : 0 ≤ 1 / (n : ℝ))
  rwa [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hn_pos.ne',
    ENNReal.rpow_one, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    mul_one_div_cancel hn_pos.ne', ENNReal.rpow_one] at h1

/-- If `F : Set ℝ` is a.e.-equal to an `OrdConnected` set `I`, then for any `h : ℝ` and
`a, b ≥ 0` with `a + b = 1`, `{τ ∈ F | τ + h ∈ F ∧ τ + b * h ∉ F}` has measure zero. -/
theorem volume_inter_preimage_add_diff_eq_zero_of_ae_eq_ordConnected {F I : Set ℝ}
    (hI : I.OrdConnected) (hFI : F =ᵐ[volume] I) (h : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    volume ((F ∩ (fun τ : ℝ ↦ τ + h) ⁻¹' F) \ (fun τ : ℝ ↦ τ + b * h) ⁻¹' F) = 0 := by
  have h1 := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hFI
  have h2 := (measurePreserving_add_right volume (b * h)).quasiMeasurePreserving.ae_eq_comp hFI
  have hae : (F ∩ (fun τ : ℝ ↦ τ + h) ⁻¹' F) \ (fun τ : ℝ ↦ τ + b * h) ⁻¹' F =ᵐ[volume]
      (I ∩ (fun τ : ℝ ↦ τ + h) ⁻¹' I) \ (fun τ : ℝ ↦ τ + b * h) ⁻¹' I := (hFI.inter h1).diff h2
  have hemp : (I ∩ (fun τ : ℝ ↦ τ + h) ⁻¹' I) \ (fun τ : ℝ ↦ τ + b * h) ⁻¹' I = ∅ := by
    ext τ; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false,
      iff_false, not_and, not_not]; intro ⟨hτ0, hτ1⟩
    have hcomb := hI.convex hτ0 hτ1 ha hb hab
    have heq : a • τ + b • (τ + h) = τ + b * h := by
      simp only [smul_eq_mul]; linear_combination τ * hab
    rwa [heq] at hcomb
  rw [measure_congr hae, hemp, measure_empty]

/-- If `s : Set E` is `NullMeasurableSet` and in unit direction `e` (`‖e‖ = 1`) a.e. 1D fiber is
a.e. `OrdConnected`, then `volume ((s ∩ (· + h • e) ⁻¹' s) \ (· + (b * h) • e) ⁻¹' s) = 0`. -/
theorem volume_inter_preimage_add_smul_diff_eq_zero_of_ae_ordConnected_steinerFiber
    {e : E} (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume)
    (hord : ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ steinerFiber e s y =ᵐ[volume] I)
    (h : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    volume ((s ∩ (fun x : E ↦ x + h • e) ⁻¹' s) \ (fun x : E ↦ x + (b * h) • e) ⁻¹' s) = 0 := by
  let N : Set E := (s ∩ (fun x : E ↦ x + h • e) ⁻¹' s) \ (fun x : E ↦ x + (b * h) • e) ⁻¹' s
  have hpe := (measurePreserving_add_right volume (h • e)).quasiMeasurePreserving
  have hpbe := (measurePreserving_add_right volume ((b * h) • e)).quasiMeasurePreserving
  have hN_nm : NullMeasurableSet N volume := (hs.inter (hs.preimage hpe)).diff (hs.preimage hpbe)
  rw [volume_eq_lintegral_steinerFiber₀ he hN_nm, lintegral_eq_zero_iff'
    (aemeasurable_volume_steinerFiber₀ he hN_nm)]
  filter_upwards [hord] with y ⟨I, hI, hyI⟩
  have hfib : steinerFiber e N y =
      (steinerFiber e s y ∩ (fun τ : ℝ ↦ τ + h) ⁻¹' steinerFiber e s y) \
        (fun τ : ℝ ↦ τ + b * h) ⁻¹' steinerFiber e s y := by
    ext τ; simp only [N, steinerFiber_sdiff, steinerFiber_inter, Set.mem_sdiff, Set.mem_inter_iff,
      mem_steinerFiber_iff, Set.mem_preimage, add_assoc, ← add_smul]
  rw [hfib]; exact volume_inter_preimage_add_diff_eq_zero_of_ae_eq_ordConnected hI hyI h ha hb hab

/-- **Ball-complement subadditivity along convex combinations** under a.e. `OrdConnected` fibers. -/
theorem volume_compl_inter_closedBall_combo_le {s : Set E} (hs : NullMeasurableSet s volume)
    (hord : ∀ e : E, ‖e‖ = 1 → ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ steinerFiber e s y =ᵐ[volume] I)
    (x₀ x₁ : E) (r : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    volume (sᶜ ∩ Metric.closedBall (a • x₀ + b • x₁) r) ≤
      volume (sᶜ ∩ Metric.closedBall x₀ r) + volume (sᶜ ∩ Metric.closedBall x₁ r) := by
  rcases eq_or_ne x₀ x₁ with rfl | hne
  · rw [← add_smul, hab, one_smul]; exact le_self_add
  · set h : ℝ := ‖x₁ - x₀‖; have hh : 0 < h := norm_sub_pos_iff.2 hne.symm
    let e : E := h⁻¹ • (x₁ - x₀); let xb : E := a • x₀ + b • x₁
    have he : ‖e‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh, inv_mul_cancel₀ hh.ne']
    have hhe : h • e = x₁ - x₀ := smul_inv_smul₀ hh.ne' (x₁ - x₀)
    have hxb : xb = x₀ + (b * h) • e := by
      rw [mul_smul, hhe]; dsimp only [xb]
      rw [eq_sub_of_add_eq hab, sub_smul, one_smul, smul_sub]; abel
    have hx1 : x₁ = x₀ + h • e := by rw [hhe, add_sub_cancel]
    let N : Set E := (s ∩ (fun x : E ↦ x + h • e) ⁻¹' s) \ (fun x : E ↦ x + (b * h) • e) ⁻¹' s
    have hN_pre : volume ((fun w : E ↦ x₀ + w) ⁻¹' N) = 0 := by
      rw [measure_preimage_add,
        volume_inter_preimage_add_smul_diff_eq_zero_of_ae_ordConnected_steinerFiber
          he hs (hord e he) h ha hb hab]
    have htr (z : E) : volume (sᶜ ∩ Metric.closedBall z r) =
        volume ((fun w : E ↦ z + w) ⁻¹' sᶜ ∩ Metric.closedBall 0 r) := by
      rw [← measure_preimage_add volume z (sᶜ ∩ Metric.closedBall z r)]
      congr 1; ext w; simp [Metric.mem_closedBall, dist_eq_norm]
    rw [htr xb, htr x₀, htr x₁]
    have hsub : (fun w : E ↦ xb + w) ⁻¹' sᶜ ∩ Metric.closedBall 0 r ⊆
        ((fun w : E ↦ x₀ + w) ⁻¹' sᶜ ∩ Metric.closedBall 0 r) ∪
          ((fun w : E ↦ x₁ + w) ⁻¹' sᶜ ∩ Metric.closedBall 0 r) ∪
          (fun w : E ↦ x₀ + w) ⁻¹' N := by
      intro w ⟨hw_xb, hw_ball⟩
      by_cases hw0 : x₀ + w ∈ s
      · by_cases hw1 : x₁ + w ∈ s
        · refine Or.inr ⟨⟨hw0, ?_⟩, ?_⟩
          · have heq : x₀ + w + h • e = x₁ + w := by rw [hx1]; abel
            change x₀ + w + h • e ∈ s; rwa [heq]
          · have heq : x₀ + w + (b * h) • e = xb + w := by rw [hxb]; abel
            change x₀ + w + (b * h) • e ∉ s; rwa [heq]
        · exact Or.inl (Or.inr ⟨hw1, hw_ball⟩)
      · exact Or.inl (Or.inl ⟨hw0, hw_ball⟩)
    refine ((measure_mono hsub).trans (measure_union_le _ _)).trans ?_
    rw [hN_pre, add_zero]; exact measure_union_le _ _

/-- **Essential convexity theorem (`essentialInterior` form)**: if `s : Set E` is
`NullMeasurableSet` and in every unit direction `e` almost every 1D fiber is a.e. `OrdConnected`,
then `Convex ℝ (essentialInterior volume s)`. -/
theorem convex_essentialInterior_of_ae_ordConnected_steinerFiber {s : Set E}
    (hs : NullMeasurableSet s volume)
    (hord : ∀ e : E, ‖e‖ = 1 → ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ steinerFiber e s y =ᵐ[volume] I) :
    Convex ℝ (essentialInterior volume s) := by
  intro x₀ hx₀ x₁ hx₁ a b ha hb hab
  rw [mem_essentialInterior_iff, ← hasMeasureDensityAt_compl_zero_iff hs] at hx₀ hx₁ ⊢
  have hsum : Tendsto
      (fun r : ℝ ↦ volume (sᶜ ∩ Metric.closedBall x₀ r) / volume (Metric.closedBall x₀ r) +
        volume (sᶜ ∩ Metric.closedBall x₁ r) / volume (Metric.closedBall x₁ r))
      (𝓝[>] 0) (𝓝 0) := by simpa using hx₀.add hx₁
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ _root_.zero_le) fun r ↦ ?_
  have hball (z : E) : volume (Metric.closedBall z r) = volume (Metric.closedBall (0 : E) r) :=
    Measure.addHaar_closedBall_center volume z r
  rw [hball (a • x₀ + b • x₁), hball x₀, hball x₁, ← ENNReal.add_div]
  exact ENNReal.div_le_div_right
    (volume_compl_inter_closedBall_combo_le hs hord x₀ x₁ r ha hb hab) _

/-- **Multi-directional essential convexity theorem**: if `s : Set E` is `NullMeasurableSet` and
in every unit direction `e` almost every 1D fiber is a.e. `OrdConnected`, then there is a convex
set `C ⊆ E` (`C = essentialInterior volume s`) with `s =ᵐ[volume] C`, `volume C = volume s`, and
`perimeter volume C = perimeter volume s`. -/
theorem exists_convex_ae_eq_of_ae_ordConnected_steinerFiber {s : Set E}
    (hs : NullMeasurableSet s volume)
    (hord : ∀ e : E, ‖e‖ = 1 → ∀ᵐ y : orthogonalHyperplane e ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ steinerFiber e s y =ᵐ[volume] I) :
    ∃ C : Set E, Convex ℝ C ∧ (s =ᵐ[volume] C) ∧
      volume C = volume s ∧ perimeter volume C = perimeter volume s := by
  have hae : (essentialInterior volume s : Set E) =ᵐ[volume] s := essentialInterior_ae_eq hs
  exact ⟨essentialInterior volume s,
    convex_essentialInterior_of_ae_ordConnected_steinerFiber hs hord,
    hae.symm, measure_congr hae, perimeter_congr_ae hae⟩

/-- **Steiner-to-convex rigidity reduction theorem**: if `s : Set E` is `NullMeasurableSet` with
`volume s < ⊤` and in every unit direction `e` (`‖e‖ = 1`) the integrated 1D fiber perimeter obeys
`∫⁻ y, perimeter volume (steinerFiber e s y) ≤ 2 * volume {y | 0 < volume (steinerFiber e s y)}`,
then `s` is a.e.-equal to a convex set `C` with `volume C = volume s` and
`perimeter volume C = perimeter volume s`. -/
theorem exists_convex_ae_eq_of_perimeter_steinerSymmetrization_eq_forall {s : Set E}
    (hs : NullMeasurableSet s volume) (htop : volume s < ⊤)
    (hmeas_lt : ∀ e : E, ‖e‖ = 1 →
      volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)} < ⊤)
    (hf_meas : ∀ e : E, ‖e‖ = 1 → AEMeasurable
      (fun y : orthogonalHyperplane e ↦ perimeter volume (steinerFiber e s y)) volume)
    (hle : ∀ e : E, ‖e‖ = 1 →
      (∫⁻ y : orthogonalHyperplane e, perimeter volume (steinerFiber e s y) ∂volume) ≤
        2 * volume {y : orthogonalHyperplane e | 0 < volume (steinerFiber e s y)}) :
    ∃ C : Set E, Convex ℝ C ∧ (s =ᵐ[volume] C) ∧
      volume C = volume s ∧ perimeter volume C = perimeter volume s :=
  exists_convex_ae_eq_of_ae_ordConnected_steinerFiber hs fun e he ↦
    ae_exists_ordConnected_ae_eq_steinerFiber he hs htop (hmeas_lt e he) (hf_meas e he) (hle e he)

end SteinerToConvexReduction

/-! ### Section 4: Topological frontier nullity & regular open point-set ball rigidity -/

section FrontierNullityAndRegularOpenRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Any set `s ⊆ E` with `μH[d] s ≠ ⊤` for some `d < Module.finrank ℝ E` has `μ s = 0`. -/
theorem measure_eq_zero_of_hausdorffMeasure_ne_top {d : ℝ≥0}
    (hd : (d : ℝ) < Module.finrank ℝ E) {s : Set E} (hs : μH[d] s ≠ ⊤) : μ s = 0 := by
  have hμ : μ ≪ μH[(Module.finrank ℝ E : ℝ)] := Measure.absolutelyContinuous_isAddHaarMeasure μ _
  refine measure_zero_of_dimH_lt (μ := μ) (d := (Module.finrank ℝ E : ℝ≥0)) hμ ?_
  exact (dimH_le_of_hausdorffMeasure_ne_top hs).trans_lt (by exact_mod_cast hd)
/-- If `[Nontrivial E]` and `μH[(Module.finrank ℝ E - 1 : ℕ)] (frontier s) ≠ ⊤`, then
`μ (frontier s) = 0`. -/
theorem measure_frontier_eq_zero_of_hausdorffMeasure_sub_one_ne_top [Nontrivial E] {s : Set E}
    (hfront : μH[(Module.finrank ℝ E - 1 : ℕ)] (frontier s) ≠ ⊤) : μ (frontier s) = 0 := by
  have hd : (((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0) : ℝ) < Module.finrank ℝ E := by
    rw [NNReal.coe_natCast]; exact_mod_cast Nat.sub_lt Module.finrank_pos zero_lt_one
  have hfront' : μH[((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0)] (frontier s) ≠ ⊤ := by
    rwa [NNReal.coe_natCast]
  exact measure_eq_zero_of_hausdorffMeasure_ne_top hd hfront'
/-- If `[Nontrivial E]` and `μH[(Module.finrank ℝ E - 1 : ℕ)] (frontier s) < ⊤`, then
`μ (frontier s) = 0`, `NullMeasurableSet s μ`, `interior s =ᵐ[μ] s`, and `closure s =ᵐ[μ] s`. -/
theorem nullMeasurableSet_and_interior_ae_eq_of_hausdorffMeasure_frontier_lt_top [Nontrivial E]
    {s : Set E} (hfront : μH[(Module.finrank ℝ E - 1 : ℕ)] (frontier s) < ⊤) :
    μ (frontier s) = 0 ∧ NullMeasurableSet s μ ∧
      (interior s =ᵐ[μ] s) ∧ (closure s =ᵐ[μ] s) ∧
      μ (interior s) = μ s ∧ μ (closure s) = μ s := by
  have h0 := measure_frontier_eq_zero_of_hausdorffMeasure_sub_one_ne_top (μ := μ) hfront.ne
  have hi := interior_ae_eq_of_null_frontier h0; have hc := closure_ae_eq_of_null_frontier h0
  exact ⟨h0, nullMeasurableSet_of_null_frontier h0, hi, hc, measure_congr hi, measure_congr hc⟩
/-- If `ν (frontier s) = 0`, then `perimeter ν (interior s) = perimeter ν s` and
`perimeter ν (closure s) = perimeter ν s`. -/
theorem perimeter_interior_and_closure_of_null_frontier {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] {ν : Measure V} {s : Set V}
    (hfront : ν (frontier s) = 0) :
    perimeter ν (interior s) = perimeter ν s ∧ perimeter ν (closure s) = perimeter ν s :=
  ⟨perimeter_congr_ae (interior_ae_eq_of_null_frontier hfront),
    perimeter_congr_ae (closure_ae_eq_of_null_frontier hfront)⟩

variable {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A subset `U` of a topological space is **regular open** if `IsOpen U` and
`interior (closure U) = U`. -/
def IsRegularOpen (U : Set X) : Prop := IsOpen U ∧ interior (closure U) = U
theorem isRegularOpen_iff_interior_closure_eq {U : Set X} :
    IsRegularOpen U ↔ interior (closure U) = U :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ isOpen_interior, h⟩⟩
theorem IsRegularOpen.isOpen {U : Set X} (hU : IsRegularOpen U) : IsOpen U := hU.1
theorem IsRegularOpen.interior_closure {U : Set X} (hU : IsRegularOpen U) :
    interior (closure U) = U := hU.2
@[simp] theorem isRegularOpen_empty : IsRegularOpen (∅ : Set X) := ⟨isOpen_empty, by simp⟩
@[simp] theorem isRegularOpen_univ : IsRegularOpen (Set.univ : Set X) := ⟨isOpen_univ, by simp⟩
/-- For any set `s`, `interior (closure s)` is regular open. -/
theorem isRegularOpen_interior_closure (s : Set X) : IsRegularOpen (interior (closure s)) :=
  ⟨isOpen_interior, interior_closure_idem⟩

/-- Every open convex set in a real normed space is regular open. -/
theorem _root_.Convex.isRegularOpen_of_isOpen {U : Set V} (hU_conv : Convex ℝ U)
    (hU_open : IsOpen U) : IsRegularOpen U := by
  refine ⟨hU_open, ?_⟩; rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  · rw [hU_conv.interior_closure_eq_interior_of_nonempty_interior
      (by rwa [hU_open.interior_eq]), hU_open.interior_eq]
/-- For any convex set `K` in a real normed space, `interior K` is regular open. -/
theorem _root_.Convex.isRegularOpen_interior {K : Set V} (hK : Convex ℝ K) :
    IsRegularOpen (interior K) := hK.interior.isRegularOpen_of_isOpen isOpen_interior
/-- **Every open ball `Metric.ball c r` in a real normed space is regular open**. -/
theorem isRegularOpen_ball (c : V) (r : ℝ) : IsRegularOpen (Metric.ball c r) :=
  (convex_ball c r).isRegularOpen_of_isOpen isOpen_ball

variable [MeasurableSpace X] {ν : Measure X} [ν.IsOpenPosMeasure]

/-- If `U` is open with `[IsOpenPosMeasure ν]` and `ν (U \ s) = 0`, then `U ⊆ closure s`. -/
theorem _root_.IsOpen.subset_closure_of_measure_diff_eq_zero {U s : Set X}
    (hU : IsOpen U) (hdiff : ν (U \ s) = 0) : U ⊆ closure s := by
  have h0 : ν (U \ closure s) = 0 :=
    measure_mono_null (Set.sdiff_subset_sdiff_right subset_closure) hdiff
  exact Set.sdiff_eq_empty.1 ((hU.sdiff isClosed_closure).eq_empty_of_measure_zero h0)
/-- If `U₁` and `U₂` are open sets with `[IsOpenPosMeasure ν]` and `U₁ =ᵐ[ν] U₂`, then
`closure U₁ = closure U₂`. -/
theorem _root_.IsOpen.closure_eq_of_ae_eq {U₁ U₂ : Set X}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (h : U₁ =ᵐ[ν] U₂) : closure U₁ = closure U₂ := by
  rw [ae_eq_set] at h
  exact Subset.antisymm
    (closure_minimal (hU₁.subset_closure_of_measure_diff_eq_zero h.1) isClosed_closure)
    (closure_minimal (hU₂.subset_closure_of_measure_diff_eq_zero h.2) isClosed_closure)
/-- **Exact point-set equality of a.e.-equal regular open sets**. -/
theorem eq_of_isRegularOpen_of_ae_eq {U₁ U₂ : Set X}
    (hU₁ : IsRegularOpen U₁) (hU₂ : IsRegularOpen U₂) (h : U₁ =ᵐ[ν] U₂) : U₁ = U₂ := by
  rw [← hU₁.interior_closure, ← hU₂.interior_closure,
    hU₁.isOpen.closure_eq_of_ae_eq hU₂.isOpen h]

variable [MeasurableSpace V] {νV : Measure V} [νV.IsOpenPosMeasure]

/-- **Exact point-set ball rigidity for regular open sets**: if `U` is regular open and
`U =ᵐ[νV] Metric.ball c r`, then `U = Metric.ball c r`. -/
theorem eq_ball_of_isRegularOpen_of_ae_eq_ball {U : Set V} {c : V} {r : ℝ}
    (hU : IsRegularOpen U) (h : U =ᵐ[νV] Metric.ball c r) : U = Metric.ball c r :=
  eq_of_isRegularOpen_of_ae_eq hU (isRegularOpen_ball c r) h
/-- **Exact frontier sphere rigidity for regular open sets** (`r ≠ 0`). -/
theorem frontier_eq_sphere_of_isRegularOpen_of_ae_eq_ball
    {U : Set V} {c : V} {r : ℝ} (hU : IsRegularOpen U) (hr : r ≠ 0)
    (h : U =ᵐ[νV] Metric.ball c r) :
    frontier U = Metric.sphere c r ∧ closure U = Metric.closedBall c r := by
  rw [eq_ball_of_isRegularOpen_of_ae_eq_ball hU h]
  exact ⟨frontier_ball c hr, closure_ball c hr⟩

end FrontierNullityAndRegularOpenRigidity

end TauCeti
