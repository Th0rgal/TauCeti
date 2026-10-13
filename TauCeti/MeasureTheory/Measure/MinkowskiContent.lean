/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.BallPerimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.PrekopaLeindler

/-!
# Outer Parallel Volume, Minkowski Boundary Content, and Brunn–Minkowski Isoperimetry

This file develops the **outer parallel set** $\operatorname{outerParallel}(s, r) =
s + r \cdot \overline{B}(0, 1)$ and the **lower and upper outer-parallel Minkowski boundary
contents** $\mathcal{M}_*^\mu(s)$ and $\mathcal{M}^{*\mu}(s)$ in a finite-dimensional real normed
or inner product space $E$.

## Main definitions and results

* `TauCeti.outerParallel`, `TauCeti.lowerMinkowskiContent`, `TauCeti.upperMinkowskiContent`:
  outer parallel sets and lower/upper Minkowski boundary contents, compared with `thickening` and
  `cthickening`, and identified with `ENNReal.ofReal S` under a right derivative $S$ at $r = 0$.
* `TauCeti.measure_outerParallel_rpow_inv_finrank_ge`, `TauCeti.measure_outerParallel_ge`,
  `TauCeti.lowerMinkowskiContent_ge_isoperimetric`, `TauCeti.lowerMinkowskiContent_pow_finrank_ge`,
  `TauCeti.perimeter_pow_finrank_ge_of_hasDerivWithinAt_outerParallel`:
  Brunn–Minkowski lower bounds and the sharp isoperimetric inequality
  $n^n \omega_n \mu(s)^{n - 1} \le \mathcal{M}_*^\mu(s)^n$ (and $\le P_\mu(K)^n$).
* `TauCeti.hasDerivWithinAt_outerParallel_closedBall`, `TauCeti.lowerMinkowskiContent_closedBall`,
  `TauCeti.upperMinkowskiContent_closedBall`: for Euclidean balls, the outer-parallel right
  derivative, lower/upper Minkowski contents, and Caccioppoli perimeter all coincide.
* `TauCeti.tendsto_outerParallel_prod_singleton_div`,
  `TauCeti.lowerMinkowskiContent_prod_singleton`,
  `TauCeti.hasDerivWithinAt_outerParallel_prod_singleton` (and `WithLp 2 (E × ℝ)` counterparts):
  for a compact set $K \subseteq E$, $K \times \{0\}$ has zero ambient volume and Caccioppoli
  perimeter while its outer-parallel right derivative and Minkowski content equal $2 \mu(K)$.
-/

open Filter Function MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped ENNReal NNReal Pointwise Topology

public section

namespace TauCeti

/-! ### Section 1: Outer parallel sets and lower/upper Minkowski boundary content -/

section OuterParallel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **outer parallel set** of $s \subseteq E$ at radius $r \in \mathbb{R}$, defined as the
Minkowski sum $s + r \cdot \overline{B}(0, 1)$. -/
noncomputable def outerParallel (s : Set E) (r : ℝ) : Set E :=
  s + r • Metric.closedBall (0 : E) 1

/-- The outer parallel set of the empty set is empty. -/
@[simp]
theorem outerParallel_empty (r : ℝ) : outerParallel (∅ : Set E) r = ∅ := by simp [outerParallel]

/-- At radius $r = 0$, the outer parallel set of $s$ equals $s$. -/
@[simp]
theorem outerParallel_zero (s : Set E) : outerParallel s 0 = s := by
  have hne : (Metric.closedBall (0 : E) 1).Nonempty := ⟨0, by simp⟩
  rw [outerParallel, zero_smul_set hne, add_zero]

/-- For $r \ge 0$, `outerParallel s r` is the Minkowski sum $s + \overline{B}(0, r)$. -/
theorem outerParallel_eq_add_closedBall {r : ℝ} (hr : 0 ≤ r) (s : Set E) :
    outerParallel s r = s + Metric.closedBall (0 : E) r := by
  rw [outerParallel, smul_unitClosedBall, Real.norm_of_nonneg hr]

/-- Every set $s$ is contained in `outerParallel s r` for any $r \in \mathbb{R}$. -/
theorem self_subset_outerParallel (s : Set E) (r : ℝ) : s ⊆ outerParallel s r :=
  fun x hx ↦ ⟨x, hx, 0, ⟨0, by simp, smul_zero r⟩, add_zero x⟩

/-- If $s$ is nonempty, then `outerParallel s r` is nonempty. -/
theorem Nonempty.outerParallel {s : Set E} (hs : s.Nonempty) (r : ℝ) :
    (outerParallel s r).Nonempty :=
  hs.mono (self_subset_outerParallel s r)

/-- Semigroup law for `outerParallel` under nonnegative radii. -/
theorem outerParallel_outerParallel (s : Set E) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    outerParallel (outerParallel s r₁) r₂ = outerParallel s (r₁ + r₂) := by
  rw [outerParallel, outerParallel, outerParallel, add_assoc,
    ← (convex_closedBall (0 : E) 1).add_smul hr₁ hr₂]

/-- Monotonicity of `outerParallel` in both the set and the nonnegative radius. -/
theorem outerParallel_mono {s t : Set E} (hst : s ⊆ t) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₁ ≤ r₂) :
    outerParallel s r₁ ⊆ outerParallel t r₂ := by
  rw [outerParallel_eq_add_closedBall hr₁, outerParallel_eq_add_closedBall (hr₁.trans hr)]
  exact add_subset_add hst (Metric.closedBall_subset_closedBall hr)

/-- The outer parallel set of $\overline{B}(c, R)$ ($R \ge 0$) at $r \ge 0$ is
$\overline{B}(c, R + r)$. -/
theorem outerParallel_closedBall (c : E) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) :
    outerParallel (Metric.closedBall c R) r = Metric.closedBall c (R + r) := by
  have hR' : Metric.closedBall (0 : E) R = R • Metric.closedBall (0 : E) 1 := by
    rw [smul_unitClosedBall, Real.norm_of_nonneg hR]
  rw [outerParallel, ← singleton_add_closedBall_zero R c, hR', add_assoc,
    ← (convex_closedBall (0 : E) 1).add_smul hR hr, smul_unitClosedBall,
    Real.norm_of_nonneg (add_nonneg hR hr), singleton_add_closedBall_zero]

/-- The outer parallel set of $B(c, R)$ ($R > 0$) at $r \ge 0$ is $B(c, R + r)$. -/
theorem outerParallel_ball (c : E) {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) :
    outerParallel (Metric.ball c R) r = Metric.ball c (R + r) := by
  rw [outerParallel_eq_add_closedBall hr]
  ext z
  simp only [Set.mem_add, Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    calc ‖x + y - c‖ = ‖(x - c) + y‖ := by abel_nf
      _ ≤ ‖x - c‖ + ‖y‖ := norm_add_le _ _
      _ < R + r := add_lt_add_of_lt_of_le hx hy
  · rcases le_or_gt ‖z - c‖ r with hle | hlt
    · exact ⟨c, by simpa using hR, z - c, hle, add_sub_cancel c z⟩
    · set d := ‖z - c‖
      have hd : 0 < d := hr.trans_lt hlt
      refine ⟨z - (r / d) • (z - c), ?_, (r / d) • (z - c), ?_, sub_add_cancel _ _⟩
      · have hsub : z - (r / d) • (z - c) - c = (1 - r / d) • (z - c) := by module
        rw [hsub, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 (div_le_one_of_le₀ hlt.le hd.le)),
          sub_mul, div_mul_cancel₀ r hd.ne', one_mul]
        linarith
      · rw [norm_smul, Real.norm_of_nonneg (div_nonneg hr hd.le), div_mul_cancel₀ r hd.ne']

omit [NormedSpace ℝ E] in
/-- Minkowski addition with the open ball $B(0, r)$ coincides with `Metric.thickening r s`. -/
theorem add_ball_zero (s : Set E) (r : ℝ) :
    s + Metric.ball (0 : E) r = Metric.thickening r s := by
  ext x
  simp only [Set.mem_add, Metric.mem_thickening_iff, dist_eq_norm]
  refine ⟨fun ⟨y, hy, z, hz, h⟩ ↦ ⟨y, hy, by simpa [← h, Metric.mem_ball] using hz⟩,
    fun ⟨y, hy, h⟩ ↦ ⟨y, hy, x - y, by simpa [Metric.mem_ball] using h, add_sub_cancel y x⟩⟩

/-- For $r \ge 0$, `Metric.thickening r s` is contained in `outerParallel s r`. -/
theorem thickening_subset_outerParallel {r : ℝ} (hr : 0 ≤ r) (s : Set E) :
    Metric.thickening r s ⊆ outerParallel s r := by
  rw [← add_ball_zero, outerParallel_eq_add_closedBall hr]
  exact add_subset_add Subset.rfl Metric.ball_subset_closedBall

/-- For $r \ge 0$, `outerParallel s r` is contained in `Metric.cthickening r s`. -/
theorem outerParallel_subset_cthickening {r : ℝ} (hr : 0 ≤ r) (s : Set E) :
    outerParallel s r ⊆ Metric.cthickening r s := by
  rw [outerParallel_eq_add_closedBall hr]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact Metric.mem_cthickening_of_dist_le (x + y) x r s hx (by simpa [dist_eq_norm] using hy)

/-- For a compact set $s$ and $r \ge 0$, `outerParallel s r = Metric.cthickening r s`. -/
theorem outerParallel_eq_cthickening_of_isCompact {s : Set E} (hs : IsCompact s) {r : ℝ}
    (hr : 0 ≤ r) : outerParallel s r = Metric.cthickening r s := by
  refine Subset.antisymm (outerParallel_subset_cthickening hr s) fun z hz ↦ ?_
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp at hz
  · obtain ⟨x, hx, hdist⟩ := hs.exists_infEDist_eq_edist hne z
    rw [Metric.mem_cthickening_iff, hdist, edist_dist, ENNReal.ofReal_le_ofReal_iff hr] at hz
    rw [outerParallel_eq_add_closedBall hr]
    exact ⟨x, hx, z - x, by simpa [dist_eq_norm] using hz, add_sub_cancel x z⟩

/-- In a proper normed space, the outer parallel set of a compact set is compact. -/
theorem isCompact_outerParallel [ProperSpace E] {s : Set E} (hs : IsCompact s) (r : ℝ) :
    IsCompact (outerParallel s r) :=
  hs.add ((isCompact_closedBall (0 : E) 1).smul r)

/-- The outer parallel set of a bounded set is bounded. -/
theorem isBounded_outerParallel {s : Set E} (hs : Bornology.IsBounded s) (r : ℝ) :
    Bornology.IsBounded (outerParallel s r) :=
  hs.add (Metric.isBounded_closedBall.smul₀ r)

/-- For any closed set $s$, $\bigcap_{k \in \mathbb{N}} \operatorname{outerParallel}(s, 1/(k+1)) =
s$. -/
theorem iInter_outerParallel_nat_inv_of_isClosed {s : Set E} (hs : IsClosed s) :
    (⋂ k : ℕ, outerParallel s (1 / (k + 1 : ℝ))) = s := by
  refine Subset.antisymm (fun x hx ↦ ?_) (subset_iInter fun k ↦ self_subset_outerParallel s _)
  rw [← hs.closure_eq, Metric.mem_closure_iff_infEDist_zero, ← nonpos_iff_eq_zero]
  have hle : ∀ k : ℕ, Metric.infEDist x s ≤ ENNReal.ofReal (1 / (k + 1 : ℝ)) := fun k ↦
    Metric.mem_cthickening_iff.1
      (outerParallel_subset_cthickening (by positivity) s (mem_iInter.1 hx k))
  have hlim : Tendsto (fun k : ℕ ↦ ENNReal.ofReal (1 / (k + 1 : ℝ))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto' hlim hle

variable [MeasurableSpace E]

/-- **Right-continuity of outer parallel volume for compact sets**: for a compact set $K$,
$\mu(\operatorname{outerParallel}(K, r)) \to \mu(K)$ as $r \to 0^+$. -/
theorem tendsto_measure_outerParallel_of_isCompact [ProperSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K) :
    Tendsto (fun r : ℝ ↦ μ (outerParallel K r)) (𝓝[>] 0) (𝓝 (μ K)) := by
  have hiInf : (⨅ k : ℕ, μ (outerParallel K (1 / (k + 1 : ℝ)))) = μ K := by
    rw [← IsCompact.measure_iInter_of_antitone μ (fun k ↦ isCompact_outerParallel hK _)
      (fun i j hij ↦ outerParallel_mono Subset.rfl (by positivity)
        (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1))),
      iInter_outerParallel_nat_inv_of_isClosed hK.isClosed]
  refine tendsto_order.2 ⟨fun b hb ↦ Eventually.of_forall fun r ↦
    hb.trans_le (measure_mono (self_subset_outerParallel K r)), fun b hb ↦ ?_⟩
  rw [gt_iff_lt, ← hiInf, iInf_lt_iff] at hb
  obtain ⟨k, hk⟩ := hb
  filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / (k + 1 : ℝ))] with r ⟨hr0, hrk⟩
  exact (measure_mono (outerParallel_mono Subset.rfl hr0.le hrk.le)).trans_lt hk

/-- The **lower outer-parallel Minkowski boundary content** $\mathcal{M}_*^\mu(s) =
\liminf_{r \to 0^+} (\mu(\operatorname{outerParallel}(s, r)) - \mu(s)) / r$. -/
noncomputable def lowerMinkowskiContent (μ : Measure E := by volume_tac) (s : Set E) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦ (μ (outerParallel s r) - μ s) / ENNReal.ofReal r) (𝓝[>] 0)

/-- The **upper outer-parallel Minkowski boundary content** $\mathcal{M}^{*\mu}(s) =
\limsup_{r \to 0^+} (\mu(\operatorname{outerParallel}(s, r)) - \mu(s)) / r$. -/
noncomputable def upperMinkowskiContent (μ : Measure E := by volume_tac) (s : Set E) : ℝ≥0∞ :=
  limsup (fun r : ℝ ↦ (μ (outerParallel s r) - μ s) / ENNReal.ofReal r) (𝓝[>] 0)

/-- The lower Minkowski content of the empty set is $0$. -/
@[simp]
theorem lowerMinkowskiContent_empty (μ : Measure E) :
    lowerMinkowskiContent μ (∅ : Set E) = 0 := by simp [lowerMinkowskiContent, liminf_const]

/-- The upper Minkowski content of the empty set is $0$. -/
@[simp]
theorem upperMinkowskiContent_empty (μ : Measure E) :
    upperMinkowskiContent μ (∅ : Set E) = 0 := by simp [upperMinkowskiContent, limsup_const]

/-- The lower Minkowski content never exceeds the upper Minkowski content. -/
theorem lowerMinkowskiContent_le_upperMinkowskiContent (μ : Measure E) (s : Set E) :
    lowerMinkowskiContent μ s ≤ upperMinkowskiContent μ s :=
  liminf_le_limsup

/-- If $r \mapsto (\mu(\operatorname{outerParallel}(s, r))).\mathrm{toReal}$ has right derivative
$S$ at $r = 0$ and $\mu(\operatorname{outerParallel}(s, r)) < \infty$ for small $r > 0$, then the
outer-parallel difference quotient converges in $\mathbb{R}_{\ge 0\infty}$ to
$\operatorname{ofReal}(S)$. -/
theorem tendsto_outerParallel_div_of_hasDerivWithinAt {μ : Measure E} {s : Set E} {S : ℝ}
    (hfin : ∀ᶠ r in 𝓝[>] 0, μ (outerParallel s r) ≠ ⊤)
    (hderiv : HasDerivWithinAt (fun r : ℝ ↦ (μ (outerParallel s r)).toReal) S (Ici 0) 0) :
    Tendsto (fun r : ℝ ↦ (μ (outerParallel s r) - μ s) / ENNReal.ofReal r)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal S)) := by
  have hIci : Ici (0 : ℝ) \ {0} = Ioi 0 := by ext x; simp [lt_iff_le_and_ne, eq_comm]
  have hslope := hasDerivWithinAt_iff_tendsto_slope.1 hderiv
  rw [hIci] at hslope
  refine ((ENNReal.continuous_ofReal.tendsto S).comp hslope).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hfin] with r hr hrfin
  have hsfin : μ s ≠ ⊤ := ne_top_of_le_ne_top hrfin (measure_mono (self_subset_outerParallel s r))
  rw [Function.comp_apply, slope_def_field, outerParallel_zero, sub_zero,
    ENNReal.ofReal_div_of_pos hr, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hrfin, ENNReal.ofReal_toReal hsfin]

/-- Under a right derivative $S$ at $r = 0$ for the real-valued outer parallel volume,
`lowerMinkowskiContent μ s = ENNReal.ofReal S`. -/
theorem lowerMinkowskiContent_eq_of_hasDerivWithinAt {μ : Measure E} {s : Set E} {S : ℝ}
    (hfin : ∀ᶠ r in 𝓝[>] 0, μ (outerParallel s r) ≠ ⊤)
    (hderiv : HasDerivWithinAt (fun r : ℝ ↦ (μ (outerParallel s r)).toReal) S (Ici 0) 0) :
    lowerMinkowskiContent μ s = ENNReal.ofReal S :=
  (tendsto_outerParallel_div_of_hasDerivWithinAt hfin hderiv).liminf_eq

/-- Under a right derivative $S$ at $r = 0$ for the real-valued outer parallel volume,
`upperMinkowskiContent μ s = ENNReal.ofReal S`. -/
theorem upperMinkowskiContent_eq_of_hasDerivWithinAt {μ : Measure E} {s : Set E} {S : ℝ}
    (hfin : ∀ᶠ r in 𝓝[>] 0, μ (outerParallel s r) ≠ ⊤)
    (hderiv : HasDerivWithinAt (fun r : ℝ ↦ (μ (outerParallel s r)).toReal) S (Ici 0) 0) :
    upperMinkowskiContent μ s = ENNReal.ofReal S :=
  (tendsto_outerParallel_div_of_hasDerivWithinAt hfin hderiv).limsup_eq

/-- For a bounded set $s$ in a proper space with a measure finite on compacts, a right derivative
$S$ of the outer parallel volume at $0$ gives `lowerMinkowskiContent μ s = ENNReal.ofReal S`. -/
theorem lowerMinkowskiContent_eq_of_hasDerivWithinAt_of_isBounded [ProperSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {s : Set E} (hs : Bornology.IsBounded s) {S : ℝ}
    (hderiv : HasDerivWithinAt (fun r : ℝ ↦ (μ (outerParallel s r)).toReal) S (Ici 0) 0) :
    lowerMinkowskiContent μ s = ENNReal.ofReal S :=
  lowerMinkowskiContent_eq_of_hasDerivWithinAt
    (Eventually.of_forall fun r ↦ (isBounded_outerParallel hs r).measure_lt_top.ne) hderiv

/-- For a bounded set $s$ in a proper space with a measure finite on compacts, a right derivative
$S$ of the outer parallel volume at $0$ gives `upperMinkowskiContent μ s = ENNReal.ofReal S`. -/
theorem upperMinkowskiContent_eq_of_hasDerivWithinAt_of_isBounded [ProperSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {s : Set E} (hs : Bornology.IsBounded s) {S : ℝ}
    (hderiv : HasDerivWithinAt (fun r : ℝ ↦ (μ (outerParallel s r)).toReal) S (Ici 0) 0) :
    upperMinkowskiContent μ s = ENNReal.ofReal S :=
  upperMinkowskiContent_eq_of_hasDerivWithinAt
    (Eventually.of_forall fun r ↦ (isBounded_outerParallel hs r).measure_lt_top.ne) hderiv

end OuterParallel

/-! ### Section 2: Brunn–Minkowski outer-parallel lower bound and Minkowski-content isoperimetry -/

section BrunnMinkowskiIsoperimetric

/-- Elementary binomial lower bound in $\mathbb{R}_{\ge 0\infty}$: for $n \ge 1$,
$a^n + n a^{n-1} b \le (a + b)^n$. -/
theorem add_pow_ge_add_mul_pow_sub_one (a b : ℝ≥0∞) {n : ℕ} (hn : 1 ≤ n) :
    a ^ n + (n : ℝ≥0∞) * a ^ (n - 1) * b ≤ (a + b) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn; clear hn
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Nat.add_sub_cancel] at ih ⊢
    calc a ^ (m + 1 + 1) + ((m + 1 + 1 : ℕ) : ℝ≥0∞) * a ^ (m + 1) * b
        = (a ^ (m + 1) + (m + 1 : ℕ) * a ^ m * b) * a + a ^ (m + 1) * b := by
          push_cast; ring
      _ ≤ (a + b) ^ (m + 1) * a + (a + b) ^ (m + 1) * b :=
          add_le_add (mul_le_mul_of_nonneg_right ih zero_le)
            (mul_le_mul_of_nonneg_right (pow_le_pow_left' le_self_add _) zero_le)
      _ = (a + b) ^ (m + 1 + 1) := by rw [← mul_add, ← pow_succ]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- For any additive Haar measure $\mu$ on $E$, the unit closed ball and unit open ball have equal
measure. -/
theorem measure_closedBall_unit_eq_ball :
    μ (Metric.closedBall (0 : E) 1) = μ (Metric.ball (0 : E) 1) := by
  rw [Measure.addHaar_closedBall μ (0 : E) zero_le_one, one_pow, ENNReal.ofReal_one, one_mul]

variable [Nontrivial E]

/-- **Brunn–Minkowski inequality for the outer parallel set**: for any nonempty
$\mu$-null-measurable set $s \subseteq E$ and $r \ge 0$,
$\mu(s)^{1/n} + r \, \mu(\overline{B}(0, 1))^{1/n} \le
\mu(\operatorname{outerParallel}(s, r))^{1/n}$. -/
theorem measure_outerParallel_rpow_inv_finrank_ge {s : Set E} (hs_ne : s.Nonempty)
    (hs_m : NullMeasurableSet s μ) {r : ℝ} (hr : 0 ≤ r) :
    μ s ^ (1 / (Module.finrank ℝ E : ℝ)) +
        ENNReal.ofReal r * μ (Metric.closedBall (0 : E) 1) ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      μ (outerParallel s r) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hB_ne : (r • Metric.closedBall (0 : E) 1).Nonempty :=
    (Metric.nonempty_closedBall.2 zero_le_one).smul_set
  have hB_m : NullMeasurableSet (r • Metric.closedBall (0 : E) 1) μ :=
    ((isCompact_closedBall (0 : E) 1).smul r).measurableSet.nullMeasurableSet
  have h := measure_add_rpow_inv_finrank_ge_of_nullMeasurableSet μ hn hs_ne hs_m hB_ne hB_m
  rwa [measure_smul_rpow_inv_finrank_of_nonneg μ hr (Metric.closedBall (0 : E) 1) hn] at h

/-- **Finite-radius outer parallel volume lower bound**: for any nonempty $\mu$-null-measurable set
$s \subseteq E$ and $r \ge 0$,
$\mu(s) + n r \, \mu(B(0, 1))^{1/n} \mu(s)^{(n-1)/n} \le \mu(\operatorname{outerParallel}(s, r))$.
-/
theorem measure_outerParallel_ge {s : Set E} (hs_ne : s.Nonempty)
    (hs_m : NullMeasurableSet s μ) {r : ℝ} (hr : 0 ≤ r) :
    μ s + (Module.finrank ℝ E : ℝ≥0∞) * ENNReal.ofReal r *
        μ (Metric.ball (0 : E) 1) ^ (1 / (Module.finrank ℝ E : ℝ)) *
        μ s ^ ((Module.finrank ℝ E - 1 : ℕ) / (Module.finrank ℝ E : ℝ)) ≤
      μ (outerParallel s r) := by
  set n := Module.finrank ℝ E
  have hn : 1 ≤ n := Module.finrank_pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1 := measure_outerParallel_rpow_inv_finrank_ge hs_ne hs_m hr
  rw [measure_closedBall_unit_eq_ball] at h1
  have h2 := (add_pow_ge_add_mul_pow_sub_one (μ s ^ (1 / (n : ℝ)))
    (ENNReal.ofReal r * μ (Metric.ball (0 : E) 1) ^ (1 / (n : ℝ))) hn).trans (pow_le_pow_left' h1 n)
  have hrpow_n (x : ℝ≥0∞) : (x ^ (1 / (n : ℝ))) ^ n = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_cancel hn_pos.ne', ENNReal.rpow_one]
  have hrpow_sub (x : ℝ≥0∞) :
      (x ^ (1 / (n : ℝ))) ^ (n - 1) = x ^ ((n - 1 : ℕ) / (n : ℝ)) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_eq_div]
  rw [hrpow_n, hrpow_n, hrpow_sub] at h2
  exact le_trans (by ring_nf; exact le_rfl) h2

/-- **Sharp Minkowski-content isoperimetric inequality**: for any nonempty $\mu$-null-measurable
set $s \subseteq E$ with $\mu(s) < \infty$,
$n \, \mu(B(0, 1))^{1/n} \mu(s)^{(n-1)/n} \le \mathcal{M}_*^\mu(s)$. -/
theorem lowerMinkowskiContent_ge_isoperimetric {s : Set E} (hs_ne : s.Nonempty)
    (hs_m : NullMeasurableSet s μ) (hs_fin : μ s ≠ ⊤) :
    (Module.finrank ℝ E : ℝ≥0∞) *
        μ (Metric.ball (0 : E) 1) ^ (1 / (Module.finrank ℝ E : ℝ)) *
        μ s ^ ((Module.finrank ℝ E - 1 : ℕ) / (Module.finrank ℝ E : ℝ)) ≤
      lowerMinkowskiContent μ s := by
  unfold lowerMinkowskiContent
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hsub := tsub_le_tsub_right (measure_outerParallel_ge hs_ne hs_m hr.le) (μ s)
  rw [ENNReal.add_sub_cancel_left hs_fin] at hsub
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← ENNReal.mul_div_cancel_right (a := _ * _ * _) hr0 hrtop]
  exact ENNReal.div_le_div_right (le_trans (by ring_nf; exact le_rfl) hsub) _

/-- Upper Minkowski-content isoperimetric inequality for a nonempty $\mu$-null-measurable set $s$
with $\mu(s) < \infty$. -/
theorem upperMinkowskiContent_ge_isoperimetric {s : Set E} (hs_ne : s.Nonempty)
    (hs_m : NullMeasurableSet s μ) (hs_fin : μ s ≠ ⊤) :
    (Module.finrank ℝ E : ℝ≥0∞) *
        μ (Metric.ball (0 : E) 1) ^ (1 / (Module.finrank ℝ E : ℝ)) *
        μ s ^ ((Module.finrank ℝ E - 1 : ℕ) / (Module.finrank ℝ E : ℝ)) ≤
      upperMinkowskiContent μ s :=
  (lowerMinkowskiContent_ge_isoperimetric hs_ne hs_m hs_fin).trans
    (lowerMinkowskiContent_le_upperMinkowskiContent μ s)

/-- **Dimensional power form of the Minkowski-content isoperimetric inequality**:
$n^n \, \mu(B(0, 1)) \, \mu(s)^{n - 1} \le \mathcal{M}_*^\mu(s)^n$. -/
theorem lowerMinkowskiContent_pow_finrank_ge {s : Set E} (hs_ne : s.Nonempty)
    (hs_m : NullMeasurableSet s μ) (hs_fin : μ s ≠ ⊤) :
    (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * μ (Metric.ball (0 : E) 1) *
        μ s ^ (Module.finrank ℝ E - 1) ≤
      lowerMinkowskiContent μ s ^ Module.finrank ℝ E := by
  set n := Module.finrank ℝ E
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 Module.finrank_pos
  have h := pow_le_pow_left' (lowerMinkowskiContent_ge_isoperimetric hs_ne hs_m hs_fin) n
  have h1 : (μ (Metric.ball (0 : E) 1) ^ (1 / (n : ℝ))) ^ n = μ (Metric.ball (0 : E) 1) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_cancel hn_pos.ne', ENNReal.rpow_one]
  have h2 : (μ s ^ ((n - 1 : ℕ) / (n : ℝ))) ^ n = μ s ^ (n - 1) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, div_mul_cancel₀ _ hn_pos.ne',
      ENNReal.rpow_natCast]
  rwa [mul_pow, mul_pow, h1, h2] at h

/-- **Outer-parallel right-derivative isoperimetric inequality**: if $s \subseteq E$ is nonempty,
$\mu$-null-measurable, and has outer-parallel volume right derivative $S$ at $r = 0$ with
$\mu(\operatorname{outerParallel}(s, r)) < \infty$ for small $r > 0$, then
$n^n \, \mu(B(0, 1)) \, \mu(s)^{n - 1} \le \operatorname{ofReal}(S)^n$. -/
theorem ofReal_pow_finrank_ge_of_hasDerivWithinAt_outerParallel {s : Set E} (hs_ne : s.Nonempty)
    (hs_m : NullMeasurableSet s μ) {S : ℝ}
    (hfin : ∀ᶠ r in 𝓝[>] 0, μ (outerParallel s r) ≠ ⊤)
    (hderiv : HasDerivWithinAt (fun r : ℝ ↦ (μ (outerParallel s r)).toReal) S (Ici 0) 0) :
    (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * μ (Metric.ball (0 : E) 1) *
        μ s ^ (Module.finrank ℝ E - 1) ≤
      ENNReal.ofReal S ^ Module.finrank ℝ E := by
  obtain ⟨r, hr⟩ := hfin.exists
  have hs_fin : μ s ≠ ⊤ := ne_top_of_le_ne_top hr (measure_mono (self_subset_outerParallel s r))
  rw [← lowerMinkowskiContent_eq_of_hasDerivWithinAt hfin hderiv]
  exact lowerMinkowskiContent_pow_finrank_ge hs_ne hs_m hs_fin

end BrunnMinkowskiIsoperimetric

/-! ### Section 3: Balls and sets whose outer-parallel right derivative is bounded by perimeter -/

section BallAndPerimeterMinkowskiContent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- Any set of $\mu$-measure zero has zero relative perimeter in every open set $\Omega$. -/
theorem relativePerimeter_eq_zero_of_measure_zero {μ : Measure E} {Ω : Opens E} {s : Set E}
    (hs : μ s = 0) : relativePerimeter μ Ω s = 0 := by
  rw [← empty_union s, relativePerimeter_union_null ∅ hs, relativePerimeter_empty]

/-- Any set of $\mu$-measure zero has zero Caccioppoli perimeter. -/
theorem perimeter_eq_zero_of_measure_zero {μ : Measure E} {s : Set E} (hs : μ s = 0) :
    perimeter μ s = 0 := by
  rw [← empty_union s, perimeter_union_null ∅ hs, perimeter_empty]

variable [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Isoperimetric inequality from outer-parallel right derivative**: if $K \subseteq E$ is a
nonempty $\mu$-null-measurable bounded set whose outer-parallel volume has right derivative at
$r = 0$ bounded above by $P_\mu(K)$, then
$n^n \, \mu(B(0, 1)) \, \mu(K)^{n - 1} \le P_\mu(K)^n$. -/
theorem perimeter_pow_finrank_ge_of_hasDerivWithinAt_outerParallel [Nontrivial E]
    {K : Set E} (hK_ne : K.Nonempty) (hK_m : NullMeasurableSet K μ)
    (hK_bdd : Bornology.IsBounded K) {S : ℝ}
    (hderiv : HasDerivWithinAt (fun r : ℝ ↦ (μ (outerParallel K r)).toReal) S (Ici 0) 0)
    (hS : ENNReal.ofReal S ≤ perimeter μ K) :
    (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * μ (Metric.ball (0 : E) 1) *
        μ K ^ (Module.finrank ℝ E - 1) ≤
      perimeter μ K ^ Module.finrank ℝ E := by
  have hfin : ∀ᶠ r in 𝓝[>] 0, μ (outerParallel K r) ≠ ⊤ :=
    Eventually.of_forall fun r ↦ (isBounded_outerParallel hK_bdd r).measure_lt_top.ne
  exact (ofReal_pow_finrank_ge_of_hasDerivWithinAt_outerParallel hK_ne hK_m hfin hderiv).trans
    (pow_le_pow_left' hS _)

/-- For any closed ball $\overline{B}(c, R)$ with $R > 0$, the outer parallel volume has right
derivative at $r = 0$ equal to $(P_\mu(\overline{B}(c, R))).\mathrm{toReal}$. -/
theorem hasDerivWithinAt_outerParallel_closedBall (c : E) {R : ℝ} (hR : 0 < R) :
    HasDerivWithinAt (fun r : ℝ ↦ (μ (outerParallel (Metric.closedBall c R) r)).toReal)
      (perimeter μ (Metric.closedBall c R)).toReal (Ici 0) 0 := by
  set n := Module.finrank ℝ E
  set ω := (μ (Metric.ball (0 : E) 1)).toReal
  have hd : HasDerivAt (fun r : ℝ ↦ (R + r) ^ n * ω) ((n : ℝ) * R ^ (n - 1) * ω) 0 := by
    simpa [add_zero, mul_one] using (((hasDerivAt_id 0).const_add R).pow n).mul_const ω
  have hperim : (perimeter μ (Metric.closedBall c R)).toReal = (n : ℝ) * R ^ (n - 1) * ω := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · simp [perimeter_eq_zero_of_subsingleton, n, Module.finrank_zero_of_subsingleton]
    · rw [perimeter_closedBall_eq_unitBall c hR, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
  rw [hperim]
  refine hd.hasDerivWithinAt.congr (fun r (hr : 0 ≤ r) ↦ ?_) ?_
  · rw [outerParallel_closedBall c hR.le hr, Measure.addHaar_closedBall μ c (add_nonneg hR.le hr),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (add_nonneg hR.le hr) _)]
  · rw [outerParallel_closedBall c hR.le le_rfl, add_zero, Measure.addHaar_closedBall μ c hR.le,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR.le _)]

/-- For any open ball $B(c, R)$ with $R > 0$, the outer parallel volume has right derivative at
$r = 0$ equal to $(P_\mu(B(c, R))).\mathrm{toReal}$. -/
theorem hasDerivWithinAt_outerParallel_ball (c : E) {R : ℝ} (hR : 0 < R) :
    HasDerivWithinAt (fun r : ℝ ↦ (μ (outerParallel (Metric.ball c R) r)).toReal)
      (perimeter μ (Metric.ball c R)).toReal (Ici 0) 0 := by
  have hball_eq (s : ℝ) (hs : 0 < s) : μ (Metric.ball c s) = μ (Metric.closedBall c s) := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · congr 1; ext x; simp [Subsingleton.elim x c, hs, hs.le]
    · rw [Measure.addHaar_ball μ c hs.le, Measure.addHaar_closedBall μ c hs.le]
  rw [← perimeter_closedBall_eq_ball]
  refine (hasDerivWithinAt_outerParallel_closedBall c hR).congr (fun r (hr : 0 ≤ r) ↦ ?_) ?_
  · rw [outerParallel_ball c hR hr, outerParallel_closedBall c hR.le hr,
      hball_eq (R + r) (add_pos_of_pos_of_nonneg hR hr)]
  · rw [outerParallel_zero, outerParallel_zero, hball_eq R hR]

/-- For $R > 0$, `lowerMinkowskiContent` of $\overline{B}(c, R)$ equals its Caccioppoli perimeter.
-/
theorem lowerMinkowskiContent_closedBall (c : E) {R : ℝ} (hR : 0 < R) :
    lowerMinkowskiContent μ (Metric.closedBall c R) = perimeter μ (Metric.closedBall c R) := by
  rw [lowerMinkowskiContent_eq_of_hasDerivWithinAt_of_isBounded Metric.isBounded_closedBall
    (hasDerivWithinAt_outerParallel_closedBall c hR),
    ENNReal.ofReal_toReal (perimeter_closedBall_lt_top c R).ne]

/-- For $R > 0$, `upperMinkowskiContent` of $\overline{B}(c, R)$ equals its Caccioppoli perimeter.
-/
theorem upperMinkowskiContent_closedBall (c : E) {R : ℝ} (hR : 0 < R) :
    upperMinkowskiContent μ (Metric.closedBall c R) = perimeter μ (Metric.closedBall c R) := by
  rw [upperMinkowskiContent_eq_of_hasDerivWithinAt_of_isBounded Metric.isBounded_closedBall
    (hasDerivWithinAt_outerParallel_closedBall c hR),
    ENNReal.ofReal_toReal (perimeter_closedBall_lt_top c R).ne]

/-- For $R > 0$, `lowerMinkowskiContent` of $B(c, R)$ equals its Caccioppoli perimeter. -/
theorem lowerMinkowskiContent_ball (c : E) {R : ℝ} (hR : 0 < R) :
    lowerMinkowskiContent μ (Metric.ball c R) = perimeter μ (Metric.ball c R) := by
  rw [lowerMinkowskiContent_eq_of_hasDerivWithinAt_of_isBounded Metric.isBounded_ball
    (hasDerivWithinAt_outerParallel_ball c hR),
    ENNReal.ofReal_toReal (perimeter_ball_lt_top c R).ne]

/-- For $R > 0$, `upperMinkowskiContent` of $B(c, R)$ equals its Caccioppoli perimeter. -/
theorem upperMinkowskiContent_ball (c : E) {R : ℝ} (hR : 0 < R) :
    upperMinkowskiContent μ (Metric.ball c R) = perimeter μ (Metric.ball c R) := by
  rw [upperMinkowskiContent_eq_of_hasDerivWithinAt_of_isBounded Metric.isBounded_ball
    (hasDerivWithinAt_outerParallel_ball c hR),
    ENNReal.ofReal_toReal (perimeter_ball_lt_top c R).ne]

end BallAndPerimeterMinkowskiContent

/-! ### Section 4: Degenerate codimension-1 and codimension-$\ge 2$ compact sets -/

section DegenerateCompactSets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lower prism inclusion in $E \times \mathbb{R}$: for $r \ge 0$,
$K \times [-r, r] \subseteq \operatorname{outerParallel}(K \times \{0\}, r)$. -/
theorem prod_Icc_subset_outerParallel_prod_singleton (K : Set E) {r : ℝ} (hr : 0 ≤ r) :
    K ×ˢ Icc (-r) r ⊆ outerParallel (K ×ˢ {(0 : ℝ)}) r := by
  rw [outerParallel_eq_add_closedBall hr]
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  refine ⟨(x, 0), ⟨hx, rfl⟩, (0, t), ?_, by ext <;> simp⟩
  simp [Metric.mem_closedBall, dist_zero_right, Prod.norm_mk, abs_le.2 ht]

/-- Upper prism inclusion in $E \times \mathbb{R}$: for $r \ge 0$,
$\operatorname{outerParallel}(K \times \{0\}, r) \subseteq
\operatorname{outerParallel}(K, r) \times [-r, r]$. -/
theorem outerParallel_prod_singleton_subset_prod_Icc (K : Set E) {r : ℝ} (hr : 0 ≤ r) :
    outerParallel (K ×ˢ {(0 : ℝ)}) r ⊆ outerParallel K r ×ˢ Icc (-r) r := by
  rw [outerParallel_eq_add_closedBall hr, outerParallel_eq_add_closedBall hr]
  rintro _ ⟨⟨x, t₀⟩, ⟨hx, rfl : t₀ = 0⟩, ⟨u, t⟩, hut, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_mk, max_le_iff] at hut
  exact ⟨⟨x, hx, u, by simpa [Metric.mem_closedBall, dist_zero_right] using hut.1, rfl⟩,
    by simpa [abs_le] using hut.2⟩

/-- Lower prism inclusion in the Euclidean product `WithLp 2 (E × ℝ)`. -/
theorem toLp_prod_Icc_subset_outerParallel (K : Set E) {r : ℝ} (hr : 0 ≤ r) :
    WithLp.toLp 2 '' (K ×ˢ Icc (-r) r) ⊆
      outerParallel (WithLp.toLp 2 '' (K ×ˢ {(0 : ℝ)})) r := by
  rw [outerParallel_eq_add_closedBall hr]
  rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
  refine ⟨WithLp.toLp 2 (x, 0), ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩, WithLp.toLp 2 ((0 : E), t), ?_,
    WithLp.ofLp_injective 2 (by ext <;> simp)⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖WithLp.toLp 2 ((0 : E), t)‖ ^ 2 = t ^ 2 := by simp
  have habs : ‖WithLp.toLp 2 ((0 : E), t)‖ = |t| := by
    rw [← Real.sqrt_sq (norm_nonneg _), hnorm, Real.sqrt_sq_eq_abs]
  exact habs.trans_le (abs_le.2 ht)

/-- Upper prism inclusion in the Euclidean product `WithLp 2 (E × ℝ)`. -/
theorem outerParallel_toLp_prod_singleton_subset (K : Set E) {r : ℝ} (hr : 0 ≤ r) :
    outerParallel (WithLp.toLp 2 '' (K ×ˢ {(0 : ℝ)})) r ⊆
      WithLp.toLp 2 '' (outerParallel K r ×ˢ Icc (-r) r) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  rw [outerParallel_eq_add_closedBall hr, outerParallel_eq_add_closedBall hr]
  rintro _ ⟨_, ⟨⟨x, t₀⟩, ⟨hx, rfl : t₀ = 0⟩, rfl⟩, u, hu, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hu
  refine ⟨(x + u.fst, u.snd), ⟨⟨x, hx, u.fst, ?_, rfl⟩, ?_⟩,
    WithLp.ofLp_injective 2 (by ext <;> simp)⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (WithLp.norm_fst_le E u).trans hu
  · exact abs_le.1 ((Real.norm_eq_abs u.snd).symm.trans_le ((WithLp.norm_snd_le E u).trans hu))

variable [MeasurableSpace E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Any codimension-1 slice $K \times \{c\} \subseteq E \times \mathbb{R}$ has product measure
zero. -/
theorem measure_prod_singleton_zero (μ : Measure E) (K : Set E) (c : ℝ) :
    (μ.prod (volume : Measure ℝ)) (K ×ˢ {c}) = 0 := by
  rw [Measure.prod_prod, Real.volume_singleton, mul_zero]

omit [NormedSpace ℝ E] in
/-- Any codimension-1 slice $K \times \{0\} \subseteq E \times \mathbb{R}$ has ambient Caccioppoli
perimeter zero. -/
theorem perimeter_prod_singleton_zero [InnerProductSpace ℝ (E × ℝ)]
    (μ : Measure E) (K : Set E) :
    perimeter (μ.prod (volume : Measure ℝ)) (K ×ˢ {(0 : ℝ)}) = 0 :=
  perimeter_eq_zero_of_measure_zero (measure_prod_singleton_zero μ K 0)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Measurable equivalence between $E \times \mathbb{R}$ and `WithLp 2 (E × ℝ)`. -/
def measurableEquivToLpProd : (E × ℝ) ≃ᵐ WithLp 2 (E × ℝ) where
  toEquiv := (WithLp.equiv 2 (E × ℝ)).symm
  measurable_toFun := by rintro _ ⟨s, hs, rfl⟩; exact hs
  measurable_invFun := comap_measurable WithLp.ofLp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Evaluating `Measure.map (WithLp.toLp 2) ν` on any subset of `WithLp 2 (E × ℝ)`. -/
theorem map_toLp_prod_apply (ν : Measure (E × ℝ)) (s : Set (WithLp 2 (E × ℝ))) :
    Measure.map (WithLp.toLp 2) ν s = ν (WithLp.toLp 2 ⁻¹' s) :=
  MeasurableEquiv.map_apply measurableEquivToLpProd s

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Evaluating `Measure.map (WithLp.toLp 2) ν` on an image `WithLp.toLp 2 '' s`. -/
theorem map_toLp_prod_image (ν : Measure (E × ℝ)) (s : Set (E × ℝ)) :
    Measure.map (WithLp.toLp 2) ν (WithLp.toLp 2 '' s) = ν s := by
  rw [map_toLp_prod_apply, preimage_image_eq _ (WithLp.toLp_injective 2)]

omit [NormedSpace ℝ E] in
/-- In the Euclidean product space `WithLp 2 (E × ℝ)`, any codimension-1 slice
`WithLp.toLp 2 '' (K ×ˢ {0})` has ambient Caccioppoli perimeter zero. -/
theorem perimeter_toLp_prod_singleton_zero [InnerProductSpace ℝ E]
    (μ : Measure E) (K : Set E) :
    perimeter (Measure.map (WithLp.toLp 2) (μ.prod (volume : Measure ℝ)))
      (WithLp.toLp 2 '' (K ×ˢ {(0 : ℝ)})) = 0 := by
  apply perimeter_eq_zero_of_measure_zero
  rw [map_toLp_prod_image, measure_prod_singleton_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- For $r > 0$, $(\mu \times \mathrm{volume})(s \times [-r, r]) / r = 2 \mu(s)$. -/
theorem measure_prod_Icc_div (μ : Measure E) (s : Set E) {r : ℝ} (hr : 0 < r) :
    (μ.prod (volume : Measure ℝ)) (s ×ˢ Icc (-r) r) / ENNReal.ofReal r = 2 * μ s := by
  rw [Measure.prod_prod, Real.volume_Icc, sub_neg_eq_add, ← two_mul,
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_left_comm (μ s) 2, ← mul_assoc,
    ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top]

/-- Lower bound
$2 \mu(K) \le (\mu \times \mathrm{volume})(\operatorname{outerParallel}(K \times \{0\}, r)) / r$
for every $r > 0$. -/
theorem le_measure_outerParallel_prod_singleton_div (μ : Measure E) (K : Set E)
    {r : ℝ} (hr : 0 < r) :
    2 * μ K ≤ (μ.prod (volume : Measure ℝ)) (outerParallel (K ×ˢ {(0 : ℝ)}) r) /
      ENNReal.ofReal r := by
  rw [← measure_prod_Icc_div μ K hr]
  exact ENNReal.div_le_div_right
    (measure_mono (prod_Icc_subset_outerParallel_prod_singleton K hr.le)) _

/-- Upper bound
$(\mu \times \mathrm{volume})(\operatorname{outerParallel}(K \times \{0\}, r)) / r \le
2 \mu(\operatorname{outerParallel}(K, r))$ for every $r > 0$. -/
theorem measure_outerParallel_prod_singleton_div_le (μ : Measure E) (K : Set E)
    {r : ℝ} (hr : 0 < r) :
    (μ.prod (volume : Measure ℝ)) (outerParallel (K ×ˢ {(0 : ℝ)}) r) / ENNReal.ofReal r ≤
      2 * μ (outerParallel K r) := by
  rw [← measure_prod_Icc_div μ (outerParallel K r) hr]
  exact ENNReal.div_le_div_right
    (measure_mono (outerParallel_prod_singleton_subset_prod_Icc K hr.le)) _

/-- **Codimension-1 outer-parallel limit formula**: for a compact set $K \subseteq E$, the
outer-parallel difference quotient of $K \times \{0\}$ converges to $2 \mu(K)$ as $r \to 0^+$. -/
theorem tendsto_outerParallel_prod_singleton_div [ProperSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K) :
    Tendsto (fun r : ℝ ↦ (μ.prod (volume : Measure ℝ)) (outerParallel (K ×ˢ {(0 : ℝ)}) r) /
      ENNReal.ofReal r) (𝓝[>] 0) (𝓝 (2 * μ K)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (ENNReal.Tendsto.const_mul (tendsto_measure_outerParallel_of_isCompact hK) (Or.inr (by simp)))
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact le_measure_outerParallel_prod_singleton_div μ K hr
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact measure_outerParallel_prod_singleton_div_le μ K hr

/-- For a compact set $K \subseteq E$, `lowerMinkowskiContent` of $K \times \{0\}$ equals
$2 \mu(K)$. -/
theorem lowerMinkowskiContent_prod_singleton [ProperSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K) :
    lowerMinkowskiContent (μ.prod (volume : Measure ℝ)) (K ×ˢ {(0 : ℝ)}) = 2 * μ K := by
  simpa [lowerMinkowskiContent, measure_prod_singleton_zero] using
    (tendsto_outerParallel_prod_singleton_div hK).liminf_eq

/-- For a compact set $K \subseteq E$, `upperMinkowskiContent` of $K \times \{0\}$ equals
$2 \mu(K)$. -/
theorem upperMinkowskiContent_prod_singleton [ProperSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K) :
    upperMinkowskiContent (μ.prod (volume : Measure ℝ)) (K ×ˢ {(0 : ℝ)}) = 2 * μ K := by
  simpa [upperMinkowskiContent, measure_prod_singleton_zero] using
    (tendsto_outerParallel_prod_singleton_div hK).limsup_eq

/-- **Codimension-1 outer-parallel right derivative formula**: for a compact set $K \subseteq E$,
the outer-parallel volume of $K \times \{0\}$ has right derivative $2 (\mu(K)).\mathrm{toReal}$ at
$r = 0$. -/
theorem hasDerivWithinAt_outerParallel_prod_singleton [ProperSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K) :
    HasDerivWithinAt (fun r : ℝ ↦
      ((μ.prod (volume : Measure ℝ)) (outerParallel (K ×ˢ {(0 : ℝ)}) r)).toReal)
      (2 * (μ K).toReal) (Ici 0) 0 := by
  have hIci : Ici (0 : ℝ) \ {0} = Ioi 0 := by ext x; simp [lt_iff_le_and_ne, eq_comm]
  rw [hasDerivWithinAt_iff_tendsto_slope, hIci]
  have hlim := (ENNReal.tendsto_toReal
    (ENNReal.mul_ne_top (by simp) (hK.measure_lt_top (μ := μ)).ne)).comp
    (tendsto_outerParallel_prod_singleton_div hK)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Function.comp_apply, slope_def_field, outerParallel_zero, measure_prod_singleton_zero,
    ENNReal.toReal_zero, sub_zero, sub_zero, ENNReal.toReal_div, ENNReal.toReal_ofReal hr.le]

/-- **Higher-codimension ($\ge 2$) outer-parallel right derivative formula**: if $K \subseteq E$ is
compact with $\mu(K) = 0$, the outer-parallel volume of $K \times \{0\}$ has right derivative $0$
at $r = 0$. -/
theorem hasDerivWithinAt_outerParallel_prod_singleton_of_measure_zero
    [ProperSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) (hK0 : μ K = 0) :
    HasDerivWithinAt (fun r : ℝ ↦
      ((μ.prod (volume : Measure ℝ)) (outerParallel (K ×ˢ {(0 : ℝ)}) r)).toReal)
      0 (Ici 0) 0 := by
  simpa [hK0] using hasDerivWithinAt_outerParallel_prod_singleton (μ := μ) hK

/-- When $K \subseteq E$ is compact with $\mu(K) = 0$, `lowerMinkowskiContent` of $K \times \{0\}$
is $0$. -/
theorem lowerMinkowskiContent_prod_singleton_of_measure_zero
    [ProperSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) (hK0 : μ K = 0) :
    lowerMinkowskiContent (μ.prod (volume : Measure ℝ)) (K ×ˢ {(0 : ℝ)}) = 0 := by
  simp [lowerMinkowskiContent_prod_singleton hK, hK0]

/-- When $K \subseteq E$ is compact with $\mu(K) = 0$, `upperMinkowskiContent` of $K \times \{0\}$
is $0$. -/
theorem upperMinkowskiContent_prod_singleton_of_measure_zero
    [ProperSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) (hK0 : μ K = 0) :
    upperMinkowskiContent (μ.prod (volume : Measure ℝ)) (K ×ˢ {(0 : ℝ)}) = 0 := by
  simp [upperMinkowskiContent_prod_singleton hK, hK0]

/-- **Euclidean `WithLp 2 (E × ℝ)` codimension-1 outer-parallel limit formula**: for a compact set
$K \subseteq E$, the outer-parallel difference quotient of `WithLp.toLp 2 '' (K ×ˢ {0})` converges
to $2 \mu(K)$ as $r \to 0^+$. -/
theorem tendsto_outerParallel_toLp_prod_singleton_div [ProperSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K) :
    Tendsto (fun r : ℝ ↦
      (Measure.map (WithLp.toLp 2) (μ.prod (volume : Measure ℝ)))
        (outerParallel (WithLp.toLp 2 '' (K ×ˢ {(0 : ℝ)})) r) / ENNReal.ofReal r)
      (𝓝[>] 0) (𝓝 (2 * μ K)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (ENNReal.Tendsto.const_mul (tendsto_measure_outerParallel_of_isCompact hK) (Or.inr (by simp)))
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [← measure_prod_Icc_div μ K hr,
      ← map_toLp_prod_image (μ.prod (volume : Measure ℝ)) (K ×ˢ Icc (-r) r)]
    exact ENNReal.div_le_div_right (measure_mono (toLp_prod_Icc_subset_outerParallel K hr.le)) _
  · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [← measure_prod_Icc_div μ (outerParallel K r) hr,
      ← map_toLp_prod_image (μ.prod (volume : Measure ℝ)) (outerParallel K r ×ˢ Icc (-r) r)]
    exact ENNReal.div_le_div_right
      (measure_mono (outerParallel_toLp_prod_singleton_subset K hr.le)) _

/-- In `WithLp 2 (E × ℝ)`, `lowerMinkowskiContent` of `WithLp.toLp 2 '' (K ×ˢ {0})` for a compact
set $K \subseteq E$ equals $2 \mu(K)$. -/
theorem lowerMinkowskiContent_toLp_prod_singleton [ProperSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K) :
    lowerMinkowskiContent (Measure.map (WithLp.toLp 2) (μ.prod (volume : Measure ℝ)))
      (WithLp.toLp 2 '' (K ×ˢ {(0 : ℝ)})) = 2 * μ K := by
  have h0 : (Measure.map (WithLp.toLp 2) (μ.prod (volume : Measure ℝ)))
      (WithLp.toLp 2 '' (K ×ˢ {(0 : ℝ)})) = 0 := by
    rw [map_toLp_prod_image, measure_prod_singleton_zero]
  simpa [lowerMinkowskiContent, h0] using
    (tendsto_outerParallel_toLp_prod_singleton_div hK).liminf_eq

/-- In `WithLp 2 (E × ℝ)`, `upperMinkowskiContent` of `WithLp.toLp 2 '' (K ×ˢ {0})` for a compact
set $K \subseteq E$ equals $2 \mu(K)$. -/
theorem upperMinkowskiContent_toLp_prod_singleton [ProperSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K) :
    upperMinkowskiContent (Measure.map (WithLp.toLp 2) (μ.prod (volume : Measure ℝ)))
      (WithLp.toLp 2 '' (K ×ˢ {(0 : ℝ)})) = 2 * μ K := by
  have h0 : (Measure.map (WithLp.toLp 2) (μ.prod (volume : Measure ℝ)))
      (WithLp.toLp 2 '' (K ×ˢ {(0 : ℝ)})) = 0 := by
    rw [map_toLp_prod_image, measure_prod_singleton_zero]
  simpa [upperMinkowskiContent, h0] using
    (tendsto_outerParallel_toLp_prod_singleton_div hK).limsup_eq

/-- **Euclidean `WithLp 2 (E × ℝ)` codimension-1 outer-parallel right derivative formula**: for a
compact set $K \subseteq E$, the outer-parallel volume of `WithLp.toLp 2 '' (K ×ˢ {0})` has right
derivative $2 (\mu(K)).\mathrm{toReal}$ at $r = 0$. -/
theorem hasDerivWithinAt_outerParallel_toLp_prod_singleton [ProperSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K) :
    HasDerivWithinAt (fun r : ℝ ↦
      ((Measure.map (WithLp.toLp 2) (μ.prod (volume : Measure ℝ)))
        (outerParallel (WithLp.toLp 2 '' (K ×ˢ {(0 : ℝ)})) r)).toReal)
      (2 * (μ K).toReal) (Ici 0) 0 := by
  have hIci : Ici (0 : ℝ) \ {0} = Ioi 0 := by ext x; simp [lt_iff_le_and_ne, eq_comm]
  rw [hasDerivWithinAt_iff_tendsto_slope, hIci]
  have hlim := (ENNReal.tendsto_toReal
    (ENNReal.mul_ne_top (by simp) (hK.measure_lt_top (μ := μ)).ne)).comp
    (tendsto_outerParallel_toLp_prod_singleton_div hK)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Function.comp_apply, slope_def_field, outerParallel_zero, map_toLp_prod_image,
    measure_prod_singleton_zero, ENNReal.toReal_zero, sub_zero, sub_zero, ENNReal.toReal_div,
    ENNReal.toReal_ofReal hr.le]

end DegenerateCompactSets

end TauCeti
