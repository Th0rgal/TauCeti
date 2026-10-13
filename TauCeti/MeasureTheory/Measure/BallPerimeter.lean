/-
Copyright (c) 2026 General Intelligence, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.MeasureTheory.Measure.BoxPerimeter
import all TauCeti.MeasureTheory.Measure.Perimeter
import all TauCeti.MeasureTheory.Measure.PerimeterTransport
import all TauCeti.MeasureTheory.Measure.PerimeterCutoff
import all TauCeti.MeasureTheory.Measure.BoxPerimeter

/-!
# Exact Perimeter of Balls and Annuli and the Ball Isoperimetric Identity

This file establishes the disjoint-open superadditivity of distributional variation and relative
perimeter, the exact Caccioppoli perimeter of open and closed Euclidean balls and concentric
annuli in any finite-dimensional real inner product space, and the exact dimensional isoperimetric
identity for Euclidean balls.

## Main Definitions

* `TauCeti.cubicCutoff`, `TauCeti.cubicCutoffDeriv`: the $C^1$ cubic Hermite cutoff on $\mathbb{R}$
  equal to $1$ on $(-\infty, 0]$, $1 - 3t^2 + 2t^3$ on $(0, 1)$, and $0$ on $[1, \infty)$, together
  with its continuous derivative $\min(0, -6t(1-t))$.
* `TauCeti.radialCubicCutoff`: the $C^1$ radial cutoff supported in $\overline{B}(c, r)$ and equal
  to $1$ on $\overline{B}(c, r - \varepsilon)$.

## Main Results

* `TauCeti.distributionalVariation_add_le_sup_of_disjoint`,
  `TauCeti.relativePerimeter_add_le_sup_of_disjoint`,
  `TauCeti.relativePerimeter_add_le_perimeter_of_disjoint`: superadditivity over disjoint opens.
* `TauCeti.integral_divergence_eq_zero_of_contDiff_one`,
  `TauCeti.integral_mul_divergence_eq_neg_integral_fderiv`: global divergence theorem and
  integration by parts for compactly supported $C^1$ fields.
* `TauCeti.perimeter_ball`, `TauCeti.perimeter_closedBall`,
  `TauCeti.perimeter_ball_eq_unitBall`, `TauCeti.perimeter_closedBall_eq_unitBall`,
  `TauCeti.hasFinitePerimeter_ball`, `TauCeti.hasFinitePerimeter_closedBall`: exact perimeter and
  finiteness of perimeter for open and closed balls.
* `TauCeti.perimeter_closedBall_diff_ball`, `TauCeti.perimeter_ball_diff_ball`,
  `TauCeti.perimeter_ball_diff_closedBall`: exact perimeter of concentric annuli.
* `TauCeti.perimeter_ball_pow_finrank`, `TauCeti.perimeter_closedBall_pow_finrank`: the exact
  dimensional isoperimetric identity $P(B(c, r))^n = n^n \omega_n \mu(B(c, r))^{n-1}$.
-/

open Filter Function MeasureTheory Pointwise Set TopologicalSpace TestFunction
open scoped ENNReal NNReal InnerProductSpace Distributions Topology

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-! ### Section 1: Disjoint-open superadditivity of variation and relative perimeter -/

section DisjointOpenSuperadditivity

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

/-- Distributional variation is superadditive over disjoint open sets `U₁` and `U₂`. -/
theorem distributionalVariation_add_le_sup_of_disjoint {U₁ U₂ : Opens E}
    (h : Disjoint (U₁ : Set E) (U₂ : Set E)) (u : E → ℝ) :
    distributionalVariation μ U₁ u + distributionalVariation μ U₂ u ≤
      distributionalVariation μ (U₁ ⊔ U₂) u := by
  have h1 : ∀ (φ₁ : 𝓓(U₁, E)) (_ : ∀ x, ‖φ₁ x‖ ≤ 1) (φ₂ : 𝓓(U₂, E)) (_ : ∀ x, ‖φ₂ x‖ ≤ 1),
      ENNReal.ofReal (∫ x in (U₁ : Set E), u x * divergence (φ₁ : E → E) x ∂μ) +
        ENNReal.ofReal (∫ x in (U₂ : Set E), u x * divergence (φ₂ : E → E) x ∂μ) ≤
      distributionalVariation μ (U₁ ⊔ U₂) u := by
    intro φ₁ hφ₁ φ₂ hφ₂
    set I₁ := ∫ x in (U₁ : Set E), u x * divergence (φ₁ : E → E) x ∂μ
    set I₂ := ∫ x in (U₂ : Set E), u x * divergence (φ₂ : E → E) x ∂μ
    rcases le_or_gt I₁ 0 with hI₁ | hI₁
    · rw [ENNReal.ofReal_of_nonpos hI₁, zero_add]
      exact (le_distributionalVariation φ₂ hφ₂ u).trans
        (distributionalVariation_mono le_sup_right u)
    rcases le_or_gt I₂ 0 with hI₂ | hI₂
    · rw [ENNReal.ofReal_of_nonpos hI₂, add_zero]
      exact (le_distributionalVariation φ₁ hφ₁ u).trans
        (distributionalVariation_mono le_sup_left u)
    have hint₁ : IntegrableOn (fun x ↦ u x * divergence (φ₁ : E → E) x) U₁ μ := by
      by_contra hni; exact hI₁.ne' (integral_undef hni)
    have hint₂ : IntegrableOn (fun x ↦ u x * divergence (φ₂ : E → E) x) U₂ μ := by
      by_contra hni; exact hI₂.ne' (integral_undef hni)
    have hU₁ : U₁ ≤ U₁ ⊔ U₂ := le_sup_left
    have hU₂ : U₂ ≤ U₁ ⊔ U₂ := le_sup_right
    let ψ : 𝓓(U₁ ⊔ U₂, E) := TestFunction.monoCLM ℝ φ₁ + TestFunction.monoCLM ℝ φ₂
    have hψ_apply : ∀ x, ψ x = φ₁ x + φ₂ x := fun x ↦ by
      simp [ψ, TestFunction.monoCLM_apply, hU₁, hU₂]
    have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
      rw [hψ_apply]
      by_cases hx₁ : x ∈ (U₁ : Set E)
      · rw [image_eq_zero_of_notMem_tsupport fun hs ↦
          h.notMem_of_mem_left hx₁ (φ₂.tsupport_subset hs), add_zero]
        exact hφ₁ x
      · rw [image_eq_zero_of_notMem_tsupport fun hs ↦ hx₁ (φ₁.tsupport_subset hs), zero_add]
        exact hφ₂ x
    have hdiv₁ : ∀ x ∈ (U₁ : Set E), divergence (ψ : E → E) x = divergence (φ₁ : E → E) x :=
      fun x hx ↦ by
        have hev : (ψ : E → E) =ᶠ[𝓝 x] (φ₁ : E → E) := by
          filter_upwards [U₁.isOpen.mem_nhds hx] with y hy
          rw [hψ_apply, image_eq_zero_of_notMem_tsupport fun hs ↦
            h.notMem_of_mem_left hy (φ₂.tsupport_subset hs), add_zero]
        rw [divergence, hev.fderiv_eq, ← divergence]
    have hdiv₂ : ∀ x ∈ (U₂ : Set E), divergence (ψ : E → E) x = divergence (φ₂ : E → E) x :=
      fun x hx ↦ by
        have hev : (ψ : E → E) =ᶠ[𝓝 x] (φ₂ : E → E) := by
          filter_upwards [U₂.isOpen.mem_nhds hx] with y hy
          rw [hψ_apply, image_eq_zero_of_notMem_tsupport fun hs ↦
            h.notMem_of_mem_right hy (φ₁.tsupport_subset hs), zero_add]
        rw [divergence, hev.fderiv_eq, ← divergence]
    have hint_sum : ∫ x in ((U₁ ⊔ U₂ : Opens E) : Set E),
        u x * divergence (ψ : E → E) x ∂μ = I₁ + I₂ := by
      change ∫ x in (U₁ : Set E) ∪ (U₂ : Set E), u x * divergence (ψ : E → E) x ∂μ = _
      rw [setIntegral_union h U₂.isOpen.measurableSet
          (hint₁.congr_fun (fun x hx ↦ by rw [hdiv₁ x hx]) U₁.isOpen.measurableSet)
          (hint₂.congr_fun (fun x hx ↦ by rw [hdiv₂ x hx]) U₂.isOpen.measurableSet),
        setIntegral_congr_fun U₁.isOpen.measurableSet (fun x hx ↦ by rw [hdiv₁ x hx]),
        setIntegral_congr_fun U₂.isOpen.measurableSet (fun x hx ↦ by rw [hdiv₂ x hx])]
    rw [← ENNReal.ofReal_add hI₁.le hI₂.le, ← hint_sum]
    exact le_distributionalVariation ψ hψ_norm u
  have : Nonempty {φ : 𝓓(U₁, E) // ∀ x, ‖φ x‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  have : Nonempty {φ : 𝓓(U₂, E) // ∀ x, ‖φ x‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  rw [distributionalVariation, distributionalVariation, iSup_subtype', iSup_subtype',
    ENNReal.iSup_add]
  refine iSup_le fun ⟨φ₁, hφ₁⟩ ↦ ?_
  rw [ENNReal.add_iSup]; exact iSup_le fun ⟨φ₂, hφ₂⟩ ↦ h1 φ₁ hφ₁ φ₂ hφ₂

/-- Relative perimeter is superadditive over disjoint open sets `U₁` and `U₂`. -/
theorem relativePerimeter_add_le_sup_of_disjoint {U₁ U₂ : Opens E}
    (h : Disjoint (U₁ : Set E) (U₂ : Set E)) (s : Set E) :
    relativePerimeter μ U₁ s + relativePerimeter μ U₂ s ≤
      relativePerimeter μ (U₁ ⊔ U₂) s :=
  distributionalVariation_add_le_sup_of_disjoint h _

/-- The sum of relative perimeters in two disjoint open sets is bounded by the global perimeter. -/
theorem relativePerimeter_add_le_perimeter_of_disjoint {U₁ U₂ : Opens E}
    (h : Disjoint (U₁ : Set E) (U₂ : Set E)) (s : Set E) :
    relativePerimeter μ U₁ s + relativePerimeter μ U₂ s ≤ perimeter μ s :=
  (relativePerimeter_add_le_sup_of_disjoint h s).trans (relativePerimeter_mono le_top s)

end DisjointOpenSuperadditivity

/-! ### Section 2: Cubic Hermite cutoff, Euler radial identity, and exact ball perimeter -/

section CubicCutoff

/-- The $C^1$ cubic Hermite cutoff on $\mathbb{R}$, equal to $1$ on $(-\infty, 0]$,
$1 - 3t^2 + 2t^3$ on $(0, 1)$, and $0$ on $[1, \infty)$. -/
noncomputable def cubicCutoff (t : ℝ) : ℝ :=
  if t ≤ 0 then 1 else if t < 1 then 1 - 3 * t ^ 2 + 2 * t ^ 3 else 0

/-- The derivative of `cubicCutoff`, given globally by $\min(0, -6t(1-t))$. -/
noncomputable def cubicCutoffDeriv (t : ℝ) : ℝ :=
  min 0 (-6 * t * (1 - t))

/-- On $(-\infty, 0]$, `cubicCutoff` is identically $1$. -/
theorem cubicCutoff_of_nonpos {t : ℝ} (ht : t ≤ 0) : cubicCutoff t = 1 := by simp [cubicCutoff, ht]

/-- On $[1, \infty)$, `cubicCutoff` is identically $0$. -/
theorem cubicCutoff_of_one_le {t : ℝ} (ht : 1 ≤ t) : cubicCutoff t = 0 := by
  simp [cubicCutoff, not_le.2 (zero_lt_one.trans_le ht), not_lt.2 ht]

/-- `cubicCutoff` is everywhere nonnegative. -/
theorem cubicCutoff_nonneg (t : ℝ) : 0 ≤ cubicCutoff t := by
  unfold cubicCutoff; split_ifs with h1 h2
  · exact zero_le_one
  · exact (show 1 - 3 * t ^ 2 + 2 * t ^ 3 = (1 - t) ^ 2 * (1 + 2 * t) by ring) ▸
      mul_nonneg (sq_nonneg _) (by linarith)
  · exact le_rfl

/-- `cubicCutoff` is everywhere bounded above by $1$. -/
theorem cubicCutoff_le_one (t : ℝ) : cubicCutoff t ≤ 1 := by
  unfold cubicCutoff; split_ifs with h1 h2
  · exact le_rfl
  · have : 0 ≤ t ^ 2 * (3 - 2 * t) := mul_nonneg (sq_nonneg t) (by linarith)
    linarith
  · exact zero_le_one

/-- `cubicCutoff` has derivative `cubicCutoffDeriv t` at every $t \in \mathbb{R}$. -/
theorem hasDerivAt_cubicCutoff (t : ℝ) : HasDerivAt cubicCutoff (cubicCutoffDeriv t) t := by
  let P : ℝ → ℝ := fun s ↦ 1 - 3 * s ^ 2 + 2 * s ^ 3
  have hP_eq : ∀ s ∈ Icc 0 1, cubicCutoff s = P s := fun s ⟨hs0, hs1⟩ ↦ by
    unfold cubicCutoff; split_ifs with h1 h2
    · rw [le_antisymm h1 hs0]; simp [P]
    · rfl
    · rw [le_antisymm hs1 (not_lt.1 h2)]; simp [P]; ring
  have hP_deriv : ∀ s, HasDerivAt P (-6 * s * (1 - s)) s := fun s ↦ by
    have hd2 : HasDerivAt (fun u ↦ 3 * u ^ 2) (3 * (2 * s ^ (2 - 1) * 1)) s :=
      ((hasDerivAt_id s).pow 2).const_mul 3
    have hd3 : HasDerivAt (fun u ↦ 2 * u ^ 3) (2 * (3 * s ^ (3 - 1) * 1)) s :=
      ((hasDerivAt_id s).pow 3).const_mul 2
    convert ((hasDerivAt_const s (1 : ℝ)).sub hd2).add hd3 using 1; ring
  have hIic : ∀ s ≤ 0, HasDerivWithinAt cubicCutoff 0 (Iic 0) s := fun s hs ↦
    (hasDerivWithinAt_const s (Iic 0) 1).congr (fun _ ↦ cubicCutoff_of_nonpos)
      (cubicCutoff_of_nonpos hs)
  have hIcc : ∀ s ∈ Icc 0 1, HasDerivWithinAt cubicCutoff (-6 * s * (1 - s)) (Icc 0 1) s :=
    fun s hs ↦ (hP_deriv s).hasDerivWithinAt.congr (fun u hu ↦ hP_eq u hu) (hP_eq s hs)
  have hIci : ∀ s, 1 ≤ s → HasDerivWithinAt cubicCutoff 0 (Ici 1) s := fun s hs ↦
    (hasDerivWithinAt_const s (Ici 1) 0).congr (fun _ ↦ cubicCutoff_of_one_le)
      (cubicCutoff_of_one_le hs)
  rcases lt_trichotomy t 0 with ht0 | rfl | ht0
  · rw [show cubicCutoffDeriv t = 0 from min_eq_left (by nlinarith)]
    exact (hIic t ht0.le).hasDerivAt (Iic_mem_nhds ht0)
  · simp only [cubicCutoffDeriv, mul_zero, zero_mul, min_self]
    have hmem : Iic (0 : ℝ) ∪ Icc 0 1 ∈ 𝓝 0 := mem_of_superset (Iic_mem_nhds zero_lt_one)
      fun u hu ↦ (le_total u 0).imp id fun h ↦ ⟨h, hu⟩
    exact ((hIic 0 le_rfl).union (by simpa using hIcc 0 ⟨le_rfl, zero_le_one⟩)).hasDerivAt hmem
  · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
    · rw [show cubicCutoffDeriv t = -6 * t * (1 - t) from min_eq_right (by nlinarith)]
      exact (hIcc t ⟨ht0.le, ht1.le⟩).hasDerivAt (Icc_mem_nhds ht0 ht1)
    · simp only [cubicCutoffDeriv, sub_self, mul_zero, min_self]
      have hmem : Ici (1 : ℝ) ∪ Icc 0 1 ∈ 𝓝 1 := mem_of_superset (Ici_mem_nhds zero_lt_one)
        fun u hu ↦ (le_total 1 u).imp id fun h ↦ ⟨hu, h⟩
      exact ((hIci 1 le_rfl).union (by simpa using hIcc 1 ⟨zero_le_one, le_rfl⟩)).hasDerivAt hmem
    · rw [show cubicCutoffDeriv t = 0 from min_eq_left (by nlinarith)]
      exact (hIci t ht1.le).hasDerivAt (Ici_mem_nhds ht1)

/-- `cubicCutoff` is $C^1$ on $\mathbb{R}$. -/
theorem contDiff_cubicCutoff : ContDiff ℝ 1 cubicCutoff :=
  contDiff_one_iff_deriv.2 ⟨fun t ↦ (hasDerivAt_cubicCutoff t).differentiableAt,
    by rw [deriv_eq hasDerivAt_cubicCutoff]; unfold cubicCutoffDeriv; fun_prop⟩

/-- The integral of the divergence of a compactly supported $C^1$ vector field on
`EuclideanSpace ℝ (Fin n)` vanishes. -/
theorem integral_divergence_eq_zero_euclidean {n : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hΨ : ContDiff ℝ 1 Ψ) (hsupp : HasCompactSupport Ψ) :
    ∫ x, divergence Ψ x = 0 := by
  obtain ⟨r, hr⟩ := hsupp.isCompact.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  let R : ℝ := max r 1
  have hRpos : 0 < R := lt_max_of_lt_right zero_lt_one
  have hsubR : tsupport Ψ ⊆ Metric.ball 0 R :=
    hr.trans (Metric.ball_subset_ball (le_max_left r 1))
  have hab : ∀ _ : Fin n, -R ≤ R := fun _ ↦ by linarith
  have hball_box : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ⊆
      euclideanBox (fun _ ↦ -R) (fun _ ↦ R) := fun x hx i ↦
    ⟨(neg_lt_of_abs_lt ((Real.norm_eq_abs (x i) ▸ PiLp.norm_apply_le x i).trans_lt
      (by simpa using hx))).le,
     (lt_of_abs_lt ((Real.norm_eq_abs (x i) ▸ PiLp.norm_apply_le x i).trans_lt
      (by simpa using hx))).le⟩
  have hcompl : ∀ x ∉ euclideanBox (fun _ ↦ -R) (fun _ ↦ R), divergence Ψ x = 0 := fun x hx ↦ by
    have hev : Ψ =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 fun hs ↦ hx (hball_box (hsubR hs))
    rw [divergence, hev.fderiv_eq]; simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl,
    integral_euclideanBox_divergence hab hΨ]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hface : ∀ (t : ℝ), |t| = R → ∀ x' : {k : Fin n // k ≠ i} → ℝ,
      Ψ (boxSlice i x' t) = 0 := fun t ht x' ↦
    image_eq_zero_of_notMem_tsupport fun hs ↦ (by simpa using hsubR hs :
      ‖boxSlice i x' t‖ < R).not_ge <| by
        calc R = ‖boxSlice i x' t i‖ := by rw [← ht, boxSlice_apply_eq, Real.norm_eq_abs]
          _ ≤ ‖boxSlice i x' t‖ := PiLp.norm_apply_le (boxSlice i x' t) i
  simp [hface R (abs_of_pos hRpos), hface (-R) (by rw [abs_neg, abs_of_pos hRpos])]

/-- The divergence of a $C^1$ vector field on a finite-dimensional inner product space is
continuous. -/
theorem continuous_divergence_of_contDiff_one [FiniteDimensional ℝ E] {Ψ : E → E}
    (hΨ : ContDiff ℝ 1 Ψ) : Continuous (divergence Ψ) := by
  rw [funext fun x ↦ divergence_eq_sum_orthonormalBasis (stdOrthonormalBasis ℝ E) Ψ x]
  exact continuous_finsetSum _ fun i _ ↦
    continuous_const.inner ((hΨ.continuous_fderiv one_ne_zero).clm_apply continuous_const)

/-- The $C^1$ radial cutoff equal to $1$ on $\overline{B}(c, r-\varepsilon)$ and vanishing outside
$B(c, r)$. -/
noncomputable def radialCubicCutoff (c : E) (r ε : ℝ) (x : E) : ℝ :=
  cubicCutoff ((‖x - c‖ ^ 2 - (r - ε) ^ 2) / (r ^ 2 - (r - ε) ^ 2))

/-- `radialCubicCutoff c r ε` has Fréchet derivative proportional to `innerSL ℝ (x - c)`. -/
theorem hasFDerivAt_radialCubicCutoff (c : E) (r ε : ℝ) (x : E) :
    HasFDerivAt (radialCubicCutoff c r ε)
      ((cubicCutoffDeriv ((‖x - c‖ ^ 2 - (r - ε) ^ 2) / (r ^ 2 - (r - ε) ^ 2)) *
        (2 / (r ^ 2 - (r - ε) ^ 2))) • innerSL ℝ (x - c)) x := by
  have hd1 : HasDerivAt (fun u : ℝ ↦ cubicCutoff ((u - (r - ε) ^ 2) / (r ^ 2 - (r - ε) ^ 2)))
      (cubicCutoffDeriv ((‖x - c‖ ^ 2 - (r - ε) ^ 2) / (r ^ 2 - (r - ε) ^ 2)) *
        (1 / (r ^ 2 - (r - ε) ^ 2))) (‖x - c‖ ^ 2) :=
    (hasDerivAt_cubicCutoff _).comp (‖x - c‖ ^ 2)
      (((hasDerivAt_id _).sub_const _).div_const _)
  have hd2 : HasFDerivAt (fun y : E ↦ ‖y - c‖ ^ 2) ((2 : ℝ) • innerSL ℝ (x - c)) x := by
    simpa [two_smul] using ((hasFDerivAt_id x).sub_const c).norm_sq
  have hd := hd1.comp_hasFDerivAt x hd2
  rwa [smul_smul, mul_assoc, one_div_mul_eq_div] at hd

/-- `radialCubicCutoff c r ε` is $C^1$ on $E$. -/
theorem contDiff_radialCubicCutoff (c : E) (r ε : ℝ) :
    ContDiff ℝ 1 (radialCubicCutoff c r ε) :=
  contDiff_cubicCutoff.comp
    (((((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const).div_const _).of_le le_top)

omit [InnerProductSpace ℝ E] in
/-- Outside $B(c, r)$, `radialCubicCutoff c r ε` vanishes. -/
theorem radialCubicCutoff_of_notMem_ball (c : E) {r ε : ℝ} (hε : 0 < ε) (hεr : ε < r)
    {x : E} (hx : x ∉ Metric.ball c r) : radialCubicCutoff c r ε x = 0 := by
  have hrx : r ≤ ‖x - c‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  exact cubicCutoff_of_one_le ((one_le_div (by nlinarith)).2 (by nlinarith))

/-- Pointwise radial gradient bound: the operator norm of the Fréchet derivative of
`radialCubicCutoff c r ε` is bounded by $(r - \varepsilon)^{-1}$ times $-Df(x)(x - c)$. -/
theorem norm_fderiv_radialCubicCutoff_le (c : E) {r ε : ℝ} (hε : 0 < ε) (hεr : ε < r) (x : E) :
    ‖fderiv ℝ (radialCubicCutoff c r ε) x‖ ≤
      (r - ε)⁻¹ * (-fderiv ℝ (radialCubicCutoff c r ε) x (x - c)) := by
  have hD : 0 < r ^ 2 - (r - ε) ^ 2 := by nlinarith
  have hre : 0 < r - ε := sub_pos.2 hεr
  rw [(hasFDerivAt_radialCubicCutoff c r ε x).fderiv]
  set s := (‖x - c‖ ^ 2 - (r - ε) ^ 2) / (r ^ 2 - (r - ε) ^ 2)
  set d := cubicCutoffDeriv s * (2 / (r ^ 2 - (r - ε) ^ 2))
  have hd_nonpos : d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (min_le_left 0 _) (by positivity)
  have hnorm : ‖d • innerSL ℝ (x - c)‖ ≤ -d * ‖x - c‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hd_nonpos]
    exact mul_le_mul_of_nonneg_left (innerSL_apply_norm ℝ (x - c)).le (by linarith)
  have happly : -((d • innerSL ℝ (x - c)) (x - c)) = -d * ‖x - c‖ ^ 2 := by
    rw [smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul]; ring
  rw [happly]
  refine hnorm.trans ?_
  rcases le_or_gt ‖x - c‖ (r - ε) with hle | hgt
  · have hs0 : s ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (x - c)]) hD.le
    have hcs0 : cubicCutoffDeriv s = 0 := min_eq_left (by nlinarith)
    simp [d, hcs0]
  · have hinv : (r - ε)⁻¹ * (r - ε) = 1 := inv_mul_cancel₀ hre.ne'
    calc -d * ‖x - c‖
        = (r - ε)⁻¹ * (-d * ((r - ε) * ‖x - c‖)) := by linear_combination (d * ‖x - c‖) * hinv
      _ ≤ (r - ε)⁻¹ * (-d * ‖x - c‖ ^ 2) := by
          gcongr; · linarith
          · nlinarith [norm_nonneg (x - c)]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For a compactly supported $C^1$ scalar function `η` and a continuous vector field `ψ`, the
directional derivative `x ↦ fderiv ℝ η x (ψ x)` is integrable on locally finite measures. -/
theorem integrable_fderiv_apply_of_hasCompactSupport [NormedSpace ℝ E]
    [IsFiniteMeasureOnCompacts μ] {η : E → ℝ} {ψ : E → E}
    (hη : ContDiff ℝ 1 η) (hsupp : HasCompactSupport η) (hψ : Continuous ψ) :
    Integrable (fun x ↦ fderiv ℝ η x (ψ x)) μ := by
  refine ((hη.continuous_fderiv one_ne_zero).clm_apply hψ).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact hsupp.isCompact fun x hx ↦ ?_
  by_contra hxs
  have hev : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxs
  exact hx (by dsimp; rw [hev.fderiv_eq]; simp)

variable [μ.IsAddHaarMeasure]

/-- Global divergence theorem for compactly supported $C^1$ vector fields on any finite-dimensional
real inner product space equipped with an additive Haar measure. -/
theorem integral_divergence_eq_zero_of_contDiff_one {Ψ : E → E}
    (hΨ : ContDiff ℝ 1 Ψ) (hsupp : HasCompactSupport Ψ) :
    ∫ x, divergence Ψ x ∂μ = 0 := by
  have hsupp_div : HasCompactSupport (divergence Ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact hsupp.isCompact fun x hx ↦ ?_
    by_contra hxs
    exact hx (by rw [divergence, (notMem_tsupport_iff_eventuallyEq.1 hxs).fderiv_eq]; simp)
  rw [Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport μ (volume : Measure E)
    (continuous_divergence_of_contDiff_one hΨ) hsupp_div, integral_smul_nnreal_measure]
  let L : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := (stdOrthonormalBasis ℝ E).repr
  let Ψ' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun z ↦ L (Ψ (L.symm z))
  have hΨ' : ContDiff ℝ 1 Ψ' := L.contDiff.comp (hΨ.comp L.symm.contDiff)
  have hsupp' : HasCompactSupport Ψ' :=
    (hsupp.comp_homeomorph L.symm.toHomeomorph).comp_left (map_zero L)
  have hint : ∫ x, divergence Ψ x ∂(volume : Measure E) = ∫ z, divergence Ψ' z := by
    rw [← L.symm.measurePreserving.integral_comp' (f := L.symm.toHomeomorph.toMeasurableEquiv)]
    exact integral_congr_ae (Eventually.of_forall fun z ↦
      (divergence_conj_linearIsometryEquiv L Ψ z).symm)
  rw [hint, integral_divergence_eq_zero_euclidean hΨ' hsupp', smul_zero]

/-- Integration by parts for a compactly supported $C^1$ scalar function `η` against a $C^1$
vector field `φ`: $\int \eta\,\mathrm{div}\,\varphi\,d\mu = -\int D\eta(\varphi)\,d\mu$. -/
theorem integral_mul_divergence_eq_neg_integral_fderiv {η : E → ℝ} {φ : E → E}
    (hη : ContDiff ℝ 1 η) (hsupp : HasCompactSupport η) (hφ : ContDiff ℝ 1 φ) :
    ∫ x, η x * divergence φ x ∂μ = -∫ x, fderiv ℝ η x (φ x) ∂μ := by
  have hzero := integral_divergence_eq_zero_of_contDiff_one (μ := μ)
    (Ψ := fun y ↦ η y • φ y) (hη.smul hφ) hsupp.smul_right
  have hdiv : (fun x ↦ divergence (fun y ↦ η y • φ y) x) =
      fun x ↦ η x * divergence φ x + fderiv ℝ η x (φ x) :=
    funext fun x ↦ divergence_smul (hη.differentiable one_ne_zero x)
      (hφ.differentiable one_ne_zero x)
  have hint1 : Integrable (fun x ↦ η x * divergence φ x) μ :=
    (hη.continuous.mul (continuous_divergence_of_contDiff_one hφ)).integrable_of_hasCompactSupport
      hsupp.mul_right
  have hint2 : Integrable (fun x ↦ fderiv ℝ η x (φ x)) μ :=
    integrable_fderiv_apply_of_hasCompactSupport hη hsupp hφ.continuous
  rw [hdiv, integral_add hint1 hint2] at hzero
  linarith

/-- The distributional variation of `radialCubicCutoff c r ε` in any open set `Ω` is bounded by
$(n / (r - \varepsilon))\,\mu(B(c, r))$. -/
theorem distributionalVariation_radialCubicCutoff_le (c : E) {r ε : ℝ}
    (hε : 0 < ε) (hεr : ε < r) :
    distributionalVariation μ Ω (radialCubicCutoff c r ε) ≤
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / (r - ε)) * μ (Metric.ball c r) := by
  have hre : 0 < r - ε := sub_pos.2 hεr
  have hcont := contDiff_radialCubicCutoff c r ε
  have hsupp : HasCompactSupport (radialCubicCutoff c r ε) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) fun x hx ↦ ?_
    by_contra hxr
    exact hx (radialCubicCutoff_of_notMem_ball c hε hεr
      fun h ↦ hxr (Metric.ball_subset_closedBall h))
  have heuler : ∫ x, -fderiv ℝ (radialCubicCutoff c r ε) x (x - c) ∂μ =
      (Module.finrank ℝ E : ℝ) * ∫ x, radialCubicCutoff c r ε x ∂μ := by
    have h1 := integral_mul_divergence_eq_neg_integral_fderiv (μ := μ)
      (φ := fun y : E ↦ y - c) hcont hsupp (contDiff_id.sub (contDiff_const (c := c)))
    simp_rw [divergence_sub_const c, mul_comm (radialCubicCutoff c r ε _) (Module.finrank ℝ E : ℝ)]
      at h1
    rw [integral_const_mul] at h1; rw [integral_neg, ← h1]
  refine iSup₂_le fun φ hφ ↦ ?_
  rw [setIntegral_mul_divergence_eq_integral,
    integral_mul_divergence_eq_neg_integral_fderiv hcont hsupp (φ.contDiff.of_le (by simp)),
    ← integral_neg]
  have hle1 : ∫ x, -fderiv ℝ (radialCubicCutoff c r ε) x (φ x) ∂μ ≤
      ∫ x, (r - ε)⁻¹ * (-fderiv ℝ (radialCubicCutoff c r ε) x (x - c)) ∂μ := by
    refine integral_mono
      (integrable_fderiv_apply_of_hasCompactSupport hcont hsupp φ.continuous).neg
      (((integrable_fderiv_apply_of_hasCompactSupport hcont hsupp
        (continuous_id.sub continuous_const)).neg).const_mul _) fun x ↦ ?_
    calc -fderiv ℝ (radialCubicCutoff c r ε) x (φ x)
        ≤ ‖fderiv ℝ (radialCubicCutoff c r ε) x‖ * ‖φ x‖ :=
          (le_abs_self _).trans (by simpa using
            (fderiv ℝ (radialCubicCutoff c r ε) x).le_opNorm (φ x))
      _ ≤ ‖fderiv ℝ (radialCubicCutoff c r ε) x‖ := by
          simpa using mul_le_mul_of_nonneg_left (hφ x) (norm_nonneg _)
      _ ≤ (r - ε)⁻¹ * (-fderiv ℝ (radialCubicCutoff c r ε) x (x - c)) :=
          norm_fderiv_radialCubicCutoff_le c hε hεr x
  have hint_ind : Integrable ((Metric.ball c r).indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  have hle2 : ∫ x, radialCubicCutoff c r ε x ∂μ ≤ (μ (Metric.ball c r)).toReal := by
    refine (integral_mono (hcont.continuous.integrable_of_hasCompactSupport hsupp) hint_ind
      fun x ↦ ?_).trans_eq ?_
    · by_cases hx : x ∈ Metric.ball c r
      · simp [hx, radialCubicCutoff, cubicCutoff_le_one]
      · simp [hx, radialCubicCutoff_of_notMem_ball c hε hεr hx]
    · rw [integral_indicator measurableSet_ball, setIntegral_const, Measure.real, smul_eq_mul,
        mul_one]
  have hle3 : ∫ x, -fderiv ℝ (radialCubicCutoff c r ε) x (φ x) ∂μ ≤
      ((Module.finrank ℝ E : ℝ) / (r - ε)) * (μ (Metric.ball c r)).toReal := by
    refine hle1.trans ?_
    rw [integral_const_mul, heuler, ← mul_assoc, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hle2 (by positivity)
  refine (ENNReal.ofReal_le_ofReal hle3).trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal measure_ball_lt_top.ne]

/-- Upper bound for the relative perimeter of an open ball $B(c, r)$ in any open set `Ω`. -/
theorem relativePerimeter_ball_le (c : E) {r : ℝ} (hr : 0 < r) :
    relativePerimeter μ Ω (Metric.ball c r) ≤
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / r) * μ (Metric.ball c r) := by
  let ε : ℕ → ℝ := fun k ↦ r / (k + 2 : ℝ)
  have hε_pos : ∀ k, 0 < ε k := fun k ↦ div_pos hr (by positivity)
  have hε_lt : ∀ k, ε k < r := fun k ↦ div_lt_self hr (by linarith : (1 : ℝ) < (k : ℝ) + 2)
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ ↦ 1 / ((k + 1 : ℕ) + 1 : ℝ)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    exact (mul_zero r ▸ (tendsto_const_nhds (x := r)).mul h1).congr fun k ↦ by
      dsimp [ε]; push_cast; ring
  have hpt : ∀ x : E, Tendsto (fun k ↦ radialCubicCutoff c r (ε k) x) atTop
      (𝓝 ((Metric.ball c r).indicator (fun _ ↦ (1 : ℝ)) x)) := fun x ↦ by
    by_cases hx : x ∈ Metric.ball c r
    · rw [indicator_of_mem hx]
      have hdist : 0 < r - ‖x - c‖ := sub_pos.2 (by simpa [Metric.mem_ball, dist_eq_norm] using hx)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hε_tendsto.eventually (gt_mem_nhds hdist)] with k hk
      exact (cubicCutoff_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by nlinarith [norm_nonneg (x - c), hε_pos k, hε_lt k])
        (by nlinarith [hε_pos k, hε_lt k]))).symm
    · rw [indicator_of_notMem hx]
      exact tendsto_const_nhds.congr fun k ↦
        (radialCubicCutoff_of_notMem_ball c (hε_pos k) (hε_lt k) hx).symm
  have hconv : ∀ φ : 𝓓(Ω, E),
      Tendsto (fun k ↦ ∫ x in (Ω : Set E),
        radialCubicCutoff c r (ε k) x * divergence (φ : E → E) x ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E),
          (Metric.ball c r).indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ)) := by
    intro φ
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖divergence (φ : E → E) x‖) ?_ (integrableOn_divergence_testFunction φ).norm ?_ ?_
    · exact fun k ↦ ((contDiff_radialCubicCutoff c r (ε k)).continuous.mul
        (continuous_divergence_of_contDiff_one (φ.contDiff.of_le (by simp)))).aestronglyMeasurable
    · intro k; filter_upwards with x
      unfold radialCubicCutoff; rw [norm_mul, Real.norm_of_nonneg (cubicCutoff_nonneg _)]
      exact (mul_le_mul_of_nonneg_right (cubicCutoff_le_one _) (norm_nonneg _)).trans (by simp)
    · filter_upwards with x; exact (hpt x).mul tendsto_const_nhds
  have hlim_rhs : Tendsto
      (fun k ↦ ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / (r - ε k)) * μ (Metric.ball c r))
      atTop (𝓝 (ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / r) * μ (Metric.ball c r))) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr measure_ball_lt_top.ne)
    refine (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.div ?_ hr.ne')
    simpa using tendsto_const_nhds.sub hε_tendsto
  refine (distributionalVariation_le_liminf hconv).trans ?_
  rw [← hlim_rhs.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun k ↦
    distributionalVariation_radialCubicCutoff_le c (hε_pos k) (hε_lt k))

/-- Upper bound for the Caccioppoli perimeter of an open ball $B(c, r)$ with $r > 0$. -/
theorem perimeter_ball_le (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter μ (Metric.ball c r) ≤
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / r) * μ (Metric.ball c r) :=
  relativePerimeter_ball_le c hr

/-- Exact Caccioppoli perimeter of an open ball $B(c, r)$ with $r > 0$. -/
theorem perimeter_ball (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter μ (Metric.ball c r) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / r) * μ (Metric.ball c r) :=
  le_antisymm (perimeter_ball_le c hr) (perimeter_ball_ge c hr)

/-- Exact Caccioppoli perimeter of a closed ball $\overline{B}(c, r)$ with $r > 0$. -/
theorem perimeter_closedBall (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter μ (Metric.closedBall c r) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) / r) * μ (Metric.closedBall c r) := by
  rcases subsingleton_or_nontrivial E with _ | _
  · simp [perimeter_eq_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  · rw [perimeter_closedBall_eq_ball, Measure.addHaar_closedBall μ c hr.le,
      ← Measure.addHaar_ball μ c hr.le, perimeter_ball c hr]

/-- Exact Caccioppoli perimeter of an open ball $B(c, r)$ in terms of the unit ball measure. -/
theorem perimeter_ball_eq_unitBall [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter μ (Metric.ball c r) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * r ^ (Module.finrank ℝ E - 1)) *
        μ (Metric.ball (0 : E) 1) := by
  rw [perimeter_ball c hr, Measure.addHaar_ball μ c hr.le, ← mul_assoc,
    ← ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) hr.le)]
  congr 2
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hrpow : r ^ Module.finrank ℝ E = r * r ^ (Module.finrank ℝ E - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ']
  rw [hrpow]; field_simp

/-- Exact Caccioppoli perimeter of a closed ball $\overline{B}(c, r)$ in terms of the unit ball. -/
theorem perimeter_closedBall_eq_unitBall [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter μ (Metric.closedBall c r) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * r ^ (Module.finrank ℝ E - 1)) *
        μ (Metric.ball (0 : E) 1) := by
  rw [perimeter_closedBall_eq_ball, perimeter_ball_eq_unitBall c hr]

/-- Every open ball $B(c, r)$ has finite Caccioppoli perimeter for any $r \in \mathbb{R}$. -/
theorem perimeter_ball_lt_top (c : E) (r : ℝ) : perimeter μ (Metric.ball c r) < ⊤ := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Metric.ball_eq_empty.2 hr]
  · rw [perimeter_ball c hr]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- Every closed ball $\overline{B}(c, r)$ has finite Caccioppoli perimeter. -/
theorem perimeter_closedBall_lt_top (c : E) (r : ℝ) : perimeter μ (Metric.closedBall c r) < ⊤ :=
  perimeter_closedBall_eq_ball (μ := μ) c r ▸ perimeter_ball_lt_top c r

/-- Every open ball $B(c, r)$ is a Caccioppoli set of finite perimeter. -/
theorem hasFinitePerimeter_ball (c : E) (r : ℝ) : HasFinitePerimeter μ (Metric.ball c r) :=
  ⟨measurableSet_ball.nullMeasurableSet, perimeter_ball_lt_top c r⟩

/-- Every closed ball $\overline{B}(c, r)$ is a Caccioppoli set of finite perimeter. -/
theorem hasFinitePerimeter_closedBall (c : E) (r : ℝ) :
    HasFinitePerimeter μ (Metric.closedBall c r) :=
  ⟨measurableSet_closedBall.nullMeasurableSet, perimeter_closedBall_lt_top c r⟩

/-- Every open ball $B(c, r)$ has finite relative perimeter in any open set `Ω`. -/
theorem hasFinitePerimeterIn_ball (Ω : Opens E) (c : E) (r : ℝ) :
    HasFinitePerimeterIn μ Ω (Metric.ball c r) :=
  ⟨measurableSet_ball.nullMeasurableSet,
    (relativePerimeter_mono (le_top : Ω ≤ ⊤) _).trans_lt (perimeter_ball_lt_top c r)⟩

/-- Every closed ball $\overline{B}(c, r)$ has finite relative perimeter in any open set `Ω`. -/
theorem hasFinitePerimeterIn_closedBall (Ω : Opens E) (c : E) (r : ℝ) :
    HasFinitePerimeterIn μ Ω (Metric.closedBall c r) :=
  ⟨measurableSet_closedBall.nullMeasurableSet,
    (relativePerimeter_mono (le_top : Ω ≤ ⊤) _).trans_lt (perimeter_closedBall_lt_top c r)⟩

end CubicCutoff

/-! ### Section 3: Localized ball perimeter and exact perimeter of concentric annuli -/

section AnnulusPerimeter

omit [InnerProductSpace ℝ E] in
/-- In any real normed space, $B(c, r + \delta)$ is contained in the $\delta$-thickening of
$\overline{B}(c, r)$ for $r, \delta > 0$. -/
theorem ball_add_subset_thickening_closedBall [NormedSpace ℝ E] (c : E) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) :
    Metric.ball c (r + δ) ⊆ Metric.thickening δ (Metric.closedBall c r) := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hrd : 0 < r + δ := add_pos hr hδ
  refine Metric.mem_thickening_iff.2 ⟨c + (r / (r + δ)) • (x - c), ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div, div_le_iff₀ hrd]
    nlinarith [norm_nonneg (x - c)]
  · have hsub : x - (c + (r / (r + δ)) • (x - c)) = (δ / (r + δ)) • (x - c) := by
      have h1 : 1 - r / (r + δ) = δ / (r + δ) := by field_simp; ring
      rw [← h1, sub_smul, one_smul]; abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_eq_mul_div, div_lt_iff₀ hrd]
    nlinarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] {μ : Measure E}

omit [FiniteDimensional ℝ E] in
/-- If a smooth cutoff `η` with values in $[0, 1]$ and topological support in `Ω` equals $1$ on an
open neighborhood `V` of `s`, then `relativePerimeter μ Ω s = perimeter μ s`. -/
theorem relativePerimeter_eq_perimeter_of_contDiff_cutoff {s V : Set E} (hV : IsOpen V)
    (hsV : s ⊆ V) {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ x, 0 ≤ η x)
    (hη1 : ∀ x, η x ≤ 1) (hη_supp : tsupport η ⊆ Ω) (hηV : ∀ x ∈ V, η x = 1) :
    relativePerimeter μ Ω s = perimeter μ s := by
  refine le_antisymm (relativePerimeter_mono (le_top : Ω ≤ ⊤) s) (iSup₂_le fun φ hφ ↦ ?_)
  let ψ : 𝓓(Ω, E) :=
    { toFun := fun x ↦ η x • φ x
      contDiff' := hη.smul φ.contDiff
      hasCompactSupport' := φ.hasCompactSupport.smul_left
      tsupport_subset' := (tsupport_smul_subset_left _ _).trans hη_supp }
  have hψ_norm : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
    change ‖η x • φ x‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (hη0 x)]
    exact (mul_le_mul (hη1 x) (hφ x) (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hdiv : ∀ x ∈ s, divergence (ψ : E → E) x = divergence (φ : E → E) x := fun x hxs ↦ by
    have hev : (ψ : E → E) =ᶠ[𝓝 x] (φ : E → E) := by
      filter_upwards [hV.mem_nhds (hsV hxs)] with y hy
      change η y • φ y = φ y; rw [hηV y hy, one_smul]
    rw [divergence, hev.fderiv_eq, ← divergence]
  have hint : ∫ x in ((⊤ : Opens E) : Set E),
        s.indicator (fun _ ↦ (1 : ℝ)) x * divergence (φ : E → E) x ∂μ =
      ∫ x in (Ω : Set E), s.indicator (fun _ ↦ (1 : ℝ)) x * divergence (ψ : E → E) x ∂μ := by
    rw [setIntegral_mul_divergence_eq_integral (Ω := ⊤),
      setIntegral_mul_divergence_eq_integral (Ω := Ω)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hxs : x ∈ s <;> simp [hxs, hdiv]
  rw [hint]
  exact le_distributionalVariation ψ hψ_norm _

/-- If `s ⊆ Metric.closedBall c r` and `Metric.closedBall c r ⊆ Ω`, then the relative perimeter of
`s` in `Ω` equals its global perimeter. -/
theorem relativePerimeter_eq_perimeter_of_subset_closedBall
    {c : E} {r : ℝ} (hr : 0 < r) {s : Set E} (hs : s ⊆ Metric.closedBall c r)
    (hΩ : Metric.closedBall c r ⊆ Ω) :
    relativePerimeter μ Ω s = perimeter μ s := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall c r).exists_thickening_subset_open Ω.isOpen hΩ
  have hRΩ : Metric.ball c (r + δ) ⊆ Ω :=
    (ball_add_subset_thickening_closedBall c hr hδ).trans hthick
  let χ : ContDiffBump c := ⟨r + δ / 3, r + 2 * δ / 3, by linarith, by linarith⟩
  have hrIn : r < χ.rIn := by change r < r + δ / 3; linarith
  have hrOut : χ.rOut < r + δ := by change r + 2 * δ / 3 < r + δ; linarith
  refine relativePerimeter_eq_perimeter_of_contDiff_cutoff Metric.isOpen_ball
    (hs.trans (Metric.closedBall_subset_ball hrIn)) χ.contDiff
    (fun _ ↦ χ.nonneg) (fun _ ↦ χ.le_one) ?_
    (fun _ hx ↦ χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx))
  rw [χ.tsupport_eq]
  exact (Metric.closedBall_subset_ball hrOut).trans hRΩ

/-- If $\overline{B}(c, r) \subseteq \Omega$, the relative perimeter of $B(c, r)$ in `Ω` equals its
global perimeter. -/
theorem relativePerimeter_ball_eq_perimeter
    (c : E) {r : ℝ} (hr : 0 < r) (hΩ : Metric.closedBall c r ⊆ Ω) :
    relativePerimeter μ Ω (Metric.ball c r) = perimeter μ (Metric.ball c r) :=
  relativePerimeter_eq_perimeter_of_subset_closedBall hr Metric.ball_subset_closedBall hΩ

/-- If $\overline{B}(c, r) \subseteq \Omega$, the relative perimeter of $\overline{B}(c, r)$ in `Ω`
equals its global perimeter. -/
theorem relativePerimeter_closedBall_eq_perimeter
    (c : E) {r : ℝ} (hr : 0 < r) (hΩ : Metric.closedBall c r ⊆ Ω) :
    relativePerimeter μ Ω (Metric.closedBall c r) = perimeter μ (Metric.closedBall c r) :=
  relativePerimeter_eq_perimeter_of_subset_closedBall hr Subset.rfl hΩ

variable [BorelSpace E] [μ.IsAddHaarMeasure]

/-- For $0 < \rho < R$, the relative perimeter of $\overline{B}(c, R)$ in the exterior open set
$\overline{B}(c, \rho)^c$ equals the global perimeter of $\overline{B}(c, R)$. -/
theorem relativePerimeter_closedBall_compl_closedBall_eq_perimeter
    (c : E) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    relativePerimeter μ ⟨(Metric.closedBall c ρ)ᶜ, Metric.isClosed_closedBall.isOpen_compl⟩
      (Metric.closedBall c R) = perimeter μ (Metric.closedBall c R) := by
  let U₂ : Opens E := ⟨(Metric.closedBall c ρ)ᶜ, Metric.isClosed_closedBall.isOpen_compl⟩
  rw [← relativePerimeter_compl (Ω := U₂), ← perimeter_compl]
  let χ : ContDiffBump c := ⟨(2 * ρ + R) / 3, (ρ + 2 * R) / 3, by linarith, by linarith⟩
  refine relativePerimeter_eq_perimeter_of_contDiff_cutoff (Ω := U₂)
    (V := (Metric.closedBall c χ.rOut)ᶜ) Metric.isClosed_closedBall.isOpen_compl
    (compl_subset_compl.2 (Metric.closedBall_subset_closedBall (by dsimp [χ]; linarith)))
    (contDiff_const.sub χ.contDiff) (fun _ ↦ sub_nonneg.2 χ.le_one)
    (fun _ ↦ sub_le_self 1 χ.nonneg) ?_ (fun y hy ↦ ?_)
  · intro x hx hxρ
    have hxb : x ∈ Metric.ball c ((2 * ρ + R) / 3) :=
      Metric.closedBall_subset_ball (by linarith) hxρ
    have hev : (fun y : E ↦ 1 - χ y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with y hy
      simp [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    exact notMem_tsupport_iff_eventuallyEq.2 hev hx
  · simp [image_eq_zero_of_notMem_tsupport (by rwa [χ.tsupport_eq] : y ∉ tsupport χ)]

/-- Exact Caccioppoli perimeter of the concentric spherical shell
$\overline{B}(c, R) \setminus B(c, r)$ for $0 < r < R$. -/
theorem perimeter_closedBall_diff_ball (c : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    perimeter μ (Metric.closedBall c R \ Metric.ball c r) =
      perimeter μ (Metric.closedBall c R) + perimeter μ (Metric.ball c r) := by
  refine le_antisymm (perimeter_closedBall_diff_ball_le c hrR.le) ?_
  let ρ : ℝ := (r + R) / 2
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  let U₁ : Opens E := ⟨Metric.ball c ρ, Metric.isOpen_ball⟩
  let U₂ : Opens E := ⟨(Metric.closedBall c ρ)ᶜ, Metric.isClosed_closedBall.isOpen_compl⟩
  have hdisj : Disjoint (U₁ : Set E) (U₂ : Set E) :=
    disjoint_compl_right.mono_left Metric.ball_subset_closedBall
  have h1 : relativePerimeter μ U₁ (Metric.closedBall c R \ Metric.ball c r) =
      perimeter μ (Metric.ball c r) := by
    have hinter : (Metric.closedBall c R \ Metric.ball c r) ∩ (U₁ : Set E) =
        (Metric.ball c r)ᶜ ∩ (U₁ : Set E) := by
      ext x; simp only [mem_inter_iff, Set.mem_sdiff, mem_compl_iff, U₁]
      exact ⟨fun ⟨⟨_, h2⟩, h3⟩ ↦ ⟨h2, h3⟩, fun ⟨h2, h3⟩ ↦
        ⟨⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball hρR.le h3), h2⟩, h3⟩⟩
    rw [relativePerimeter_eq_of_inter_ae_eq (Filter.EventuallyEq.of_eq hinter),
      relativePerimeter_compl,
      relativePerimeter_ball_eq_perimeter c hr (Metric.closedBall_subset_ball hrρ)]
  have h2 : relativePerimeter μ U₂ (Metric.closedBall c R \ Metric.ball c r) =
      perimeter μ (Metric.closedBall c R) := by
    have hinter : (Metric.closedBall c R \ Metric.ball c r) ∩ (U₂ : Set E) =
        Metric.closedBall c R ∩ (U₂ : Set E) := by
      ext x; simp only [mem_inter_iff, Set.mem_sdiff, U₂]
      exact ⟨fun ⟨⟨h1, _⟩, h3⟩ ↦ ⟨h1, h3⟩, fun ⟨h1, h3⟩ ↦
        ⟨⟨h1, fun hxr ↦ h3 (Metric.ball_subset_closedBall (Metric.ball_subset_ball hrρ.le hxr))⟩,
          h3⟩⟩
    rw [relativePerimeter_eq_of_inter_ae_eq (Filter.EventuallyEq.of_eq hinter),
      relativePerimeter_closedBall_compl_closedBall_eq_perimeter c (hr.trans hrρ) hρR]
  rw [add_comm, ← h1, ← h2]
  exact relativePerimeter_add_le_perimeter_of_disjoint hdisj _

/-- Exact Caccioppoli perimeter of the concentric spherical shell
$\overline{B}(c, R) \setminus B(c, r)$ in terms of the unit ball measure. -/
theorem perimeter_closedBall_diff_ball_eq_unitBall [Nontrivial E] (c : E) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    perimeter μ (Metric.closedBall c R \ Metric.ball c r) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) *
        (R ^ (Module.finrank ℝ E - 1) + r ^ (Module.finrank ℝ E - 1))) *
        μ (Metric.ball (0 : E) 1) := by
  have hR : 0 < R := hr.trans hrR
  rw [perimeter_closedBall_diff_ball c hr hrR, perimeter_closedBall_eq_unitBall c hR,
    perimeter_ball_eq_unitBall c hr, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity), mul_add]

/-- Exact Caccioppoli perimeter of the half-open concentric annulus $B(c, R) \setminus B(c, r)$. -/
theorem perimeter_ball_diff_ball (c : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    perimeter μ (Metric.ball c R \ Metric.ball c r) =
      perimeter μ (Metric.closedBall c R) + perimeter μ (Metric.ball c r) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [perimeter_eq_zero_of_subsingleton]
  · have hsub : (Metric.closedBall c R \ Metric.ball c r) \ Metric.sphere c R =
        Metric.ball c R \ Metric.ball c r := by
      ext x
      simp only [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨lt_of_le_of_ne h1 h3, h2⟩,
        fun ⟨h1, h2⟩ ↦ ⟨⟨h1.le, h2⟩, h1.ne⟩⟩
    rw [← hsub, perimeter_diff_null _ (Measure.addHaar_sphere μ c R),
      perimeter_closedBall_diff_ball c hr hrR]

/-- Exact Caccioppoli perimeter of the open concentric annulus
$B(c, R) \setminus \overline{B}(c, r)$ for $0 < r < R$. -/
theorem perimeter_ball_diff_closedBall (c : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    perimeter μ (Metric.ball c R \ Metric.closedBall c r) =
      perimeter μ (Metric.closedBall c R) + perimeter μ (Metric.ball c r) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [perimeter_eq_zero_of_subsingleton]
  · have hsub : (Metric.ball c R \ Metric.ball c r) \ Metric.sphere c r =
        Metric.ball c R \ Metric.closedBall c r := by
      rw [← Metric.ball_union_sphere, Set.sdiff_sdiff]
    rw [← hsub, perimeter_diff_null _ (Measure.addHaar_sphere μ c r),
      perimeter_ball_diff_ball c hr hrR]

end AnnulusPerimeter

/-! ### Section 4: Exact ball isoperimetric identity -/

section BallIsoperimetricIdentity

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]

/-- Exact dimensional isoperimetric identity for an open ball $B(c, r)$ with $r > 0$. -/
theorem perimeter_ball_pow_finrank (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter μ (Metric.ball c r) ^ Module.finrank ℝ E =
      (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * μ (Metric.ball (0 : E) 1) *
        μ (Metric.ball c r) ^ (Module.finrank ℝ E - 1) := by
  set n := Module.finrank ℝ E
  have hn : 1 ≤ n := Module.finrank_pos
  rw [perimeter_ball_eq_unitBall c hr, Measure.addHaar_ball μ c hr.le,
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow hr.le, ENNReal.ofReal_pow hr.le,
    mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (n - 1) n]
  have hpow : μ (Metric.ball (0 : E) 1) ^ n =
      μ (Metric.ball (0 : E) 1) * μ (Metric.ball (0 : E) 1) ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']
  rw [hpow]; ring

/-- Exact dimensional isoperimetric identity for a closed ball $\overline{B}(c, r)$ ($r > 0$). -/
theorem perimeter_closedBall_pow_finrank (c : E) {r : ℝ} (hr : 0 < r) :
    perimeter μ (Metric.closedBall c r) ^ Module.finrank ℝ E =
      (Module.finrank ℝ E : ℝ≥0∞) ^ Module.finrank ℝ E * μ (Metric.ball (0 : E) 1) *
        μ (Metric.closedBall c r) ^ (Module.finrank ℝ E - 1) := by
  rw [perimeter_closedBall_eq_ball, Measure.addHaar_closedBall μ c hr.le,
    ← Measure.addHaar_ball μ c hr.le, perimeter_ball_pow_finrank c hr]

end BallIsoperimetricIdentity

end TauCeti
