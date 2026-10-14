/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CenteredScatter
public import TauCeti.Analysis.Matrix.Eigenvalues
public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.Probability.Moments.Chebyshev
public import TauCeti.Probability.Moments.SampleMean

/-!
# Empirical Second Moments and Elementary Matrix and Eigenvalue Concentration

This file develops the uncentered empirical second-moment matrix of a finite sample of random
vectors in `EuclideanSpace ℝ (Fin d)` together with entrywise, operator-norm, and sorted-eigenvalue
concentration bounds obtained by combining Chebyshev's second-moment inequality with a union bound
over matrix entries, as well as the `Fin.append` rank-one update formulas for `TauCeti.finiteMean`
and `TauCeti.centeredScatter`:

1. **Add-one `Fin.append` updates for finite means and centered scatter**:
   `TauCeti.finiteMean_append_singleton`, `TauCeti.centeredScatter_append`,
   `TauCeti.re_inner_centeredScatter_append_apply_self`, and
   `TauCeti.centeredScatter_le_centeredScatter_append`.
2. **Empirical second-moment matrices and per-entry `1 / r` mean-square error**:
   `TauCeti.sampleSecondMoment` (`M̂ₖₗ(ω) = r⁻¹ ∑ᵢ Vᵢ(ω)ₖ Vᵢ(ω)ₗ`), symmetry and Hermitianness
   (`TauCeti.isSymm_sampleSecondMoment`, `TauCeti.isHermitian_sampleSecondMoment`), identification
   with `TauCeti.finiteMean` (`TauCeti.sampleSecondMoment_apply_eq_finiteMean`), and the per-entry
   second-moment bound `∫ ω, (sampleSecondMoment V ω k l - M k l) ^ 2 ∂P ≤ v / r` under pairwise
   independence (`TauCeti.integral_sampleSecondMoment_sub_sq_le`).
3. **Entrywise deviation events and `n²` union-bound concentration**:
   Measurability of the entrywise deviation event `{ω | ∃ k l, η < |Ŝ ω k l - A k l|}`
   (`TauCeti.measurableSet_exists_lt_abs_sub`) and the Chebyshev union bound
   `P {ω | ∃ k l, η < |Ŝ ω k l - A k l|} ≤ ENNReal.ofReal (n ^ 2 * v / η ^ 2)`
   (`TauCeti.measure_exists_lt_abs_sub_le`).
4. **High-probability eigenvalue, operator-norm, and empirical-second-moment bounds**:
   Simultaneous two-sided sorted-eigenvalue concentration
   (`TauCeti.measure_forall_abs_eigenvalues₀_sub_le_ge`), one-sided sorted-eigenvalue lower bounds
   (`TauCeti.measure_forall_eigenvalues₀_sub_le_ge`), Euclidean operator-norm concentration
   (`TauCeti.measure_forall_norm_toEuclideanLin_sub_le_ge`), and the empirical-second-moment
   eigenvalue floor at threshold `c / 2` with probability at least
   `1 - ENNReal.ofReal (4 * d ^ 4 * v / (r * c ^ 2))`
   (`TauCeti.measure_sampleSecondMoment_eigenvalues₀_ge_half`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Finset InnerProductSpace
open scoped ENNReal Matrix ComplexOrder InnerProductSpace

namespace TauCeti

/-! ### Section 1: `Fin.append` rank-one updates for `finiteMean` and `centeredScatter` -/

section CenteredScatterAppend

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Add-one mean identity (`Fin.append` form)**: appending a single vector `y` via
`Fin.append z (fun _ : Fin 1 ↦ y)` shifts the finite mean by `(m + 1)⁻¹ • (y - finiteMean 𝕜 z)`. -/
theorem finiteMean_append_singleton {m : ℕ} (z : Fin m → E) (y : E) :
    finiteMean 𝕜 (Fin.append z (fun _ : Fin 1 ↦ y)) =
      finiteMean 𝕜 z + ((m : 𝕜) + 1)⁻¹ • (y - finiteMean 𝕜 z) := by
  rw [Fin.append_right_eq_snoc]
  exact finiteMean_snoc z y
/-- **Add-one scatter identity (`Fin.append` form)**: appending a single vector `y` via
`Fin.append z (fun _ : Fin 1 ↦ y)` updates the centered scatter operator by the rank-one term
`(m / (m + 1)) • rankOne 𝕜 (y - finiteMean 𝕜 z) (y - finiteMean 𝕜 z)`. -/
theorem centeredScatter_append {m : ℕ} (z : Fin m → E) (y : E) :
    centeredScatter 𝕜 (Fin.append z (fun _ : Fin 1 ↦ y)) =
      centeredScatter 𝕜 z +
        ((m : 𝕜) / ((m : 𝕜) + 1)) •
          rankOne 𝕜 (y - finiteMean 𝕜 z) (y - finiteMean 𝕜 z) := by
  rw [Fin.append_right_eq_snoc]
  exact centeredScatter_snoc z y
/-- **Add-one scatter identity on `EuclideanSpace` (`Fin.append` form with real scalar weight)**:
appending a single vector `y` via `Fin.append z (fun _ : Fin 1 ↦ y)` updates the centered scatter
operator by `((m : ℝ) / (m + 1 : ℝ)) • rankOne 𝕜 (y - finiteMean 𝕜 z) (y - finiteMean 𝕜 z)`. -/
theorem centeredScatter_append_euclidean {m d : ℕ} (z : Fin m → EuclideanSpace 𝕜 (Fin d))
    (y : EuclideanSpace 𝕜 (Fin d)) :
    centeredScatter 𝕜 (Fin.append z (fun _ : Fin 1 ↦ y)) =
      centeredScatter 𝕜 z +
        ((m : ℝ) / (m + 1 : ℝ)) •
          rankOne 𝕜 (y - finiteMean 𝕜 z) (y - finiteMean 𝕜 z) := by
  rw [centeredScatter_append, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  simp only [RCLike.ofReal_div, RCLike.ofReal_add, RCLike.ofReal_natCast, RCLike.ofReal_one]
/-- **Add-one quadratic-form identity (`Fin.append` form)**: the quadratic form of
`centeredScatter 𝕜 (Fin.append z (fun _ : Fin 1 ↦ y))` increases by
`(m / (m + 1)) * ‖⟪y - finiteMean 𝕜 z, x⟫_𝕜‖ ^ 2`. -/
theorem re_inner_centeredScatter_append_apply_self {m : ℕ} (z : Fin m → E) (y x : E) :
    RCLike.re ⟪centeredScatter 𝕜 (Fin.append z (fun _ : Fin 1 ↦ y)) x, x⟫_𝕜 =
      RCLike.re ⟪centeredScatter 𝕜 z x, x⟫_𝕜 +
        (m : ℝ) / (m + 1 : ℝ) * ‖⟪y - finiteMean 𝕜 z, x⟫_𝕜‖ ^ 2 := by
  rw [Fin.append_right_eq_snoc]
  exact re_inner_centeredScatter_snoc_apply_self z y x
/-- **Monotonicity under appending (`Fin.append` form)**: appending a point increases
`centeredScatter` in the Loewner order. -/
theorem centeredScatter_le_centeredScatter_append {m : ℕ} (z : Fin m → E) (y : E) :
    centeredScatter 𝕜 z ≤ centeredScatter 𝕜 (Fin.append z (fun _ : Fin 1 ↦ y)) := by
  rw [Fin.append_right_eq_snoc]
  exact centeredScatter_le_centeredScatter_snoc z y

end CenteredScatterAppend

/-! ### Section 2: Empirical second-moment matrices and per-entry second-moment bounds -/

variable {Ω : Type*} {n r d : ℕ}

/-- The uncentered empirical second-moment matrix `M̂ₖₗ(ω) = r⁻¹ ∑ᵢ Vᵢ(ω)ₖ Vᵢ(ω)ₗ` of `r` random
vectors in `EuclideanSpace ℝ (Fin d)`. -/
@[expose]
def sampleSecondMoment (V : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun k l => (r : ℝ)⁻¹ * ∑ i : Fin r, V i ω k * V i ω l
/-- Entrywise evaluation of `sampleSecondMoment`. -/
@[simp]
theorem sampleSecondMoment_apply (V : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω)
    (k l : Fin d) :
    sampleSecondMoment V ω k l = (r : ℝ)⁻¹ * ∑ i : Fin r, V i ω k * V i ω l :=
  rfl
/-- Each entry `(k, l)` of `sampleSecondMoment V ω` is the `finiteMean` of the coordinate products
`i ↦ V i ω k * V i ω l`. -/
theorem sampleSecondMoment_apply_eq_finiteMean (V : Fin r → Ω → EuclideanSpace ℝ (Fin d))
    (ω : Ω) (k l : Fin d) :
    sampleSecondMoment V ω k l = finiteMean ℝ (fun i : Fin r ↦ V i ω k * V i ω l) := by
  rw [finiteMean_eq_inv_smul_sum, Fintype.card_fin, smul_eq_mul, sampleSecondMoment_apply]
/-- For `r = 0`, `sampleSecondMoment V ω = 0`. -/
@[simp]
theorem sampleSecondMoment_zero (V : Fin 0 → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    sampleSecondMoment V ω = 0 := by
  ext k l
  simp [sampleSecondMoment]
/-- The empirical second-moment matrix is symmetric (`M̂ᵀ = M̂`). -/
theorem isSymm_sampleSecondMoment (V : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    (sampleSecondMoment V ω).IsSymm := by
  ext k l
  simp only [transpose_apply, sampleSecondMoment_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm (V i ω l) (V i ω k)
/-- **Hermitian empirical second moment**: for every sample `ω`, `sampleSecondMoment V ω` is
Hermitian. -/
theorem isHermitian_sampleSecondMoment (V : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    (sampleSecondMoment V ω).IsHermitian := by
  ext k l
  simp only [conjTranspose_apply, star_trivial, sampleSecondMoment_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm (V i ω l) (V i ω k)

variable [MeasurableSpace Ω]

/-- If each coordinate `ω ↦ V i ω k` is measurable, then each entry `ω ↦ sampleSecondMoment V ω k l`
is measurable. -/
theorem measurable_sampleSecondMoment_apply {V : Fin r → Ω → EuclideanSpace ℝ (Fin d)}
    (hV : ∀ i k, Measurable fun ω ↦ V i ω k) (k l : Fin d) :
    Measurable fun ω ↦ sampleSecondMoment V ω k l := by
  refine Measurable.const_mul ?_ (r : ℝ)⁻¹
  exact Finset.measurable_sum univ fun i _ ↦ (hV i k).mul (hV i l)
/-- If each coordinate `ω ↦ V i ω k` is measurable, then `sampleSecondMoment V` is measurable. -/
theorem measurable_sampleSecondMoment {V : Fin r → Ω → EuclideanSpace ℝ (Fin d)}
    (hV : ∀ i k, Measurable fun ω ↦ V i ω k) :
    Measurable (sampleSecondMoment V) :=
  Matrix.measurable_iff.mpr (measurable_sampleSecondMoment_apply hV)
/-- **Exact per-entry second-moment identity for `sampleSecondMoment`**: for `0 < r` and pairwise
independent coordinate products `Y i ω = V i ω k * V i ω l` with common mean `M k l`,
`∫ ω, (sampleSecondMoment V ω k l - M k l) ^ 2 ∂P =
  ((r : ℝ) ^ 2)⁻¹ * ∑ i, ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂P`. -/
theorem integral_sampleSecondMoment_sub_sq (P : Measure Ω) [IsProbabilityMeasure P]
    (hr : 0 < r) (V : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ)
    (k l : Fin d)
    (hY : ∀ i : Fin r, MemLp (fun ω ↦ V i ω k * V i ω l) 2 P)
    (hmean : ∀ i : Fin r, ∫ ω, V i ω k * V i ω l ∂P = M k l)
    (hindep : Pairwise fun i j : Fin r ↦
      (fun ω ↦ V i ω k * V i ω l) ⟂ᵢ[P] (fun ω ↦ V j ω k * V j ω l)) :
    ∫ ω, (sampleSecondMoment V ω k l - M k l) ^ 2 ∂P =
      ((r : ℝ) ^ 2)⁻¹ * ∑ i : Fin r, ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂P := by
  have : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  simp_rw [sampleSecondMoment_apply_eq_finiteMean]
  simpa [Fintype.card_fin] using integral_finiteMean_sub_sq hY hmean hindep
/-- **Per-entry second-moment identity under equal centered second moments**: if every sample
coordinate product `V i ω k * V i ω l` has centered second moment equal to `γ`, then
`∫ ω, (sampleSecondMoment V ω k l - M k l) ^ 2 ∂P = γ / r`. -/
theorem integral_sampleSecondMoment_sub_sq_of_forall_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (hr : 0 < r) (V : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ)
    (k l : Fin d)
    (hY : ∀ i : Fin r, MemLp (fun ω ↦ V i ω k * V i ω l) 2 P)
    (hmean : ∀ i : Fin r, ∫ ω, V i ω k * V i ω l ∂P = M k l)
    (hindep : Pairwise fun i j : Fin r ↦
      (fun ω ↦ V i ω k * V i ω l) ⟂ᵢ[P] (fun ω ↦ V j ω k * V j ω l))
    {γ : ℝ} (hγ : ∀ i : Fin r, ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂P = γ) :
    ∫ ω, (sampleSecondMoment V ω k l - M k l) ^ 2 ∂P = γ / r := by
  have : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  simp_rw [sampleSecondMoment_apply_eq_finiteMean]
  have h := integral_norm_finiteMean_sub_sq_of_forall_eq hY hmean hindep
    (γ := γ) (fun i ↦ by simpa [Real.norm_eq_abs, sq_abs] using hγ i)
  simpa [Real.norm_eq_abs, sq_abs, Fintype.card_fin] using h
/-- **Per-entry second-moment bound for `sampleSecondMoment`**: for `0 < r`, if the coordinate
products `Y i ω = V i ω k * V i ω l` are square-integrable, pairwise independent with common mean
`M k l`, and have centered second moments `∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂P ≤ v` (in
particular when all centered second moments are equal and at most `v`), then
`∫ ω, (sampleSecondMoment V ω k l - M k l) ^ 2 ∂P ≤ v / r`. -/
theorem integral_sampleSecondMoment_sub_sq_le (P : Measure Ω) [IsProbabilityMeasure P]
    (hr : 0 < r) (V : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ)
    (k l : Fin d)
    (hY : ∀ i : Fin r, MemLp (fun ω ↦ V i ω k * V i ω l) 2 P)
    (hmean : ∀ i : Fin r, ∫ ω, V i ω k * V i ω l ∂P = M k l)
    (hindep : Pairwise fun i j : Fin r ↦
      (fun ω ↦ V i ω k * V i ω l) ⟂ᵢ[P] (fun ω ↦ V j ω k * V j ω l))
    {v : ℝ} (hv : ∀ i : Fin r, ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂P ≤ v) :
    ∫ ω, (sampleSecondMoment V ω k l - M k l) ^ 2 ∂P ≤ v / r := by
  have : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  simp_rw [sampleSecondMoment_apply_eq_finiteMean]
  have h := integral_norm_finiteMean_sub_sq_le_of_forall_le hY hmean hindep
    (γ := v) (fun i ↦ by simpa [Real.norm_eq_abs, sq_abs] using hv i)
  simpa [Real.norm_eq_abs, sq_abs, Fintype.card_fin] using h

/-! ### Section 3: Entrywise deviation events and union-bound concentration -/

section EntrywiseConcentration

variable {ι κ : Type*}

/-- If the `(k, l)` entry of `Shat` is measurable, then `{ω | η < |Shat ω k l - A k l|}` is
measurable. -/
theorem measurableSet_lt_abs_sub_entry {Shat : Ω → Matrix ι κ ℝ} {A : Matrix ι κ ℝ}
    {k : ι} {l : κ} (hmeas : Measurable fun ω ↦ Shat ω k l) (η : ℝ) :
    MeasurableSet {ω | η < |Shat ω k l - A k l|} :=
  measurableSet_lt measurable_const (continuous_abs.measurable.comp (hmeas.sub_const (A k l)))
/-- **Measurability of the entrywise deviation event**: if every entry of `Shat` is measurable, then
`{ω | ∃ k l, η < |Shat ω k l - A k l|}` is measurable. -/
theorem measurableSet_exists_lt_abs_sub [Countable ι] [Countable κ]
    {Shat : Ω → Matrix ι κ ℝ} (A : Matrix ι κ ℝ)
    (hmeas : ∀ k l, Measurable fun ω ↦ Shat ω k l) (η : ℝ) :
    MeasurableSet {ω | ∃ k l, η < |Shat ω k l - A k l|} := by
  have hset : {ω | ∃ k l, η < |Shat ω k l - A k l|} =
      ⋃ k : ι, ⋃ l : κ, {ω | η < |Shat ω k l - A k l|} := by
    ext ω; simp
  rw [hset]
  exact MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun l ↦
    measurableSet_lt_abs_sub_entry (hmeas k l) η
/-- If every entry of `Shat` is measurable, then the simultaneous entrywise closeness event
`{ω | ∀ k l, |Shat ω k l - A k l| ≤ η}` is measurable. -/
theorem measurableSet_forall_abs_sub_le [Countable ι] [Countable κ]
    {Shat : Ω → Matrix ι κ ℝ} (A : Matrix ι κ ℝ)
    (hmeas : ∀ k l, Measurable fun ω ↦ Shat ω k l) (η : ℝ) :
    MeasurableSet {ω | ∀ k l, |Shat ω k l - A k l| ≤ η} := by
  have hset : {ω | ∀ k l, |Shat ω k l - A k l| ≤ η} =
      ⋂ k : ι, ⋂ l : κ, {ω | |Shat ω k l - A k l| ≤ η} := by
    ext ω; simp
  rw [hset]
  exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun l ↦
    measurableSet_le (continuous_abs.measurable.comp ((hmeas k l).sub_const (A k l)))
      measurable_const
/-- Chebyshev bound for a single matrix entry: if `(Shat ω k l - A k l) ^ 2` is integrable with
integral at most `v` and `0 < η`, then
`P {ω | η < |Shat ω k l - A k l|} ≤ ENNReal.ofReal (v / η ^ 2)`. -/
theorem measure_lt_abs_sub_entry_le (P : Measure Ω) {Shat : Ω → Matrix ι κ ℝ}
    {A : Matrix ι κ ℝ} {k : ι} {l : κ}
    (hint : Integrable (fun ω ↦ (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | η < |Shat ω k l - A k l|} ≤ ENNReal.ofReal (v / η ^ 2) := by
  have hint_abs : Integrable (fun ω ↦ |Shat ω k l - A k l| ^ 2) P := by
    simpa only [sq_abs] using hint
  have hmom_abs : ∫ ω, |Shat ω k l - A k l| ^ 2 ∂P ≤ v := by
    simpa only [sq_abs] using hmoment
  exact meas_gt_le_div_sq_of_integral_sq_le hint_abs hmom_abs hη

variable [Fintype ι] [Fintype κ]

/-- **General finite-index entrywise concentration**: for a random `ι × κ` real matrix `Shat` whose
squared entrywise deviations from `A` are integrable with expectation at most `v`,
`P {ω | ∃ k l, η < |Shat ω k l - A k l|} ≤
  ENNReal.ofReal ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ) * v / η ^ 2)`. -/
theorem measure_exists_lt_abs_sub_le_card (P : Measure Ω)
    (Shat : Ω → Matrix ι κ ℝ) (A : Matrix ι κ ℝ)
    (_hmeas : ∀ k l, Measurable fun ω ↦ Shat ω k l)
    (hint : ∀ k l, Integrable (fun ω ↦ (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∃ k l, η < |Shat ω k l - A k l|} ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ) * v / η ^ 2) := by
  have hset : {ω | ∃ k l, η < |Shat ω k l - A k l|} =
      ⋃ k : ι, ⋃ l : κ, {ω | η < |Shat ω k l - A k l|} := by
    ext ω; simp
  rw [hset]
  calc
    P (⋃ k : ι, ⋃ l : κ, {ω | η < |Shat ω k l - A k l|})
        ≤ ∑ k : ι, P (⋃ l : κ, {ω | η < |Shat ω k l - A k l|}) :=
      measure_iUnion_fintype_le P _
    _ ≤ ∑ k : ι, ∑ l : κ, P {ω | η < |Shat ω k l - A k l|} :=
      Finset.sum_le_sum fun k _ ↦ measure_iUnion_fintype_le P _
    _ ≤ ∑ _k : ι, ∑ _l : κ, ENNReal.ofReal (v / η ^ 2) :=
      Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun l _ ↦
        measure_lt_abs_sub_entry_le P (hint k l) hη (hmoment k l)
    _ = (Fintype.card ι : ℝ≥0∞) * ((Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal (v / η ^ 2)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ) * (v / η ^ 2)) := by
      rw [← ENNReal.ofReal_natCast (Fintype.card ι), ← ENNReal.ofReal_natCast (Fintype.card κ),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ) * v / η ^ 2) := by
      rw [mul_div_assoc]
/-- **Entrywise matrix concentration on `Fin n × Fin n`**: if every entry of `Shat` is measurable
and every squared entrywise deviation `(Shat ω k l - A k l) ^ 2` is integrable with integral at most
`v`, then for `0 < η`,
`P {ω | ∃ k l, η < |Shat ω k l - A k l|} ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2)`. -/
theorem measure_exists_lt_abs_sub_le (P : Measure Ω)
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hmeas : ∀ k l, Measurable fun ω ↦ Shat ω k l)
    (hint : ∀ k l, Integrable (fun ω ↦ (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∃ k l, η < |Shat ω k l - A k l|} ≤
      ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  simpa [Fintype.card_fin, sq] using
    measure_exists_lt_abs_sub_le_card P Shat A hmeas hint hη hmoment
/-- **High-probability simultaneous entrywise bound**: on a probability space, under the hypotheses
of `measure_exists_lt_abs_sub_le`,
`P {ω | ∀ k l, |Shat ω k l - A k l| ≤ η} ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2)`. -/
theorem measure_forall_abs_sub_le_ge (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hmeas : ∀ k l, Measurable fun ω ↦ Shat ω k l)
    (hint : ∀ k l, Integrable (fun ω ↦ (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k l, |Shat ω k l - A k l| ≤ η} ≥
      1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  have hcompl : {ω | ∀ k l, |Shat ω k l - A k l| ≤ η}ᶜ =
      {ω | ∃ k l, η < |Shat ω k l - A k l|} := by
    ext ω; simp
  have h1 := P.one_sub_measure_compl_le {ω | ∀ k l, |Shat ω k l - A k l| ≤ η}
  rw [hcompl] at h1
  exact (tsub_le_tsub_left (measure_exists_lt_abs_sub_le P Shat A hmeas hint hη hmoment) 1).trans h1

end EntrywiseConcentration

/-! ### Section 4: Eigenvalue, operator-norm, and sample-second-moment concentration -/

/-- **Eigenvalue concentration**: under entrywise second-moment control with bound `v` and `0 < η`,
for symmetric/Hermitian matrices `Shat ω` and `A`, the probability that every sorted eigenvalue
differs by at most `n * η` is at least `1 - ENNReal.ofReal (n ^ 2 * v / η ^ 2)`. -/
theorem measure_forall_abs_eigenvalues₀_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hSherm : ∀ ω, (Shat ω).IsHermitian) (hAherm : A.IsHermitian)
    (hmeas : ∀ k l, Measurable fun ω => Shat ω k l)
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k, |(hSherm ω).eigenvalues₀ k - hAherm.eigenvalues₀ k|
        ≤ (n : ℝ) * η} ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  refine (measure_forall_abs_sub_le_ge P Shat A hmeas hint hη hmoment).trans (measure_mono ?_)
  intro ω hω k
  simpa [Fintype.card_fin] using
    (hSherm ω).abs_eigenvalues₀_sub_le_of_entry_le hAherm (fun i j ↦ by simpa using hω i j) k
/-- **One-sided eigenvalue floor**: under the hypotheses of
`measure_forall_abs_eigenvalues₀_sub_le_ge`, with probability at least
`1 - ENNReal.ofReal (n ^ 2 * v / η ^ 2)`, every sorted eigenvalue of `Shat ω` is at least the
corresponding sorted eigenvalue of `A` minus `n * η`. -/
theorem measure_forall_eigenvalues₀_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hSherm : ∀ ω, (Shat ω).IsHermitian) (hAherm : A.IsHermitian)
    (hmeas : ∀ k l, Measurable fun ω => Shat ω k l)
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k, hAherm.eigenvalues₀ k - (n : ℝ) * η ≤ (hSherm ω).eigenvalues₀ k}
      ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  refine (measure_forall_abs_eigenvalues₀_sub_le_ge P Shat A hSherm hAherm hmeas hint hη
    hmoment).trans (measure_mono ?_)
  intro ω hω k
  linarith [(abs_le.mp (hω k)).1]
/-- **Operator-norm concentration**: under entrywise second-moment control with bound `v` and
`0 < η`, with probability at least `1 - ENNReal.ofReal (n ^ 2 * v / η ^ 2)`,
`‖Matrix.toEuclideanLin (Shat ω - A) x‖ ≤ n * η * ‖x‖` for every `x : EuclideanSpace ℝ (Fin n)`. -/
theorem measure_forall_norm_toEuclideanLin_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hmeas : ∀ k l, Measurable fun ω => Shat ω k l)
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ x : EuclideanSpace ℝ (Fin n),
        ‖Matrix.toEuclideanLin (Shat ω - A) x‖ ≤ (n : ℝ) * η * ‖x‖}
      ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  refine (measure_forall_abs_sub_le_ge P Shat A hmeas hint hη hmoment).trans (measure_mono ?_)
  intro ω hω x
  simpa [Fintype.card_fin] using
    Matrix.norm_toEuclideanLin_le_of_entry_le_square (A := Shat ω - A)
      (fun i j ↦ by simpa using hω i j) x
/-- **Empirical-second-moment one-sided eigenvalue bound**: if `0 < r`, every coordinate pair
`(k, l)` satisfies the hypotheses of `integral_sampleSecondMoment_sub_sq_le` with bound `v`, every
entry of `sampleSecondMoment V` is measurable, and every squared entrywise deviation from the
Hermitian population second moment `M` is integrable, then for `0 < η`,
`P {ω | ∀ k, hM.eigenvalues₀ k - (d : ℝ) * η ≤ (isHermitian_sampleSecondMoment V ω).eigenvalues₀ k}
  ≥ 1 - ENNReal.ofReal ((d : ℝ) ^ 2 * (v / r) / η ^ 2)`. -/
theorem measure_sampleSecondMoment_eigenvalues₀_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hr : 0 < r) (V : Fin r → Ω → EuclideanSpace ℝ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hY : ∀ k l (i : Fin r), MemLp (fun ω ↦ V i ω k * V i ω l) 2 P)
    (hmean : ∀ k l (i : Fin r), ∫ ω, V i ω k * V i ω l ∂P = M k l)
    (hindep : ∀ k l, Pairwise fun i j : Fin r ↦
      (fun ω ↦ V i ω k * V i ω l) ⟂ᵢ[P] (fun ω ↦ V j ω k * V j ω l))
    {v : ℝ} (hv : ∀ k l (i : Fin r), ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂P ≤ v)
    (hmeas : ∀ k l, Measurable fun ω ↦ sampleSecondMoment V ω k l)
    (hint : ∀ k l, Integrable (fun ω ↦ (sampleSecondMoment V ω k l - M k l) ^ 2) P)
    {η : ℝ} (hη : 0 < η) :
    P {ω | ∀ k,
        hM.eigenvalues₀ k - (d : ℝ) * η ≤
          (isHermitian_sampleSecondMoment V ω).eigenvalues₀ k}
      ≥ 1 - ENNReal.ofReal ((d : ℝ) ^ 2 * (v / r) / η ^ 2) :=
  measure_forall_eigenvalues₀_sub_le_ge P (sampleSecondMoment V) M
    (isHermitian_sampleSecondMoment V) hM hmeas hint hη
    (fun k l ↦ integral_sampleSecondMoment_sub_sq_le P hr V M k l (hY k l) (hmean k l)
      (hindep k l) (hv k l))
/-- **Empirical-second-moment eigenvalue floor at `c / 2`**: under the hypotheses of
`measure_sampleSecondMoment_eigenvalues₀_sub_le_ge` with `0 < d` and `0 < c`, taking
`η = c / (2 * d)` shows that with probability at least
`1 - ENNReal.ofReal (4 * (d : ℝ) ^ 4 * v / ((r : ℝ) * c ^ 2))`, every empirical eigenvalue whose
population eigenvalue is at least `c` is at least `c / 2`. -/
theorem measure_sampleSecondMoment_eigenvalues₀_ge_half
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hr : 0 < r) (hd : 0 < d) (V : Fin r → Ω → EuclideanSpace ℝ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hY : ∀ k l (i : Fin r), MemLp (fun ω ↦ V i ω k * V i ω l) 2 P)
    (hmean : ∀ k l (i : Fin r), ∫ ω, V i ω k * V i ω l ∂P = M k l)
    (hindep : ∀ k l, Pairwise fun i j : Fin r ↦
      (fun ω ↦ V i ω k * V i ω l) ⟂ᵢ[P] (fun ω ↦ V j ω k * V j ω l))
    {v c : ℝ} (hc : 0 < c)
    (hv : ∀ k l (i : Fin r), ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂P ≤ v)
    (hmeas : ∀ k l, Measurable fun ω ↦ sampleSecondMoment V ω k l)
    (hint : ∀ k l, Integrable (fun ω ↦ (sampleSecondMoment V ω k l - M k l) ^ 2) P) :
    P {ω | ∀ k, c ≤ hM.eigenvalues₀ k →
        c / 2 ≤ (isHermitian_sampleSecondMoment V ω).eigenvalues₀ k}
      ≥ 1 - ENNReal.ofReal (4 * (d : ℝ) ^ 4 * v / ((r : ℝ) * c ^ 2)) := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hc_ne : c ≠ 0 := hc.ne'
  set η : ℝ := c / (2 * (d : ℝ))
  have hη : 0 < η := div_pos hc (mul_pos zero_lt_two hd_pos)
  have hrate : (d : ℝ) ^ 2 * (v / r) / η ^ 2 = 4 * (d : ℝ) ^ 4 * v / ((r : ℝ) * c ^ 2) := by
    dsimp [η]
    field_simp
    ring
  have hfloor := measure_sampleSecondMoment_eigenvalues₀_sub_le_ge P hr V M hM hY hmean hindep hv
    hmeas hint hη
  rw [hrate] at hfloor
  refine hfloor.trans (measure_mono ?_)
  intro ω hω k hck
  have hdη : (d : ℝ) * η = c / 2 := by
    dsimp [η]; field_simp
  have hle := hω k
  linarith

end TauCeti
