/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Measurable
public import TauCeti.Analysis.Matrix.Eigenvalues
public import TauCeti.Analysis.Matrix.MeasurableSpace

/-!
# Measurability of the Matrix Functional Calculus and Fixed-Threshold Spectral Projectors

This file establishes continuity and Borel measurability of the continuous functional calculus for
Hermitian matrices over `𝕜` (`RCLike 𝕜`), defines the fixed-threshold spectral projector
`Matrix.spectralProjectionIci c A = cfc (Set.indicator (Set.Ici c) 1) A` onto the sum of
eigenspaces with eigenvalue in `[c, ∞)`, and proves its algebraic, Borel-measurability, and
spectral-gap rank-stability properties:

1. **Continuity and Borel measurability of the Hermitian matrix functional calculus**:
   `Matrix.isClosed_isHermitian`, `Matrix.measurableSet_isHermitian`,
   `Matrix.continuous_cfc_on_hermitian_fintype`, `Matrix.continuous_cfc_on_hermitian`,
   `Matrix.measurable_cfc_matrix`, and `Matrix.measurable_cfc_of_hermitian`.
2. **Fixed-threshold spectral projector `Matrix.spectralProjectionIci`**:
   Hermitianness (`Matrix.isHermitian_spectralProjectionIci`), idempotence
   (`Matrix.spectralProjectionIci_mul_self`), positive semidefiniteness
   (`Matrix.posSemidef_spectralProjectionIci`), and Borel measurability on the full matrix space
   and along measurable Hermitian random matrices (`Matrix.measurable_spectralProjectionIci`,
   `Matrix.measurable_spectralProjectionIci_of_hermitian`), proved by approximating the indicator of
   `[c, ∞)` with a sequence of continuous piecewise-linear ramps that is eventually constant on the
   finite spectrum of each matrix.
3. **Rank of spectral functions and threshold rank stability**:
   `Matrix.IsHermitian.rank_cfc_eq_card_eigenvalues₀`,
   `Matrix.IsHermitian.rank_spectralProjectionIci_eq_natCard`,
   `Matrix.IsHermitian.card_eigenvalues_ge_eq_of_norm_sub_lt`, and
   `Matrix.IsHermitian.rank_spectralProjectionIci_eq_of_norm_sub_lt`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Unitary
open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}

/-! ### Section 1: Continuity and measurability of the Hermitian matrix functional calculus -/

/-- The set of Hermitian `ι × ι` matrices over `𝕜` is closed in the entrywise topology. -/
theorem isClosed_isHermitian : IsClosed {A : Matrix ι ι 𝕜 | A.IsHermitian} :=
  isClosed_eq (by fun_prop) (by fun_prop)
/-- The set of Hermitian `ι × ι` matrices over `𝕜` is Borel measurable. -/
theorem measurableSet_isHermitian [MeasurableSpace (Matrix ι ι 𝕜)] [BorelSpace (Matrix ι ι 𝕜)] :
    MeasurableSet {A : Matrix ι ι 𝕜 | A.IsHermitian} :=
  isClosed_isHermitian.measurableSet

variable [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.L2Operator in
@[instance_reducible]
private def instL2OpNormedAlgebraReal : NormedAlgebra ℝ (Matrix ι ι 𝕜) where
  norm_smul_le r A := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), norm_smul, RCLike.norm_ofReal, Real.norm_eq_abs]

scoped[Matrix.Norms.L2Operator] attribute [instance] instL2OpNormedAlgebraReal

/-- **Continuity of the Hermitian matrix functional calculus**: for a continuous function
`h : ℝ → ℝ`, the map `A ↦ cfc h A.1` is continuous on the subtype of Hermitian `ι × ι` matrices. -/
theorem continuous_cfc_on_hermitian_fintype {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous fun A : {A : Matrix ι ι 𝕜 // A.IsHermitian} ↦ cfc h A.1 := by
  open scoped Matrix.Norms.L2Operator in
  exact Continuous.cfc_of_mem_nhdsSet h Filter.univ_mem
    (a := (Subtype.val : {A : Matrix ι ι 𝕜 // A.IsHermitian} → Matrix ι ι 𝕜))
    continuous_subtype_val (fun A ↦ A.2.isSelfAdjoint) hh.continuousOn
/-- **Continuity of the Hermitian functional calculus on `Fin n`**: for continuous `h : ℝ → ℝ`,
`A ↦ cfc h A.1` is continuous on `{A : Matrix (Fin n) (Fin n) 𝕜 // A.IsHermitian}`. -/
theorem continuous_cfc_on_hermitian {n : ℕ} [DecidableEq (Fin n)] {h : ℝ → ℝ}
    (hh : Continuous h) :
    Continuous fun A : {A : Matrix (Fin n) (Fin n) 𝕜 // A.IsHermitian} ↦ cfc h A.1 :=
  continuous_cfc_on_hermitian_fintype hh
/-- Applying `cfc h` for a continuous function `h : ℝ → ℝ` is Borel measurable on the entire matrix
space `Matrix ι ι 𝕜` (taking the value `0` outside Hermitian matrices). -/
@[fun_prop]
theorem measurable_cfc_matrix
    [MeasurableSpace (Matrix ι ι 𝕜)] [BorelSpace (Matrix ι ι 𝕜)]
    {h : ℝ → ℝ} (hh : Continuous h) :
    Measurable (cfc h : Matrix ι ι 𝕜 → Matrix ι ι 𝕜) := by
  open scoped Matrix.Norms.L2Operator in
  exact TauCeti.measurable_cfc hh.continuousOn Filter.univ_mem
    (by simpa only [isHermitian_iff_isSelfAdjoint] using
      measurableSet_isHermitian (𝕜 := 𝕜) (ι := ι))
/-- **Measurability of the Hermitian functional calculus**: if `f : Ω → Matrix (Fin n) (Fin n) 𝕜`
is a measurable Hermitian random matrix and `h : ℝ → ℝ` is continuous, then `ω ↦ cfc h (f ω)` is
measurable. -/
theorem measurable_cfc_of_hermitian {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    [DecidableEq (Fin n)] [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕜)]
    [BorelSpace (Matrix (Fin n) (Fin n) 𝕜)] {h : ℝ → ℝ} (hh : Continuous h)
    {f : Ω → Matrix (Fin n) (Fin n) 𝕜} (hf : Measurable f)
    (_hfherm : ∀ ω, (f ω).IsHermitian) :
    Measurable fun ω ↦ cfc h (f ω) :=
  (measurable_cfc_matrix hh).comp hf

/-! ### Section 2: Fixed-threshold spectral projector and its Borel measurability -/

/-- **Fixed-threshold spectral projector**: `spectralProjectionIci c A` is the spectral projection
`cfc (Set.indicator (Set.Ici c) 1) A` of a matrix `A` onto its eigenspaces with eigenvalue in
`[c, ∞)` (and `0` if `A` is not Hermitian). -/
@[expose]
noncomputable def spectralProjectionIci (c : ℝ) (A : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  cfc (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A
/-- On a Hermitian matrix `A`, `spectralProjectionIci c A` agrees with the spectral-theorem
functional calculus `hA.cfc (Set.indicator (Set.Ici c) 1)`. -/
theorem IsHermitian.spectralProjectionIci_eq {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (c : ℝ) :
    spectralProjectionIci c A = hA.cfc (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) :=
  hA.cfc_eq _
/-- Outside Hermitian matrices, `spectralProjectionIci c A` vanishes. -/
theorem spectralProjectionIci_of_not_isHermitian {A : Matrix ι ι 𝕜} (hA : ¬ A.IsHermitian)
    (c : ℝ) : spectralProjectionIci c A = 0 :=
  cfc_apply_of_not_predicate A (by simpa only [isHermitian_iff_isSelfAdjoint] using hA)
/-- The fixed-threshold spectral projector `spectralProjectionIci c A` is always Hermitian. -/
theorem isHermitian_spectralProjectionIci (c : ℝ) (A : Matrix ι ι 𝕜) :
    (spectralProjectionIci c A).IsHermitian :=
  isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A)
/-- The fixed-threshold spectral projector `spectralProjectionIci c A` is idempotent. -/
theorem spectralProjectionIci_mul_self (c : ℝ) (A : Matrix ι ι 𝕜) :
    spectralProjectionIci c A * spectralProjectionIci c A = spectralProjectionIci c A := by
  by_cases hA : A.IsHermitian
  · have hind :
        (fun x : ℝ ↦ Set.indicator (Set.Ici c) (1 : ℝ → ℝ) x *
          Set.indicator (Set.Ici c) (1 : ℝ → ℝ) x) =
          Set.indicator (Set.Ici c) (1 : ℝ → ℝ) := by
      ext x
      by_cases hx : c ≤ x <;> simp [hx]
    have hcont : ContinuousOn (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) (spectrum ℝ A) := by
      rw [continuousOn_iff_continuous_domRestrict]
      fun_prop
    rw [spectralProjectionIci, ← cfc_mul _ _ A hcont hcont, hind]
  · rw [spectralProjectionIci_of_not_isHermitian hA, mul_zero]
/-- The fixed-threshold spectral projector `spectralProjectionIci c A` is positive semidefinite. -/
theorem posSemidef_spectralProjectionIci (c : ℝ) (A : Matrix ι ι 𝕜) :
    (spectralProjectionIci c A).PosSemidef := by
  have h1 : (spectralProjectionIci c A)ᴴ * spectralProjectionIci c A =
      spectralProjectionIci c A := by
    rw [(isHermitian_spectralProjectionIci c A).eq, spectralProjectionIci_mul_self]
  rw [← h1]
  exact posSemidef_conjTranspose_mul_self _

/-- Continuous piecewise-linear ramp approximating `Set.indicator (Set.Ici c) 1`: equal to `1` on
`[c, ∞)` and equal to `0` on `(-∞, c - 1 / m]`. -/
private def thresholdRamp (c : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (1 + (m : ℝ) * (x - c)))

private theorem continuous_thresholdRamp (c : ℝ) (m : ℕ) :
    Continuous (thresholdRamp c m) := by
  unfold thresholdRamp
  fun_prop

private theorem eventually_thresholdRamp_eq_indicator (c x : ℝ) :
    ∀ᶠ m : ℕ in atTop, thresholdRamp c m x = Set.indicator (Set.Ici c) (1 : ℝ → ℝ) x := by
  by_cases hx : c ≤ x
  · refine Eventually.of_forall fun m ↦ ?_
    have hnonneg : 0 ≤ (m : ℝ) * (x - c) := mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr hx)
    have hmin : min 1 (1 + (m : ℝ) * (x - c)) = 1 := min_eq_left (by linarith)
    simp [thresholdRamp, hmin, hx]
  · have hcx : 0 < c - x := sub_pos.mpr (lt_of_not_ge hx)
    filter_upwards [eventually_ge_atTop (Nat.ceil (c - x)⁻¹)] with m hm
    have hm' : (c - x)⁻¹ ≤ (m : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hm)
    have hmul : 1 ≤ (m : ℝ) * (c - x) := by
      calc
        1 = (c - x)⁻¹ * (c - x) := (inv_mul_cancel₀ hcx.ne').symm
        _ ≤ (m : ℝ) * (c - x) := mul_le_mul_of_nonneg_right hm' hcx.le
    have hle0 : 1 + (m : ℝ) * (x - c) ≤ 0 := by linarith
    have hmin : min 1 (1 + (m : ℝ) * (x - c)) = 1 + (m : ℝ) * (x - c) :=
      min_eq_right (hle0.trans zero_le_one)
    have hmax : max 0 (1 + (m : ℝ) * (x - c)) = 0 := max_eq_left hle0
    simp [thresholdRamp, hmin, hmax, hx]

private theorem eventually_cfc_thresholdRamp_eq (c : ℝ) (A : Matrix ι ι 𝕜) :
    (fun m : ℕ ↦ cfc (thresholdRamp c m) A) =ᶠ[atTop] fun _ ↦ spectralProjectionIci c A := by
  by_cases hA : A.IsHermitian
  · have hall : ∀ᶠ m : ℕ in atTop, ∀ i : ι,
        thresholdRamp c m (hA.eigenvalues i) =
          Set.indicator (Set.Ici c) (1 : ℝ → ℝ) (hA.eigenvalues i) :=
      eventually_all.mpr fun i ↦ eventually_thresholdRamp_eq_indicator c (hA.eigenvalues i)
    filter_upwards [hall] with m hm
    rw [hA.cfc_eq, hA.spectralProjectionIci_eq]
    unfold IsHermitian.cfc
    congr 3
    ext i
    simp [hm i]
  · refine Eventually.of_forall fun m ↦ ?_
    dsimp only
    have hnot : ¬ IsSelfAdjoint A := by simpa only [isHermitian_iff_isSelfAdjoint] using hA
    rw [cfc_apply_of_not_predicate A hnot, spectralProjectionIci_of_not_isHermitian hA]

/-- **Borel measurability of the fixed-threshold spectral projector**: for every real threshold `c`,
`spectralProjectionIci c : Matrix ι ι 𝕜 → Matrix ι ι 𝕜` is Borel measurable. -/
@[fun_prop]
theorem measurable_spectralProjectionIci_fintype
    [MeasurableSpace (Matrix ι ι 𝕜)] [BorelSpace (Matrix ι ι 𝕜)] (c : ℝ) :
    Measurable (spectralProjectionIci (𝕜 := 𝕜) (ι := ι) c) := by
  open scoped Matrix.Norms.L2Operator in
  exact measurable_of_tendsto_metrizable
    (fun m ↦ measurable_cfc_matrix (continuous_thresholdRamp c m))
    (tendsto_pi_nhds.mpr fun A ↦
      tendsto_const_nhds.congr' (eventually_cfc_thresholdRamp_eq c A).symm)
/-- **Borel measurability of the fixed-threshold projector on `Fin n`**: for fixed `c : ℝ`,
`spectralProjectionIci c : Matrix (Fin n) (Fin n) 𝕜 → Matrix (Fin n) (Fin n) 𝕜` is measurable. -/
theorem measurable_spectralProjectionIci {n : ℕ} [DecidableEq (Fin n)]
    [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕜)] [BorelSpace (Matrix (Fin n) (Fin n) 𝕜)]
    (c : ℝ) :
    Measurable (spectralProjectionIci (𝕜 := 𝕜) (ι := Fin n) c) :=
  measurable_spectralProjectionIci_fintype c
/-- **Random-matrix threshold projector measurability**: if `f : Ω → Matrix (Fin n) (Fin n) 𝕜` is
measurable, then `ω ↦ spectralProjectionIci c (f ω)` is measurable for every fixed `c : ℝ`. -/
theorem measurable_spectralProjectionIci_of_hermitian {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    [DecidableEq (Fin n)] [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕜)]
    [BorelSpace (Matrix (Fin n) (Fin n) 𝕜)] (c : ℝ)
    {f : Ω → Matrix (Fin n) (Fin n) 𝕜} (hf : Measurable f)
    (_hfherm : ∀ ω, (f ω).IsHermitian) :
    Measurable fun ω ↦ spectralProjectionIci c (f ω) :=
  (measurable_spectralProjectionIci c).comp hf

/-! ### Section 3: Rank of spectral functions and threshold rank stability -/

/-- For a Hermitian matrix `A` and any function `f : ℝ → ℝ`, the rank of `cfc f A` equals the number
of eigenvalues `hA.eigenvalues i` at which `f` is nonzero. -/
theorem IsHermitian.rank_cfc_eq_card_eigenvalues {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) [DecidablePred fun i : ι ↦ f (hA.eigenvalues i) ≠ 0] :
    (cfc f A).rank = Fintype.card {i : ι // f (hA.eigenvalues i) ≠ 0} := by
  classical
  have hU : IsUnit (hA.eigenvectorUnitary : Matrix ι ι 𝕜).det :=
    (isUnit_iff_isUnit_det _).mp Unitary.isUnit_coe
  have hUstar : IsUnit ((star hA.eigenvectorUnitary : unitaryGroup ι 𝕜) : Matrix ι ι 𝕜).det :=
    (isUnit_iff_isUnit_det _).mp Unitary.isUnit_coe
  rw [hA.cfc_eq f, IsHermitian.cfc, conjStarAlgAut_apply, ← coe_star,
    rank_mul_eq_left_of_isUnit_det _ _ hUstar, rank_mul_eq_right_of_isUnit_det _ _ hU,
    rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i ↦ by simp)
/-- For a Hermitian matrix `A` and any function `f : ℝ → ℝ`, the rank of `cfc f A` equals the number
of sorted eigenvalues `hA.eigenvalues₀ i` at which `f` is nonzero. -/
theorem IsHermitian.rank_cfc_eq_card_eigenvalues₀ {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ)
    [DecidablePred fun i : Fin (Fintype.card ι) ↦ f (hA.eigenvalues₀ i) ≠ 0] :
    (cfc f A).rank = Fintype.card {i : Fin (Fintype.card ι) // f (hA.eigenvalues₀ i) ≠ 0} := by
  classical
  rw [hA.rank_cfc_eq_card_eigenvalues f]
  exact Fintype.card_congr
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm.subtypeEquiv
      fun _ ↦ by rw [← hA.eigenvalues_apply_equivOfCardEq, Equiv.apply_symm_apply])
/-- The rank of `spectralProjectionIci c A` for a Hermitian matrix `A` equals the number of sorted
eigenvalues in `[c, ∞)`, counted with multiplicity. -/
theorem IsHermitian.rank_spectralProjectionIci_eq_natCard {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (c : ℝ) :
    (spectralProjectionIci c A).rank =
      Nat.card {i : Fin (Fintype.card ι) // c ≤ hA.eigenvalues₀ i} := by
  classical
  rw [spectralProjectionIci, hA.rank_cfc_eq_card_eigenvalues₀, Nat.card_eq_fintype_card]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun i ↦ ?_)
  by_cases hi : c ≤ hA.eigenvalues₀ i <;> simp [hi]

section ThresholdStability

open scoped Matrix.Norms.L2Operator

/-- **Threshold eigenvalue-count stability on `Fin n`**: if every sorted eigenvalue of a Hermitian
matrix `A : Matrix (Fin n) (Fin n) 𝕜` lies at distance at least `δ` from `c` and `‖Ahat - A‖ < δ`
in the Euclidean operator norm, then `Ahat` and `A` have the same number of eigenvalues in `[c, ∞)`.
-/
theorem IsHermitian.card_eigenvalues_ge_eq_of_norm_sub_lt {n : ℕ} [DecidableEq (Fin n)]
    {A Ahat : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {c δ : ℝ} (_hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card (Fin n)), δ ≤ |hA.eigenvalues₀ i - c|)
    (hpert : ‖Ahat - A‖ < δ) :
    Nat.card {i : Fin (Fintype.card (Fin n)) // c ≤ hAhat.eigenvalues₀ i} =
      Nat.card {i : Fin (Fintype.card (Fin n)) // c ≤ hA.eigenvalues₀ i} :=
  hA.card_eigenvalues₀_ge_eq_of_norm_sub_lt hAhat hgap (by rwa [norm_sub_rev])
/-- **Threshold projector rank stability**: if every sorted eigenvalue of a Hermitian matrix `A`
lies at distance at least `δ` from `c` and `‖Ahat - A‖ < δ` in the Euclidean operator norm, then
`spectralProjectionIci c Ahat` and `spectralProjectionIci c A` have the same rank. -/
theorem IsHermitian.rank_spectralProjectionIci_eq_of_norm_sub_lt
    {A Ahat : Matrix ι ι 𝕜} (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {c δ : ℝ} (_hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card ι), δ ≤ |hA.eigenvalues₀ i - c|)
    (hpert : ‖Ahat - A‖ < δ) :
    (spectralProjectionIci c Ahat).rank = (spectralProjectionIci c A).rank := by
  rw [hAhat.rank_spectralProjectionIci_eq_natCard, hA.rank_spectralProjectionIci_eq_natCard]
  exact hA.card_eigenvalues₀_ge_eq_of_norm_sub_lt hAhat hgap (by rwa [norm_sub_rev])

end ThresholdStability

end Matrix
