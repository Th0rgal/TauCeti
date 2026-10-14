/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues
public import TauCeti.Analysis.Matrix.GramFactorization
public import TauCeti.Analysis.Matrix.GramFactorization.Uniqueness
public import TauCeti.Analysis.Matrix.Spectrum

/-!
# Uniqueness of Exact-Rank Factorizations and Dimension-Indexed Gram and Spectral Bounds

This file proves the uniqueness up to change of basis of exact-rank matrix factorizations over an
arbitrary field and collects the `Fin`-indexed characterizations of positive-semidefinite Gram
factorizations, unitary equivalence of Gram factors, and entrywise-to-operator/eigenvalue bounds:

1. **Exact-rank factorization geometry and change-of-basis uniqueness**:
   For a matrix `M : Matrix m n 𝕜` over a field `𝕜` with `M.rank = r` factored as `M = L * R`
   through `Fin r`, the right factor `R.mulVecLin` is surjective, the left factor `L.mulVecLin` is
   injective with range equal to `LinearMap.range M.mulVecLin`, and any two exact-rank
   factorizations `M = L * R = L' * R'` through `Fin r` are related by an invertible matrix
   `g : (Matrix (Fin r) (Fin r) 𝕜)ˣ` satisfying `L' = L * g` and `R' = g⁻¹ * R`
   (`Matrix.exists_units_eq_mul_of_rank_factorization`).
2. **Dimension-indexed (`Fin d` / `Fin n`) Gram factorization and unitary uniqueness**:
   `Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self` and
   `Matrix.exists_unitary_mul_of_conjTranspose_mul_self_eq`, together with unitary invariance of
   `Aᴴ * A` under left multiplication by `U ∈ Matrix.unitaryGroup (Fin d) 𝕜`.
3. **Euclidean operator-norm and `Fin n` sorted-eigenvalue bounds from entrywise bounds**:
   `Matrix.opNorm_toEuclideanCLM_le_of_entry_le`,
   `Matrix.norm_toEuclideanLin_le_of_entry_le_fin`,
   `Matrix.IsHermitian.abs_eigenvalues₀_sub_le_of_entry_le_fin`, and
   `Matrix.IsHermitian.abs_eigenvalues₀_le_of_entry_le_fin`.
-/

public section

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ENNReal Matrix ComplexOrder

namespace Matrix

section ExactRankUniqueness

variable {𝕜 : Type*} [Field 𝕜] {m n : Type*} [Fintype n]

/-- Two matrices with finitely many columns are equal if and only if their induced linear maps
`mulVecLin` are equal. -/
theorem ext_of_mulVecLin_eq {k : Type*} [Fintype k] {A B : Matrix m k 𝕜}
    (h : A.mulVecLin = B.mulVecLin) : A = B := by
  classical
  ext i j
  have hj := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
  simpa [mulVec_single_one] using hj
/-- Two matrices with finitely many columns have equal `mulVecLin` if and only if they are equal. -/
theorem mulVecLin_eq_iff {k : Type*} [Fintype k] {A B : Matrix m k 𝕜} :
    A.mulVecLin = B.mulVecLin ↔ A = B :=
  ⟨ext_of_mulVecLin_eq, fun h ↦ h ▸ rfl⟩
/-- In an exact-rank factorization `M = L * R` through `Fin r` with `M.rank = r`, the right factor
`R.mulVecLin` has full range `⊤`. -/
theorem range_mulVecLin_right_eq_top {r : ℕ} {M : Matrix m n 𝕜} (hr : M.rank = r)
    {L : Matrix m (Fin r) 𝕜} {R : Matrix (Fin r) n 𝕜} (h : M = L * R) :
    LinearMap.range R.mulVecLin = ⊤ := by
  have hle₁ : M.rank ≤ R.rank := h ▸ rank_mul_le_right L R
  have hle₂ : R.rank ≤ Module.finrank 𝕜 (Fin r → 𝕜) :=
    Submodule.finrank_le (LinearMap.range R.mulVecLin)
  have hcard : Module.finrank 𝕜 (Fin r → 𝕜) = r := Module.finrank_fin_fun 𝕜
  have hfin : Module.finrank 𝕜 (LinearMap.range R.mulVecLin) = Module.finrank 𝕜 (Fin r → 𝕜) := by
    change R.rank = _
    omega
  exact Submodule.eq_top_of_finrank_eq hfin
/-- In an exact-rank factorization `M = L * R` through `Fin r` with `M.rank = r`, the right factor
`R.mulVecLin` is surjective. -/
theorem surjective_mulVecLin_right_of_rank_eq {r : ℕ} {M : Matrix m n 𝕜} (hr : M.rank = r)
    {L : Matrix m (Fin r) 𝕜} {R : Matrix (Fin r) n 𝕜} (h : M = L * R) :
    Function.Surjective R.mulVecLin :=
  LinearMap.range_eq_top.mp (range_mulVecLin_right_eq_top hr h)
/-- In an exact-rank factorization `M = L * R` through `Fin r` with `M.rank = r`, the column space
of `L` equals the column space of `M`. -/
theorem range_mulVecLin_left_eq_of_rank_eq {r : ℕ} {M : Matrix m n 𝕜} (hr : M.rank = r)
    {L : Matrix m (Fin r) 𝕜} {R : Matrix (Fin r) n 𝕜} (h : M = L * R) :
    LinearMap.range L.mulVecLin = LinearMap.range M.mulVecLin := by
  rw [h, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ (range_mulVecLin_right_eq_top hr h)]
/-- In an exact-rank factorization `M = L * R` through `Fin r` with `M.rank = r`, the left factor
`L` has rank `r`. -/
theorem rank_left_eq_of_rank_eq {r : ℕ} {M : Matrix m n 𝕜} (hr : M.rank = r)
    {L : Matrix m (Fin r) 𝕜} {R : Matrix (Fin r) n 𝕜} (h : M = L * R) :
    L.rank = r := by
  rw [Matrix.rank, range_mulVecLin_left_eq_of_rank_eq hr h, ← Matrix.rank, hr]
/-- In an exact-rank factorization `M = L * R` through `Fin r` with `M.rank = r`, the right factor
`R` has rank `r`. -/
theorem rank_right_eq_of_rank_eq {r : ℕ} {M : Matrix m n 𝕜} (hr : M.rank = r)
    {L : Matrix m (Fin r) 𝕜} {R : Matrix (Fin r) n 𝕜} (h : M = L * R) :
    R.rank = r := by
  rw [Matrix.rank, range_mulVecLin_right_eq_top hr h, finrank_top, Module.finrank_fin_fun]
/-- In an exact-rank factorization `M = L * R` through `Fin r` with `M.rank = r`, the left factor
`L.mulVecLin` is injective. -/
theorem injective_mulVecLin_left_of_rank_eq {r : ℕ} {M : Matrix m n 𝕜} (hr : M.rank = r)
    {L : Matrix m (Fin r) 𝕜} {R : Matrix (Fin r) n 𝕜} (h : M = L * R) :
    Function.Injective L.mulVecLin := by
  have hnull := LinearMap.finrank_range_add_finrank_ker L.mulVecLin
  have hrange : Module.finrank 𝕜 (LinearMap.range L.mulVecLin) = r :=
    rank_left_eq_of_rank_eq hr h
  rw [Module.finrank_fin_fun 𝕜, hrange] at hnull
  have hker0 : Module.finrank 𝕜 (LinearMap.ker L.mulVecLin) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0)
/-- In an exact-rank factorization `M = L * R` through `Fin r` with `M.rank = r`, the kernel of
`R.mulVecLin` equals the kernel of `M.mulVecLin`. -/
theorem ker_mulVecLin_right_eq_of_rank_eq {r : ℕ} {M : Matrix m n 𝕜} (hr : M.rank = r)
    {L : Matrix m (Fin r) 𝕜} {R : Matrix (Fin r) n 𝕜} (h : M = L * R) :
    LinearMap.ker R.mulVecLin = LinearMap.ker M.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, h, mulVecLin_mul, LinearMap.comp_apply]
  exact ⟨fun hx ↦ by rw [hx, map_zero],
    fun hx ↦ injective_mulVecLin_left_of_rank_eq hr h (by rw [hx, map_zero])⟩
/-- **Exact-rank factorization uniqueness**: two factorizations `M = L * R = L' * R'` through the
exact rank `Fin r` (`M.rank = r`) differ by an invertible change of basis
`g : (Matrix (Fin r) (Fin r) 𝕜)ˣ` satisfying `L' = L * g` and `R' = g⁻¹ * R`. -/
theorem exists_units_eq_mul_of_rank_factorization {r : ℕ} (M : Matrix m n 𝕜)
    (hr : M.rank = r) {L L' : Matrix m (Fin r) 𝕜} {R R' : Matrix (Fin r) n 𝕜}
    (h : M = L * R) (h' : M = L' * R') :
    ∃ g : (Matrix (Fin r) (Fin r) 𝕜)ˣ,
      L' = L * (g : Matrix (Fin r) (Fin r) 𝕜) ∧
        R' = ((g⁻¹ : (Matrix (Fin r) (Fin r) 𝕜)ˣ) : Matrix (Fin r) (Fin r) 𝕜) * R := by
  have hL_inj := injective_mulVecLin_left_of_rank_eq hr h
  have hL'_inj := injective_mulVecLin_left_of_rank_eq hr h'
  have hrange : LinearMap.range L'.mulVecLin = LinearMap.range L.mulVecLin :=
    (range_mulVecLin_left_eq_of_rank_eq hr h').trans (range_mulVecLin_left_eq_of_rank_eq hr h).symm
  let eL : (Fin r → 𝕜) ≃ₗ[𝕜] LinearMap.range L.mulVecLin :=
    LinearEquiv.ofInjective L.mulVecLin hL_inj
  let eL' : (Fin r → 𝕜) ≃ₗ[𝕜] LinearMap.range L.mulVecLin :=
    (LinearEquiv.ofInjective L'.mulVecLin hL'_inj).trans (LinearEquiv.ofEq _ _ hrange)
  let e : (Fin r → 𝕜) ≃ₗ[𝕜] (Fin r → 𝕜) := eL'.trans eL.symm
  have heL (v : Fin r → 𝕜) : L.mulVecLin (e v) = L'.mulVecLin v := by
    change (eL (eL.symm (eL' v))).1 = L'.mulVecLin v
    rw [eL.apply_symm_apply]
    rfl
  have heR (x : n → 𝕜) : R'.mulVecLin x = e.symm (R.mulVecLin x) := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply hL_inj
    rw [heL]
    have hM : (L' * R').mulVecLin x = (L * R).mulVecLin x := by rw [← h', ← h]
    simpa [mulVecLin_mul] using hM
  let g : (Matrix (Fin r) (Fin r) 𝕜)ˣ :=
    { val := LinearMap.toMatrix' e.toLinearMap
      inv := LinearMap.toMatrix' e.symm.toLinearMap
      val_inv := by
        rw [← LinearMap.toMatrix'_mul]
        have hcomp : e.toLinearMap * e.symm.toLinearMap = 1 := by ext v; simp
        rw [hcomp, LinearMap.toMatrix'_one]
      inv_val := by
        rw [← LinearMap.toMatrix'_mul]
        have hcomp : e.symm.toLinearMap * e.toLinearMap = 1 := by ext v; simp
        rw [hcomp, LinearMap.toMatrix'_one] }
  refine ⟨g, ?_, ?_⟩
  · refine ext_of_mulVecLin_eq (LinearMap.ext fun v ↦ ?_)
    rw [mulVecLin_mul, LinearMap.comp_apply]
    change L'.mulVecLin v = L.mulVecLin (toLin' (LinearMap.toMatrix' e.toLinearMap) v)
    rw [toLin'_toMatrix']
    exact (heL v).symm
  · refine ext_of_mulVecLin_eq (LinearMap.ext fun x ↦ ?_)
    rw [mulVecLin_mul, LinearMap.comp_apply]
    change R'.mulVecLin x = toLin' (LinearMap.toMatrix' e.symm.toLinearMap) (R.mulVecLin x)
    rw [toLin'_toMatrix']
    exact heR x

end ExactRankUniqueness

section GramAndSpectralFin

variable {𝕜 : Type*} [RCLike 𝕜] {n d : ℕ}

/-- **Gram-factorization characterization (`Fin d` × `Fin n`)**: a square matrix
`B : Matrix (Fin n) (Fin n) 𝕜` is positive semidefinite of rank at most `d` if and only if
`B = Aᴴ * A` for some `A : Matrix (Fin d) (Fin n) 𝕜`. -/
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  simpa [Fintype.card_fin] using
    (posSemidef_and_rank_le_iff_eq_conjTranspose_mul_self (m := Fin d) (B := B))
/-- **Gram-factorization uniqueness (`Fin d` × `Fin n`)**: if `Aᴴ * A = A'ᴴ * A'` for two matrices
`A A' : Matrix (Fin d) (Fin n) 𝕜`, then `A' = U * A` for some `U ∈ Matrix.unitaryGroup (Fin d) 𝕜`.
-/
theorem exists_unitary_mul_of_conjTranspose_mul_self_eq
    {A A' : Matrix (Fin d) (Fin n) 𝕜} (h : Aᴴ * A = A'ᴴ * A') :
    ∃ U ∈ Matrix.unitaryGroup (Fin d) 𝕜, A' = U * A := by
  obtain ⟨U, hU⟩ := TauCeti.conjTranspose_mul_self_eq_iff_exists_unitary_mul.mp h
  exact ⟨U.1, U.2, hU⟩
/-- Left multiplication by a unitary matrix preserves the column Gram matrix `Aᴴ * A`. -/
theorem conjTranspose_mul_self_unitary_mul {m n : Type*} [Fintype m] [DecidableEq m]
    {U : Matrix m m 𝕜} (hU : U ∈ Matrix.unitaryGroup m 𝕜) (A : Matrix m n 𝕜) :
    (U * A)ᴴ * (U * A) = Aᴴ * A :=
  (TauCeti.conjTranspose_mul_self_eq_iff_exists_unitary_mul.mpr ⟨⟨U, hU⟩, rfl⟩).symm
/-- **Entrywise-to-Euclidean operator bound on `Fin n`**: if `‖A i j‖ ≤ ε` for all `i, j : Fin n`,
then `‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖` for every `x : EuclideanSpace 𝕜 (Fin n)`. -/
theorem norm_toEuclideanLin_le_of_entry_le_fin {A : Matrix (Fin n) (Fin n) 𝕜}
    {ε : ℝ} (hentry : ∀ i j, ‖A i j‖ ≤ ε) (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖ := by
  simpa [Fintype.card_fin] using norm_toEuclideanLin_le_of_entry_le_square hentry x
/-- **Continuous linear operator-norm bound from entrywise bound**: if `0 ≤ ε` and `‖A i j‖ ≤ ε`
for all `i, j`, then `‖Matrix.toEuclideanCLM A‖ ≤ (Fintype.card ι : ℝ) * ε`. -/
theorem opNorm_toEuclideanCLM_le_of_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι 𝕜} {ε : ℝ} (hε : 0 ≤ ε) (hentry : ∀ i j, ‖A i j‖ ≤ ε) :
    ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) A‖ ≤ (Fintype.card ι : ℝ) * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have hx : Matrix.toEuclideanCLM (𝕜 := 𝕜) A x = Matrix.toEuclideanLin A x :=
    congrFun (congrArg DFunLike.coe (coe_toEuclideanCLM_eq_toEuclideanLin (𝕜 := 𝕜) A)) x
  rw [hx]
  exact norm_toEuclideanLin_le_of_entry_le_square hentry x
/-- **Entrywise sorted-eigenvalue perturbation bound on `Fin n`**: if `A` and `Ahat` are Hermitian
`n × n` matrices with `‖Ahat i j - A i j‖ ≤ ε` entrywise, then
`|hAhat.eigenvalues₀ k - hA.eigenvalues₀ k| ≤ (n : ℝ) * ε` for all `k`. -/
theorem IsHermitian.abs_eigenvalues₀_sub_le_of_entry_le_fin {A Ahat : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {ε : ℝ} (hentry : ∀ i j, ‖Ahat i j - A i j‖ ≤ ε) (k : Fin (Fintype.card (Fin n))) :
    |hAhat.eigenvalues₀ k - hA.eigenvalues₀ k| ≤ (n : ℝ) * ε := by
  simpa [Fintype.card_fin] using hAhat.abs_eigenvalues₀_sub_le_of_entry_le hA hentry k
/-- **A-priori sorted-eigenvalue bound on `Fin n`**: if a Hermitian `n × n` matrix `A` satisfies
`‖A i j‖ ≤ β` entrywise, then `|hA.eigenvalues₀ k| ≤ (n : ℝ) * β` for all `k`. -/
theorem IsHermitian.abs_eigenvalues₀_le_of_entry_le_fin {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) {β : ℝ} (hentry : ∀ i j, ‖A i j‖ ≤ β)
    (k : Fin (Fintype.card (Fin n))) :
    |hA.eigenvalues₀ k| ≤ (n : ℝ) * β := by
  simpa [Fintype.card_fin] using hA.abs_eigenvalues₀_le_of_entry_le hentry k

end GramAndSpectralFin

end Matrix
