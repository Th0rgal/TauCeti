/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Compact
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Basic

/-!
# The logarithmic unit quotient from idele classes

The logarithms of the archimedean absolute values of an everywhere-integral idele are
well defined modulo the logarithms of global units when one passes to its idele class.
This gives a continuous additive homomorphism from the trivial ray subgroup (with its
additive group structure) to `logSpace K / unitLattice K`.
Its restriction to norm-one classes is surjective. Consequently compactness of the norm-one
idele class group implies compactness of the logarithmic unit quotient, the cocompactness
part of Dirichlet's unit theorem, and hence full-lattice spanning over `ℝ`.

We use Mathlib's `NumberField.Units.dirichletUnitTheorem.logSpace` and
`NumberField.Units.unitLattice`, with the distinguished infinite place omitted.
On everywhere-integral norm-one ideles the omitted coordinate is minus the sum of the
others, so these coordinates describe the usual trace-zero hyperplane. Compactness of the
norm-one idele class group in this library was itself proved using Dirichlet's theorem;
this is an agreement result, rather than an independent proof of that theorem.

## Main definitions

* `TauCeti.GlobalNumberFields.ideleLog`: the archimedean logarithmic map on ideles.
* `TauCeti.GlobalNumberFields.unitLogQuotient`: the archimedean logarithmic map modulo global
  units on the trivial ray subgroup.

## Main results

* `TauCeti.GlobalNumberFields.raySubgroup_one_eq_ker_toClassGroup`: the trivial ray subgroup is
  the kernel of `NumberField.IdeleClassGroup.toClassGroup`.
* `TauCeti.GlobalNumberFields.ideleLog_eq_zero_iff_of_ideleNorm_eq_one`: on an everywhere-integral
  idele of norm one, `ideleLog` vanishes exactly when all infinite coordinates have normalized
  absolute value `1`.
* `TauCeti.GlobalNumberFields.unitLogQuotient_normOne_surjective`: `unitLogQuotient` is surjective
  on norm-one classes in the trivial ray subgroup.
* `TauCeti.GlobalNumberFields.compactSpace_logSpace_quotient_unitLattice`: the quotient of
  `logSpace K` by the unit lattice is compact.
* `TauCeti.GlobalNumberFields.span_eq_top_of_compactSpace_quotient` and
  `TauCeti.GlobalNumberFields.isZLattice_of_compactSpace_quotient`: a discrete cocompact
  `ℤ`-submodule of a finite-dimensional real normed space spans the space over `ℝ` and is a full
  `ℤ`-lattice, recovering `IsZLattice ℝ (unitLattice K)` from
  `compactSpace_logSpace_quotient_unitLattice`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1, Theorem 1.6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open Topology Submodule
open scoped NumberField NNReal

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The archimedean logarithms of an idele, omitting Mathlib's distinguished infinite place.
Each coordinate is the logarithm of the normalized local absolute value. -/
def ideleLog : Additive (IdeleGroup (𝓞 K) K) →+ logSpace K where
  toFun x w := Real.log (completionNormalizedAbsValue w.1 (w.1.ideleInfiniteCoord x.toMul))
  map_zero' := by ext w; simp
  map_add' x y := by
    ext w
    simp only [toMul_add, map_mul, Units.val_mul, Pi.add_apply]
    exact Real.log_mul
      ((map_ne_zero _).mpr (w.1.ideleInfiniteCoord x.toMul).ne_zero)
      ((map_ne_zero _).mpr (w.1.ideleInfiniteCoord y.toMul).ne_zero)

/-- The coordinate formula for the logarithmic idele map. -/
@[simp]
theorem ideleLog_apply (x : IdeleGroup (𝓞 K) K) (w : {w : InfinitePlace K // w ≠ w₀}) :
    ideleLog (Additive.ofMul x) w =
      Real.log (completionNormalizedAbsValue w.1 (w.1.ideleInfiniteCoord x)) := (rfl)

/-- The logarithmic idele map is continuous. -/
@[fun_prop]
theorem continuous_ideleLog : Continuous (ideleLog (K := K)) := by
  apply continuous_pi
  intro w
  apply Continuous.log
  · simp only [InfinitePlace.coe_ideleInfiniteCoord]
    exact (continuous_completionNormalizedAbsValue w.1).comp
      (((continuous_apply w.1).comp continuous_fst).comp Units.continuous_val)
  · intro x
    exact (map_ne_zero _).mpr (w.1.ideleInfiniteCoord x.toMul).ne_zero

/-- On principal ideles of global units, the logarithmic map is Mathlib's unit embedding. -/
@[simp]
theorem ideleLog_unitEmbedding (u : (𝓞 K)ˣ) :
    ideleLog (Additive.ofMul (IdeleGroup.unitEmbedding (𝓞 K) K
      (Units.map (algebraMap (𝓞 K) K) u))) = logEmbedding K (Additive.ofMul u) := by
  ext w
  rw [ideleLog_apply, InfinitePlace.ideleInfiniteCoord_unitEmbedding]
  simp only [Units.coe_map, MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe,
    completionNormalizedAbsValue_algebraMap, Real.log_pow, logEmbedding_component]

private abbrev integralIdeles := ideleCongruenceSubgroup (Modulus.one K)
private abbrev integralClasses := raySubgroup (Modulus.one K)

private def integralClassMap : C(integralIdeles (K := K), integralClasses (K := K)) :=
  ⟨fun x ↦ ⟨(x.1 : IdeleClassGroup (𝓞 K) K), mem_raySubgroup_iff.mpr ⟨x.1, x.2, rfl⟩⟩,
    (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _⟩

private theorem integralClassMap_isQuotientMap :
    IsQuotientMap (integralClassMap (K := K)) := by
  have ho : IsOpenMap (integralClassMap (K := K)) :=
    ((QuotientGroup.isOpenMap_coe).domRestrict
      (isOpen_ideleCongruenceSubgroup (Modulus.one K))).codRestrict _
  apply ho.isQuotientMap integralClassMap.continuous
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, rfl⟩ := mem_raySubgroup_iff.mp hc
  exact ⟨⟨x, hx⟩, rfl⟩

private def integralIdeleLog :
    C(integralIdeles (K := K), logSpace K ⧸ (unitLattice K).toAddSubgroup) :=
  ⟨fun x ↦ QuotientAddGroup.mk (ideleLog (Additive.ofMul x.1)),
    QuotientAddGroup.continuous_mk.comp (continuous_ideleLog.comp continuous_subtype_val)⟩

private theorem integralIdeleLog_factorsThrough :
    Function.FactorsThrough (integralIdeleLog (K := K)) integralClassMap := by
  intro x y hxy
  have h : ((x.1 : IdeleClassGroup (𝓞 K) K)) = (y.1 : IdeleClassGroup (𝓞 K) K) :=
    congrArg Subtype.val hxy
  obtain ⟨a, ha⟩ := QuotientGroup.eq.mp h
  have hai : IdeleGroup.unitEmbedding (𝓞 K) K a ∈ integralIdeles (K := K) :=
    ha ▸ (integralIdeles (K := K)).mul_mem ((integralIdeles (K := K)).inv_mem x.2) y.2
  obtain ⟨u, -, hu⟩ := unitEmbedding_mem_ideleCongruenceSubgroup_iff.mp hai
  have hlog : ideleLog (Additive.ofMul (x.1⁻¹ * y.1)) = logEmbedding K (Additive.ofMul u) := by
    rw [← ha, ← hu]
    simpa only [RingHom.toMonoidHom_eq_coe] using ideleLog_unitEmbedding u
  apply QuotientAddGroup.eq.mpr
  -- The quotient equality uses subtraction, while ideles use multiplication and inversion.
  rw [← map_neg, ← map_add, ← ofMul_inv, ← ofMul_mul, hlog]
  exact Submodule.mem_map.mpr ⟨Additive.ofMul u, Submodule.mem_top, rfl⟩

private def integralUnitLog :
    C(raySubgroup (Modulus.one K), logSpace K ⧸ (unitLattice K).toAddSubgroup) :=
  integralClassMap_isQuotientMap.lift integralIdeleLog integralIdeleLog_factorsThrough

private theorem integralUnitLog_mk (x : IdeleGroup (𝓞 K) K)
    (hx : x ∈ ideleCongruenceSubgroup (Modulus.one K)) :
    integralUnitLog ⟨(x : IdeleClassGroup (𝓞 K) K), mem_raySubgroup_iff.mpr ⟨x, hx, rfl⟩⟩ =
      QuotientAddGroup.mk (ideleLog (Additive.ofMul x)) := by
  exact ContinuousMap.congr_fun
    (integralClassMap_isQuotientMap.lift_comp integralIdeleLog
      integralIdeleLog_factorsThrough) ⟨x, hx⟩

/-- Archimedean logarithms modulo global units on the trivial ray subgroup, viewed additively.
This subgroup consists of the idele classes admitting an everywhere-integral representative. -/
def unitLogQuotient :
    Additive (raySubgroup (Modulus.one K)) →+ logSpace K ⧸ (unitLattice K).toAddSubgroup :=
  AddMonoidHom.mk' (fun c ↦ integralUnitLog c.toMul) fun c d ↦ by
    obtain ⟨x, hx⟩ := integralClassMap_isQuotientMap.surjective c.toMul
    obtain ⟨y, hy⟩ := integralClassMap_isQuotientMap.surjective d.toMul
    -- Unwrap the additive domain to use the continuous descent on multiplicative classes.
    change integralUnitLog (c.toMul * d.toMul) =
      integralUnitLog c.toMul + integralUnitLog d.toMul
    rw [← hx, ← hy]
    have hmul : integralClassMap x * integralClassMap y = integralClassMap (x * y) :=
      Subtype.ext (QuotientGroup.mk_mul _ x.1 y.1).symm
    rw [hmul]
    calc
      _ = QuotientAddGroup.mk (ideleLog (Additive.ofMul (x.1 * y.1))) :=
        integralUnitLog_mk _ (mul_mem x.2 y.2)
      _ = _ := by
        rw [ofMul_mul, map_add, QuotientAddGroup.mk_add]
        exact congrArg₂ (· + ·) (integralUnitLog_mk x.1 x.2).symm
          (integralUnitLog_mk y.1 y.2).symm

/-- The logarithmic quotient homomorphism is continuous. -/
@[fun_prop]
theorem continuous_unitLogQuotient : Continuous (unitLogQuotient (K := K)) :=
  integralUnitLog.continuous.comp continuous_toMul

/-- The logarithmic quotient homomorphism evaluated on an everywhere-integral representative. -/
@[simp]
theorem unitLogQuotient_mk (x : IdeleGroup (𝓞 K) K)
    (hx : x ∈ ideleCongruenceSubgroup (Modulus.one K)) :
    unitLogQuotient (Additive.ofMul
      ⟨(x : IdeleClassGroup (𝓞 K) K), mem_raySubgroup_iff.mpr ⟨x, hx, rfl⟩⟩) =
      QuotientAddGroup.mk (ideleLog (Additive.ofMul x)) :=
  integralUnitLog_mk x hx

/-- Every logarithmic vector is realized by an everywhere-integral idele of norm one. -/
theorem exists_ideleLog_eq_and_norm_eq_one (y : logSpace K) :
    ∃ x : IdeleGroup (𝓞 K) K, x ∈ ideleCongruenceSubgroup (Modulus.one K) ∧
      ideleNorm x = 1 ∧ ideleLog (Additive.ofMul x) = y := by
  classical
  let t : InfinitePlace K → ℝ := fun w ↦
    if h : w = w₀ then -∑ v, y v else y ⟨w, h⟩
  have ht : ∑ w, t w = 0 := by
    rw [Fintype.sum_eq_add_sum_subtype_ne t w₀]
    have hn (v : {w : InfinitePlace K // w ≠ w₀}) : t v.1 = y v := by
      simp [t, v.2]
    rw [show t w₀ = -∑ v, y v by simp [t]]
    simp_rw [hn]
    exact neg_add_cancel _
  have hu (w : InfinitePlace K) :
      ∃ u : w.Completionˣ, completionNormalizedAbsValue w u = Real.exp (t w) := by
    obtain ⟨a, ha⟩ := exists_completionNormalizedAbsValue_eq w (Real.exp_pos (t w)).le
    have ha0 : a ≠ 0 := by
      intro h
      exact (Real.exp_ne_zero (t w)) (by simpa [h] using ha.symm)
    exact ⟨Units.mk0 a ha0, ha⟩
  choose u hu using hu
  let x := ideleOfUnits (R := 𝓞 K) u (fun _ ↦ 1) (Filter.Eventually.of_forall fun _ ↦ one_mem _)
  refine ⟨x, mem_ideleCongruenceSubgroup_one_iff.mpr (fun v ↦ by simp [x]), ?_, ?_⟩
  · apply Units.ext
    apply NNReal.eq
    rw [Units.val_one, NNReal.coe_one, coe_ideleNorm]
    simp only [x, ideleInfiniteCoord_ideleOfUnits, hu, ideleFiniteCoord_ideleOfUnits,
      Units.val_one, norm_one, finprod_one, mul_one]
    rw [← Real.exp_sum, ht, Real.exp_zero]
  · ext w
    simp [x, hu, t, w.2]

/-- The logarithmic quotient map remains surjective on norm-one classes in the trivial
ray subgroup. -/
theorem unitLogQuotient_normOne_surjective
    (z : logSpace K ⧸ (unitLattice K).toAddSubgroup) :
    ∃ c : raySubgroup (Modulus.one K), c.1 ∈ IdeleClassGroup.normOne K ∧
      unitLogQuotient (Additive.ofMul c) = z := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨x, hx, hnorm, hlog⟩ := exists_ideleLog_eq_and_norm_eq_one y
  refine ⟨⟨(x : IdeleClassGroup (𝓞 K) K), mem_raySubgroup_iff.mpr ⟨x, hx, rfl⟩⟩,
    IdeleClassGroup.mk_mem_normOne_iff.mpr hnorm, ?_⟩
  exact (unitLogQuotient_mk x hx).trans (congrArg QuotientAddGroup.mk hlog)

/-- The quotient of `logSpace K` by the unit lattice is compact: the logarithmic unit
lattice is cocompact in Mathlib's coordinates omitting the distinguished infinite place. -/
instance compactSpace_logSpace_quotient_unitLattice :
    CompactSpace (logSpace K ⧸ (unitLattice K).toAddSubgroup) := by
  let S : Set (raySubgroup (Modulus.one K)) :=
    {c | c.1 ∈ IdeleClassGroup.normOne K}
  have hS : IsCompact S := by
    have hc : IsCompact ((raySubgroup (Modulus.one K) : Set (IdeleClassGroup (𝓞 K) K)) ∩
        IdeleClassGroup.normOne K) :=
      (IdeleClassGroup.isCompact_normOne K).inter_left
        (Subgroup.isClosed_of_isOpen _ (isOpen_raySubgroup (Modulus.one K)))
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    convert hc using 1
    ext c
    exact ⟨fun ⟨a, ha, hac⟩ ↦ hac ▸ ⟨a.2, ha⟩,
      fun ⟨hc₁, hc₂⟩ ↦ ⟨⟨c, hc₁⟩, hc₂, rfl⟩⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hs : Function.Surjective (fun c : S ↦ unitLogQuotient (Additive.ofMul c.1)) := by
    intro z
    obtain ⟨c, hc, hlog⟩ := unitLogQuotient_normOne_surjective z
    exact ⟨⟨c, hc⟩, hlog⟩
  exact hs.compactSpace
    (continuous_unitLogQuotient.comp (continuous_ofMul.comp continuous_subtype_val))

/-- An idele lies in the congruence subgroup of the trivial modulus exactly when its finite
component is an everywhere-integral unit. -/
theorem mem_ideleCongruenceSubgroup_one_iff_toFiniteIdele_mem_integralUnits
    {x : IdeleGroup (𝓞 K) K} :
    x ∈ ideleCongruenceSubgroup (Modulus.one K) ↔
      IdeleGroup.toFiniteIdele (𝓞 K) K x ∈ FiniteAdeleRing.integralUnits (𝓞 K) K := by
  rw [mem_ideleCongruenceSubgroup_one_iff, ← toFractionalIdeal_toFiniteIdele_eq_one_iff,
    ← MonoidHom.mem_ker, FiniteAdeleRing.ker_toFractionalIdeal]

variable (K) in
/-- **The ray subgroup of the trivial modulus is the kernel of the class-group homomorphism** on
the idele class group: an idele class has trivial ideal class exactly when it is represented by an
everywhere-integral idele. -/
theorem raySubgroup_one_eq_ker_toClassGroup :
    raySubgroup (Modulus.one K) = (NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker := by
  ext c
  constructor
  · intro hc
    obtain ⟨x, hx, rfl⟩ := mem_raySubgroup_iff.mp hc
    rw [QuotientGroup.mk'_apply, NumberField.IdeleClassGroup.mk_mem_ker_toClassGroup_iff]
    exact Subgroup.mem_sup_left
      (mem_ideleCongruenceSubgroup_one_iff_toFiniteIdele_mem_integralUnits.mp hx)
  · intro hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨f, hf, _, ⟨a, rfl⟩, hfa⟩ :=
      Subgroup.mem_sup.mp (NumberField.IdeleClassGroup.mk_mem_ker_toClassGroup_iff.mp hc)
    refine mem_raySubgroup_iff.mpr ⟨x * (IdeleGroup.unitEmbedding (𝓞 K) K a)⁻¹, ?_, ?_⟩
    · rw [mem_ideleCongruenceSubgroup_one_iff_toFiniteIdele_mem_integralUnits,
        map_mul, map_inv, IdeleGroup.toFiniteIdele_unitEmbedding, ← hfa, mul_inv_cancel_right]
      exact hf
    · rw [QuotientGroup.mk'_apply]
      exact QuotientGroup.mk_mul_of_mem x ⟨a⁻¹, map_inv _ a⟩

/-- On an everywhere-integral idele of norm one, the logarithmic map vanishes exactly when every
infinite coordinate has normalized absolute value `1`. -/
theorem ideleLog_eq_zero_iff_of_ideleNorm_eq_one {x : IdeleGroup (𝓞 K) K}
    (hx : x ∈ ideleCongruenceSubgroup (Modulus.one K)) (hnorm : ideleNorm x = 1) :
    ideleLog (Additive.ofMul x) = 0 ↔
      ∀ w : InfinitePlace K, completionNormalizedAbsValue w (w.ideleInfiniteCoord x) = 1 := by
  classical
  constructor
  · intro hlog w
    have hne (v : {v : InfinitePlace K // v ≠ w₀}) :
        completionNormalizedAbsValue v.1 (v.1.ideleInfiniteCoord x) = 1 := by
      have hv : Real.log (completionNormalizedAbsValue v.1 (v.1.ideleInfiniteCoord x)) = 0 :=
        (ideleLog_apply x v).symm.trans (congrFun hlog v)
      have hpos : 0 < completionNormalizedAbsValue v.1 (v.1.ideleInfiniteCoord x) :=
        lt_of_le_of_ne (by simp [completionNormalizedAbsValue_apply])
          (Ne.symm ((map_ne_zero _).mpr (v.1.ideleInfiniteCoord x).ne_zero))
      rw [← Real.exp_log hpos, hv, Real.exp_zero]
    by_cases hw : w = w₀
    · subst hw
      have hfin (v : HeightOneSpectrum (𝓞 K)) :
          ‖(v.ideleFiniteCoord x : v.adicCompletion K)‖ = 1 := by
        rw [FinitePlace.norm_def, mem_ideleCongruenceSubgroup_one_iff.mp hx v,
          map_one, NNReal.coe_one]
      have hprod : ∏ w, completionNormalizedAbsValue w (w.ideleInfiniteCoord x) = 1 := by
        have := coe_ideleNorm x
        rw [hnorm, Units.val_one, NNReal.coe_one, finprod_congr hfin, finprod_one, mul_one] at this
        exact this.symm
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ w₀,
        Finset.prod_eq_one (fun v _ ↦ hne v), mul_one] at hprod
      exact hprod
    · exact hne ⟨w, hw⟩
  · intro h
    ext w
    rw [ideleLog_apply, h w.1, Real.log_one, Pi.zero_apply]

/-- **A cocompact `ℤ`-submodule of a finite-dimensional real normed space spans the space over
`ℝ`.**  Any proper `ℝ`-subspace is the kernel of a nonzero continuous linear functional, which
would descend to a continuous surjection from the compact quotient onto `ℝ`. -/
theorem span_eq_top_of_compactSpace_quotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [CompactSpace (E ⧸ L.toAddSubgroup)] :
    Submodule.span ℝ (L : Set E) = ⊤ := by
  by_contra hne
  set W : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  have : Nontrivial (E ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hne
  let B := Module.Basis.ofVectorSpace ℝ (E ⧸ W)
  obtain ⟨i⟩ : Nonempty (Module.Basis.ofVectorSpaceIndex ℝ (E ⧸ W)) := B.index_nonempty
  let φ : E →ₗ[ℝ] ℝ := (B.coord i).comp W.mkQ
  have hker : L.toAddSubgroup ≤ φ.toAddMonoidHom.ker := by
    intro x hx
    change (B.coord i) (W.mkQ x) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.subset_span hx),
      map_zero]
  let ψ : E ⧸ L.toAddSubgroup →+ ℝ := QuotientAddGroup.lift L.toAddSubgroup φ.toAddMonoidHom hker
  have hcont : Continuous ψ :=
    (QuotientAddGroup.isQuotientMap_mk L.toAddSubgroup).continuous_iff.mpr
      φ.continuous_of_finiteDimensional
  have hsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective W (r • B i)
    refine ⟨QuotientAddGroup.mk x, ?_⟩
    change (B.coord i) (W.mkQ x) = r
    rw [hx, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  have : CompactSpace ℝ := hsurj.compactSpace hcont
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (Set.univ : Set ℝ)).bddAbove
  linarith [hM (Set.mem_univ (M + 1))]

/-- **A discrete cocompact `ℤ`-submodule of a finite-dimensional real normed space is a full
`ℤ`-lattice.**  Combined with `compactSpace_logSpace_quotient_unitLattice`, this recovers the
spanning part of Dirichlet's unit theorem (`IsZLattice ℝ (unitLattice K)`) from the compactness
of the norm-one idele class group. -/
theorem isZLattice_of_compactSpace_quotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [CompactSpace (E ⧸ L.toAddSubgroup)] :
    IsZLattice ℝ L :=
  ⟨span_eq_top_of_compactSpace_quotient L⟩

end TauCeti.GlobalNumberFields
