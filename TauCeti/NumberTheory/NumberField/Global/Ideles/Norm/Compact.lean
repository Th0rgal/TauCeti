/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One
public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology

import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Compactness of the norm-one idele class group and its agreement corollaries

For a number field `K`, the norm-one idele class group `C_K¹ = 𝕀_K¹ / Kˣ` is compact.  This is the
adelic form of the two finiteness theorems of algebraic number theory: the finiteness of the ideal
class group and Dirichlet's unit theorem.

Conversely, the compactness of `C_K¹` recovers the finiteness of the ideal class group via the
locally constant class-group projection `NumberField.IdeleClassGroup.toClassGroup`, whose
restriction to `C_K¹` is surjective with compact open kernel.  On the other hand, the full idele
class group `C_K` and the full idele group `𝕀_K` are not compact: the idele class norm identifies
the quotient `C_K / C_K¹` with the non-compact group `ℝ>0`.

## Main definitions

* `NumberField.IdeleClassGroup.toClassGroup`: the homomorphism from the idele class group to the
  ideal class group attached to the finite component.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.quotientNormOneEquiv`: the multiplicative equivalence
  `C_K / C_K¹ ≃* ℝ≥0ˣ` induced by the idele class norm.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.normOneQuotientEquivClassGroup`: the multiplicative
  equivalence between the quotient of `C_K¹` by the kernel of `toClassGroup` and `ClassGroup (𝓞 K)`.

## Main results

* `TauCeti.GlobalNumberFields.IdeleClassGroup.isCompact_normOne`: the norm-one idele class group
  is a compact subset of the idele class group.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.compactSpace_normOne`: the norm-one idele class
  group is a compact space.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.not_compactSpace`: the full idele class group is not
  compact.
* `NumberField.IdeleGroup.not_compactSpace`: the full idele group is not compact.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.finite_classGroup_of_compactSpace_normOne`:
  finiteness of the ideal class group recovered from the compactness of `C_K¹`.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.classNumber_eq_relIndex_ker_toClassGroup_normOne`:
  the class number of `K` is the index in `C_K¹` of the kernel of `toClassGroup`.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.compactSpace_ker_toClassGroup_subgroupOf_normOne`:
  the kernel of `toClassGroup` on `C_K¹` is compact.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1, Theorem 1.6.
* A. Weil, *Basic Number Theory*, Chapter IV, §4.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped NNReal

namespace NumberField.IdeleGroup

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Projection from the idele group to the finite idele group is continuous. -/
@[continuity, fun_prop]
theorem continuous_toFiniteIdele : Continuous (toFiniteIdele R K) := by
  have h : toFiniteIdele R K =
      Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K)) :=
    MonoidHom.ext fun x ↦ Units.ext (coe_toFiniteIdele R K x)
  rw [h]
  exact continuous_snd.units_map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K))

end NumberField.IdeleGroup

namespace NumberField.IdeleClassGroup

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The ideal class attached to an idele class: the class of the fractional ideal of the finite
component of any representative idele. -/
noncomputable def toClassGroup : IdeleClassGroup R K →* ClassGroup R :=
  QuotientGroup.lift _
    ((FiniteAdeleRing.toClassGroup R K).comp (IdeleGroup.toFiniteIdele R K)) <| by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, IdeleGroup.toFiniteIdele_unitEmbedding,
      FiniteAdeleRing.toClassGroup_apply, FiniteAdeleRing.toFractionalIdeal_unitEmbedding,
      ClassGroup.mk_toPrincipalIdeal]

variable {R K} in
/-- The ideal class of the class of an idele is the ideal class of its finite component. -/
@[simp]
theorem toClassGroup_mk (x : IdeleGroup R K) :
    toClassGroup R K (x : IdeleClassGroup R K) =
      FiniteAdeleRing.toClassGroup R K (IdeleGroup.toFiniteIdele R K x) :=
  (rfl)

/-- Every ideal class is the class of an idele class. -/
theorem toClassGroup_surjective : Function.Surjective (toClassGroup R K) := by
  intro c
  obtain ⟨f, rfl⟩ := FiniteAdeleRing.toClassGroup_surjective (R := R) (K := K) c
  exact ⟨(IdeleGroup.ofFiniteIdele R K f : IdeleClassGroup R K), by simp⟩

variable {R K} in
/-- The class of an idele has trivial ideal class exactly when its finite component is an
everywhere-integral unit times a principal finite idele. -/
@[simp]
theorem mk_mem_ker_toClassGroup_iff {x : IdeleGroup R K} :
    (x : IdeleClassGroup R K) ∈ (toClassGroup R K).ker ↔
      IdeleGroup.toFiniteIdele R K x ∈
        FiniteAdeleRing.integralUnits R K ⊔ (FiniteAdeleRing.unitEmbedding R K).range := by
  rw [MonoidHom.mem_ker, toClassGroup_mk, ← FiniteAdeleRing.ker_toClassGroup, MonoidHom.mem_ker]

/-- The ideal class attached to an idele class is locally constant. -/
theorem isLocallyConstant_toClassGroup : IsLocallyConstant (toClassGroup R K) := by
  let : TopologicalSpace (ClassGroup R) := ⊥
  let : DiscreteTopology (ClassGroup R) := ⟨rfl⟩
  rw [IsLocallyConstant.iff_continuous]
  exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (((TauCeti.isLocallyConstant_toClassGroup R K).continuous).comp
      (IdeleGroup.continuous_toFiniteIdele R K))

/-- The kernel of the class-group homomorphism on the idele class group is open. -/
theorem isOpen_ker_toClassGroup :
    IsOpen ((toClassGroup R K).ker : Set (IdeleClassGroup R K)) :=
  (isLocallyConstant_toClassGroup R K) {(1 : ClassGroup R)}

/-- The kernel of the class-group homomorphism on the idele class group is closed. -/
theorem isClosed_ker_toClassGroup :
    IsClosed ((toClassGroup R K).ker : Set (IdeleClassGroup R K)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_ker_toClassGroup R K)

/-- With the discrete topology on the ideal class group, its canonical map from the idele class
group is an open quotient map. -/
theorem isOpenQuotientMap_toClassGroup
    [TopologicalSpace (ClassGroup R)] [DiscreteTopology (ClassGroup R)] :
    IsOpenQuotientMap (toClassGroup R K) :=
  ⟨toClassGroup_surjective R K, (isLocallyConstant_toClassGroup R K).continuous,
    fun _ _ ↦ isOpen_discrete _⟩

end NumberField.IdeleClassGroup

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- Multiplying an idele by a principal unit acts on its infinite component by the corresponding
unit action on the mixed space. -/
private lemma ringEquiv_mixedSpace_mul_unitEmbedding (z : IdeleGroup (𝓞 K) K)
    (u : (𝓞 K)ˣ) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K
      ((z * IdeleGroup.unitEmbedding (𝓞 K) K
        (Units.map (algebraMap (𝓞 K) K) u) : AdeleRing (𝓞 K) K).1) =
      u • InfiniteAdeleRing.ringEquiv_mixedSpace K (z : AdeleRing (𝓞 K) K).1 := by
  rw [unitSMul_smul, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← map_mul,
    IdeleGroup.val_unitEmbedding_apply, AdeleRing.fst_mul, mul_comm]
  refine congrArg _ (congrArg (· * _) (funext fun w ↦ ?_))
  rw [AdeleRing.algebraMap_fst_apply, InfiniteAdeleRing.algebraMap_apply, Units.coe_map,
    MonoidHom.coe_ofClass]

/-- There is a compact set of ideles meeting the orbit under the global units of every idele of
norm one whose finite part is an everywhere-integral unit. -/
private lemma exists_isCompact_forall_exists_mul_unitEmbedding_mem :
    ∃ W : Set (IdeleGroup (𝓞 K) K), IsCompact W ∧
      ∀ z : IdeleGroup (𝓞 K) K, ideleNorm z = 1 →
        IdeleGroup.toFiniteIdele (𝓞 K) K z ∈ FiniteAdeleRing.integralUnits (𝓞 K) K →
        ∃ u : (𝓞 K)ˣ,
          z * IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u) ∈ W := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  -- The infinite parts: the norm-one points of the closure of `normLeOne`, and their inverses.
  let F : Set (mixedSpace K) :=
    closure (fundamentalCone.normLeOne K) ∩ {x | mixedEmbedding.norm x = 1}
  have hF : IsCompact F := (fundamentalCone.isBounded_normLeOne K).isCompact_closure.inter_right
    (isClosed_eq (mixedEmbedding.continuous_norm K) continuous_const)
  have hFunit (x : mixedSpace K) (hx : x ∈ F) : IsUnit x :=
    TauCeti.NumberField.mixedEmbedding.isUnit_iff_norm_ne_zero.mpr (hx.2 ▸ one_ne_zero)
  let G : Set (mixedSpace K) := Ring.inverse '' F
  have hG : IsCompact G := hF.image_of_continuousOn fun x hx ↦
    (NormedRing.inverse_continuousAt (hFunit x hx).unit).continuousWithinAt
  -- The finite parts: the integral finite adeles.
  let O : Set (FiniteAdeleRing (𝓞 K) K) := FiniteAdeleRing.integralAdeles (𝓞 K) K
  have hO : IsCompact O := FiniteAdeleRing.isCompact_integralAdeles
  let C : Set (AdeleRing (𝓞 K) K) := (e.symm '' F) ×ˢ O
  let D : Set (AdeleRing (𝓞 K) K) := (e.symm '' G) ×ˢ O
  have hC : IsCompact C :=
    (hF.image (InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K)).prod hO
  have hD : IsCompact D :=
    (hG.image (InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K)).prod hO
  -- An idele lies in `W` when it lies in `C` and its inverse lies in `D`; this is compact since
  -- the idele group is embedded as a closed subset of `𝔸_K × 𝔸_Kᵐᵒᵖ` by `x ↦ (x, x⁻¹)`.
  refine ⟨{z | (z : AdeleRing (𝓞 K) K) ∈ C ∧ ((z⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) ∈ D},
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hD)), ?_⟩
  intro z hz hzf
  have hnorm : mixedEmbedding.norm (e (z : AdeleRing (𝓞 K) K).1) = 1 := by
    rw [mixedEmbedding_norm_eq_ideleNorm (K := K) hzf, hz, Units.val_one, NNReal.coe_one]
  -- Dirichlet's unit theorem moves the infinite part into the fundamental cone.
  obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem (hnorm ▸ one_ne_zero)
  refine ⟨u, ?_⟩
  set z' := z * IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)
  have he : e (z' : AdeleRing (𝓞 K) K).1 = u • e (z : AdeleRing (𝓞 K) K).1 := by
    simpa only [z', e, Units.val_mul] using ringEquiv_mixedSpace_mul_unitEmbedding K z u
  have hF' : e (z' : AdeleRing (𝓞 K) K).1 ∈ F := by
    rw [he]
    exact ⟨subset_closure ⟨hu, by simp [hnorm]⟩, by simp [hnorm]⟩
  have hf' : IdeleGroup.toFiniteIdele (𝓞 K) K z' ∈ FiniteAdeleRing.integralUnits (𝓞 K) K := by
    rw [map_mul, IdeleGroup.toFiniteIdele_unitEmbedding]
    exact mul_mem hzf (FiniteAdeleRing.unitEmbedding_map_algebraMap_mem_integralUnits u)
  have hint := FiniteAdeleRing.mem_integralUnits_iff_forall_mem_adicCompletionIntegers.mp hf'
  refine ⟨⟨⟨e (z' : AdeleRing (𝓞 K) K).1, hF', e.symm_apply_apply _⟩,
      FiniteAdeleRing.mem_integralAdeles.mpr fun v ↦ ?_⟩,
    ⟨⟨Ring.inverse (e (z' : AdeleRing (𝓞 K) K).1), ⟨_, hF', rfl⟩, ?_⟩,
      FiniteAdeleRing.mem_integralAdeles.mpr fun v ↦ ?_⟩⟩
  · simpa using (hint v).1
  · -- The infinite part of `z'⁻¹` is the inverse of the infinite part of `z'`: the unit of the
    -- mixed space below has, by `Units.coe_map`, value `e (z' : 𝔸_K).1` and inverse
    -- `e (z'⁻¹ : 𝔸_K).1`.
    rw [e.symm_apply_eq]
    exact Ring.inverse_unit (Units.map ((e : InfiniteAdeleRing K →* mixedSpace K).comp
      (MonoidHom.fst _ (FiniteAdeleRing (𝓞 K) K))) z')
  · simpa [← map_inv] using (hint v).2

/-- The multiplicative group of positive real numbers `ℝ≥0ˣ` is not compact. -/
theorem not_compactSpace_units_nnreal : ¬ CompactSpace ℝ≥0ˣ := by
  intro _
  obtain ⟨B, hB⟩ := (isCompact_range (Units.continuous_val (M := ℝ≥0))).bddAbove
  have h0 : B + 1 ≠ 0 := by simp
  exact (lt_add_one B).not_ge (hB ⟨Units.mk0 (B + 1) h0, rfl⟩)

namespace IdeleClassGroup

/-- **The norm-one idele class group is compact.**  This is the adelic form of the finiteness of
the class group together with Dirichlet's unit theorem. -/
theorem isCompact_normOne : IsCompact (normOne K : Set (IdeleClassGroup (𝓞 K) K)) := by
  classical
  obtain ⟨W, hW, hWmem⟩ := exists_isCompact_forall_exists_mul_unitEmbedding_mem K
  choose b hb1 hbc using ClassGroup.exists_ideleNorm_eq_one_and_toClassGroup_eq (K := K)
  have hq : Continuous (QuotientGroup.mk : IdeleGroup (𝓞 K) K → IdeleClassGroup (𝓞 K) K) :=
    continuous_quot_mk
  -- `C_K¹` is a closed subset of the union over the finitely many ideal classes `c` of the
  -- images of the compact sets `b_c • W`.
  refine (isCompact_iUnion fun c ↦ hW.image (hq.comp (continuous_const.mul continuous_id)
    (f := fun z ↦ b c * z))).of_isClosed_subset (isClosed_normOne K) ?_
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have ha : ideleNorm a = 1 := mk_mem_normOne_iff.mp hx
  set c := FiniteAdeleRing.toClassGroup (𝓞 K) K (IdeleGroup.toFiniteIdele (𝓞 K) K a)
  -- The finite part of `a / b_c` has trivial class, so it is an everywhere-integral unit times a
  -- principal finite idele.
  have hker : IdeleGroup.toFiniteIdele (𝓞 K) K (a * (b c)⁻¹) ∈
      FiniteAdeleRing.integralUnits (𝓞 K) K ⊔ (FiniteAdeleRing.unitEmbedding (𝓞 K) K).range := by
    rw [← FiniteAdeleRing.ker_toClassGroup, MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv,
      hbc, mul_inv_cancel]
  obtain ⟨f, hf, _, ⟨y, rfl⟩, hfy⟩ := Subgroup.mem_sup.mp hker
  set z := a * (b c)⁻¹ * (IdeleGroup.unitEmbedding (𝓞 K) K y)⁻¹
  have hz1 : ideleNorm z = 1 := by simp [z, ha, hb1]
  have hzf : IdeleGroup.toFiniteIdele (𝓞 K) K z ∈ FiniteAdeleRing.integralUnits (𝓞 K) K := by
    rw [map_mul, map_inv, IdeleGroup.toFiniteIdele_unitEmbedding, ← hfy, mul_inv_cancel_right]
    exact hf
  obtain ⟨u, hu⟩ := hWmem z hz1 hzf
  refine Set.mem_iUnion.mpr ⟨c, _, hu, ?_⟩
  -- `b_c * z * u` differs from `a` by the principal idele of `y * u⁻¹`.
  rw [Function.comp_apply, QuotientGroup.eq]
  have h : (b c * (z * IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)))⁻¹ *
      a = IdeleGroup.unitEmbedding (𝓞 K) K (y * (Units.map (algebraMap (𝓞 K) K) u)⁻¹) := by
    simp only [z, map_mul, map_inv]
    simp [mul_comm, mul_left_comm]
  rw [h]
  exact ⟨_, rfl⟩

/-- **The norm-one idele class group is a compact space.** -/
instance compactSpace_normOne : CompactSpace (normOne K) :=
  isCompact_iff_compactSpace.mp (isCompact_normOne K)

/-- The norm-one idele class group is the kernel of `ideleClassNorm`. -/
theorem normOne_eq_ker_ideleClassNorm :
    normOne K = (ideleClassNorm (K := K)).ker := by
  ext x
  exact mem_normOne_iff

/-- The norm-one subgroup of the idele class group is normal. -/
instance normal_normOne : (normOne K).Normal :=
  normOne_eq_ker_ideleClassNorm K ▸ MonoidHom.normal_ker (ideleClassNorm (K := K))

/-- **The norm quotient of the idele class group is `ℝ>0`**: the idele class norm identifies
`C_K / C_K¹` with the multiplicative group of positive real numbers. -/
noncomputable def quotientNormOneEquiv :
    IdeleClassGroup (𝓞 K) K ⧸ normOne K ≃* ℝ≥0ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (normOne_eq_ker_ideleClassNorm K)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (ideleClassNorm (K := K)) ideleClassNorm_surjective)

variable {K} in
/-- `quotientNormOneEquiv` sends the coset of an idele class to its idele class norm. -/
@[simp]
theorem quotientNormOneEquiv_mk {c : IdeleClassGroup (𝓞 K) K} :
    quotientNormOneEquiv K (c : IdeleClassGroup (𝓞 K) K ⧸ normOne K) = ideleClassNorm c := by
  rw [quotientNormOneEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk]

/-- The norm-quotient equivalence `C_K / C_K¹ ≃* ℝ≥0ˣ` is continuous. -/
@[continuity, fun_prop]
theorem continuous_quotientNormOneEquiv : Continuous (quotientNormOneEquiv K) :=
  (QuotientGroup.isQuotientMap_mk (normOne K)).continuous_iff.mpr <| by
    simpa only [Function.comp_def, QuotientGroup.mk'_apply, quotientNormOneEquiv_mk] using
      continuous_ideleClassNorm (K := K)

/-- **The norm quotient `C_K / C_K¹` is not compact.** -/
theorem not_compactSpace_quotient_normOne :
    ¬ CompactSpace (IdeleClassGroup (𝓞 K) K ⧸ normOne K) := fun _ ↦
  not_compactSpace_units_nnreal <|
    (quotientNormOneEquiv K).surjective.compactSpace (continuous_quotientNormOneEquiv K)

/-- **The full idele class group is not compact**: its continuous norm quotient is `ℝ>0`. -/
theorem not_compactSpace : ¬ CompactSpace (IdeleClassGroup (𝓞 K) K) := fun _ ↦
  not_compactSpace_units_nnreal <|
    ideleClassNorm_surjective.compactSpace (continuous_ideleClassNorm (K := K))

/-- The full idele class group is not a compact set. -/
theorem not_isCompact_univ : ¬ IsCompact (Set.univ : Set (IdeleClassGroup (𝓞 K) K)) := by
  rw [isCompact_univ_iff]
  exact not_compactSpace K

/-- **The class-group homomorphism is surjective on the norm-one idele class group.** -/
theorem toClassGroup_domRestrict_normOne_surjective :
    Function.Surjective
      ((NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).domRestrict (normOne K)) := by
  intro c
  obtain ⟨b, hb1, hbc⟩ := ClassGroup.exists_ideleNorm_eq_one_and_toClassGroup_eq (K := K) c
  exact ⟨⟨(b : IdeleClassGroup (𝓞 K) K), mk_mem_normOne_iff.mpr hb1⟩, hbc⟩

/-- The restriction of the class-group homomorphism to the norm-one idele class group is locally
constant. -/
theorem isLocallyConstant_toClassGroup_domRestrict_normOne :
    IsLocallyConstant
      ((NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).domRestrict (normOne K)) :=
  (NumberField.IdeleClassGroup.isLocallyConstant_toClassGroup (𝓞 K) K).comp_continuous
    continuous_subtype_val

/-- The kernel of the class-group homomorphism on the norm-one idele class group is open. -/
theorem isOpen_ker_toClassGroup_domRestrict_normOne :
    IsOpen (((NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).domRestrict (normOne K)).ker :
      Set (normOne K)) :=
  (isLocallyConstant_toClassGroup_domRestrict_normOne K) {(1 : ClassGroup (𝓞 K))}

/-- **The kernel of the class-group homomorphism has finite index in `C_K¹`**, recovered directly
from compactness of `C_K¹` since its intersection with `C_K¹` is an open subgroup. -/
instance isFiniteRelIndex_ker_toClassGroup_normOne :
    (NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker.IsFiniteRelIndex (normOne K) := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  have := Subgroup.quotient_finite_of_isOpen
    ((NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker.subgroupOf (normOne K))
    ((NumberField.IdeleClassGroup.isOpen_ker_toClassGroup (𝓞 K) K).preimage continuous_subtype_val)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **The ideal class group is a quotient of the norm-one idele class group** by its open subgroup
of norm-one classes with everywhere-integral representatives. -/
noncomputable def normOneQuotientEquivClassGroup :
    normOne K ⧸
      ((NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker.subgroupOf (normOne K)) ≃*
        ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq (MonoidHom.ker_domRestrict _ _).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (toClassGroup_domRestrict_normOne_surjective K))

variable {K} in
/-- `normOneQuotientEquivClassGroup` sends the coset of a norm-one idele class to its ideal
class. -/
@[simp]
theorem normOneQuotientEquivClassGroup_mk (c : normOne K) :
    normOneQuotientEquivClassGroup K
      (c : normOne K ⧸
        ((NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker.subgroupOf (normOne K))) =
      NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K c := by
  rw [normOneQuotientEquivClassGroup, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk,
    MonoidHom.domRestrict_apply]

/-- **Finiteness of the ideal class group recovered from compactness of `C_K¹`**: the locally
constant class-group homomorphism on the compact group `C_K¹` is surjective. -/
theorem finite_classGroup_of_compactSpace_normOne : Finite (ClassGroup (𝓞 K)) := by
  have := Subgroup.quotient_finite_of_isOpen
    ((NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker.subgroupOf (normOne K))
    ((NumberField.IdeleClassGroup.isOpen_ker_toClassGroup (𝓞 K) K).preimage continuous_subtype_val)
  exact Finite.of_equiv _ (normOneQuotientEquivClassGroup K).toEquiv

/-- The order of the ideal class group is the index in `C_K¹` of the kernel of the class-group
homomorphism. -/
theorem relIndex_ker_toClassGroup_normOne :
    (NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker.relIndex (normOne K) =
      Nat.card (ClassGroup (𝓞 K)) :=
  Nat.card_congr (normOneQuotientEquivClassGroup K).toEquiv

/-- The class number of `K` is the index in `C_K¹` of the kernel of the class-group map. -/
theorem classNumber_eq_relIndex_ker_toClassGroup_normOne :
    classNumber K =
      (NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker.relIndex (normOne K) := by
  rw [relIndex_ker_toClassGroup_normOne, classNumber, Nat.card_eq_fintype_card]

/-- The norm-one idele classes with trivial ideal class form a compact subset of `C_K`. -/
theorem isCompact_ker_toClassGroup_inf_normOne :
    IsCompact (((NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker ⊓ normOne K :
      Subgroup (IdeleClassGroup (𝓞 K) K)) : Set (IdeleClassGroup (𝓞 K) K)) :=
  (isCompact_normOne K).inter_left (NumberField.IdeleClassGroup.isClosed_ker_toClassGroup (𝓞 K) K)

/-- The kernel of the class-group map on `C_K¹` is a compact subgroup. -/
instance compactSpace_ker_toClassGroup_subgroupOf_normOne :
    CompactSpace
      (((NumberField.IdeleClassGroup.toClassGroup (𝓞 K) K).ker).subgroupOf (normOne K)) :=
  isCompact_iff_compactSpace.mp <|
    ((NumberField.IdeleClassGroup.isClosed_ker_toClassGroup (𝓞 K) K).preimage
      continuous_subtype_val).isCompact

end IdeleClassGroup

end TauCeti.GlobalNumberFields

namespace NumberField.IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- **The full idele group of a number field is not compact**: its continuous idele norm surjects
onto `ℝ>0`. -/
theorem not_compactSpace : ¬ CompactSpace (IdeleGroup (𝓞 K) K) := fun _ ↦
  TauCeti.GlobalNumberFields.not_compactSpace_units_nnreal <|
    TauCeti.GlobalNumberFields.ideleNorm_surjective.compactSpace
      (TauCeti.GlobalNumberFields.continuous_ideleNorm (K := K))

/-- The full idele group of a number field is not a compact set. -/
theorem not_isCompact_univ : ¬ IsCompact (Set.univ : Set (IdeleGroup (𝓞 K) K)) := by
  rw [isCompact_univ_iff]
  exact not_compactSpace K

end NumberField.IdeleGroup
