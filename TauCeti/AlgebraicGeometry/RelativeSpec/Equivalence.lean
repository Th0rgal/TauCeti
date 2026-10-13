/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Counit
public import TauCeti.AlgebraicGeometry.RelativeSpec.Unit

/-!
# The anti-equivalence between quasi-coherent algebras and affine schemes over a base

For any scheme `X`, the relative spectrum functor
`relativeSpec X : (QuasicoherentAlgebra X)ᵒᵖ ⥤ AffineSchemeOver X` and the coordinate-algebra
functor `affineFunctions X : AffineSchemeOver X ⥤ (QuasicoherentAlgebra X)ᵒᵖ` form an equivalence
of categories, with unit `relativeSpecUnit X` and counit `relativeSpecCounit X`.

The key input is the triangle identity
`CommMon.relativeSpecMap_relativeSpecPushforwardIso_hom_comp_relativeSpecFunctionsToScheme`:
for a quasi-coherent commutative `𝒪ₓ`-algebra `A` with structure morphism
`p : Spec_X A ⟶ X`, pulling back functions along the unit `p_* 𝒪 ≅ A` and applying the
geometric recovery morphism `Spec_X (p_* 𝒪) ⟶ Spec_X A` yields the identity on `Spec_X A`.
Over each affine open `U` of `X`, both morphisms are given by the standard affine identification
of the chart `Spec Γ(A.X, U)` with the spectrum of its global sections.

## Main declarations

* `CommMon.relativeSpecMap_relativeSpecPushforwardIso_hom_comp_relativeSpecFunctionsToScheme`:
  the scheme-side triangle identity for a quasi-coherent algebra `A`.
* `TauCeti.AlgebraicGeometry.relativeSpecEquiv`: the equivalence of categories
  `(QuasicoherentAlgebra X)ᵒᵖ ≌ AffineSchemeOver X`.
* `TauCeti.AlgebraicGeometry.relativeSpecEquivFunctorIso` and
  `TauCeti.AlgebraicGeometry.relativeSpecEquivInverseIso`: the canonical identifications of the
  functors of `relativeSpecEquiv X` with `relativeSpec X` and `affineFunctions X`.
* `TauCeti.AlgebraicGeometry.relativeSpecHomEquiv`: the hom-set bijection
  `(V ⟶ (relativeSpec X).obj (op A)) ≃ (A ⟶ ((affineFunctions X).obj V).unop)` classifying
  morphisms of affine `X`-schemes into a relative spectrum by morphisms of quasi-coherent
  `𝒪ₓ`-algebras.

## References

* The Stacks Project, [Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ) (relative spectrum as
  a functor).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3–1.4.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace CategoryTheory.CommMon

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon X.Modules) [A.X.IsQuasicoherent]

private lemma pushforwardStructureAlgebraPresheafIso_inv_comp_relativeSpecPushforwardIso
    (U : X.AffineZariskiSite) :
    A.relativeSpecToBase.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1) ≫
      CommRingCat.ofHom
        (CommMon.sectionsAlgHom A.relativeSpecPushforwardIso.hom U.1).toRingHom =
      (A.relativeSpecCover.f U).appLE (A.relativeSpecToBase ⁻¹ᵁ U.1) ⊤
        (A.top_le_preimage_relativeSpecToBase U) ≫
        (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, U.1))).hom := by
  rw [Scheme.Hom.pushforwardStructureAlgebraPresheafIso_inv_app]
  apply ConcreteCategory.hom_ext
  intro x
  change CommMon.sectionsAlgHom A.relativeSpecPushforwardIso.hom U.1
    ((A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv U.1).symm x) =
    (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, U.1))).hom
      ((A.relativeSpecCover.f U).appLE (A.relativeSpecToBase ⁻¹ᵁ U.1) ⊤
        (A.top_le_preimage_relativeSpecToBase U) x)
  rw [sectionsAlgHom_relativeSpecPushforwardIso_hom_apply,
    relativeSpecCoverFunctionAlgebraSectionsRingEquiv_apply, RingEquiv.apply_symm_apply]

/-- For a quasi-coherent commutative `𝒪ₓ`-algebra `A`, applying `Spec_X` to the unit isomorphism
`p_* 𝒪 ≅ A` and composing with the canonical recovery map `Spec_X (p_* 𝒪) ⟶ Spec_X A` is the
identity on `Spec_X A`. -/
@[reassoc (attr := simp)]
lemma relativeSpecMap_relativeSpecPushforwardIso_hom_comp_relativeSpecFunctionsToScheme :
    CommMon.relativeSpecMap A.relativeSpecPushforwardIso.hom ≫
      A.relativeSpecToBase.relativeSpecFunctionsToScheme = 𝟙 A.relativeSpec := by
  apply A.relativeSpec_hom_ext
  intro U
  let R : CommRingCat.{u} := CommRingCat.of Γ(A.X, U.1)
  let p := A.relativeSpecToBase
  let fU : CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1) ⟶ R :=
    CommRingCat.ofHom (CommMon.sectionsAlgHom A.relativeSpecPushforwardIso.hom U.1).toRingHom
  let kU : Γ(A.relativeSpec, p ⁻¹ᵁ U.1) ⟶
      CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1) :=
    p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1)
  have h1 : A.relativeSpecCover.f U ≫
      (CommMon.relativeSpecMap A.relativeSpecPushforwardIso.hom ≫
        p.relativeSpecFunctionsToScheme) =
      Spec.map fU ≫ (Spec.map kU ≫ (U.2.preimage p).fromSpec) :=
    (CommMon.relativeSpecCover_f_relativeSpecMap_assoc A.relativeSpecPushforwardIso.hom U
      p.relativeSpecFunctionsToScheme).trans
      (congrArg (Spec.map fU ≫ ·) (p.relativeSpecCover_f_relativeSpecFunctionsToScheme U))
  let ιA : Spec R ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let gU : Γ(A.relativeSpec, p ⁻¹ᵁ U.1) ⟶ Γ(Spec R, ⊤) :=
    ιA.appLE (p ⁻¹ᵁ U.1) ⊤ (A.top_le_preimage_relativeSpecToBase U)
  have h2 : kU ≫ fU = gU ≫ (Scheme.ΓSpecIso R).hom :=
    pushforwardStructureAlgebraPresheafIso_inv_comp_relativeSpecPushforwardIso A U
  have h2' : Spec.map fU ≫ (Spec.map kU ≫ (U.2.preimage p).fromSpec) =
      Spec.map (Scheme.ΓSpecIso R).hom ≫ (Spec.map gU ≫ (U.2.preimage p).fromSpec) :=
    (Spec.map_comp_assoc kU fU (U.2.preimage p).fromSpec).symm.trans
      ((congrArg (fun φ ↦ Spec.map φ ≫ (U.2.preimage p).fromSpec) h2).trans
        (Spec.map_comp_assoc gU (Scheme.ΓSpecIso R).hom (U.2.preimage p).fromSpec))
  have h3 : Spec.map fU ≫ (Spec.map kU ≫ (U.2.preimage p).fromSpec) =
      Spec.map (Scheme.ΓSpecIso R).hom ≫
        ((isAffineOpen_top (Spec R)).fromSpec ≫ A.relativeSpecCover.f U) :=
    h2'.trans (congrArg (Spec.map (Scheme.ΓSpecIso R).hom ≫ ·)
      (IsAffineOpen.SpecMap_appLE_fromSpec (A.relativeSpecCover.f U) (U.2.preimage p)
        (isAffineOpen_top (Spec R)) (A.top_le_preimage_relativeSpecToBase U)))
  have h4 : Spec.map (Scheme.ΓSpecIso R).hom ≫ (isAffineOpen_top (Spec R)).fromSpec =
      𝟙 (Spec R) := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id]
  exact h1.trans (h3.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ A.relativeSpecCover.f U) h4).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm))))

end

end CategoryTheory.CommMon

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

/-- The anti-equivalence of categories between quasi-coherent commutative `𝒪ₓ`-algebras and
affine schemes over `X`, given by `relativeSpec X` and `affineFunctions X`. -/
@[expose]
def relativeSpecEquiv : (QuasicoherentAlgebra X)ᵒᵖ ≌ AffineSchemeOver X where
  functor := relativeSpec X
  inverse := affineFunctions X
  unitIso := relativeSpecUnit X
  counitIso := relativeSpecCounit X
  functor_unitIso_comp A := by
    apply MorphismProperty.Over.Hom.ext
    change ((relativeSpec X).map ((relativeSpecUnit X).hom.app A)).left ≫
        ((relativeSpecCounit X).hom.app ((relativeSpec X).obj A)).left =
      𝟙 A.unop.obj.relativeSpec
    rw [relativeSpec_map_left, relativeSpecUnit_hom_app_unop_hom,
      relativeSpecCounit_hom_app_left]
    exact CommMon.relativeSpecMap_relativeSpecPushforwardIso_hom_comp_relativeSpecFunctionsToScheme
      A.unop.obj

@[simp]
lemma relativeSpecEquiv_functor : (relativeSpecEquiv X).functor = relativeSpec X :=
  (rfl)

@[simp]
lemma relativeSpecEquiv_inverse : (relativeSpecEquiv X).inverse = affineFunctions X :=
  (rfl)

@[simp]
lemma relativeSpecEquiv_unitIso : (relativeSpecEquiv X).unitIso = relativeSpecUnit X :=
  (rfl)

@[simp]
lemma relativeSpecEquiv_counitIso : (relativeSpecEquiv X).counitIso = relativeSpecCounit X :=
  (rfl)

@[simp]
lemma relativeSpecEquiv_unit : (relativeSpecEquiv X).unit = (relativeSpecUnit X).hom :=
  (rfl)

@[simp]
lemma relativeSpecEquiv_unitInv : (relativeSpecEquiv X).unitInv = (relativeSpecUnit X).inv :=
  (rfl)

@[simp]
lemma relativeSpecEquiv_counit : (relativeSpecEquiv X).counit = (relativeSpecCounit X).hom :=
  (rfl)

@[simp]
lemma relativeSpecEquiv_counitInv :
    (relativeSpecEquiv X).counitInv = (relativeSpecCounit X).inv :=
  (rfl)

/-- The forward functor of `relativeSpecEquiv X` is canonically `relativeSpec X`. -/
@[expose]
def relativeSpecEquivFunctorIso : (relativeSpecEquiv X).functor ≅ relativeSpec X :=
  Iso.refl (relativeSpec X)

@[simp]
lemma relativeSpecEquivFunctorIso_hom :
    (relativeSpecEquivFunctorIso X).hom = 𝟙 (relativeSpec X) :=
  (rfl)

@[simp]
lemma relativeSpecEquivFunctorIso_inv :
    (relativeSpecEquivFunctorIso X).inv = 𝟙 (relativeSpec X) :=
  (rfl)

/-- The inverse functor of `relativeSpecEquiv X` is canonically `affineFunctions X`. -/
@[expose]
def relativeSpecEquivInverseIso : (relativeSpecEquiv X).inverse ≅ affineFunctions X :=
  Iso.refl (affineFunctions X)

@[simp]
lemma relativeSpecEquivInverseIso_hom :
    (relativeSpecEquivInverseIso X).hom = 𝟙 (affineFunctions X) :=
  (rfl)

@[simp]
lemma relativeSpecEquivInverseIso_inv :
    (relativeSpecEquivInverseIso X).inv = 𝟙 (affineFunctions X) :=
  (rfl)

/-- `relativeSpec X` is fully faithful. -/
def fullyFaithfulRelativeSpec : (relativeSpec X).FullyFaithful :=
  (relativeSpecEquiv X).fullyFaithfulFunctor

/-- `affineFunctions X` is fully faithful. -/
def fullyFaithfulAffineFunctions : (affineFunctions X).FullyFaithful :=
  (relativeSpecEquiv X).fullyFaithfulInverse

instance : (relativeSpec X).Full :=
  (relativeSpecEquiv X).full_functor

instance : (relativeSpec X).Faithful :=
  (relativeSpecEquiv X).faithful_functor

instance : (relativeSpec X).EssSurj :=
  (relativeSpecEquiv X).essSurj_functor

instance : (relativeSpec X).IsEquivalence :=
  (relativeSpecEquiv X).isEquivalence_functor

instance : (affineFunctions X).Full :=
  (relativeSpecEquiv X).full_inverse

instance : (affineFunctions X).Faithful :=
  (relativeSpecEquiv X).faithful_inverse

instance : (affineFunctions X).EssSurj :=
  (relativeSpecEquiv X).essSurj_inverse

instance : (affineFunctions X).IsEquivalence :=
  (relativeSpecEquiv X).isEquivalence_inverse

variable {X}

/-- The scheme-side triangle identity for `relativeSpecUnit` and `relativeSpecCounit`. -/
@[reassoc (attr := simp)]
lemma relativeSpec_map_relativeSpecUnit_hom_app_comp_relativeSpecCounit_hom_app
    (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    (relativeSpec X).map ((relativeSpecUnit X).hom.app A) ≫
      (relativeSpecCounit X).hom.app ((relativeSpec X).obj A) =
      𝟙 ((relativeSpec X).obj A) :=
  (relativeSpecEquiv X).functor_unit_comp A

/-- The inverse scheme-side triangle identity for `relativeSpecUnit` and `relativeSpecCounit`. -/
@[reassoc (attr := simp)]
lemma relativeSpecCounit_inv_app_comp_relativeSpec_map_relativeSpecUnit_inv_app
    (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    (relativeSpecCounit X).inv.app ((relativeSpec X).obj A) ≫
      (relativeSpec X).map ((relativeSpecUnit X).inv.app A) =
      𝟙 ((relativeSpec X).obj A) :=
  (relativeSpecEquiv X).counitInv_functor_comp A

/-- The algebra-side triangle identity for `relativeSpecUnit` and `relativeSpecCounit`. -/
@[reassoc (attr := simp)]
lemma relativeSpecUnit_hom_app_comp_affineFunctions_map_relativeSpecCounit_hom_app
    (V : AffineSchemeOver X) :
    (relativeSpecUnit X).hom.app ((affineFunctions X).obj V) ≫
      (affineFunctions X).map ((relativeSpecCounit X).hom.app V) =
      𝟙 ((affineFunctions X).obj V) :=
  (relativeSpecEquiv X).unit_inverse_comp V

/-- The inverse algebra-side triangle identity for `relativeSpecUnit` and `relativeSpecCounit`. -/
@[reassoc (attr := simp)]
lemma affineFunctions_map_relativeSpecCounit_inv_app_comp_relativeSpecUnit_inv_app
    (V : AffineSchemeOver X) :
    (affineFunctions X).map ((relativeSpecCounit X).inv.app V) ≫
      (relativeSpecUnit X).inv.app ((affineFunctions X).obj V) =
      𝟙 ((affineFunctions X).obj V) :=
  (relativeSpecEquiv X).inverse_counitInv_comp V

end

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

open TauCeti.AlgebraicGeometry

/-- For an affine morphism `p : V ⟶ X`, pulling back regular functions along the canonical recovery
morphism `Spec_X (p_* 𝒪_V) ⟶ V` and composing with the algebra-side unit is the identity on
`p_* 𝒪_V`. -/
@[reassoc (attr := simp)]
lemma
    pushforwardStructureAlgebraMap_relativeSpecFunctionsToScheme_comp_relativeSpecPushforwardIso_hom
    {X V : Scheme.{u}} (p : V ⟶ X) [IsAffineHom p] :
    Scheme.Hom.pushforwardStructureAlgebraMap p.relativeSpecFunctionsToScheme
        p.relativeSpecFunctionsToScheme_comp ≫
      p.pushforwardStructureAlgebra.relativeSpecPushforwardIso.hom =
      𝟙 p.pushforwardStructureAlgebra := by
  let V' : AffineSchemeOver X := MorphismProperty.Over.mk ⊤ p inferInstance
  have h := congrArg (fun f ↦ f.unop.hom)
    (relativeSpecUnit_hom_app_comp_affineFunctions_map_relativeSpecCounit_hom_app V')
  change (((affineFunctions X).map ((relativeSpecCounit X).hom.app V')).unop.hom ≫
      ((relativeSpecUnit X).hom.app ((affineFunctions X).obj V')).unop.hom) =
    𝟙 p.pushforwardStructureAlgebra at h
  rw [affineFunctions_map_unop_hom, relativeSpecUnit_hom_app_unop_hom] at h
  have hmap : ∀ (f : p.pushforwardStructureAlgebra.relativeSpec ⟶ V)
      (hf : f ≫ p = p.pushforwardStructureAlgebra.relativeSpecToBase),
      f = p.relativeSpecFunctionsToScheme →
      Scheme.Hom.pushforwardStructureAlgebraMap f hf =
        Scheme.Hom.pushforwardStructureAlgebraMap p.relativeSpecFunctionsToScheme
          p.relativeSpecFunctionsToScheme_comp := by
    rintro _ _ rfl
    rfl
  exact (congrArg (· ≫ p.pushforwardStructureAlgebra.relativeSpecPushforwardIso.hom)
    (hmap ((relativeSpecCounit X).hom.app V').left
      (MorphismProperty.Over.w ((relativeSpecCounit X).hom.app V'))
      (relativeSpecCounit_hom_app_left V')).symm).trans h

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- Morphisms from an affine `X`-scheme `V` into the relative spectrum `Spec_X A` of a
quasi-coherent commutative `𝒪ₓ`-algebra `A` correspond bijectively to `𝒪ₓ`-algebra morphisms from
`A` to the coordinate algebra `p_* 𝒪_V` of `V`. -/
@[expose]
def relativeSpecHomEquiv (V : AffineSchemeOver X) (A : QuasicoherentAlgebra X) :
    (V ⟶ (relativeSpec X).obj (op A)) ≃ (A ⟶ ((affineFunctions X).obj V).unop) where
  toFun g := ((relativeSpecUnit X).inv.app (op A)).unop ≫ ((affineFunctions X).map g).unop
  invFun f := (relativeSpecCounit X).inv.app V ≫ (relativeSpec X).map f.op
  left_inv g := by
    have hnat :
        (relativeSpecCounit X).inv.app V ≫ (relativeSpec X).map ((affineFunctions X).map g) =
          g ≫ (relativeSpecCounit X).inv.app ((relativeSpec X).obj (op A)) :=
      ((relativeSpecCounit X).inv.naturality g).symm
    calc
      (relativeSpecCounit X).inv.app V ≫
          (relativeSpec X).map
            (((relativeSpecUnit X).inv.app (op A)).unop ≫ ((affineFunctions X).map g).unop).op
        = ((relativeSpecCounit X).inv.app V ≫ (relativeSpec X).map ((affineFunctions X).map g)) ≫
            (relativeSpec X).map ((relativeSpecUnit X).inv.app (op A)) := by
          simp [op_comp]
      _ = g ≫ ((relativeSpecCounit X).inv.app ((relativeSpec X).obj (op A)) ≫
            (relativeSpec X).map ((relativeSpecUnit X).inv.app (op A))) := by
          rw [hnat, Category.assoc]
      _ = g := by
          rw [relativeSpecCounit_inv_app_comp_relativeSpec_map_relativeSpecUnit_inv_app]
          exact Category.comp_id g
  right_inv f := by
    apply Quiver.Hom.op_inj
    have hnat : (affineFunctions X).map ((relativeSpec X).map f.op) ≫
        (relativeSpecUnit X).inv.app (op A) =
        (relativeSpecUnit X).inv.app ((affineFunctions X).obj V) ≫ f.op :=
      (relativeSpecUnit X).inv.naturality f.op
    calc
      (((relativeSpecUnit X).inv.app (op A)).unop ≫
          ((affineFunctions X).map
            ((relativeSpecCounit X).inv.app V ≫ (relativeSpec X).map f.op)).unop).op
        = (affineFunctions X).map ((relativeSpecCounit X).inv.app V) ≫
            ((affineFunctions X).map ((relativeSpec X).map f.op) ≫
              (relativeSpecUnit X).inv.app (op A)) := by
          simp [op_comp]
      _ = ((affineFunctions X).map ((relativeSpecCounit X).inv.app V) ≫
            (relativeSpecUnit X).inv.app ((affineFunctions X).obj V)) ≫ f.op := by
          rw [hnat, Category.assoc]
      _ = f.op := by
          rw [affineFunctions_map_relativeSpecCounit_inv_app_comp_relativeSpecUnit_inv_app]
          exact Category.id_comp f.op

lemma relativeSpecHomEquiv_apply (V : AffineSchemeOver X) (A : QuasicoherentAlgebra X)
    (g : V ⟶ (relativeSpec X).obj (op A)) :
    relativeSpecHomEquiv V A g =
      ((relativeSpecUnit X).inv.app (op A)).unop ≫ ((affineFunctions X).map g).unop :=
  (rfl)

@[simp]
lemma relativeSpecHomEquiv_apply_hom (V : AffineSchemeOver X) (A : QuasicoherentAlgebra X)
    (g : V ⟶ (relativeSpec X).obj (op A)) :
    (relativeSpecHomEquiv V A g).hom =
      A.obj.relativeSpecPushforwardIso.inv ≫
        Scheme.Hom.pushforwardStructureAlgebraMap g.left (MorphismProperty.Over.w g) := by
  change (((relativeSpecUnit X).inv.app (op A)).unop.hom ≫
      ((affineFunctions X).map g).unop.hom) = _
  rw [relativeSpecUnit_inv_app_unop_hom, affineFunctions_map_unop_hom]
  rfl

lemma relativeSpecHomEquiv_symm_apply (V : AffineSchemeOver X) (A : QuasicoherentAlgebra X)
    (f : A ⟶ ((affineFunctions X).obj V).unop) :
    (relativeSpecHomEquiv V A).symm f =
      (relativeSpecCounit X).inv.app V ≫ (relativeSpec X).map f.op :=
  (rfl)

@[simp]
lemma relativeSpecHomEquiv_symm_apply_left (V : AffineSchemeOver X) (A : QuasicoherentAlgebra X)
    (f : A ⟶ ((affineFunctions X).obj V).unop) :
    ((relativeSpecHomEquiv V A).symm f).left =
      inv V.hom.relativeSpecFunctionsToScheme ≫ CommMon.relativeSpecMap f.hom := by
  change ((relativeSpecCounit X).inv.app V).left ≫ ((relativeSpec X).map f.op).left = _
  rw [relativeSpecCounit_inv_app_left, relativeSpec_map_left]
  rfl

@[simp]
lemma relativeSpecHomEquiv_id (A : QuasicoherentAlgebra X) :
    relativeSpecHomEquiv ((relativeSpec X).obj (op A)) A (𝟙 ((relativeSpec X).obj (op A))) =
      ((relativeSpecUnit X).inv.app (op A)).unop := by
  simp [relativeSpecHomEquiv_apply]

@[simp]
lemma relativeSpecHomEquiv_symm_id (V : AffineSchemeOver X) :
    (relativeSpecHomEquiv V ((affineFunctions X).obj V).unop).symm
        (𝟙 ((affineFunctions X).obj V).unop) =
      (relativeSpecCounit X).inv.app V := by
  rw [relativeSpecHomEquiv_symm_apply, op_id]
  exact (congrArg ((relativeSpecCounit X).inv.app V ≫ ·)
    ((relativeSpec X).map_id ((affineFunctions X).obj V))).trans (Category.comp_id _)

lemma relativeSpecHomEquiv_comp_left {W V : AffineSchemeOver X} (A : QuasicoherentAlgebra X)
    (h : W ⟶ V) (g : V ⟶ (relativeSpec X).obj (op A)) :
    relativeSpecHomEquiv W A (h ≫ g) =
      relativeSpecHomEquiv V A g ≫ ((affineFunctions X).map h).unop := by
  simp [relativeSpecHomEquiv_apply]

lemma relativeSpecHomEquiv_comp_right (V : AffineSchemeOver X) {A B : QuasicoherentAlgebra X}
    (f : B ⟶ A) (g : V ⟶ (relativeSpec X).obj (op A)) :
    relativeSpecHomEquiv V B (g ≫ (relativeSpec X).map f.op) =
      f ≫ relativeSpecHomEquiv V A g := by
  apply Quiver.Hom.op_inj
  have hnat : (affineFunctions X).map ((relativeSpec X).map f.op) ≫
      (relativeSpecUnit X).inv.app (op B) =
      (relativeSpecUnit X).inv.app (op A) ≫ f.op :=
    (relativeSpecUnit X).inv.naturality f.op
  calc
    (relativeSpecHomEquiv V B (g ≫ (relativeSpec X).map f.op)).op
      = (affineFunctions X).map g ≫
          ((affineFunctions X).map ((relativeSpec X).map f.op) ≫
            (relativeSpecUnit X).inv.app (op B)) := by
        simp [relativeSpecHomEquiv_apply, op_comp]
    _ = ((affineFunctions X).map g ≫ (relativeSpecUnit X).inv.app (op A)) ≫ f.op := by
        rw [hnat, Category.assoc]
    _ = (f ≫ relativeSpecHomEquiv V A g).op := by
        simp [relativeSpecHomEquiv_apply, op_comp]

end

end TauCeti.AlgebraicGeometry

end
