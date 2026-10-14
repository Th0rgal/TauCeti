/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Base change of structured linear schemes and geometric vector bundles

For a morphism of schemes `f : Y ⟶ X`, we define base change functors:
* `TauCeti.AlgebraicGeometry.baseChangeLinearScheme f`: base change of structured linear schemes
  `QuasicoherentLinearScheme X ⥤ QuasicoherentLinearScheme Y`;
* `TauCeti.AlgebraicGeometry.linearSpecBaseChangeIso f F`: canonical isomorphism
  `(baseChangeLinearScheme f).obj ((linearSpec X).obj F) ≅
    (linearSpec Y).obj (op ((pullbackQuasicoherent f).obj F.unop))`;
* `TauCeti.AlgebraicGeometry.baseChangeGeometricVectorBundle f`: base change of geometric vector
  bundles `GeometricVectorBundle X ⥤ GeometricVectorBundle Y`;
* `TauCeti.AlgebraicGeometry.totalSpaceBaseChangeIso f E`: canonical isomorphism
  `(baseChangeGeometricVectorBundle f).obj ((totalSpace X).obj E) ≅
    (totalSpace Y).obj ((pullbackFiniteLocallyFree f).obj E)`.
-/

public section

open CategoryTheory Category Limits Opposite MonoidalCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- Construct an isomorphism in `QuasicoherentSheaf X` from an isomorphism of underlying
`X.Modules`. -/
@[expose]
def quasicoherentSheafIsoMk {X : Scheme.{u}} {E F : QuasicoherentSheaf X}
    (e : E.obj ≅ F.obj) : E ≅ F where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := ObjectProperty.hom_ext _ e.hom_inv_id
  inv_hom_id := ObjectProperty.hom_ext _ e.inv_hom_id

/-- Base change of structured linear schemes along `f : Y ⟶ X`. -/
@[expose]
noncomputable def baseChangeLinearScheme {X Y : Scheme.{u}} (f : Y ⟶ X) :
    QuasicoherentLinearScheme X ⥤ QuasicoherentLinearScheme Y :=
  degreeOne X ⋙ (pullbackQuasicoherent f).op ⋙ linearSpec Y

/-- Base change of `linearSpec X` along `f : Y ⟶ X` is canonically isomorphic to `linearSpec Y` of
the pulled-back quasi-coherent sheaf. -/
@[expose]
noncomputable def linearSpecBaseChangeIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (baseChangeLinearScheme f).obj ((linearSpec X).obj F) ≅
      (linearSpec Y).obj (op ((pullbackQuasicoherent f).obj F.unop)) :=
  (linearSpec Y).mapIso ((pullbackQuasicoherent f).op.mapIso (degreeOneLinearSpecIso F))

/-- Base change of geometric vector bundles along `f : Y ⟶ X`. -/
@[expose]
noncomputable def baseChangeGeometricVectorBundle {X Y : Scheme.{u}} (f : Y ⟶ X) :
    GeometricVectorBundle X ⥤ GeometricVectorBundle Y :=
  (isGeometricVectorBundle Y).lift
    (geometricVectorBundleToLinearScheme X ⋙ baseChangeLinearScheme f) fun V ↦ by
      let E : FiniteLocallyFreeSheaf X := V.property.choose
      let eE : E.obj ≅ ((degreeOne X).obj V.obj).unop.obj := V.property.choose_spec.some
      let G : QuasicoherentSheaf X := ((degreeOne X).obj V.obj).unop
      refine ⟨(pullbackFiniteLocallyFree f).obj E,
        ⟨eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj f E) ≪≫
          (Scheme.Modules.pullback f).mapIso eE ≪≫
          eqToIso (QuasicoherentSheaf.pullback_obj_obj f G).symm ≪≫
          quasicoherentSheafObjIso
            (degreeOneLinearSpecIso (op ((pullbackQuasicoherent f).obj G))).unop⟩⟩

/-- Pullback of `finiteLocallyFreeToQuasicoherent X` commutes with `pullbackFiniteLocallyFree f`
and `pullbackQuasicoherent f`. -/
@[expose]
noncomputable def pullbackFiniteLocallyFreeToQuasicoherentIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : FiniteLocallyFreeSheaf X) :
    (pullbackQuasicoherent f).obj ((finiteLocallyFreeToQuasicoherent X).obj E) ≅
      (finiteLocallyFreeToQuasicoherent Y).obj ((pullbackFiniteLocallyFree f).obj E) :=
  quasicoherentSheafIsoMk
    (eqToIso (QuasicoherentSheaf.pullback_obj_obj f ((finiteLocallyFreeToQuasicoherent X).obj E)) ≪≫
      eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj f E).symm)

/-- Base change of the geometric total space `(totalSpace X).obj E` along `f : Y ⟶ X` is
canonically isomorphic to the total space of the pulled-back bundle
`(pullbackFiniteLocallyFree f).obj E`. -/
@[expose]
noncomputable def totalSpaceBaseChangeIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : FiniteLocallyFreeSheaf X) :
    (baseChangeGeometricVectorBundle f).obj ((totalSpace X).obj E) ≅
      (totalSpace Y).obj ((pullbackFiniteLocallyFree f).obj E) :=
  ObjectProperty.isoMk (isGeometricVectorBundle Y)
    (linearSpecBaseChangeIso f ((dualAsQuasicoherentOp X).obj E) ≪≫
      (linearSpec Y).mapIso
        ((pullbackFiniteLocallyFreeToQuasicoherentIso f (FiniteLocallyFreeSheaf.dual E) ≪≫
          (finiteLocallyFreeToQuasicoherent Y).mapIso
            (FiniteLocallyFreeSheaf.pullbackDualIso f E)).op.symm))

end

end TauCeti.AlgebraicGeometry
