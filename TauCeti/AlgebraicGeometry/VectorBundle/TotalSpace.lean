/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.LinearScheme
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Pullback

/-!
# Geometric vector bundles and the total-space equivalence

For a scheme `X`, we define:
* `TauCeti.AlgebraicGeometry.isGeometricVectorBundle X` and
  `TauCeti.AlgebraicGeometry.GeometricVectorBundle X`: the full subcategory of structured linear
  `X`-schemes whose degree-`1` coordinate sheaf is finite locally free;
* `TauCeti.AlgebraicGeometry.geometricVectorBundleToLinearScheme X`: the forgetful functor to
  `QuasicoherentLinearScheme X`;
* `TauCeti.AlgebraicGeometry.dualAsQuasicoherentOp X`: the functor sending a finite locally free
  sheaf `E` to `op (E^∨)` in `(QuasicoherentSheaf X)ᵒᵖ`;
* `TauCeti.AlgebraicGeometry.totalSpaceScheme X` and `TauCeti.AlgebraicGeometry.totalSpace X`:
  the geometric total space functor `E ↦ Spec_X (Sym^* (E^∨))` valued in `AffineSchemeOver X` and
  `GeometricVectorBundle X`;
* `TauCeti.AlgebraicGeometry.totalSpaceEquiv X`: the covariant equivalence of categories
  `FiniteLocallyFreeSheaf X ≌ GeometricVectorBundle X`.
-/

public section

open CategoryTheory Category Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- Top-level alias for `FiniteLocallyFreeSheaf.toQuasicoherent`. -/
abbrev finiteLocallyFreeToQuasicoherent (X : Scheme.{u}) :
    FiniteLocallyFreeSheaf X ⥤ QuasicoherentSheaf X :=
  FiniteLocallyFreeSheaf.toQuasicoherent X

/-- Top-level alias for `FiniteLocallyFreeSheaf.dualFunctor`. -/
abbrev dual (X : Scheme.{u}) :
    (FiniteLocallyFreeSheaf X)ᵒᵖ ⥤ FiniteLocallyFreeSheaf X :=
  FiniteLocallyFreeSheaf.dualFunctor

/-- Top-level alias for `FiniteLocallyFreeSheaf.pullback`. -/
abbrev pullbackFiniteLocallyFree {X Y : Scheme.{u}} (f : Y ⟶ X) :
    FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y :=
  FiniteLocallyFreeSheaf.pullback f

/-- Top-level alias for `QuasicoherentSheaf.pullback`. -/
abbrev pullbackQuasicoherent {X Y : Scheme.{u}} (f : Y ⟶ X) :
    QuasicoherentSheaf X ⥤ QuasicoherentSheaf Y :=
  QuasicoherentSheaf.pullback f

/-- A structured linear scheme over `X` is a geometric vector bundle if its degree-`1` coordinate
sheaf is isomorphic to a finite locally free sheaf on `X`. -/
@[expose]
noncomputable def isGeometricVectorBundle (X : Scheme.{u}) :
    ObjectProperty (QuasicoherentLinearScheme X) :=
  fun V ↦ ∃ E : FiniteLocallyFreeSheaf X,
    Nonempty (E.obj ≅ ((degreeOne X).obj V).unop.obj)

/-- A structured linear scheme over `X` is a geometric vector bundle if and only if its degree-`1`
coordinate sheaf is finite locally free. -/
lemma isGeometricVectorBundle_iff {X : Scheme.{u}} (V : QuasicoherentLinearScheme X) :
    isGeometricVectorBundle X V ↔
      Scheme.Modules.isFiniteLocallyFree X ((degreeOne X).obj V).unop.obj := by
  refine ⟨?_, fun h ↦ ⟨⟨_, h⟩, ⟨Iso.refl _⟩⟩⟩
  rintro ⟨E, ⟨e⟩⟩
  exact (Scheme.Modules.isFiniteLocallyFree X).prop_of_iso e E.property

/-- The category of geometric vector bundles over `X`, defined as the full subcategory of
`QuasicoherentLinearScheme X` cut out by `isGeometricVectorBundle X`. -/
noncomputable abbrev GeometricVectorBundle (X : Scheme.{u}) :=
  (isGeometricVectorBundle X).FullSubcategory

/-- The forgetful functor from geometric vector bundles over `X` to structured linear schemes over
`X`. -/
noncomputable abbrev geometricVectorBundleToLinearScheme (X : Scheme.{u}) :
    GeometricVectorBundle X ⥤ QuasicoherentLinearScheme X :=
  ObjectProperty.ι (isGeometricVectorBundle X)

/-- The functor sending a finite locally free sheaf `E` on `X` to `op (E^∨)` in
`(QuasicoherentSheaf X)ᵒᵖ`. -/
@[expose]
noncomputable def dualAsQuasicoherentOp (X : Scheme.{u}) :
    FiniteLocallyFreeSheaf X ⥤ (QuasicoherentSheaf X)ᵒᵖ :=
  (dual X).rightOp ⋙ (finiteLocallyFreeToQuasicoherent X).op

instance faithfulDualRightOp (X : Scheme.{u}) : (dual X).rightOp.Faithful :=
  Functor.Faithful.of_comp_iso FiniteLocallyFreeSheaf.evalNatIso.symm

instance faithfulDual (X : Scheme.{u}) : (dual X).Faithful where
  map_injective {E F} f g h := by
    have h' : (dual X).rightOp.map f.unop = (dual X).rightOp.map g.unop :=
      congrArg Quiver.Hom.op h
    exact Quiver.Hom.unop_inj ((dual X).rightOp.map_injective h')

/-- If `𝟭 C ≅ F ⋙ G` and `G` is faithful, then `F` is full. -/
lemma full_of_comp_faithful_iso {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) (G : D ⥤ C) [G.Faithful] (e : 𝟭 C ≅ F ⋙ G) : F.Full where
  map_surjective {X Y} φ :=
    ⟨e.hom.app X ≫ G.map φ ≫ e.inv.app Y, G.map_injective <| by
      have hnat := e.hom.naturality (e.hom.app X ≫ G.map φ ≫ e.inv.app Y)
      simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
        assoc, Iso.inv_hom_id_app, comp_id] at hnat
      exact (cancel_epi (e.hom.app X)).1 hnat.symm⟩

instance fullDualRightOp (X : Scheme.{u}) : (dual X).rightOp.Full :=
  full_of_comp_faithful_iso (dual X).rightOp (dual X) FiniteLocallyFreeSheaf.evalNatIso

instance faithfulDualAsQuasicoherentOp (X : Scheme.{u}) :
    (dualAsQuasicoherentOp X).Faithful :=
  Functor.Faithful.comp (dual X).rightOp (finiteLocallyFreeToQuasicoherent X).op

instance fullDualAsQuasicoherentOp (X : Scheme.{u}) :
    (dualAsQuasicoherentOp X).Full :=
  Functor.Full.comp (dual X).rightOp (finiteLocallyFreeToQuasicoherent X).op

/-- The underlying `X.Modules` isomorphism of an isomorphism in `QuasicoherentSheaf X`. -/
@[expose]
def quasicoherentSheafObjIso {X : Scheme.{u}} {E F : QuasicoherentSheaf X} (e : E ≅ F) :
    E.obj ≅ F.obj where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg InducedCategory.Hom.hom e.hom_inv_id
  inv_hom_id := congrArg InducedCategory.Hom.hom e.inv_hom_id

/-- The underlying affine `X`-scheme total space functor `E ↦ Spec_X (Sym (E^∨))` on
`FiniteLocallyFreeSheaf X`. -/
@[expose]
noncomputable def totalSpaceScheme (X : Scheme.{u}) :
    FiniteLocallyFreeSheaf X ⥤ AffineSchemeOver X :=
  dualAsQuasicoherentOp X ⋙ linearSpecScheme X

/-- The geometric total space functor `E ↦ Spec_X (Sym^* (E^∨))` from `FiniteLocallyFreeSheaf X`
to `GeometricVectorBundle X`. -/
@[expose]
noncomputable def totalSpace (X : Scheme.{u}) :
    FiniteLocallyFreeSheaf X ⥤ GeometricVectorBundle X :=
  (isGeometricVectorBundle X).lift (dualAsQuasicoherentOp X ⋙ linearSpec X) fun E ↦
    ⟨FiniteLocallyFreeSheaf.dual E,
      ⟨quasicoherentSheafObjIso
        (degreeOneLinearSpecIso ((dualAsQuasicoherentOp X).obj E)).unop⟩⟩

/-- Forgetting the finite-locally-free degree-`1` condition after `totalSpace X` recovers
`dualAsQuasicoherentOp X ⋙ linearSpec X`. -/
@[expose]
noncomputable def totalSpaceLinearSpecIso (X : Scheme.{u}) :
    totalSpace X ⋙ geometricVectorBundleToLinearScheme X ≅
      dualAsQuasicoherentOp X ⋙ linearSpec X :=
  Iso.refl _

/-- Forgetting down to `AffineSchemeOver X` after `totalSpace X` recovers `totalSpaceScheme X`. -/
@[expose]
noncomputable def totalSpaceForgetIso (X : Scheme.{u}) :
    totalSpace X ⋙ geometricVectorBundleToLinearScheme X ⋙ linearSchemeForget X ≅
      totalSpaceScheme X :=
  Iso.refl _

instance isEquivalenceLinearSpec (X : Scheme.{u}) : (linearSpec X).IsEquivalence :=
  Functor.isEquivalence_of_iso (linearSpecEquivFunctorIso X)

instance faithfulTotalSpace (X : Scheme.{u}) : (totalSpace X).Faithful :=
  haveI : (dualAsQuasicoherentOp X ⋙ linearSpec X).Faithful :=
    Functor.Faithful.comp (dualAsQuasicoherentOp X) (linearSpec X)
  Functor.Faithful.of_comp_iso (totalSpaceLinearSpecIso X)

instance fullTotalSpace (X : Scheme.{u}) : (totalSpace X).Full :=
  haveI : (dualAsQuasicoherentOp X ⋙ linearSpec X).Full :=
    Functor.Full.comp (dualAsQuasicoherentOp X) (linearSpec X)
  haveI : (totalSpace X ⋙ geometricVectorBundleToLinearScheme X).Full :=
    Functor.Full.of_iso (totalSpaceLinearSpecIso X).symm
  Functor.Full.of_comp_faithful (totalSpace X) (geometricVectorBundleToLinearScheme X)

instance essSurjTotalSpace (X : Scheme.{u}) : (totalSpace X).EssSurj where
  mem_essImage V := by
    obtain ⟨E₀, ⟨e₀⟩⟩ := V.property
    let E : FiniteLocallyFreeSheaf X := FiniteLocallyFreeSheaf.dual E₀
    have eDual : ((dualAsQuasicoherentOp X).obj E).unop ≅
        ((degreeOne X).obj V.obj).unop :=
      (finiteLocallyFreeToQuasicoherent X).mapIso (FiniteLocallyFreeSheaf.evalIso E₀).symm ≪≫
        ObjectProperty.isoMk _ e₀
    have eLin : (linearSpec X).obj ((dualAsQuasicoherentOp X).obj E) ≅ V.obj :=
      (linearSpec X).mapIso (Iso.op eDual.symm) ≪≫ linearSpecDegreeOneIso V.obj
    exact ⟨E, ⟨ObjectProperty.isoMk (isGeometricVectorBundle X) eLin⟩⟩

instance isEquivalenceTotalSpace (X : Scheme.{u}) : (totalSpace X).IsEquivalence where

/-- The equivalence of categories between finite locally free sheaves on `X` and geometric vector
bundles over `X`. -/
@[expose]
noncomputable def totalSpaceEquiv (X : Scheme.{u}) :
    FiniteLocallyFreeSheaf X ≌ GeometricVectorBundle X :=
  (totalSpace X).asEquivalence

/-- The forward functor of `totalSpaceEquiv X` is canonically `totalSpace X`. -/
@[expose]
noncomputable def totalSpaceEquivFunctorIso (X : Scheme.{u}) :
    (totalSpaceEquiv X).functor ≅ totalSpace X :=
  Iso.refl _

end

end TauCeti.AlgebraicGeometry
