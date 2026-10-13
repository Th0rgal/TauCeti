/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence

/-!
# Structured linear schemes and the linear-scheme anti-equivalence

For a scheme `X`, we define:
* `TauCeti.AlgebraicGeometry.linearSpecScheme X`: the underlying affine `X`-scheme functor
  `F ↦ Spec_X (Sym F)` on `(QuasicoherentSheaf X)ᵒᵖ`;
* `TauCeti.AlgebraicGeometry.QuasicoherentLinearScheme X`: structured linear `X`-schemes, packaging
  an affine `X`-scheme together with a free graded quasi-coherent coordinate algebra and an
  identification of its algebra of affine functions with the underlying ungraded algebra;
* `TauCeti.AlgebraicGeometry.gradedRelativeSpec X`,
  `TauCeti.AlgebraicGeometry.linearSchemeCoordinates X`, and
  `TauCeti.AlgebraicGeometry.gradedRelativeSpecEquiv X`: the equivalence between
  `(FreeGradedQuasicoherentAlgebra X)ᵒᵖ` and `QuasicoherentLinearScheme X`;
* `TauCeti.AlgebraicGeometry.linearSpec X`, `TauCeti.AlgebraicGeometry.degreeOne X`, and
  `TauCeti.AlgebraicGeometry.linearSpecEquiv X`: the anti-equivalence between quasi-coherent sheaves
  on `X` and structured linear `X`-schemes.
-/

public section

open CategoryTheory Category Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- The underlying affine `X`-scheme functor `F ↦ Spec_X (Sym F)` on `(QuasicoherentSheaf X)ᵒᵖ`. -/
@[expose]
noncomputable def linearSpecScheme (X : Scheme.{u}) :
    (QuasicoherentSheaf X)ᵒᵖ ⥤ AffineSchemeOver X :=
  (symmetricAlgebra X).op ⋙ relativeSpec X

/-- A structured linear scheme over `X`: an affine `X`-scheme equipped with a free graded
quasi-coherent coordinate algebra and an identification of its algebra of affine functions with the
underlying ungraded quasi-coherent algebra. -/
structure QuasicoherentLinearScheme (X : Scheme.{u}) where
  /-- The underlying affine scheme over `X`. -/
  toAffineSchemeOver : AffineSchemeOver X
  /-- The free graded quasi-coherent coordinate algebra. -/
  coordinateAlgebra : FreeGradedQuasicoherentAlgebra X
  /-- Identification of the algebra of affine functions with the underlying ungraded coordinate
  algebra. -/
  coordinateIso :
    (affineFunctions X).obj toAffineSchemeOver ≅
      op ((gradedAlgebraForget X).obj ((freeGradedAlgebraForget X).obj coordinateAlgebra))

namespace QuasicoherentLinearScheme

/-- A morphism of structured linear schemes over `X` consists of a morphism of underlying affine
`X`-schemes and a graded morphism of coordinate algebras in the opposite direction, compatible with
the coordinate identifications. -/
structure Hom {X : Scheme.{u}} (V W : QuasicoherentLinearScheme X) where
  /-- The morphism of underlying affine schemes over `X`. -/
  schemeHom : V.toAffineSchemeOver ⟶ W.toAffineSchemeOver
  /-- The graded morphism of free graded quasi-coherent coordinate algebras. -/
  coordinateHom : W.coordinateAlgebra ⟶ V.coordinateAlgebra
  /-- Compatibility of `schemeHom` and `coordinateHom` under `coordinateIso`. -/
  compatibility :
    (affineFunctions X).map schemeHom ≫ W.coordinateIso.hom =
      V.coordinateIso.hom ≫
        ((freeGradedAlgebraForget X ⋙ gradedAlgebraForget X).map coordinateHom).op

attribute [reassoc] Hom.compatibility

noncomputable instance instCategoryQuasicoherentLinearScheme (X : Scheme.{u}) :
    Category.{u} (QuasicoherentLinearScheme X) where
  Hom := Hom
  id V :=
    { schemeHom := 𝟙 V.toAffineSchemeOver
      coordinateHom := 𝟙 V.coordinateAlgebra
      compatibility := by simp }
  comp f g :=
    { schemeHom := f.schemeHom ≫ g.schemeHom
      coordinateHom := g.coordinateHom ≫ f.coordinateHom
      compatibility := by
        rw [Functor.map_comp, assoc, g.compatibility, ← assoc, f.compatibility, assoc, ← op_comp,
          ← Functor.map_comp] }
  id_comp f := by
    cases f
    simp
  comp_id f := by
    cases f
    simp
  assoc f g h := by
    cases f
    cases g
    cases h
    simp

@[ext]
theorem hom_ext {X : Scheme.{u}} {V W : QuasicoherentLinearScheme X} {f g : V ⟶ W}
    (hS : f.schemeHom = g.schemeHom) (hA : f.coordinateHom = g.coordinateHom) : f = g := by
  cases f
  cases g
  cases hS
  cases hA
  rfl

@[simp]
lemma id_schemeHom {X : Scheme.{u}} (V : QuasicoherentLinearScheme X) :
    (𝟙 V : V ⟶ V).schemeHom = 𝟙 V.toAffineSchemeOver :=
  rfl

@[simp]
lemma id_coordinateHom {X : Scheme.{u}} (V : QuasicoherentLinearScheme X) :
    (𝟙 V : V ⟶ V).coordinateHom = 𝟙 V.coordinateAlgebra :=
  rfl

@[simp, reassoc]
lemma comp_schemeHom {X : Scheme.{u}} {U V W : QuasicoherentLinearScheme X}
    (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).schemeHom = f.schemeHom ≫ g.schemeHom :=
  rfl

@[simp, reassoc]
lemma comp_coordinateHom {X : Scheme.{u}} {U V W : QuasicoherentLinearScheme X}
    (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).coordinateHom = g.coordinateHom ≫ f.coordinateHom :=
  rfl

end QuasicoherentLinearScheme

/-- The forgetful functor from structured linear `X`-schemes to affine `X`-schemes. -/
@[expose]
noncomputable def linearSchemeForget (X : Scheme.{u}) :
    QuasicoherentLinearScheme X ⥤ AffineSchemeOver X where
  obj V := V.toAffineSchemeOver
  map f := f.schemeHom

@[simp]
theorem linearSchemeForget_map {X : Scheme.{u}} {V W : QuasicoherentLinearScheme X}
    (f : V ⟶ W) : (linearSchemeForget X).map f = f.schemeHom :=
  rfl

/-- The graded relative spectrum functor from `(FreeGradedQuasicoherentAlgebra X)ᵒᵖ` to
`QuasicoherentLinearScheme X`. -/
@[expose]
noncomputable def gradedRelativeSpec (X : Scheme.{u}) :
    (FreeGradedQuasicoherentAlgebra X)ᵒᵖ ⥤ QuasicoherentLinearScheme X where
  obj A :=
    { toAffineSchemeOver :=
        (relativeSpec X).obj
          (op ((gradedAlgebraForget X).obj ((freeGradedAlgebraForget X).obj A.unop)))
      coordinateAlgebra := A.unop
      coordinateIso :=
        ((relativeSpecUnit X).app
          (op ((gradedAlgebraForget X).obj ((freeGradedAlgebraForget X).obj A.unop)))).symm }
  map f :=
    { schemeHom :=
        (relativeSpec X).map
          ((freeGradedAlgebraForget X ⋙ gradedAlgebraForget X).map f.unop).op
      coordinateHom := f.unop
      compatibility :=
        (relativeSpecUnit X).inv.naturality
          ((freeGradedAlgebraForget X ⋙ gradedAlgebraForget X).map f.unop).op }
  map_id A := by
    refine QuasicoherentLinearScheme.hom_ext ?_ rfl
    dsimp
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, op_id,
      CategoryTheory.Functor.map_id]
  map_comp f g := by
    refine QuasicoherentLinearScheme.hom_ext ?_ rfl
    dsimp
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, op_comp,
      CategoryTheory.Functor.map_comp]

/-- The coordinate-algebra functor from structured linear `X`-schemes to
`(FreeGradedQuasicoherentAlgebra X)ᵒᵖ`. -/
@[expose]
noncomputable def linearSchemeCoordinates (X : Scheme.{u}) :
    QuasicoherentLinearScheme X ⥤ (FreeGradedQuasicoherentAlgebra X)ᵒᵖ where
  obj V := op V.coordinateAlgebra
  map f := f.coordinateHom.op

@[simp]
theorem linearSchemeCoordinates_map {X : Scheme.{u}} {V W : QuasicoherentLinearScheme X}
    (f : V ⟶ W) : (linearSchemeCoordinates X).map f = f.coordinateHom.op :=
  rfl

/-- The counit isomorphism `linearSchemeCoordinates X ⋙ gradedRelativeSpec X ≅ 𝟭 _` for structured
linear `X`-schemes. -/
@[expose]
noncomputable def gradedRelativeSpecCounitIso (X : Scheme.{u}) :
    linearSchemeCoordinates X ⋙ gradedRelativeSpec X ≅ 𝟭 (QuasicoherentLinearScheme X) :=
  NatIso.ofComponents
    (fun V ↦
      let B : (QuasicoherentAlgebra X)ᵒᵖ :=
        op ((gradedAlgebraForget X).obj ((freeGradedAlgebraForget X).obj V.coordinateAlgebra))
      let eV : (relativeSpec X).obj B ≅ V.toAffineSchemeOver :=
        ((relativeSpec X).mapIso V.coordinateIso).symm ≪≫
          (relativeSpecCounit X).app V.toAffineSchemeOver
      have hcomp : (affineFunctions X).map eV.hom ≫ V.coordinateIso.hom =
          (relativeSpecUnit X).inv.app B := by
        dsimp [eV]
        rw [Functor.map_comp, assoc]
        have htri : (affineFunctions X).map ((relativeSpecCounit X).hom.app V.toAffineSchemeOver) =
            (relativeSpecUnit X).inv.app ((affineFunctions X).obj V.toAffineSchemeOver) := by
          rw [← cancel_epi ((relativeSpecUnit X).hom.app
            ((affineFunctions X).obj V.toAffineSchemeOver)),
            relativeSpecUnit_hom_app_comp_affineFunctions_map_relativeSpecCounit_hom_app,
            Iso.hom_inv_id_app]
          rfl
        have hnat := (relativeSpecUnit X).inv.naturality V.coordinateIso.inv
        rw [reassoc_of% htri, reassoc_of% hnat, Iso.inv_hom_id, comp_id]
      { hom :=
          { schemeHom := eV.hom
            coordinateHom := 𝟙 V.coordinateAlgebra
            compatibility := by
              dsimp [gradedRelativeSpec, linearSchemeCoordinates]
              rw [hcomp, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, op_id,
                comp_id] }
        inv :=
          { schemeHom := eV.inv
            coordinateHom := 𝟙 V.coordinateAlgebra
            compatibility := by
              dsimp [gradedRelativeSpec, linearSchemeCoordinates]
              rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, op_id, comp_id,
                ← hcomp, ← Functor.map_comp_assoc, eV.inv_hom_id,
                CategoryTheory.Functor.map_id, id_comp] }
        hom_inv_id := QuasicoherentLinearScheme.hom_ext eV.hom_inv_id (comp_id _)
        inv_hom_id := QuasicoherentLinearScheme.hom_ext eV.inv_hom_id (comp_id _) })
    (fun {V W} f ↦ by
      refine QuasicoherentLinearScheme.hom_ext ?_ ?_
      · dsimp [gradedRelativeSpec, linearSchemeCoordinates]
        have hf :
            ((gradedAlgebraForget X).map ((freeGradedAlgebraForget X).map f.coordinateHom)).op ≫
              W.coordinateIso.inv =
              V.coordinateIso.inv ≫ (affineFunctions X).map f.schemeHom := by
          rw [← cancel_epi V.coordinateIso.hom, ← cancel_mono W.coordinateIso.hom, assoc, assoc,
            W.coordinateIso.inv_hom_id, comp_id, V.coordinateIso.hom_inv_id_assoc]
          exact f.compatibility.symm
        have hnat : (relativeSpec X).map ((affineFunctions X).map f.schemeHom) ≫
            (relativeSpecCounit X).hom.app W.toAffineSchemeOver =
            (relativeSpecCounit X).hom.app V.toAffineSchemeOver ≫ f.schemeHom :=
          (relativeSpecCounit X).hom.naturality f.schemeHom
        rw [← (relativeSpec X).map_comp_assoc, hf, (relativeSpec X).map_comp_assoc, hnat, assoc]
      · dsimp [gradedRelativeSpec, linearSchemeCoordinates]
        rw [comp_id, id_comp])

/-- The equivalence of categories between `(FreeGradedQuasicoherentAlgebra X)ᵒᵖ` and
`QuasicoherentLinearScheme X`. -/
@[expose]
noncomputable def gradedRelativeSpecEquiv (X : Scheme.{u}) :
    (FreeGradedQuasicoherentAlgebra X)ᵒᵖ ≌ QuasicoherentLinearScheme X where
  functor := gradedRelativeSpec X
  inverse := linearSchemeCoordinates X
  unitIso := Iso.refl _
  counitIso := gradedRelativeSpecCounitIso X
  functor_unitIso_comp A := by
    refine QuasicoherentLinearScheme.hom_ext ?_ (comp_id _)
    dsimp [gradedRelativeSpec, gradedRelativeSpecCounitIso, linearSchemeCoordinates]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, op_id,
      (relativeSpec X).map_id, id_comp]
    exact relativeSpec_map_relativeSpecUnit_hom_app_comp_relativeSpecCounit_hom_app
      (op ((gradedAlgebraForget X).obj ((freeGradedAlgebraForget X).obj A.unop)))

/-- The forward functor of `gradedRelativeSpecEquiv X` is canonically `gradedRelativeSpec X`. -/
@[expose]
noncomputable def gradedRelativeSpecEquivFunctorIso (X : Scheme.{u}) :
    (gradedRelativeSpecEquiv X).functor ≅ gradedRelativeSpec X :=
  Iso.refl _

/-- Forgetting the graded coordinate data after `gradedRelativeSpec X` recovers `relativeSpec X`
on the underlying ungraded quasi-coherent algebra. -/
@[expose]
noncomputable def gradedRelativeSpecForgetIso (X : Scheme.{u}) :
    gradedRelativeSpec X ⋙ linearSchemeForget X ≅
      (freeGradedAlgebraForget X ⋙ gradedAlgebraForget X).op ⋙ relativeSpec X :=
  Iso.refl _

/-- The structured linear spectrum functor `F ↦ Spec_X (Sym^* F)` from `(QuasicoherentSheaf X)ᵒᵖ`
to `QuasicoherentLinearScheme X`. -/
@[expose]
noncomputable def linearSpec (X : Scheme.{u}) :
    (QuasicoherentSheaf X)ᵒᵖ ⥤ QuasicoherentLinearScheme X :=
  (gradedSymmetricAlgebraFree X).op ⋙ gradedRelativeSpec X

/-- Forgetting the graded coordinate structure on `linearSpec X` recovers `linearSpecScheme X`. -/
@[expose]
noncomputable def linearSpecForgetIso (X : Scheme.{u}) :
    linearSpec X ⋙ linearSchemeForget X ≅ linearSpecScheme X :=
  Iso.refl _

/-- The degree-`1` coordinate-sheaf functor from `QuasicoherentLinearScheme X` to
`(QuasicoherentSheaf X)ᵒᵖ`. -/
@[expose]
noncomputable def degreeOne (X : Scheme.{u}) :
    QuasicoherentLinearScheme X ⥤ (QuasicoherentSheaf X)ᵒᵖ :=
  linearSchemeCoordinates X ⋙ (freeGradedAlgebraForget X ⋙ gradedAlgebraDegreeOne X).op

/-- A structured linear scheme over `X` is canonically isomorphic to the linear spectrum of its
degree-`1` coordinate sheaf. -/
@[expose]
noncomputable def linearSpecDegreeOneIso {X : Scheme.{u}} (V : QuasicoherentLinearScheme X) :
    (linearSpec X).obj ((degreeOne X).obj V) ≅ V :=
  (gradedRelativeSpec X).mapIso (freeGradedAlgebraDegreeOneIso V.coordinateAlgebra).symm.op ≪≫
    (gradedRelativeSpecCounitIso X).app V

/-- The degree-`1` coordinate sheaf of `linearSpec X` of `F` is canonically isomorphic to `F`. -/
@[expose]
noncomputable def degreeOneLinearSpecIso {X : Scheme.{u}} (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (degreeOne X).obj ((linearSpec X).obj F) ≅ F :=
  (gradedSymmetricAlgebraDegreeOneIso F.unop).symm.op

/-- The anti-equivalence of categories between quasi-coherent sheaves on `X` and structured linear
`X`-schemes. -/
@[expose]
noncomputable def linearSpecEquiv (X : Scheme.{u}) :
    (QuasicoherentSheaf X)ᵒᵖ ≌ QuasicoherentLinearScheme X :=
  (gradedSymmetricAlgebraEquiv X).op.trans (gradedRelativeSpecEquiv X)

/-- The forward functor of `linearSpecEquiv X` is canonically `linearSpec X`. -/
@[expose]
noncomputable def linearSpecEquivFunctorIso (X : Scheme.{u}) :
    (linearSpecEquiv X).functor ≅ linearSpec X :=
  Iso.refl _

end

end TauCeti.AlgebraicGeometry
