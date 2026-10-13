/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.Functoriality
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Identity
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor

/-!
# Pullback of quasi-coherent commutative algebras

Pullback of sheaves of modules along a scheme morphism `f : Y ⟶ X` is strong symmetric monoidal on
quasi-coherent sheaves (`AlgebraicGeometry.Scheme.Modules.pullbackToModulesBraided`), and preserves
quasi-coherence (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`). It therefore induces
a pullback functor on quasi-coherent commutative algebras

`pullbackQuasicoherentAlgebra f : QuasicoherentAlgebra X ⥤ QuasicoherentAlgebra Y`

whose underlying module on `A` is literally `(Scheme.Modules.pullback f).obj A.obj.X`.

Because the module pullback--pushforward adjunction is monoidal
(`AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackPushforwardAdjunction`), morphisms of
commutative algebras out of `(pullbackQuasicoherentAlgebra f).obj A` into any commutative
`𝒪_Y`-algebra `B` correspond bijectively to morphisms of `𝒪_X`-algebras `A.obj ⟶ f_* B`
(`pullbackPushforwardCommMonHomEquiv`). In particular, morphisms into the structure-sheaf algebra
`structureSheafAlgebra Y` correspond bijectively to morphisms
`A.obj ⟶ f.pushforwardStructureAlgebra` (`pullbackStructureSheafAlgebraHomEquiv`), compatibly with
composition of scheme morphisms.

## Main declarations

* `TauCeti.AlgebraicGeometry.structureSheafAlgebra`: the structure sheaf `𝒪_X` as a quasi-coherent
  commutative `𝒪_X`-algebra;
* `TauCeti.AlgebraicGeometry.pullbackQuasicoherentAlgebra`: pullback of quasi-coherent commutative
  algebras along `f : Y ⟶ X`;
* `TauCeti.AlgebraicGeometry.pullbackQuasicoherentAlgebraIdIso`,
  `TauCeti.AlgebraicGeometry.pullbackQuasicoherentAlgebraCompIso`,
  `TauCeti.AlgebraicGeometry.pullbackAlgebraCompOverIso`, and
  `TauCeti.AlgebraicGeometry.pullbackStructureSheafAlgebraIso`: identity, composition, and
  structure-sheaf coherence isomorphisms for algebra pullback;
* `TauCeti.AlgebraicGeometry.pullbackPushforwardCommMonHomEquiv` and
  `TauCeti.AlgebraicGeometry.pullbackStructureSheafAlgebraHomEquiv`: the adjunction bijections for
  pulled-back quasi-coherent algebras.
-/

public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- The structure sheaf `𝒪_X` as a quasi-coherent commutative `𝒪_X`-algebra. -/
@[expose]
def structureSheafAlgebra (X : Scheme.{u}) : QuasicoherentAlgebra X :=
  ⟨CommMon.trivial X.Modules, isQuasicoherent_unit X⟩

@[simp]
lemma structureSheafAlgebra_obj (X : Scheme.{u}) :
    (structureSheafAlgebra X).obj = CommMon.trivial X.Modules :=
  (rfl)

lemma structureSheafAlgebra_obj_X (X : Scheme.{u}) :
    (structureSheafAlgebra X).obj.X = 𝟙_ X.Modules :=
  (rfl)

/-- View a quasi-coherent commutative `𝒪_X`-algebra as a commutative monoid object in the full
monoidal subcategory `QuasicoherentSheaf X`. -/
@[expose]
def toCommMonQuasicoherentSheaf (X : Scheme.{u}) :
    QuasicoherentAlgebra X ⥤ CommMon (QuasicoherentSheaf X) where
  obj A :=
    let E : QuasicoherentSheaf X := ⟨A.obj.X, A.property⟩
    letI : MonObj E :=
      { one := ObjectProperty.homMk η[A.obj.X]
        mul := ObjectProperty.homMk μ[A.obj.X]
        one_mul := ObjectProperty.hom_ext _ (MonObj.one_mul (X := A.obj.X))
        mul_one := ObjectProperty.hom_ext _ (MonObj.mul_one (X := A.obj.X))
        mul_assoc := ObjectProperty.hom_ext _ (MonObj.mul_assoc (X := A.obj.X)) }
    letI : IsCommMonObj E :=
      { mul_comm := ObjectProperty.hom_ext _ (IsCommMonObj.mul_comm (X := A.obj.X)) }
    CommMon.mk E
  map {A B} a :=
    let E : QuasicoherentSheaf X := ⟨A.obj.X, A.property⟩
    let F : QuasicoherentSheaf X := ⟨B.obj.X, B.property⟩
    letI : MonObj E :=
      { one := ObjectProperty.homMk η[A.obj.X]
        mul := ObjectProperty.homMk μ[A.obj.X]
        one_mul := ObjectProperty.hom_ext _ (MonObj.one_mul (X := A.obj.X))
        mul_one := ObjectProperty.hom_ext _ (MonObj.mul_one (X := A.obj.X))
        mul_assoc := ObjectProperty.hom_ext _ (MonObj.mul_assoc (X := A.obj.X)) }
    letI : MonObj F :=
      { one := ObjectProperty.homMk η[B.obj.X]
        mul := ObjectProperty.homMk μ[B.obj.X]
        one_mul := ObjectProperty.hom_ext _ (MonObj.one_mul (X := B.obj.X))
        mul_one := ObjectProperty.hom_ext _ (MonObj.mul_one (X := B.obj.X))
        mul_assoc := ObjectProperty.hom_ext _ (MonObj.mul_assoc (X := B.obj.X)) }
    CommMon.homMk
      { hom := (ObjectProperty.homMk a.hom.hom.hom : E ⟶ F)
        isMonHom_hom :=
          { one_hom := ObjectProperty.hom_ext _ (IsMonHom.one_hom (f := a.hom.hom.hom))
            mul_hom := ObjectProperty.hom_ext _ (IsMonHom.mul_hom (f := a.hom.hom.hom)) } }

/-- Pullback of quasi-coherent commutative algebras along a morphism of schemes `f : Y ⟶ X`.
Its underlying module on `A` is definitionally `(Scheme.Modules.pullback f).obj A.obj.X`. -/
@[expose]
def pullbackQuasicoherentAlgebra {X Y : Scheme.{u}} (f : Y ⟶ X) :
    QuasicoherentAlgebra X ⥤ QuasicoherentAlgebra Y where
  obj A :=
    ⟨((ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules) ⋙
        Scheme.Modules.pullback f).mapCommMon.obj ((toCommMonQuasicoherentSheaf X).obj A),
      Scheme.Modules.isQuasicoherent_pullback f A.obj.X⟩
  map a := ObjectProperty.homMk
    (((ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules) ⋙
      Scheme.Modules.pullback f).mapCommMon.map ((toCommMonQuasicoherentSheaf X).map a))
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    exact (Scheme.Modules.pullback f).map_id _
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    exact (Scheme.Modules.pullback f).map_comp _ _

@[simp]
lemma pullbackQuasicoherentAlgebra_obj_obj_X {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) :
    ((pullbackQuasicoherentAlgebra f).obj A).obj.X = (Scheme.Modules.pullback f).obj A.obj.X :=
  (rfl)

@[simp]
lemma pullbackQuasicoherentAlgebra_map_hom_hom_hom {X Y : Scheme.{u}} (f : Y ⟶ X)
    {A B : QuasicoherentAlgebra X} (a : A ⟶ B) :
    ((pullbackQuasicoherentAlgebra f).map a).hom.hom.hom =
      (Scheme.Modules.pullback f).map a.hom.hom.hom :=
  (rfl)

lemma pullbackQuasicoherentAlgebra_obj_one {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) :
    η[((pullbackQuasicoherentAlgebra f).obj A).obj.X] =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map η[A.obj.X] := by
  let F := (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules) ⋙ Scheme.Modules.pullback f
  have hε : Functor.LaxMonoidal.ε F = (Scheme.Modules.pullbackObjUnitIso f).inv := by
    rw [← cancel_mono (Functor.OplaxMonoidal.η F), Functor.Monoidal.ε_η,
      Scheme.Modules.pullbackToModules_η, Iso.inv_hom_id]
  exact congrArg (· ≫ (Scheme.Modules.pullback f).map η[A.obj.X]) hε

lemma pullbackQuasicoherentAlgebra_obj_mul {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) :
    μ[((pullbackQuasicoherentAlgebra f).obj A).obj.X] =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) ≫
        (Scheme.Modules.pullback f).map μ[A.obj.X] := by
  let F := (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules) ⋙ Scheme.Modules.pullback f
  let E : QuasicoherentSheaf X := ⟨A.obj.X, A.property⟩
  have hμ : Functor.LaxMonoidal.μ F E E =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ F E E), Functor.Monoidal.δ_μ,
      Scheme.Modules.pullbackToModules_δ, IsIso.hom_inv_id]
  exact congrArg (· ≫ (Scheme.Modules.pullback f).map μ[A.obj.X]) hμ

/-- Construct an isomorphism in `QuasicoherentAlgebra X` from a module isomorphism compatible with
unit and multiplication. -/
@[expose]
def QuasicoherentAlgebra.isoMk {X : Scheme.{u}} {A B : QuasicoherentAlgebra X}
    (e : A.obj.X ≅ B.obj.X)
    (one_f : η[A.obj.X] ≫ e.hom = η[B.obj.X])
    (mul_f : μ[A.obj.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[B.obj.X]) : A ≅ B :=
  ObjectProperty.isoMk _ (CommMon.mkIso e one_f mul_f)

@[simp]
lemma QuasicoherentAlgebra.isoMk_hom_hom_hom_hom {X : Scheme.{u}}
    {A B : QuasicoherentAlgebra X} (e : A.obj.X ≅ B.obj.X)
    (one_f : η[A.obj.X] ≫ e.hom = η[B.obj.X])
    (mul_f : μ[A.obj.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[B.obj.X]) :
    (QuasicoherentAlgebra.isoMk e one_f mul_f).hom.hom.hom.hom = e.hom :=
  (rfl)

@[simp]
lemma QuasicoherentAlgebra.isoMk_inv_hom_hom_hom {X : Scheme.{u}}
    {A B : QuasicoherentAlgebra X} (e : A.obj.X ≅ B.obj.X)
    (one_f : η[A.obj.X] ≫ e.hom = η[B.obj.X])
    (mul_f : μ[A.obj.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[B.obj.X]) :
    (QuasicoherentAlgebra.isoMk e one_f mul_f).inv.hom.hom.hom = e.inv :=
  (rfl)

/-- Pullback of the structure-sheaf algebra along `f : Y ⟶ X` is canonically isomorphic to the
structure-sheaf algebra on `Y`. -/
@[expose]
def pullbackStructureSheafAlgebraIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackQuasicoherentAlgebra f).obj (structureSheafAlgebra X) ≅ structureSheafAlgebra Y :=
  QuasicoherentAlgebra.isoMk (Scheme.Modules.pullbackObjUnitIso f)
    (by
      rw [pullbackQuasicoherentAlgebra_obj_one]
      change ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (𝟙 (𝟙_ X.Modules))) ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom = 𝟙 (𝟙_ Y.Modules)
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id])
    (by
      rw [pullbackQuasicoherentAlgebra_obj_mul]
      change (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f)
            (𝟙_ X.Modules) (𝟙_ X.Modules)) ≫
          (Scheme.Modules.pullback f).map (λ_ (𝟙_ X.Modules)).hom) ≫
          (Scheme.Modules.pullbackObjUnitIso f).hom =
        ((Scheme.Modules.pullbackObjUnitIso f).hom ⊗ₘ
          (Scheme.Modules.pullbackObjUnitIso f).hom) ≫ (λ_ (𝟙_ Y.Modules)).hom
      rw [Category.assoc, IsIso.inv_comp_eq]
      have h := (Functor.OplaxMonoidal.left_unitality (Scheme.Modules.pullback f)
        (𝟙_ X.Modules)).symm
      rw [Scheme.Modules.pullback_η] at h
      have h1 : (Scheme.Modules.pullback f).map (λ_ (𝟙_ X.Modules)).hom =
          Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) (𝟙_ X.Modules) (𝟙_ X.Modules) ≫
            ((Scheme.Modules.pullbackObjUnitIso f).hom ▷
              (Scheme.Modules.pullback f).obj (𝟙_ X.Modules)) ≫
            (λ_ ((Scheme.Modules.pullback f).obj (𝟙_ X.Modules))).hom := by
        rw [← cancel_epi ((Scheme.Modules.pullback f).map (λ_ (𝟙_ X.Modules)).inv),
          ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
          reassoc_of% h, Iso.inv_hom_id]
      rw [h1, Category.assoc, Category.assoc, ← leftUnitor_naturality, ← tensorHom_def_assoc])

/-- On underlying modules, `pullbackStructureSheafAlgebraIso` is the structure-sheaf pullback
comparison `pullbackObjUnitIso`. -/
@[simp]
theorem pullbackStructureSheafAlgebraIso_underlying {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackStructureSheafAlgebraIso f).hom.hom.hom.hom =
      (Scheme.Modules.pullbackObjUnitIso f).hom :=
  (rfl)

@[simp]
theorem pullbackStructureSheafAlgebraIso_inv_underlying {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackStructureSheafAlgebraIso f).inv.hom.hom.hom =
      (Scheme.Modules.pullbackObjUnitIso f).inv :=
  (rfl)

lemma pullbackId_one_hom (X : Scheme.{u}) (M : X.Modules) [MonObj M] :
    ((Scheme.Modules.pullbackObjUnitIso (𝟙 X)).inv ≫
        (Scheme.Modules.pullback (𝟙 X)).map η[M]) ≫
      ((Scheme.Modules.pullbackId X).app M).hom = η[M] := by
  rw [Category.assoc]
  erw [(Scheme.Modules.pullbackId X).hom.naturality η[M]]
  rw [CategoryTheory.Functor.id_map, ← Category.assoc,
    ← Scheme.Modules.pullbackObjUnitIso_id, Iso.inv_hom_id, Category.id_comp]

lemma pullbackId_mul_hom (X : Scheme.{u}) (M : X.Modules) [MonObj M]
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (𝟙 X)) M M)] :
    (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (𝟙 X)) M M) ≫
        (Scheme.Modules.pullback (𝟙 X)).map μ[M]) ≫
      ((Scheme.Modules.pullbackId X).app M).hom =
    (((Scheme.Modules.pullbackId X).app M).hom ⊗ₘ
      ((Scheme.Modules.pullbackId X).app M).hom) ≫ μ[M] := by
  rw [Category.assoc]
  erw [(Scheme.Modules.pullbackId X).hom.naturality μ[M]]
  rw [CategoryTheory.Functor.id_map, ← Category.assoc, ← Scheme.Modules.pullback_id_δ,
    IsIso.inv_hom_id_assoc]
  rfl

/-- Pullback of quasi-coherent algebras along the identity morphism is naturally isomorphic to the
identity functor. -/
@[expose]
def pullbackQuasicoherentAlgebraIdIso (X : Scheme.{u}) :
    pullbackQuasicoherentAlgebra (𝟙 X) ≅ 𝟭 (QuasicoherentAlgebra X) :=
  NatIso.ofComponents
    (fun A ↦ QuasicoherentAlgebra.isoMk ((Scheme.Modules.pullbackId X).app A.obj.X)
      ((congrArg (· ≫ ((Scheme.Modules.pullbackId X).app A.obj.X).hom)
        (pullbackQuasicoherentAlgebra_obj_one (𝟙 X) A)).trans (pullbackId_one_hom X A.obj.X))
      ((congrArg (· ≫ ((Scheme.Modules.pullbackId X).app A.obj.X).hom)
        (pullbackQuasicoherentAlgebra_obj_mul (𝟙 X) A)).trans (pullbackId_mul_hom X A.obj.X)))
    (by
      intro A B a
      apply ObjectProperty.hom_ext
      apply CommMon.hom_ext
      exact (Scheme.Modules.pullbackId X).hom.naturality a.hom.hom.hom)

@[simp]
lemma pullbackQuasicoherentAlgebraIdIso_hom_app_underlying (X : Scheme.{u})
    (A : QuasicoherentAlgebra X) :
    ((pullbackQuasicoherentAlgebraIdIso X).hom.app A).hom.hom.hom =
      (Scheme.Modules.pullbackId X).hom.app A.obj.X :=
  (rfl)

@[simp]
lemma pullbackQuasicoherentAlgebraIdIso_inv_app_underlying (X : Scheme.{u})
    (A : QuasicoherentAlgebra X) :
    ((pullbackQuasicoherentAlgebraIdIso X).inv.app A).hom.hom.hom =
      (Scheme.Modules.pullbackId X).inv.app A.obj.X :=
  (rfl)

lemma pullbackComp_one_hom {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (M : X.Modules) [MonObj M] :
    ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackObjUnitIso g).inv ≫ (Scheme.Modules.pullback g).map η[M])) ≫
      ((Scheme.Modules.pullbackComp f g).app M).hom =
    (Scheme.Modules.pullbackObjUnitIso (f ≫ g)).inv ≫
      (Scheme.Modules.pullback (f ≫ g)).map η[M] := by
  rw [CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]
  erw [(Scheme.Modules.pullbackComp f g).hom.naturality η[M]]
  rw [← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ (Scheme.Modules.pullback (f ≫ g)).map η[M]) ?_
  rw [← cancel_mono (Scheme.Modules.pullbackObjUnitIso (f ≫ g)).hom,
    Iso.inv_hom_id, ← Scheme.Modules.pullbackObjUnitIso_comp f g,
    Category.assoc, Iso.hom_inv_id_app_assoc,
    Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

lemma pullbackComp_mul_hom {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (M : X.Modules) [MonObj M]
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) M M)]
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f)
      ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj M))]
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (f ≫ g)) M M)] :
    (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f)
          ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj M)) ≫
        (Scheme.Modules.pullback f).map
          (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) M M) ≫
            (Scheme.Modules.pullback g).map μ[M])) ≫
      ((Scheme.Modules.pullbackComp f g).app M).hom =
    (((Scheme.Modules.pullbackComp f g).app M).hom ⊗ₘ
      ((Scheme.Modules.pullbackComp f g).app M).hom) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (f ≫ g)) M M) ≫
        (Scheme.Modules.pullback (f ≫ g)).map μ[M] := by
  rw [CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]
  erw [(Scheme.Modules.pullbackComp f g).hom.naturality μ[M]]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ (Scheme.Modules.pullback (f ≫ g)).map μ[M]) ?_
  rw [← cancel_mono (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (f ≫ g)) M M)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [pullbackComp_hom_app_comp_δ, ← CategoryTheory.Functor.map_comp_assoc,
    IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    IsIso.inv_hom_id_assoc]
  rfl

/-- Pullback of quasi-coherent algebras respects composition of scheme morphisms. -/
@[expose]
def pullbackQuasicoherentAlgebraCompIso {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) :
    pullbackQuasicoherentAlgebra g ⋙ pullbackQuasicoherentAlgebra f ≅
      pullbackQuasicoherentAlgebra (f ≫ g) :=
  NatIso.ofComponents
    (fun A ↦ QuasicoherentAlgebra.isoMk ((Scheme.Modules.pullbackComp f g).app A.obj.X)
      (by
        have h1 := pullbackQuasicoherentAlgebra_obj_one f ((pullbackQuasicoherentAlgebra g).obj A)
        have h2 := pullbackQuasicoherentAlgebra_obj_one g A
        have h3 := pullbackQuasicoherentAlgebra_obj_one (f ≫ g) A
        exact (congrArg (· ≫ ((Scheme.Modules.pullbackComp f g).app A.obj.X).hom)
          (h1.trans (congrArg ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
            (Scheme.Modules.pullback f).map ·) h2))).trans
          ((pullbackComp_one_hom f g A.obj.X).trans h3.symm))
      (by
        have h1 := pullbackQuasicoherentAlgebra_obj_mul f ((pullbackQuasicoherentAlgebra g).obj A)
        have h2 := pullbackQuasicoherentAlgebra_obj_mul g A
        have h3 := pullbackQuasicoherentAlgebra_obj_mul (f ≫ g) A
        exact (congrArg (· ≫ ((Scheme.Modules.pullbackComp f g).app A.obj.X).hom)
          (h1.trans (congrArg (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) _ _) ≫
            (Scheme.Modules.pullback f).map ·) h2))).trans
          ((pullbackComp_mul_hom f g A.obj.X).trans
            (congrArg ((((Scheme.Modules.pullbackComp f g).app A.obj.X).hom ⊗ₘ
              ((Scheme.Modules.pullbackComp f g).app A.obj.X).hom) ≫ ·) h3.symm))))
    (by
      intro A B a
      apply ObjectProperty.hom_ext
      apply CommMon.hom_ext
      exact (Scheme.Modules.pullbackComp f g).hom.naturality a.hom.hom.hom)

@[simp]
lemma pullbackQuasicoherentAlgebraCompIso_hom_app_underlying {X Y Z : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    ((pullbackQuasicoherentAlgebraCompIso f g).hom.app A).hom.hom.hom =
      (Scheme.Modules.pullbackComp f g).hom.app A.obj.X :=
  (rfl)

@[simp]
lemma pullbackQuasicoherentAlgebraCompIso_inv_app_underlying {X Y Z : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    ((pullbackQuasicoherentAlgebraCompIso f g).inv.app A).hom.hom.hom =
      (Scheme.Modules.pullbackComp f g).inv.app A.obj.X :=
  (rfl)

/-- Pullback of quasi-coherent algebras along equal scheme morphisms are canonically isomorphic. -/
@[expose]
def pullbackQuasicoherentAlgebraCongr {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    pullbackQuasicoherentAlgebra f ≅ pullbackQuasicoherentAlgebra g :=
  NatIso.ofComponents
    (fun A ↦ QuasicoherentAlgebra.isoMk ((Scheme.Modules.pullbackCongr h).app A.obj.X)
      (by
        subst h
        exact Category.comp_id _)
      (by
        subst h
        exact (Category.comp_id _).trans
          ((Category.id_comp _).symm.trans
            (congrArg (· ≫ _) (MonoidalCategory.id_tensorHom_id _ _).symm))))
    (by
      intro A B a
      apply ObjectProperty.hom_ext
      apply CommMon.hom_ext
      exact (Scheme.Modules.pullbackCongr h).hom.naturality a.hom.hom.hom)

@[simp]
lemma pullbackQuasicoherentAlgebraCongr_hom_app_underlying {X Y : Scheme.{u}} {f g : Y ⟶ X}
    (h : f = g) (A : QuasicoherentAlgebra X) :
    ((pullbackQuasicoherentAlgebraCongr h).hom.app A).hom.hom.hom =
      (Scheme.Modules.pullbackCongr h).hom.app A.obj.X :=
  (rfl)

@[simp]
lemma pullbackQuasicoherentAlgebraCongr_inv_app_underlying {X Y : Scheme.{u}} {f g : Y ⟶ X}
    (h : f = g) (A : QuasicoherentAlgebra X) :
    ((pullbackQuasicoherentAlgebraCongr h).inv.app A).hom.hom.hom =
      (Scheme.Modules.pullbackCongr h).inv.app A.obj.X :=
  (rfl)

/-- Algebra pullback composition along a morphism `g : T' ⟶ T` in `Over X`, lifting the module
comparison `pullbackComp g.left T.hom ≪≫ pullbackCongr g.w`. -/
@[expose]
def pullbackAlgebraCompOverIso {X : Scheme.{u}} {T T' : Over X}
    (g : T' ⟶ T) (A : QuasicoherentAlgebra X) :
    (pullbackQuasicoherentAlgebra g.left).obj ((pullbackQuasicoherentAlgebra T.hom).obj A) ≅
      (pullbackQuasicoherentAlgebra T'.hom).obj A :=
  (pullbackQuasicoherentAlgebraCompIso g.left T.hom).app A ≪≫
    (pullbackQuasicoherentAlgebraCongr g.w).app A

/-- On underlying modules, `pullbackAlgebraCompOverIso` is the composite of `pullbackComp` and
`pullbackCongr`. -/
@[simp]
theorem pullbackAlgebraCompOverIso_underlying {X : Scheme.{u}} {T T' : Over X}
    (g : T' ⟶ T) (A : QuasicoherentAlgebra X) :
    (pullbackAlgebraCompOverIso g A).hom.hom.hom.hom =
      (Scheme.Modules.pullbackComp g.left T.hom).hom.app A.obj.X ≫
        (Scheme.Modules.pullbackCongr g.w).hom.app A.obj.X :=
  (rfl)

@[simp]
theorem pullbackAlgebraCompOverIso_inv_underlying {X : Scheme.{u}} {T T' : Over X}
    (g : T' ⟶ T) (A : QuasicoherentAlgebra X) :
    (pullbackAlgebraCompOverIso g A).inv.hom.hom.hom =
      (Scheme.Modules.pullbackCongr g.w).inv.app A.obj.X ≫
        (Scheme.Modules.pullbackComp g.left T.hom).inv.app A.obj.X :=
  (rfl)

/-- For a monoidal adjunction `L ⊣ R` where `L` has invertible oplax unit and tensor comparison on
a monoid object `M`, a morphism `L.obj M ⟶ N.X` respects the pulled-back unit and multiplication if
and only if its adjunct `M ⟶ R.obj N.X` is a monoid homomorphism. -/
theorem isMonHom_homEquiv_iff_of_adjunction {C D : Type*} [Category C] [MonoidalCategory C]
    [Category D] [MonoidalCategory D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.OplaxMonoidal] [R.LaxMonoidal] [adj.IsMonoidal]
    (M : C) [MonObj M] [IsIso (Functor.OplaxMonoidal.η L)]
    [IsIso (Functor.OplaxMonoidal.δ L M M)] (N : Mon D) (φ : L.obj M ⟶ N.X) :
    ((inv (Functor.OplaxMonoidal.η L) ≫ L.map η[M]) ≫ φ = η[N.X] ∧
      (inv (Functor.OplaxMonoidal.δ L M M) ≫ L.map μ[M]) ≫ φ = (φ ⊗ₘ φ) ≫ μ[N.X]) ↔
      @IsMonHom C _ _ M (R.mapMon.obj N).X _ (R.mapMon.obj N).mon
        ((adj.homEquiv M N.X) φ) := by
  let ψ := (adj.homEquiv M N.X) φ
  have hunit : (inv (Functor.OplaxMonoidal.η L) ≫ L.map η[M]) ≫ φ = η[N.X] ↔
      η[M] ≫ ψ = Functor.LaxMonoidal.ε R ≫ R.map η[N.X] := by
    rw [Category.assoc, IsIso.inv_comp_eq,
      ← (adj.homEquiv (𝟙_ C) N.X).apply_eq_iff_eq,
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    have hη : (adj.homEquiv (𝟙_ C) (𝟙_ D)) (Functor.OplaxMonoidal.η L) =
        Functor.LaxMonoidal.ε R := by
      rw [Adjunction.homEquiv_unit, adj.unit_app_unit_comp_map_η]
    rw [hη]
  have hmul : (inv (Functor.OplaxMonoidal.δ L M M) ≫ L.map μ[M]) ≫ φ = (φ ⊗ₘ φ) ≫ μ[N.X] ↔
      μ[M] ≫ ψ = (ψ ⊗ₘ ψ) ≫ Functor.LaxMonoidal.μ R N.X N.X ≫ R.map μ[N.X] := by
    rw [Category.assoc, IsIso.inv_comp_eq,
      ← (adj.homEquiv (M ⊗ M) N.X).apply_eq_iff_eq,
      Adjunction.homEquiv_naturality_left]
    have hδ : (adj.homEquiv (M ⊗ M) N.X)
        (Functor.OplaxMonoidal.δ L M M ≫ (φ ⊗ₘ φ) ≫ μ[N.X]) =
        (ψ ⊗ₘ ψ) ≫ Functor.LaxMonoidal.μ R N.X N.X ≫ R.map μ[N.X] := by
      rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp, adj.unit_app_tensor_comp_map_δ_assoc,
        ← Functor.LaxMonoidal.μ_natural_assoc, tensorHom_comp_tensorHom_assoc]
      rfl
    rw [hδ]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨hunit.mp h1, hmul.mp h2⟩, fun ⟨h1, h2⟩ ↦ ⟨hunit.mpr h1, hmul.mpr h2⟩⟩

/-- The module-level pullback--pushforward adjunction preserves monoid homomorphisms on
quasi-coherent algebras. -/
theorem isMonHom_homEquiv_iff {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) (B : CommMon Y.Modules)
    (φ : ((pullbackQuasicoherentAlgebra f).obj A).obj.X ⟶ B.X) :
    @IsMonHom Y.Modules _ _ ((pullbackQuasicoherentAlgebra f).obj A).obj.X B.X
      ((pullbackQuasicoherentAlgebra f).obj A).obj.mon B.mon φ ↔
    @IsMonHom X.Modules _ _ A.obj.X (((Scheme.Modules.pushforward f).mapCommMon.obj B).X)
      A.obj.mon ((Scheme.Modules.pushforward f).mapCommMon.obj B).mon
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A.obj.X B.X) φ) := by
  have hη : inv (Functor.OplaxMonoidal.η (Scheme.Modules.pullback f)) =
      (Scheme.Modules.pullbackObjUnitIso f).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [Scheme.Modules.pullback_η, Iso.hom_inv_id]
  have h1_eq : η[((pullbackQuasicoherentAlgebra f).obj A).obj.X] =
      inv (Functor.OplaxMonoidal.η (Scheme.Modules.pullback f)) ≫
        (Scheme.Modules.pullback f).map η[A.obj.X] := by
    rw [hη, pullbackQuasicoherentAlgebra_obj_one]
  have h2_eq := pullbackQuasicoherentAlgebra_obj_mul f A
  constructor
  · rintro ⟨h1, h2⟩
    exact (isMonHom_homEquiv_iff_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction f) A.obj.X B.toMon φ).mp
      ⟨(congrArg (· ≫ φ) h1_eq.symm).trans h1, (congrArg (· ≫ φ) h2_eq.symm).trans h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := (isMonHom_homEquiv_iff_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction f) A.obj.X B.toMon φ).mpr h
    exact ⟨(congrArg (· ≫ φ) h1_eq).trans h1, (congrArg (· ≫ φ) h2_eq).trans h2⟩

/-- Morphisms of commutative `𝒪_Y`-algebras out of `(pullbackQuasicoherentAlgebra f).obj A` into an
arbitrary commutative `𝒪_Y`-algebra `B` correspond bijectively to morphisms of commutative
`𝒪_X`-algebras `A.obj ⟶ (Scheme.Modules.pushforward f).mapCommMon.obj B`. -/
@[expose]
def pullbackPushforwardCommMonHomEquiv {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) (B : CommMon Y.Modules) :
    (((pullbackQuasicoherentAlgebra f).obj A).obj ⟶ B) ≃
      (A.obj ⟶ (Scheme.Modules.pushforward f).mapCommMon.obj B) where
  toFun φ := CommMon.homMk
    { hom := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A.obj.X B.X) φ.hom.hom
      isMonHom_hom := (isMonHom_homEquiv_iff f A B φ.hom.hom).mp φ.hom.isMonHom_hom }
  invFun ψ := CommMon.homMk
    { hom := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A.obj.X B.X).symm ψ.hom.hom
      isMonHom_hom := (isMonHom_homEquiv_iff f A B _).mpr
        (Eq.mp (congrArg
          (fun k ↦ @IsMonHom X.Modules _ _ A.obj.X
            ((Scheme.Modules.pushforward f).mapCommMon.obj B).X
            A.obj.mon ((Scheme.Modules.pushforward f).mapCommMon.obj B).mon k)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A.obj.X B.X).apply_symm_apply
            ψ.hom.hom).symm) ψ.hom.isMonHom_hom) }
  left_inv φ := CommMon.hom_ext _ _ (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    A.obj.X B.X).left_inv φ.hom.hom)
  right_inv ψ := CommMon.hom_ext _ _ (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    A.obj.X B.X).right_inv ψ.hom.hom)

@[simp]
lemma pullbackPushforwardCommMonHomEquiv_apply_hom_hom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) (B : CommMon Y.Modules)
    (φ : ((pullbackQuasicoherentAlgebra f).obj A).obj ⟶ B) :
    (pullbackPushforwardCommMonHomEquiv f A B φ).hom.hom =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A.obj.X B.X) φ.hom.hom :=
  (rfl)

@[simp]
lemma pullbackPushforwardCommMonHomEquiv_symm_apply_hom_hom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) (B : CommMon Y.Modules)
    (ψ : A.obj ⟶ (Scheme.Modules.pushforward f).mapCommMon.obj B) :
    ((pullbackPushforwardCommMonHomEquiv f A B).symm ψ).hom.hom =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A.obj.X B.X).symm ψ.hom.hom :=
  (rfl)

/-- Morphisms in `QuasicoherentAlgebra Y` from `(pullbackQuasicoherentAlgebra f).obj A` to the
structure-sheaf algebra `structureSheafAlgebra Y` correspond bijectively to morphisms in
`CommMon X.Modules` from `A.obj` to `f.pushforwardStructureAlgebra`. -/
@[expose]
def pullbackStructureSheafAlgebraHomEquiv {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) :
    ((pullbackQuasicoherentAlgebra f).obj A ⟶ structureSheafAlgebra Y) ≃
      (A.obj ⟶ f.pushforwardStructureAlgebra) :=
  { toFun := fun a ↦ pullbackPushforwardCommMonHomEquiv f A (CommMon.trivial Y.Modules) a.hom
    invFun := fun ψ ↦ ObjectProperty.homMk
      ((pullbackPushforwardCommMonHomEquiv f A (CommMon.trivial Y.Modules)).symm ψ)
    left_inv := fun a ↦ ObjectProperty.hom_ext _
      ((pullbackPushforwardCommMonHomEquiv f A (CommMon.trivial Y.Modules)).left_inv a.hom)
    right_inv := fun ψ ↦
      (pullbackPushforwardCommMonHomEquiv f A (CommMon.trivial Y.Modules)).right_inv ψ }

@[simp]
lemma pullbackStructureSheafAlgebraHomEquiv_apply_hom_hom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X)
    (a : (pullbackQuasicoherentAlgebra f).obj A ⟶ structureSheafAlgebra Y) :
    (pullbackStructureSheafAlgebraHomEquiv f A a).hom.hom =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A.obj.X (𝟙_ Y.Modules))
        a.hom.hom.hom :=
  (rfl)

@[simp]
lemma pullbackStructureSheafAlgebraHomEquiv_symm_apply_hom_hom_hom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) (ψ : A.obj ⟶ f.pushforwardStructureAlgebra) :
    ((pullbackStructureSheafAlgebraHomEquiv f A).symm ψ).hom.hom.hom =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A.obj.X (𝟙_ Y.Modules)).symm
        ψ.hom.hom :=
  (rfl)

/-- Precomposing with a morphism of quasi-coherent algebras commutes with
`pullbackStructureSheafAlgebraHomEquiv`. -/
@[reassoc]
theorem pullbackStructureSheafAlgebraHomEquiv_precomp {X Y : Scheme.{u}} (f : Y ⟶ X)
    {A B : QuasicoherentAlgebra X} (φ : B ⟶ A)
    (a : (pullbackQuasicoherentAlgebra f).obj A ⟶ structureSheafAlgebra Y) :
    pullbackStructureSheafAlgebraHomEquiv f B ((pullbackQuasicoherentAlgebra f).map φ ≫ a) =
      φ.hom ≫ pullbackStructureSheafAlgebraHomEquiv f A a := by
  apply CommMon.hom_ext
  exact Adjunction.homEquiv_naturality_left
    (Scheme.Modules.pullbackPushforwardAdjunction f) φ.hom.hom.hom a.hom.hom.hom

lemma pullbackPushforwardAdjunction_homEquiv_pullback {X : Scheme.{u}} {T T' : Over X}
    (g : T' ⟶ T) (M : X.Modules)
    (a : (Scheme.Modules.pullback T.hom).obj M ⟶ 𝟙_ T.left.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction T'.hom).homEquiv M (𝟙_ T'.left.Modules))
        (((Scheme.Modules.pullbackCongr g.w).inv.app M ≫
            (Scheme.Modules.pullbackComp g.left T.hom).inv.app M) ≫
          (Scheme.Modules.pullback g.left).map a ≫
          (Scheme.Modules.pullbackObjUnitIso g.left).hom) =
      ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv M (𝟙_ T.left.Modules)) a ≫
        (Scheme.Modules.pushforward T.hom).map
          (SheafOfModules.unitToPushforwardObjUnit g.left.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp g.left T.hom).hom.app (𝟙_ T'.left.Modules) ≫
        (Scheme.Modules.pushforwardCongr g.w).hom.app (𝟙_ T'.left.Modules) := by
  have hcongr : ∀ (f₁ f₂ : T'.left ⟶ X) (h : f₁ = f₂)
      (m : (Scheme.Modules.pullback f₁).obj M ⟶ 𝟙_ T'.left.Modules),
      ((Scheme.Modules.pullbackPushforwardAdjunction f₂).homEquiv M (𝟙_ T'.left.Modules))
        ((Scheme.Modules.pullbackCongr h).inv.app M ≫ m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f₁).homEquiv M (𝟙_ T'.left.Modules)) m ≫
        (Scheme.Modules.pushforwardCongr h).hom.app (𝟙_ T'.left.Modules) := by
    rintro f₁ _ rfl m
    have hpush : (Scheme.Modules.pushforwardCongr (rfl : f₁ = f₁)).hom.app
        (𝟙_ T'.left.Modules) = 𝟙 _ := by
      ext U : 2
      simp
      rfl
    have hpull : (Scheme.Modules.pullbackCongr (rfl : f₁ = f₁)).inv.app M = 𝟙 _ := rfl
    rw [hpull, hpush, Category.id_comp, Category.comp_id]
  rw [Category.assoc, hcongr (g.left ≫ T.hom) T'.hom g.w]
  rw [← Adjunction.homEquiv_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g.left)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left]
  refine (congrArg (fun k ↦ (k ≫ (Scheme.Modules.pushforwardComp g.left T.hom).hom.app _) ≫
      (Scheme.Modules.pushforwardCongr g.w).hom.app _)
    (((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv_naturality_right
      a _).trans
      (congrArg (((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _) a ≫
        (Scheme.Modules.pushforward T.hom).map ·)
        (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom
          g.left)))).trans
    ?_
  simp only [Category.assoc]
  rfl

/-- Under `pullbackStructureSheafAlgebraHomEquiv`, pulling back an algebra morphism along a
test-scheme morphism `g : T' ⟶ T` over `X` corresponds to post-composing with
`Scheme.Hom.pushforwardStructureAlgebraMap g.left g.w`. -/
theorem pullbackStructureSheafAlgebraHomEquiv_pullback {X : Scheme.{u}} {T T' : Over X}
    (g : T' ⟶ T) (A : QuasicoherentAlgebra X)
    (a : (pullbackQuasicoherentAlgebra T.hom).obj A ⟶ structureSheafAlgebra T.left) :
    pullbackStructureSheafAlgebraHomEquiv T'.hom A
        ((pullbackAlgebraCompOverIso g A).inv ≫
          (pullbackQuasicoherentAlgebra g.left).map a ≫
          (pullbackStructureSheafAlgebraIso g.left).hom) =
      pullbackStructureSheafAlgebraHomEquiv T.hom A a ≫
        Scheme.Hom.pushforwardStructureAlgebraMap g.left g.w := by
  apply CommMon.hom_ext
  exact (pullbackPushforwardAdjunction_homEquiv_pullback g A.obj.X a.hom.hom.hom).trans
    (congrArg (((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv A.obj.X
      (𝟙_ T.left.Modules)) a.hom.hom.hom ≫ ·)
      (Scheme.Hom.pushforwardStructureAlgebraMap_hom g.left g.w).symm)

end

end TauCeti.AlgebraicGeometry
