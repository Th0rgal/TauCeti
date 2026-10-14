/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.UniversalProperty
public import TauCeti.AlgebraicGeometry.VectorBundle.SymmetricAlgebraUniversalProperty
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpaceBaseChange

/-!
# Section-valued universal property of the total space and direct sums

For a scheme `X` and a finite locally free sheaf `E : FiniteLocallyFreeSheaf X`, we establish the
section-valued universal property of the total space `V(E) = Spec_X (Sym (E^∨))`:
* `TauCeti.AlgebraicGeometry.pullbackSectionMap`: restriction of pulled-back sections along a
  morphism of test schemes `g : T' ⟶ T` over `X`;
* `TauCeti.AlgebraicGeometry.totalSpacePoints` and `TauCeti.AlgebraicGeometry.pullbackSections`:
  the `Over X`-point presheaf of `V(E)` and the presheaf of pulled-back sections
  `T ↦ Hom_{𝒪_T}(𝒪_T, T.hom^* E)`, both functorial in `E`;
* `TauCeti.AlgebraicGeometry.totalSpaceUniversalProperty`: the natural isomorphism
  `totalSpacePoints X ≅ pullbackSections X`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv`,
  `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_naturality_test`, and
  `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_naturality_bundle`: the pointwise equivalence and
  its naturality in both the test scheme `T` and the bundle `E`;
* `TauCeti.AlgebraicGeometry.directSum` and `TauCeti.AlgebraicGeometry.totalSpaceDirectSumIso`:
  compatibility of the total space with binary direct sums `E ⊞ F`.
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

section ExactPairingUnitHomEquiv

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Given an exact pairing `ExactPairing D M` in a monoidal category `C`, morphisms `D ⟶ 𝟙_ C`
correspond bijectively to sections `𝟙_ C ⟶ M`. -/
@[expose]
def exactPairingUnitHomEquiv (D M : C) [ExactPairing D M] : (D ⟶ 𝟙_ C) ≃ (𝟙_ C ⟶ M) where
  toFun w := η_ D M ≫ (w ▷ M) ≫ (λ_ M).hom
  invFun s := (λ_ D).inv ≫ (s ▷ D) ≫ ε_ D M
  left_inv w := by
    calc
      (λ_ D).inv ≫ ((η_ D M ≫ (w ▷ M) ≫ (λ_ M).hom) ▷ D) ≫ ε_ D M
        = 𝟙 _ ⊗≫ η_ D M ▷ D ⊗≫ (w ▷ (M ⊗ D) ≫ 𝟙_ C ◁ ε_ D M) ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ (η_ D M ▷ D ⊗≫ D ◁ ε_ D M) ⊗≫ w := by
        rw [← whisker_exchange]; monoidal
      _ = w := by
        rw [ExactPairing.evaluation_coevaluation'']; monoidal
  right_inv s := by
    calc
      η_ D M ≫ (((λ_ D).inv ≫ (s ▷ D) ≫ ε_ D M) ▷ M) ≫ (λ_ M).hom
        = 𝟙 _ ⊗≫ (𝟙_ C ◁ η_ D M ≫ s ▷ (D ⊗ M)) ⊗≫ ε_ D M ▷ M ⊗≫ 𝟙 _ := by
        monoidal
      _ = s ⊗≫ (M ◁ η_ D M ⊗≫ ε_ D M ▷ M) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; monoidal
      _ = s := by
        rw [ExactPairing.coevaluation_evaluation'']; monoidal

@[simp]
lemma exactPairingUnitHomEquiv_symm_apply (D M : C) [ExactPairing D M] (s : 𝟙_ C ⟶ M) :
    (exactPairingUnitHomEquiv D M).symm s = (λ_ D).inv ≫ (s ▷ D) ≫ ε_ D M :=
  (rfl)

end ExactPairingUnitHomEquiv

section TotalSpaceUniversalProperty

variable {X : Scheme.{u}}

/-- Restriction of pulled-back sections along a morphism of test schemes over `X`. -/
@[expose]
noncomputable def pullbackSectionMap (E : X.Modules) {T T' : Over X} (g : T' ⟶ T)
    (s : SheafOfModules.unit T.left.ringCatSheaf ⟶
      (Scheme.Modules.pullback T.hom).obj E) :
    SheafOfModules.unit T'.left.ringCatSheaf ⟶
      (Scheme.Modules.pullback T'.hom).obj E :=
  (Scheme.Modules.pullbackObjUnitIso g.left).inv ≫
    (Scheme.Modules.pullback g.left).map s ≫
    (Scheme.Modules.pullbackComp g.left T.hom).hom.app E ≫
    (Scheme.Modules.pullbackCongr g.w).hom.app E

/-- The `Over X`-point presheaf of the total space `V(E)`, functorial in `E`. -/
@[expose]
noncomputable def totalSpacePoints (X : Scheme.{u}) :
    FiniteLocallyFreeSheaf X ⥤ ((Over X)ᵒᵖ ⥤ Type u) :=
  totalSpaceScheme X ⋙ affineSchemeOverForget X ⋙ yoneda

/-- The exact pairing between `f^* (E^∨)` and `f^* E` on `Y.Modules` obtained by transporting the
canonical pairing on `QuasicoherentSheaf X` along the strong monoidal pullback functor. -/
@[instance_reducible, expose]
def pulledBackExactPairingDual (E : FiniteLocallyFreeSheaf X) {Y : Scheme.{u}} (f : Y ⟶ X) :
    ExactPairing
      ((Scheme.Modules.pullback f).obj (FiniteLocallyFreeSheaf.dual E).obj)
      ((Scheme.Modules.pullback f).obj E.obj) :=
  letI : ExactPairing (FiniteLocallyFreeSheaf.dual E).obj E.obj :=
    exactPairingOfIsIsoDualTensorIhom (Y := E.obj)
  let D_qc : QuasicoherentSheaf X :=
    (FiniteLocallyFreeSheaf.toQuasicoherent X).obj (FiniteLocallyFreeSheaf.dual E)
  let E_qc : QuasicoherentSheaf X :=
    (FiniteLocallyFreeSheaf.toQuasicoherent X).obj E
  letI : ExactPairing D_qc E_qc :=
    @ObjectProperty.exactPairingFullSubcategory X.Modules _ _ _
      (Scheme.Modules.isMonoidal_isQuasicoherent X) D_qc E_qc ‹_›
  let P : QuasicoherentSheaf X ⥤ Y.Modules :=
    (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules) ⋙ Scheme.Modules.pullback f
  P.mapExactPairing D_qc E_qc

lemma pulledBackExactPairingDual_evaluation (E : FiniteLocallyFreeSheaf X) {Y : Scheme.{u}}
    (f : Y ⟶ X) :
    @ExactPairing.evaluation Y.Modules _ _
      ((Scheme.Modules.pullback f).obj (FiniteLocallyFreeSheaf.dual E).obj)
      ((Scheme.Modules.pullback f).obj E.obj)
      (pulledBackExactPairingDual E f) =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) E.obj
          (FiniteLocallyFreeSheaf.dual E).obj) ≫
        (Scheme.Modules.pullback f).map ((ihom.ev E.obj).app (𝟙_ X.Modules)) ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom := by
  let _ : ExactPairing (FiniteLocallyFreeSheaf.dual E).obj E.obj :=
    exactPairingOfIsIsoDualTensorIhom (Y := E.obj)
  let D_qc : QuasicoherentSheaf X :=
    (FiniteLocallyFreeSheaf.toQuasicoherent X).obj (FiniteLocallyFreeSheaf.dual E)
  let E_qc : QuasicoherentSheaf X :=
    (FiniteLocallyFreeSheaf.toQuasicoherent X).obj E
  let _ : ExactPairing D_qc E_qc :=
    @ObjectProperty.exactPairingFullSubcategory X.Modules _ _ _
      (Scheme.Modules.isMonoidal_isQuasicoherent X) D_qc E_qc ‹_›
  let P : QuasicoherentSheaf X ⥤ Y.Modules :=
    (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules) ⋙ Scheme.Modules.pullback f
  have hdef : @ExactPairing.evaluation Y.Modules _ _
      ((Scheme.Modules.pullback f).obj (FiniteLocallyFreeSheaf.dual E).obj)
      ((Scheme.Modules.pullback f).obj E.obj)
      (pulledBackExactPairingDual E f) =
      Functor.LaxMonoidal.μ P E_qc D_qc ≫
        (Scheme.Modules.pullback f).map (ε_ D_qc E_qc).hom ≫
        Functor.OplaxMonoidal.η P :=
    Functor.mapExactPairing_evaluation (F := P) D_qc E_qc
  have hμ : Functor.LaxMonoidal.μ P E_qc D_qc =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) E.obj
        (FiniteLocallyFreeSheaf.dual E).obj) := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ P E_qc D_qc), Functor.Monoidal.δ_μ,
      Scheme.Modules.pullbackToModules_δ]
    exact (IsIso.hom_inv_id
      (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) E.obj E.dual.obj)).symm
  let _ : MonoidalCategory (SheafOfModules X.ringCatSheaf) :=
    inferInstanceAs (MonoidalCategory X.Modules)
  let _ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsMonoidal :=
    Scheme.Modules.isMonoidal_isQuasicoherent X
  let _ : ExactPairing D_qc.obj E_qc.obj :=
    exactPairingOfIsIsoDualTensorIhom (Y := E.obj)
  have hε : (ε_ D_qc E_qc).hom = (ihom.ev E.obj).app (𝟙_ X.Modules) :=
    (ObjectProperty.exactPairingFullSubcategory_evaluation_hom D_qc E_qc).trans
      exactPairingOfIsIsoDualTensorIhom_evaluation
  exact hdef.trans ((congrArg (· ≫ _) hμ).trans
    (congrArg (_ ≫ ·) ((congrArg (· ≫ _) (congrArg (Scheme.Modules.pullback f).map hε)).trans
      (congrArg (_ ≫ ·) (Scheme.Modules.pullbackToModules_η f)))))

/-- Equivalence between morphisms `f^* (E^∨) ⟶ 𝒪_Y` and sections `𝒪_Y ⟶ f^* E`. -/
@[expose]
def pulledBackDualToSectionEquiv (E : FiniteLocallyFreeSheaf X) {Y : Scheme.{u}} (f : Y ⟶ X) :
    ((Scheme.Modules.pullback f).obj (FiniteLocallyFreeSheaf.dual E).obj ⟶ 𝟙_ Y.Modules) ≃
      (𝟙_ Y.Modules ⟶ (Scheme.Modules.pullback f).obj E.obj) :=
  letI := pulledBackExactPairingDual E f
  exactPairingUnitHomEquiv
    ((Scheme.Modules.pullback f).obj (FiniteLocallyFreeSheaf.dual E).obj)
    ((Scheme.Modules.pullback f).obj E.obj)

@[simp]
lemma pulledBackDualToSectionEquiv_symm_apply (E : FiniteLocallyFreeSheaf X) {Y : Scheme.{u}}
    (f : Y ⟶ X) (s : 𝟙_ Y.Modules ⟶ (Scheme.Modules.pullback f).obj E.obj) :
    (pulledBackDualToSectionEquiv E f).symm s =
      (λ_ ((Scheme.Modules.pullback f).obj (FiniteLocallyFreeSheaf.dual E).obj)).inv ≫
        (s ▷ (Scheme.Modules.pullback f).obj (FiniteLocallyFreeSheaf.dual E).obj) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) E.obj
            (FiniteLocallyFreeSheaf.dual E).obj) ≫
          (Scheme.Modules.pullback f).map ((ihom.ev E.obj).app (𝟙_ X.Modules)) ≫
          (Scheme.Modules.pullbackObjUnitIso f).hom :=
  congrArg ((λ_ _).inv ≫ (s ▷ _) ≫ ·) (pulledBackExactPairingDual_evaluation E f)

private lemma pulledBackDualToSectionEquiv_symm_pullback (E : FiniteLocallyFreeSheaf X)
    {T T' : Over X} (g : T' ⟶ T)
    (s : 𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj E.obj) :
    (pulledBackDualToSectionEquiv E T'.hom).symm (pullbackSectionMap E.obj g s) =
      (Scheme.Modules.pullbackCongr g.w).inv.app (FiniteLocallyFreeSheaf.dual E).obj ≫
        (Scheme.Modules.pullbackComp g.left T.hom).inv.app (FiniteLocallyFreeSheaf.dual E).obj ≫
        (Scheme.Modules.pullback g.left).map ((pulledBackDualToSectionEquiv E T.hom).symm s) ≫
        (Scheme.Modules.pullbackObjUnitIso g.left).hom := by
  let D : X.Modules := (FiniteLocallyFreeSheaf.dual E).obj
  let M : X.Modules := E.obj
  let ev : M ⊗ D ⟶ 𝟙_ X.Modules := (ihom.ev E.obj).app (𝟙_ X.Modules)
  have hcongr : ∀ (f₁ f₂ : T'.left ⟶ X) (hw : f₁ = f₂)
      (s₀ : 𝟙_ T'.left.Modules ⟶ (Scheme.Modules.pullback f₁).obj M),
      (pulledBackDualToSectionEquiv E f₂).symm
        (s₀ ≫ (Scheme.Modules.pullbackCongr hw).hom.app M) =
      (Scheme.Modules.pullbackCongr hw).inv.app D ≫
        (pulledBackDualToSectionEquiv E f₁).symm s₀ := by
    rintro f₁ _ rfl s₀
    have h1 : (Scheme.Modules.pullbackCongr (rfl : f₁ = f₁)).hom.app M = 𝟙 _ := rfl
    have h2 : (Scheme.Modules.pullbackCongr (rfl : f₁ = f₁)).inv.app D = 𝟙 _ := rfl
    rw [h1, h2, comp_id, id_comp]
  change (pulledBackDualToSectionEquiv E T'.hom).symm
      (((Scheme.Modules.pullbackObjUnitIso g.left).inv ≫
        (Scheme.Modules.pullback g.left).map s ≫
        (Scheme.Modules.pullbackComp g.left T.hom).hom.app M) ≫
        (Scheme.Modules.pullbackCongr g.w).hom.app M) =
    (Scheme.Modules.pullbackCongr g.w).inv.app D ≫
      (Scheme.Modules.pullbackComp g.left T.hom).inv.app D ≫
      (Scheme.Modules.pullback g.left).map ((pulledBackDualToSectionEquiv E T.hom).symm s) ≫
      (Scheme.Modules.pullbackObjUnitIso g.left).hom
  rw [hcongr (g.left ≫ T.hom) T'.hom g.w]
  congr 1
  refine (Iso.eq_inv_comp ((Scheme.Modules.pullbackComp g.left T.hom).app D)).mpr ?_
  rw [pulledBackDualToSectionEquiv_symm_apply, pulledBackDualToSectionEquiv_symm_apply]
  change (Scheme.Modules.pullbackComp g.left T.hom).hom.app D ≫
      (λ_ ((Scheme.Modules.pullback (g.left ≫ T.hom)).obj D)).inv ≫
      (((Scheme.Modules.pullbackObjUnitIso g.left).inv ≫
        (Scheme.Modules.pullback g.left).map s ≫
        (Scheme.Modules.pullbackComp g.left T.hom).hom.app M) ▷
        (Scheme.Modules.pullback (g.left ≫ T.hom)).obj D) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (g.left ≫ T.hom)) M D) ≫
      (Scheme.Modules.pullback (g.left ≫ T.hom)).map ev ≫
      (Scheme.Modules.pullbackObjUnitIso (g.left ≫ T.hom)).hom =
    (Scheme.Modules.pullback g.left).map
        ((λ_ ((Scheme.Modules.pullback T.hom).obj D)).inv ≫
          (s ▷ (Scheme.Modules.pullback T.hom).obj D) ≫
          inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) M D) ≫
          (Scheme.Modules.pullback T.hom).map ev ≫
          (Scheme.Modules.pullbackObjUnitIso T.hom).hom) ≫
      (Scheme.Modules.pullbackObjUnitIso g.left).hom
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  simp only [comp_whiskerRight, assoc]
  rw [leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc, whisker_exchange_assoc, ← tensorHom_def'_assoc]
  dsimp only [Functor.comp_obj]
  have hδ : ((Scheme.Modules.pullbackComp g.left T.hom).hom.app M ⊗ₘ
        (Scheme.Modules.pullbackComp g.left T.hom).hom.app D) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (g.left ≫ T.hom)) M D) =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g.left)
          ((Scheme.Modules.pullback T.hom).obj M) ((Scheme.Modules.pullback T.hom).obj D)) ≫
        (Scheme.Modules.pullback g.left).map
          (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) M D)) ≫
        (Scheme.Modules.pullbackComp g.left T.hom).hom.app (M ⊗ D) := by
    rw [← cancel_mono (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (g.left ≫ T.hom)) M D),
      assoc, assoc, assoc, IsIso.inv_hom_id, comp_id, pullbackComp_hom_app_comp_δ,
      ← Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, id_comp,
      IsIso.inv_hom_id_assoc]
  rw [← assoc ((Scheme.Modules.pullbackComp g.left T.hom).hom.app M ⊗ₘ _), hδ]
  simp only [assoc]
  have hnat_ev : (Scheme.Modules.pullbackComp g.left T.hom).hom.app (M ⊗ D) ≫
      (Scheme.Modules.pullback (g.left ≫ T.hom)).map ev ≫
      (Scheme.Modules.pullbackObjUnitIso (g.left ≫ T.hom)).hom =
      (Scheme.Modules.pullback g.left).map
        ((Scheme.Modules.pullback T.hom).map ev) ≫
      (Scheme.Modules.pullback g.left).map (Scheme.Modules.pullbackObjUnitIso T.hom).hom ≫
      (Scheme.Modules.pullbackObjUnitIso g.left).hom := by
    rw [← (Scheme.Modules.pullbackComp g.left T.hom).hom.naturality_assoc ev,
      ← Scheme.Modules.pullbackObjUnitIso_comp g.left T.hom, Iso.hom_inv_id_app_assoc]
    rfl
  rw [hnat_ev]
  have h_s : ((Scheme.Modules.pullback g.left).map s ▷
        (Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback T.hom).obj D)) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g.left)
        ((Scheme.Modules.pullback T.hom).obj M) ((Scheme.Modules.pullback T.hom).obj D)) =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g.left)
        (𝟙_ T.left.Modules) ((Scheme.Modules.pullback T.hom).obj D)) ≫
      (Scheme.Modules.pullback g.left).map (s ▷ (Scheme.Modules.pullback T.hom).obj D) := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g.left) _ _),
      IsIso.hom_inv_id_assoc, Functor.OplaxMonoidal.δ_natural_left_assoc,
      IsIso.hom_inv_id, comp_id]
  rw [← assoc ((Scheme.Modules.pullback g.left).map s ▷ _), h_s, assoc]
  have h_unit : (λ_ ((Scheme.Modules.pullback g.left).obj
        ((Scheme.Modules.pullback T.hom).obj D))).inv ≫
      ((Scheme.Modules.pullbackObjUnitIso g.left).inv ▷
        (Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback T.hom).obj D)) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g.left)
        (𝟙_ T.left.Modules) ((Scheme.Modules.pullback T.hom).obj D)) =
      (Scheme.Modules.pullback g.left).map (λ_ ((Scheme.Modules.pullback T.hom).obj D)).inv := by
    rw [Functor.OplaxMonoidal.oplax_left_unitality (Scheme.Modules.pullback g.left),
      Scheme.Modules.pullback_η, assoc, assoc, ← comp_whiskerRight_assoc,
      Iso.hom_inv_id, id_whiskerRight, id_comp, IsIso.hom_inv_id, comp_id]
  rw [reassoc_of% h_unit]

private lemma pulledBackDualToSectionEquiv_symm_bundle {E F : FiniteLocallyFreeSheaf X}
    (a : E ⟶ F) (T : Over X)
    (s : 𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj E.obj) :
    (pulledBackDualToSectionEquiv F T.hom).symm
        (s ≫ (Scheme.Modules.pullback T.hom).map a.hom) =
      (Scheme.Modules.pullback T.hom).map
          (((dualAsQuasicoherentOp X).map a).unop.hom) ≫
        (pulledBackDualToSectionEquiv E T.hom).symm s := by
  let DE : X.Modules := (FiniteLocallyFreeSheaf.dual E).obj
  let DF : X.Modules := (FiniteLocallyFreeSheaf.dual F).obj
  let ME : X.Modules := E.obj
  let MF : X.Modules := F.obj
  let da : DF ⟶ DE := ((dualAsQuasicoherentOp X).map a).unop.hom
  let evE : ME ⊗ DE ⟶ 𝟙_ X.Modules := (ihom.ev E.obj).app (𝟙_ X.Modules)
  let evF : MF ⊗ DF ⟶ 𝟙_ X.Modules := (ihom.ev F.obj).app (𝟙_ X.Modules)
  have hev : (a.hom ▷ DF) ≫ evF = (ME ◁ da) ≫ evE :=
    (MonoidalClosed.id_tensor_pre_app_comp_ev a.hom (𝟙_ X.Modules)).symm
  rw [pulledBackDualToSectionEquiv_symm_apply, pulledBackDualToSectionEquiv_symm_apply]
  change (λ_ ((Scheme.Modules.pullback T.hom).obj DF)).inv ≫
      ((s ≫ (Scheme.Modules.pullback T.hom).map a.hom) ▷
        (Scheme.Modules.pullback T.hom).obj DF) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) MF DF) ≫
      (Scheme.Modules.pullback T.hom).map evF ≫
      (Scheme.Modules.pullbackObjUnitIso T.hom).hom =
    (Scheme.Modules.pullback T.hom).map da ≫
      (λ_ ((Scheme.Modules.pullback T.hom).obj DE)).inv ≫
      (s ▷ (Scheme.Modules.pullback T.hom).obj DE) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) ME DE) ≫
      (Scheme.Modules.pullback T.hom).map evE ≫
      (Scheme.Modules.pullbackObjUnitIso T.hom).hom
  rw [comp_whiskerRight_assoc, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  have h1 : ((Scheme.Modules.pullback T.hom).map a.hom ▷
        (Scheme.Modules.pullback T.hom).obj DF) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) MF DF) =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) ME DF) ≫
      (Scheme.Modules.pullback T.hom).map (a.hom ▷ DF) := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) _ _),
      IsIso.hom_inv_id_assoc, Functor.OplaxMonoidal.δ_natural_left_assoc,
      IsIso.hom_inv_id, comp_id]
  have h2 : ((Scheme.Modules.pullback T.hom).obj ME ◁
        (Scheme.Modules.pullback T.hom).map da) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) ME DE) =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) ME DF) ≫
      (Scheme.Modules.pullback T.hom).map (ME ◁ da) := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback T.hom) _ _),
      IsIso.hom_inv_id_assoc, Functor.OplaxMonoidal.δ_natural_right_assoc,
      IsIso.hom_inv_id, comp_id]
  rw [← assoc ((Scheme.Modules.pullback T.hom).map a.hom ▷ _), h1,
    ← assoc ((Scheme.Modules.pullback T.hom).obj ME ◁ _), h2,
    assoc, assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hev]

/-- Direct construction of the bijection between `X`-morphisms `T ⟶ V(E)` and sections of
`T.hom^* E`. -/
@[expose]
noncomputable def totalSpaceHomEquiv₀ (E : FiniteLocallyFreeSheaf X) (T : Over X) :
    (T ⟶ (affineSchemeOverForget X).obj ((totalSpaceScheme X).obj E)) ≃
      (SheafOfModules.unit T.left.ringCatSheaf ⟶
        (Scheme.Modules.pullback T.hom).obj E.obj) :=
  (relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj
    ((dualAsQuasicoherentOp X).obj E).unop) T).trans <|
    (symmetricAlgebraCommMonHomEquiv (FiniteLocallyFreeSheaf.dual E).obj
      T.hom.pushforwardStructureAlgebra).trans <|
    (((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv
      (FiniteLocallyFreeSheaf.dual E).obj (𝟙_ T.left.Modules)).symm).trans <|
    pulledBackDualToSectionEquiv E T.hom

lemma totalSpaceHomEquiv₀_naturality_test (E : FiniteLocallyFreeSheaf X)
    {T T' : Over X} (g : T' ⟶ T)
    (h : T ⟶ (affineSchemeOverForget X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomEquiv₀ E T' (g ≫ h) =
      pullbackSectionMap E.obj g (totalSpaceHomEquiv₀ E T h) := by
  let D := (FiniteLocallyFreeSheaf.dual E).obj
  let F_qc := ((dualAsQuasicoherentOp X).obj E).unop
  let wT : (Scheme.Modules.pullback T.hom).obj D ⟶ 𝟙_ T.left.Modules :=
    ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv D (𝟙_ T.left.Modules)).symm
      (symmetricAlgebraCommMonHomEquiv D T.hom.pushforwardStructureAlgebra
        (relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj F_qc) T h))
  let wT' : (Scheme.Modules.pullback T'.hom).obj D ⟶ 𝟙_ T'.left.Modules :=
    ((Scheme.Modules.pullbackPushforwardAdjunction T'.hom).homEquiv D (𝟙_ T'.left.Modules)).symm
      (symmetricAlgebraCommMonHomEquiv D T'.hom.pushforwardStructureAlgebra
        (relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj F_qc) T' (g ≫ h)))
  apply (pulledBackDualToSectionEquiv E T'.hom).symm.injective
  refine ((pulledBackDualToSectionEquiv E T'.hom).symm_apply_apply wT').trans ?_
  refine (?_ : wT' = _).trans
    (pulledBackDualToSectionEquiv_symm_pullback E g (totalSpaceHomEquiv₀ E T h)).symm
  have hwT : (pulledBackDualToSectionEquiv E T.hom).symm (totalSpaceHomEquiv₀ E T h) = wT :=
    (pulledBackDualToSectionEquiv E T.hom).symm_apply_apply wT
  rw [hwT]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction T'.hom).homEquiv D
    (𝟙_ T'.left.Modules)).injective
  have hlhs : ((Scheme.Modules.pullbackPushforwardAdjunction T'.hom).homEquiv D
      (𝟙_ T'.left.Modules)) wT' =
      symmetricAlgebraCommMonHomEquiv D T'.hom.pushforwardStructureAlgebra
        (relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj F_qc) T' (g ≫ h)) :=
    Equiv.apply_symm_apply _ _
  have hrhs : ((Scheme.Modules.pullbackPushforwardAdjunction T'.hom).homEquiv D
      (𝟙_ T'.left.Modules))
      ((Scheme.Modules.pullbackCongr g.w).inv.app D ≫
        (Scheme.Modules.pullbackComp g.left T.hom).inv.app D ≫
        (Scheme.Modules.pullback g.left).map wT ≫
        (Scheme.Modules.pullbackObjUnitIso g.left).hom) =
      symmetricAlgebraCommMonHomEquiv D T.hom.pushforwardStructureAlgebra
        (relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj F_qc) T h) ≫
        (Scheme.Hom.pushforwardStructureAlgebraMap g.left g.w).hom.hom := by
    rw [← assoc, pullbackPushforwardAdjunction_homEquiv_pullback]
    exact (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans
      (congrArg (_ ≫ ·) (Scheme.Hom.pushforwardStructureAlgebraMap_hom g.left g.w)).symm
  refine hlhs.trans (Eq.trans ?_ hrhs.symm)
  exact (congrArg (symmetricAlgebraCommMonHomEquiv D T'.hom.pushforwardStructureAlgebra)
    (relativeSpecOverPushforwardHomEquiv_comp_left ((symmetricAlgebra X).obj F_qc) g h)).trans
    (symmetricAlgebraCommMonHomEquiv_postcomp D
      (relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj F_qc) T h)
      (Scheme.Hom.pushforwardStructureAlgebraMap g.left g.w))

lemma totalSpaceHomEquiv₀_naturality_bundle {E F : FiniteLocallyFreeSheaf X}
    (a : E ⟶ F) (T : Over X)
    (h : T ⟶ (affineSchemeOverForget X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomEquiv₀ F T (h ≫ (affineSchemeOverForget X).map ((totalSpaceScheme X).map a)) =
      totalSpaceHomEquiv₀ E T h ≫ (Scheme.Modules.pullback T.hom).map a.hom := by
  let DE := (FiniteLocallyFreeSheaf.dual E).obj
  let DF := (FiniteLocallyFreeSheaf.dual F).obj
  let FE_qc := ((dualAsQuasicoherentOp X).obj E).unop
  let FF_qc := ((dualAsQuasicoherentOp X).obj F).unop
  let wE : (Scheme.Modules.pullback T.hom).obj DE ⟶ 𝟙_ T.left.Modules :=
    ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv DE (𝟙_ T.left.Modules)).symm
      (symmetricAlgebraCommMonHomEquiv DE T.hom.pushforwardStructureAlgebra
        (relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj FE_qc) T h))
  let wF : (Scheme.Modules.pullback T.hom).obj DF ⟶ 𝟙_ T.left.Modules :=
    ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv DF (𝟙_ T.left.Modules)).symm
      (symmetricAlgebraCommMonHomEquiv DF T.hom.pushforwardStructureAlgebra
        (relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj FF_qc) T
          (h ≫ (affineSchemeOverForget X).map ((totalSpaceScheme X).map a))))
  apply (pulledBackDualToSectionEquiv F T.hom).symm.injective
  refine ((pulledBackDualToSectionEquiv F T.hom).symm_apply_apply wF).trans ?_
  refine (?_ : wF = _).trans
    (pulledBackDualToSectionEquiv_symm_bundle a T (totalSpaceHomEquiv₀ E T h)).symm
  have hwE : (pulledBackDualToSectionEquiv E T.hom).symm (totalSpaceHomEquiv₀ E T h) = wE :=
    (pulledBackDualToSectionEquiv E T.hom).symm_apply_apply wE
  rw [hwE]
  refine (congrArg
    (((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv DF
      (𝟙_ T.left.Modules)).symm) ?_).trans
    (Adjunction.homEquiv_naturality_left_symm
      (Scheme.Modules.pullbackPushforwardAdjunction T.hom)
      ((dualAsQuasicoherentOp X).map a).unop.hom _)
  refine (congrArg
    (symmetricAlgebraCommMonHomEquiv DF T.hom.pushforwardStructureAlgebra)
    (relativeSpecOverPushforwardHomEquiv_comp_right
      ((symmetricAlgebra X).map ((dualAsQuasicoherentOp X).map a).unop) T h)).trans
    (symmetricAlgebraCommMonHomEquiv_precomp
      (((dualAsQuasicoherentOp X).map a).unop)
      T.hom.pushforwardStructureAlgebra _)

lemma totalSpaceHomEquiv₀_def (E : FiniteLocallyFreeSheaf X) (T : Over X) :
    totalSpaceHomEquiv₀ E T =
      ((relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj
        ((dualAsQuasicoherentOp X).obj E).unop) T).trans <|
        (symmetricAlgebraCommMonHomEquiv (FiniteLocallyFreeSheaf.dual E).obj
          T.hom.pushforwardStructureAlgebra).trans <|
        (((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv
          (FiniteLocallyFreeSheaf.dual E).obj (𝟙_ T.left.Modules)).symm).trans <|
        pulledBackDualToSectionEquiv E T.hom) :=
  rfl

attribute [local irreducible] totalSpaceHomEquiv₀

/-- The functor sending a finite locally free sheaf `E` to the presheaf of pulled-back sections
`T ↦ Hom_{𝒪_T}(𝒪_T, T.hom^* E)` on `Over X`. -/
@[expose]
noncomputable def pullbackSections (X : Scheme.{u}) :
    FiniteLocallyFreeSheaf X ⥤ ((Over X)ᵒᵖ ⥤ Type u) where
  obj E :=
    { obj := fun T ↦
        SheafOfModules.unit T.unop.left.ringCatSheaf ⟶
          (Scheme.Modules.pullback T.unop.hom).obj E.obj
      map := fun g ↦ TypeCat.ofHom fun s ↦ pullbackSectionMap E.obj g.unop s
      map_id := fun T ↦ ConcreteCategory.hom_ext _ _ fun s ↦ by
        obtain ⟨h, rfl⟩ := (totalSpaceHomEquiv₀ E T.unop).surjective s
        change pullbackSectionMap E.obj (𝟙 T.unop) (totalSpaceHomEquiv₀ E T.unop h) =
          totalSpaceHomEquiv₀ E T.unop h
        rw [← totalSpaceHomEquiv₀_naturality_test, id_comp]
      map_comp := fun f g ↦ ConcreteCategory.hom_ext _ _ fun s ↦ by
        obtain ⟨h, rfl⟩ := (totalSpaceHomEquiv₀ E _).surjective s
        change pullbackSectionMap E.obj (g.unop ≫ f.unop) (totalSpaceHomEquiv₀ E _ h) =
          pullbackSectionMap E.obj g.unop
            (pullbackSectionMap E.obj f.unop (totalSpaceHomEquiv₀ E _ h))
        rw [← totalSpaceHomEquiv₀_naturality_test, ← totalSpaceHomEquiv₀_naturality_test,
          ← totalSpaceHomEquiv₀_naturality_test, assoc] }
  map f :=
    { app := fun T ↦ TypeCat.ofHom fun s ↦ s ≫ (Scheme.Modules.pullback T.unop.hom).map f.hom
      naturality := fun T T' g ↦ ConcreteCategory.hom_ext _ _ fun s ↦ by
        obtain ⟨h, rfl⟩ := (totalSpaceHomEquiv₀ _ T.unop).surjective s
        change pullbackSectionMap _ g.unop (totalSpaceHomEquiv₀ _ T.unop h) ≫
            (Scheme.Modules.pullback T'.unop.hom).map f.hom =
          pullbackSectionMap _ g.unop
            (totalSpaceHomEquiv₀ _ T.unop h ≫ (Scheme.Modules.pullback T.unop.hom).map f.hom)
        rw [← totalSpaceHomEquiv₀_naturality_test, ← totalSpaceHomEquiv₀_naturality_bundle,
          ← totalSpaceHomEquiv₀_naturality_bundle, ← totalSpaceHomEquiv₀_naturality_test,
          assoc] }
  map_id E := by
    ext T : 2
    refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
    let s₀ : 𝟙_ T.unop.left.Modules ⟶ (Scheme.Modules.pullback T.unop.hom).obj E.obj := s
    exact (congrArg (s₀ ≫ ·) ((Scheme.Modules.pullback T.unop.hom).map_id E.obj)).trans
      (comp_id s₀)
  map_comp f g := by
    ext T : 2
    refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
    let s₀ : 𝟙_ T.unop.left.Modules ⟶ (Scheme.Modules.pullback T.unop.hom).obj _ := s
    exact (congrArg (s₀ ≫ ·) ((Scheme.Modules.pullback T.unop.hom).map_comp f.hom g.hom)).trans
      (assoc s₀ _ _).symm

/-- Construct a natural isomorphism between two bifunctors `C ⥤ D ⥤ Type u` from pointwise
equivalences that are natural in both variables. -/
@[expose]
def natIsoOfPointwiseEquiv {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D ⥤ Type u)
    (e : ∀ (A : C) (B : D), (F.obj A).obj B ≃ (G.obj A).obj B)
    (h₁ : ∀ (A : C) {B₁ B₂ : D} (g : B₁ ⟶ B₂) (x : (F.obj A).obj B₁),
      e A B₂ ((F.obj A).map g x) = (G.obj A).map g (e A B₁ x))
    (h₂ : ∀ {A₁ A₂ : C} (a : A₁ ⟶ A₂) (B : D) (x : (F.obj A₁).obj B),
      e A₂ B ((F.map a).app B x) = (G.map a).app B (e A₁ B x)) :
    F ≅ G :=
  NatIso.ofComponents
    (fun A ↦ NatIso.ofComponents
      (fun B ↦ Equiv.toIso (e A B))
      (fun g ↦ ConcreteCategory.hom_ext _ _ fun x ↦ h₁ A g x))
    (fun a ↦ NatTrans.ext (funext fun B ↦ ConcreteCategory.hom_ext _ _ fun x ↦ h₂ a B x))

@[simp]
lemma natIsoOfPointwiseEquiv_app_app_toEquiv {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D ⥤ Type u)
    (e : ∀ (A : C) (B : D), (F.obj A).obj B ≃ (G.obj A).obj B)
    (h₁ : ∀ (A : C) {B₁ B₂ : D} (g : B₁ ⟶ B₂) (x : (F.obj A).obj B₁),
      e A B₂ ((F.obj A).map g x) = (G.obj A).map g (e A B₁ x))
    (h₂ : ∀ {A₁ A₂ : C} (a : A₁ ⟶ A₂) (B : D) (x : (F.obj A₁).obj B),
      e A₂ B ((F.map a).app B x) = (G.map a).app B (e A₁ B x))
    (A : C) (B : D) :
    (((natIsoOfPointwiseEquiv F G e h₁ h₂).app A).app B).toEquiv = e A B :=
  (rfl)

lemma natIsoOfPointwiseEquiv_naturality₁ {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D ⥤ Type u)
    (e : ∀ (A : C) (B : D), (F.obj A).obj B ≃ (G.obj A).obj B)
    (h₁ : ∀ (A : C) {B₁ B₂ : D} (g : B₁ ⟶ B₂) (x : (F.obj A).obj B₁),
      e A B₂ ((F.obj A).map g x) = (G.obj A).map g (e A B₁ x))
    (h₂ : ∀ {A₁ A₂ : C} (a : A₁ ⟶ A₂) (B : D) (x : (F.obj A₁).obj B),
      e A₂ B ((F.map a).app B x) = (G.map a).app B (e A₁ B x))
    (A : C) {B₁ B₂ : D} (g : B₁ ⟶ B₂) (x : (F.obj A).obj B₁) :
    (((natIsoOfPointwiseEquiv F G e h₁ h₂).app A).app B₂).toEquiv ((F.obj A).map g x) =
      (G.obj A).map g ((((natIsoOfPointwiseEquiv F G e h₁ h₂).app A).app B₁).toEquiv x) :=
  h₁ A g x

lemma natIsoOfPointwiseEquiv_naturality₂ {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D ⥤ Type u)
    (e : ∀ (A : C) (B : D), (F.obj A).obj B ≃ (G.obj A).obj B)
    (h₁ : ∀ (A : C) {B₁ B₂ : D} (g : B₁ ⟶ B₂) (x : (F.obj A).obj B₁),
      e A B₂ ((F.obj A).map g x) = (G.obj A).map g (e A B₁ x))
    (h₂ : ∀ {A₁ A₂ : C} (a : A₁ ⟶ A₂) (B : D) (x : (F.obj A₁).obj B),
      e A₂ B ((F.map a).app B x) = (G.map a).app B (e A₁ B x))
    {A₁ A₂ : C} (a : A₁ ⟶ A₂) (B : D) (x : (F.obj A₁).obj B) :
    (((natIsoOfPointwiseEquiv F G e h₁ h₂).app A₂).app B).toEquiv ((F.map a).app B x) =
      (G.map a).app B ((((natIsoOfPointwiseEquiv F G e h₁ h₂).app A₁).app B).toEquiv x) :=
  h₂ a B x

/-- Yoneda-level universal property of the total space, simultaneously natural in both variables. -/
@[expose]
noncomputable def totalSpaceUniversalProperty (X : Scheme.{u}) :
    totalSpacePoints X ≅ pullbackSections X :=
  natIsoOfPointwiseEquiv (totalSpacePoints X) (pullbackSections X)
    (fun E T ↦ totalSpaceHomEquiv₀ E T.unop)
    (fun E _ _ g h ↦ totalSpaceHomEquiv₀_naturality_test E g.unop h)
    (fun a T h ↦ totalSpaceHomEquiv₀_naturality_bundle a T.unop h)

/-- The pointwise equivalence between `X`-morphisms `T ⟶ V(E)` and sections of `T.hom^* E` is the
component of `totalSpaceUniversalProperty`. -/
@[expose]
noncomputable def totalSpaceHomEquiv {X : Scheme.{u}}
    (E : FiniteLocallyFreeSheaf X) (T : Over X) :
    (T ⟶ (affineSchemeOverForget X).obj ((totalSpaceScheme X).obj E)) ≃
      (SheafOfModules.unit T.left.ringCatSheaf ⟶
        (Scheme.Modules.pullback T.hom).obj E.obj) :=
  (((totalSpaceUniversalProperty X).app E).app (op T)).toEquiv

lemma totalSpaceHomEquiv_eq {X : Scheme.{u}}
    (E : FiniteLocallyFreeSheaf X) (T : Over X) :
    totalSpaceHomEquiv E T =
      ((relativeSpecOverPushforwardHomEquiv ((symmetricAlgebra X).obj
        ((dualAsQuasicoherentOp X).obj E).unop) T).trans <|
        (symmetricAlgebraCommMonHomEquiv (FiniteLocallyFreeSheaf.dual E).obj
          T.hom.pushforwardStructureAlgebra).trans <|
        (((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv
          (FiniteLocallyFreeSheaf.dual E).obj (𝟙_ T.left.Modules)).symm).trans <|
        pulledBackDualToSectionEquiv E T.hom) :=
  (natIsoOfPointwiseEquiv_app_app_toEquiv (totalSpacePoints X) (pullbackSections X)
    (fun E T ↦ totalSpaceHomEquiv₀ E T.unop)
    (fun E _ _ g h ↦ totalSpaceHomEquiv₀_naturality_test E g.unop h)
    (fun a T h ↦ totalSpaceHomEquiv₀_naturality_bundle a T.unop h) E (op T)).trans
    (totalSpaceHomEquiv₀_def E T)

theorem totalSpaceHomEquiv_naturality_test {X : Scheme.{u}}
    (E : FiniteLocallyFreeSheaf X) {T T' : Over X} (g : T' ⟶ T)
    (h : T ⟶ (affineSchemeOverForget X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomEquiv E T' (g ≫ h) =
      pullbackSectionMap E.obj g (totalSpaceHomEquiv E T h) :=
  natIsoOfPointwiseEquiv_naturality₁ (totalSpacePoints X) (pullbackSections X)
    (fun E T ↦ totalSpaceHomEquiv₀ E T.unop)
    (fun E _ _ g h ↦ totalSpaceHomEquiv₀_naturality_test E g.unop h)
    (fun a T h ↦ totalSpaceHomEquiv₀_naturality_bundle a T.unop h)
    E g.op h

theorem totalSpaceHomEquiv_naturality_bundle {X : Scheme.{u}}
    {E F : FiniteLocallyFreeSheaf X} (a : E ⟶ F) (T : Over X)
    (h : T ⟶ (affineSchemeOverForget X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomEquiv F T (h ≫ (affineSchemeOverForget X).map ((totalSpaceScheme X).map a)) =
      totalSpaceHomEquiv E T h ≫ (Scheme.Modules.pullback T.hom).map a.hom :=
  natIsoOfPointwiseEquiv_naturality₂ (totalSpacePoints X) (pullbackSections X)
    (fun E T ↦ totalSpaceHomEquiv₀ E T.unop)
    (fun E _ _ g h ↦ totalSpaceHomEquiv₀_naturality_test E g.unop h)
    (fun a T h ↦ totalSpaceHomEquiv₀_naturality_bundle a T.unop h)
    a (op T) h

end TotalSpaceUniversalProperty

section DirectSum

instance {X : Scheme.{u}} : HasBinaryBiproducts (FiniteLocallyFreeSheaf X) :=
  hasBinaryBiproducts_of_finite_biproducts _

instance {X : Scheme.{u}} : HasBinaryProducts (Over X) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- The direct-sum functor `(E, F) ↦ E ⊞ F` on finite locally free sheaves. -/
@[expose]
noncomputable def directSum (X : Scheme.{u}) :
    FiniteLocallyFreeSheaf X × FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf X where
  obj P := P.1 ⊞ P.2
  map f := biprod.map f.1 f.2
  map_id P := by apply biprod.hom_ext <;> simp
  map_comp f g := by apply biprod.hom_ext <;> simp

@[simp]
lemma directSum_obj {X : Scheme.{u}} (E F : FiniteLocallyFreeSheaf X) :
    (directSum X).obj (E, F) = (E ⊞ F) :=
  (rfl)

/-- Sections of `T.hom^* (E ⊞ F)` correspond bijectively to pairs of sections of `T.hom^* E` and
`T.hom^* F`. -/
@[expose]
noncomputable def pulledBackBiprodSectionEquiv {X : Scheme.{u}} (E F : FiniteLocallyFreeSheaf X)
    (T : Over X) :
    (𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj (E ⊞ F).obj) ≃
      (𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj E.obj) ×
        (𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj F.obj) where
  toFun s :=
    (s ≫ (Scheme.Modules.pullback T.hom).map (biprod.fst : E ⊞ F ⟶ E).hom,
      s ≫ (Scheme.Modules.pullback T.hom).map (biprod.snd : E ⊞ F ⟶ F).hom)
  invFun p :=
    p.1 ≫ (Scheme.Modules.pullback T.hom).map (biprod.inl : E ⟶ E ⊞ F).hom +
      p.2 ≫ (Scheme.Modules.pullback T.hom).map (biprod.inr : F ⟶ E ⊞ F).hom
  left_inv s := by
    dsimp only
    have htotal : (biprod.fst : E ⊞ F ⟶ E).hom ≫ (biprod.inl : E ⟶ E ⊞ F).hom +
        (biprod.snd : E ⊞ F ⟶ F).hom ≫ (biprod.inr : F ⟶ E ⊞ F).hom = 𝟙 (E ⊞ F).obj :=
      congrArg InducedCategory.Hom.hom (biprod.total :
        (biprod.fst : E ⊞ F ⟶ E) ≫ biprod.inl + (biprod.snd : E ⊞ F ⟶ F) ≫ biprod.inr = 𝟙 (E ⊞ F))
    rw [assoc, assoc, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← Preadditive.comp_add, ← Functor.map_add, htotal,
      CategoryTheory.Functor.map_id, comp_id]
  right_inv p := by
    have h11 : (biprod.inl : E ⟶ E ⊞ F).hom ≫ (biprod.fst : E ⊞ F ⟶ E).hom = 𝟙 E.obj :=
      congrArg InducedCategory.Hom.hom (biprod.inl_fst : (biprod.inl : E ⟶ E ⊞ F) ≫ biprod.fst = _)
    have h12 : (biprod.inl : E ⟶ E ⊞ F).hom ≫ (biprod.snd : E ⊞ F ⟶ F).hom = 0 :=
      congrArg InducedCategory.Hom.hom (biprod.inl_snd : (biprod.inl : E ⟶ E ⊞ F) ≫ biprod.snd = _)
    have h21 : (biprod.inr : F ⟶ E ⊞ F).hom ≫ (biprod.fst : E ⊞ F ⟶ E).hom = 0 :=
      congrArg InducedCategory.Hom.hom (biprod.inr_fst : (biprod.inr : F ⟶ E ⊞ F) ≫ biprod.fst = _)
    have h22 : (biprod.inr : F ⟶ E ⊞ F).hom ≫ (biprod.snd : E ⊞ F ⟶ F).hom = 𝟙 F.obj :=
      congrArg InducedCategory.Hom.hom (biprod.inr_snd : (biprod.inr : F ⟶ E ⊞ F) ≫ biprod.snd = _)
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [Preadditive.add_comp, assoc, assoc, ← CategoryTheory.Functor.map_comp,
        ← CategoryTheory.Functor.map_comp, h11, h21, CategoryTheory.Functor.map_id,
        Functor.map_zero, comp_id, comp_zero, add_zero]
    · dsimp only
      rw [Preadditive.add_comp, assoc, assoc, ← CategoryTheory.Functor.map_comp,
        ← CategoryTheory.Functor.map_comp, h12, h22, Functor.map_zero,
        CategoryTheory.Functor.map_id, comp_zero, comp_id, zero_add]

/-- Morphisms into a binary product `A ⨯ B` correspond bijectively to pairs of morphisms into `A`
and `B`. -/
@[expose]
noncomputable def prodHomEquiv {C : Type*} [Category C] [HasBinaryProducts C] (T A B : C) :
    (T ⟶ Limits.prod A B) ≃ (T ⟶ A) × (T ⟶ B) where
  toFun f := (f ≫ Limits.prod.fst, f ≫ Limits.prod.snd)
  invFun p := Limits.prod.lift p.1 p.2
  left_inv f := by ext <;> simp
  right_inv p := Prod.ext (Limits.prod.lift_fst _ _) (Limits.prod.lift_snd _ _)

/-- The total space of a direct sum `E ⊞ F` is canonically isomorphic in `Over X` to the fiber
product `V(E) ×_X V(F)`. -/
@[expose]
noncomputable def totalSpaceDirectSumIso {X : Scheme.{u}}
    (E F : FiniteLocallyFreeSheaf X) :
    (affineSchemeOverForget X).obj
        ((totalSpaceScheme X).obj ((directSum X).obj (E, F))) ≅
      Limits.prod
        ((affineSchemeOverForget X).obj ((totalSpaceScheme X).obj E))
        ((affineSchemeOverForget X).obj ((totalSpaceScheme X).obj F)) :=
  let G := totalSpaceScheme X ⋙ affineSchemeOverForget X
  let φ : G.obj ((directSum X).obj (E, F)) ⟶ Limits.prod (G.obj E) (G.obj F) :=
    Limits.prod.lift (G.map (biprod.fst : E ⊞ F ⟶ E)) (G.map (biprod.snd : E ⊞ F ⟶ F))
  have hφ : IsIso (yoneda.map φ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [isIso_iff_bijective]
    let e : (T.unop ⟶ G.obj ((directSum X).obj (E, F))) ≃
        (T.unop ⟶ Limits.prod (G.obj E) (G.obj F)) :=
      (totalSpaceHomEquiv (E ⊞ F) T.unop).trans <|
        (pulledBackBiprodSectionEquiv E F T.unop).trans <|
        ((totalSpaceHomEquiv E T.unop).prodCongr (totalSpaceHomEquiv F T.unop)).symm.trans <|
        (prodHomEquiv T.unop (G.obj E) (G.obj F)).symm
    have he : ∀ h : T.unop ⟶ G.obj ((directSum X).obj (E, F)),
        (yoneda.map φ).app T h = e h := by
      intro h
      have h1 := (totalSpaceHomEquiv_naturality_bundle (biprod.fst : E ⊞ F ⟶ E) T.unop h).symm
      have h2 := (totalSpaceHomEquiv_naturality_bundle (biprod.snd : E ⊞ F ⟶ F) T.unop h).symm
      change h ≫ Limits.prod.lift (G.map (biprod.fst : E ⊞ F ⟶ E))
          (G.map (biprod.snd : E ⊞ F ⟶ F)) =
        Limits.prod.lift
          ((totalSpaceHomEquiv E T.unop).symm
            (totalSpaceHomEquiv (E ⊞ F) T.unop h ≫
              (Scheme.Modules.pullback T.unop.hom).map (biprod.fst : E ⊞ F ⟶ E).hom))
          ((totalSpaceHomEquiv F T.unop).symm
            (totalSpaceHomEquiv (E ⊞ F) T.unop h ≫
              (Scheme.Modules.pullback T.unop.hom).map (biprod.snd : E ⊞ F ⟶ F).hom))
      rw [h1, h2, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact Limits.prod.comp_lift h (G.map (biprod.fst : E ⊞ F ⟶ E))
        (G.map (biprod.snd : E ⊞ F ⟶ F))
    have hfun : ((yoneda.map φ).app T : (T.unop ⟶ G.obj ((directSum X).obj (E, F))) → _) = e :=
      funext he
    rw [hfun]
    exact e.bijective
  letI : IsIso φ := isIso_of_fully_faithful yoneda φ
  asIso φ

end DirectSum

end

end TauCeti.AlgebraicGeometry
