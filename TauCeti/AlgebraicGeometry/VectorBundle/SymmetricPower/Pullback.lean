/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent
public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover
public import TauCeti.AlgebraicGeometry.VectorBundle.SymmetricPower.Basic

/-!
# Pullback of symmetric powers of finite locally free sheaves

For a morphism of schemes `f : X ⟶ Y` and `n : ℕ`, the canonical pullback comparison
`f^* (Symⁿ M) ⟶ Symⁿ (f^* M)` (`Scheme.Modules.pullbackSymmetricPowerComparison f n`) is an
isomorphism when `f` is an open immersion
(`Scheme.Modules.isIso_pullbackSymmetricPowerComparison_of_isOpenImmersion`), and is an isomorphism
for every finite locally free `𝒪_Y`-module `M` along any morphism of schemes
(`Scheme.Modules.isIso_pullbackSymmetricPowerComparison_of_isFiniteLocallyFree`).

Restricting to the category `FiniteLocallyFreeSheaf` yields the natural isomorphism
`FiniteLocallyFreeSheaf.pullbackSymmetricPowerNatIso f n :
  symmetricPower Y n ⋙ pullback f ≅ pullback f ⋙ symmetricPower X n`
with components `FiniteLocallyFreeSheaf.pullbackSymmetricPowerIso f n E`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.pullbackSymmetricPowerComparison`: the canonical natural
  transformation `symmetricPower Y.sheaf n ⋙ pullback f ⟶ pullback f ⋙ symmetricPower X.sheaf n`;
* `AlgebraicGeometry.Scheme.Modules.isIso_pullbackSymmetricPowerComparison_of_isOpenImmersion`:
  invertibility along an open immersion;
* `AlgebraicGeometry.Scheme.Modules.isIso_pullbackSymmetricPowerComparison_of_isFiniteLocallyFree`:
  invertibility on finite locally free modules along any scheme morphism;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pullbackSymmetricPowerIso`: the component
  isomorphism `(pullback f).obj ((symmetricPower Y n).obj E) ≅
    (symmetricPower X n).obj ((pullback f).obj E)`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pullbackSymmetricPowerNatIso`: the natural
  isomorphism `symmetricPower Y n ⋙ pullback f ≅ pullback f ⋙ symmetricPower X n`.
-/

public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical comparison `f^* (Symⁿ M) ⟶ Symⁿ (f^* M)` for `𝒪_Y`-modules along a morphism of
schemes `f : X ⟶ Y`, obtained as the mate of `SheafOfModules.pushforwardSymmetricPowerComparison`
under the pullback--pushforward adjunction. -/
@[expose]
def pullbackSymmetricPowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    SheafOfModules.symmetricPower Y.sheaf n ⋙ pullback f ⟶
      pullback f ⋙ SheafOfModules.symmetricPower X.sheaf n :=
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  SheafOfModules.pullbackSymmetricPowerComparison (S := Y.sheaf) (R := X.sheaf)
    f.toRingCatSheafHom n

/-- Compatibility of `pullbackSymmetricPowerComparison` with composition of scheme morphisms. -/
theorem pullback_comp_pullbackSymmetricPowerComparison {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (M : Z.Modules) :
    (pullbackSymmetricPowerComparison (f ≫ g) n).app M =
      (pullbackComp f g).inv.app ((SheafOfModules.symmetricPower Z.sheaf n).obj M) ≫
        (pullback f).map ((pullbackSymmetricPowerComparison g n).app M) ≫
        (pullbackSymmetricPowerComparison f n).app ((pullback g).obj M) ≫
        (SheafOfModules.symmetricPower X.sheaf n).map ((pullbackComp f g).hom.app M) :=
  have : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward g).IsRightAdjoint
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  SheafOfModules.pullback_comp_pullbackSymmetricPowerComparison
    (S := Z.sheaf) (R := Y.sheaf) (T := X.sheaf) g.toRingCatSheafHom f.toRingCatSheafHom n M

/-- Pullback along an open immersion of schemes commutes with symmetric powers for all sheaves of
modules. -/
instance isIso_pullbackSymmetricPowerComparison_of_isOpenImmersion
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (n : ℕ) (M : Y.Modules) :
    IsIso ((pullbackSymmetricPowerComparison j n).app M) := by
  have : (SheafOfModules.pushforward.{u} j.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward j).IsRightAdjoint
  refine SheafOfModules.isIso_pullbackSymmetricPowerComparison_of_adjunction
    (S := U.sheaf) (R := Y.sheaf) (restrictRingCatSheafHom j)
    (show j.opensFunctor ⊣ TopologicalSpace.Opens.map j.base from
      j.isOpenEmbedding.isOpenMap.adjunction)
    j.toRingCatSheafHom ?_ ?_ n M
  · ext W x
    congrm $((j.app_appIso_inv _).symm).hom x
  · ext W x
    have : (j.appIso W.unop).inv ≫ j.app _ ≫
        U.presheaf.map (eqToHom (j.preimage_image_eq W.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← U.presheaf.map_id]
      rfl
    congrm $this x

private theorem isIso_app_of_iso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (α : F ⟶ G) {A B : C} (e : A ≅ B) [IsIso (α.app B)] :
    IsIso (α.app A) := by
  have : α.app A = F.map e.hom ≫ α.app B ≫ G.map e.inv := by
    rw [α.naturality_assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]
  rw [this]
  infer_instance

private theorem isIso_of_comp_iso {C : Type*} [Category* C]
    {X₁ X₂ X₃ X₄ X₅ : C} {φ : X₂ ⟶ X₄} (i₁ : X₁ ≅ X₂)
    (f₁ : X₁ ⟶ X₃) (f₂ : X₃ ⟶ X₅) (i₂ : X₅ ≅ X₄)
    (h : φ = i₁.inv ≫ f₁ ≫ f₂ ≫ i₂.hom) [IsIso f₁] [IsIso f₂] :
    IsIso φ := by
  subst h
  infer_instance

private theorem isIso_left_of_comp_iso {C : Type*} [Category* C]
    {X₁ X₂ X₃ X₄ X₅ : C} {φ : X₂ ⟶ X₄} (i₁ : X₁ ≅ X₂)
    (f₁ : X₁ ⟶ X₃) (f₂ : X₃ ⟶ X₅) (i₂ : X₅ ≅ X₄)
    (h : φ = i₁.inv ≫ f₁ ≫ f₂ ≫ i₂.hom) [IsIso φ] [IsIso f₂] :
    IsIso f₁ := by
  have : f₁ = i₁.hom ≫ φ ≫ i₂.inv ≫ inv f₂ := by
    subst h
    simp
  rw [this]
  infer_instance

private theorem isIso_pullbackSymmetricPowerComparison_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (n : ℕ) (M : Y.Modules)
    [IsIso ((pullbackSymmetricPowerComparison g n).app M)] :
    IsIso ((pullbackSymmetricPowerComparison f n).app M) := by
  subst h
  infer_instance

/-- Pullback along any morphism of schemes commutes with symmetric powers on finite locally free
modules: checked locally on an open cover of the target on which the module is finite free. -/
theorem isIso_pullbackSymmetricPowerComparison_of_isFiniteLocallyFree
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (M : Y.Modules) (hM : isFiniteLocallyFree Y M) :
    IsIso ((pullbackSymmetricPowerComparison f n).app M) := by
  obtain ⟨q, hq, hq'⟩ :=
    (SheafOfModules.isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType M).mp hM
  refine (isIso_iff_of_isOpenCover
    (TopologicalSpace.IsOpenCover.comap ((_root_.Opens.coversTop_iff _ q.X).mp
      q.coversTop) f.base.hom) _).mpr fun i ↦ ?_
  let U : Y.Opens := q.X i
  have : Finite (q.generators i).I := (hq'.isFiniteType i).finite
  have := hq.isIso i
  let e : (pullback U.ι).obj M ≅ SheafOfModules.free (q.generators i).I :=
    ((restrictFunctorIsoPullback U.ι).app M).symm ≪≫
      restrictIsoFreeOfOverIsoFree M U (asIso (q.generators i).π).symm
  have : (SheafOfModules.pushforward.{u} (f ∣_ U).toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward (f ∣_ U)).IsRightAdjoint
  have hfree : IsIso ((pullbackSymmetricPowerComparison (f ∣_ U) n).app
      (SheafOfModules.free (q.generators i).I)) :=
    SheafOfModules.isIso_pullbackSymmetricPowerComparison_free (S := U.toScheme.sheaf)
      (R := (f ⁻¹ᵁ U).toScheme.sheaf) (f ∣_ U).toRingCatSheafHom (q.generators i).I n
  have hU : IsIso ((pullbackSymmetricPowerComparison (f ∣_ U) n).app ((pullback U.ι).obj M)) :=
    isIso_app_of_iso (pullbackSymmetricPowerComparison (f ∣_ U) n) e
  have hg : IsIso ((pullbackSymmetricPowerComparison (f ∣_ U ≫ U.ι) n).app M) :=
    isIso_of_comp_iso
      ((pullbackComp (f ∣_ U) U.ι).app ((SheafOfModules.symmetricPower Y.sheaf n).obj M))
      ((pullback (f ∣_ U)).map ((pullbackSymmetricPowerComparison U.ι n).app M))
      ((pullbackSymmetricPowerComparison (f ∣_ U) n).app ((pullback U.ι).obj M))
      ((SheafOfModules.symmetricPower (f ⁻¹ᵁ U).toScheme.sheaf n).mapIso
        ((pullbackComp (f ∣_ U) U.ι).app M))
      (pullback_comp_pullbackSymmetricPowerComparison (f ∣_ U) U.ι n M)
  have hg' : IsIso ((pullbackSymmetricPowerComparison ((f ⁻¹ᵁ U).ι ≫ f) n).app M) :=
    isIso_pullbackSymmetricPowerComparison_congr (morphismRestrict_ι f U).symm n M
  exact isIso_left_of_comp_iso
    ((pullbackComp (f ⁻¹ᵁ U).ι f).app ((SheafOfModules.symmetricPower Y.sheaf n).obj M))
    ((pullback (f ⁻¹ᵁ U).ι).map ((pullbackSymmetricPowerComparison f n).app M))
    ((pullbackSymmetricPowerComparison (f ⁻¹ᵁ U).ι n).app ((pullback f).obj M))
    ((SheafOfModules.symmetricPower (f ⁻¹ᵁ U).toScheme.sheaf n).mapIso
      ((pullbackComp (f ⁻¹ᵁ U).ι f).app M))
    (pullback_comp_pullbackSymmetricPowerComparison (f ⁻¹ᵁ U).ι f n M)

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

variable {X Y : _root_.AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Pullback commutes with symmetric powers of a finite free sheaf, by identifying both sides with
the free sheaf on degree-`n` multisets in the basis. -/
noncomputable def pullbackSymmetricPowerFreeIso (I : Type u) [Finite I] (n : ℕ) :
    (pullback f).obj ((symmetricPower Y n).obj (free Y I)) ≅
      (symmetricPower X n).obj ((pullback f).obj (free Y I)) := by
  classical
  let eY : (symmetricPower Y n).obj (free Y I) ≅ free Y (Sym I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by simp only [symmetricPower_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.symmetricPowerFreeIso (R := Y.sheaf) I n ≪≫
        eqToIso (free_obj Y (Sym I n)).symm)
  let eX : (symmetricPower X n).obj (free X I) ≅ free X (Sym I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by simp only [symmetricPower_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.symmetricPowerFreeIso (R := X.sheaf) I n ≪≫
        eqToIso (free_obj X (Sym I n)).symm)
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let pI : (pullback f).obj (free Y I) ≅ free X I :=
    ObjectProperty.isoMk _
      (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I ≪≫
        eqToIso (free_obj X I).symm)
  let pSym : (pullback f).obj (free Y (Sym I n)) ≅ free X (Sym I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Sym I n) ≪≫
        eqToIso (free_obj X (Sym I n)).symm)
  exact ((pullback f).mapIso eY ≪≫ pSym) ≪≫
    ((symmetricPower X n).mapIso pI ≪≫ eX).symm

/-- The forward map of the pullback comparison is the composite of the free-sheaf
identifications on both sides. -/
theorem pullbackSymmetricPowerFreeIso_hom (I : Type u) [Finite I] (n : ℕ) :
    (pullbackSymmetricPowerFreeIso f I n).hom =
      (let eY : (symmetricPower Y n).obj (free Y I) ≅ free Y (Sym I n) :=
          ObjectProperty.isoMk _
            (eqToIso (by simp only [symmetricPower_obj_obj, free_obj]; rfl) ≪≫
              SheafOfModules.symmetricPowerFreeIso (R := Y.sheaf) I n ≪≫
              eqToIso (free_obj Y (Sym I n)).symm)
       let eX : (symmetricPower X n).obj (free X I) ≅ free X (Sym I n) :=
          ObjectProperty.isoMk _
            (eqToIso (by simp only [symmetricPower_obj_obj, free_obj]; rfl) ≪≫
              SheafOfModules.symmetricPowerFreeIso (R := X.sheaf) I n ≪≫
              eqToIso (free_obj X (Sym I n)).symm)
       letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
          inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
       let pI : (pullback f).obj (free Y I) ≅ free X I :=
          ObjectProperty.isoMk _
            (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
              SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I ≪≫
              eqToIso (free_obj X I).symm)
       let pSym : (pullback f).obj (free Y (Sym I n)) ≅ free X (Sym I n) :=
          ObjectProperty.isoMk _
            (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
              SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Sym I n) ≪≫
              eqToIso (free_obj X (Sym I n)).symm)
       (((pullback f).mapIso eY ≪≫ pSym) ≪≫
         ((symmetricPower X n).mapIso pI ≪≫ eX).symm).hom) := by
  classical
  rfl

/-- The module-level symmetric power pullback comparison is an isomorphism on every finite locally
free sheaf. -/
instance isIso_pullbackSymmetricPowerComparison (n : ℕ) (E : FiniteLocallyFreeSheaf Y) :
    IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app E.obj) :=
  Scheme.Modules.isIso_pullbackSymmetricPowerComparison_of_isFiniteLocallyFree f n E.obj E.property

/-- Pulling back the `n`-th symmetric power of a finite locally free sheaf is canonically
isomorphic to the `n`-th symmetric power of its pullback. -/
def pullbackSymmetricPowerIso (n : ℕ) (E : FiniteLocallyFreeSheaf Y) :
    (pullback f).obj ((symmetricPower Y n).obj E) ≅
      (symmetricPower X n).obj ((pullback f).obj E) :=
  ObjectProperty.isoMk _
    (eqToIso (by rw [pullback_obj_obj, symmetricPower_obj_obj]; rfl) ≪≫
      asIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app E.obj) ≪≫
      eqToIso (by rw [symmetricPower_obj_obj, pullback_obj_obj]; rfl))

/-- On underlying sheaves of modules, `pullbackSymmetricPowerIso` is the canonical comparison
`Scheme.Modules.pullbackSymmetricPowerComparison`. -/
@[simp]
theorem pullbackSymmetricPowerIso_hom_hom (n : ℕ) (E : FiniteLocallyFreeSheaf Y) :
    (pullbackSymmetricPowerIso f n E).hom.hom =
      eqToHom (by rw [pullback_obj_obj, symmetricPower_obj_obj]; rfl) ≫
        (Scheme.Modules.pullbackSymmetricPowerComparison f n).app E.obj ≫
        eqToHom (by rw [symmetricPower_obj_obj, pullback_obj_obj]; rfl) := by
  simp [pullbackSymmetricPowerIso]

private theorem naturality_of_eqToHom {C D : Type*} [Category* C] [Category* D]
    (F₁ : C ⥤ C) (F₂ : D ⥤ D) (P : C ⥤ D) (α : F₁ ⋙ P ⟶ P ⋙ F₂)
    {E F : C} (g : E ⟶ F)
    {FE FF : C} (hFE : FE = F₁.obj E) (hFF : FF = F₁.obj F)
    {PE PF : D} (hPE : PE = P.obj E) (hPF : PF = P.obj F)
    {PFE PFF FPE FPF : D}
    (hPFE : PFE = (F₁ ⋙ P).obj E) (hPFF : PFF = (F₁ ⋙ P).obj F)
    (hFPE : (P ⋙ F₂).obj E = FPE) (hFPF : (P ⋙ F₂).obj F = FPF)
    (hPFE' : PFE = P.obj FE) (hPFF' : PFF = P.obj FF)
    (hFPE' : FPE = F₂.obj PE) (hFPF' : FPF = F₂.obj PF) :
    (eqToHom hPFE' ≫ P.map (eqToHom hFE ≫ F₁.map g ≫ eqToHom hFF.symm) ≫ eqToHom hPFF'.symm) ≫
        (eqToHom hPFF ≫ α.app F ≫ eqToHom hFPF) =
      (eqToHom hPFE ≫ α.app E ≫ eqToHom hFPE) ≫
        (eqToHom hFPE' ≫ F₂.map (eqToHom hPE ≫ P.map g ≫ eqToHom hPF.symm) ≫
          eqToHom hFPF'.symm) := by
  subst hFE hFF hPE hPF hPFE hPFF hFPE hFPF
  simpa using α.naturality g

/-- The symmetric power pullback isomorphism is natural in maps of finite locally free sheaves. -/
@[reassoc]
theorem pullbackSymmetricPowerIso_naturality (n : ℕ) {E F : FiniteLocallyFreeSheaf Y} (g : E ⟶ F) :
    (pullback f).map ((symmetricPower Y n).map g) ≫ (pullbackSymmetricPowerIso f n F).hom =
      (pullbackSymmetricPowerIso f n E).hom ≫ (symmetricPower X n).map ((pullback f).map g) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullback_map_hom, symmetricPower_map_hom,
    pullbackSymmetricPowerIso_hom_hom]
  exact naturality_of_eqToHom (SheafOfModules.symmetricPower Y.sheaf n)
    (SheafOfModules.symmetricPower X.sheaf n) (Scheme.Modules.pullback f)
    (Scheme.Modules.pullbackSymmetricPowerComparison f n) g.hom
    (symmetricPower_obj_obj n E) (symmetricPower_obj_obj n F)
    (pullback_obj_obj f E) (pullback_obj_obj f F)
    _ _ _ _
    (pullback_obj_obj f ((symmetricPower Y n).obj E))
    (pullback_obj_obj f ((symmetricPower Y n).obj F))
    (symmetricPower_obj_obj n ((pullback f).obj E))
    (symmetricPower_obj_obj n ((pullback f).obj F))

/-- Pulling back `n`-th symmetric powers of finite locally free sheaves is naturally isomorphic to
taking `n`-th symmetric powers of their pullbacks. -/
def pullbackSymmetricPowerNatIso (n : ℕ) :
    symmetricPower Y n ⋙ pullback f ≅ pullback f ⋙ symmetricPower X n :=
  NatIso.ofComponents (pullbackSymmetricPowerIso f n)
    fun g ↦ pullbackSymmetricPowerIso_naturality f n g

/-- The forward component of `pullbackSymmetricPowerNatIso` is `pullbackSymmetricPowerIso`. -/
@[simp]
theorem pullbackSymmetricPowerNatIso_hom_app (n : ℕ) (E : FiniteLocallyFreeSheaf Y) :
    (pullbackSymmetricPowerNatIso f n).hom.app E = (pullbackSymmetricPowerIso f n E).hom :=
  (rfl)

/-- The inverse component of `pullbackSymmetricPowerNatIso` is `pullbackSymmetricPowerIso`. -/
@[simp]
theorem pullbackSymmetricPowerNatIso_inv_app (n : ℕ) (E : FiniteLocallyFreeSheaf Y) :
    (pullbackSymmetricPowerNatIso f n).inv.app E = (pullbackSymmetricPowerIso f n E).inv :=
  (rfl)

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

end
