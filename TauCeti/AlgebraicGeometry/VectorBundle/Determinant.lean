/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank

/-!
# The determinant of a vector bundle of fixed rank

If `E` is a finite locally free sheaf on a scheme `X` of constant rank `r`, its top exterior power
`det E = ⋀ʳ E` has rank `r.choose r = 1` at every point, so it is an invertible sheaf. This file
packages the top exterior power as the determinant functor
`FiniteLocallyFreeSheaf.determinant X r : FixedRank X r ⥤ InvertibleSheaf X`, proves that it
commutes with pullback along morphisms of schemes (`pullbackDeterminantIso`,
`pullbackDeterminantNatIso`), and computes it in the basic cases: the determinant of the free sheaf
of rank `r` is the trivial line bundle, the determinant of a sheaf of constant rank one is the
sheaf itself, and every sheaf of rank zero has trivial determinant.

## Main declarations

* `FiniteLocallyFreeSheaf.determinant X r`: the determinant `E ↦ ⋀ʳ E` of finite locally free
  sheaves of constant rank `r`, with values in invertible sheaves;
* `FiniteLocallyFreeSheaf.pullbackDeterminantIso`: the component isomorphism comparing the
  pullback of the determinant with the determinant of the pullback;
* `FiniteLocallyFreeSheaf.pullbackDeterminantNatIso`: the natural isomorphism
  `determinant Y r ⋙ InvertibleSheaf.pullback f ≅ FixedRank.pullback f ⋙ determinant X r`;
* `FiniteLocallyFreeSheaf.determinantFreeIso`: the determinant of the free sheaf of rank `r` is
  the trivial invertible sheaf;
* `FiniteLocallyFreeSheaf.determinantOneIso`: on sheaves of constant rank one, the determinant is
  naturally the sheaf itself, as a finite locally free sheaf;
* `FiniteLocallyFreeSheaf.determinantZeroIso`: in rank zero, the determinant is naturally the
  trivial invertible sheaf.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocallyFreeSheaf

variable (X : Scheme.{u})

/-- The determinant of finite locally free sheaves of constant rank `r` on `X`: the top exterior
power `E ↦ ⋀ʳ E` of the underlying `𝒪_X`-modules, which has rank `r.choose r = 1` everywhere and
so is an invertible sheaf. -/
def determinant (r : ℕ) : FixedRank X r ⥤ InvertibleSheaf X :=
  (SheafOfModules.isInvertible X).lift
    (FixedRank.toFiniteLocallyFree X r ⋙ (Scheme.Modules.isFiniteLocallyFree X).ι ⋙
      SheafOfModules.exteriorPower X.sheaf r)
    fun E ↦ exteriorPower_obj_obj r E.obj ▸
      (isInvertible_iff_forall_rank_eq_one ((exteriorPower X r).obj E.obj)).mpr fun x ↦ by
        rw [rank_exteriorPower_apply, FixedRank.rank_apply, Nat.choose_self]

variable {X}

/-- The underlying sheaf of the determinant of a sheaf `E` of constant rank `r` is the `r`-th
exterior power of the underlying `𝒪_X`-module of `E`. -/
@[simp]
theorem determinant_obj_obj {r : ℕ} (E : FixedRank X r) :
    ((determinant X r).obj E).obj = (SheafOfModules.exteriorPower X.sheaf r).obj E.obj.obj :=
  (rfl)

/-- The determinant acts on a morphism of sheaves of constant rank `r` by the `r`-th exterior
power of the underlying morphism of `𝒪_X`-modules. -/
@[simp]
theorem determinant_map_hom {r : ℕ} {E F : FixedRank X r} (φ : E ⟶ F) :
    ((determinant X r).map φ).hom =
      eqToHom (determinant_obj_obj E) ≫ (SheafOfModules.exteriorPower X.sheaf r).map φ.hom.hom ≫
        eqToHom (determinant_obj_obj F).symm :=
  -- Both `eqToHom`s are identities, since `determinant` is a lift of the exterior power; they only
  -- record `determinant_obj_obj`, which is not a syntactic equality outside this file.
  ((Category.id_comp _).trans (Category.comp_id _)).symm

variable {Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)

/-- Pulling back the determinant of a finite locally free sheaf of constant rank `r` is
canonically isomorphic to the determinant of its pullback. -/
def pullbackDeterminantIso (E : FixedRank Y r) :
    (InvertibleSheaf.pullback f).obj ((determinant Y r).obj E) ≅
      (determinant X r).obj ((FixedRank.pullback f).obj E) :=
  ObjectProperty.isoMk _
    (eqToIso (by rw [InvertibleSheaf.pullback_obj_obj, determinant_obj_obj]; rfl) ≪≫
      asIso ((Scheme.Modules.pullbackExteriorPowerComparison f r).app E.obj.obj) ≪≫
      eqToIso (by rw [determinant_obj_obj, FixedRank.pullback_obj_obj, pullback_obj_obj]; rfl))

/-- On underlying sheaves of modules, `pullbackDeterminantIso` is the top exterior power pullback
comparison `Scheme.Modules.pullbackExteriorPowerComparison`. -/
@[simp]
theorem pullbackDeterminantIso_hom_hom (E : FixedRank Y r) :
    (pullbackDeterminantIso f r E).hom.hom =
      eqToHom (by rw [InvertibleSheaf.pullback_obj_obj, determinant_obj_obj]; rfl) ≫
        (Scheme.Modules.pullbackExteriorPowerComparison f r).app E.obj.obj ≫
        eqToHom
          (by rw [determinant_obj_obj, FixedRank.pullback_obj_obj, pullback_obj_obj]; rfl) := by
  simp [pullbackDeterminantIso]

private theorem determinant_naturality_aux {C D : Type*} [Category* C] [Category* D]
    (F₁ : C ⥤ C) (F₂ : D ⥤ D) (P : C ⥤ D) (α : F₁ ⋙ P ⟶ P ⋙ F₂)
    {E F : C} (g : E ⟶ F)
    {DE DF : C} (hDE : DE = F₁.obj E) (hDF : DF = F₁.obj F)
    {PE PF : D} (hPE : PE = P.obj E) (hPF : PF = P.obj F)
    {RPE RPF : D} (hRPE : RPE = PE) (hRPF : RPF = PF)
    {PDE PDF DRPE DRPF : D}
    (hPDE : PDE = (F₁ ⋙ P).obj E) (hPDF : PDF = (F₁ ⋙ P).obj F)
    (hDRPE : (P ⋙ F₂).obj E = DRPE) (hDRPF : (P ⋙ F₂).obj F = DRPF)
    (hPDE' : PDE = P.obj DE) (hPDF' : PDF = P.obj DF)
    (hDRPE' : DRPE = F₂.obj RPE) (hDRPF' : DRPF = F₂.obj RPF) :
    (eqToHom hPDE' ≫ P.map (eqToHom hDE ≫ F₁.map g ≫ eqToHom hDF.symm) ≫ eqToHom hPDF'.symm) ≫
        (eqToHom hPDF ≫ α.app F ≫ eqToHom hDRPF) =
      (eqToHom hPDE ≫ α.app E ≫ eqToHom hDRPE) ≫
        (eqToHom hDRPE' ≫
          F₂.map (eqToHom hRPE ≫ (eqToHom hPE ≫ P.map g ≫ eqToHom hPF.symm) ≫ eqToHom hRPF.symm) ≫
          eqToHom hDRPF'.symm) := by
  subst hDE hDF hRPE hRPF hPE hPF hPDE hPDF hDRPE hDRPF
  simpa using α.naturality g

/-- The determinant pullback comparison is natural in morphisms of fixed-rank sheaves. -/
@[reassoc]
theorem pullbackDeterminantIso_naturality {E F : FixedRank Y r} (g : E ⟶ F) :
    (InvertibleSheaf.pullback f).map ((determinant Y r).map g) ≫
        (pullbackDeterminantIso f r F).hom =
      (pullbackDeterminantIso f r E).hom ≫
        (determinant X r).map ((FixedRank.pullback f).map g) := by
  have hEq {A B : FiniteLocallyFreeSheaf X} (h : A = B) :
      (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
    subst h
    rfl
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, InvertibleSheaf.pullback_map,
    determinant_map_hom, pullbackDeterminantIso_hom_hom, FixedRank.pullback_map_hom,
    pullback_map_hom, hEq]
  exact determinant_naturality_aux (SheafOfModules.exteriorPower Y.sheaf r)
    (SheafOfModules.exteriorPower X.sheaf r) (Scheme.Modules.pullback f)
    (Scheme.Modules.pullbackExteriorPowerComparison f r) g.hom.hom
    (determinant_obj_obj E) (determinant_obj_obj F)
    (pullback_obj_obj f E.obj) (pullback_obj_obj f F.obj)
    (congrArg ObjectProperty.FullSubcategory.obj (FixedRank.pullback_obj_obj f E))
    (congrArg ObjectProperty.FullSubcategory.obj (FixedRank.pullback_obj_obj f F))
    _ _ _ _
    (InvertibleSheaf.pullback_obj_obj f ((determinant Y r).obj E))
    (InvertibleSheaf.pullback_obj_obj f ((determinant Y r).obj F))
    (determinant_obj_obj ((FixedRank.pullback f).obj E))
    (determinant_obj_obj ((FixedRank.pullback f).obj F))

/-- Pulling back determinants of fixed-rank finite locally free sheaves is naturally isomorphic to
taking determinants of their pullbacks. -/
def pullbackDeterminantNatIso :
    determinant Y r ⋙ InvertibleSheaf.pullback f ≅ FixedRank.pullback f ⋙ determinant X r :=
  NatIso.ofComponents (pullbackDeterminantIso f r)
    fun g ↦ pullbackDeterminantIso_naturality f r g

/-- The forward component of `pullbackDeterminantNatIso` is `pullbackDeterminantIso`. -/
@[simp]
theorem pullbackDeterminantNatIso_hom_app (E : FixedRank Y r) :
    (pullbackDeterminantNatIso f r).hom.app E = (pullbackDeterminantIso f r E).hom :=
  (rfl)

/-- The inverse component of `pullbackDeterminantNatIso` is `pullbackDeterminantIso`. -/
@[simp]
theorem pullbackDeterminantNatIso_inv_app (E : FixedRank Y r) :
    (pullbackDeterminantNatIso f r).inv.app E = (pullbackDeterminantIso f r E).inv :=
  (rfl)

variable (X) in
/-- The determinant of the free sheaf of rank `r` is the trivial invertible sheaf: the top
exterior power of the free sheaf on `Fin r` is free on its single `r`-element subset. -/
def determinantFreeIso (r : ℕ) :
    (determinant X r).obj (FixedRank.free X r) ≅ InvertibleSheaf.trivial X :=
  -- `Fin r` has exactly one `r`-element subset, so the free sheaf on these subsets is the free
  -- sheaf on one generator.
  have h := Nat.card_eq_one_iff_unique.mp (by
    rw [Set.powersetCard.card, Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin,
      Nat.choose_self] : Nat.card (Set.powersetCard (ULift.{u} (Fin r)) r) = 1)
  have := h.1
  ObjectProperty.isoMk _ (eqToIso (by rw [determinant_obj_obj, FixedRank.free_obj, free_obj]) ≪≫
    SheafOfModules.exteriorPowerFreeIso (R := X.sheaf) (ULift.{u} (Fin r)) r ≪≫
    (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso
      (equivOfSubsingletonOfSubsingleton (fun _ ↦ PUnit.unit) fun _ ↦ h.2.some).toIso ≪≫
    eqToIso (InvertibleSheaf.trivial_obj X).symm)

/-- On underlying sheaves, `determinantFreeIso` is the identification
`⋀ʳ (free (Fin r)) ≅ free (Set.powersetCard (Fin r) r)` of `exteriorPowerFreeIso`, followed by the
map of free sheaves collapsing the single `r`-element subset of `Fin r` to a point. -/
theorem determinantFreeIso_hom_hom (r : ℕ) :
    (determinantFreeIso X r).hom.hom =
      eqToHom (by rw [determinant_obj_obj, FixedRank.free_obj, free_obj]) ≫
        (SheafOfModules.exteriorPowerFreeIso (R := X.sheaf) (ULift.{u} (Fin r)) r).hom ≫
        SheafOfModules.freeMap (R := X.ringCatSheaf) (fun _ ↦ PUnit.unit) ≫
        eqToHom (InvertibleSheaf.trivial_obj X).symm := by
  -- The free-sheaf part of `determinantFreeIso` is `freeFunctor` applied to the collapsing map,
  -- which `freeFunctor_map` identifies with `freeMap`.
  unfold determinantFreeIso
  exact congrArg (fun g ↦ _ ≫ _ ≫ g ≫ _) (SheafOfModules.freeFunctor_map _)

variable (X) in
/-- The determinant of a finite locally free sheaf of constant rank one is naturally the sheaf
itself: `⋀¹ E ≅ E`. -/
def determinantOneIso :
    determinant X 1 ⋙ InvertibleSheaf.toFiniteLocallyFree X ≅ FixedRank.toFiniteLocallyFree X 1 :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _ ((SheafOfModules.exteriorPowerOneIso X.sheaf).app E.obj.obj))
    (fun f ↦ by
      -- `determinant` is a lift of the exterior power, so on underlying morphisms this is the
      -- naturality of `exteriorPowerOneIso`.
      ext1
      exact (SheafOfModules.exteriorPowerOneIso X.sheaf).hom.naturality f.hom.hom)

/-- On underlying sheaves, the components of `determinantOneIso` are those of
`SheafOfModules.exteriorPowerOneIso`. -/
@[simp]
theorem determinantOneIso_hom_app_hom (E : FixedRank X 1) :
    ((determinantOneIso X).hom.app E).hom =
      eqToHom (determinant_obj_obj E) ≫
        (SheafOfModules.exteriorPowerOneIso X.sheaf).hom.app E.obj.obj :=
  (Category.id_comp _).symm

variable (X) in
/-- In rank zero the determinant is naturally the trivial invertible sheaf: `⋀⁰ E ≅ 𝒪_X`. -/
def determinantZeroIso :
    determinant X 0 ≅ (Functor.const _).obj (InvertibleSheaf.trivial X) :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _
      ((SheafOfModules.exteriorPowerZeroIso X.sheaf).app E.obj.obj ≪≫
        (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).symm ≪≫
        eqToIso (InvertibleSheaf.trivial_obj X).symm))
    (fun f ↦ by
      -- As for `determinantOneIso`, this is the naturality of `exteriorPowerZeroIso`; the
      -- constant functor acts on morphisms by identities.
      ext1
      exact ((SheafOfModules.exteriorPowerZeroIso X.sheaf).hom.naturality_assoc f.hom.hom _).trans
        (Category.comp_id _).symm)

/-- On underlying sheaves, the components of `determinantZeroIso` are those of
`SheafOfModules.exteriorPowerZeroIso`, followed by the identification of the structure sheaf with
the free sheaf on one generator. -/
@[simp]
theorem determinantZeroIso_hom_app_hom (E : FixedRank X 0) :
    ((determinantZeroIso X).hom.app E).hom =
      eqToHom (determinant_obj_obj E) ≫
        (SheafOfModules.exteriorPowerZeroIso X.sheaf).hom.app E.obj.obj ≫
        (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).inv ≫
        eqToHom (InvertibleSheaf.trivial_obj X).symm :=
  (Category.id_comp _).symm

end FiniteLocallyFreeSheaf

end

end AlgebraicGeometry

end TauCeti
