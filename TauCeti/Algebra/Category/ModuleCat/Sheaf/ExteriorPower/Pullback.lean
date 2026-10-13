/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Pullback
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward

/-!
# Pushforward and Pullback Comparisons for Exterior Powers of Sheaves of Modules

Given a continuous functor `F : C ⥤ D` between Grothendieck sites, sheaves of commutative rings
`S : Sheaf J CommRingCat.{u}` and `R : Sheaf K CommRingCat.{u}`, and a morphism
`φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R)`, we
construct the natural pushforward and pullback comparison transformations for `n`-th exterior
powers of sheaves of modules:
* `SheafOfModules.pushforwardExteriorPowerComparison φ n`, obtained by sheafifying
  `TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison`;
* `SheafOfModules.pullbackExteriorPowerComparison φ n`, obtained as the mate of
  `pushforwardExteriorPowerComparison φ n` under `SheafOfModules.pullbackPushforwardAdjunction φ`.

We prove composition laws (`pushforwardComp_pushforwardExteriorPowerComparison`,
`pullback_comp_pullbackExteriorPowerComparison`), invertibility along site adjunctions
(`isIso_pushforwardExteriorPowerComparison_of_adjunction`,
`isIso_pullbackExteriorPowerComparison_of_adjunction`), and compatibility with
`exteriorPowerFreeIso` and `pullbackObjFreeIso` on finite free sheaves
(`pullbackExteriorPowerComparison_free`, `isIso_pullbackExteriorPowerComparison_free`).
-/

public section

open CategoryTheory Category Limits Opposite
open TauCeti.SheafOfModules (ringCatSheaf sheafificationIso sheafificationIso_hom
  sheafificationIso_hom_naturality sheafificationForgetAdjunction
  sheafificationForgetAdjunction_counit_app presheafPushforward
  presheafPushforward_map_map freeBasis)

universe u

noncomputable section

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section Ext

variable {R : Sheaf J CommRingCat.{u}}

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
variable (R) in
/-- The sectionwise `n`-th exterior power of presheaves of modules, with source and target written
as presheaves of modules over `(ringCatSheaf R).obj` so that it composes with
`SheafOfModules.forget`, `presheafPushforward`, and `PresheafOfModules.sheafification`. -/
@[expose]
def presheafExteriorPower (n : ℕ) :
    PresheafOfModules.{u} (ringCatSheaf R).obj ⥤ PresheafOfModules.{u} (ringCatSheaf R).obj :=
  PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n

/-- `exteriorPowerIso` with its sectionwise exterior power written through `presheafExteriorPower`,
so that its target is syntactically in the image of `PresheafOfModules.sheafification`. -/
def exteriorPowerUnderlyingIso (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (exteriorPower R n).obj M ≅
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        ((presheafExteriorPower R n).obj M.val) :=
  exteriorPowerIso n M

/-- The canonical morphism from the sectionwise `n`-th exterior power of `M` to the underlying
presheaf of the sheafified `n`-th exterior power `⋀ⁿ M`: the unit of sheafification followed by
`exteriorPowerUnderlyingIso`. -/
def toExteriorPower (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (presheafExteriorPower R n).obj M.val ⟶
      (SheafOfModules.forget (ringCatSheaf R)).obj ((exteriorPower R n).obj M) :=
  (sheafificationForgetAdjunction R).unit.app ((presheafExteriorPower R n).obj M.val) ≫
    (SheafOfModules.forget (ringCatSheaf R)).map (exteriorPowerUnderlyingIso n M).inv

/-- A morphism out of `⋀ⁿ M`, precomposed on underlying presheaves with `toExteriorPower`, is the
transpose along sheafification of the morphism read through `exteriorPowerUnderlyingIso`. -/
theorem toExteriorPower_comp_forget_map (n : ℕ)
    {M N : SheafOfModules.{u} (ringCatSheaf R)} (p : (exteriorPower R n).obj M ⟶ N) :
    toExteriorPower n M ≫ (SheafOfModules.forget (ringCatSheaf R)).map p =
      (sheafificationForgetAdjunction R).homEquiv
        ((presheafExteriorPower R n).obj M.val) N ((exteriorPowerUnderlyingIso n M).inv ≫ p) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← assoc, toExteriorPower]

/-- Two morphisms out of an exterior power `⋀ⁿ M` of a sheaf of modules agree as soon as they
agree after precomposition with `toExteriorPower` on the sectionwise exterior power of `M`. -/
theorem exteriorPower_hom_ext (n : ℕ) {M N : SheafOfModules.{u} (ringCatSheaf R)}
    {p q : (exteriorPower R n).obj M ⟶ N}
    (h : toExteriorPower n M ≫ (SheafOfModules.forget (ringCatSheaf R)).map p =
      toExteriorPower n M ≫ (SheafOfModules.forget (ringCatSheaf R)).map q) :
    p = q := by
  rw [toExteriorPower_comp_forget_map, toExteriorPower_comp_forget_map] at h
  exact (cancel_epi _).mp (((sheafificationForgetAdjunction R).homEquiv _ _).injective h)

/-- `toExteriorPower` intertwines the sectionwise exterior power of a morphism with its
sheafified exterior power. -/
@[reassoc]
theorem toExteriorPower_comp_forget_map_exteriorPower_map (n : ℕ)
    {M N : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) :
    toExteriorPower n M ≫
      (SheafOfModules.forget (ringCatSheaf R)).map ((exteriorPower R n).map f) =
    (presheafExteriorPower R n).map f.val ≫ toExteriorPower n N := by
  have hm : (exteriorPower R n).map f =
      (exteriorPowerUnderlyingIso n M).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((presheafExteriorPower R n).map f.val) ≫
        (exteriorPowerUnderlyingIso n N).inv := exteriorPower_map n f
  rw [toExteriorPower_comp_forget_map, hm, Iso.inv_hom_id_assoc,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit, ← toExteriorPower]

/-- On decomposable wedges of sections, the sheafified exterior power of a morphism acts on each
factor of the wedge. -/
theorem exteriorPower_map_toExteriorPower_app_mk (n : ℕ)
    {M N : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) (U : Cᵒᵖ) (m : Fin n → M.val.obj U) :
    ((exteriorPower R n).map f).val.app U ((toExteriorPower n M).app U
        (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj M.val U) m)) =
      (toExteriorPower n N).app U
        (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj N.val U)
          fun j ↦ f.val.app U (m j)) := by
  have h := congrArg (fun p ↦ (p.app U).hom
    (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj M.val U) m))
    (toExteriorPower_comp_forget_map_exteriorPower_map n f)
  change ((exteriorPower R n).map f).val.app U ((toExteriorPower n M).app U
      (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj M.val U) m)) =
    (toExteriorPower n N).app U (((presheafExteriorPower R n).map f.val).app U
      (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj M.val U) m)) at h
  exact h.trans (congrArg ((toExteriorPower n N).app U)
    (ModuleCat.exteriorPower.map_mk (f.val.app' U) m))

/-- Restriction of a decomposable wedge in the sheafified exterior power restricts each factor. -/
theorem toExteriorPower_naturality_mk (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R))
    {U V : Cᵒᵖ} (g : U ⟶ V) (m : Fin n → M.val.obj U) :
    ((exteriorPower R n).obj M).val.map g ((toExteriorPower n M).app U
        (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj M.val U) m)) =
      (toExteriorPower n M).app V
        (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj M.val V)
          fun j ↦ M.val.map g (m j)) :=
  (PresheafOfModules.naturality_apply (toExteriorPower n M) g
    (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj M.val U) m)).symm.trans
    (congrArg ((toExteriorPower n M).app V)
      (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n M.val g m))

/-- Precomposing `exteriorPowerFreeIso` with `toExteriorPower` on underlying presheaves recovers
`presheafExteriorPowerFreeIso`. -/
@[reassoc]
theorem toExteriorPower_comp_forget_map_exteriorPowerFreeIso_hom (I : Type u) [Finite I]
    [LinearOrder I] (n : ℕ) :
    toExteriorPower (R := R) n (free I) ≫
      (SheafOfModules.forget (ringCatSheaf R)).map (exteriorPowerFreeIso (R := R) I n).hom =
    (presheafExteriorPowerFreeIso (R := R) I n).hom := by
  have hf : (exteriorPowerFreeIso (R := R) I n).hom = (exteriorPowerUnderlyingIso n (free I)).hom ≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        (presheafExteriorPowerFreeIso (R := R) I n).hom ≫
      (sheafificationIso (ringCatSheaf R) (free _)).hom := exteriorPowerFreeIso_hom I n
  rw [toExteriorPower_comp_forget_map, hf, Iso.inv_hom_id_assoc,
    ← sheafificationForgetAdjunction_counit_app]
  exact (congrArg _ ((sheafificationForgetAdjunction R).homEquiv_counit _ _ _).symm).trans
    (Equiv.apply_symm_apply _ _)

end Ext

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} [F.IsContinuous J K] {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))

/-- The morphism of presheaves of commutative rings underlying `φ`. -/
private def commRingCatHom : S.obj ⟶ F.op ⋙ R.obj where
  app U := CommRingCat.ofHom (φ.hom.app U).hom
  naturality _ _ f := by ext x; exact congr($(φ.hom.naturality f).hom x)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The sectionwise restriction-of-scalars comparison for exterior powers, written between
`presheafPushforward` and `presheafExteriorPower`. -/
def presheafPushforwardExteriorPowerComparison (n : ℕ) :
    presheafPushforward φ ⋙ presheafExteriorPower S n ⟶
      presheafExteriorPower R n ⋙ presheafPushforward φ :=
  TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison (commRingCatHom φ) n

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On a decomposable wedge over `U`, `presheafPushforwardExteriorPowerComparison` keeps the
factors unchanged and changes the coefficient ring along `φ`. -/
@[simp]
theorem presheafPushforwardExteriorPowerComparison_app_app_mk (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} R.obj) (U : Cᵒᵖ) (m : Fin n → M.obj (F.op.obj U)) :
    (((presheafPushforwardExteriorPowerComparison φ n).app M).app U
        (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj
          ((presheafPushforward φ).obj M) U) m) =
      ModuleCat.exteriorPower.mk (M := M.obj (F.op.obj U)) m) :=
  TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison_app_app_mk
    (commRingCatHom φ) n M U m

private def pushforwardExteriorPowerMap (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (exteriorPower S n).obj ((SheafOfModules.pushforward φ).obj M) ⟶
      (SheafOfModules.pushforward φ).obj ((exteriorPower R n).obj M) :=
  (exteriorPowerUnderlyingIso n ((SheafOfModules.pushforward φ).obj M)).hom ≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf S).obj)).map
      ((presheafPushforwardExteriorPowerComparison φ n).app M.val ≫
        (presheafPushforward φ).map (toExteriorPower n M)) ≫
    (sheafificationIso (ringCatSheaf S)
      ((SheafOfModules.pushforward φ).obj ((exteriorPower R n).obj M))).hom

@[reassoc]
private theorem toExteriorPower_comp_pushforwardExteriorPowerMap (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    toExteriorPower n ((SheafOfModules.pushforward φ).obj M) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map (pushforwardExteriorPowerMap φ n M) =
    (presheafPushforwardExteriorPowerComparison φ n).app M.val ≫
      (presheafPushforward φ).map (toExteriorPower n M) := by
  rw [pushforwardExteriorPowerMap, toExteriorPower_comp_forget_map, Iso.inv_hom_id_assoc,
    ← sheafificationForgetAdjunction_counit_app]
  exact (congrArg _ ((sheafificationForgetAdjunction S).homEquiv_counit _ _ _).symm).trans
    (Equiv.apply_symm_apply _ _)

/-- The canonical comparison `⋀ⁿ (φ_* M) ⟶ φ_* (⋀ⁿ M)` for pushforward of sheaves of modules,
obtained by sheafifying the sectionwise restriction-of-scalars comparison
`TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison`. -/
def pushforwardExteriorPowerComparison (n : ℕ) :
    SheafOfModules.pushforward φ ⋙ exteriorPower S n ⟶
      exteriorPower R n ⋙ SheafOfModules.pushforward φ where
  app M := pushforwardExteriorPowerMap φ n M
  naturality {M N} f := by
    apply exteriorPower_hom_ext
    simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp,
      toExteriorPower_comp_forget_map_exteriorPower_map_assoc,
      toExteriorPower_comp_pushforwardExteriorPowerMap,
      toExteriorPower_comp_pushforwardExteriorPowerMap_assoc]
    have e : (presheafExteriorPower R n ⋙ presheafPushforward φ).map f.val ≫
        (presheafPushforward φ).map (toExteriorPower n N) =
      (presheafPushforward φ).map (toExteriorPower n M) ≫
        (SheafOfModules.forget (ringCatSheaf S)).map
          ((SheafOfModules.pushforward φ).map ((exteriorPower R n).map f)) := by
      rw [Functor.comp_map, ← Functor.map_comp, ← toExteriorPower_comp_forget_map_exteriorPower_map,
        Functor.map_comp]; rfl
    exact ((presheafPushforwardExteriorPowerComparison φ n).naturality_assoc
      f.val ((presheafPushforward φ).map (toExteriorPower n N))).trans (congrArg _ e)

/-- Read on underlying presheaves along `toExteriorPower`, the pushforward comparison is the
sectionwise comparison followed by the pushforward of `toExteriorPower`. -/
@[reassoc]
theorem toExteriorPower_comp_forget_map_pushforwardExteriorPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    toExteriorPower n ((SheafOfModules.pushforward φ).obj M) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map
        ((pushforwardExteriorPowerComparison φ n).app M) =
    (presheafPushforwardExteriorPowerComparison φ n).app M.val ≫
      (presheafPushforward φ).map (toExteriorPower n M) :=
  toExteriorPower_comp_pushforwardExteriorPowerMap φ n M

/-- On components, `pushforwardExteriorPowerComparison` is the sheafification of the sectionwise
comparison and `toExteriorPower`, followed by `sheafificationIso`. -/
theorem pushforwardExteriorPowerComparison_app (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardExteriorPowerComparison φ n).app M =
      (exteriorPowerUnderlyingIso n ((SheafOfModules.pushforward φ).obj M)).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf S).obj)).map
          ((presheafPushforwardExteriorPowerComparison φ n).app M.val ≫
            (presheafPushforward φ).map (toExteriorPower n M)) ≫
        (sheafificationIso (ringCatSheaf S)
          ((SheafOfModules.pushforward φ).obj ((exteriorPower R n).obj M))).hom :=
  (rfl)

/-- On decomposable wedges of sections, the exterior power comparison map of sheaf pushforward
is the inclusion of the corresponding decomposable wedge on the source site into the sheaf
exterior power. -/
theorem pushforwardExteriorPowerComparison_app_mk (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) (U : Cᵒᵖ) (m : Fin n → M.val.obj (F.op.obj U)) :
    ((pushforwardExteriorPowerComparison φ n).app M).val.app U
      ((toExteriorPower n ((SheafOfModules.pushforward φ).obj M)).app U
        (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj
          ((presheafPushforward φ).obj M.val) U) m)) =
    (toExteriorPower n M).app (F.op.obj U)
      (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj M.val (F.op.obj U)) m) := by
  have h := congrArg (fun p ↦ (p.app U).hom
    (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj
      ((presheafPushforward φ).obj M.val) U) m))
    (toExteriorPower_comp_forget_map_pushforwardExteriorPowerComparison φ n M)
  change ((pushforwardExteriorPowerComparison φ n).app M).val.app U
      ((toExteriorPower n ((SheafOfModules.pushforward φ).obj M)).app U
        (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj
          ((presheafPushforward φ).obj M.val) U) m)) =
    (toExteriorPower n M).app (F.op.obj U)
      (((presheafPushforwardExteriorPowerComparison φ n).app M.val).app U
        (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj
          ((presheafPushforward φ).obj M.val) U) m)) at h
  exact h.trans (congrArg ((toExteriorPower n M).app (F.op.obj U))
    (presheafPushforwardExteriorPowerComparison_app_app_mk φ n M.val U m))

section Comp

variable {E : Type u} [SmallCategory E] {L : GrothendieckTopology E}
  [L.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {G : D ⥤ E} [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L] {T : Sheaf L CommRingCat.{u}}
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj (ringCatSheaf T))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The sectionwise pushforward comparison for exterior powers along a composite is the composite
of the sectionwise comparisons: both keep the factors of a decomposable wedge unchanged. -/
@[reassoc]
theorem presheafPushforwardExteriorPowerComparison_comp (n : ℕ)
    (M : PresheafOfModules.{u} (ringCatSheaf T).obj) :
    (presheafPushforwardExteriorPowerComparison φ n).app ((presheafPushforward ψ).obj M) ≫
      (presheafPushforward φ).map ((presheafPushforwardExteriorPowerComparison ψ n).app M) =
    (presheafPushforwardExteriorPowerComparison (F := F ⋙ G) (R := T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n).app M := by
  ext U : 1
  apply ModuleCat.exteriorPower.hom_ext (R := S.obj.obj U)
  apply ModuleCat.AlternatingMap.ext
  intro m
  have h₁ := presheafPushforwardExteriorPowerComparison_app_app_mk φ n
    ((presheafPushforward ψ).obj M) U m
  have h₂ := presheafPushforwardExteriorPowerComparison_app_app_mk ψ n M (F.op.obj U) m
  have h₃ := presheafPushforwardExteriorPowerComparison_app_app_mk (F := F ⋙ G) (R := T)
    (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n M U m
  exact (congrArg (fun x ↦ ((presheafPushforward φ).map
    ((presheafPushforwardExteriorPowerComparison ψ n).app M)).app U x) h₁).trans (h₂.trans h₃.symm)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(F ⋙ G).IsContinuous J L] in
private lemma forget_map_pushforwardComp_hom_app (M : SheafOfModules.{u} (ringCatSheaf T)) :
    (SheafOfModules.forget (ringCatSheaf S)).map
      ((SheafOfModules.pushforwardComp φ ψ).hom.app M) = 𝟙 _ := (rfl)

/-- The pushforward comparison for exterior powers along a composite is the composite of the
pushforward comparisons, read through `SheafOfModules.pushforwardComp`. -/
@[reassoc]
theorem pushforwardComp_pushforwardExteriorPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf T)) :
    (pushforwardExteriorPowerComparison φ n).app ((SheafOfModules.pushforward ψ).obj M) ≫
      (SheafOfModules.pushforward φ).map ((pushforwardExteriorPowerComparison ψ n).app M) ≫
      (SheafOfModules.pushforwardComp φ ψ).hom.app ((exteriorPower T n).obj M) =
    (exteriorPower S n).map ((SheafOfModules.pushforwardComp φ ψ).hom.app M) ≫
      (pushforwardExteriorPowerComparison (F := F ⋙ G) (R := T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n).app M := by
  apply exteriorPower_hom_ext
  simp only [Functor.map_comp, toExteriorPower_comp_forget_map_pushforwardExteriorPowerComparison,
    toExteriorPower_comp_forget_map_pushforwardExteriorPowerComparison_assoc,
    toExteriorPower_comp_forget_map_exteriorPower_map_assoc, forget_map_pushforwardComp_hom_app]
  have e : (presheafPushforward φ).map (toExteriorPower n ((SheafOfModules.pushforward ψ).obj M)) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map
        ((SheafOfModules.pushforward φ).map ((pushforwardExteriorPowerComparison ψ n).app M)) =
    (presheafPushforward φ).map ((presheafPushforwardExteriorPowerComparison ψ n).app M.val) ≫
      (presheafPushforward φ).map ((presheafPushforward ψ).map (toExteriorPower n M)) := by
    rw [← Functor.map_comp, ← toExteriorPower_comp_forget_map_pushforwardExteriorPowerComparison]
    rfl
  refine (assoc _ _ _).trans ((congrArg (_ ≫ ·) (assoc _ _ _).symm).trans
    ((congrArg (fun x ↦ _ ≫ x ≫ _) e).trans ?_))
  erw [comp_id, CategoryTheory.Functor.map_id, id_comp,
    presheafPushforwardExteriorPowerComparison_comp_assoc, presheafPushforward_map_map]
  rfl

end Comp

@[reassoc]
private lemma unit_comp_map_mateEquiv_symm {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : L ⊣ R)
    {E₁ : C₁ ⥤ C₁} {E₂ : C₂ ⥤ C₂} (α : R ⋙ E₁ ⟶ E₂ ⋙ R) (Y : C₁) :
    adj.unit.app (E₁.obj Y) ≫
        R.map (((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ α)).natTrans.app Y) =
      E₁.map (adj.unit.app Y) ≫ α.app (L.obj Y) :=
  (unit_mateEquiv_symm adj adj (TwoSquare.mk _ _ _ _ α) Y).symm

section Adjunction

private lemma comp_mateEquiv_symm_of_counit {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : F ⊣ G) {E₁ : C₁ ⥤ C₁} {E₂ : C₂ ⥤ C₂}
    (αF : F ⋙ E₂ ⟶ E₁ ⋙ F) (αG : G ⋙ E₁ ⟶ E₂ ⋙ G)
    (hcounit : ∀ Y : C₂, αF.app (G.obj Y) ≫ F.map (αG.app Y) ≫ adj.counit.app (E₂.obj Y) =
      E₂.map (adj.counit.app Y)) (X : C₁) :
    αF.app X ≫ ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X =
      𝟙 (E₂.obj (F.obj X)) := by
  have hm : ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X =
      (adj.homEquiv (E₁.obj X) (E₂.obj (F.obj X))).symm
        (E₁.map (adj.unit.app X) ≫ αG.app (F.obj X)) := by
    apply (adj.homEquiv (E₁.obj X) (E₂.obj (F.obj X))).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact unit_comp_map_mateEquiv_symm adj αG X
  have hnat : αF.app X ≫ F.map (E₁.map (adj.unit.app X)) =
      E₂.map (F.map (adj.unit.app X)) ≫ αF.app (G.obj (F.obj X)) :=
    (αF.naturality (adj.unit.app X)).symm
  rw [hm, Adjunction.homEquiv_counit, F.map_comp, assoc, reassoc_of% hnat, hcounit,
    ← E₂.map_comp, adj.left_triangle_components, E₂.map_id]

private lemma mateEquiv_symm_comp_of_unit {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : F ⊣ G) {E₁ : C₁ ⥤ C₁} {E₂ : C₂ ⥤ C₂}
    (αF : F ⋙ E₂ ⟶ E₁ ⋙ F) (αG : G ⋙ E₁ ⟶ E₂ ⋙ G)
    (hunit : ∀ X : C₁, adj.unit.app (E₁.obj X) =
      E₁.map (adj.unit.app X) ≫ αG.app (F.obj X) ≫ G.map (αF.app X)) (X : C₁) :
    ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X ≫ αF.app X =
      𝟙 (F.obj (E₁.obj X)) := by
  apply (adj.homEquiv (E₁.obj X) (F.obj (E₁.obj X))).injective
  rw [Adjunction.homEquiv_unit, Functor.map_comp, unit_comp_map_mateEquiv_symm_assoc, ← hunit,
    Adjunction.homEquiv_unit, G.map_id]
  exact (comp_id _).symm

private lemma isIso_mateEquiv_symm_of_leftAdjoint {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {F L : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : F ⊣ G) (adj' : L ⊣ G)
    {E₁ : C₁ ⥤ C₁} {E₂ : C₂ ⥤ C₂} (αG : G ⋙ E₁ ⟶ E₂ ⋙ G) (X : C₁)
    [IsIso (((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X)] :
    IsIso (((mateEquiv adj' adj').symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X) := by
  let σ := (Adjunction.leftAdjointUniq adj adj').inv
  have hσ (Z : C₁) : adj'.unit.app Z ≫ G.map (σ.app Z) = adj.unit.app Z := by
    have hc : conjugateEquiv adj adj' σ = 𝟙 G := by simp [σ, Adjunction.leftAdjointUniq]
    have hu := unit_conjugateEquiv adj adj' σ Z
    erw [hc, NatTrans.id_app, comp_id] at hu
    exact hu.symm
  have hcomm :
      σ.app (E₁.obj X) ≫ ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X =
        ((mateEquiv adj' adj').symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X ≫
          E₂.map (σ.app X) := by
    apply (adj'.homEquiv _ _).injective
    have hnat : E₁.map (G.map (σ.app X)) ≫ αG.app (F.obj X) =
        αG.app (L.obj X) ≫ G.map (E₂.map (σ.app X)) := αG.naturality (σ.app X)
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, reassoc_of% hσ,
      unit_comp_map_mateEquiv_symm, unit_comp_map_mateEquiv_symm_assoc]
    rw [← hσ X, E₁.map_comp_assoc, hnat]
  have : IsIso (((mateEquiv adj' adj').symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X ≫
      E₂.map (σ.app X)) := by rw [← hcomm]; infer_instance
  exact IsIso.of_isIso_comp_right _ (E₂.map (σ.app X))

variable {G : D ⥤ C} [G.IsContinuous K J] (adj : F ⊣ G)
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj (ringCatSheaf S))
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) (ringCatSheaf R).obj =
    ψ.hom ≫ G.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op adj.unit) (ringCatSheaf S).obj = 𝟙 (ringCatSheaf S).obj)

/-- The unit `M ⟶ ψ_* φ_* M` of the adjunction between pushforwards is compatible with the
exterior power comparison maps of the two pushforwards. -/
theorem pushforwardPushforwardAdj_unit_app_exteriorPower (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app ((exteriorPower R n).obj M) =
      (exteriorPower R n).map ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M) ≫
        (pushforwardExteriorPowerComparison ψ n).app ((SheafOfModules.pushforward φ).obj M) ≫
        (SheafOfModules.pushforward ψ).map ((pushforwardExteriorPowerComparison φ n).app M) := by
  apply exteriorPower_hom_ext
  ext V : 1
  apply ModuleCat.exteriorPower.hom_ext (R := R.obj.obj V)
  apply ModuleCat.AlternatingMap.ext
  intro m
  set η := (SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit
  have hnat := exteriorPower_map_toExteriorPower_app_mk n (η.app M) V m
  have hψ := pushforwardExteriorPowerComparison_app_mk ψ n
    ((SheafOfModules.pushforward φ).obj M) V (fun j ↦ (η.app M).val.app V (m j))
  have hφ := pushforwardExteriorPowerComparison_app_mk φ n M (G.op.obj V)
    (fun j ↦ (η.app M).val.app V (m j))
  refine (toExteriorPower_naturality_mk n M (adj.counit.app V.unop).op m).trans ?_
  refine Eq.trans ?_ (congrArg (fun z ↦ ((SheafOfModules.forget (ringCatSheaf R)).map
    ((pushforwardExteriorPowerComparison ψ n).app ((SheafOfModules.pushforward φ).obj M) ≫
      (SheafOfModules.pushforward ψ).map
        ((pushforwardExteriorPowerComparison φ n).app M))).app V z) hnat.symm)
  exact hφ.symm.trans (congrArg (((SheafOfModules.forget (ringCatSheaf S)).map
    ((pushforwardExteriorPowerComparison φ n).app M)).app (G.op.obj V)) hψ.symm)

/-- The counit `φ_* ψ_* A ⟶ A` of the adjunction between pushforwards is compatible with the
exterior power comparison maps of the two pushforwards. -/
theorem pushforwardPushforwardAdj_counit_app_exteriorPower (n : ℕ)
    (A : SheafOfModules.{u} (ringCatSheaf S)) :
    (pushforwardExteriorPowerComparison φ n).app ((SheafOfModules.pushforward ψ).obj A) ≫
      (SheafOfModules.pushforward φ).map ((pushforwardExteriorPowerComparison ψ n).app A) ≫
        (SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app
          ((exteriorPower S n).obj A) =
      (exteriorPower S n).map
        ((SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app A) := by
  apply exteriorPower_hom_ext
  ext U : 1
  apply ModuleCat.exteriorPower.hom_ext (R := S.obj.obj U)
  apply ModuleCat.AlternatingMap.ext
  intro a
  set ε := (SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit
  have hnat := exteriorPower_map_toExteriorPower_app_mk n (ε.app A) U a
  have hφ := pushforwardExteriorPowerComparison_app_mk φ n
    ((SheafOfModules.pushforward ψ).obj A) U a
  have hψ := pushforwardExteriorPowerComparison_app_mk ψ n A (F.op.obj U) a
  refine Eq.trans (congrArg (((SheafOfModules.forget (ringCatSheaf S)).map
    ((SheafOfModules.pushforward φ).map ((pushforwardExteriorPowerComparison ψ n).app A) ≫
      ε.app ((exteriorPower S n).obj A))).app U) hφ) ?_
  refine Eq.trans (congrArg (((SheafOfModules.forget (ringCatSheaf S)).map
    (ε.app ((exteriorPower S n).obj A))).app U) hψ) ?_
  exact (toExteriorPower_naturality_mk n A (adj.unit.app U.unop).op a).trans hnat.symm

include adj ψ H₁ H₂ in
/-- **Pushforward along a left adjoint of sites commutes with exterior powers**: the comparison
map `⋀ⁿ (φ_* M) ⟶ φ_* (⋀ⁿ M)` of the pushforward along `φ` is an isomorphism. -/
theorem isIso_pushforwardExteriorPowerComparison_of_adjunction (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    IsIso ((pushforwardExteriorPowerComparison φ n).app M) :=
  ⟨((mateEquiv (SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂)
      (SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂)).symm
      (TwoSquare.mk _ _ _ _ (pushforwardExteriorPowerComparison ψ n))).natTrans.app M,
    comp_mateEquiv_symm_of_counit (SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂)
      (pushforwardExteriorPowerComparison φ n) (pushforwardExteriorPowerComparison ψ n)
      (pushforwardPushforwardAdj_counit_app_exteriorPower φ adj ψ H₁ H₂ n) M,
    mateEquiv_symm_comp_of_unit (SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂)
      (pushforwardExteriorPowerComparison φ n) (pushforwardExteriorPowerComparison ψ n)
      (pushforwardPushforwardAdj_unit_app_exteriorPower φ adj ψ H₁ H₂ n) M⟩

end Adjunction

variable [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- The canonical comparison `φ^* (⋀ⁿ M) ⟶ ⋀ⁿ (φ^* M)` for pullback of sheaves of modules,
obtained as the mate of `pushforwardExteriorPowerComparison φ n` under
`SheafOfModules.pullbackPushforwardAdjunction φ`. -/
def pullbackExteriorPowerComparison (n : ℕ) :
    exteriorPower S n ⋙ SheafOfModules.pullback φ ⟶
      SheafOfModules.pullback φ ⋙ exteriorPower R n :=
  let A := SheafOfModules.pullbackPushforwardAdjunction φ
  ((mateEquiv A A).symm (TwoSquare.mk _ _ _ _ (pushforwardExteriorPowerComparison φ n))).natTrans

/-- The adjunction unit equation characterizing `pullbackExteriorPowerComparison`. -/
@[reassoc (attr := simp)]
theorem unit_comp_pushforward_pullbackExteriorPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (SheafOfModules.pullbackPushforwardAdjunction φ).unit.app ((exteriorPower S n).obj M) ≫
      (SheafOfModules.pushforward φ).map ((pullbackExteriorPowerComparison φ n).app M) =
    (exteriorPower S n).map ((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M) ≫
      (pushforwardExteriorPowerComparison φ n).app ((SheafOfModules.pullback φ).obj M) :=
  (unit_mateEquiv_symm (SheafOfModules.pullbackPushforwardAdjunction φ)
    (SheafOfModules.pullbackPushforwardAdjunction φ)
    (TwoSquare.mk _ _ _ _ (pushforwardExteriorPowerComparison φ n)) M).symm

/-- `pullbackExteriorPowerComparison` is the transpose under
`SheafOfModules.pullbackPushforwardAdjunction φ` of the exterior power of the unit followed by
`pushforwardExteriorPowerComparison`. -/
theorem pullbackExteriorPowerComparison_app (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackExteriorPowerComparison φ n).app M =
      ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv ((exteriorPower S n).obj M)
        ((exteriorPower R n).obj ((SheafOfModules.pullback φ).obj M))).symm
        ((exteriorPower S n).map ((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M) ≫
          (pushforwardExteriorPowerComparison φ n).app ((SheafOfModules.pullback φ).obj M)) := by
  apply ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv ((exteriorPower S n).obj M)
    ((exteriorPower R n).obj ((SheafOfModules.pullback φ).obj M))).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact unit_comp_pushforward_pullbackExteriorPowerComparison φ n M

section PullbackAdjunction

variable {G : D ⥤ C} [G.IsContinuous K J] (adj : F ⊣ G)
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj (ringCatSheaf S))
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) (ringCatSheaf R).obj =
    ψ.hom ≫ G.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op adj.unit) (ringCatSheaf S).obj = 𝟙 (ringCatSheaf S).obj)
  [(SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]

include φ adj H₁ H₂ in
omit [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint] in
/-- **Pullback along a right adjoint of sites commutes with exterior powers**: when `F ⊣ G`
induces an adjunction `pushforward φ ⊣ pushforward ψ`, the pullback comparison
`ψ^* (⋀ⁿ M) ⟶ ⋀ⁿ (ψ^* M)` is an isomorphism for every sheaf of modules `M`. -/
theorem isIso_pullbackExteriorPowerComparison_of_adjunction (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    IsIso ((pullbackExteriorPowerComparison ψ n).app M) := by
  let A := SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂
  have : IsIso (((mateEquiv A A).symm
      (TwoSquare.mk _ _ _ _ (pushforwardExteriorPowerComparison ψ n))).natTrans.app M) :=
    ⟨(pushforwardExteriorPowerComparison φ n).app M,
      mateEquiv_symm_comp_of_unit A
        (pushforwardExteriorPowerComparison φ n) (pushforwardExteriorPowerComparison ψ n)
        (pushforwardPushforwardAdj_unit_app_exteriorPower φ adj ψ H₁ H₂ n) M,
      comp_mateEquiv_symm_of_counit A
        (pushforwardExteriorPowerComparison φ n) (pushforwardExteriorPowerComparison ψ n)
        (pushforwardPushforwardAdj_counit_app_exteriorPower φ adj ψ H₁ H₂ n) M⟩
  exact isIso_mateEquiv_symm_of_leftAdjoint A (SheafOfModules.pullbackPushforwardAdjunction ψ)
    (pushforwardExteriorPowerComparison ψ n) M

end PullbackAdjunction

section Comp

private theorem mateEquiv_symm_comp_of_conjugateEquiv
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} (adj₁ : L₁ ⊣ R₁)
    {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂} (adj₂ : L₂ ⊣ R₂)
    {L₁₂ : C₁ ⥤ C₃} {R₁₂ : C₃ ⥤ C₁} (adj₁₂ : L₁₂ ⊣ R₁₂)
    {E₁ : C₁ ⥤ C₁} {E₂ : C₂ ⥤ C₂} {E₃ : C₃ ⥤ C₃}
    (α₁ : R₁ ⋙ E₁ ⟶ E₂ ⋙ R₁) (α₂ : R₂ ⋙ E₂ ⟶ E₃ ⋙ R₂) (α₁₂ : R₁₂ ⋙ E₁ ⟶ E₃ ⋙ R₁₂)
    (i : L₁ ⋙ L₂ ≅ L₁₂) {τ : R₂ ⋙ R₁ ⟶ R₁₂} (h : conjugateEquiv (adj₁.comp adj₂) adj₁₂ i.inv = τ)
    (hτ : ∀ X : C₃, α₁.app (R₂.obj X) ≫ R₁.map (α₂.app X) ≫ τ.app (E₃.obj X) =
      E₁.map (τ.app X) ≫ α₁₂.app X) (Y : C₁) :
    ((mateEquiv adj₁₂ adj₁₂).symm (TwoSquare.mk _ _ _ _ α₁₂)).natTrans.app Y =
      i.inv.app (E₁.obj Y) ≫
        L₂.map (((mateEquiv adj₁ adj₁).symm (TwoSquare.mk _ _ _ _ α₁)).natTrans.app Y) ≫
        ((mateEquiv adj₂ adj₂).symm (TwoSquare.mk _ _ _ _ α₂)).natTrans.app (L₁.obj Y) ≫
        E₃.map (i.hom.app Y) := by
  have hσ (Z : C₁) : adj₁₂.unit.app Z ≫ R₁₂.map (i.inv.app Z) =
      (adj₁.comp adj₂).unit.app Z ≫ τ.app ((L₁ ⋙ L₂).obj Z) := by rw [← unit_conjugateEquiv, h]
  have hnat₂ : adj₂.unit.app (L₁.obj (E₁.obj Y)) ≫
      R₂.map (L₂.map (((mateEquiv adj₁ adj₁).symm (TwoSquare.mk _ _ _ _ α₁)).natTrans.app Y)) =
    (((mateEquiv adj₁ adj₁).symm (TwoSquare.mk _ _ _ _ α₁)).natTrans.app Y) ≫
      adj₂.unit.app (E₂.obj (L₁.obj Y)) :=
    (adj₂.unit.naturality
      (((mateEquiv adj₁ adj₁).symm (TwoSquare.mk _ _ _ _ α₁)).natTrans.app Y)).symm
  have hnatα₁ : α₁.app (L₁.obj Y) ≫ R₁.map (E₂.map (adj₂.unit.app (L₁.obj Y))) =
      E₁.map (R₁.map (adj₂.unit.app (L₁.obj Y))) ≫ α₁.app (R₂.obj (L₂.obj (L₁.obj Y))) :=
    (α₁.naturality (adj₂.unit.app (L₁.obj Y))).symm
  apply (adj₁₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, reassoc_of% hσ,
    Adjunction.comp_unit_app, Functor.comp_obj, assoc, unit_comp_map_mateEquiv_symm]
  rw [← τ.naturality_assoc, ← τ.naturality_assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  rw [← Functor.map_comp_assoc R₁, hnat₂, Functor.map_comp_assoc R₁,
    unit_comp_map_mateEquiv_symm_assoc adj₁ α₁, ← Functor.map_comp_assoc R₁,
    unit_comp_map_mateEquiv_symm adj₂ α₂, Functor.map_comp_assoc R₁,
    reassoc_of% hnatα₁, reassoc_of% (hτ (L₂.obj (L₁.obj Y))),
    ← Functor.map_comp_assoc E₁, ← Functor.map_comp_assoc E₁]
  have hσ' : (adj₁.unit.app Y ≫ R₁.map (adj₂.unit.app (L₁.obj Y))) ≫ τ.app (L₂.obj (L₁.obj Y)) =
      adj₁₂.unit.app Y ≫ R₁₂.map (i.inv.app Y) := by
    simpa [Adjunction.comp_unit_app, Functor.comp_obj] using (hσ Y).symm
  have hnatα₁₂ : E₁.map (R₁₂.map (i.inv.app Y)) ≫ α₁₂.app (L₂.obj (L₁.obj Y)) =
      α₁₂.app (L₁₂.obj Y) ≫ R₁₂.map (E₃.map (i.inv.app Y)) := α₁₂.naturality (i.inv.app Y)
  rw [hσ', Functor.map_comp_assoc E₁, reassoc_of% hnatα₁₂, ← Functor.map_comp R₁₂,
    ← Functor.map_comp E₃, Iso.inv_hom_id_app, E₃.map_id, R₁₂.map_id, comp_id]

variable {E : Type u} [SmallCategory E] {L : GrothendieckTopology E}
  [L.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {G : D ⥤ E} [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L] {T : Sheaf L CommRingCat.{u}}
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj (ringCatSheaf T))
  [(SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]

/-- The pullback comparison for exterior powers along a composite is the composite of the two
pullback comparisons, read through `SheafOfModules.pullbackComp`. -/
theorem pullback_comp_pullbackExteriorPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackExteriorPowerComparison (F := F ⋙ G) (R := T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n).app M =
      (SheafOfModules.pullbackComp φ ψ).inv.app ((exteriorPower S n).obj M) ≫
        (SheafOfModules.pullback ψ).map ((pullbackExteriorPowerComparison φ n).app M) ≫
        (pullbackExteriorPowerComparison ψ n).app ((SheafOfModules.pullback φ).obj M) ≫
        (exteriorPower T n).map ((SheafOfModules.pullbackComp φ ψ).hom.app M) :=
  mateEquiv_symm_comp_of_conjugateEquiv
    (SheafOfModules.pullbackPushforwardAdjunction φ)
    (SheafOfModules.pullbackPushforwardAdjunction ψ)
    (SheafOfModules.pullbackPushforwardAdjunction (F := F ⋙ G) (R := ringCatSheaf T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
    (pushforwardExteriorPowerComparison φ n) (pushforwardExteriorPowerComparison ψ n)
    (pushforwardExteriorPowerComparison (F := F ⋙ G) (R := T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n)
    (SheafOfModules.pullbackComp φ ψ) (SheafOfModules.conjugateEquiv_pullbackComp_inv φ ψ)
    (pushforwardComp_pushforwardExteriorPowerComparison φ ψ n) M

end Comp

section Free

variable [F.Final]

/-- The transpose of `pullbackObjFreeIso` along the pullback--pushforward adjunction sends each
tautological basis section `freeSection i` over `W` to `freeSection i` over `F(W)`. -/
theorem homEquiv_pullbackObjFreeIso_hom_val_app_freeSection (I : Type u) (W : Cᵒᵖ) (i : I) :
    ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv (free I) (free I)
        (SheafOfModules.pullbackObjFreeIso φ I).hom).val.app W
      ((freeSection (R := ringCatSheaf S) i).eval W) =
    (freeSection (R := ringCatSheaf R) i).eval (F.op.obj W) := by
  have h : ιFree i ≫ (SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv (free I) (free I)
      (SheafOfModules.pullbackObjFreeIso φ I).hom =
    SheafOfModules.unitToPushforwardObjUnit φ ≫ (SheafOfModules.pushforward φ).map (ιFree i) := by
    rw [← Adjunction.homEquiv_naturality_left,
      SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom,
      Adjunction.homEquiv_naturality_right,
      SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  have hW := congrArg (fun p ↦ p.val.app W (1 : S.obj.obj W)) h
  change ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv (free I) (free I)
        (SheafOfModules.pullbackObjFreeIso φ I).hom).val.app W
      ((freeSection (R := ringCatSheaf S) i).eval W) =
    (ιFree (R := ringCatSheaf R) i).val.app (F.op.obj W)
      (((commRingCatHom φ).app W).hom (1 : S.obj.obj W)) at hW
  exact hW.trans (congrArg
    (fun r : R.obj.obj (F.op.obj W) ↦ (ιFree (R := ringCatSheaf R) i).val.app (F.op.obj W) r)
    (map_one ((commRingCatHom φ).app W).hom))

/-- For a free sheaf on a finite linearly ordered type `I`, the exterior-power pullback comparison
intertwines `exteriorPowerFreeIso` with `pullbackObjFreeIso` on `Set.powersetCard I n`. -/
@[reassoc]
theorem pullbackExteriorPowerComparison_free (I : Type u) [Finite I] [LinearOrder I] (n : ℕ) :
    (pullbackExteriorPowerComparison φ n).app (free I) ≫
      (exteriorPower R n).map (SheafOfModules.pullbackObjFreeIso φ I).hom ≫
      (exteriorPowerFreeIso (R := R) I n).hom =
    (SheafOfModules.pullback φ).map (exteriorPowerFreeIso (R := S) I n).hom ≫
      (SheafOfModules.pullbackObjFreeIso φ (Set.powersetCard I n)).hom := by
  let A := SheafOfModules.pullbackPushforwardAdjunction φ
  let gI := A.homEquiv (free I) (free I) (SheafOfModules.pullbackObjFreeIso φ I).hom
  let gP := A.homEquiv (free (Set.powersetCard I n)) (free (Set.powersetCard I n))
    (SheafOfModules.pullbackObjFreeIso φ (Set.powersetCard I n)).hom
  apply (A.homEquiv ((exteriorPower S n).obj (free I)) (free (Set.powersetCard I n))).injective
  have hL : A.homEquiv ((exteriorPower S n).obj (free I)) (free (Set.powersetCard I n))
      ((pullbackExteriorPowerComparison φ n).app (free I) ≫
        (exteriorPower R n).map (SheafOfModules.pullbackObjFreeIso φ I).hom ≫
        (exteriorPowerFreeIso (R := R) I n).hom) =
      (exteriorPower S n).map gI ≫ (pushforwardExteriorPowerComparison φ n).app (free I) ≫
        (SheafOfModules.pushforward φ).map (exteriorPowerFreeIso (R := R) I n).hom := by
    have hnat :
        (pushforwardExteriorPowerComparison φ n).app ((SheafOfModules.pullback φ).obj (free I)) ≫
          (SheafOfModules.pushforward φ).map
            ((exteriorPower R n).map (SheafOfModules.pullbackObjFreeIso φ I).hom) =
        (exteriorPower S n).map
          ((SheafOfModules.pushforward φ).map (SheafOfModules.pullbackObjFreeIso φ I).hom) ≫
          (pushforwardExteriorPowerComparison φ n).app (free I) :=
      ((pushforwardExteriorPowerComparison φ n).naturality
        (SheafOfModules.pullbackObjFreeIso φ I).hom).symm
    rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
      unit_comp_pushforward_pullbackExteriorPowerComparison_assoc, reassoc_of% hnat,
      ← Functor.map_comp_assoc (exteriorPower S n), ← Adjunction.homEquiv_unit]
  rw [hL, A.homEquiv_naturality_left]
  apply exteriorPower_hom_ext
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
    toExteriorPower_comp_forget_map_exteriorPower_map_assoc,
    toExteriorPower_comp_forget_map_exteriorPowerFreeIso_hom_assoc]
  have hmid : toExteriorPower n ((SheafOfModules.pushforward φ).obj (free I)) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map
        ((pushforwardExteriorPowerComparison φ n).app (free I)) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map
        ((SheafOfModules.pushforward φ).map (exteriorPowerFreeIso (R := R) I n).hom) =
    (presheafPushforwardExteriorPowerComparison φ n).app (free I).val ≫
      (presheafPushforward φ).map (presheafExteriorPowerFreeIso (R := R) I n).hom :=
    (Category.assoc _ _ _).symm.trans ((eq_whisker
      (toExteriorPower_comp_forget_map_pushforwardExteriorPowerComparison φ n (free I)) _).trans
      ((Category.assoc _ _ _).trans (whisker_eq _
        (((presheafPushforward φ).map_comp (toExteriorPower n (free I))
          ((SheafOfModules.forget (ringCatSheaf R)).map
            (exteriorPowerFreeIso (R := R) I n).hom)).symm.trans
          (congrArg (presheafPushforward φ).map
            (toExteriorPower_comp_forget_map_exteriorPowerFreeIso_hom (R := R) I n))))))
  refine (whisker_eq ((presheafExteriorPower S n).map gI.val) hmid).trans ?_
  ext W : 1; ext : 1
  refine ((freeBasis (R := S) I W).exteriorPower n).ext fun s ↦ ?_
  have hI (i : I) : gI.val.app W (freeBasis (R := S) I W i) =
      freeBasis (R := R) I (F.op.obj W) i := by
    rw [TauCeti.SheafOfModules.freeBasis_apply, TauCeti.SheafOfModules.freeBasis_apply]
    exact homEquiv_pullbackObjFreeIso_hom_val_app_freeSection φ I W i
  have hP_basis :
      (((presheafExteriorPower S n).map gI.val ≫
        (presheafPushforwardExteriorPowerComparison φ n).app (free I).val).app W)
          ((freeBasis (R := S) I W).exteriorPower n s) =
        (freeBasis (R := R) I (F.op.obj W)).exteriorPower n s := by
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
    have h1 : ((presheafExteriorPower S n).map gI.val).app W
        (exteriorPower.ιMulti_family (S.obj.obj W) n (freeBasis (R := S) I W) s) =
      ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj
        ((presheafPushforward φ).obj (free (R := ringCatSheaf R) I).val) W)
        (fun j ↦ gI.val.app W (freeBasis (R := S) I W (Set.powersetCard.ofFinEmbEquiv.symm s j))) :=
      ModuleCat.exteriorPower.map_mk (gI.val.app' W) _
    exact ((congrArg (((presheafPushforwardExteriorPowerComparison φ n).app (free I).val).app W)
      h1).trans (presheafPushforwardExteriorPowerComparison_app_app_mk φ n
        (free (R := ringCatSheaf R) I).val W _)).trans (congrArg _ (funext fun j ↦ hI _))
  have hFreeIso {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
      [J'.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [HasWeakSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
      {R' : Sheaf J' CommRingCat.{u}} (V : C'ᵒᵖ) :
      (presheafExteriorPowerFreeIso (R := R') I n).hom.app V
          ((freeBasis (R := R') I V).exteriorPower n s) =
        (freeSection (R := ringCatSheaf R') s).eval V := by
    rw [exteriorPower.basis_apply, show (freeBasis (R := R') I V : I → _) =
      fun i ↦ (freeSection (R := ringCatSheaf R') i).eval V from
        funext fun i ↦ TauCeti.SheafOfModules.freeBasis_apply I V i]
    exact presheafExteriorPowerFreeIso_hom_app_ιMulti_family I n V s
  exact ((congrArg ((presheafExteriorPowerFreeIso (R := R) I n).hom.app (F.op.obj W))
      hP_basis).trans (hFreeIso (F.op.obj W))).trans
    ((congrArg (gP.val.app W) (hFreeIso W)).trans
      (homEquiv_pullbackObjFreeIso_hom_val_app_freeSection φ (Set.powersetCard I n) W s)).symm

/-- For a free sheaf on a finite type `I`, the exterior-power pullback comparison is an
isomorphism when the underlying site functor is final. -/
instance isIso_pullbackExteriorPowerComparison_free (I : Type u) [Finite I] (n : ℕ) :
    IsIso ((pullbackExteriorPowerComparison φ n).app (free I)) := by
  classical
  let _ : LinearOrder I := linearOrderOfSTO WellOrderingRel
  have h := pullbackExteriorPowerComparison_free φ I n
  have : IsIso ((pullbackExteriorPowerComparison φ n).app (free I) ≫
      (exteriorPower R n).map (SheafOfModules.pullbackObjFreeIso φ I).hom ≫
      (exteriorPowerFreeIso (R := R) I n).hom) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((exteriorPower R n).map (SheafOfModules.pullbackObjFreeIso φ I).hom ≫
      (exteriorPowerFreeIso (R := R) I n).hom)

end Free

end SheafOfModules

end
