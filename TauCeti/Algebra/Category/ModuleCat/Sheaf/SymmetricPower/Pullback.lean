/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower.RestrictScalars
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward

/-!
# Pushforward and Pullback Comparisons for Symmetric Powers of Sheaves of Modules

Given a continuous functor `F : C ⥤ D` between Grothendieck sites, sheaves of commutative rings
`S : Sheaf J CommRingCat.{u}` and `R : Sheaf K CommRingCat.{u}`, and a morphism
`φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R)`, we
construct the natural pushforward and pullback comparison transformations for `n`-th symmetric
powers of sheaves of modules:
* `SheafOfModules.pushforwardSymmetricPowerComparison φ n`, obtained by sheafifying the
  sectionwise restriction-of-scalars comparison `presheafPushforwardSymmetricPowerComparison`;
* `SheafOfModules.pullbackSymmetricPowerComparison φ n`, obtained as the mate of
  `pushforwardSymmetricPowerComparison φ n` under `SheafOfModules.pullbackPushforwardAdjunction φ`.

We prove identity and composition laws, invertibility along site adjunctions, and compatibility with
`symmetricPowerFreeIso` and `pullbackObjFreeIso` on finite free sheaves.
-/

public section

open CategoryTheory Category Limits Opposite
open TauCeti.ModuleCat (restrictScalarsSymmetricPowerComparison
  coe_restrictScalarsSymmetricPowerComparison_app_apply)
open TauCeti.SymmetricAlgebra (homogeneousSubmoduleMapₛₗ_symmetricAlgebraHomogeneous
  coe_homogeneousSubmoduleMapₛₗ_apply)
open TauCeti.SheafOfModules (ringCatSheaf sheafificationIso sheafificationIso_hom
  sheafificationIso_hom_naturality sheafificationForgetAdjunction
  sheafificationForgetAdjunction_counit_app presheafPushforward presheafPushforward_map_map
  freeBasis freeBasis_apply)

universe u

noncomputable section

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

/-- The sectionwise `n`-th symmetric power of presheaves of modules, with source and target written
as presheaves of modules over `(ringCatSheaf R).obj`. -/
@[expose]
def presheafSymmetricPower (R : Sheaf J CommRingCat.{u}) (n : ℕ) :
    PresheafOfModules.{u} (ringCatSheaf R).obj ⥤ PresheafOfModules.{u} (ringCatSheaf R).obj :=
  PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n

section Sym

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

private def symmetricPowerUnderlyingIso (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (symmetricPower R n).obj M ≅ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
      ((presheafSymmetricPower R n).obj M.val) := symmetricPowerIso n M

/-- The canonical morphism from the sectionwise `n`-th symmetric power of `M` to the underlying
presheaf of the sheafified `n`-th symmetric power `Symⁿ M`. -/
def toSymmetricPower (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (presheafSymmetricPower R n).obj M.val ⟶
      (SheafOfModules.forget (ringCatSheaf R)).obj ((symmetricPower R n).obj M) :=
  (sheafificationForgetAdjunction R).unit.app ((presheafSymmetricPower R n).obj M.val) ≫
    (SheafOfModules.forget (ringCatSheaf R)).map (symmetricPowerUnderlyingIso n M).inv

private theorem toSymmetricPower_comp_forget_map (n : ℕ)
    {M N : SheafOfModules.{u} (ringCatSheaf R)} (p : (symmetricPower R n).obj M ⟶ N) :
    toSymmetricPower n M ≫ (SheafOfModules.forget (ringCatSheaf R)).map p =
      (sheafificationForgetAdjunction R).homEquiv ((presheafSymmetricPower R n).obj M.val) N
        ((symmetricPowerUnderlyingIso n M).inv ≫ p) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← assoc, toSymmetricPower]

private theorem symmetricPower_hom_ext (n : ℕ) {M N : SheafOfModules.{u} (ringCatSheaf R)}
    {p q : (symmetricPower R n).obj M ⟶ N}
    (h : toSymmetricPower n M ≫ (SheafOfModules.forget (ringCatSheaf R)).map p =
      toSymmetricPower n M ≫ (SheafOfModules.forget (ringCatSheaf R)).map q) : p = q := by
  rw [toSymmetricPower_comp_forget_map, toSymmetricPower_comp_forget_map] at h
  exact (cancel_epi _).mp (((sheafificationForgetAdjunction R).homEquiv _ _).injective h)

@[reassoc]
private theorem toSymmetricPower_comp_forget_map_symmetricPower_map (n : ℕ)
    {M N : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) : toSymmetricPower n M ≫
      (SheafOfModules.forget (ringCatSheaf R)).map ((symmetricPower R n).map f) =
    (presheafSymmetricPower R n).map f.val ≫ toSymmetricPower n N := by
  have hm : (symmetricPower R n).map f = (symmetricPowerUnderlyingIso n M).hom ≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        ((presheafSymmetricPower R n).map f.val) ≫ (symmetricPowerUnderlyingIso n N).inv :=
    symmetricPower_map n f
  rw [toSymmetricPower_comp_forget_map, hm, Iso.inv_hom_id_assoc,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit, ← toSymmetricPower]

@[reassoc]
private theorem toSymmetricPower_comp_forget_map_symmetricPowerFreeIso_hom
    (I : Type u) [Finite I] (n : ℕ) : toSymmetricPower (R := R) n (free I) ≫
      (SheafOfModules.forget (ringCatSheaf R)).map (symmetricPowerFreeIso (R := R) I n).hom =
    (presheafSymmetricPowerFreeIso (R := R) I n).hom := by
  have hf : (symmetricPowerFreeIso (R := R) I n).hom =
      (symmetricPowerUnderlyingIso n (free I)).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          (presheafSymmetricPowerFreeIso (R := R) I n).hom ≫
        (sheafificationIso (ringCatSheaf R) (free _)).hom := symmetricPowerFreeIso_hom I n
  rw [toSymmetricPower_comp_forget_map, hf, Iso.inv_hom_id_assoc,
    ← sheafificationForgetAdjunction_counit_app]
  exact (congrArg _ ((sheafificationForgetAdjunction R).homEquiv_counit _ _ _).symm).trans
    (Equiv.apply_symm_apply _ _)

end Sym

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  {F : C ⥤ D} [F.IsContinuous J K] {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))

/-- The sectionwise ring homomorphism `S(U) →+* R(F(U))` underlying `φ`. -/
abbrev ringHom (U : Cᵒᵖ) : ((sheafToPresheaf J CommRingCat).obj S).obj U →+*
    ((sheafToPresheaf K CommRingCat).obj R).obj (F.op.obj U) := (φ.hom.app U).hom

private def presheafPushforwardSymmetricPowerApp (n : ℕ)
    (M : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    (presheafSymmetricPower S n).obj ((presheafPushforward φ).obj M) ⟶
      (presheafPushforward φ).obj ((presheafSymmetricPower R n).obj M) where
  app U := (restrictScalarsSymmetricPowerComparison (ringHom φ U) n).app
    (PresheafOfModulesOfCommRing.obj M (F.op.obj U))
  naturality {U V} f := by
    let MU := PresheafOfModulesOfCommRing.obj M (F.op.obj U)
    let MV := PresheafOfModulesOfCommRing.obj M (F.op.obj V)
    let PM := (presheafPushforward φ).obj M; let PMU := PresheafOfModulesOfCommRing.obj PM U
    let PMV := PresheafOfModulesOfCommRing.obj PM V
    let g₁ := (ModuleCat.semilinearMapAddEquiv (S.obj.map f).hom PMU PMV).symm (PM.map f)
    let g₂ := (ModuleCat.semilinearMapAddEquiv (ringHom φ V) PMV MV).symm (𝟙 PMV)
    let h₁ := (ModuleCat.semilinearMapAddEquiv (ringHom φ U) PMU MU).symm (𝟙 PMU)
    let h₂ := (ModuleCat.semilinearMapAddEquiv (R.obj.map (F.op.map f)).hom MU MV).symm
      (M.map (F.op.map f))
    have : RingHomCompTriple (ringHom φ U) (R.obj.map (F.op.map f)).hom
      ((R.obj.map (F.op.map f)).hom.comp (ringHom φ U)) := ⟨rfl⟩
    have key : (SymmetricAlgebra.mapₛₗ g₂).comp (SymmetricAlgebra.mapₛₗ g₁) =
        (SymmetricAlgebra.mapₛₗ h₂).comp (SymmetricAlgebra.mapₛₗ h₁) :=
      (SymmetricAlgebra.mapₛₗ_comp_mapₛₗ g₁ g₂ (h₂.comp h₁)
        (fun r ↦ congr($(φ.hom.naturality f).hom r)) (fun _ ↦ rfl)).trans
        (SymmetricAlgebra.mapₛₗ_comp_mapₛₗ h₁ h₂ (h₂.comp h₁) (fun _ ↦ rfl) (fun _ ↦ rfl)).symm
    ext x; apply Subtype.ext
    exact ((coe_restrictScalarsSymmetricPowerComparison_app_apply (ringHom φ V) n MV _).trans
      (congrArg _ (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n PM f x))).trans
      ((RingHom.congr_fun key x.1).trans
        ((congrArg _ (coe_restrictScalarsSymmetricPowerComparison_app_apply
          (ringHom φ U) n MU x).symm).trans
          (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n M (F.op.map f) _).symm))

/-- The sectionwise restriction-of-scalars comparison for symmetric powers, written between
`presheafPushforward` and `presheafSymmetricPower`. -/
def presheafPushforwardSymmetricPowerComparison (n : ℕ) :
    presheafPushforward φ ⋙ presheafSymmetricPower S n ⟶
      presheafSymmetricPower R n ⋙ presheafPushforward φ where
  app := presheafPushforwardSymmetricPowerApp φ n
  naturality {M N} f := by
    ext U : 1
    exact (restrictScalarsSymmetricPowerComparison (ringHom φ U) n).naturality (f.app' (F.op.obj U))

/-- On sections over `U`, `presheafPushforwardSymmetricPowerComparison` acts in the ambient
symmetric algebra by the canonical semilinear map over `ringHom φ U`. -/
theorem coe_presheafPushforwardSymmetricPowerComparison_app_app_apply (n : ℕ)
    (M : PresheafOfModules.{u} (ringCatSheaf R).obj) (U : Cᵒᵖ)
    (x : (PresheafOfModulesOfCommRing.obj ((presheafPushforward φ).obj M) U).symmetricPower n) :
    Subtype.val ((((presheafPushforwardSymmetricPowerComparison φ n).app M).app' U) x) =
      SymmetricAlgebra.mapₛₗ ((ModuleCat.semilinearMapAddEquiv (ringHom φ U)
          (PresheafOfModulesOfCommRing.obj ((presheafPushforward φ).obj M) U)
          (PresheafOfModulesOfCommRing.obj M (F.op.obj U))).symm
        (𝟙 (PresheafOfModulesOfCommRing.obj ((presheafPushforward φ).obj M) U))) x.1 :=
  coe_restrictScalarsSymmetricPowerComparison_app_apply
    (ringHom φ U) n (PresheafOfModulesOfCommRing.obj M (F.op.obj U)) x

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

private def pushforwardSymmetricPowerMap (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (symmetricPower S n).obj ((pushforward φ).obj M) ⟶
      (pushforward φ).obj ((symmetricPower R n).obj M) :=
  (symmetricPowerUnderlyingIso n ((pushforward φ).obj M)).hom ≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf S).obj)).map
      ((presheafPushforwardSymmetricPowerComparison φ n).app M.val ≫
        (presheafPushforward φ).map (toSymmetricPower n M)) ≫
    (sheafificationIso (ringCatSheaf S) ((pushforward φ).obj ((symmetricPower R n).obj M))).hom

@[reassoc]
private theorem toSymmetricPower_comp_pushforwardSymmetricPowerMap (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    toSymmetricPower n ((pushforward φ).obj M) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map (pushforwardSymmetricPowerMap φ n M) =
    (presheafPushforwardSymmetricPowerComparison φ n).app M.val ≫
      (presheafPushforward φ).map (toSymmetricPower n M) := by
  rw [pushforwardSymmetricPowerMap, toSymmetricPower_comp_forget_map, Iso.inv_hom_id_assoc,
    ← sheafificationForgetAdjunction_counit_app]
  exact (congrArg _ ((sheafificationForgetAdjunction S).homEquiv_counit _ _ _).symm).trans
    (Equiv.apply_symm_apply _ _)

/-- The canonical comparison `Symⁿ (φ_* M) ⟶ φ_* (Symⁿ M)` for pushforward of sheaves of modules,
obtained by sheafifying `presheafPushforwardSymmetricPowerComparison`. -/
def pushforwardSymmetricPowerComparison (n : ℕ) :
    pushforward φ ⋙ symmetricPower S n ⟶ symmetricPower R n ⋙ pushforward φ where
  app M := pushforwardSymmetricPowerMap φ n M
  naturality {M N} f := by
    apply symmetricPower_hom_ext
    simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp,
      toSymmetricPower_comp_forget_map_symmetricPower_map_assoc,
      toSymmetricPower_comp_pushforwardSymmetricPowerMap,
      toSymmetricPower_comp_pushforwardSymmetricPowerMap_assoc]
    have e : (presheafSymmetricPower R n ⋙ presheafPushforward φ).map f.val ≫
        (presheafPushforward φ).map (toSymmetricPower n N) =
      (presheafPushforward φ).map (toSymmetricPower n M) ≫
        (SheafOfModules.forget (ringCatSheaf S)).map
          ((pushforward φ).map ((symmetricPower R n).map f)) := by
      rw [Functor.comp_map, ← Functor.map_comp,
        ← toSymmetricPower_comp_forget_map_symmetricPower_map, Functor.map_comp]; rfl
    exact ((presheafPushforwardSymmetricPowerComparison φ n).naturality_assoc
      f.val ((presheafPushforward φ).map (toSymmetricPower n N))).trans (congrArg _ e)

@[reassoc]
private theorem toSymmetricPower_comp_forget_map_pushforwardSymmetricPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    toSymmetricPower n ((pushforward φ).obj M) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map
        ((pushforwardSymmetricPowerComparison φ n).app M) =
    (presheafPushforwardSymmetricPowerComparison φ n).app M.val ≫
      (presheafPushforward φ).map (toSymmetricPower n M) :=
  toSymmetricPower_comp_pushforwardSymmetricPowerMap φ n M

/-- On sections over `U` coming from the sectionwise symmetric power via `toSymmetricPower`,
`pushforwardSymmetricPowerComparison` applies the sectionwise comparison followed by
`toSymmetricPower` over `F.op.obj U`. -/
theorem pushforwardSymmetricPowerComparison_app_toSymmetricPower (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) (U : Cᵒᵖ)
    (x : (PresheafOfModulesOfCommRing.obj ((presheafPushforward φ).obj M.val) U).symmetricPower n) :
    ((pushforwardSymmetricPowerComparison φ n).app M).val.app U
      ((toSymmetricPower n ((pushforward φ).obj M)).app U x) =
    (toSymmetricPower n M).app (F.op.obj U)
      (((presheafPushforwardSymmetricPowerComparison φ n).app M.val).app U x) :=
  congrArg (fun p ↦ (p.app U).hom x)
    (toSymmetricPower_comp_forget_map_pushforwardSymmetricPowerComparison φ n M)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private def presheafPushforwardIdHom (M : PresheafOfModules.{u} (ringCatSheaf S).obj) :
    (presheafPushforward (F := 𝟭 C) (R := S) (𝟙 (ringCatSheaf S))).obj M ⟶ M := 𝟙 _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma presheafPushforward_id_map_comp {A : PresheafOfModules.{u} (ringCatSheaf S).obj}
    {B : SheafOfModules.{u} (ringCatSheaf S)} (f : A ⟶ B.val) :
    (presheafPushforward (F := 𝟭 C) (R := S) (𝟙 (ringCatSheaf S))).map f ≫
      (SheafOfModules.forget (ringCatSheaf S)).map ((pushforwardId (ringCatSheaf S)).hom.app B) =
    presheafPushforwardIdHom A ≫ f := by ext U x; rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
@[reassoc]
private theorem presheafPushforwardSymmetricPowerComparison_id (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (presheafPushforwardSymmetricPowerComparison (F := 𝟭 C) (R := S)
        (𝟙 (ringCatSheaf S)) n).app M.val ≫
      presheafPushforwardIdHom ((presheafSymmetricPower S n).obj M.val) =
    (presheafSymmetricPower S n).map ((SheafOfModules.forget (ringCatSheaf S)).map
      ((pushforwardId (ringCatSheaf S)).hom.app M)) := by
  ext U x; apply Subtype.ext; let MU := PresheafOfModulesOfCommRing.obj M.val U
  let PMU := PresheafOfModulesOfCommRing.obj
    ((presheafPushforward (F := 𝟭 C) (R := S) (𝟙 (ringCatSheaf S))).obj M.val) U
  let iU : PMU ⟶ MU := (((pushforwardId (ringCatSheaf S)).hom.app M).val).app' U
  let f := (ModuleCat.semilinearMapAddEquiv
    (ringHom (F := 𝟭 C) (R := S) (𝟙 (ringCatSheaf S)) U) PMU MU).symm (𝟙 PMU)
  have hfi : SymmetricAlgebra.mapₛₗ f = SymmetricAlgebra.mapₛₗ iU.hom := by ext y <;> rfl
  have hi := RingHom.congr_fun (hfi.trans (SymmetricAlgebra.mapₛₗ_eq_map iU.hom)) x.1
  exact (coe_presheafPushforwardSymmetricPowerComparison_app_app_apply (F := 𝟭 C) (R := S)
      (𝟙 (ringCatSheaf S)) n M.val U x).trans
    (hi.trans (ModuleCat.symmetricPower.coe_map_apply iU n x).symm)

/-- The pushforward comparison for the identity ring-sheaf morphism is the identity, read through
`SheafOfModules.pushforwardId`. -/
@[reassoc]
theorem pushforwardId_pushforwardSymmetricPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (pushforwardSymmetricPowerComparison (F := 𝟭 C) (R := S) (𝟙 (ringCatSheaf S)) n).app M ≫
      (pushforwardId (ringCatSheaf S)).hom.app ((symmetricPower S n).obj M) =
    (symmetricPower S n).map ((pushforwardId (ringCatSheaf S)).hom.app M) := by
  apply symmetricPower_hom_ext n (M := (pushforward (F := 𝟭 C) (𝟙 (ringCatSheaf S))).obj M)
  rw [Functor.map_comp, toSymmetricPower_comp_forget_map_symmetricPower_map]
  refine (toSymmetricPower_comp_forget_map_pushforwardSymmetricPowerComparison_assoc
    (F := 𝟭 C) (R := S) (𝟙 (ringCatSheaf S)) n M _).trans ?_
  exact (whisker_eq _ (presheafPushforward_id_map_comp (toSymmetricPower n M))).trans
    (presheafPushforwardSymmetricPowerComparison_id_assoc n M (toSymmetricPower n M))

@[reassoc]
private lemma unit_comp_map_mateEquiv_symm {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : L ⊣ R) {E₁ : C₁ ⥤ C₁} {E₂ : C₂ ⥤ C₂}
    (α : R ⋙ E₁ ⟶ E₂ ⋙ R) (Y : C₁) : adj.unit.app (E₁.obj Y) ≫
      R.map (((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ α)).natTrans.app Y) =
    E₁.map (adj.unit.app Y) ≫ α.app (L.obj Y) :=
  (unit_mateEquiv_symm adj adj (TwoSquare.mk _ _ _ _ α) Y).symm

variable [(pushforward.{u} φ).IsRightAdjoint]

/-- The canonical comparison `φ^* (Symⁿ M) ⟶ Symⁿ (φ^* M)` for pullback of sheaves of modules,
obtained as the mate of `pushforwardSymmetricPowerComparison φ n`. -/
def pullbackSymmetricPowerComparison (n : ℕ) :
    symmetricPower S n ⋙ pullback φ ⟶ pullback φ ⋙ symmetricPower R n :=
  let A := pullbackPushforwardAdjunction φ
  ((mateEquiv A A).symm (TwoSquare.mk _ _ _ _ (pushforwardSymmetricPowerComparison φ n))).natTrans

/-- The adjunction unit equation characterizing `pullbackSymmetricPowerComparison`. -/
@[reassoc (attr := simp)]
theorem unit_comp_pushforward_pullbackSymmetricPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackPushforwardAdjunction φ).unit.app ((symmetricPower S n).obj M) ≫
      (pushforward φ).map ((pullbackSymmetricPowerComparison φ n).app M) =
    (symmetricPower S n).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
      (pushforwardSymmetricPowerComparison φ n).app ((pullback φ).obj M) :=
  (unit_mateEquiv_symm (pullbackPushforwardAdjunction φ) (pullbackPushforwardAdjunction φ)
    (TwoSquare.mk _ _ _ _ (pushforwardSymmetricPowerComparison φ n)) M).symm

/-- `pullbackSymmetricPowerComparison` is the transpose under `pullbackPushforwardAdjunction φ` of
the symmetric power of the unit followed by `pushforwardSymmetricPowerComparison`. -/
theorem pullbackSymmetricPowerComparison_app (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackSymmetricPowerComparison φ n).app M =
      ((pullbackPushforwardAdjunction φ).homEquiv ((symmetricPower S n).obj M)
        ((symmetricPower R n).obj ((pullback φ).obj M))).symm
        ((symmetricPower S n).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
          (pushforwardSymmetricPowerComparison φ n).app ((pullback φ).obj M)) := by
  apply ((pullbackPushforwardAdjunction φ).homEquiv ((symmetricPower S n).obj M)
    ((symmetricPower R n).obj ((pullback φ).obj M))).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact unit_comp_pushforward_pullbackSymmetricPowerComparison φ n M

section Comp

variable {E : Type u} [SmallCategory E] {L : GrothendieckTopology E}
  [L.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  {G : D ⥤ E} [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L] {T : Sheaf L CommRingCat.{u}}
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj (ringCatSheaf T))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(pushforward.{u} φ).IsRightAdjoint] in
private def presheafPushforwardCompHom (M : PresheafOfModules.{u} (ringCatSheaf T).obj) :
    (presheafPushforward φ).obj ((presheafPushforward ψ).obj M) ⟶
      (presheafPushforward (F := F ⋙ G) (R := T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).obj M := 𝟙 _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(pushforward.{u} φ).IsRightAdjoint] in
private lemma presheafPushforward_comp_map_comp {A : PresheafOfModules.{u} (ringCatSheaf T).obj}
    {B : SheafOfModules.{u} (ringCatSheaf T)} (f : A ⟶ B.val) :
    (presheafPushforward φ).map ((presheafPushforward ψ).map f) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map ((pushforwardComp φ ψ).hom.app B) =
    presheafPushforwardCompHom φ ψ A ≫ (presheafPushforward (F := F ⋙ G) (R := T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).map f := by ext U x; rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(pushforward.{u} φ).IsRightAdjoint] in
@[reassoc]
private theorem presheafPushforwardSymmetricPowerComparison_comp (n : ℕ)
    (M : PresheafOfModules.{u} (ringCatSheaf T).obj) :
    (presheafPushforwardSymmetricPowerComparison φ n).app ((presheafPushforward ψ).obj M) ≫
      (presheafPushforward φ).map ((presheafPushforwardSymmetricPowerComparison ψ n).app M) ≫
      presheafPushforwardCompHom φ ψ ((presheafSymmetricPower T n).obj M) =
    (presheafSymmetricPower S n).map (presheafPushforwardCompHom φ ψ M) ≫
      (presheafPushforwardSymmetricPowerComparison (F := F ⋙ G) (R := T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n).app M := by
  ext U x; apply Subtype.ext; let MGFU := PresheafOfModulesOfCommRing.obj M (G.op.obj (F.op.obj U))
  let PMFU := PresheafOfModulesOfCommRing.obj ((presheafPushforward ψ).obj M) (F.op.obj U)
  let PPMU := PresheafOfModulesOfCommRing.obj ((presheafPushforward φ).obj
    ((presheafPushforward ψ).obj M)) U
  let P₁₂MU := PresheafOfModulesOfCommRing.obj ((presheafPushforward (F := F ⋙ G)
    (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).obj M) U
  let cU : PPMU ⟶ P₁₂MU := (presheafPushforwardCompHom φ ψ M).app' U
  let g₁ := (ModuleCat.semilinearMapAddEquiv (ringHom φ U) PPMU PMFU).symm (𝟙 PPMU)
  let g₂ := (ModuleCat.semilinearMapAddEquiv (ringHom ψ (F.op.obj U)) PMFU MGFU).symm (𝟙 PMFU)
  let h := (ModuleCat.semilinearMapAddEquiv
    (ringHom (F := F ⋙ G) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) U)
    P₁₂MU MGFU).symm (𝟙 P₁₂MU)
  have key : (SymmetricAlgebra.mapₛₗ g₂).comp (SymmetricAlgebra.mapₛₗ g₁) =
      (SymmetricAlgebra.mapₛₗ h).comp (SymmetricAlgebra.map _ cU.hom : _ →+* _) := by
    rw [← SymmetricAlgebra.mapₛₗ_eq_map cU.hom,
      SymmetricAlgebra.mapₛₗ_comp_mapₛₗ cU.hom h (h.comp cU.hom) (fun _ ↦ rfl) (fun _ ↦ rfl),
      SymmetricAlgebra.mapₛₗ_comp_mapₛₗ g₁ g₂ (h.comp cU.hom) (fun _ ↦ rfl) (fun _ ↦ rfl)]
  have h₁ := coe_presheafPushforwardSymmetricPowerComparison_app_app_apply φ n
    ((presheafPushforward ψ).obj M) U x
  have h₂ := coe_presheafPushforwardSymmetricPowerComparison_app_app_apply ψ n M (F.op.obj U)
    ((((presheafPushforwardSymmetricPowerComparison φ n).app
      ((presheafPushforward ψ).obj M)).app' U) x)
  have h₃ := (coe_presheafPushforwardSymmetricPowerComparison_app_app_apply (F := F ⋙ G)
    (R := T) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n M U _).trans
    (congrArg _ (ModuleCat.symmetricPower.coe_map_apply cU n x))
  exact (h₂.trans (congrArg _ h₁)).trans ((RingHom.congr_fun key x.1).trans h₃.symm)

variable [HasWeakSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [(pushforward.{u} φ).IsRightAdjoint] in
/-- The pushforward comparison for symmetric powers along a composite is the composite of the
pushforward comparisons, read through `SheafOfModules.pushforwardComp`. -/
@[reassoc]
theorem pushforwardComp_pushforwardSymmetricPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf T)) :
    (pushforwardSymmetricPowerComparison φ n).app ((pushforward ψ).obj M) ≫
      (pushforward φ).map ((pushforwardSymmetricPowerComparison ψ n).app M) ≫
      (pushforwardComp φ ψ).hom.app ((symmetricPower T n).obj M) =
    (symmetricPower S n).map ((pushforwardComp φ ψ).hom.app M) ≫
      (pushforwardSymmetricPowerComparison (F := F ⋙ G) (R := T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n).app M := by
  apply symmetricPower_hom_ext; rw [Functor.map_comp, Functor.map_comp,
    toSymmetricPower_comp_forget_map_pushforwardSymmetricPowerComparison_assoc,
    Functor.map_comp, toSymmetricPower_comp_forget_map_symmetricPower_map_assoc,
    toSymmetricPower_comp_forget_map_pushforwardSymmetricPowerComparison]
  have e : (presheafPushforward φ).map (toSymmetricPower n ((pushforward ψ).obj M)) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map
        ((pushforward φ).map ((pushforwardSymmetricPowerComparison ψ n).app M)) =
    (presheafPushforward φ).map ((presheafPushforwardSymmetricPowerComparison ψ n).app M.val) ≫
      (presheafPushforward φ).map ((presheafPushforward ψ).map (toSymmetricPower n M)) := by
    rw [← Functor.map_comp, ← toSymmetricPower_comp_forget_map_pushforwardSymmetricPowerComparison]
    rfl
  exact (Category.assoc _ _ _).trans ((whisker_eq _ ((Category.assoc _ _ _).symm.trans
    ((eq_whisker e _).trans ((Category.assoc _ _ _).trans
      (whisker_eq _ (presheafPushforward_comp_map_comp φ ψ (toSymmetricPower n M))))))).trans
    (presheafPushforwardSymmetricPowerComparison_comp_assoc φ ψ n M.val _))

private theorem mateEquiv_symm_comp_of_conjugateEquiv
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} (adj₁ : L₁ ⊣ R₁) {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂} (adj₂ : L₂ ⊣ R₂)
    {L₁₂ : C₁ ⥤ C₃} {R₁₂ : C₃ ⥤ C₁} (adj₁₂ : L₁₂ ⊣ R₁₂) {E₁ : C₁ ⥤ C₁} {E₂ : C₂ ⥤ C₂} {E₃ : C₃ ⥤ C₃}
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
      adj₂.unit.app (E₂.obj (L₁.obj Y)) := (adj₂.unit.naturality
    (((mateEquiv adj₁ adj₁).symm (TwoSquare.mk _ _ _ _ α₁)).natTrans.app Y)).symm
  have hnatα₁ : α₁.app (L₁.obj Y) ≫ R₁.map (E₂.map (adj₂.unit.app (L₁.obj Y))) =
      E₁.map (R₁.map (adj₂.unit.app (L₁.obj Y))) ≫ α₁.app (R₂.obj (L₂.obj (L₁.obj Y))) :=
    (α₁.naturality (adj₂.unit.app (L₁.obj Y))).symm
  apply (adj₁₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, reassoc_of% hσ,
    Adjunction.comp_unit_app, Functor.comp_obj, assoc, unit_comp_map_mateEquiv_symm]
  rw [← τ.naturality_assoc, ← τ.naturality_assoc]; dsimp only [Functor.comp_obj, Functor.comp_map]
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

variable [(pushforward.{u} ψ).IsRightAdjoint]

/-- The pullback comparison for symmetric powers along a composite is the composite of the two
pullback comparisons, read through `SheafOfModules.pullbackComp`. -/
theorem pullback_comp_pullbackSymmetricPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackSymmetricPowerComparison (F := F ⋙ G) (R := T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n).app M =
      (pullbackComp φ ψ).inv.app ((symmetricPower S n).obj M) ≫
        (pullback ψ).map ((pullbackSymmetricPowerComparison φ n).app M) ≫
        (pullbackSymmetricPowerComparison ψ n).app ((pullback φ).obj M) ≫
        (symmetricPower T n).map ((pullbackComp φ ψ).hom.app M) :=
  mateEquiv_symm_comp_of_conjugateEquiv
    (pullbackPushforwardAdjunction φ) (pullbackPushforwardAdjunction ψ)
    (pullbackPushforwardAdjunction (F := F ⋙ G) (R := ringCatSheaf T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
    (pushforwardSymmetricPowerComparison φ n) (pushforwardSymmetricPowerComparison ψ n)
    (pushforwardSymmetricPowerComparison (F := F ⋙ G) (R := T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) n)
    (pullbackComp φ ψ) (conjugateEquiv_pullbackComp_inv φ ψ)
    (pushforwardComp_pushforwardSymmetricPowerComparison φ ψ n) M

end Comp

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
    (αF : F ⋙ E₂ ⟶ E₁ ⋙ F) (αG : G ⋙ E₁ ⟶ E₂ ⋙ G) (hunit : ∀ X : C₁, adj.unit.app (E₁.obj X) =
      E₁.map (adj.unit.app X) ≫ αG.app (F.obj X) ≫ G.map (αF.app X)) (X : C₁) :
    ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X ≫ αF.app X =
      𝟙 (F.obj (E₁.obj X)) := by
  apply (adj.homEquiv (E₁.obj X) (F.obj (E₁.obj X))).injective
  rw [Adjunction.homEquiv_unit, Functor.map_comp, unit_comp_map_mateEquiv_symm_assoc, ← hunit,
    Adjunction.homEquiv_unit, G.map_id]; exact (comp_id _).symm

private lemma isIso_mateEquiv_symm_of_leftAdjoint {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {F L : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : F ⊣ G) (adj' : L ⊣ G)
    {E₁ : C₁ ⥤ C₁} {E₂ : C₂ ⥤ C₂} (αG : G ⋙ E₁ ⟶ E₂ ⋙ G) (X : C₁)
    [IsIso (((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X)] :
    IsIso (((mateEquiv adj' adj').symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X) := by
  let σ := (Adjunction.leftAdjointUniq adj adj').inv
  have hσ (Z : C₁) : adj'.unit.app Z ≫ G.map (σ.app Z) = adj.unit.app Z := by
    have hc : conjugateEquiv adj adj' σ = 𝟙 G := by simp [σ, Adjunction.leftAdjointUniq]
    have hu := unit_conjugateEquiv adj adj' σ Z
    erw [hc, NatTrans.id_app, comp_id] at hu; exact hu.symm
  have hcomm : σ.app (E₁.obj X) ≫
      ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X =
      ((mateEquiv adj' adj').symm (TwoSquare.mk _ _ _ _ αG)).natTrans.app X ≫ E₂.map (σ.app X) := by
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
    ψ.hom ≫ G.op.whiskerLeft φ.hom) (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op adj.unit) (ringCatSheaf S).obj = 𝟙 (ringCatSheaf S).obj)

omit [(pushforward.{u} φ).IsRightAdjoint] in
private theorem pushforwardPushforwardAdj_unit_app_symmetricPower (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app ((symmetricPower R n).obj M) =
      (symmetricPower R n).map ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M) ≫
        (pushforwardSymmetricPowerComparison ψ n).app ((pushforward φ).obj M) ≫
        (pushforward ψ).map ((pushforwardSymmetricPowerComparison φ n).app M) := by
  apply symmetricPower_hom_ext; ext V x; set η := (pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit
  let cV : V ⟶ F.op.obj (G.op.obj V) := (adj.counit.app V.unop).op
  have hL : ((toSymmetricPower n M ≫ (SheafOfModules.forget (ringCatSheaf R)).map
      (η.app ((symmetricPower R n).obj M))).app V) x =
    (toSymmetricPower n M).app (F.op.obj (G.op.obj V))
      (((presheafSymmetricPower R n).obj M.val).map cV x) :=
    (PresheafOfModules.naturality_apply (toSymmetricPower n M) cV x).symm
  have h₁ := congrArg (fun p ↦ (p.app V).hom x)
    (toSymmetricPower_comp_forget_map_symmetricPower_map n (η.app M))
  have h₂ := pushforwardSymmetricPowerComparison_app_toSymmetricPower ψ n ((pushforward φ).obj M) V
    ((((presheafSymmetricPower R n).map (η.app M).val).app V) x)
  have h₃ := pushforwardSymmetricPowerComparison_app_toSymmetricPower φ n M (G.op.obj V)
    ((((presheafPushforwardSymmetricPowerComparison ψ n).app ((pushforward φ).obj M).val).app V)
      ((((presheafSymmetricPower R n).map (η.app M).val).app V) x))
  have hR := (congrArg (((SheafOfModules.forget (ringCatSheaf R)).map
    ((pushforwardSymmetricPowerComparison ψ n).app ((pushforward φ).obj M) ≫
      (pushforward ψ).map ((pushforwardSymmetricPowerComparison φ n).app M))).app V) h₁).trans
    ((congrArg (((SheafOfModules.forget (ringCatSheaf S)).map
      ((pushforwardSymmetricPowerComparison φ n).app M)).app (G.op.obj V)) h₂).trans h₃)
  refine hL.trans (Eq.trans ?_ hR.symm); congr 1; apply Subtype.ext
  let MV := PresheafOfModulesOfCommRing.obj M.val V
  let MFGV := PresheafOfModulesOfCommRing.obj M.val (F.op.obj (G.op.obj V))
  let PMGV := PresheafOfModulesOfCommRing.obj ((presheafPushforward φ).obj M.val) (G.op.obj V)
  let PPMV := PresheafOfModulesOfCommRing.obj
    ((presheafPushforward ψ).obj ((pushforward φ).obj M).val) V
  let ηV : MV ⟶ PPMV := (η.app M).val.app' V; let f_c := (ModuleCat.semilinearMapAddEquiv
    (((sheafToPresheaf K CommRingCat).obj R).map cV).hom MV MFGV).symm (M.val.map cV)
  let f_ψ := (ModuleCat.semilinearMapAddEquiv (ringHom ψ V) PPMV PMGV).symm (𝟙 PPMV)
  let f_φ := (ModuleCat.semilinearMapAddEquiv (ringHom φ (G.op.obj V)) PMGV MFGV).symm (𝟙 PMGV)
  have key : SymmetricAlgebra.mapₛₗ f_c = (SymmetricAlgebra.mapₛₗ f_φ).comp
      ((SymmetricAlgebra.mapₛₗ f_ψ).comp (SymmetricAlgebra.map _ ηV.hom : _ →+* _)) := by
    rw [← SymmetricAlgebra.mapₛₗ_eq_map ηV.hom,
      SymmetricAlgebra.mapₛₗ_comp_mapₛₗ ηV.hom f_ψ (f_ψ.comp ηV.hom) (fun _ ↦ rfl) (fun _ ↦ rfl),
      SymmetricAlgebra.mapₛₗ_comp_mapₛₗ (f_ψ.comp ηV.hom) f_φ f_c
        (fun r ↦ congr(($(H₁).app V).hom r).symm) (fun _ ↦ rfl)]
  exact (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n M.val cV x).trans
    ((RingHom.congr_fun key x.1).trans ((congrArg _
      ((coe_presheafPushforwardSymmetricPowerComparison_app_app_apply ψ n
        ((pushforward φ).obj M).val V _).trans (congrArg _
        (ModuleCat.symmetricPower.coe_map_apply ηV n x))).symm).trans
      (coe_presheafPushforwardSymmetricPowerComparison_app_app_apply φ n M.val
        (G.op.obj V) _).symm))

omit [(pushforward.{u} φ).IsRightAdjoint] in
private theorem pushforwardPushforwardAdj_counit_app_symmetricPower (n : ℕ)
    (A : SheafOfModules.{u} (ringCatSheaf S)) :
    (pushforwardSymmetricPowerComparison φ n).app ((pushforward ψ).obj A) ≫
      (pushforward φ).map ((pushforwardSymmetricPowerComparison ψ n).app A) ≫
        (pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app ((symmetricPower S n).obj A) =
      (symmetricPower S n).map ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app A) := by
  apply symmetricPower_hom_ext; ext U x; set ε := (pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit
  let uU : G.op.obj (F.op.obj U) ⟶ U := (adj.unit.app U.unop).op
  have h₁ := pushforwardSymmetricPowerComparison_app_toSymmetricPower φ n
    ((pushforward ψ).obj A) U x
  have h₂ := pushforwardSymmetricPowerComparison_app_toSymmetricPower ψ n A (F.op.obj U)
    ((((presheafPushforwardSymmetricPowerComparison φ n).app ((pushforward ψ).obj A).val).app U) x)
  have h₃ := (PresheafOfModules.naturality_apply (toSymmetricPower n A) uU
    ((((presheafPushforwardSymmetricPowerComparison ψ n).app A.val).app (F.op.obj U))
      ((((presheafPushforwardSymmetricPowerComparison φ n).app
        ((pushforward ψ).obj A).val).app U) x))).symm
  have hL := (congrArg (((SheafOfModules.forget (ringCatSheaf S)).map
    ((pushforward φ).map ((pushforwardSymmetricPowerComparison ψ n).app A) ≫
      ε.app ((symmetricPower S n).obj A))).app U) h₁).trans
    ((congrArg (((SheafOfModules.forget (ringCatSheaf S)).map
      (ε.app ((symmetricPower S n).obj A))).app U) h₂).trans h₃)
  have hR : ((toSymmetricPower n ((pushforward φ).obj ((pushforward ψ).obj A)) ≫
      (SheafOfModules.forget (ringCatSheaf S)).map ((symmetricPower S n).map (ε.app A))).app U) x =
      (toSymmetricPower n A).app U ((((presheafSymmetricPower S n).map (ε.app A).val).app U) x) :=
    congrArg (fun p ↦ (p.app U).hom x)
      (toSymmetricPower_comp_forget_map_symmetricPower_map n (ε.app A))
  refine hL.trans (Eq.trans ?_ hR.symm); congr 1; apply Subtype.ext
  let AU := PresheafOfModulesOfCommRing.obj A.val U
  let AGFU := PresheafOfModulesOfCommRing.obj A.val (G.op.obj (F.op.obj U))
  let PAFU := PresheafOfModulesOfCommRing.obj ((presheafPushforward ψ).obj A.val) (F.op.obj U)
  let PPAU := PresheafOfModulesOfCommRing.obj
    ((presheafPushforward φ).obj ((pushforward ψ).obj A).val) U
  let εU : PPAU ⟶ AU := (ε.app A).val.app' U; let f_u := (ModuleCat.semilinearMapAddEquiv
    (((sheafToPresheaf J CommRingCat).obj S).map uU).hom AGFU AU).symm (A.val.map uU)
  let f_φ := (ModuleCat.semilinearMapAddEquiv (ringHom φ U) PPAU PAFU).symm (𝟙 PPAU)
  let f_ψ := (ModuleCat.semilinearMapAddEquiv (ringHom ψ (F.op.obj U)) PAFU AGFU).symm (𝟙 PAFU)
  have : RingHomCompTriple (ringHom φ U) (ringHom ψ (F.op.obj U))
    ((ringHom ψ (F.op.obj U)).comp (ringHom φ U)) := ⟨rfl⟩
  have key : (SymmetricAlgebra.mapₛₗ f_u).comp
      ((SymmetricAlgebra.mapₛₗ f_ψ).comp (SymmetricAlgebra.mapₛₗ f_φ)) =
      (SymmetricAlgebra.map _ εU.hom : _ →+* _) := by
    rw [← SymmetricAlgebra.mapₛₗ_eq_map εU.hom,
      SymmetricAlgebra.mapₛₗ_comp_mapₛₗ f_φ f_ψ (f_ψ.comp f_φ) (fun _ ↦ rfl) (fun _ ↦ rfl),
      SymmetricAlgebra.mapₛₗ_comp_mapₛₗ (f_ψ.comp f_φ) f_u εU.hom
        (fun r ↦ congr(($(H₂).app U).hom r)) (fun _ ↦ rfl)]
  exact ((PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n A.val uU _).trans
    (congrArg _ ((coe_presheafPushforwardSymmetricPowerComparison_app_app_apply ψ n A.val
      (F.op.obj U) _).trans (congrArg _
      (coe_presheafPushforwardSymmetricPowerComparison_app_app_apply φ n
        ((pushforward ψ).obj A).val U x))))).trans
    ((RingHom.congr_fun key x.1).trans (ModuleCat.symmetricPower.coe_map_apply εU n x).symm)

include adj ψ H₁ H₂ in
omit [(pushforward.{u} φ).IsRightAdjoint] in
/-- **Pushforward along a left adjoint of sites commutes with symmetric powers**: the comparison
map `Symⁿ (φ_* M) ⟶ φ_* (Symⁿ M)` of the pushforward along `φ` is an isomorphism. -/
theorem isIso_pushforwardSymmetricPowerComparison_of_adjunction (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    IsIso ((pushforwardSymmetricPowerComparison φ n).app M) :=
  let A := pushforwardPushforwardAdj adj φ ψ H₁ H₂
  ⟨((mateEquiv A A).symm
      (TwoSquare.mk _ _ _ _ (pushforwardSymmetricPowerComparison ψ n))).natTrans.app M,
    comp_mateEquiv_symm_of_counit A (pushforwardSymmetricPowerComparison φ n)
      (pushforwardSymmetricPowerComparison ψ n)
      (pushforwardPushforwardAdj_counit_app_symmetricPower φ adj ψ H₁ H₂ n) M,
    mateEquiv_symm_comp_of_unit A (pushforwardSymmetricPowerComparison φ n)
      (pushforwardSymmetricPowerComparison ψ n)
      (pushforwardPushforwardAdj_unit_app_symmetricPower φ adj ψ H₁ H₂ n) M⟩

include φ adj H₁ H₂ in
omit [(pushforward.{u} φ).IsRightAdjoint] in
/-- **Pullback along a right adjoint of sites commutes with symmetric powers**: when `F ⊣ G`
induces an adjunction `pushforward φ ⊣ pushforward ψ`, the pullback comparison
`ψ^* (Symⁿ M) ⟶ Symⁿ (ψ^* M)` is an isomorphism. -/
theorem isIso_pullbackSymmetricPowerComparison_of_adjunction
    [(pushforward.{u} ψ).IsRightAdjoint] (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    IsIso ((pullbackSymmetricPowerComparison ψ n).app M) := by
  let A := pushforwardPushforwardAdj adj φ ψ H₁ H₂
  have : IsIso (((mateEquiv A A).symm
      (TwoSquare.mk _ _ _ _ (pushforwardSymmetricPowerComparison ψ n))).natTrans.app M) :=
    ⟨(pushforwardSymmetricPowerComparison φ n).app M, mateEquiv_symm_comp_of_unit A
        (pushforwardSymmetricPowerComparison φ n) (pushforwardSymmetricPowerComparison ψ n)
        (pushforwardPushforwardAdj_unit_app_symmetricPower φ adj ψ H₁ H₂ n) M,
      comp_mateEquiv_symm_of_counit A (pushforwardSymmetricPowerComparison φ n)
        (pushforwardSymmetricPowerComparison ψ n)
        (pushforwardPushforwardAdj_counit_app_symmetricPower φ adj ψ H₁ H₂ n) M⟩
  exact isIso_mateEquiv_symm_of_leftAdjoint A (pullbackPushforwardAdjunction ψ)
    (pushforwardSymmetricPowerComparison ψ n) M

end Adjunction

section Free
variable [F.Final]

private theorem homEquiv_pullbackObjFreeIso_hom_val_app_freeSection (I : Type u) (W : Cᵒᵖ) (i : I) :
    ((pullbackPushforwardAdjunction φ).homEquiv (free I) (free I)
        (pullbackObjFreeIso φ I).hom).val.app W ((freeSection (R := ringCatSheaf S) i).eval W) =
    (freeSection (R := ringCatSheaf R) i).eval (F.op.obj W) := by
  have h : ιFree i ≫ (pullbackPushforwardAdjunction φ).homEquiv (free I) (free I)
      (pullbackObjFreeIso φ I).hom =
    unitToPushforwardObjUnit φ ≫ (pushforward φ).map (ιFree i) := by
    rw [← Adjunction.homEquiv_naturality_left, pullback_map_ιFree_comp_pullbackObjFreeIso_hom,
      Adjunction.homEquiv_naturality_right,
      pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  have hW := congrArg (fun p ↦ p.val.app W (1 : S.obj.obj W)) h
  change ((pullbackPushforwardAdjunction φ).homEquiv (free I) (free I)
        (pullbackObjFreeIso φ I).hom).val.app W ((freeSection (R := ringCatSheaf S) i).eval W) =
    (ιFree (R := ringCatSheaf R) i).val.app (F.op.obj W) (ringHom φ W (1 : S.obj.obj W)) at hW
  exact hW.trans (congrArg (fun r : R.obj.obj (F.op.obj W) ↦
    (ιFree (R := ringCatSheaf R) i).val.app (F.op.obj W) r) (map_one (ringHom φ W)))

/-- For a free sheaf on a finite type `I`, the symmetric-power pullback comparison intertwines
`symmetricPowerFreeIso` with `pullbackObjFreeIso` on `Sym I n`. -/
@[reassoc]
theorem pullbackSymmetricPowerComparison_free (I : Type u) [Finite I] (n : ℕ) :
    (pullbackSymmetricPowerComparison φ n).app (free I) ≫
      (symmetricPower R n).map (pullbackObjFreeIso φ I).hom ≫
      (symmetricPowerFreeIso (R := R) I n).hom =
    (pullback φ).map (symmetricPowerFreeIso (R := S) I n).hom ≫
      (pullbackObjFreeIso φ (Sym I n)).hom := by
  let A := pullbackPushforwardAdjunction φ
  let gI := A.homEquiv (free I) (free I) (pullbackObjFreeIso φ I).hom
  let gP := A.homEquiv (free (Sym I n)) (free (Sym I n)) (pullbackObjFreeIso φ (Sym I n)).hom
  apply (A.homEquiv ((symmetricPower S n).obj (free I)) (free (Sym I n))).injective
  have hL : A.homEquiv ((symmetricPower S n).obj (free I)) (free (Sym I n))
      ((pullbackSymmetricPowerComparison φ n).app (free I) ≫
        (symmetricPower R n).map (pullbackObjFreeIso φ I).hom ≫
        (symmetricPowerFreeIso (R := R) I n).hom) =
      (symmetricPower S n).map gI ≫ (pushforwardSymmetricPowerComparison φ n).app (free I) ≫
        (pushforward φ).map (symmetricPowerFreeIso (R := R) I n).hom := by
    have hnat := ((pushforwardSymmetricPowerComparison φ n).naturality
      (pullbackObjFreeIso φ I).hom).symm
    rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
      unit_comp_pushforward_pullbackSymmetricPowerComparison_assoc, reassoc_of% hnat,
      ← Functor.map_comp_assoc (symmetricPower S n), ← Adjunction.homEquiv_unit]
  rw [hL, A.homEquiv_naturality_left]; apply symmetricPower_hom_ext
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
    toSymmetricPower_comp_forget_map_symmetricPower_map_assoc,
    toSymmetricPower_comp_forget_map_symmetricPowerFreeIso_hom_assoc]
  have hmid := (Category.assoc _ _ _).symm.trans ((eq_whisker
    (toSymmetricPower_comp_forget_map_pushforwardSymmetricPowerComparison φ n (free I)) _).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ (((presheafPushforward φ).map_comp
      (toSymmetricPower n (free I)) ((SheafOfModules.forget (ringCatSheaf R)).map
        (symmetricPowerFreeIso (R := R) I n).hom)).symm.trans (congrArg (presheafPushforward φ).map
      (toSymmetricPower_comp_forget_map_symmetricPowerFreeIso_hom (R := R) I n))))))
  refine (whisker_eq ((presheafSymmetricPower S n).map gI.val) hmid).trans ?_; ext W : 1; ext : 1
  refine ((freeBasis (R := S) I W).symmetricAlgebraHomogeneous n).ext fun d ↦ ?_
  let FSW := PresheafOfModulesOfCommRing.obj (free (R := ringCatSheaf S) I).val W
  let FRW := PresheafOfModulesOfCommRing.obj (free (R := ringCatSheaf R) I).val (F.op.obj W)
  let PFRW := PresheafOfModulesOfCommRing.obj
    ((pushforward φ).obj (free (R := ringCatSheaf R) I)).val W
  let gI_W : FSW ⟶ PFRW := gI.val.app' W; let g := (ModuleCat.semilinearMapAddEquiv
    (ringHom φ W) FSW FRW).symm gI_W
  have hg (i : I) : g (freeBasis (R := S) I W i) = freeBasis (R := R) I (F.op.obj W) i := by
    change gI.val.app W (freeBasis (R := S) I W i) = freeBasis (R := R) I (F.op.obj W) i
    rw [freeBasis_apply, freeBasis_apply]
    exact homEquiv_pullbackObjFreeIso_hom_val_app_freeSection φ I W i
  have hP_basis : (((presheafSymmetricPower S n).map gI.val ≫
        (presheafPushforwardSymmetricPowerComparison φ n).app (free I).val).app W)
          ((freeBasis (R := S) I W).symmetricAlgebraHomogeneous n d) =
        (freeBasis (R := R) I (F.op.obj W)).symmetricAlgebraHomogeneous n d := by
    let f_φ := (ModuleCat.semilinearMapAddEquiv (ringHom φ W) PFRW FRW).symm (𝟙 PFRW)
    have key : (SymmetricAlgebra.mapₛₗ f_φ).comp (SymmetricAlgebra.map _ gI_W.hom : _ →+* _) =
        SymmetricAlgebra.mapₛₗ g := by
      rw [← SymmetricAlgebra.mapₛₗ_eq_map gI_W.hom]
      exact SymmetricAlgebra.mapₛₗ_comp_mapₛₗ gI_W.hom f_φ g (fun _ ↦ rfl) (fun _ ↦ rfl)
    apply Subtype.ext; have h₁ := (coe_presheafPushforwardSymmetricPowerComparison_app_app_apply φ n
      (free (R := ringCatSheaf R) I).val W _).trans (congrArg _
      (ModuleCat.symmetricPower.coe_map_apply gI_W n
        ((freeBasis (R := S) I W).symmetricAlgebraHomogeneous n d)))
    have h₂ := congrArg Subtype.val (homogeneousSubmoduleMapₛₗ_symmetricAlgebraHomogeneous
      (R := S.obj.obj W) (M := FSW) (freeBasis (R := S) I W) (freeBasis (R := R) I (F.op.obj W))
      g hg n d)
    exact (h₁.trans (RingHom.congr_fun key _)).trans
      ((coe_homogeneousSubmoduleMapₛₗ_apply g n _).symm.trans h₂)
  exact ((congrArg ((presheafSymmetricPowerFreeIso (R := R) I n).hom.app (F.op.obj W))
      hP_basis).trans (presheafSymmetricPowerFreeIso_hom_app_basis I n (F.op.obj W) d)).trans
    ((congrArg (gP.val.app W) (presheafSymmetricPowerFreeIso_hom_app_basis I n W d)).trans
      (homEquiv_pullbackObjFreeIso_hom_val_app_freeSection φ (Sym I n) W d)).symm

/-- For a free sheaf on a finite type `I`, the symmetric-power pullback comparison is an
isomorphism when the underlying site functor is final. -/
instance isIso_pullbackSymmetricPowerComparison_free (I : Type u) [Finite I] (n : ℕ) :
    IsIso ((pullbackSymmetricPowerComparison φ n).app (free I)) := by
  have h := pullbackSymmetricPowerComparison_free φ I n
  have : IsIso ((pullbackSymmetricPowerComparison φ n).app (free I) ≫
      (symmetricPower R n).map (pullbackObjFreeIso φ I).hom ≫
      (symmetricPowerFreeIso (R := R) I n).hom) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((symmetricPower R n).map (pullbackObjFreeIso φ I).hom ≫
    (symmetricPowerFreeIso (R := R) I n).hom)

end Free
end SheafOfModules
end
