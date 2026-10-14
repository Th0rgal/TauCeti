/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpaceUniversalProperty

/-!
# Total space of a finite free sheaf and coordinate normalization

For a scheme `X` and `r : ℕ`, we relate the total space `V(𝒪_X^r)` of the standard finite free
bundle `freeFiniteLocallyFree X r` to Mathlib's affine space `𝔸(ULift (Fin r); X)` over `X`:
* `TauCeti.AlgebraicGeometry.freeFiniteLocallyFree` and
  `TauCeti.AlgebraicGeometry.affineSpaceOver`: the standard rank-`r` free bundle and affine space
  over `X`;
* `TauCeti.AlgebraicGeometry.freeCoordinate`,
  `TauCeti.AlgebraicGeometry.freeSectionCoordinates`,
  `TauCeti.AlgebraicGeometry.freeSectionsEquiv`, and
  `TauCeti.AlgebraicGeometry.freeSectionsEquiv_pullback`: coordinates of pulled-back sections of the
  free bundle and their compatibility with pullback along `g : T' ⟶ T`;
* `TauCeti.AlgebraicGeometry.totalSpaceFreeLinePoints` and
  `TauCeti.AlgebraicGeometry.totalSpaceFreeLinePoints_pullback`: points of the rank-one trivial line
  bundle recover global regular functions;
* `TauCeti.AlgebraicGeometry.totalSpaceFreeIso` and
  `TauCeti.AlgebraicGeometry.totalSpaceFreeIso_homOfVector`: canonical isomorphism
  `V(𝒪_X^r) ≅ 𝔸^r_X` in `AffineSchemeOver X`, normalized to agree with `AffineSpace.homOfVector`;
* `TauCeti.AlgebraicGeometry.totalSpaceFree_matrix`: matrix action of a bundle morphism between free
  bundles in standard coordinates.
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- The standard free finite locally free sheaf of rank `r` on `X`, indexed by
`ULift.{u} (Fin r)`. -/
@[expose]
noncomputable def freeFiniteLocallyFree (X : Scheme.{u}) (r : ℕ) :
    FiniteLocallyFreeSheaf X :=
  ⟨_root_.SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)), inferInstance,
    SheafOfModules.isFinitePresentation_free (ULift.{u} (Fin r))⟩

/-- Affine `r`-space `𝔸(ULift.{u} (Fin r); X)` over `X` as an object of `AffineSchemeOver X`. -/
@[expose]
noncomputable def affineSpaceOver (X : Scheme.{u}) (r : ℕ) :
    AffineSchemeOver X :=
  ⟨Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) X ↘ X),
    inferInstanceAs (IsAffineHom (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) X ↘ X))⟩

/-- Coordinate projection from the finite coproduct of copies of the structure sheaf. -/
@[expose]
noncomputable def freeCoordinate (X : Scheme.{u}) {r : ℕ} (i : ULift.{u} (Fin r)) :
    (freeFiniteLocallyFree X r).obj ⟶ SheafOfModules.unit X.ringCatSheaf :=
  Sigma.desc (C := SheafOfModules X.ringCatSheaf) fun j ↦
    if j = i then 𝟙 (SheafOfModules.unit X.ringCatSheaf)
    else (0 : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- The `i`-th standard basis inclusion `𝟙_ X.Modules ⟶ (freeFiniteLocallyFree X r).obj` in
`X.Modules`. -/
@[expose]
noncomputable def freeBasis (X : Scheme.{u}) {r : ℕ} (i : ULift.{u} (Fin r)) :
    (𝟙_ X.Modules : X.Modules) ⟶ (freeFiniteLocallyFree X r).obj :=
  SheafOfModules.ιFree (R := X.ringCatSheaf) i

/-- The `i`-th coordinate projection `(freeFiniteLocallyFree X r).obj ⟶ 𝟙_ X.Modules` in
`X.Modules`. -/
@[expose]
noncomputable def freeCoord (X : Scheme.{u}) {r : ℕ} (i : ULift.{u} (Fin r)) :
    (freeFiniteLocallyFree X r).obj ⟶ (𝟙_ X.Modules : X.Modules) :=
  freeCoordinate X i

/-- Canonical isomorphism `f^* (𝒪_X^r) ≅ 𝒪_Y^r` in `Y.Modules`. -/
@[expose]
noncomputable def pullbackFreeIso {X Y : Scheme.{u}} (f : Y ⟶ X) (r : ℕ) :
    (Scheme.Modules.pullback f).obj (freeFiniteLocallyFree X r).obj ≅
      (freeFiniteLocallyFree Y r).obj :=
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (ULift.{u} (Fin r))

@[reassoc (attr := simp)]
lemma freeBasis_freeCoord (X : Scheme.{u}) {r : ℕ} (j i : ULift.{u} (Fin r)) :
    freeBasis X j ≫ freeCoord X i =
      if j = i then 𝟙 (𝟙_ X.Modules : X.Modules) else 0 :=
  Sigma.ι_comp_desc (C := SheafOfModules X.ringCatSheaf)
    (fun k : ULift.{u} (Fin r) ↦
      if k = i then 𝟙 (SheafOfModules.unit X.ringCatSheaf)
      else (0 : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)) j

lemma sum_freeCoord_comp_freeBasis (X : Scheme.{u}) (r : ℕ) :
    (∑ k : ULift.{u} (Fin r), freeCoord X k ≫ freeBasis X k) =
      𝟙 (freeFiniteLocallyFree X r).obj := by
  refine Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) (ULift.{u} (Fin r))) _ _ fun j ↦ ?_
  change freeBasis X j ≫ (∑ k : ULift.{u} (Fin r), freeCoord X k ≫ freeBasis X k) =
    freeBasis X j ≫ 𝟙 (freeFiniteLocallyFree X r).obj
  rw [Preadditive.comp_sum, comp_id, Finset.sum_eq_single j]
  · rw [freeBasis_freeCoord_assoc]
    simp only [↓reduceIte, id_comp]
  · intro k _ hk
    rw [freeBasis_freeCoord_assoc]
    simp only [Ne.symm hk, ↓reduceIte, zero_comp]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Evaluate the pulled-back section in the standard free basis. -/
@[expose]
noncomputable def freeSectionCoordinates {X : Scheme.{u}} (r : ℕ) (T : Over X)
    (s : SheafOfModules.unit T.left.ringCatSheaf ⟶
      (Scheme.Modules.pullback T.hom).obj (freeFiniteLocallyFree X r).obj) :
    ULift.{u} (Fin r) → Γ(T.left, ⊤) :=
  letI : (SheafOfModules.pushforward T.hom.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward T.hom).IsRightAdjoint
  fun i ↦ Scheme.Modules.Hom.app
    (s ≫ (SheafOfModules.pullbackObjFreeIso T.hom.toRingCatSheafHom
      (ULift.{u} (Fin r))).hom ≫ freeCoordinate T.left i) ⊤ (1 : Γ(T.left, ⊤))

/-- Evaluate an endomorphism `u : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules` at `(1 : Γ(X, ⊤))` over `⊤` as an
element of `Γ(X, ⊤)`. -/
@[expose]
noncomputable def evalUnitEnd {X : Scheme.{u}}
    (u : (𝟙_ X.Modules : X.Modules) ⟶ (𝟙_ X.Modules : X.Modules)) : Γ(X, ⊤) :=
  Scheme.Modules.Hom.app u ⊤ (1 : Γ(X, ⊤))

@[simp]
lemma evalUnitEnd_zero (X : Scheme.{u}) :
    evalUnitEnd (0 : (𝟙_ X.Modules : X.Modules) ⟶ (𝟙_ X.Modules : X.Modules)) = 0 := by
  dsimp only [evalUnitEnd]
  rw [Scheme.Modules.Hom.zero_app]
  rfl

@[simp]
lemma evalUnitEnd_add {X : Scheme.{u}}
    (u₁ u₂ : (𝟙_ X.Modules : X.Modules) ⟶ (𝟙_ X.Modules : X.Modules)) :
    evalUnitEnd (u₁ + u₂) = evalUnitEnd u₁ + evalUnitEnd u₂ := by
  dsimp only [evalUnitEnd]
  rw [Scheme.Modules.Hom.add_app]
  rfl

/-- Two morphisms out of `𝟙_ X.Modules` into `M : X.Modules` are equal if they take the same value
on `(1 : Γ(X, ⊤))` over `⊤`. -/
lemma unit_hom_ext_of_app_top {X : Scheme.{u}} {M : X.Modules}
    {φ₁ φ₂ : (𝟙_ X.Modules : X.Modules) ⟶ M}
    (h : Scheme.Modules.Hom.app φ₁ ⊤ (1 : Γ(X, ⊤)) =
      Scheme.Modules.Hom.app φ₂ ⊤ (1 : Γ(X, ⊤))) :
    φ₁ = φ₂ := by
  apply M.unitHomEquiv.injective
  ext U
  have h₁ : (M.unitHomEquiv φ₁).val U =
      M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op ((M.unitHomEquiv φ₁).val (op ⊤)) :=
    ((M.unitHomEquiv φ₁).property (homOfLE (le_top : U.unop ≤ ⊤)).op).symm
  have h₂ : (M.unitHomEquiv φ₂).val U =
      M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op ((M.unitHomEquiv φ₂).val (op ⊤)) :=
    ((M.unitHomEquiv φ₂).property (homOfLE (le_top : U.unop ≤ ⊤)).op).symm
  exact h₁.trans ((congrArg (M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op) h).trans h₂.symm)

/-- The endomorphism of `𝟙_ X.Modules` given by multiplication by a global section `c : Γ(X, ⊤)`. -/
@[expose]
noncomputable def unitEnd (X : Scheme.{u}) (c : Γ(X, ⊤)) :
    (𝟙_ X.Modules : X.Modules) ⟶ (𝟙_ X.Modules : X.Modules) :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op c)
      (fun U V f ↦ by
        change (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ X.presheaf.map f) c =
          X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op c
        rw [← X.presheaf.map_comp, Subsingleton.elim
          ((homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f)
          (homOfLE (le_top : V.unop ≤ ⊤)).op]))

@[simp]
lemma evalUnitEnd_unitEnd (X : Scheme.{u}) (c : Γ(X, ⊤)) :
    evalUnitEnd (unitEnd X c) = c := by
  have h := congrArg (fun s ↦ s.val (op (⊤ : X.Opens)))
    ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.apply_symm_apply
      (PresheafOfModules.sectionsMk
        (fun U ↦ X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op c)
        (fun U V f ↦ by
          change (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ X.presheaf.map f) c =
            X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op c
          rw [← X.presheaf.map_comp, Subsingleton.elim
            ((homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f)
            (homOfLE (le_top : V.unop ≤ ⊤)).op])))
  refine h.trans ?_
  change X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op c = c
  have hid : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : X.Opens)) :=
    Subsingleton.elim _ _
  rw [hid, X.presheaf.map_id]
  rfl

lemma unitEnd_evalUnitEnd {X : Scheme.{u}}
    (u : (𝟙_ X.Modules : X.Modules) ⟶ (𝟙_ X.Modules : X.Modules)) :
    unitEnd X (evalUnitEnd u) = u :=
  unit_hom_ext_of_app_top (evalUnitEnd_unitEnd X _)

lemma evalUnitEnd_comp {X : Scheme.{u}}
    (u₁ u₂ : (𝟙_ X.Modules : X.Modules) ⟶ (𝟙_ X.Modules : X.Modules)) :
    evalUnitEnd (u₁ ≫ u₂) = evalUnitEnd u₂ * evalUnitEnd u₁ := by
  let c₁ : Γ(X, ⊤) := evalUnitEnd u₁
  let c₂ : Γ(X, ⊤) := evalUnitEnd u₂
  have hc₁ : (c₁ : Γ(𝟙_ X.Modules, ⊤)) = c₁ • (1 : Γ(X, ⊤)) := by
    change c₁ = c₁ * (1 : Γ(X, ⊤))
    exact (mul_one c₁).symm
  have hsmul : (Scheme.Modules.Hom.app u₂ ⊤ (c₁ • (1 : Γ(X, ⊤))) : Γ(X, ⊤)) = c₁ * c₂ :=
    Scheme.Modules.Hom.app_smul u₂ c₁ (1 : Γ(X, ⊤))
  exact (congrArg (Scheme.Modules.Hom.app u₂ ⊤) hc₁).trans (hsmul.trans (mul_comm c₁ c₂))

/-- Construct a pulled-back section of the standard rank-`r` free bundle from an `r`-tuple of
global functions on `T.left`. -/
@[expose]
noncomputable def freeSectionOfCoord {X : Scheme.{u}} (r : ℕ) (T : Over X)
    (v : ULift.{u} (Fin r) → Γ(T.left, ⊤)) :
    (𝟙_ T.left.Modules : T.left.Modules) ⟶
      (Scheme.Modules.pullback T.hom).obj (freeFiniteLocallyFree X r).obj :=
  (∑ j : ULift.{u} (Fin r), unitEnd T.left (v j) ≫ freeBasis T.left j) ≫
    (pullbackFreeIso T.hom r).inv

lemma freeSectionOfCoord_coord {X : Scheme.{u}} (r : ℕ) (T : Over X)
    (s : (𝟙_ T.left.Modules : T.left.Modules) ⟶
      (Scheme.Modules.pullback T.hom).obj (freeFiniteLocallyFree X r).obj) :
    freeSectionOfCoord r T
      (fun j ↦ evalUnitEnd (s ≫ (pullbackFreeIso T.hom r).hom ≫ freeCoord T.left j)) = s := by
  dsimp only [freeSectionOfCoord]
  rw [Iso.comp_inv_eq]
  have hj : ∀ j : ULift.{u} (Fin r),
      unitEnd T.left (evalUnitEnd (s ≫ (pullbackFreeIso T.hom r).hom ≫ freeCoord T.left j)) =
        s ≫ (pullbackFreeIso T.hom r).hom ≫ freeCoord T.left j :=
    fun j ↦ unitEnd_evalUnitEnd _
  simp_rw [hj, Category.assoc, ← Preadditive.comp_sum, sum_freeCoord_comp_freeBasis,
    Category.comp_id]

lemma freeSectionCoord_ofCoord {X : Scheme.{u}} (r : ℕ) (T : Over X)
    (v : ULift.{u} (Fin r) → Γ(T.left, ⊤)) :
    (fun i ↦ evalUnitEnd
      (freeSectionOfCoord r T v ≫ (pullbackFreeIso T.hom r).hom ≫ freeCoord T.left i)) = v := by
  funext i
  dsimp only [freeSectionOfCoord]
  rw [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp, Finset.sum_eq_single i]
  · rw [Category.assoc, freeBasis_freeCoord]
    simp only [↓reduceIte, Category.comp_id, evalUnitEnd_unitEnd]
  · intro j _ hj
    rw [Category.assoc, freeBasis_freeCoord]
    simp only [hj, ↓reduceIte, comp_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Equivalence between pulled-back sections of the standard rank-`r` free bundle on `X` along
`T.hom : T.left ⟶ X` and `r`-tuples of global functions on `T.left`. -/
@[expose]
noncomputable def freeSectionsEquiv {X : Scheme.{u}} (r : ℕ) (T : Over X) :
    (SheafOfModules.unit T.left.ringCatSheaf ⟶
      (Scheme.Modules.pullback T.hom).obj (freeFiniteLocallyFree X r).obj) ≃
      (ULift.{u} (Fin r) → Γ(T.left, ⊤)) where
  toFun := freeSectionCoordinates r T
  invFun := freeSectionOfCoord r T
  left_inv s := freeSectionOfCoord_coord r T s
  right_inv v := freeSectionCoord_ofCoord r T v

/-- Pulling back `freeCoord X i` along `f : Y ⟶ X` agrees with `freeCoord Y i` after the canonical
free-module pullback isomorphism `pullbackFreeIso`. -/
@[reassoc]
lemma pullbackFreeIso_hom_comp_freeCoord {X Y : Scheme.{u}} (f : Y ⟶ X)
    {r : ℕ} (i : ULift.{u} (Fin r)) :
    (pullbackFreeIso f r).hom ≫ freeCoord Y i =
      (Scheme.Modules.pullback f).map (freeCoord X i) ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  refine Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _
      (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) (ULift.{u} (Fin r)))) _ _
    fun j ↦ ?_
  have hj : (Scheme.Modules.pullback f).map (freeBasis X j) ≫ (pullbackFreeIso f r).hom =
      (Scheme.Modules.pullbackObjUnitIso f).hom ≫ freeBasis Y j :=
    (SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
      f.toRingCatSheafHom j).trans
      (congrArg (· ≫ freeBasis Y j) (Scheme.Modules.pullbackObjUnitIso_hom f).symm)
  change (Scheme.Modules.pullback f).map (freeBasis X j) ≫
      (pullbackFreeIso f r).hom ≫ freeCoord Y i =
    (Scheme.Modules.pullback f).map (freeBasis X j) ≫
      (Scheme.Modules.pullback f).map (freeCoord X i) ≫
      (Scheme.Modules.pullbackObjUnitIso f).hom
  rw [reassoc_of% hj, ← Functor.map_comp_assoc, freeBasis_freeCoord, freeBasis_freeCoord]
  split_ifs with hji
  · rw [comp_id, CategoryTheory.Functor.map_id, id_comp]
  · rw [comp_zero, Functor.map_zero, zero_comp]

/-- Pulling back a unit endomorphism `u : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules` along `f : Y ⟶ X` acts on
`(1 : Γ(Y, ⊤))` by applying `f.appTop` to `evalUnitEnd u`. -/
lemma evalUnitEnd_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (u : (𝟙_ X.Modules : X.Modules) ⟶ (𝟙_ X.Modules : X.Modules)) :
    evalUnitEnd
      ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map u ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom) =
      f.appTop (evalUnitEnd u) := by
  let v : (𝟙_ Y.Modules : Y.Modules) ⟶ (𝟙_ Y.Modules : Y.Modules) :=
    (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map u ≫
      (Scheme.Modules.pullbackObjUnitIso f).hom
  have hv : (Scheme.Modules.pullbackObjUnitIso f).hom ≫ v =
      (Scheme.Modules.pullback f).map u ≫ (Scheme.Modules.pullbackObjUnitIso f).hom :=
    Iso.hom_inv_id_assoc (Scheme.Modules.pullbackObjUnitIso f)
      ((Scheme.Modules.pullback f).map u ≫ (Scheme.Modules.pullbackObjUnitIso f).hom)
  have hadj := congrArg
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      (𝟙_ X.Modules) (𝟙_ Y.Modules)) hv
  have hL : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.pullbackObjUnitIso f).hom ≫ v) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map v :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
      (Scheme.Modules.pullbackObjUnitIso f).hom v).trans
      (congrArg (· ≫ (Scheme.Modules.pushforward f).map v)
        (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f))
  have hR : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.pullback f).map u ≫ (Scheme.Modules.pullbackObjUnitIso f).hom) =
      u ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    (Adjunction.homEquiv_naturality_left (Scheme.Modules.pullbackPushforwardAdjunction f)
      u (Scheme.Modules.pullbackObjUnitIso f).hom).trans
      (congrArg (u ≫ ·)
        (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f))
  have heq : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward f).map v =
      u ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    hL.symm.trans (hadj.trans hR)
  have happ := congrArg (fun φ : (𝟙_ X.Modules : X.Modules) ⟶
      (Scheme.Modules.pushforward f).obj (𝟙_ Y.Modules) ↦
    Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤))) heq
  have happL : Scheme.Modules.Hom.app
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map v) ⊤ (1 : Γ(X, ⊤)) =
      evalUnitEnd v := by
    change Scheme.Modules.Hom.app v (f ⁻¹ᵁ ⊤) (f.appTop (1 : Γ(X, ⊤))) =
      Scheme.Modules.Hom.app v ⊤ (1 : Γ(Y, ⊤))
    rw [map_one]
    rfl
  exact happL.symm.trans happ

theorem freeSectionsEquiv_pullback {X : Scheme.{u}} (r : ℕ) {T T' : Over X}
    (g : T' ⟶ T) (s : SheafOfModules.unit T.left.ringCatSheaf ⟶
      (Scheme.Modules.pullback T.hom).obj (freeFiniteLocallyFree X r).obj)
    (i : ULift.{u} (Fin r)) :
    freeSectionsEquiv r T' (pullbackSectionMap (freeFiniteLocallyFree X r).obj g s) i =
      g.left.appTop (freeSectionsEquiv r T s i) := by
  let s₀ : (𝟙_ T.left.Modules : T.left.Modules) ⟶
      (Scheme.Modules.pullback T.hom).obj (freeFiniteLocallyFree X r).obj := s
  change evalUnitEnd
      ((Scheme.Modules.pullbackObjUnitIso g.left).inv ≫
        (Scheme.Modules.pullback g.left).map s₀ ≫
        (Scheme.Modules.pullbackComp g.left T.hom).hom.app (freeFiniteLocallyFree X r).obj ≫
        (Scheme.Modules.pullbackCongr g.w).hom.app (freeFiniteLocallyFree X r).obj ≫
        (pullbackFreeIso T'.hom r).hom ≫ freeCoord T'.left i) =
    g.left.appTop (evalUnitEnd (s₀ ≫ (pullbackFreeIso T.hom r).hom ≫ freeCoord T.left i))
  rw [pullbackFreeIso_hom_comp_freeCoord T'.hom i]
  have hcongr : (Scheme.Modules.pullbackCongr g.w).hom.app (freeFiniteLocallyFree X r).obj ≫
      (Scheme.Modules.pullback T'.hom).map (freeCoord X i) ≫
      (Scheme.Modules.pullbackObjUnitIso T'.hom).hom =
      (Scheme.Modules.pullback (g.left ≫ T.hom)).map (freeCoord X i) ≫
      (Scheme.Modules.pullbackObjUnitIso (g.left ≫ T.hom)).hom := by
    rw [← (Scheme.Modules.pullbackCongr g.w).hom.naturality_assoc (freeCoord X i),
      Scheme.Modules.pullbackObjUnitIso_congr g.w]
  have hcomp : (Scheme.Modules.pullbackComp g.left T.hom).hom.app (freeFiniteLocallyFree X r).obj ≫
      (Scheme.Modules.pullback (g.left ≫ T.hom)).map (freeCoord X i) ≫
      (Scheme.Modules.pullbackObjUnitIso (g.left ≫ T.hom)).hom =
      (Scheme.Modules.pullback g.left).map ((Scheme.Modules.pullback T.hom).map (freeCoord X i)) ≫
      (Scheme.Modules.pullback g.left).map (Scheme.Modules.pullbackObjUnitIso T.hom).hom ≫
      (Scheme.Modules.pullbackObjUnitIso g.left).hom := by
    rw [← (Scheme.Modules.pullbackComp g.left T.hom).hom.naturality_assoc (freeCoord X i),
      ← Scheme.Modules.pullbackObjUnitIso_comp g.left T.hom, Iso.hom_inv_id_app_assoc]
    rfl
  rw [hcongr, hcomp, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, ← pullbackFreeIso_hom_comp_freeCoord T.hom i]
  exact evalUnitEnd_pullback g.left
    (s₀ ≫ (pullbackFreeIso T.hom r).hom ≫ freeCoord T.left i)

/-- Rank one recovers regular functions, with restriction tested below. -/
@[expose]
noncomputable def totalSpaceFreeLinePoints {X : Scheme.{u}} (T : Over X) :
    (T ⟶ (affineSchemeOverForget X).obj
      ((totalSpaceScheme X).obj (freeFiniteLocallyFree X 1))) ≃ Γ(T.left, ⊤) :=
  (totalSpaceHomEquiv (freeFiniteLocallyFree X 1) T).trans
    ((freeSectionsEquiv 1 T).trans (Equiv.funUnique (ULift.{u} (Fin 1)) _))

theorem totalSpaceFreeLinePoints_pullback {X : Scheme.{u}} {T T' : Over X}
    (g : T' ⟶ T) (h : T ⟶ (affineSchemeOverForget X).obj
      ((totalSpaceScheme X).obj (freeFiniteLocallyFree X 1))) :
    totalSpaceFreeLinePoints T' (g ≫ h) = g.left.appTop (totalSpaceFreeLinePoints T h) :=
  (congrArg (fun s ↦ freeSectionsEquiv 1 T' s default)
    (totalSpaceHomEquiv_naturality_test (freeFiniteLocallyFree X 1) g h)).trans
    (freeSectionsEquiv_pullback 1 g (totalSpaceHomEquiv (freeFiniteLocallyFree X 1) T h) default)

/-- Equivalence between `Over X`-morphisms `T ⟶ affineSpaceOver X r` and `r`-tuples of global
functions on `T.left`. -/
@[expose]
noncomputable def affineSpaceOverHomEquiv (X : Scheme.{u}) (r : ℕ) (T : Over X) :
    (T ⟶ (affineSchemeOverForget X).obj (affineSpaceOver X r)) ≃
      (ULift.{u} (Fin r) → Γ(T.left, ⊤)) where
  toFun f i := f.left.appTop (AffineSpace.coord X i)
  invFun v := Over.homMk (AffineSpace.homOfVector T.hom v) (AffineSpace.homOfVector_over T.hom v)
  left_inv f := by
    ext1
    exact AffineSpace.hom_ext
      ((AffineSpace.homOfVector_over T.hom _).trans (Over.w f).symm)
      (fun i ↦ AffineSpace.homOfVector_appTop_coord T.hom _ i)
  right_inv v := funext fun i ↦ AffineSpace.homOfVector_appTop_coord T.hom v i

/-- Pointwise equivalence between `Over X`-points of `V(𝒪_X^r)` and `Over X`-points of `𝔸^r_X`. -/
@[expose]
noncomputable def totalSpaceFreeOverHomEquiv (X : Scheme.{u}) (r : ℕ) (T : Over X) :
    (T ⟶ (affineSchemeOverForget X).obj
      ((totalSpaceScheme X).obj (freeFiniteLocallyFree X r))) ≃
    (T ⟶ (affineSchemeOverForget X).obj (affineSpaceOver X r)) :=
  (totalSpaceHomEquiv (freeFiniteLocallyFree X r) T).trans
    ((freeSectionsEquiv r T).trans (affineSpaceOverHomEquiv X r T).symm)

lemma totalSpaceFreeOverHomEquiv_naturality (X : Scheme.{u}) (r : ℕ) {T T' : Over X}
    (g : T' ⟶ T)
    (h : T ⟶ (affineSchemeOverForget X).obj
      ((totalSpaceScheme X).obj (freeFiniteLocallyFree X r))) :
    totalSpaceFreeOverHomEquiv X r T' (g ≫ h) =
      g ≫ totalSpaceFreeOverHomEquiv X r T h := by
  apply (affineSpaceOverHomEquiv X r T').injective
  funext i
  have hL : affineSpaceOverHomEquiv X r T' (totalSpaceFreeOverHomEquiv X r T' (g ≫ h)) i =
      freeSectionsEquiv r T' (totalSpaceHomEquiv (freeFiniteLocallyFree X r) T' (g ≫ h)) i :=
    congrFun ((affineSpaceOverHomEquiv X r T').apply_symm_apply _) i
  let φ : T.left ⟶ AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) X :=
    (totalSpaceFreeOverHomEquiv X r T h).left
  have hR : affineSpaceOverHomEquiv X r T' (g ≫ totalSpaceFreeOverHomEquiv X r T h) i =
      g.left.appTop
        (affineSpaceOverHomEquiv X r T (totalSpaceFreeOverHomEquiv X r T h) i) :=
    congrArg (fun ψ : Γ(AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) X, ⊤) ⟶
        Γ(T'.left, ⊤) ↦ ψ (AffineSpace.coord X i)) (Scheme.Hom.comp_appTop g.left φ)
  have hR' : affineSpaceOverHomEquiv X r T (totalSpaceFreeOverHomEquiv X r T h) i =
      freeSectionsEquiv r T (totalSpaceHomEquiv (freeFiniteLocallyFree X r) T h) i :=
    congrFun ((affineSpaceOverHomEquiv X r T).apply_symm_apply _) i
  exact hL.trans ((((congrArg (fun s ↦ freeSectionsEquiv r T' s i)
    (totalSpaceHomEquiv_naturality_test (freeFiniteLocallyFree X r) g h)).trans
    (freeSectionsEquiv_pullback r g
      (totalSpaceHomEquiv (freeFiniteLocallyFree X r) T h) i)).trans
    (congrArg g.left.appTop hR'.symm)).trans hR.symm)

/-- Natural isomorphism of `(Over X)ᵒᵖ`-presheaves of points between `V(𝒪_X^r)` and `𝔸^r_X`. -/
@[expose]
noncomputable def totalSpaceFreePointsIso (X : Scheme.{u}) (r : ℕ) :
    yoneda.obj ((affineSchemeOverForget X).obj
      ((totalSpaceScheme X).obj (freeFiniteLocallyFree X r))) ≅
    yoneda.obj ((affineSchemeOverForget X).obj (affineSpaceOver X r)) :=
  NatIso.ofComponents
    (fun T ↦
      { hom := TypeCat.ofHom (totalSpaceFreeOverHomEquiv X r T.unop)
        inv := TypeCat.ofHom (totalSpaceFreeOverHomEquiv X r T.unop).symm
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro h
          exact (totalSpaceFreeOverHomEquiv X r T.unop).symm_apply_apply h
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro h
          exact (totalSpaceFreeOverHomEquiv X r T.unop).apply_symm_apply h })
    (fun g ↦ by
      apply ConcreteCategory.hom_ext
      intro h
      exact totalSpaceFreeOverHomEquiv_naturality X r g.unop h)

/-- The total space of the standard rank-`r` free bundle on `X` is canonically isomorphic in
`AffineSchemeOver X` to affine `r`-space `affineSpaceOver X r`. -/
@[expose]
noncomputable def totalSpaceFreeIso (X : Scheme.{u}) (r : ℕ) :
    (totalSpaceScheme X).obj (freeFiniteLocallyFree X r) ≅ affineSpaceOver X r :=
  ((fullyFaithfulAffineSchemeOverForget X).comp Yoneda.fullyFaithful).preimageIso
    (totalSpaceFreePointsIso X r)

/-- The free-bundle normalization agrees with Mathlib's coordinate-valued affine-space map. -/
theorem totalSpaceFreeIso_homOfVector {X : Scheme.{u}} (r : ℕ) (T : Over X)
    (v : ULift.{u} (Fin r) → Γ(T.left, ⊤)) :
    (((totalSpaceHomEquiv (freeFiniteLocallyFree X r) T).symm
      ((freeSectionsEquiv r T).symm v)) ≫
      (affineSchemeOverForget X).map (totalSpaceFreeIso X r).hom).left =
        AffineSpace.homOfVector T.hom v := by
  let h : T ⟶ (affineSchemeOverForget X).obj
      ((totalSpaceScheme X).obj (freeFiniteLocallyFree X r)) :=
    (totalSpaceHomEquiv (freeFiniteLocallyFree X r) T).symm ((freeSectionsEquiv r T).symm v)
  have hmap : h ≫ (affineSchemeOverForget X).map (totalSpaceFreeIso X r).hom =
      totalSpaceFreeOverHomEquiv X r T h :=
    congrArg (fun α ↦ α.app (op T) h)
      (((fullyFaithfulAffineSchemeOverForget X).comp Yoneda.fullyFaithful).map_preimage
        (totalSpaceFreePointsIso X r).hom)
  have hval : totalSpaceFreeOverHomEquiv X r T h =
      (affineSpaceOverHomEquiv X r T).symm v := by
    dsimp only [totalSpaceFreeOverHomEquiv, Equiv.trans_apply, h]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact congrArg CommaMorphism.left (hmap.trans hval)

/-- A matrix is measured on the actual standard generators, not on a separately chosen functor. -/
theorem totalSpaceFree_matrix {X : Scheme.{u}} {r s : ℕ}
    (a : freeFiniteLocallyFree X r ⟶ freeFiniteLocallyFree X s)
    (A : Matrix (ULift.{u} (Fin s)) (ULift.{u} (Fin r)) Γ(X, ⊤))
    (hA : ∀ i j,
      Scheme.Modules.Hom.app (X := X)
        (SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ a.hom ≫ freeCoordinate X i) ⊤
        (1 : Γ(X, ⊤)) = A i j)
    (T : Over X) (h : T ⟶ (affineSchemeOverForget X).obj
      ((totalSpaceScheme X).obj (freeFiniteLocallyFree X r))) (i : ULift.{u} (Fin s)) :
    freeSectionsEquiv s T (totalSpaceHomEquiv (freeFiniteLocallyFree X s) T
      (h ≫ (affineSchemeOverForget X).map ((totalSpaceScheme X).map a))) i =
        ∑ j, T.hom.appTop (A i j) *
          freeSectionsEquiv r T (totalSpaceHomEquiv (freeFiniteLocallyFree X r) T h) j := by
  let σ : (𝟙_ T.left.Modules : T.left.Modules) ⟶
      (Scheme.Modules.pullback T.hom).obj (freeFiniteLocallyFree X r).obj :=
    totalSpaceHomEquiv (freeFiniteLocallyFree X r) T h
  let row : ULift.{u} (Fin r) → Γ(X, ⊤) := A i
  have hnat : freeSectionsEquiv s T (totalSpaceHomEquiv (freeFiniteLocallyFree X s) T
      (h ≫ (affineSchemeOverForget X).map ((totalSpaceScheme X).map a))) i =
      evalUnitEnd ((σ ≫ (Scheme.Modules.pullback T.hom).map a.hom) ≫
        (pullbackFreeIso T.hom s).hom ≫ freeCoord T.left i) :=
    congrArg (fun τ ↦ freeSectionsEquiv s T τ i)
      (totalSpaceHomEquiv_naturality_bundle a T h)
  refine hnat.trans ?_
  change evalUnitEnd ((σ ≫ (Scheme.Modules.pullback T.hom).map a.hom) ≫
      (pullbackFreeIso T.hom s).hom ≫ freeCoord T.left i) =
    ∑ j, T.hom.appTop (row j) *
      evalUnitEnd (σ ≫ (pullbackFreeIso T.hom r).hom ≫ freeCoord T.left j)
  have hA' : ∀ j : ULift.{u} (Fin r),
      evalUnitEnd (freeBasis X j ≫ a.hom ≫ freeCoord X i) = row j :=
    fun j ↦ hA i j
  have ha : a.hom ≫ freeCoord X i =
      ∑ j : ULift.{u} (Fin r), freeCoord X j ≫ unitEnd X (row j) := by
    have hsum := congrArg (· ≫ a.hom ≫ freeCoord X i) (sum_freeCoord_comp_freeBasis X r).symm
    rw [id_comp, Preadditive.sum_comp] at hsum
    refine hsum.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [Category.assoc]
    congr 1
    rw [← hA' j]
    exact (unitEnd_evalUnitEnd _).symm
  rw [Category.assoc, pullbackFreeIso_hom_comp_freeCoord T.hom i,
    ← Functor.map_comp_assoc, ha, Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  have hsum_app :
      evalUnitEnd
        (∑ j : ULift.{u} (Fin r),
          σ ≫ (Scheme.Modules.pullback T.hom).map
            (freeCoord X j ≫ unitEnd X (row j)) ≫
            (Scheme.Modules.pullbackObjUnitIso T.hom).hom) =
      ∑ j : ULift.{u} (Fin r),
        evalUnitEnd
          (σ ≫ (Scheme.Modules.pullback T.hom).map
            (freeCoord X j ≫ unitEnd X (row j)) ≫
            (Scheme.Modules.pullbackObjUnitIso T.hom).hom) := by
    induction (Finset.univ : Finset (ULift.{u} (Fin r))) using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, evalUnitEnd_zero]
    | @insert k S hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, evalUnitEnd_add, ih]
  rw [hsum_app]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  let u₁ : (𝟙_ T.left.Modules : T.left.Modules) ⟶ (𝟙_ T.left.Modules : T.left.Modules) :=
    σ ≫ (pullbackFreeIso T.hom r).hom ≫ freeCoord T.left j
  let u₂ : (𝟙_ T.left.Modules : T.left.Modules) ⟶ (𝟙_ T.left.Modules : T.left.Modules) :=
    (Scheme.Modules.pullbackObjUnitIso T.hom).inv ≫
      (Scheme.Modules.pullback T.hom).map (unitEnd X (row j)) ≫
      (Scheme.Modules.pullbackObjUnitIso T.hom).hom
  have hdecomp : σ ≫ (Scheme.Modules.pullback T.hom).map
      (freeCoord X j ≫ unitEnd X (row j)) ≫
      (Scheme.Modules.pullbackObjUnitIso T.hom).hom = u₁ ≫ u₂ := by
    dsimp only [u₁, u₂]
    rw [Category.assoc, Category.assoc, pullbackFreeIso_hom_comp_freeCoord_assoc T.hom j,
      Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc]
  rw [hdecomp, evalUnitEnd_comp]
  have hu₂ : evalUnitEnd u₂ = T.hom.appTop (row j) := by
    dsimp only [u₂]
    rw [evalUnitEnd_pullback, evalUnitEnd_unitEnd]
  rw [hu₂]

end

end TauCeti.AlgebraicGeometry
