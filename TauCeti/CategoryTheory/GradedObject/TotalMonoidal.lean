/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# Symmetric monoidal structure on totalization of graded objects and componentwise graded monoids

For a symmetric monoidal closed category `C` with countable coproducts and an initial object:
* `GradedObject ℕ C` inherits a symmetric monoidal structure from `C`;
* the totalization functor `GradedObject.total ℕ C : GradedObject ℕ C ⥤ C`, sending `A` to
  `∐ (n : ℕ), A n`, is a strong braided monoidal functor, so it induces
  `(GradedObject.total ℕ C).mapCommMon : CommMon (GradedObject ℕ C) ⥤ CommMon C`;
* `TauCeti.GradedCommMonData C` packages componentwise graded commutative monoid data
  `(X n, one₀ : 𝟙_ C ⟶ X 0, mul i j k : X i ⊗ X j ⟶ X k)` in `C`, pushes forward along any lax
  braided monoidal functor `F : C ⥤ D` (`GradedCommMonData.mapObj`, `GradedCommMonData.mapHom`), and
  assembles into a commutative monoid object in `GradedObject ℕ C`
  (`GradedCommMonData.toCommMonObj`, `GradedCommMonData.toCommMonHom`).
-/

public section

open CategoryTheory Category Limits MonoidalCategory

namespace TauCeti

universe v u v' u'

noncomputable section

section ClosedCoproducts

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

instance (X : C) : PreservesColimitsOfSize.{0, 0} ((curriedTensor C).obj X) :=
  (ihom.adjunction X).leftAdjoint_preservesColimits

variable [HasCoproducts.{0} C]

instance : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts.{0} C

/-- Descend a family of morphisms `A ⊗ Y j ⟶ Z` to a morphism `A ⊗ (∐ Y) ⟶ Z`. -/
def leftTensorSigmaDesc {κ : Type} {A : C} {Y : κ → C} {Z : C}
    (f : ∀ j : κ, A ⊗ Y j ⟶ Z) : A ⊗ (∐ Y) ⟶ Z :=
  ((ihom.adjunction A).homEquiv (∐ Y) Z).symm
    (Sigma.desc fun j ↦ (ihom.adjunction A).homEquiv (Y j) Z (f j))

@[reassoc (attr := simp)]
lemma whiskerLeft_ι_leftTensorSigmaDesc {κ : Type} {A : C} {Y : κ → C} {Z : C}
    (f : ∀ j : κ, A ⊗ Y j ⟶ Z) (j : κ) :
    (A ◁ Sigma.ι Y j) ≫ leftTensorSigmaDesc f = f j := by
  apply ((ihom.adjunction A).homEquiv (Y j) Z).injective
  change (ihom.adjunction A).homEquiv (Y j) Z
    (((tensorLeft A).map (Sigma.ι Y j)) ≫ leftTensorSigmaDesc f) = _
  rw [Adjunction.homEquiv_naturality_left, leftTensorSigmaDesc, Equiv.apply_symm_apply,
    Sigma.ι_comp_desc]

lemma leftTensorSigma_hom_ext {κ : Type} {A : C} {Y : κ → C} {Z : C}
    {g₁ g₂ : A ⊗ (∐ Y) ⟶ Z}
    (h : ∀ j : κ, (A ◁ Sigma.ι Y j) ≫ g₁ = (A ◁ Sigma.ι Y j) ≫ g₂) : g₁ = g₂ := by
  apply ((ihom.adjunction A).homEquiv (∐ Y) Z).injective
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  have hj : (ihom.adjunction A).homEquiv (Y j) Z (((tensorLeft A).map (Sigma.ι Y j)) ≫ g₁) =
      (ihom.adjunction A).homEquiv (Y j) Z (((tensorLeft A).map (Sigma.ι Y j)) ≫ g₂) :=
    congrArg ((ihom.adjunction A).homEquiv (Y j) Z) (h j)
  simpa only [Adjunction.homEquiv_naturality_left] using hj

variable [SymmetricCategory C]

/-- Right-tensoring with `Y` is left adjoint to `ihom Y` in a symmetric monoidal closed category. -/
def tensorRightAdjunction (Y : C) : tensorRight Y ⊣ ihom Y :=
  (ihom.adjunction Y).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight Y)

instance (Y : C) : PreservesColimitsOfSize.{0, 0} ((curriedTensor C).flip.obj Y) :=
  (tensorRightAdjunction Y).leftAdjoint_preservesColimits

/-- Descend a family of morphisms `X i ⊗ B ⟶ Z` to a morphism `(∐ X) ⊗ B ⟶ Z`. -/
def rightTensorSigmaDesc {ι : Type} {X : ι → C} {B : C} {Z : C}
    (f : ∀ i : ι, X i ⊗ B ⟶ Z) : (∐ X) ⊗ B ⟶ Z :=
  ((tensorRightAdjunction B).homEquiv (∐ X) Z).symm
    (Sigma.desc fun i ↦ (tensorRightAdjunction B).homEquiv (X i) Z (f i))

@[reassoc (attr := simp)]
lemma whiskerRight_ι_rightTensorSigmaDesc {ι : Type} {X : ι → C} {B : C} {Z : C}
    (f : ∀ i : ι, X i ⊗ B ⟶ Z) (i : ι) :
    (Sigma.ι X i ▷ B) ≫ rightTensorSigmaDesc f = f i := by
  apply ((tensorRightAdjunction B).homEquiv (X i) Z).injective
  change (tensorRightAdjunction B).homEquiv (X i) Z
    (((tensorRight B).map (Sigma.ι X i)) ≫ rightTensorSigmaDesc f) = _
  rw [Adjunction.homEquiv_naturality_left, rightTensorSigmaDesc, Equiv.apply_symm_apply,
    Sigma.ι_comp_desc]

lemma rightTensorSigma_hom_ext {ι : Type} {X : ι → C} {B : C} {Z : C}
    {g₁ g₂ : (∐ X) ⊗ B ⟶ Z}
    (h : ∀ i : ι, (Sigma.ι X i ▷ B) ≫ g₁ = (Sigma.ι X i ▷ B) ≫ g₂) : g₁ = g₂ := by
  apply ((tensorRightAdjunction B).homEquiv (∐ X) Z).injective
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  have hi : (tensorRightAdjunction B).homEquiv (X i) Z (((tensorRight B).map (Sigma.ι X i)) ≫ g₁) =
      (tensorRightAdjunction B).homEquiv (X i) Z (((tensorRight B).map (Sigma.ι X i)) ≫ g₂) :=
    congrArg ((tensorRightAdjunction B).homEquiv (X i) Z) (h i)
  simpa only [Adjunction.homEquiv_naturality_left] using hi

/-- Descend a doubly indexed family of morphisms `X i ⊗ Y j ⟶ Z` to `(∐ X) ⊗ (∐ Y) ⟶ Z`. -/
def tensorSigmaDesc {ι κ : Type} {X : ι → C} {Y : κ → C} {Z : C}
    (f : ∀ (i : ι) (j : κ), X i ⊗ Y j ⟶ Z) : (∐ X) ⊗ (∐ Y) ⟶ Z :=
  rightTensorSigmaDesc fun i ↦ leftTensorSigmaDesc fun j ↦ f i j

@[reassoc (attr := simp)]
lemma ι_tensorSigmaDesc {ι κ : Type} {X : ι → C} {Y : κ → C} {Z : C}
    (f : ∀ (i : ι) (j : κ), X i ⊗ Y j ⟶ Z) (i : ι) (j : κ) :
    (Sigma.ι X i ⊗ₘ Sigma.ι Y j) ≫ tensorSigmaDesc f = f i j := by
  rw [tensorHom_def', assoc, tensorSigmaDesc, whiskerRight_ι_rightTensorSigmaDesc,
    whiskerLeft_ι_leftTensorSigmaDesc]

@[ext]
lemma tensorSigma_hom_ext {ι κ : Type} {X : ι → C} {Y : κ → C} {Z : C}
    {g₁ g₂ : (∐ X) ⊗ (∐ Y) ⟶ Z}
    (h : ∀ (i : ι) (j : κ),
      (Sigma.ι X i ⊗ₘ Sigma.ι Y j) ≫ g₁ = (Sigma.ι X i ⊗ₘ Sigma.ι Y j) ≫ g₂) :
    g₁ = g₂ := by
  refine rightTensorSigma_hom_ext fun i ↦ leftTensorSigma_hom_ext fun j ↦ ?_
  simpa only [tensorHom_def', assoc] using h i j

lemma tensorSigma₃_hom_ext {ι κ μ : Type} {X : ι → C} {Y : κ → C} {W : μ → C} {Z : C}
    {g₁ g₂ : ((∐ X) ⊗ (∐ Y)) ⊗ (∐ W) ⟶ Z}
    (h : ∀ (i : ι) (j : κ) (k : μ),
      ((Sigma.ι X i ⊗ₘ Sigma.ι Y j) ⊗ₘ Sigma.ι W k) ≫ g₁ =
        ((Sigma.ι X i ⊗ₘ Sigma.ι Y j) ⊗ₘ Sigma.ι W k) ≫ g₂) :
    g₁ = g₂ := by
  refine leftTensorSigma_hom_ext fun k ↦ ?_
  apply ((tensorRightAdjunction (W k)).homEquiv ((∐ X) ⊗ (∐ Y)) Z).injective
  refine tensorSigma_hom_ext fun i j ↦ ?_
  have hijk : (tensorRightAdjunction (W k)).homEquiv (X i ⊗ Y j) Z
      (((tensorRight (W k)).map (Sigma.ι X i ⊗ₘ Sigma.ι Y j)) ≫
        (((∐ X) ⊗ (∐ Y)) ◁ Sigma.ι W k) ≫ g₁) =
    (tensorRightAdjunction (W k)).homEquiv (X i ⊗ Y j) Z
      (((tensorRight (W k)).map (Sigma.ι X i ⊗ₘ Sigma.ι Y j)) ≫
        (((∐ X) ⊗ (∐ Y)) ◁ Sigma.ι W k) ≫ g₂) := by
    refine congrArg ((tensorRightAdjunction (W k)).homEquiv (X i ⊗ Y j) Z) ?_
    dsimp [tensorRight]
    rw [← tensorHom_def_assoc, h i j k, tensorHom_def_assoc]
  simpa only [Adjunction.homEquiv_naturality_left] using hijk

omit [MonoidalClosed C] [HasCoproducts C] [SymmetricCategory C] in
@[reassoc]
private lemma whiskerRight_tensorHom {X₁ X₂ Y₁ Y₂ Z : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ Y₁)
    (h : Z ⟶ Y₂) :
    (f ▷ Z) ≫ (g ⊗ₘ h) = (f ≫ g) ⊗ₘ h := by
  rw [← tensorHom_id, tensorHom_comp_tensorHom, id_comp]

omit [MonoidalClosed C] [HasCoproducts C] [SymmetricCategory C] in
@[reassoc]
private lemma whiskerLeft_tensorHom {X Y₁ Y₂ Z₁ Z₂ : C} (f : X ⟶ Z₁) (g : Y₁ ⟶ Y₂)
    (h : Y₂ ⟶ Z₂) :
    (X ◁ g) ≫ (f ⊗ₘ h) = f ⊗ₘ (g ≫ h) := by
  rw [← id_tensorHom, tensorHom_comp_tensorHom, id_comp]

end ClosedCoproducts

section TotalMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasCoproducts.{0} C] [HasInitial C]

/-- The unit isomorphism `𝟙_ C ≅ (GradedObject.total ℕ C).obj (𝟙_ (GradedObject ℕ C))`. -/
def gradedTotalεIso : 𝟙_ C ≅ (GradedObject.total ℕ C).obj (𝟙_ (GradedObject ℕ C)) where
  hom := GradedObject.Monoidal.tensorUnit₀.inv ≫ Sigma.ι (fun n ↦ (𝟙_ (GradedObject ℕ C)) n) 0
  inv := Sigma.desc (f := fun n ↦ (𝟙_ (GradedObject ℕ C)) n) fun n ↦
    if h : n = 0 then
      eqToHom (by subst h; rfl) ≫ GradedObject.Monoidal.tensorUnit₀.hom
    else
      (GradedObject.Monoidal.isInitialTensorUnitApply n h).to (𝟙_ C)
  hom_inv_id := by
    dsimp [GradedObject.total]
    simp
  inv_hom_id := by
    dsimp [GradedObject.total]
    refine Sigma.hom_ext _ _ fun n ↦ ?_
    by_cases h : n = 0
    · subst h
      simp
    · exact (GradedObject.Monoidal.isInitialTensorUnitApply n h).hom_ext _ _

/-- The tensor isomorphism `(GradedObject.total ℕ C).obj X ⊗ (GradedObject.total ℕ C).obj Y ≅
(GradedObject.total ℕ C).obj (X ⊗ Y)`. -/
def gradedTotalμIso (X Y : GradedObject ℕ C) :
    (GradedObject.total ℕ C).obj X ⊗ (GradedObject.total ℕ C).obj Y ≅
      (GradedObject.total ℕ C).obj (X ⊗ Y) where
  hom := tensorSigmaDesc (X := fun i ↦ X i) (Y := fun j ↦ Y j) fun i j ↦
    GradedObject.Monoidal.ιTensorObj X Y i j (i + j) rfl ≫
      Sigma.ι (fun k ↦ (X ⊗ Y) k) (i + j)
  inv := Sigma.desc (f := fun k ↦ (X ⊗ Y) k) fun k ↦
    GradedObject.Monoidal.tensorObjDesc fun i j _ ↦
      Sigma.ι (fun i ↦ X i) i ⊗ₘ Sigma.ι (fun j ↦ Y j) j
  hom_inv_id := by
    dsimp [GradedObject.total]
    refine tensorSigma_hom_ext fun i j ↦ ?_
    simp
  inv_hom_id := by
    dsimp [GradedObject.total]
    refine Sigma.hom_ext _ _ fun k ↦ GradedObject.Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
    subst h
    simp

@[reassoc]
private lemma ι_gradedTotalμ_of_eq (X Y : GradedObject ℕ C) (i j k : ℕ) (h : i + j = k) :
    (Sigma.ι (fun i ↦ X i) i ⊗ₘ Sigma.ι (fun j ↦ Y j) j) ≫
      (tensorSigmaDesc (X := fun i ↦ X i) (Y := fun j ↦ Y j) fun i j ↦
        GradedObject.Monoidal.ιTensorObj X Y i j (i + j) rfl ≫
          Sigma.ι (fun k ↦ (X ⊗ Y) k) (i + j)) =
      GradedObject.Monoidal.ιTensorObj X Y i j k h ≫ Sigma.ι (fun k ↦ (X ⊗ Y) k) k := by
  subst h
  exact ι_tensorSigmaDesc _ i j

/-- Core monoidal structure on `GradedObject.total ℕ C`. -/
def gradedTotalCoreMonoidal : (GradedObject.total ℕ C).CoreMonoidal where
  εIso := gradedTotalεIso
  μIso := gradedTotalμIso
  μIso_hom_natural_left {X Y} f Z := by
    refine tensorSigma_hom_ext fun i j ↦ ?_
    rw [← tensorHom_id f]
    dsimp [GradedObject.total, gradedTotalμIso]
    rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Sigma.ι_map, comp_id,
      ← whiskerRight_tensorHom_assoc, ι_tensorSigmaDesc, ι_tensorSigmaDesc_assoc, assoc,
      Sigma.ι_map]
    change _ = GradedObject.Monoidal.ιTensorObj X Z i j (i + j) rfl ≫
      GradedObject.Monoidal.tensorHom f (𝟙 Z) (i + j) ≫ _
    rw [GradedObject.Monoidal.ι_tensorHom_assoc,
      GradedObject.categoryOfGradedObjects_id, tensorHom_id]
  μIso_hom_natural_right X {Y Z} g := by
    refine tensorSigma_hom_ext fun i j ↦ ?_
    dsimp [GradedObject.total, gradedTotalμIso]
    rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Sigma.ι_map, comp_id,
      ← whiskerLeft_tensorHom_assoc, ι_tensorSigmaDesc, ι_tensorSigmaDesc_assoc, assoc,
      Sigma.ι_map]
    change _ = GradedObject.Monoidal.ιTensorObj Z X i j (i + j) rfl ≫
      GradedObject.Monoidal.tensorHom (𝟙 Z) g (i + j) ≫ _
    rw [GradedObject.Monoidal.ι_tensorHom_assoc,
      GradedObject.categoryOfGradedObjects_id, id_tensorHom]
  associativity X Y Z := by
    refine tensorSigma₃_hom_ext fun i j k ↦ ?_
    have hα : (α_ X Y Z).hom = (GradedObject.Monoidal.associator X Y Z).hom := rfl
    rw [hα]
    dsimp [GradedObject.total, gradedTotalμIso]
    rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, ι_tensorSigmaDesc, comp_id,
      ← whiskerRight_tensorHom_assoc, ι_tensorSigmaDesc_assoc, assoc, Sigma.ι_map]
    have h₁ : (GradedObject.Monoidal.ιTensorObj X Y i j (i + j) rfl ▷ Z k) ≫
        GradedObject.Monoidal.ιTensorObj (X ⊗ Y) Z (i + j) k (i + j + k) rfl =
        GradedObject.Monoidal.ιTensorObj₃' X Y Z i j k (i + j + k) rfl := rfl
    rw [associator_naturality_assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      comp_id, ι_tensorSigmaDesc, ← whiskerLeft_tensorHom_assoc,
      ι_gradedTotalμ_of_eq X (Y ⊗ Z) i (j + k) (i + j + k) (add_assoc i j k).symm]
    rw [reassoc_of% h₁, GradedObject.Monoidal.ιTensorObj₃'_associator_hom_assoc,
      GradedObject.Monoidal.ιTensorObj₃_eq X Y Z i j k (i + j + k) rfl (j + k) rfl, assoc]
    rfl
  left_unitality X := by
    rw [← cancel_mono ((GradedObject.total ℕ C).map (λ_ X).inv)]
    rw [assoc, assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, comp_id]
    refine leftTensorSigma_hom_ext fun k ↦ ?_
    dsimp [GradedObject.total, gradedTotalεIso, gradedTotalμIso]
    rw [leftUnitor_naturality_assoc, Sigma.ι_map]
    have hk : (λ_ X).inv k = (λ_ (X k)).inv ≫ (GradedObject.Monoidal.tensorUnit₀.inv ▷ X k) ≫
        GradedObject.Monoidal.ιTensorObj (𝟙_ _) X 0 k k (zero_add k) := rfl
    rw [hk, assoc, Iso.hom_inv_id_assoc, ← tensorHom_def'_assoc, ← whiskerRight_tensorHom_assoc,
      ι_gradedTotalμ_of_eq (𝟙_ (GradedObject ℕ C)) X 0 k k (zero_add k), assoc]
  right_unitality X := by
    rw [← cancel_mono ((GradedObject.total ℕ C).map (ρ_ X).inv)]
    rw [assoc, assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, comp_id]
    refine rightTensorSigma_hom_ext fun k ↦ ?_
    dsimp [GradedObject.total, gradedTotalεIso, gradedTotalμIso]
    rw [rightUnitor_naturality_assoc, Sigma.ι_map]
    have hk : (ρ_ X).inv k = (ρ_ (X k)).inv ≫ (X k ◁ GradedObject.Monoidal.tensorUnit₀.inv) ≫
        GradedObject.Monoidal.ιTensorObj X (𝟙_ _) k 0 k (add_zero k) := rfl
    rw [hk, assoc, Iso.hom_inv_id_assoc, ← tensorHom_def_assoc, ← whiskerLeft_tensorHom_assoc,
      ι_gradedTotalμ_of_eq X (𝟙_ (GradedObject ℕ C)) k 0 k (add_zero k), assoc]

instance instMonoidalGradedObjectTotal : (GradedObject.total ℕ C).Monoidal :=
  gradedTotalCoreMonoidal.toMonoidal

instance instBraidedGradedObjectTotal : (GradedObject.total ℕ C).Braided where
  braided X Y := by
    refine tensorSigma_hom_ext fun i j ↦ ?_
    have hβ : (β_ X Y).hom = (GradedObject.Monoidal.braiding X Y).hom := rfl
    change (Sigma.ι (fun i ↦ X i) i ⊗ₘ Sigma.ι (fun j ↦ Y j) j) ≫
        (gradedTotalμIso X Y).hom ≫ (GradedObject.total ℕ C).map (β_ X Y).hom =
      (Sigma.ι (fun i ↦ X i) i ⊗ₘ Sigma.ι (fun j ↦ Y j) j) ≫ (β_ _ _).hom ≫
        (gradedTotalμIso Y X).hom
    rw [hβ]
    dsimp [GradedObject.total, gradedTotalμIso, GradedObject.Monoidal.braiding]
    rw [BraidedCategory.braiding_naturality_assoc,
      ι_gradedTotalμ_of_eq_assoc X Y i j (i + j) rfl, Sigma.ι_map,
      ι_gradedTotalμ_of_eq Y X j i (i + j) (add_comm j i),
      GradedObject.Monoidal.ι_tensorObjDesc_assoc, assoc]

end TotalMonoidal

section GradedCommMonData

/-- Componentwise data for an `ℕ`-graded commutative monoid object in a braided monoidal category
`C`. -/
structure GradedCommMonData (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] where
  /-- The degree-`n` component object. -/
  X : GradedObject ℕ C
  /-- The unit morphism in degree `0`. -/
  one₀ : 𝟙_ C ⟶ X 0
  /-- The homogeneous multiplication morphism `X i ⊗ X j ⟶ X k` when `i + j = k`. -/
  mul : ∀ (i j k : ℕ), i + j = k → (X i ⊗ X j ⟶ X k)
  one_mul : ∀ k : ℕ, (one₀ ▷ X k) ≫ mul 0 k k (zero_add k) = (λ_ (X k)).hom
  mul_one : ∀ k : ℕ, (X k ◁ one₀) ≫ mul k 0 k (add_zero k) = (ρ_ (X k)).hom
  mul_assoc : ∀ (i₁ i₂ i₃ k : ℕ) (h : i₁ + i₂ + i₃ = k),
    (mul i₁ i₂ (i₁ + i₂) rfl ▷ X i₃) ≫ mul (i₁ + i₂) i₃ k h =
      (α_ (X i₁) (X i₂) (X i₃)).hom ≫
        (X i₁ ◁ mul i₂ i₃ (i₂ + i₃) rfl) ≫ mul i₁ (i₂ + i₃) k (by omega)
  mul_comm : ∀ (i j k : ℕ) (h : i + j = k),
    (β_ (X i) (X j)).hom ≫ mul j i k (by omega) = mul i j k h

namespace GradedCommMonData

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Morphisms of componentwise graded commutative monoid data. -/
@[ext]
structure Hom (A B : GradedCommMonData C) where
  /-- The degree-`n` morphism. -/
  hom : A.X ⟶ B.X
  one_hom : A.one₀ ≫ hom 0 = B.one₀
  mul_hom : ∀ (i j k : ℕ) (h : i + j = k),
    (hom i ⊗ₘ hom j) ≫ B.mul i j k h = A.mul i j k h ≫ hom k

/-- Push forward componentwise graded commutative monoid data along a lax braided monoidal
functor. -/
@[expose]
def mapObj {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxBraided] (A : GradedCommMonData C) : GradedCommMonData D where
  X n := F.obj (A.X n)
  one₀ := Functor.LaxMonoidal.ε F ≫ F.map A.one₀
  mul i j k h := Functor.LaxMonoidal.μ F (A.X i) (A.X j) ≫ F.map (A.mul i j k h)
  one_mul k := by
    rw [comp_whiskerRight_assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      ← F.map_comp, A.one_mul, Functor.LaxMonoidal.left_unitality]
  mul_one k := by
    rw [whiskerLeft_comp_assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
      ← F.map_comp, A.mul_one, Functor.LaxMonoidal.right_unitality]
  mul_assoc i₁ i₂ i₃ k h := by
    rw [comp_whiskerRight_assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      ← F.map_comp, A.mul_assoc i₁ i₂ i₃ k h, F.map_comp, F.map_comp,
      Functor.LaxMonoidal.associativity_assoc, whiskerLeft_comp_assoc,
      Functor.LaxMonoidal.μ_natural_right_assoc]
  mul_comm i j k h := by
    rw [← Functor.LaxBraided.braided_assoc, ← F.map_comp, A.mul_comm i j k h]

/-- Push forward a morphism of componentwise graded commutative monoid data along a lax braided
monoidal functor. -/
@[expose]
def mapHom {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxBraided] {A B : GradedCommMonData C} (f : Hom A B) :
    Hom (A.mapObj F) (B.mapObj F) where
  hom n := F.map (f.hom n)
  one_hom := by
    change (Functor.LaxMonoidal.ε F ≫ F.map A.one₀) ≫ F.map (f.hom 0) =
      Functor.LaxMonoidal.ε F ≫ F.map B.one₀
    rw [assoc, ← F.map_comp, f.one_hom]
  mul_hom i j k h := by
    change (F.map (f.hom i) ⊗ₘ F.map (f.hom j)) ≫
        (Functor.LaxMonoidal.μ F _ _ ≫ F.map _) =
      (Functor.LaxMonoidal.μ F _ _ ≫ F.map _) ≫ F.map (f.hom k)
    rw [Functor.LaxMonoidal.μ_natural_assoc, ← F.map_comp, f.mul_hom, F.map_comp, assoc]

section ToCommMon

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasCoproducts.{0} C] [HasInitial C]

/-- The graded unit morphism `𝟙_ (GradedObject ℕ C) ⟶ A.X` of `A : GradedCommMonData C`. -/
def toGradedOne (A : GradedCommMonData C) : 𝟙_ (GradedObject ℕ C) ⟶ A.X := fun n ↦
  if h : n = 0 then
    eqToHom (by subst h; rfl) ≫ GradedObject.Monoidal.tensorUnit₀.hom ≫
      A.one₀ ≫ eqToHom (by subst h; rfl)
  else
    (GradedObject.Monoidal.isInitialTensorUnitApply n h).to (A.X n)

@[simp, reassoc]
lemma tensorUnit₀_inv_toGradedOne_zero (A : GradedCommMonData C) :
    GradedObject.Monoidal.tensorUnit₀.inv ≫ A.toGradedOne 0 = A.one₀ := by
  simp [toGradedOne]

/-- The graded multiplication morphism `A.X ⊗ A.X ⟶ A.X` of `A : GradedCommMonData C`. -/
def toGradedMul (A : GradedCommMonData C) : A.X ⊗ A.X ⟶ A.X := fun k ↦
  GradedObject.Monoidal.tensorObjDesc fun i j h ↦ A.mul i j k h

@[simp, reassoc]
lemma ι_toGradedMul (A : GradedCommMonData C) (i j k : ℕ) (h : i + j = k) :
    GradedObject.Monoidal.ιTensorObj A.X A.X i j k h ≫ A.toGradedMul k = A.mul i j k h :=
  GradedObject.Monoidal.ι_tensorObjDesc _ i j h

/-- The `MonObj` instance on `A.X` induced by `A : GradedCommMonData C`. -/
@[expose, instance_reducible]
def toMonObj (A : GradedCommMonData C) : MonObj A.X where
  one := A.toGradedOne
  mul := A.toGradedMul
  one_mul := by
    rw [← cancel_epi (λ_ A.X).inv, Iso.inv_hom_id]
    ext k
    have hk : (λ_ A.X).inv k =
        (λ_ (A.X k)).inv ≫ (GradedObject.Monoidal.tensorUnit₀.inv ▷ A.X k) ≫
          GradedObject.Monoidal.ιTensorObj (𝟙_ _) A.X 0 k k (zero_add k) := rfl
    change (λ_ A.X).inv k ≫
        GradedObject.Monoidal.tensorHom A.toGradedOne (𝟙 A.X) k ≫ A.toGradedMul k =
      𝟙 (A.X k)
    rw [hk, assoc, assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
      GradedObject.categoryOfGradedObjects_id, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, tensorUnit₀_inv_toGradedOne_zero, comp_id,
      tensorHom_id, ι_toGradedMul, A.one_mul, Iso.inv_hom_id]
  mul_one := by
    rw [← cancel_epi (ρ_ A.X).inv, Iso.inv_hom_id]
    ext k
    have hk : (ρ_ A.X).inv k =
        (ρ_ (A.X k)).inv ≫ (A.X k ◁ GradedObject.Monoidal.tensorUnit₀.inv) ≫
          GradedObject.Monoidal.ιTensorObj A.X (𝟙_ _) k 0 k (add_zero k) := rfl
    change (ρ_ A.X).inv k ≫
        GradedObject.Monoidal.tensorHom (𝟙 A.X) A.toGradedOne k ≫ A.toGradedMul k =
      𝟙 (A.X k)
    rw [hk, assoc, assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
      GradedObject.categoryOfGradedObjects_id, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, tensorUnit₀_inv_toGradedOne_zero, id_comp,
      id_tensorHom, ι_toGradedMul, A.mul_one, Iso.inv_hom_id]
  mul_assoc := by
    ext k
    refine GradedObject.Monoidal.tensorObj₃'_ext _ _ fun i₁ i₂ i₃ h ↦ ?_
    change GradedObject.Monoidal.ιTensorObj₃' A.X A.X A.X i₁ i₂ i₃ k h ≫
        GradedObject.Monoidal.tensorHom A.toGradedMul (𝟙 A.X) k ≫ A.toGradedMul k =
      GradedObject.Monoidal.ιTensorObj₃' A.X A.X A.X i₁ i₂ i₃ k h ≫
        (GradedObject.Monoidal.associator A.X A.X A.X).hom k ≫
        GradedObject.Monoidal.tensorHom (𝟙 A.X) A.toGradedMul k ≫ A.toGradedMul k
    rw [GradedObject.Monoidal.ιTensorObj₃'_associator_hom_assoc,
      GradedObject.Monoidal.ιTensorObj₃'_eq A.X A.X A.X i₁ i₂ i₃ k h (i₁ + i₂) rfl,
      assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
      GradedObject.categoryOfGradedObjects_id, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, ι_toGradedMul, comp_id, tensorHom_id, ι_toGradedMul,
      GradedObject.Monoidal.ιTensorObj₃_eq A.X A.X A.X i₁ i₂ i₃ k h (i₂ + i₃) rfl,
      assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
      GradedObject.categoryOfGradedObjects_id, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, ι_toGradedMul, id_comp, id_tensorHom, ι_toGradedMul,
      A.mul_assoc i₁ i₂ i₃ k h]

/-- Assemble `A : GradedCommMonData C` into `CommMon (GradedObject ℕ C)`. -/
@[expose]
def toCommMonObj (A : GradedCommMonData C) : CommMon (GradedObject ℕ C) :=
  letI : MonObj A.X := A.toMonObj
  haveI : IsCommMonObj A.X :=
    { mul_comm := by
        ext k
        refine GradedObject.Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
        change GradedObject.Monoidal.ιTensorObj A.X A.X i j k h ≫
            (GradedObject.Monoidal.braiding A.X A.X).hom k ≫ A.toGradedMul k =
          GradedObject.Monoidal.ιTensorObj A.X A.X i j k h ≫ A.toGradedMul k
        dsimp [GradedObject.Monoidal.braiding]
        rw [GradedObject.Monoidal.ι_tensorObjDesc_assoc, assoc, ι_toGradedMul, ι_toGradedMul,
          A.mul_comm i j k h] }
  CommMon.mk A.X

/-- Assemble `f : Hom A B` into a morphism `A.toCommMonObj ⟶ B.toCommMonObj` in
`CommMon (GradedObject ℕ C)`. -/
@[expose]
def toCommMonHom {A B : GradedCommMonData C} (f : Hom A B) :
    A.toCommMonObj ⟶ B.toCommMonObj :=
  letI : MonObj A.X := A.toMonObj
  letI : MonObj B.X := B.toMonObj
  CommMon.homMk
    { hom := f.hom
      isMonHom_hom :=
        { one_hom := by
            ext n
            by_cases h : n = 0
            · subst h
              rw [← cancel_epi GradedObject.Monoidal.tensorUnit₀.inv]
              change GradedObject.Monoidal.tensorUnit₀.inv ≫ A.toGradedOne 0 ≫ f.hom 0 =
                GradedObject.Monoidal.tensorUnit₀.inv ≫ B.toGradedOne 0
              rw [tensorUnit₀_inv_toGradedOne_zero_assoc, tensorUnit₀_inv_toGradedOne_zero,
                f.one_hom]
            · exact (GradedObject.Monoidal.isInitialTensorUnitApply n h).hom_ext _ _
          mul_hom := by
            ext k
            refine GradedObject.Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
            change GradedObject.Monoidal.ιTensorObj A.X A.X i j k h ≫ A.toGradedMul k ≫ f.hom k =
              GradedObject.Monoidal.ιTensorObj A.X A.X i j k h ≫
                GradedObject.Monoidal.tensorHom f.hom f.hom k ≫ B.toGradedMul k
            rw [GradedObject.Monoidal.ι_tensorHom_assoc, ι_toGradedMul, ι_toGradedMul_assoc,
              f.mul_hom i j k h] } }

end ToCommMon

end GradedCommMonData

end GradedCommMonData

end

end TauCeti
