/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.SymmetricAlgebra

/-!
# Universal property of the symmetric algebra of a sheaf of modules

For a scheme `X`, a sheaf of `𝒪_X`-modules `M : X.Modules`, and a commutative monoid object
`B : CommMon X.Modules`, we establish the universal property of the symmetric algebra
`(GradedObject.total ℕ X.Modules).mapCommMon.obj (sheafSymmetricAlgebraData M).toCommMonObj`:
morphisms of commutative `𝒪_X`-algebras out of `Sym(M)` into `B` correspond bijectively to module
morphisms `M ⟶ B.X` (`TauCeti.AlgebraicGeometry.symmetricAlgebraCommMonHomEquiv`), naturally in both
`M` and `B`.
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti

universe v u

noncomputable section

namespace GradedCommMonData

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Constant `GradedCommMonData` with `B.X` in every degree and multiplication `μ[B.X]`. -/
@[expose]
def const (B : CommMon C) : GradedCommMonData C where
  X _ := B.X
  one₀ := η[B.X]
  mul _ _ _ _ := μ[B.X]
  one_mul _ := MonObj.one_mul (X := B.X)
  mul_one _ := MonObj.mul_one (X := B.X)
  mul_assoc _ _ _ _ _ := MonObj.mul_assoc (X := B.X)
  mul_comm _ _ _ _ := IsCommMonObj.mul_comm (X := B.X)

/-- If `A` is generated in degree `1` (in the sense that `A.one₀` and `A.mul n 1 (n + 1) rfl` are
epimorphisms), two morphisms `A.Hom D` agreeing in degree `1` are equal. -/
lemma hom_ext_of_degree_one {A D : GradedCommMonData C}
    (h_one : Epi A.one₀) (h_mul : ∀ n, Epi (A.mul n 1 (n + 1) rfl))
    {f₁ f₂ : A.Hom D} (h1 : f₁.hom 1 = f₂.hom 1) : f₁ = f₂ := by
  ext n
  induction n with
  | zero =>
    rw [← cancel_epi A.one₀, f₁.one_hom, f₂.one_hom]
  | succ n ih =>
    have := h_mul n
    rw [← cancel_epi (A.mul n 1 (n + 1) rfl), ← f₁.mul_hom n 1 (n + 1) rfl,
      ← f₂.mul_hom n 1 (n + 1) rfl, ih, h1]

end Braided

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasCoproducts.{0} C] [HasInitial C]

/-- Morphisms in `CommMon C` from the totalization of `A.toCommMonObj` to `B` correspond
bijectively to morphisms `A.Hom (GradedCommMonData.const B)`. -/
@[expose]
def totalToCommMonHomEquiv (A : GradedCommMonData C) (B : CommMon C) :
    ((GradedObject.total ℕ C).mapCommMon.obj A.toCommMonObj ⟶ B) ≃
      A.Hom (GradedCommMonData.const B) where
  toFun g :=
    { hom := fun n ↦ Sigma.ι A.X n ≫ (g.hom.hom : ∐ A.X ⟶ B.X)
      one_hom := by
        let g₀ : ((GradedObject.total ℕ C).mapCommMon.obj A.toCommMonObj).X ⟶ B.X := g.hom.hom
        have h1 : η[((GradedObject.total ℕ C).mapCommMon.obj A.toCommMonObj).X] ≫ g₀ = η[B.X] :=
          IsMonHom.one_hom (f := g.hom.hom)
        exact (assoc A.one₀ (Sigma.ι A.X 0) g₀).symm.trans
          ((congrArg (· ≫ g₀) (total_mapCommMon_obj_one A).symm).trans h1)
      mul_hom := fun i j k h ↦ by
        subst h
        let g₀ : ((GradedObject.total ℕ C).mapCommMon.obj A.toCommMonObj).X ⟶ B.X := g.hom.hom
        have hmul : μ[((GradedObject.total ℕ C).mapCommMon.obj A.toCommMonObj).X] ≫ g₀ =
            (g₀ ⊗ₘ g₀) ≫ μ[B.X] :=
          IsMonHom.mul_hom (f := g.hom.hom)
        exact (tensorHom_comp_tensorHom_assoc (Sigma.ι A.X i) (Sigma.ι A.X j) g₀ g₀ _).symm.trans
          ((congrArg ((Sigma.ι A.X i ⊗ₘ Sigma.ι A.X j) ≫ ·) hmul.symm).trans
            ((assoc (Sigma.ι A.X i ⊗ₘ Sigma.ι A.X j) _ g₀).symm.trans
              ((congrArg (· ≫ g₀) (ι_total_mapCommMon_obj_mul A i j)).trans
                (assoc (A.mul i j (i + j) rfl) (Sigma.ι A.X (i + j)) g₀)))) }
  invFun f :=
    let f₀ : ∀ n : ℕ, A.X n ⟶ B.X := f.hom
    CommMon.homMk
      { hom := (Sigma.desc f₀ : ((GradedObject.total ℕ C).mapCommMon.obj A.toCommMonObj).X ⟶ B.X)
        isMonHom_hom :=
          { one_hom :=
              (congrArg (· ≫ Sigma.desc f₀) (total_mapCommMon_obj_one A)).trans
                ((assoc A.one₀ (Sigma.ι A.X 0) (Sigma.desc f₀)).trans
                  ((congrArg (A.one₀ ≫ ·) (Sigma.ι_comp_desc f₀ 0)).trans f.one_hom))
            mul_hom :=
              tensorSigma_hom_ext (X := A.X) (Y := A.X) fun i j ↦
                (assoc (Sigma.ι A.X i ⊗ₘ Sigma.ι A.X j) _ (Sigma.desc f₀)).symm.trans <|
                  (congrArg (· ≫ Sigma.desc f₀) (ι_total_mapCommMon_obj_mul A i j)).trans <|
                    (assoc (A.mul i j (i + j) rfl) (Sigma.ι A.X (i + j)) (Sigma.desc f₀)).trans <|
                      (congrArg (A.mul i j (i + j) rfl ≫ ·) (Sigma.ι_comp_desc f₀ (i + j))).trans <|
                        (f.mul_hom i j (i + j) rfl).symm.trans <|
                          (congrArg (· ≫ μ[B.X])
                            (congrArg₂ tensorHom (Sigma.ι_comp_desc f₀ i).symm
                              (Sigma.ι_comp_desc f₀ j).symm)).trans
                            (tensorHom_comp_tensorHom_assoc _ _ _ _ _).symm } }
  left_inv g := by
    apply CommMon.hom_ext
    exact Sigma.hom_ext _ _ fun n ↦ Sigma.ι_comp_desc _ n
  right_inv f := by
    ext n
    exact Sigma.ι_comp_desc (f.hom : ∀ n : ℕ, A.X n ⟶ B.X) n

end Symmetric

end GradedCommMonData

namespace AlgebraicGeometry

section ModuleLift

variable {R : Type u} [CommRing R]

/-- Given a commutative monoid `B` in `ModuleCat.{u} R` and a linear map `u : M ⟶ B.X`, the
induced morphism `moduleSymmetricAlgebraData M ⟶ GradedCommMonData.const B` given in degree `n` by
restricting `SymmetricAlgebra.lift u.hom` to `M.symmetricPower n`. -/
@[expose]
def moduleSymmetricAlgebraLift (M : ModuleCat.{u} R) (B : CommMon (ModuleCat.{u} R))
    (u : M ⟶ B.X) :
    (moduleSymmetricAlgebraData M).Hom (GradedCommMonData.const B) :=
  letI : CommRing B.X := ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing B.X
  letI : Algebra R B.X := ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ B.X
  let φ : SymmetricAlgebra R M →ₐ[R] B.X := SymmetricAlgebra.lift u.hom
  { hom := fun n ↦ ModuleCat.ofHom (φ.toLinearMap.comp
      (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n).subtype)
    one_hom :=
      ModuleCat.hom_ext <| LinearMap.ext fun r ↦
        (congrArg φ (ModuleCat.symmetricPower.coe_iso₀_inv_apply M r)).trans
          (AlgHom.commutes φ r)
    mul_hom := fun i j k h ↦
      ModuleCat.MonoidalCategory.tensor_ext fun x y ↦
        (map_mul φ x.1 y.1).symm.trans
          (congrArg φ (coe_symmetricPowerMul_tmul M i j k h x y)).symm }

@[simp]
lemma iso₁_inv_moduleSymmetricAlgebraLift_hom_one (M : ModuleCat.{u} R)
    (B : CommMon (ModuleCat.{u} R)) (u : M ⟶ B.X) :
    (ModuleCat.symmetricPower.iso₁ M).inv ≫ (moduleSymmetricAlgebraLift M B u).hom 1 = u := by
  let _ : CommRing B.X := ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing B.X
  let _ : Algebra R B.X := ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ B.X
  exact ModuleCat.hom_ext <| LinearMap.ext fun m ↦
    (congrArg (SymmetricAlgebra.lift u.hom)
      (ModuleCat.symmetricPower.coe_iso₁_inv_apply M m)).trans
      (SymmetricAlgebra.lift_ι_apply u.hom m)

end ModuleLift

section SheafLift

open TauCeti.SheafOfModules (ringCatSheaf)

variable {X : Scheme.{u}}

lemma presheafSymmetricAlgebraLiftHom_naturality (M : X.Modules) (B : CommMon X.Modules)
    (u : M ⟶ B.X) (n : ℕ) {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    let P : PresheafOfModulesOfCommRing.{u} X.presheaf := M.val
    let Q : PresheafOfModulesOfCommRing.{u} X.presheaf := B.X.val
    let φ : P ⟶ Q := u.val
    ((PresheafOfModulesOfCommRing.symmetricPower n).obj P).map i ≫
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
        ((moduleSymmetricAlgebraLift (P.obj V) (B.sectionsCommMon V.unop) (φ.app' V)).hom n) =
      (moduleSymmetricAlgebraLift (P.obj U) (B.sectionsCommMon U.unop) (φ.app' U)).hom n ≫
        Q.map i := by
  intro P Q φ
  let uU : P.obj U ⟶ (B.sectionsCommMon U.unop).X := φ.app' U
  let uV : P.obj V ⟶ (B.sectionsCommMon V.unop).X := φ.app' V
  let _ : CommRing (B.sectionsCommMon U.unop).X :=
    ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing (B.sectionsCommMon U.unop).X
  let _ : Algebra (X.presheaf.obj U) (B.sectionsCommMon U.unop).X :=
    ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ (B.sectionsCommMon U.unop).X
  let _ : CommRing (B.sectionsCommMon V.unop).X :=
    ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing (B.sectionsCommMon V.unop).X
  let _ : Algebra (X.presheaf.obj V) (B.sectionsCommMon V.unop).X :=
    ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ (B.sectionsCommMon V.unop).X
  have key : (B.restrictSections i.unop).comp
      (SymmetricAlgebra.lift uU.hom).toRingHom =
      (SymmetricAlgebra.lift uV.hom).toRingHom.comp
        (SymmetricAlgebra.mapₛₗ
          ((ModuleCat.semilinearMapAddEquiv (X.presheaf.map i).hom _ _).symm
            (P.map i))) := by
    refine SymmetricAlgebra.ringHom_ext ?_ (fun m ↦ ?_)
    · ext r
      change B.restrictSections i.unop
          ((SymmetricAlgebra.lift uU.hom)
            (algebraMap (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj U) (P.obj U)) r)) =
        (SymmetricAlgebra.lift uV.hom)
          ((SymmetricAlgebra.mapₛₗ
            ((ModuleCat.semilinearMapAddEquiv (X.presheaf.map i).hom _ _).symm (P.map i)))
            (algebraMap (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj U) (P.obj U)) r))
      rw [AlgHom.commutes, SymmetricAlgebra.mapₛₗ_algebraMap, AlgHom.commutes]
      have hnat := B.toSectionsPresheaf.naturality i
      rw [CommMon.toSectionsPresheaf_app, CommMon.toSectionsPresheaf_app,
        CommMon.sectionsPresheaf_map] at hnat
      exact (ConcreteCategory.congr_hom hnat r).symm
    · change B.restrictSections i.unop
          ((SymmetricAlgebra.lift uU.hom) (SymmetricAlgebra.ι (X.presheaf.obj U) (P.obj U) m)) =
        (SymmetricAlgebra.lift uV.hom)
          ((SymmetricAlgebra.mapₛₗ
            ((ModuleCat.semilinearMapAddEquiv (X.presheaf.map i).hom _ _).symm (P.map i)))
            (SymmetricAlgebra.ι (X.presheaf.obj U) (P.obj U) m))
      rw [SymmetricAlgebra.lift_ι_apply, SymmetricAlgebra.mapₛₗ_ι, SymmetricAlgebra.lift_ι_apply]
      exact (B.restrictSections_apply i.unop (uU m)).trans
        (PresheafOfModules.naturality_apply φ i m).symm
  ext x
  exact (congrArg (SymmetricAlgebra.lift uV.hom)
    (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n P i x)).trans
    ((RingHom.congr_fun key x.1).symm.trans
      (B.restrictSections_apply i.unop ((SymmetricAlgebra.lift uU.hom) x.1)))

/-- Sectionwise degree-`n` morphism from `presheafSymmetricAlgebraData M.val` to the underlying
presheaf of `B : CommMon X.Modules`. -/
@[expose]
def presheafSymmetricAlgebraLiftHom (M : X.Modules) (B : CommMon X.Modules) (u : M ⟶ B.X)
    (n : ℕ) :
    (PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj
        (M.val : PresheafOfModulesOfCommRing.{u} X.presheaf) ⟶
      (_root_.SheafOfModules.forget (ringCatSheaf X.sheaf)).obj B.X :=
  let P : PresheafOfModulesOfCommRing.{u} X.presheaf := M.val
  let Q : PresheafOfModulesOfCommRing.{u} X.presheaf := B.X.val
  let φ : P ⟶ Q := u.val
  PresheafOfModulesOfCommRing.homMk
    (fun U ↦ (moduleSymmetricAlgebraLift (P.obj U) (B.sectionsCommMon U.unop) (φ.app' U)).hom n)
    (fun i ↦ presheafSymmetricAlgebraLiftHom_naturality M B u n i)

@[simp]
lemma presheafSymmetricAlgebraLiftHom_app (M : X.Modules) (B : CommMon X.Modules) (u : M ⟶ B.X)
    (n : ℕ) (U : X.Opensᵒᵖ) :
    let P : PresheafOfModulesOfCommRing.{u} X.presheaf := M.val
    (presheafSymmetricAlgebraLiftHom M B u n).app U =
      (moduleSymmetricAlgebraLift (P.obj U) (B.sectionsCommMon U.unop) (u.val.app' U)).hom n :=
  (rfl)

lemma sheafSymmetricAlgebraLift_one_hom (M : X.Modules) (B : CommMon X.Modules)
    (u : M ⟶ B.X) :
    let P : PresheafOfModulesOfCommRing.{u} X.presheaf := M.val
    let G : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget (ringCatSheaf X.sheaf)
    let adj : sheafifyModules X ⊣ G :=
      TauCeti.SheafOfModules.sheafificationForgetAdjunction X.sheaf
    (sheafSymmetricAlgebraData M).one₀ ≫
      (adj.homEquiv ((PresheafOfModulesOfCommRing.symmetricPower 0).obj P) B.X).symm
        (presheafSymmetricAlgebraLiftHom M B u 0) = η[B.X] := by
  intro P G adj
  let _ : G.LaxMonoidal := TauCeti.SheafOfModules.forgetLaxMonoidal X.sheaf
  let φ : P ⟶ B.X.val := u.val
  let f₀ := presheafSymmetricAlgebraLiftHom M B u 0
  refine (cancel_epi (Functor.OplaxMonoidal.η (sheafifyModules X))).1 ?_
  apply (adj.homEquiv (𝟙_ (PresheafOfModulesOfCommRing.{u} X.presheaf)) B.X).injective
  have h_lhs : adj.homEquiv _ B.X
      (Functor.OplaxMonoidal.η (sheafifyModules X) ≫
        ((sheafSymmetricAlgebraData M).one₀ ≫ (adj.homEquiv _ B.X).symm f₀)) =
      (presheafSymmetricAlgebraData (R := X.presheaf) P).one₀ ≫ f₀ :=
    (congrArg (adj.homEquiv _ B.X)
      ((congrArg (Functor.OplaxMonoidal.η (sheafifyModules X) ≫ ·)
        (assoc (Functor.LaxMonoidal.ε (sheafifyModules X))
          ((sheafifyModules X).map (presheafSymmetricAlgebraData (R := X.presheaf) P).one₀)
          ((adj.homEquiv _ B.X).symm f₀))).trans
        (Functor.Monoidal.η_ε_assoc (sheafifyModules X) _))).trans
      ((adj.homEquiv_naturality_left _ _).trans
        (congrArg (_ ≫ ·) (Equiv.apply_symm_apply _ _)))
  have hη : Functor.OplaxMonoidal.η (sheafifyModules X) = adj.counit.app (𝟙_ X.Modules) :=
    (((TauCeti.SheafOfModules.sheafification_η X.sheaf).trans
      (TauCeti.SheafOfModules.sheafificationUnitIso_hom X.sheaf)).trans
      (TauCeti.SheafOfModules.sheafificationIso_hom (ringCatSheaf X.sheaf)
        (_root_.SheafOfModules.unit (ringCatSheaf X.sheaf))).symm).trans
      (TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app X.sheaf (𝟙_ X.Modules)).symm
  have h_rhs : adj.homEquiv _ B.X
      (Functor.OplaxMonoidal.η (sheafifyModules X) ≫ η[B.X]) = G.map η[B.X] :=
    (congrArg (adj.homEquiv _ B.X)
      (((congrArg (· ≫ η[B.X]) hη).trans
        (adj.counit.naturality η[B.X]).symm).trans
        (adj.homEquiv_counit _ _ (G.map η[B.X])).symm)).trans
      (Equiv.apply_symm_apply _ _)
  refine h_lhs.trans (Eq.trans ?_ h_rhs.symm)
  ext1 U
  exact ((moduleSymmetricAlgebraLift (P.obj U) (B.sectionsCommMon U.unop)
    (φ.app' U)).one_hom).trans
    ((congrArg (· ≫ (G.map η[B.X]).app U)
      (Scheme.Modules.sectionsFunctor_ε U.unop)).trans
      (id_comp ((G.map η[B.X]).app U)))

lemma sheafSymmetricAlgebraLift_mul_hom (M : X.Modules) (B : CommMon X.Modules)
    (u : M ⟶ B.X) (i j k : ℕ) (h : i + j = k) :
    let P : PresheafOfModulesOfCommRing.{u} X.presheaf := M.val
    let G : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget (ringCatSheaf X.sheaf)
    let adj : sheafifyModules X ⊣ G :=
      TauCeti.SheafOfModules.sheafificationForgetAdjunction X.sheaf
    ((adj.homEquiv ((PresheafOfModulesOfCommRing.symmetricPower i).obj P) B.X).symm
        (presheafSymmetricAlgebraLiftHom M B u i) ⊗ₘ
      (adj.homEquiv ((PresheafOfModulesOfCommRing.symmetricPower j).obj P) B.X).symm
        (presheafSymmetricAlgebraLiftHom M B u j)) ≫ μ[B.X] =
      (sheafSymmetricAlgebraData M).mul i j k h ≫
        (adj.homEquiv ((PresheafOfModulesOfCommRing.symmetricPower k).obj P) B.X).symm
          (presheafSymmetricAlgebraLiftHom M B u k) := by
  intro P G adj
  let _ : MonoidalCategory (SheafOfModules.{u} (ringCatSheaf X.sheaf)) :=
    TauCeti.SheafOfModules.monoidalCategory X.sheaf
  let _ : G.LaxMonoidal := TauCeti.SheafOfModules.forgetLaxMonoidal X.sheaf
  let φ : P ⟶ B.X.val := u.val
  let δ := Functor.OplaxMonoidal.δ (sheafifyModules X)
    ((PresheafOfModulesOfCommRing.symmetricPower i).obj P)
    ((PresheafOfModulesOfCommRing.symmetricPower j).obj P)
  let fi := presheafSymmetricAlgebraLiftHom M B u i
  let fj := presheafSymmetricAlgebraLiftHom M B u j
  let fk := presheafSymmetricAlgebraLiftHom M B u k
  refine (cancel_epi δ).1 ?_
  apply (adj.homEquiv
    ((PresheafOfModulesOfCommRing.symmetricPower i).obj P ⊗
      (PresheafOfModulesOfCommRing.symmetricPower j).obj P) B.X).injective
  have h_rhs : adj.homEquiv _ B.X
      (δ ≫ ((sheafSymmetricAlgebraData M).mul i j k h ≫ (adj.homEquiv _ B.X).symm fk)) =
      (presheafSymmetricAlgebraData (R := X.presheaf) P).mul i j k h ≫ fk :=
    (congrArg (adj.homEquiv _ B.X)
      ((congrArg (δ ≫ ·)
        (assoc (Functor.LaxMonoidal.μ (sheafifyModules X) _ _)
          ((sheafifyModules X).map ((presheafSymmetricAlgebraData (R := X.presheaf) P).mul i j k h))
          ((adj.homEquiv _ B.X).symm fk))).trans
        (Functor.Monoidal.δ_μ_assoc (sheafifyModules X) _ _ _))).trans
      ((adj.homEquiv_naturality_left _ _).trans
        (congrArg (_ ≫ ·) (Equiv.apply_symm_apply _ _)))
  have h_inv : (B.X.tensorUnderlyingIso B.X).inv =
      Functor.OplaxMonoidal.δ (sheafifyModules X) (G.obj B.X) (G.obj B.X) ≫
        (adj.counit.app B.X ⊗ₘ adj.counit.app B.X) :=
    (SheafOfModules.tensorUnderlyingIso_inv B.X B.X).trans
      (congrArg (Functor.OplaxMonoidal.δ (sheafifyModules X) (G.obj B.X) (G.obj B.X) ≫ ·)
        (congrArg₂ tensorHom
          (TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app X.sheaf B.X).symm
          (TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app X.sheaf B.X).symm))
  have h_tensor : δ ≫ ((adj.homEquiv _ B.X).symm fi ⊗ₘ (adj.homEquiv _ B.X).symm fj) =
      (sheafifyModules X).map (fi ⊗ₘ fj) ≫ (B.X.tensorUnderlyingIso B.X).inv := by
    have h1 : ((adj.homEquiv _ B.X).symm fi ⊗ₘ (adj.homEquiv _ B.X).symm fj) =
        ((sheafifyModules X).map fi ⊗ₘ (sheafifyModules X).map fj) ≫
          (adj.counit.app B.X ⊗ₘ adj.counit.app B.X) :=
      (congrArg₂ tensorHom (adj.homEquiv_counit _ _ fi)
        (adj.homEquiv_counit _ _ fj)).trans
        (tensorHom_comp_tensorHom _ _ _ _).symm
    exact ((((congrArg (δ ≫ ·) h1).trans
      (assoc _ _ _).symm).trans
        (congrArg (· ≫ (adj.counit.app B.X ⊗ₘ adj.counit.app B.X))
          (Functor.OplaxMonoidal.δ_natural (sheafifyModules X) fi fj))).trans
          (assoc _ _ _)).trans
          (congrArg ((sheafifyModules X).map (fi ⊗ₘ fj) ≫ ·) h_inv.symm)
  have h_lhs : adj.homEquiv _ B.X
      (δ ≫ (((adj.homEquiv _ B.X).symm fi ⊗ₘ (adj.homEquiv _ B.X).symm fj) ≫ μ[B.X])) =
      (fi ⊗ₘ fj) ≫ (Functor.LaxMonoidal.μ G B.X B.X ≫ G.map μ[B.X]) :=
    ((congrArg (adj.homEquiv _ B.X)
      (((assoc _ _ _).symm.trans
        (congrArg (· ≫ μ[B.X]) h_tensor)).trans (assoc _ _ _))).trans
      (adj.homEquiv_naturality_left (fi ⊗ₘ fj)
        ((B.X.tensorUnderlyingIso B.X).inv ≫ μ[B.X]))).trans
      (congrArg ((fi ⊗ₘ fj) ≫ ·)
        (TauCeti.SheafOfModules.forget_μ_comp_map (R := X.sheaf) μ[B.X]).symm)
  refine h_lhs.trans (Eq.trans ?_ h_rhs.symm)
  ext1 U
  have hμ : ((Functor.LaxMonoidal.μ G B.X B.X ≫ G.map μ[B.X]).app U) =
      μ[(B.sectionsCommMon U.unop).X] :=
    congrArg (· ≫ (G.map μ[B.X]).app U)
      ((id_comp ((Functor.LaxMonoidal.μ G B.X B.X).app U)).symm.trans
        ((congrArg (· ≫ (Functor.LaxMonoidal.μ G B.X B.X).app U)
          (PresheafOfModulesOfCommRing.evaluation_μ U (G.obj B.X) (G.obj B.X)).symm).trans
          (Functor.LaxMonoidal.comp_μ G
            (PresheafOfModulesOfCommRing.evaluation U) B.X B.X).symm))
  exact (congrArg ((fi.app' U ⊗ₘ fj.app' U) ≫ ·) hμ).trans
    ((moduleSymmetricAlgebraLift (P.obj U) (B.sectionsCommMon U.unop)
      (φ.app' U)).mul_hom i j k h)

/-- The graded morphism from `sheafSymmetricAlgebraData M` to `GradedCommMonData.const B` induced
by `u : M ⟶ B.X`. -/
@[expose]
def sheafSymmetricAlgebraLift (M : X.Modules) (B : CommMon X.Modules) (u : M ⟶ B.X) :
    (sheafSymmetricAlgebraData M).Hom (GradedCommMonData.const B) where
  hom n :=
    ((TauCeti.SheafOfModules.sheafificationForgetAdjunction X.sheaf).homEquiv
      ((PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj M.val) B.X).symm
      (presheafSymmetricAlgebraLiftHom M B u n)
  one_hom := sheafSymmetricAlgebraLift_one_hom M B u
  mul_hom i j k h := sheafSymmetricAlgebraLift_mul_hom M B u i j k h

lemma sheafSymmetricAlgebraLift_degree_one (M : X.Modules) (B : CommMon X.Modules)
    (u : M ⟶ B.X) :
    (sheafSymmetricAlgebraDegreeOneIso M).inv ≫ (sheafSymmetricAlgebraLift M B u).hom 1 = u := by
  let P : PresheafOfModulesOfCommRing.{u} X.presheaf := M.val
  let G : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
    _root_.SheafOfModules.forget (ringCatSheaf X.sheaf)
  let adj : sheafifyModules X ⊣ G :=
    TauCeti.SheafOfModules.sheafificationForgetAdjunction X.sheaf
  let f₁ : (PresheafOfModulesOfCommRing.symmetricPower 1).obj P ⟶ P :=
    (PresheafOfModulesOfCommRing.symmetricPowerOneIso X.presheaf).hom.app P
  refine (Iso.inv_comp_eq (sheafSymmetricAlgebraDegreeOneIso M)).mpr ?_
  have hdeg : (sheafSymmetricAlgebraDegreeOneIso M).hom = (adj.homEquiv _ M).symm f₁ :=
    (congrArg ((SheafOfModules.symmetricPowerIso (R := X.sheaf) 1 M).inv ≫ ·)
      (SheafOfModules.symmetricPowerOneIso_hom_app (R := X.sheaf) M)).trans
      ((Iso.inv_hom_id_assoc (SheafOfModules.symmetricPowerIso (R := X.sheaf) 1 M) _).trans
        ((congrArg ((sheafifyModules X).map f₁ ≫ ·)
          (TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app X.sheaf M).symm).trans
          (adj.homEquiv_counit _ _ f₁).symm))
  have h_presheaf : presheafSymmetricAlgebraLiftHom M B u 1 = f₁ ≫ G.map u := by
    ext1 U
    exact ((Iso.inv_comp_eq (ModuleCat.symmetricPower.iso₁ (P.obj U))).mp
      (iso₁_inv_moduleSymmetricAlgebraLift_hom_one (P.obj U) (B.sectionsCommMon U.unop)
        (u.val.app' U))).trans
      (congrArg (· ≫ u.val.app' U)
        (PresheafOfModulesOfCommRing.symmetricPowerOneIso_hom_app_app P U).symm)
  exact (congrArg (adj.homEquiv _ B.X).symm h_presheaf).trans
    ((adj.homEquiv_naturality_right_symm f₁ u).trans
      (congrArg (· ≫ u) hdeg.symm))

/-- Universal property of the symmetric algebra of `M : X.Modules`: commutative `𝒪_X`-algebra
morphisms `Sym(M) ⟶ B` correspond bijectively to module morphisms `M ⟶ B.X`. -/
@[expose]
def symmetricAlgebraCommMonHomEquiv (M : X.Modules) (B : CommMon X.Modules) :
    ((GradedObject.total ℕ X.Modules).mapCommMon.obj (sheafSymmetricAlgebraData M).toCommMonObj ⟶
      B) ≃ (M ⟶ B.X) where
  toFun φ :=
    (sheafSymmetricAlgebraDegreeOneIso M).inv ≫
      Sigma.ι (sheafSymmetricAlgebraData M).X 1 ≫ φ.hom.hom
  invFun u :=
    (GradedCommMonData.totalToCommMonHomEquiv (sheafSymmetricAlgebraData M) B).symm
      (sheafSymmetricAlgebraLift M B u)
  left_inv φ := by
    apply (GradedCommMonData.totalToCommMonHomEquiv (sheafSymmetricAlgebraData M) B).injective
    rw [Equiv.apply_symm_apply]
    refine GradedCommMonData.hom_ext_of_degree_one
      (@IsIso.epi_of_iso _ _ _ _ _ (isIso_sheafSymmetricAlgebraData_one₀ M))
      (epi_sheafSymmetricAlgebraData_mul_succ M) ?_
    exact ((Iso.inv_comp_eq (sheafSymmetricAlgebraDegreeOneIso M)).mp
      (sheafSymmetricAlgebraLift_degree_one M B _)).trans
      (Iso.hom_inv_id_assoc (sheafSymmetricAlgebraDegreeOneIso M) _)
  right_inv u :=
    (congrArg ((sheafSymmetricAlgebraDegreeOneIso M).inv ≫ ·)
      (congrArg (fun h ↦ h.hom 1)
        (Equiv.apply_symm_apply
          (GradedCommMonData.totalToCommMonHomEquiv (sheafSymmetricAlgebraData M) B)
          (sheafSymmetricAlgebraLift M B u)))).trans
      (sheafSymmetricAlgebraLift_degree_one M B u)

@[simp]
lemma symmetricAlgebraCommMonHomEquiv_apply (M : X.Modules) (B : CommMon X.Modules)
    (φ : (GradedObject.total ℕ X.Modules).mapCommMon.obj
      (sheafSymmetricAlgebraData M).toCommMonObj ⟶ B) :
    symmetricAlgebraCommMonHomEquiv M B φ =
      (sheafSymmetricAlgebraDegreeOneIso M).inv ≫
        Sigma.ι (sheafSymmetricAlgebraData M).X 1 ≫ φ.hom.hom :=
  (rfl)

lemma symmetricAlgebraCommMonHomEquiv_postcomp (M : X.Modules) {B B' : CommMon X.Modules}
    (φ : (GradedObject.total ℕ X.Modules).mapCommMon.obj
      (sheafSymmetricAlgebraData M).toCommMonObj ⟶ B)
    (ψ : B ⟶ B') :
    symmetricAlgebraCommMonHomEquiv M B' (φ ≫ ψ) =
      symmetricAlgebraCommMonHomEquiv M B φ ≫ ψ.hom.hom :=
  (congrArg ((sheafSymmetricAlgebraDegreeOneIso M).inv ≫ ·)
    (assoc (Sigma.ι (sheafSymmetricAlgebraData M).X 1) φ.hom.hom ψ.hom.hom).symm).trans
    (assoc (sheafSymmetricAlgebraDegreeOneIso M).inv _ ψ.hom.hom).symm

lemma symmetricAlgebraCommMonHomEquiv_precomp {F₁ F₂ : QuasicoherentSheaf X} (f : F₁ ⟶ F₂)
    (B : CommMon X.Modules)
    (φ : ((symmetricAlgebra X).obj F₂).obj ⟶ B) :
    symmetricAlgebraCommMonHomEquiv F₁.obj B (((symmetricAlgebra X).map f).hom ≫ φ) =
      f.hom ≫ symmetricAlgebraCommMonHomEquiv F₂.obj B φ := by
  have h1 : Sigma.ι (sheafSymmetricAlgebraData F₁.obj).X 1 ≫
      ((GradedObject.total ℕ X.Modules).map (sheafSymmetricAlgebraHom f.hom).hom ≫ φ.hom.hom) =
      (sheafSymmetricAlgebraHom f.hom).hom 1 ≫
        Sigma.ι (sheafSymmetricAlgebraData F₂.obj).X 1 ≫ φ.hom.hom :=
    (assoc _ _ _).symm.trans
      (Sigma.ι_map_assoc (sheafSymmetricAlgebraHom f.hom).hom 1 φ.hom.hom)
  have h2 : (sheafSymmetricAlgebraDegreeOneIso F₁.obj).inv ≫
      (sheafSymmetricAlgebraHom f.hom).hom 1 =
      f.hom ≫ (sheafSymmetricAlgebraDegreeOneIso F₂.obj).inv :=
    (Iso.inv_comp_eq (sheafSymmetricAlgebraDegreeOneIso F₁.obj)).mpr
      (((Iso.comp_inv_eq (sheafSymmetricAlgebraDegreeOneIso F₂.obj)).mpr
        (sheafSymmetricAlgebraDegreeOneIso_hom_naturality f.hom).symm).symm.trans
        (assoc _ _ _))
  exact (congrArg ((sheafSymmetricAlgebraDegreeOneIso F₁.obj).inv ≫ ·) h1).trans
    ((assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h2).trans (assoc _ _ _)))

end SheafLift

end AlgebraicGeometry

end

end TauCeti
