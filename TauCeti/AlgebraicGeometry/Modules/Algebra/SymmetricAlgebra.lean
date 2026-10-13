/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GradedObject.TotalMonoidal
public import TauCeti.AlgebraicGeometry.Modules.Algebra.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Affine
public import TauCeti.AlgebraicGeometry.VectorBundle.SymmetricPower.Pullback

/-!
# Graded quasi-coherent algebras and the symmetric algebra of a quasi-coherent sheaf

For a scheme `X`, we define:
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra X`: `ℕ`-graded commutative `𝒪_X`-algebras
  whose graded pieces are quasi-coherent `𝒪_X`-modules;
* `TauCeti.AlgebraicGeometry.gradedAlgebraForget X`: totalization `⨁_{n : ℕ} A_n` from graded
  quasi-coherent algebras to quasi-coherent commutative `𝒪_X`-algebras;
* `TauCeti.AlgebraicGeometry.gradedAlgebraDegreeOne X`: the degree-`1` piece functor to
  `QuasicoherentSheaf X`;
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebra X` and
  `TauCeti.AlgebraicGeometry.symmetricAlgebra X`: the graded and ungraded symmetric algebra functors
  on `QuasicoherentSheaf X`;
* `TauCeti.AlgebraicGeometry.FreeGradedQuasicoherentAlgebra X` and
  `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraEquiv X`: the full subcategory of free graded
  quasi-coherent `𝒪_X`-algebras and its equivalence with `QuasicoherentSheaf X`.
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

section Quasicoherence

private theorem isQuasicoherent_sigmaObj_spec {R : CommRingCat.{u}}
    (f : ℕ → (Spec R).Modules) [∀ n, (f n).IsQuasicoherent] :
    (∐ f).IsQuasicoherent := by
  let F : ModuleCat.{u} R ⥤ (Spec R).Modules := tilde.functor R
  have : PreservesColimitsOfSize.{0, 0} F :=
    (tilde.adjunction (R := R)).leftAdjoint_preservesColimits
  let g : ℕ → ModuleCat.{u} R := fun n ↦ (moduleSpecΓFunctor (R := R)).obj (f n)
  let e : F.obj (∐ g) ≅ ∐ f :=
    PreservesCoproduct.iso F g ≪≫
      Sigma.mapIso fun n ↦
        @asIso _ _ _ _ (f n).fromTildeΓ
          (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) (f n))
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance

private theorem isQuasicoherent_sigmaObj_affine {X : Scheme.{u}} [IsAffine X]
    (f : ℕ → X.Modules) [∀ n, (f n).IsQuasicoherent] :
    (∐ f).IsQuasicoherent := by
  let G := Scheme.Modules.restrictFunctor X.isoSpec.inv
  have : PreservesColimitsOfSize.{0, 0} G :=
    (Scheme.Modules.restrictAdjunction X.isoSpec.inv).leftAdjoint_preservesColimits
  have : (G.obj (∐ f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesCoproduct.iso G f).symm
      (isQuasicoherent_sigmaObj_spec fun n ↦ G.obj (f n))
  exact isQuasicoherent_of_isQuasicoherent_restrict_iso X.isoSpec (∐ f)

/-- A countable coproduct of quasi-coherent modules on a scheme is quasi-coherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigmaObj
    {X : Scheme.{u}} (f : ℕ → X.Modules) [∀ n, (f n).IsQuasicoherent] :
    (∐ f).IsQuasicoherent := by
  refine isQuasicoherent_of_isQuasicoherent_restrict_affineOpens (∐ f) fun U ↦ ?_
  let G := Scheme.Modules.restrictFunctor U.1.ι
  have : PreservesColimitsOfSize.{0, 0} G :=
    (Scheme.Modules.restrictAdjunction U.1.ι).leftAdjoint_preservesColimits
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (PreservesCoproduct.iso G f).symm
    (isQuasicoherent_sigmaObj_affine fun n ↦ G.obj (f n))

/-- Restriction along an open immersion commutes with symmetric powers of sheaves of modules. -/
def restrictSymmetricPowerIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor j).obj ((SheafOfModules.symmetricPower X.sheaf n).obj M) ≅
      (SheafOfModules.symmetricPower U.sheaf n).obj ((Scheme.Modules.restrictFunctor j).obj M) :=
  have := Scheme.Modules.isIso_pullbackSymmetricPowerComparison_of_isOpenImmersion j n M
  (Scheme.Modules.restrictFunctorIsoPullback j).app
      ((SheafOfModules.symmetricPower X.sheaf n).obj M) ≪≫
    asIso ((Scheme.Modules.pullbackSymmetricPowerComparison j n).app M) ≪≫
    (SheafOfModules.symmetricPower U.sheaf n).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app M)

private theorem isQuasicoherent_symmetricPower_spec {R : CommRingCat.{u}}
    (n : ℕ) (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((SheafOfModules.symmetricPower (Spec R).sheaf n).obj M).IsQuasicoherent := by
  let e : tilde (((moduleSpecΓFunctor (R := R)).obj M).symmetricPower n) ≅
      (SheafOfModules.symmetricPower (Spec R).sheaf n).obj M :=
    tildeSymmetricPowerIso n ((moduleSpecΓFunctor (R := R)).obj M) ≪≫
      (SheafOfModules.symmetricPower (Spec R).sheaf n).mapIso
        (@asIso _ _ _ _ M.fromTildeΓ
          (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M))
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance

private theorem isQuasicoherent_symmetricPower_affine {X : Scheme.{u}} [IsAffine X]
    (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    ((SheafOfModules.symmetricPower X.sheaf n).obj M).IsQuasicoherent := by
  let N : X.Modules := (SheafOfModules.symmetricPower X.sheaf n).obj M
  have : (N.restrict X.isoSpec.inv).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (restrictSymmetricPowerIso X.isoSpec.inv n M).symm
      (isQuasicoherent_symmetricPower_spec n (M.restrict X.isoSpec.inv))
  exact isQuasicoherent_of_isQuasicoherent_restrict_iso X.isoSpec N

/-- The `n`-th symmetric power of a quasi-coherent module on a scheme is quasi-coherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricPower
    {X : Scheme.{u}} (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    ((SheafOfModules.symmetricPower X.sheaf n).obj M).IsQuasicoherent := by
  refine isQuasicoherent_of_isQuasicoherent_restrict_affineOpens
    ((SheafOfModules.symmetricPower X.sheaf n).obj M) fun U ↦ ?_
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (restrictSymmetricPowerIso U.1.ι n M).symm
    (isQuasicoherent_symmetricPower_affine n (M.restrict U.1.ι))

end Quasicoherence

section GradedSymmetricAlgebraData

section ModuleCat

variable {R : Type u} [CommRing R]

/-- Homogeneous multiplication `M.symmetricPower i ⊗ M.symmetricPower j ⟶ M.symmetricPower k`
for `i + j = k`. -/
@[expose]
def symmetricPowerMul (M : ModuleCat.{u} R) (i j k : ℕ) (h : i + j = k) :
    M.symmetricPower i ⊗ M.symmetricPower j ⟶ M.symmetricPower k :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun (x : M.symmetricPower i) (y : M.symmetricPower j) ↦
      (⟨x.1 * y.1, h ▸ SetLike.mul_mem_graded x.2 y.2⟩ : M.symmetricPower k))
    (fun x₁ x₂ y ↦ Subtype.ext (add_mul x₁.1 x₂.1 y.1))
    (fun r x y ↦ Subtype.ext (smul_mul_assoc r x.1 y.1))
    (fun x y₁ y₂ ↦ Subtype.ext (mul_add x.1 y₁.1 y₂.1))
    (fun r x y ↦ Subtype.ext (mul_smul_comm r x.1 y.1))

@[simp]
lemma coe_symmetricPowerMul_tmul (M : ModuleCat.{u} R) (i j k : ℕ) (h : i + j = k)
    (x : M.symmetricPower i) (y : M.symmetricPower j) :
    Subtype.val (symmetricPowerMul M i j k h (x ⊗ₜ[R] y)) = x.1 * y.1 :=
  rfl

lemma surjective_symmetricPowerMul (M : ModuleCat.{u} R) (n : ℕ) :
    Function.Surjective (symmetricPowerMul M n 1 (n + 1) rfl) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro z _
  have hz : z.1 ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n *
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R M 1 := by
    rw [TauCeti.SymmetricAlgebra.homogeneousSubmodule,
      TauCeti.SymmetricAlgebra.homogeneousSubmodule, pow_one, ← pow_succ]
    exact z.2
  suffices z.1 ∈ (LinearMap.range (symmetricPowerMul M n 1 (n + 1) rfl).hom).map
      (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M (n + 1)).subtype by
    rcases this with ⟨w, hw, hwz⟩
    exact Subtype.ext hwz ▸ hw
  refine Submodule.mul_le.mpr (fun x hx y hy ↦ ?_) hz
  exact ⟨symmetricPowerMul M n 1 (n + 1) rfl (⟨x, hx⟩ ⊗ₜ[R] ⟨y, hy⟩),
    ⟨⟨x, hx⟩ ⊗ₜ[R] ⟨y, hy⟩, rfl⟩, rfl⟩

/-- Componentwise graded commutative monoid data of symmetric powers of `M : ModuleCat.{u} R`. -/
@[expose]
def moduleSymmetricAlgebraData (M : ModuleCat.{u} R) : GradedCommMonData (ModuleCat.{u} R) where
  X n := M.symmetricPower n
  one₀ := (ModuleCat.symmetricPower.iso₀ M).inv
  mul i j k h := symmetricPowerMul M i j k h
  one_mul k := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro r x
    apply Subtype.ext
    change Subtype.val (symmetricPowerMul M 0 k k (zero_add k)
      ((ModuleCat.symmetricPower.iso₀ M).inv r ⊗ₜ[R] x)) = (r • x).1
    rw [coe_symmetricPowerMul_tmul, ModuleCat.symmetricPower.coe_iso₀_inv_apply,
      ← Algebra.smul_def]
    rfl
  mul_one k := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x r
    apply Subtype.ext
    change Subtype.val (symmetricPowerMul M k 0 k (add_zero k)
      (x ⊗ₜ[R] (ModuleCat.symmetricPower.iso₀ M).inv r)) = (r • x).1
    rw [coe_symmetricPowerMul_tmul, ModuleCat.symmetricPower.coe_iso₀_inv_apply,
      mul_comm, ← Algebra.smul_def]
    rfl
  mul_assoc i₁ i₂ i₃ k h := by
    apply ModuleCat.MonoidalCategory.tensor_ext₃'
    intro x y z
    apply Subtype.ext
    exact mul_assoc x.1 y.1 z.1
  mul_comm i j k h := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    apply Subtype.ext
    exact mul_comm y.1 x.1

/-- Morphism of componentwise graded symmetric algebra data induced by `f : M ⟶ N`. -/
@[expose]
def moduleSymmetricAlgebraHom {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (moduleSymmetricAlgebraData M).Hom (moduleSymmetricAlgebraData N) where
  hom n := ModuleCat.symmetricPower.map f n
  one_hom := by
    dsimp [moduleSymmetricAlgebraData]
    rw [Iso.inv_comp_eq, ← ModuleCat.symmetricPower.iso₀_hom_naturality f,
      assoc, Iso.hom_inv_id, comp_id]
  mul_hom i j k h := by
    dsimp [moduleSymmetricAlgebraData]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    apply Subtype.ext
    change Subtype.val (symmetricPowerMul N i j k h
      (ModuleCat.symmetricPower.map f i x ⊗ₜ[R] ModuleCat.symmetricPower.map f j y)) =
      Subtype.val (ModuleCat.symmetricPower.map f k (symmetricPowerMul M i j k h (x ⊗ₜ[R] y)))
    rw [coe_symmetricPowerMul_tmul, ModuleCat.symmetricPower.coe_map_apply,
      ModuleCat.symmetricPower.coe_map_apply, ModuleCat.symmetricPower.coe_map_apply,
      coe_symmetricPowerMul_tmul, map_mul]

end ModuleCat

section Presheaf

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The degree-zero unit morphism `R ⟶ Sym^0(P)` for a presheaf of modules, defined sectionwise
by `(ModuleCat.symmetricPower.iso₀ (P.obj U)).inv`. -/
@[expose]
def presheafSymmetricPowerOne₀ (P : PresheafOfModulesOfCommRing.{u} R) :
    𝟙_ (PresheafOfModulesOfCommRing.{u} R) ⟶
      (PresheafOfModulesOfCommRing.symmetricPower 0).obj P :=
  PresheafOfModulesOfCommRing.homMk
    (fun U ↦ (ModuleCat.symmetricPower.iso₀ (P.obj U)).inv)
    (fun {_ _} f ↦ by
      have h := ((PresheafOfModulesOfCommRing.symmetricPowerZeroIso R).inv.app P).naturality f
      rwa [PresheafOfModulesOfCommRing.symmetricPowerZeroIso_inv_app_app,
        PresheafOfModulesOfCommRing.symmetricPowerZeroIso_inv_app_app] at h)

lemma presheafSymmetricPowerOne₀_eq (P : PresheafOfModulesOfCommRing.{u} R) :
    presheafSymmetricPowerOne₀ P =
      (PresheafOfModulesOfCommRing.symmetricPowerZeroIso R).inv.app P := by
  ext1 U
  exact (PresheafOfModulesOfCommRing.symmetricPowerZeroIso_inv_app_app P U).symm

/-- Sectionwise homogeneous multiplication on symmetric powers of a presheaf of modules. -/
@[expose]
def presheafSymmetricPowerMul (P : PresheafOfModulesOfCommRing.{u} R)
    (i j k : ℕ) (h : i + j = k) :
    (PresheafOfModulesOfCommRing.symmetricPower i).obj P ⊗
      (PresheafOfModulesOfCommRing.symmetricPower j).obj P ⟶
        (PresheafOfModulesOfCommRing.symmetricPower k).obj P :=
  PresheafOfModulesOfCommRing.homMk
    (fun U ↦ symmetricPowerMul (P.obj U) i j k h)
    (fun {U V} f ↦ ModuleCat.MonoidalCategory.tensor_ext fun x y ↦ Subtype.ext <|
      (coe_symmetricPowerMul_tmul (P.obj V) i j k h
        (((PresheafOfModulesOfCommRing.symmetricPower i).obj P).map f x)
        (((PresheafOfModulesOfCommRing.symmetricPower j).obj P).map f y)).trans <|
      (congrArg₂ (· * ·)
        (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply i P f x)
        (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply j P f y)).trans <|
      (map_mul _ x.1 y.1).symm.trans
        (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply k P f
          (symmetricPowerMul (P.obj U) i j k h (x ⊗ₜ[R.obj U] y))).symm)

instance epi_presheafSymmetricPowerMul (P : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) :
    Epi (presheafSymmetricPowerMul P n 1 (n + 1) rfl) where
  left_cancellation g₁ g₂ h := by
    ext U z
    obtain ⟨t, rfl⟩ := surjective_symmetricPowerMul (P.obj U) n z
    exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U) h) t

/-- Componentwise graded symmetric algebra data of a presheaf of modules. -/
@[expose]
def presheafSymmetricAlgebraData (P : PresheafOfModulesOfCommRing.{u} R) :
    GradedCommMonData (PresheafOfModulesOfCommRing.{u} R) where
  X n := (PresheafOfModulesOfCommRing.symmetricPower n).obj P
  one₀ := presheafSymmetricPowerOne₀ P
  mul i j k h := presheafSymmetricPowerMul P i j k h
  one_mul k := by
    ext1 U
    exact (moduleSymmetricAlgebraData (P.obj U)).one_mul k
  mul_one k := by
    ext1 U
    exact (moduleSymmetricAlgebraData (P.obj U)).mul_one k
  mul_assoc i₁ i₂ i₃ k h := by
    ext1 U
    exact (moduleSymmetricAlgebraData (P.obj U)).mul_assoc i₁ i₂ i₃ k h
  mul_comm i j k h := by
    ext1 U
    exact (moduleSymmetricAlgebraData (P.obj U)).mul_comm i j k h

/-- Morphism of presheaf graded symmetric algebra data induced by `φ : P ⟶ Q`. -/
@[expose]
def presheafSymmetricAlgebraHom {P Q : PresheafOfModulesOfCommRing.{u} R} (φ : P ⟶ Q) :
    (presheafSymmetricAlgebraData P).Hom (presheafSymmetricAlgebraData Q) where
  hom n := (PresheafOfModulesOfCommRing.symmetricPower n).map φ
  one_hom := by
    ext1 U
    exact (moduleSymmetricAlgebraHom (φ.app' U)).one_hom
  mul_hom i j k h := by
    ext1 U
    exact (moduleSymmetricAlgebraHom (φ.app' U)).mul_hom i j k h

end Presheaf

section Sheaf

open TauCeti.SheafOfModules (ringCatSheaf)

variable {X : Scheme.{u}}

/-- Sheafification of presheaves of modules on `X`, with domain
`PresheafOfModulesOfCommRing.{u} X.presheaf` and codomain `X.Modules`. -/
@[expose]
def sheafifyModules (X : Scheme.{u}) :
    PresheafOfModulesOfCommRing.{u} X.presheaf ⥤ X.Modules :=
  PresheafOfModules.sheafification.{u} (R₀ := (ringCatSheaf X.sheaf).obj)
    (R := ringCatSheaf X.sheaf) (𝟙 (ringCatSheaf X.sheaf).obj)

instance sheafifyModulesBraided (X : Scheme.{u}) :
    (sheafifyModules X).Braided :=
  TauCeti.SheafOfModules.sheafificationBraided X.sheaf

instance sheafifyModulesIsLeftAdjoint (X : Scheme.{u}) :
    (sheafifyModules X).IsLeftAdjoint :=
  (TauCeti.SheafOfModules.sheafificationForgetAdjunction X.sheaf).isLeftAdjoint

/-- Componentwise graded symmetric algebra data of `M : X.Modules`, obtained by pushing forward
`presheafSymmetricAlgebraData M.val` along the braided monoidal sheafification functor. -/
@[expose]
def sheafSymmetricAlgebraData (M : X.Modules) :
    GradedCommMonData X.Modules :=
  (presheafSymmetricAlgebraData (R := X.presheaf) M.val).mapObj (sheafifyModules X)

/-- Morphism of componentwise graded symmetric algebra data induced by `φ : M ⟶ N`. -/
@[expose]
def sheafSymmetricAlgebraHom {M N : X.Modules} (φ : M ⟶ N) :
    (sheafSymmetricAlgebraData M).Hom (sheafSymmetricAlgebraData N) :=
  GradedCommMonData.mapHom (sheafifyModules X) (presheafSymmetricAlgebraHom (R := X.presheaf) φ.val)

@[simp]
lemma sheafSymmetricAlgebraHom_id (M : X.Modules) (n : ℕ) :
    (sheafSymmetricAlgebraHom (𝟙 M)).hom n = 𝟙 ((sheafSymmetricAlgebraData M).X n) :=
  (congrArg (sheafifyModules X).map
    ((PresheafOfModulesOfCommRing.symmetricPower n).map_id M.val)).trans
    ((sheafifyModules X).map_id _)

@[simp]
lemma sheafSymmetricAlgebraHom_comp
    {M₁ M₂ M₃ : X.Modules} (φ : M₁ ⟶ M₂) (ψ : M₂ ⟶ M₃) (n : ℕ) :
    (sheafSymmetricAlgebraHom (φ ≫ ψ)).hom n =
      (sheafSymmetricAlgebraHom φ).hom n ≫ (sheafSymmetricAlgebraHom ψ).hom n :=
  (congrArg (sheafifyModules X).map
    ((PresheafOfModulesOfCommRing.symmetricPower n).map_comp φ.val ψ.val)).trans
    ((sheafifyModules X).map_comp _ _)

/-- The degree-`1` piece of `sheafSymmetricAlgebraData M` is canonically isomorphic to `M`. -/
def sheafSymmetricAlgebraDegreeOneIso (M : X.Modules) :
    (sheafSymmetricAlgebraData M).X 1 ≅ M :=
  (SheafOfModules.symmetricPowerIso (R := X.sheaf) 1 M).symm ≪≫
    (SheafOfModules.symmetricPowerOneIso X.sheaf).app M

@[reassoc]
lemma sheafSymmetricAlgebraDegreeOneIso_hom_naturality
    {M N : X.Modules} (φ : M ⟶ N) :
    (sheafSymmetricAlgebraHom φ).hom 1 ≫ (sheafSymmetricAlgebraDegreeOneIso N).hom =
      (sheafSymmetricAlgebraDegreeOneIso M).hom ≫ φ := by
  let iM := SheafOfModules.symmetricPowerIso (R := X.sheaf) 1 M
  let uM := (SheafOfModules.symmetricPowerOneIso X.sheaf).hom.app M
  let uN := (SheafOfModules.symmetricPowerOneIso X.sheaf).hom.app N
  have h1 := SheafOfModules.symmetricPower_map (R := X.sheaf) 1 φ
  have h2 := (SheafOfModules.symmetricPowerOneIso X.sheaf).hom.naturality φ
  have lhs_eq : iM.hom ≫ (sheafSymmetricAlgebraHom φ).hom 1 ≫
      (sheafSymmetricAlgebraDegreeOneIso N).hom =
      (SheafOfModules.symmetricPower X.sheaf 1).map φ ≫ uN :=
    ((reassoc_of% h1) uN).symm
  have rhs_eq : iM.hom ≫ (sheafSymmetricAlgebraDegreeOneIso M).hom ≫ φ = uM ≫ φ :=
    (congrArg (iM.hom ≫ ·) (assoc iM.inv uM φ)).trans
      (Iso.hom_inv_id_assoc iM (uM ≫ φ))
  exact (cancel_epi iM.hom).1 (lhs_eq.trans (h2.trans rhs_eq.symm))

instance isIso_sheafSymmetricAlgebraData_one₀ (M : X.Modules) :
    IsIso (sheafSymmetricAlgebraData M).one₀ := by
  let P : PresheafOfModulesOfCommRing.{u} X.presheaf := M.val
  let e : 𝟙_ X.Modules ≅ (sheafSymmetricAlgebraData M).X 0 :=
    Functor.Monoidal.εIso (sheafifyModules X) ≪≫
      ((sheafifyModules X).mapIso
        ((PresheafOfModulesOfCommRing.symmetricPowerZeroIso X.presheaf).app P)).symm
  have h : (sheafSymmetricAlgebraData M).one₀ = e.hom :=
    congrArg (Functor.LaxMonoidal.ε (sheafifyModules X) ≫ (sheafifyModules X).map ·)
      (presheafSymmetricPowerOne₀_eq P)
  exact h ▸ e.isIso_hom

instance epi_sheafSymmetricAlgebraData_mul_succ (M : X.Modules) (n : ℕ) :
    Epi ((sheafSymmetricAlgebraData M).mul n 1 (n + 1) rfl) := by
  let P : PresheafOfModulesOfCommRing.{u} X.presheaf := M.val
  let e := Functor.Monoidal.μIso (sheafifyModules X)
    ((PresheafOfModulesOfCommRing.symmetricPower n).obj P)
    ((PresheafOfModulesOfCommRing.symmetricPower 1).obj P)
  have h₁ : Epi e.hom := inferInstance
  have h₂ : Epi ((sheafifyModules X).map (presheafSymmetricPowerMul P n 1 (n + 1) rfl)) :=
    Functor.map_epi (sheafifyModules X) (presheafSymmetricPowerMul P n 1 (n + 1) rfl)
  exact @epi_comp _ _ _ _ _ e.hom h₁
    ((sheafifyModules X).map (presheafSymmetricPowerMul P n 1 (n + 1) rfl)) h₂

end Sheaf

section Ext

variable {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasCoproducts.{0} C] [HasInitial C]

/-- If `d₁` is generated in degree `1` (in the sense that `d₁.one₀` and
`d₁.mul n 1 (n + 1) rfl` are epimorphisms), two morphisms `d₁.toCommMonObj ⟶ d₂.toCommMonObj`
agreeing in degree `1` are equal. -/
private lemma toCommMonObj_hom_ext {d₁ d₂ : GradedCommMonData C}
    (h_one : Epi d₁.one₀) (h_mul : ∀ n, Epi (d₁.mul n 1 (n + 1) rfl))
    {g₁ g₂ : d₁.toCommMonObj ⟶ d₂.toCommMonObj}
    (h1 : g₁.hom.hom 1 = g₂.hom.hom 1) : g₁ = g₂ := by
  let : MonObj d₁.X := d₁.toMonObj
  let : MonObj d₂.X := d₂.toMonObj
  have h0 : ∀ (f : d₁.X ⟶ d₂.X) [IsMonHom f], d₁.one₀ ≫ f 0 = d₂.one₀ := by
    intro f _
    have hf := congrFun (IsMonHom.one_hom (f := f)) 0
    have hf' := congrArg (GradedObject.Monoidal.tensorUnit₀.inv ≫ ·) hf
    change GradedObject.Monoidal.tensorUnit₀.inv ≫ d₁.toGradedOne 0 ≫ f 0 =
      GradedObject.Monoidal.tensorUnit₀.inv ≫ d₂.toGradedOne 0 at hf'
    simpa only [GradedCommMonData.tensorUnit₀_inv_toGradedOne_zero_assoc,
      GradedCommMonData.tensorUnit₀_inv_toGradedOne_zero] using hf'
  have hmul : ∀ (f : d₁.X ⟶ d₂.X) [IsMonHom f] (n : ℕ),
      d₁.mul n 1 (n + 1) rfl ≫ f (n + 1) =
        (f n ⊗ₘ f 1) ≫ d₂.mul n 1 (n + 1) rfl := by
    intro f _ n
    have hf := congrFun (IsMonHom.mul_hom (f := f)) (n + 1)
    have hf' := congrArg (GradedObject.Monoidal.ιTensorObj d₁.X d₁.X n 1 (n + 1) rfl ≫ ·) hf
    change GradedObject.Monoidal.ιTensorObj d₁.X d₁.X n 1 (n + 1) rfl ≫
        d₁.toGradedMul (n + 1) ≫ f (n + 1) =
      GradedObject.Monoidal.ιTensorObj d₁.X d₁.X n 1 (n + 1) rfl ≫
        GradedObject.Monoidal.tensorHom f f (n + 1) ≫
          d₂.toGradedMul (n + 1) at hf'
    simpa only [GradedCommMonData.ι_toGradedMul_assoc,
      GradedObject.Monoidal.ι_tensorHom_assoc, GradedCommMonData.ι_toGradedMul] using hf'
  let f₁ : d₁.X ⟶ d₂.X := g₁.hom.hom
  let f₂ : d₁.X ⟶ d₂.X := g₂.hom.hom
  have : IsMonHom f₁ := g₁.hom.isMonHom_hom
  have : IsMonHom f₂ := g₂.hom.isMonHom_hom
  have h1' : f₁ 1 = f₂ 1 := h1
  ext1
  change f₁ = f₂
  funext n
  induction n with
  | zero => rw [← cancel_epi d₁.one₀, h0 f₁, h0 f₂]
  | succ n ih =>
      have := h_mul n
      rw [← cancel_epi (d₁.mul n 1 (n + 1) rfl), hmul f₁ n, hmul f₂ n, ih, h1']

end Ext

end GradedSymmetricAlgebraData

section Functors

/-- An `ℕ`-graded commutative `𝒪_X`-algebra is quasi-coherent if each of its graded pieces is a
quasi-coherent `𝒪_X`-module. -/
@[expose]
def isGradedQuasicoherentAlgebra (X : Scheme.{u}) :
    ObjectProperty (CommMon (GradedObject ℕ X.Modules)) :=
  fun A ↦ ∀ n, (A.X n).IsQuasicoherent

/-- The category of `ℕ`-graded quasi-coherent commutative `𝒪_X`-algebras. -/
abbrev GradedQuasicoherentAlgebra (X : Scheme.{u}) :=
  (isGradedQuasicoherentAlgebra X).FullSubcategory

/-- Totalization `⨁_{n : ℕ} A_n` of a graded quasi-coherent `𝒪_X`-algebra as a quasi-coherent
commutative `𝒪_X`-algebra. -/
@[expose]
noncomputable def gradedAlgebraForget (X : Scheme.{u}) :
    GradedQuasicoherentAlgebra X ⥤ QuasicoherentAlgebra X where
  obj A :=
    { obj := (GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj
      property := by
        have : ∀ n, (A.obj.X n).IsQuasicoherent := A.property
        exact Scheme.Modules.isQuasicoherent_sigmaObj fun n ↦ A.obj.X n }
  map f := ObjectProperty.homMk ((GradedObject.total ℕ X.Modules).mapCommMon.map f.hom)
  map_id A := by
    ext1
    exact (GradedObject.total ℕ X.Modules).mapCommMon.map_id A.obj
  map_comp f g := by
    ext1
    exact (GradedObject.total ℕ X.Modules).mapCommMon.map_comp f.hom g.hom

/-- The degree-`1` quasi-coherent sheaf of a graded quasi-coherent `𝒪_X`-algebra. -/
@[expose]
noncomputable def gradedAlgebraDegreeOne (X : Scheme.{u}) :
    GradedQuasicoherentAlgebra X ⥤ QuasicoherentSheaf X where
  obj A := ⟨A.obj.X 1, A.property 1⟩
  map f := ObjectProperty.homMk (f.hom.hom.hom 1)

/-- The graded symmetric algebra functor `Sym^*` from quasi-coherent sheaves on `X` to graded
quasi-coherent `𝒪_X`-algebras. -/
@[expose]
noncomputable def gradedSymmetricAlgebra (X : Scheme.{u}) :
    QuasicoherentSheaf X ⥤ GradedQuasicoherentAlgebra X where
  obj F :=
    { obj := (sheafSymmetricAlgebraData F.obj).toCommMonObj
      property := fun n ↦ by
        have : F.obj.IsQuasicoherent := F.property
        exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
          (SheafOfModules.symmetricPowerIso (R := X.sheaf) n F.obj)
          (Scheme.Modules.isQuasicoherent_symmetricPower n F.obj) }
  map f := ObjectProperty.homMk (GradedCommMonData.toCommMonHom (sheafSymmetricAlgebraHom f.hom))
  map_id F := by
    ext1
    ext1
    funext n
    exact sheafSymmetricAlgebraHom_id F.obj n
  map_comp f g := by
    ext1
    ext1
    funext n
    exact sheafSymmetricAlgebraHom_comp f.hom g.hom n

/-- The symmetric algebra functor `Sym` from quasi-coherent sheaves on `X` to quasi-coherent
commutative `𝒪_X`-algebras. -/
@[expose]
noncomputable def symmetricAlgebra (X : Scheme.{u}) :
    QuasicoherentSheaf X ⥤ QuasicoherentAlgebra X :=
  gradedSymmetricAlgebra X ⋙ gradedAlgebraForget X

/-- Forgetting the grading on the graded symmetric algebra recovers the symmetric algebra. -/
@[expose]
noncomputable def gradedSymmetricAlgebraForgetIso (X : Scheme.{u}) :
    gradedSymmetricAlgebra X ⋙ gradedAlgebraForget X ≅ symmetricAlgebra X :=
  Iso.refl _

/-- The degree-`1` piece of the graded symmetric algebra of `F` is canonically isomorphic to `F`. -/
@[expose]
noncomputable def gradedSymmetricAlgebraDegreeOneIso {X : Scheme.{u}}
    (F : QuasicoherentSheaf X) :
    (gradedAlgebraDegreeOne X).obj ((gradedSymmetricAlgebra X).obj F) ≅ F :=
  ObjectProperty.isoMk _ (sheafSymmetricAlgebraDegreeOneIso F.obj)

/-- Natural isomorphism `gradedSymmetricAlgebra X ⋙ gradedAlgebraDegreeOne X ≅ 𝟭 _`. -/
@[expose]
noncomputable def gradedSymmetricAlgebraDegreeOneNatIso (X : Scheme.{u}) :
    gradedSymmetricAlgebra X ⋙ gradedAlgebraDegreeOne X ≅ 𝟭 (QuasicoherentSheaf X) :=
  NatIso.ofComponents gradedSymmetricAlgebraDegreeOneIso fun f ↦ by
    ext1
    exact sheafSymmetricAlgebraDegreeOneIso_hom_naturality f.hom

instance faithfulGradedSymmetricAlgebra (X : Scheme.{u}) :
    (gradedSymmetricAlgebra X).Faithful :=
  Functor.Faithful.of_comp_iso (gradedSymmetricAlgebraDegreeOneNatIso X)

private lemma gradedSymmetricAlgebra_hom_eq {X : Scheme.{u}} {E F : QuasicoherentSheaf X}
    (φ : (gradedSymmetricAlgebra X).obj E ⟶ (gradedSymmetricAlgebra X).obj F) :
    let f : E ⟶ F := (gradedSymmetricAlgebraDegreeOneIso E).inv ≫
      (gradedAlgebraDegreeOne X).map φ ≫ (gradedSymmetricAlgebraDegreeOneIso F).hom
    φ = (gradedSymmetricAlgebra X).map f := by
  intro f
  ext1
  refine toCommMonObj_hom_ext
    (@IsIso.epi_of_iso _ _ _ _ _ (isIso_sheafSymmetricAlgebraData_one₀ E.obj))
    (epi_sheafSymmetricAlgebraData_mul_succ E.obj) ?_
  have h1 : (gradedAlgebraDegreeOne X).map ((gradedSymmetricAlgebra X).map f) ≫
      (gradedSymmetricAlgebraDegreeOneIso F).hom =
      (gradedSymmetricAlgebraDegreeOneIso E).hom ≫ f :=
    (gradedSymmetricAlgebraDegreeOneNatIso X).hom.naturality f
  have h2 : (gradedSymmetricAlgebraDegreeOneIso E).hom ≫ f =
      (gradedAlgebraDegreeOne X).map φ ≫ (gradedSymmetricAlgebraDegreeOneIso F).hom :=
    Iso.hom_inv_id_assoc (gradedSymmetricAlgebraDegreeOneIso E)
      ((gradedAlgebraDegreeOne X).map φ ≫ (gradedSymmetricAlgebraDegreeOneIso F).hom)
  exact congrArg InducedCategory.Hom.hom
    ((cancel_mono (gradedSymmetricAlgebraDegreeOneIso F).hom).1 (h2.symm.trans h1.symm))

instance fullGradedSymmetricAlgebra (X : Scheme.{u}) :
    (gradedSymmetricAlgebra X).Full where
  map_surjective φ := ⟨_, (gradedSymmetricAlgebra_hom_eq φ).symm⟩

/-- The full subcategory of free graded quasi-coherent `𝒪_X`-algebras, defined as the essential
image of `gradedSymmetricAlgebra X`. -/
abbrev FreeGradedQuasicoherentAlgebra (X : Scheme.{u}) :=
  (gradedSymmetricAlgebra X).EssImageSubcategory

/-- The forgetful functor from free graded quasi-coherent `𝒪_X`-algebras to all graded
quasi-coherent `𝒪_X`-algebras. -/
@[expose]
noncomputable def freeGradedAlgebraForget (X : Scheme.{u}) :
    FreeGradedQuasicoherentAlgebra X ⥤ GradedQuasicoherentAlgebra X :=
  (gradedSymmetricAlgebra X).essImage.ι

/-- The graded symmetric algebra functor valued in free graded quasi-coherent `𝒪_X`-algebras. -/
@[expose]
noncomputable def gradedSymmetricAlgebraFree (X : Scheme.{u}) :
    QuasicoherentSheaf X ⥤ FreeGradedQuasicoherentAlgebra X :=
  (gradedSymmetricAlgebra X).toEssImage

instance isEquivalenceGradedSymmetricAlgebraFree (X : Scheme.{u}) :
    (gradedSymmetricAlgebraFree X).IsEquivalence :=
  Equivalence.fullyFaithfulToEssImage (gradedSymmetricAlgebra X)

/-- The equivalence between quasi-coherent sheaves on `X` and free graded quasi-coherent
`𝒪_X`-algebras. -/
@[expose]
noncomputable def gradedSymmetricAlgebraEquiv (X : Scheme.{u}) :
    QuasicoherentSheaf X ≌ FreeGradedQuasicoherentAlgebra X :=
  (gradedSymmetricAlgebraFree X).asEquivalence

/-- The forward functor of `gradedSymmetricAlgebraEquiv X` is canonically
`gradedSymmetricAlgebraFree X`. -/
@[expose]
noncomputable def gradedSymmetricAlgebraEquivFunctorIso (X : Scheme.{u}) :
    (gradedSymmetricAlgebraEquiv X).functor ≅ gradedSymmetricAlgebraFree X :=
  Iso.refl _

/-- Recovering a free graded quasi-coherent `𝒪_X`-algebra from its degree-`1` piece. -/
@[expose]
noncomputable def freeGradedAlgebraDegreeOneIso {X : Scheme.{u}}
    (A : FreeGradedQuasicoherentAlgebra X) :
    (gradedSymmetricAlgebraFree X).obj
      ((gradedAlgebraDegreeOne X).obj ((freeGradedAlgebraForget X).obj A)) ≅ A :=
  let eA : (gradedSymmetricAlgebraFree X).obj A.property.witness ≅ A :=
    (gradedSymmetricAlgebra X).essImage.isoMk A.property.getIso
  (gradedSymmetricAlgebraFree X).mapIso
      ((freeGradedAlgebraForget X ⋙ gradedAlgebraDegreeOne X).mapIso eA.symm ≪≫
        gradedSymmetricAlgebraDegreeOneIso A.property.witness) ≪≫
    eA

end Functors

end

end TauCeti.AlgebraicGeometry
