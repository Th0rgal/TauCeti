/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.Pullback
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence

/-!
# The universal property of relative Spec for arbitrary schemes over a base

For a scheme `X`, a quasi-coherent commutative `𝒪ₓ`-algebra `A`, and an arbitrary scheme
`p : T ⟶ X` over `X` (not necessarily affine over `X`), morphisms `T ⟶ Spec_X A` over `X`
correspond bijectively and naturally to:
1. morphisms `A.obj ⟶ p_* 𝒪_T` of commutative `𝒪ₓ`-algebras
   (`TauCeti.AlgebraicGeometry.relativeSpecOverPushforwardHomEquiv`), and
2. morphisms `p^* A ⟶ 𝒪_T` of quasi-coherent commutative `𝒪_T`-algebras
   (`TauCeti.AlgebraicGeometry.relativeSpecOverHomEquiv`).

Geometrically, given an `𝒪ₓ`-algebra morphism `φ : A ⟶ p_* 𝒪_T`, over each affine open `U` of `X`
the composition of the canonical morphism `p⁻¹(U) ⟶ Spec Γ(T, p⁻¹(U))` with `Spec` of the section
map `Γ(A, U) ⟶ Γ(T, p⁻¹(U))` and the open chart `Spec Γ(A, U) ⟶ Spec_X A` glues along the
locally directed pullback cover `((directedCover X).pullback₁ p)` to a global morphism
`p.toRelativeSpec φ : T ⟶ Spec_X A` over `X`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.toRelativeSpec`: the scheme morphism `T ⟶ A.relativeSpec` glued
  from an `𝒪ₓ`-algebra morphism `φ : A ⟶ p.pushforwardStructureAlgebra`.
* `TauCeti.AlgebraicGeometry.affineSchemeOverForget`: the forgetful functor
  `AffineSchemeOver X ⥤ Over X`.
* `TauCeti.AlgebraicGeometry.relativeSpecOverPushforwardHomEquiv`: the natural bijection
  `(T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) ≃
    (A.obj ⟶ T.hom.pushforwardStructureAlgebra)`.
* `TauCeti.AlgebraicGeometry.relativeSpecOverHomEquiv`: the natural bijection
  `(T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) ≃
    ((pullbackQuasicoherentAlgebra T.hom).obj A ⟶ structureSheafAlgebra T.left)`.
* `TauCeti.AlgebraicGeometry.relativeSpecPoints`: the functor of `Over X`-points of
  `relativeSpec X`.
* `TauCeti.AlgebraicGeometry.relativeSpecAlgebraMaps`: the functor of pullback algebra maps into the
  structure sheaf.
* `TauCeti.AlgebraicGeometry.relativeSpecUniversalProperty`: the natural isomorphism
  `relativeSpecPoints X ≅ relativeSpecAlgebraMaps X`.

## References

* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL) and
  [Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, Proposition 1.2.7 and
  §1.3.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace AlgebraicGeometry.Scheme.Hom

universe u

noncomputable section

variable {X T : Scheme.{u}} (p : T ⟶ X)
variable {A : CommMon X.Modules} [A.X.IsQuasicoherent]

/-- Two morphisms out of `T` are equal if they agree on the preimages `p ⁻¹ᵁ U.toOpens` of all
affine opens `U` of `X`. -/
lemma hom_ext_of_preimage_affineZariskiSite {Y : Scheme.{u}} (f₁ f₂ : T ⟶ Y)
    (h : ∀ U : X.AffineZariskiSite,
      (p ⁻¹ᵁ U.toOpens).ι ≫ f₁ = (p ⁻¹ᵁ U.toOpens).ι ≫ f₂) :
    f₁ = f₂ :=
  Scheme.Cover.hom_ext
    (T.openCoverOfIsOpenCover (fun U : X.AffineZariskiSite ↦ p ⁻¹ᵁ U.toOpens)
      (p.iSup_preimage_eq_top (iSup_affineOpens_eq_top X))) f₁ f₂ h

/-- On the affine open `U` of `X`, the ring homomorphism `Γ(A.X, U) ⟶ Γ(T, p⁻¹(U))` associated to
an `𝒪ₓ`-algebra morphism `φ : A ⟶ p_* 𝒪_T`. -/
@[expose]
def toRelativeSpecRingHom (φ : A ⟶ p.pushforwardStructureAlgebra)
    (U : X.AffineZariskiSite) :
    CommRingCat.of Γ(A.X, U.toOpens) ⟶ Γ(T, p ⁻¹ᵁ U.toOpens) :=
  (CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom).app
    (op U.toOpens)

omit [A.X.IsQuasicoherent] in
lemma toRelativeSpecRingHom_naturality (φ : A ⟶ p.pushforwardStructureAlgebra)
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    toRelativeSpecRingHom p φ V ≫
        T.presheaf.map (homOfLE (show p ⁻¹ᵁ U.toOpens ≤ p ⁻¹ᵁ V.toOpens from
          p.preimage_mono ((toOpensFunctor X).map i).le)).op =
      A.sectionsPresheaf.map ((toOpensFunctor X).map i).op ≫
        toRelativeSpecRingHom p φ U :=
  ((CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom).naturality
    ((toOpensFunctor X).map i).op).symm

/-- On each member of the pullback cover `((directedCover X).pullback₁ p)`, the local morphism
to `A.relativeSpec` induced by `φ : A ⟶ p_* 𝒪_T`. -/
@[expose]
def toRelativeSpecChart (φ : A ⟶ p.pushforwardStructureAlgebra)
    (U : X.AffineZariskiSite) :
    ((directedCover X).pullback₁ p).X U ⟶ A.relativeSpec :=
  (pullbackRestrictIsoRestrict p U.toOpens).hom ≫
    (p ⁻¹ᵁ U.toOpens).toSpecΓ ≫
    Spec.map (toRelativeSpecRingHom p φ U) ≫
    A.relativeSpecCover.f U

lemma cover_trans_pullbackRestrictIsoRestrict_hom
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Scheme.Cover.trans ((directedCover X).pullback₁ p) i ≫
      (pullbackRestrictIsoRestrict p V.toOpens).hom =
      (pullbackRestrictIsoRestrict p U.toOpens).hom ≫
        T.homOfLE (show p ⁻¹ᵁ U.toOpens ≤ p ⁻¹ᵁ V.toOpens from
          p.preimage_mono ((toOpensFunctor X).map i).le) := by
  let hle : p ⁻¹ᵁ U.toOpens ≤ p ⁻¹ᵁ V.toOpens :=
    p.preimage_mono ((toOpensFunctor X).map i).le
  apply (cancel_mono (p ⁻¹ᵁ V.toOpens).ι).mp
  have hV : (pullbackRestrictIsoRestrict p V.toOpens).hom ≫ (p ⁻¹ᵁ V.toOpens).ι =
      ((directedCover X).pullback₁ p).f V :=
    pullbackRestrictIsoRestrict_hom_ι p V.toOpens
  have hU : (pullbackRestrictIsoRestrict p U.toOpens).hom ≫ (p ⁻¹ᵁ U.toOpens).ι =
      ((directedCover X).pullback₁ p).f U :=
    pullbackRestrictIsoRestrict_hom_ι p U.toOpens
  exact (Category.assoc _ _ _).trans
    ((congrArg (Scheme.Cover.trans ((directedCover X).pullback₁ p) i ≫ ·) hV).trans
      ((Scheme.Cover.trans_map ((directedCover X).pullback₁ p) i).trans
        (hU.symm.trans
          ((congrArg ((pullbackRestrictIsoRestrict p U.toOpens).hom ≫ ·)
            (T.homOfLE_ι hle).symm).trans
            (Category.assoc _ _ _).symm))))

lemma toRelativeSpecChart_naturality (φ : A ⟶ p.pushforwardStructureAlgebra)
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Scheme.Cover.trans ((directedCover X).pullback₁ p) i ≫ toRelativeSpecChart p φ V =
      toRelativeSpecChart p φ U := by
  let hle : p ⁻¹ᵁ U.toOpens ≤ p ⁻¹ᵁ V.toOpens :=
    p.preimage_mono ((toOpensFunctor X).map i).le
  let ιU : A.relativeSpecGluingData.functor.obj U ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιV : A.relativeSpecGluingData.functor.obj V ⟶ A.relativeSpec := A.relativeSpecCover.f V
  let cU : (p ⁻¹ᵁ U.toOpens).toScheme ⟶ A.relativeSpec :=
    (p ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map (toRelativeSpecRingHom p φ U) ≫ ιU
  let cV : (p ⁻¹ᵁ V.toOpens).toScheme ⟶ A.relativeSpec :=
    (p ⁻¹ᵁ V.toOpens).toSpecΓ ≫ Spec.map (toRelativeSpecRingHom p φ V) ≫ ιV
  have h1 : T.homOfLE hle ≫ (p ⁻¹ᵁ V.toOpens).toSpecΓ =
      (p ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map (T.presheaf.map (homOfLE hle).op) :=
    (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map (p ⁻¹ᵁ U.toOpens) (p ⁻¹ᵁ V.toOpens) hle).symm
  have h2 :
      Spec.map (T.presheaf.map (homOfLE hle).op) ≫ Spec.map (toRelativeSpecRingHom p φ V) =
        Spec.map (toRelativeSpecRingHom p φ U) ≫ A.relativeSpecGluingData.functor.map i := by
    rw [A.relativeSpecGluingData_functor_map]
    exact (Spec.map_comp _ _).symm.trans
      ((congrArg Spec.map (p.toRelativeSpecRingHom_naturality φ i)).trans
        (Spec.map_comp _ _))
  have h3 : A.relativeSpecGluingData.functor.map i ≫ ιV = ιU :=
    colimit.w A.relativeSpecGluingData.functor i
  have hc : T.homOfLE hle ≫ cV = cU :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (Spec.map (toRelativeSpecRingHom p φ V) ≫ ιV)) h1).trans
        ((Category.assoc _ _ _).trans
          (congrArg ((p ⁻¹ᵁ U.toOpens).toSpecΓ ≫ ·)
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ ιV) h2).trans
                ((Category.assoc _ _ _).trans
                  (congrArg (Spec.map (toRelativeSpecRingHom p φ U) ≫ ·) h3)))))))
  exact (Category.assoc _ _ cV).symm.trans
    ((congrArg (· ≫ cV) (p.cover_trans_pullbackRestrictIsoRestrict_hom i)).trans
      ((Category.assoc _ _ cV).trans
        (congrArg ((pullbackRestrictIsoRestrict p U.toOpens).hom ≫ ·) hc)))

/-- The morphism `T ⟶ A.relativeSpec` over `X` induced by a morphism of commutative
`𝒪ₓ`-algebras `φ : A ⟶ p_* 𝒪_T`, obtained by gluing the canonical affine morphisms over the
affine opens of `X`. -/
@[expose]
def toRelativeSpec (φ : A ⟶ p.pushforwardStructureAlgebra) : T ⟶ A.relativeSpec :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover X).pullback₁ p)
    (p.toRelativeSpecChart φ)
    (fun i ↦ p.toRelativeSpecChart_naturality φ i)

/-- On the preimage of an affine open `U` of `X`, `p.toRelativeSpec φ` is given by the canonical
morphism `p⁻¹(U) ⟶ Spec Γ(T, p⁻¹(U))` followed by `Spec` of the section map on `U` and the chart
inclusion into `A.relativeSpec`. -/
@[reassoc]
lemma ι_toRelativeSpec (φ : A ⟶ p.pushforwardStructureAlgebra) (U : X.AffineZariskiSite) :
    (p ⁻¹ᵁ U.toOpens).ι ≫ p.toRelativeSpec φ =
      (p ⁻¹ᵁ U.toOpens).toSpecΓ ≫
        Spec.map
          ((CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom).app
            (op U.toOpens)) ≫
        A.relativeSpecCover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict p U.toOpens).hom, ← Category.assoc]
  have hU : (pullbackRestrictIsoRestrict p U.toOpens).hom ≫ (p ⁻¹ᵁ U.toOpens).ι =
      ((directedCover X).pullback₁ p).f U :=
    pullbackRestrictIsoRestrict_hom_ι p U.toOpens
  rw [hU]
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected
    ((directedCover X).pullback₁ p) (p.toRelativeSpecChart φ)
    (fun i ↦ p.toRelativeSpecChart_naturality φ i) U

/-- The morphism `p.toRelativeSpec φ` is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma toRelativeSpec_relativeSpecToBase (φ : A ⟶ p.pushforwardStructureAlgebra) :
    p.toRelativeSpec φ ≫ A.relativeSpecToBase = p := by
  refine p.hom_ext_of_preimage_affineZariskiSite _ _ fun U ↦ ?_
  let ψU : CommRingCat.of Γ(A.X, U.toOpens) ⟶ Γ(T, p ⁻¹ᵁ U.toOpens) :=
    (CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom).app
      (op U.toOpens)
  let aU : CommRingCat.of Γ(X, U.toOpens) ⟶ CommRingCat.of Γ(A.X, U.toOpens) :=
    A.toSectionsPresheaf.app (op U.toOpens)
  have hcomp : aU ≫ ψU = p.app U.toOpens := by
    have h1 : A.toSectionsPresheaf ≫
        (CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom) = p.c := by
      rw [← Category.assoc, CommMon.toSectionsPresheaf_comp_sectionsPresheafMap,
        p.pushforwardStructureAlgebra_toSectionsPresheaf_comp]
    exact NatTrans.congr_app h1 (op U.toOpens)
  refine (p.ι_toRelativeSpec_assoc φ U A.relativeSpecToBase).trans ?_
  have hchart : A.relativeSpecCover.f U ≫ A.relativeSpecToBase =
      Spec.map aU ≫ U.2.fromSpec :=
    A.relativeSpecCover_f_relativeSpecToBase U
  refine (congrArg (fun k ↦ (p ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map ψU ≫ k) hchart).trans ?_
  rw [← Spec.map_comp_assoc, hcomp]
  simp

/-- `toRelativeSpec` is natural with respect to morphisms of quasi-coherent `𝒪ₓ`-algebras. -/
@[reassoc]
lemma toRelativeSpec_comp_relativeSpecMap {B : CommMon X.Modules} [B.X.IsQuasicoherent]
    (f : B ⟶ A) (φ : A ⟶ p.pushforwardStructureAlgebra) :
    p.toRelativeSpec φ ≫ CommMon.relativeSpecMap f = p.toRelativeSpec (f ≫ φ) := by
  refine p.hom_ext_of_preimage_affineZariskiSite _ _ fun U ↦ ?_
  let ψU : CommRingCat.of Γ(A.X, U.toOpens) ⟶ Γ(T, p ⁻¹ᵁ U.toOpens) :=
    (CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom).app
      (op U.toOpens)
  let fU : CommRingCat.of Γ(B.X, U.toOpens) ⟶ CommRingCat.of Γ(A.X, U.toOpens) :=
    CommRingCat.ofHom (CommMon.sectionsAlgHom f U.toOpens).toRingHom
  let ιB : Spec (CommRingCat.of Γ(B.X, U.toOpens)) ⟶ B.relativeSpec := B.relativeSpecCover.f U
  have hfφ : fU ≫ ψU =
      (CommMon.sectionsPresheafMap (f ≫ φ) ≫
        p.pushforwardStructureAlgebraPresheafIso.hom).app (op U.toOpens) := by
    have hfU : fU = (CommMon.sectionsPresheafMap f).app (op U.toOpens) :=
      (CommMon.sectionsPresheafMap_app f (op U.toOpens)).symm
    have hcomp : CommMon.sectionsPresheafMap (f ≫ φ) ≫
        p.pushforwardStructureAlgebraPresheafIso.hom =
      CommMon.sectionsPresheafMap f ≫
        (CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom) := by
      rw [CommMon.sectionsPresheafMap_comp, Category.assoc]
    exact (congrArg (· ≫ ψU) hfU).trans (NatTrans.congr_app hcomp (op U.toOpens)).symm
  refine (p.ι_toRelativeSpec_assoc φ U (CommMon.relativeSpecMap f)).trans ?_
  refine (congrArg (fun k ↦ (p ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map ψU ≫ k)
    (CommMon.relativeSpecCover_f_relativeSpecMap f U)).trans ?_
  refine ((congrArg ((p ⁻¹ᵁ U.toOpens).toSpecΓ ≫ ·) (Spec.map_comp_assoc fU ψU ιB).symm).trans
    (congrArg (fun h ↦ (p ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map h ≫ ιB) hfφ)).trans ?_
  exact (p.ι_toRelativeSpec (f ≫ φ) U).symm

/-- `toRelativeSpec` is natural with respect to precomposition by scheme morphisms over `X`. -/
@[reassoc]
lemma comp_toRelativeSpec {T' : Scheme.{u}} (g : T' ⟶ T) {p' : T' ⟶ X} (h : g ≫ p = p')
    (φ : A ⟶ p.pushforwardStructureAlgebra) :
    g ≫ p.toRelativeSpec φ =
      p'.toRelativeSpec (φ ≫ Scheme.Hom.pushforwardStructureAlgebraMap g h) := by
  refine p'.hom_ext_of_preimage_affineZariskiSite _ _ fun U ↦ ?_
  have hle : p' ⁻¹ᵁ U.toOpens ≤ g ⁻¹ᵁ (p ⁻¹ᵁ U.toOpens) := by
    rw [← Scheme.Hom.comp_preimage, h]
  let ψU : CommRingCat.of Γ(A.X, U.toOpens) ⟶ Γ(T, p ⁻¹ᵁ U.toOpens) :=
    (CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom).app
      (op U.toOpens)
  let ψU' : CommRingCat.of Γ(A.X, U.toOpens) ⟶ Γ(T', p' ⁻¹ᵁ U.toOpens) :=
    (CommMon.sectionsPresheafMap (φ ≫ Scheme.Hom.pushforwardStructureAlgebraMap g h) ≫
      p'.pushforwardStructureAlgebraPresheafIso.hom).app (op U.toOpens)
  let ιA : Spec (CommRingCat.of Γ(A.X, U.toOpens)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  have hring : ψU ≫ g.appLE (p ⁻¹ᵁ U.toOpens) (p' ⁻¹ᵁ U.toOpens) hle = ψU' := by
    have hmap : p.pushforwardStructureAlgebraPresheafIso.hom.app (op U.toOpens) ≫
        g.appLE (p ⁻¹ᵁ U.toOpens) (p' ⁻¹ᵁ U.toOpens) hle =
        (CommMon.sectionsPresheafMap (Scheme.Hom.pushforwardStructureAlgebraMap g h)).app
          (op U.toOpens) ≫
          p'.pushforwardStructureAlgebraPresheafIso.hom.app (op U.toOpens) := by
      rw [CommMon.sectionsPresheafMap_app,
        Scheme.Hom.pushforwardStructureAlgebraPresheafIso_hom_app,
        Scheme.Hom.pushforwardStructureAlgebraPresheafIso_hom_app]
      apply ConcreteCategory.hom_ext
      intro (x : Γ(p.pushforwardStructureAlgebra.X, U.toOpens))
      change g.appLE (p ⁻¹ᵁ U.toOpens) (p' ⁻¹ᵁ U.toOpens) hle
          (p.pushforwardStructureAlgebraSectionsRingEquiv U.toOpens x) =
        (p'.pushforwardStructureAlgebraSectionsRingEquiv U.toOpens)
          (CommMon.sectionsAlgHom (Scheme.Hom.pushforwardStructureAlgebraMap g h) U.toOpens x)
      rw [Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply,
        RingEquiv.apply_symm_apply]
    have hcomp : ψU' =
        (CommMon.sectionsPresheafMap φ).app (op U.toOpens) ≫
          ((CommMon.sectionsPresheafMap (Scheme.Hom.pushforwardStructureAlgebraMap g h)).app
            (op U.toOpens) ≫
            p'.pushforwardStructureAlgebraPresheafIso.hom.app (op U.toOpens)) := by
      dsimp only [ψU']
      rw [CommMon.sectionsPresheafMap_comp, Category.assoc]
      rfl
    exact (Category.assoc _ _ _).trans
      ((congrArg ((CommMon.sectionsPresheafMap φ).app (op U.toOpens) ≫ ·) hmap).trans hcomp.symm)
  have h1 : (p' ⁻¹ᵁ U.toOpens).ι ≫ (g ≫ p.toRelativeSpec φ) =
      g.resLE (p ⁻¹ᵁ U.toOpens) (p' ⁻¹ᵁ U.toOpens) hle ≫
        ((p ⁻¹ᵁ U.toOpens).ι ≫ p.toRelativeSpec φ) := by
    rw [← Category.assoc, ← g.resLE_comp_ι hle, Category.assoc]
  have h2 : g.resLE (p ⁻¹ᵁ U.toOpens) (p' ⁻¹ᵁ U.toOpens) hle ≫
        ((p ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map ψU ≫ ιA) =
      (p' ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map ψU' ≫ ιA := by
    rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp_assoc, hring]
  exact h1.trans ((congrArg (g.resLE (p ⁻¹ᵁ U.toOpens) (p' ⁻¹ᵁ U.toOpens) hle ≫ ·)
    (p.ι_toRelativeSpec φ U)).trans
      (h2.trans (p'.ι_toRelativeSpec (φ ≫ Scheme.Hom.pushforwardStructureAlgebraMap g h) U).symm))

/-- Applying `toRelativeSpec` to the inverse of the canonical unit isomorphism
`p_* 𝒪_{Spec_X A} ≅ A` gives the identity on `Spec_X A`. -/
@[simp]
lemma toRelativeSpec_relativeSpecPushforwardIso_inv (A : CommMon X.Modules)
    [A.X.IsQuasicoherent] :
    A.relativeSpecToBase.toRelativeSpec A.relativeSpecPushforwardIso.inv =
      𝟙 A.relativeSpec := by
  let p := A.relativeSpecToBase
  refine p.hom_ext_of_preimage_affineZariskiSite _ _ fun U ↦ ?_
  let R : CommRingCat.{u} := CommRingCat.of Γ(A.X, U.1)
  let ψInv : R ⟶ Γ(A.relativeSpec, p ⁻¹ᵁ U.toOpens) :=
    (CommMon.sectionsPresheafMap A.relativeSpecPushforwardIso.inv ≫
      p.pushforwardStructureAlgebraPresheafIso.hom).app (op U.toOpens)
  let fU : CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.toOpens) ⟶ R :=
    CommRingCat.ofHom (CommMon.sectionsAlgHom A.relativeSpecPushforwardIso.hom U.toOpens).toRingHom
  let kU : Γ(A.relativeSpec, p ⁻¹ᵁ U.toOpens) ⟶
      CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.toOpens) :=
    p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.toOpens)
  let ιA : Spec R ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let gU : Γ(A.relativeSpec, p ⁻¹ᵁ U.toOpens) ⟶ Γ(Spec R, ⊤) :=
    ιA.appLE (p ⁻¹ᵁ U.toOpens) ⊤ (A.top_le_preimage_relativeSpecToBase U)
  have hkU : kU ≫ fU = gU ≫ (Scheme.ΓSpecIso R).hom := by
    dsimp only [kU]
    rw [Scheme.Hom.pushforwardStructureAlgebraPresheafIso_inv_app]
    apply ConcreteCategory.hom_ext
    intro x
    change CommMon.sectionsAlgHom A.relativeSpecPushforwardIso.hom U.1
      ((p.pushforwardStructureAlgebraSectionsRingEquiv U.1).symm x) =
      (Scheme.ΓSpecIso R).hom (gU x)
    rw [A.sectionsAlgHom_relativeSpecPushforwardIso_hom_apply U,
      A.relativeSpecCoverFunctionAlgebraSectionsRingEquiv_apply U,
      RingEquiv.apply_symm_apply]
    rfl
  have hchart1 : Spec.map (kU ≫ fU) ≫ (U.2.preimage p).fromSpec = ιA := by
    rw [hkU, Spec.map_comp_assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec ιA (U.2.preimage p) (isAffineOpen_top (Spec R))
        (A.top_le_preimage_relativeSpecToBase U),
      ← Category.assoc]
    have htop : Spec.map (Scheme.ΓSpecIso R).hom ≫ (isAffineOpen_top (Spec R)).fromSpec =
        𝟙 (Spec R) := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, Iso.inv_hom_id,
        Spec.map_id]
    rw [htop, Category.id_comp]
  have hinv : (kU ≫ fU) ≫ ψInv = 𝟙 Γ(A.relativeSpec, p ⁻¹ᵁ U.toOpens) := by
    have hfU : fU =
        (CommMon.sectionsPresheafMap A.relativeSpecPushforwardIso.hom).app (op U.toOpens) :=
      (CommMon.sectionsPresheafMap_app A.relativeSpecPushforwardIso.hom (op U.toOpens)).symm
    rw [hfU]
    change (p.pushforwardStructureAlgebraPresheafIso.inv ≫
        CommMon.sectionsPresheafMap A.relativeSpecPushforwardIso.hom ≫
        CommMon.sectionsPresheafMap A.relativeSpecPushforwardIso.inv ≫
        p.pushforwardStructureAlgebraPresheafIso.hom).app (op U.toOpens) = _
    rw [← Category.assoc (CommMon.sectionsPresheafMap A.relativeSpecPushforwardIso.hom),
      ← CommMon.sectionsPresheafMap_comp, Iso.hom_inv_id, CommMon.sectionsPresheafMap_id,
      Category.id_comp, Iso.inv_hom_id, NatTrans.id_app]
  have hchart2 : Spec.map ψInv ≫ ιA = (U.2.preimage p).fromSpec := by
    rw [← hchart1, ← Spec.map_comp_assoc, hinv, Spec.map_id, Category.id_comp]
  refine (p.ι_toRelativeSpec A.relativeSpecPushforwardIso.inv U).trans ?_
  exact (congrArg ((p ⁻¹ᵁ U.toOpens).toSpecΓ ≫ ·) hchart2).trans
    ((U.2.preimage p).toSpecΓ_fromSpec.trans (Category.comp_id _).symm)

/-- A morphism `f : T ⟶ A.relativeSpec` over `X` is uniquely recovered by `toRelativeSpec` from the
induced `𝒪ₓ`-algebra morphism `A ⟶ p_* 𝒪_T`. -/
@[simp]
lemma toRelativeSpec_pushforwardStructureAlgebraMap
    (f : T ⟶ A.relativeSpec) (hf : f ≫ A.relativeSpecToBase = p) :
    p.toRelativeSpec
        (A.relativeSpecPushforwardIso.inv ≫ Scheme.Hom.pushforwardStructureAlgebraMap f hf) =
      f := by
  rw [← comp_toRelativeSpec A.relativeSpecToBase f hf A.relativeSpecPushforwardIso.inv,
    toRelativeSpec_relativeSpecPushforwardIso_inv, Category.comp_id]

private lemma opens_ι_appLE_top_eq_topIso_inv (W : T.Opens) (e : ⊤ ≤ W.ι ⁻¹ᵁ W) :
    W.ι.appLE W ⊤ e = W.topIso.inv :=
  (T.ofRestrict_appLE W.isOpenEmbedding W ⊤ e).trans
    (congrArg T.presheaf.map (Subsingleton.elim _ _))

/-- On each affine open `U` of `X`, the action of `p.toRelativeSpec φ` on sections over
`A.relativeSpecToBase ⁻¹ᵁ U.toOpens` agrees with pulling back along the relative-Spec chart over `U`
and applying `φ`. -/
lemma toRelativeSpec_appLE (φ : A ⟶ p.pushforwardStructureAlgebra) (U : X.AffineZariskiSite)
    (hle : p ⁻¹ᵁ U.toOpens ≤ p.toRelativeSpec φ ⁻¹ᵁ (A.relativeSpecToBase ⁻¹ᵁ U.toOpens)) :
    (p.toRelativeSpec φ).appLE (A.relativeSpecToBase ⁻¹ᵁ U.toOpens) (p ⁻¹ᵁ U.toOpens) hle =
      (A.relativeSpecCover.f U).appLE (A.relativeSpecToBase ⁻¹ᵁ U.toOpens) ⊤
          (A.top_le_preimage_relativeSpecToBase U) ≫
        (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, U.toOpens))).hom ≫
        (CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom).app
          (op U.toOpens) := by
  let V : A.relativeSpec.Opens := A.relativeSpecToBase ⁻¹ᵁ U.toOpens
  let W : T.Opens := p ⁻¹ᵁ U.toOpens
  let R : CommRingCat.{u} := CommRingCat.of Γ(A.X, U.toOpens)
  let ψU : R ⟶ Γ(T, W) :=
    (CommMon.sectionsPresheafMap φ ≫ p.pushforwardStructureAlgebraPresheafIso.hom).app
      (op U.toOpens)
  let ιA : Spec R ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let q : Spec Γ(T, W) ⟶ A.relativeSpec := Spec.map ψU ≫ ιA
  have hq_le : ⊤ ≤ q ⁻¹ᵁ V := by
    change ⊤ ≤ Spec.map ψU ⁻¹ᵁ (ιA ⁻¹ᵁ V)
    exact (Scheme.Hom.preimage_mono (Spec.map ψU) (A.top_le_preimage_relativeSpecToBase U))
  have hι : W.ι ≫ p.toRelativeSpec φ = W.toSpecΓ ≫ q := p.ι_toRelativeSpec φ U
  have hle_top : (⊤ : W.toScheme.Opens) ≤ (W.ι ≫ p.toRelativeSpec φ) ⁻¹ᵁ V :=
    W.ι_preimage_self.ge.trans (Scheme.Hom.preimage_mono W.ι hle)
  have h1 : (p.toRelativeSpec φ).appLE V W hle ≫ W.topIso.inv =
      (W.ι ≫ p.toRelativeSpec φ).appLE V ⊤ hle_top := by
    rw [← opens_ι_appLE_top_eq_topIso_inv W W.ι_preimage_self.ge,
      Scheme.Hom.appLE_comp_appLE]
  have hle_top' : (⊤ : W.toScheme.Opens) ≤ (W.toSpecΓ ≫ q) ⁻¹ᵁ V :=
    Scheme.Hom.preimage_mono W.toSpecΓ hq_le
  have h2 : (W.toSpecΓ ≫ q).appLE V ⊤ hle_top' =
      (ιA.appLE V ⊤ (A.top_le_preimage_relativeSpecToBase U) ≫
        (Scheme.ΓSpecIso R).hom ≫ ψU) ≫ W.topIso.inv := by
    have hcomp : (W.toSpecΓ ≫ q).appLE V ⊤ hle_top' = q.appLE V ⊤ hq_le ≫ W.toSpecΓ.appTop :=
      (Scheme.Hom.appLE_comp_appLE W.toSpecΓ q V ⊤ ⊤ hq_le le_rfl).symm.trans
        (congrArg (q.appLE V ⊤ hq_le ≫ ·) (Scheme.Hom.appLE_eq_app W.toSpecΓ (U := ⊤)))
    have hnat : q.appLE V ⊤ hq_le ≫ (Scheme.ΓSpecIso Γ(T, W)).hom =
        (ιA.appLE V ⊤ (A.top_le_preimage_relativeSpecToBase U) ≫ (Scheme.ΓSpecIso R).hom) ≫ ψU :=
      Scheme.Hom.appLE_ΓSpecIso_hom_naturality ιA ψU rfl (A.top_le_preimage_relativeSpecToBase U)
        hq_le
    exact hcomp.trans ((congrArg (q.appLE V ⊤ hq_le ≫ ·) (Scheme.Opens.toSpecΓ_appTop W)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ W.topIso.inv) hnat).trans
          (congrArg (· ≫ W.topIso.inv) (Category.assoc _ _ _)))))
  rw [← cancel_mono W.topIso.inv, h1]
  have hcongr : (W.ι ≫ p.toRelativeSpec φ).appLE V ⊤ hle_top =
      (W.toSpecΓ ≫ q).appLE V ⊤ hle_top' := by
    congr 1
  exact hcongr.trans h2

/-- Pulling back regular functions along `p.toRelativeSpec φ` recovers `φ` up to the canonical
unit isomorphism `p_* 𝒪_{Spec_X A} ≅ A`. -/
@[reassoc, simp]
lemma pushforwardStructureAlgebraMap_toRelativeSpec (φ : A ⟶ p.pushforwardStructureAlgebra) :
    Scheme.Hom.pushforwardStructureAlgebraMap (p.toRelativeSpec φ)
        (p.toRelativeSpec_relativeSpecToBase φ) =
      A.relativeSpecPushforwardIso.hom ≫ φ := by
  refine CommMon.hom_ext_of_isAffineOpen fun U hU ↦ AlgHom.ext fun x ↦ ?_
  let V : X.AffineZariskiSite := ⟨U, hU⟩
  apply (p.pushforwardStructureAlgebraSectionsRingEquiv U).injective
  have hle : p ⁻¹ᵁ V.toOpens ≤ p.toRelativeSpec φ ⁻¹ᵁ (A.relativeSpecToBase ⁻¹ᵁ V.toOpens) := by
    rw [← Scheme.Hom.comp_preimage, p.toRelativeSpec_relativeSpecToBase φ]
  rw [Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply,
    RingEquiv.apply_symm_apply, CommMon.sectionsAlgHom_comp, AlgHom.comp_apply,
    A.sectionsAlgHom_relativeSpecPushforwardIso_hom_apply V,
    A.relativeSpecCoverFunctionAlgebraSectionsRingEquiv_apply V]
  have happ := congr($(p.toRelativeSpec_appLE φ V hle)
    (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv U x))
  have hφ_hom : (CommMon.sectionsPresheafMap φ ≫
        p.pushforwardStructureAlgebraPresheafIso.hom).app (op U) =
      CommRingCat.ofHom (CommMon.sectionsAlgHom φ U).toRingHom ≫
        (p.pushforwardStructureAlgebraSectionsRingEquiv U).toCommRingCatIso.hom := by
    rw [NatTrans.comp_app, CommMon.sectionsPresheafMap_app,
      Scheme.Hom.pushforwardStructureAlgebraPresheafIso_hom_app]
    rfl
  exact happ.trans (congr($hφ_hom _))

/-- Composing the inverse unit isomorphism `A ≅ p_* 𝒪_{Spec_X A}` with pullback of regular
functions along `p.toRelativeSpec φ` recovers `φ`. -/
@[reassoc]
lemma relativeSpecPushforwardIso_inv_comp_pushforwardStructureAlgebraMap_toRelativeSpec
    (φ : A ⟶ p.pushforwardStructureAlgebra) :
    A.relativeSpecPushforwardIso.inv ≫
        Scheme.Hom.pushforwardStructureAlgebraMap (p.toRelativeSpec φ)
          (p.toRelativeSpec_relativeSpecToBase φ) =
      φ := by
  rw [pushforwardStructureAlgebraMap_toRelativeSpec, Iso.inv_hom_id_assoc]

end

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

/-- The forgetful functor from affine schemes over `X` to all schemes over `X`. -/
abbrev affineSchemeOverForget : AffineSchemeOver X ⥤ Over X :=
  MorphismProperty.Over.forget (@IsAffineHom : MorphismProperty Scheme.{u})
    (⊤ : MorphismProperty Scheme.{u}) X

@[simp]
lemma affineSchemeOverForget_obj_left (V : AffineSchemeOver X) :
    ((affineSchemeOverForget X).obj V).left = V.left :=
  (rfl)

@[simp]
lemma affineSchemeOverForget_obj_hom (V : AffineSchemeOver X) :
    ((affineSchemeOverForget X).obj V).hom = V.hom :=
  (rfl)

@[simp]
lemma affineSchemeOverForget_map_left {V W : AffineSchemeOver X} (g : V ⟶ W) :
    ((affineSchemeOverForget X).map g).left = g.left :=
  (rfl)

/-- The forgetful functor `AffineSchemeOver X ⥤ Over X` is fully faithful. -/
def fullyFaithfulAffineSchemeOverForget : (affineSchemeOverForget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful (Functor.id Scheme.{u})
    (Functor.fromPUnit.{0} X) (@IsAffineHom : MorphismProperty Scheme.{u})

instance : (affineSchemeOverForget X).Full :=
  (fullyFaithfulAffineSchemeOverForget X).full

instance : (affineSchemeOverForget X).Faithful :=
  (fullyFaithfulAffineSchemeOverForget X).faithful

variable {X}

/-- Morphisms from an arbitrary `X`-scheme `T` into `Spec_X A` over `X` correspond bijectively to
morphisms `A.obj ⟶ T.hom_* 𝒪_T` of commutative `𝒪ₓ`-algebras. -/
@[expose]
def relativeSpecOverPushforwardHomEquiv (A : QuasicoherentAlgebra X) (T : Over X) :
    (T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) ≃
      (A.obj ⟶ T.hom.pushforwardStructureAlgebra) where
  toFun f :=
    A.obj.relativeSpecPushforwardIso.inv ≫
      Scheme.Hom.pushforwardStructureAlgebraMap f.left (Over.w f)
  invFun φ :=
    Over.homMk (T.hom.toRelativeSpec φ) (T.hom.toRelativeSpec_relativeSpecToBase φ)
  left_inv f := by
    ext1
    exact T.hom.toRelativeSpec_pushforwardStructureAlgebraMap f.left (Over.w f)
  right_inv φ :=
    T.hom.relativeSpecPushforwardIso_inv_comp_pushforwardStructureAlgebraMap_toRelativeSpec φ

@[simp]
lemma relativeSpecOverPushforwardHomEquiv_apply (A : QuasicoherentAlgebra X) (T : Over X)
    (f : T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) :
    relativeSpecOverPushforwardHomEquiv A T f =
      A.obj.relativeSpecPushforwardIso.inv ≫
        Scheme.Hom.pushforwardStructureAlgebraMap f.left (Over.w f) :=
  (rfl)

@[simp]
lemma relativeSpecOverPushforwardHomEquiv_symm_apply_left (A : QuasicoherentAlgebra X)
    (T : Over X) (φ : A.obj ⟶ T.hom.pushforwardStructureAlgebra) :
    ((relativeSpecOverPushforwardHomEquiv A T).symm φ).left = T.hom.toRelativeSpec φ :=
  (rfl)

lemma relativeSpecOverPushforwardHomEquiv_comp_left (A : QuasicoherentAlgebra X)
    {T' T : Over X} (g : T' ⟶ T)
    (f : T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) :
    relativeSpecOverPushforwardHomEquiv A T' (g ≫ f) =
      relativeSpecOverPushforwardHomEquiv A T f ≫
        Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g) := by
  have hcomp : Scheme.Hom.pushforwardStructureAlgebraMap (g ≫ f).left (Over.w (g ≫ f)) =
      Scheme.Hom.pushforwardStructureAlgebraMap f.left (Over.w f) ≫
        Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g) :=
    Scheme.Hom.pushforwardStructureAlgebraMap_comp g.left f.left (Over.w g) (Over.w f)
  exact (congrArg (A.obj.relativeSpecPushforwardIso.inv ≫ ·) hcomp).trans
    (Category.assoc _ _ _).symm

lemma relativeSpecOverPushforwardHomEquiv_comp_right {A B : QuasicoherentAlgebra X}
    (a : B ⟶ A) (T : Over X)
    (f : T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) :
    relativeSpecOverPushforwardHomEquiv B T
        (f ≫ (affineSchemeOverForget X).map ((relativeSpec X).map a.op)) =
      a.hom ≫ relativeSpecOverPushforwardHomEquiv A T f := by
  have hcomp : Scheme.Hom.pushforwardStructureAlgebraMap
        (f ≫ (affineSchemeOverForget X).map ((relativeSpec X).map a.op)).left
        (Over.w (f ≫ (affineSchemeOverForget X).map ((relativeSpec X).map a.op))) =
      Scheme.Hom.pushforwardStructureAlgebraMap (CommMon.relativeSpecMap a.hom)
          (CommMon.relativeSpecMap_relativeSpecToBase a.hom) ≫
        Scheme.Hom.pushforwardStructureAlgebraMap f.left (Over.w f) :=
    Scheme.Hom.pushforwardStructureAlgebraMap_comp f.left (CommMon.relativeSpecMap a.hom)
      (Over.w f) (CommMon.relativeSpecMap_relativeSpecToBase a.hom)
  have hnat : B.obj.relativeSpecPushforwardIso.inv ≫
      Scheme.Hom.pushforwardStructureAlgebraMap (CommMon.relativeSpecMap a.hom)
        (CommMon.relativeSpecMap_relativeSpecToBase a.hom) =
      a.hom ≫ A.obj.relativeSpecPushforwardIso.inv := by
    rw [← cancel_mono A.obj.relativeSpecPushforwardIso.hom, Category.assoc, Category.assoc,
      CommMon.relativeSpecPushforwardIso_hom_naturality, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (B.obj.relativeSpecPushforwardIso.inv ≫ ·) hcomp).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Scheme.Hom.pushforwardStructureAlgebraMap f.left (Over.w f)) hnat).trans
        (Category.assoc _ _ _)))

/-- Morphisms from an arbitrary `X`-scheme `p : T ⟶ X` into `Spec_X A` over `X` correspond
bijectively to morphisms `p^* A ⟶ 𝒪_T` of quasi-coherent commutative `𝒪_T`-algebras. -/
@[expose]
def relativeSpecOverHomEquiv (A : QuasicoherentAlgebra X) (T : Over X) :
    (T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) ≃
      ((pullbackQuasicoherentAlgebra T.hom).obj A ⟶ structureSheafAlgebra T.left) :=
  (relativeSpecOverPushforwardHomEquiv A T).trans
    (pullbackStructureSheafAlgebraHomEquiv T.hom A).symm

lemma relativeSpecOverHomEquiv_apply (A : QuasicoherentAlgebra X) (T : Over X)
    (f : T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) :
    relativeSpecOverHomEquiv A T f =
      (pullbackStructureSheafAlgebraHomEquiv T.hom A).symm
        (relativeSpecOverPushforwardHomEquiv A T f) :=
  (rfl)

lemma relativeSpecOverHomEquiv_symm_apply (A : QuasicoherentAlgebra X) (T : Over X)
    (φ : (pullbackQuasicoherentAlgebra T.hom).obj A ⟶ structureSheafAlgebra T.left) :
    (relativeSpecOverHomEquiv A T).symm φ =
      (relativeSpecOverPushforwardHomEquiv A T).symm
        (pullbackStructureSheafAlgebraHomEquiv T.hom A φ) :=
  (rfl)

lemma relativeSpecOverHomEquiv_comp_left (A : QuasicoherentAlgebra X)
    {T' T : Over X} (g : T' ⟶ T)
    (f : T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) :
    relativeSpecOverHomEquiv A T' (g ≫ f) =
      (pullbackAlgebraCompOverIso g A).inv ≫
        (pullbackQuasicoherentAlgebra g.left).map (relativeSpecOverHomEquiv A T f) ≫
        (pullbackStructureSheafAlgebraIso g.left).hom := by
  apply (pullbackStructureSheafAlgebraHomEquiv T'.hom A).injective
  rw [relativeSpecOverHomEquiv_apply, Equiv.apply_symm_apply,
    pullbackStructureSheafAlgebraHomEquiv_pullback, relativeSpecOverHomEquiv_apply,
    Equiv.apply_symm_apply, relativeSpecOverPushforwardHomEquiv_comp_left]

lemma relativeSpecOverHomEquiv_comp_right {A B : QuasicoherentAlgebra X}
    (a : B ⟶ A) (T : Over X)
    (f : T ⟶ (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))) :
    relativeSpecOverHomEquiv B T
        (f ≫ (affineSchemeOverForget X).map ((relativeSpec X).map a.op)) =
      (pullbackQuasicoherentAlgebra T.hom).map a ≫ relativeSpecOverHomEquiv A T f := by
  apply (pullbackStructureSheafAlgebraHomEquiv T.hom B).injective
  rw [relativeSpecOverHomEquiv_apply, Equiv.apply_symm_apply,
    pullbackStructureSheafAlgebraHomEquiv_precomp, relativeSpecOverHomEquiv_apply,
    Equiv.apply_symm_apply, relativeSpecOverPushforwardHomEquiv_comp_right]

variable (X)

/-- The functor of `Over X`-points of `relativeSpec X`. -/
@[expose]
def relativeSpecPoints : (QuasicoherentAlgebra X)ᵒᵖ ⥤ (Over X)ᵒᵖ ⥤ Type u :=
  relativeSpec X ⋙ affineSchemeOverForget X ⋙ yoneda

/-- The functor sending `A : (QuasicoherentAlgebra X)ᵒᵖ` and `T : (Over X)ᵒᵖ` to the type of
quasi-coherent algebra morphisms `(pullbackQuasicoherentAlgebra T.hom).obj A ⟶ 𝒪_T`, pulled back
in `T` and precomposed in `A`. -/
@[expose]
def relativeSpecAlgebraMaps : (QuasicoherentAlgebra X)ᵒᵖ ⥤ (Over X)ᵒᵖ ⥤ Type u where
  obj A := {
    obj T := (pullbackQuasicoherentAlgebra T.unop.hom).obj A.unop ⟶
      structureSheafAlgebra T.unop.left
    map g := TypeCat.ofHom fun a ↦
      (pullbackAlgebraCompOverIso g.unop A.unop).inv ≫
        (pullbackQuasicoherentAlgebra g.unop.left).map a ≫
        (pullbackStructureSheafAlgebraIso g.unop.left).hom
    map_id T := by
      apply ConcreteCategory.hom_ext
      intro a
      apply (pullbackStructureSheafAlgebraHomEquiv T.unop.hom A.unop).injective
      change pullbackStructureSheafAlgebraHomEquiv T.unop.hom A.unop
          ((pullbackAlgebraCompOverIso (𝟙 T.unop) A.unop).inv ≫
            (pullbackQuasicoherentAlgebra (Over.Hom.left (𝟙 T.unop))).map a ≫
            (pullbackStructureSheafAlgebraIso (Over.Hom.left (𝟙 T.unop))).hom) =
        pullbackStructureSheafAlgebraHomEquiv T.unop.hom A.unop a
      rw [pullbackStructureSheafAlgebraHomEquiv_pullback]
      exact (congrArg (pullbackStructureSheafAlgebraHomEquiv T.unop.hom A.unop a ≫ ·)
        Scheme.Hom.pushforwardStructureAlgebraMap_id).trans (Category.comp_id _)
    map_comp {T₁ T₂ T₃} f g := by
      apply ConcreteCategory.hom_ext
      intro a
      apply (pullbackStructureSheafAlgebraHomEquiv T₃.unop.hom A.unop).injective
      change pullbackStructureSheafAlgebraHomEquiv T₃.unop.hom A.unop
          ((pullbackAlgebraCompOverIso (g.unop ≫ f.unop) A.unop).inv ≫
            (pullbackQuasicoherentAlgebra (Over.Hom.left (g.unop ≫ f.unop))).map a ≫
            (pullbackStructureSheafAlgebraIso (Over.Hom.left (g.unop ≫ f.unop))).hom) =
        pullbackStructureSheafAlgebraHomEquiv T₃.unop.hom A.unop
          ((pullbackAlgebraCompOverIso g.unop A.unop).inv ≫
            (pullbackQuasicoherentAlgebra g.unop.left).map
              ((pullbackAlgebraCompOverIso f.unop A.unop).inv ≫
                (pullbackQuasicoherentAlgebra f.unop.left).map a ≫
                (pullbackStructureSheafAlgebraIso f.unop.left).hom) ≫
            (pullbackStructureSheafAlgebraIso g.unop.left).hom)
      rw [pullbackStructureSheafAlgebraHomEquiv_pullback,
        pullbackStructureSheafAlgebraHomEquiv_pullback,
        pullbackStructureSheafAlgebraHomEquiv_pullback]
      have hcomp : Scheme.Hom.pushforwardStructureAlgebraMap (g.unop ≫ f.unop).left
            (Over.w (g.unop ≫ f.unop)) =
          Scheme.Hom.pushforwardStructureAlgebraMap f.unop.left (Over.w f.unop) ≫
            Scheme.Hom.pushforwardStructureAlgebraMap g.unop.left (Over.w g.unop) :=
        Scheme.Hom.pushforwardStructureAlgebraMap_comp g.unop.left f.unop.left
          (Over.w g.unop) (Over.w f.unop)
      rw [hcomp, Category.assoc] }
  map a := {
    app T := TypeCat.ofHom fun h ↦
      (pullbackQuasicoherentAlgebra T.unop.hom).map a.unop ≫ h
    naturality {T₁ T₂} g := by
      apply ConcreteCategory.hom_ext
      intro h
      apply (pullbackStructureSheafAlgebraHomEquiv T₂.unop.hom _).injective
      change pullbackStructureSheafAlgebraHomEquiv T₂.unop.hom _
          ((pullbackQuasicoherentAlgebra T₂.unop.hom).map a.unop ≫
            (pullbackAlgebraCompOverIso g.unop _).inv ≫
              (pullbackQuasicoherentAlgebra g.unop.left).map h ≫
              (pullbackStructureSheafAlgebraIso g.unop.left).hom) =
        pullbackStructureSheafAlgebraHomEquiv T₂.unop.hom _
          ((pullbackAlgebraCompOverIso g.unop _).inv ≫
            (pullbackQuasicoherentAlgebra g.unop.left).map
              ((pullbackQuasicoherentAlgebra T₁.unop.hom).map a.unop ≫ h) ≫
            (pullbackStructureSheafAlgebraIso g.unop.left).hom)
      rw [pullbackStructureSheafAlgebraHomEquiv_precomp,
        pullbackStructureSheafAlgebraHomEquiv_pullback,
        pullbackStructureSheafAlgebraHomEquiv_pullback,
        pullbackStructureSheafAlgebraHomEquiv_precomp, Category.assoc] }
  map_id A := by
    refine NatTrans.ext (funext fun T ↦ ?_)
    apply ConcreteCategory.hom_ext
    intro h
    exact (congrArg (· ≫ h) ((pullbackQuasicoherentAlgebra T.unop.hom).map_id A.unop)).trans
      (Category.id_comp h)
  map_comp a b := by
    refine NatTrans.ext (funext fun T ↦ ?_)
    apply ConcreteCategory.hom_ext
    intro h
    exact (congrArg (· ≫ h)
      ((pullbackQuasicoherentAlgebra T.unop.hom).map_comp b.unop a.unop)).trans
      (Category.assoc _ _ h)

/-- The universal property of relative Spec as a natural isomorphism of bifunctors
`relativeSpecPoints X ≅ relativeSpecAlgebraMaps X`. -/
@[expose]
def relativeSpecUniversalProperty :
    relativeSpecPoints X ≅ relativeSpecAlgebraMaps X :=
  NatIso.ofComponents
    (fun A ↦ NatIso.ofComponents
      (fun T ↦
        { hom := TypeCat.ofHom (relativeSpecOverHomEquiv A.unop T.unop)
          inv := TypeCat.ofHom (relativeSpecOverHomEquiv A.unop T.unop).symm
          hom_inv_id := by
            apply ConcreteCategory.hom_ext
            intro f
            exact (relativeSpecOverHomEquiv A.unop T.unop).symm_apply_apply f
          inv_hom_id := by
            apply ConcreteCategory.hom_ext
            intro φ
            exact (relativeSpecOverHomEquiv A.unop T.unop).apply_symm_apply φ })
      (fun g ↦ by
        apply ConcreteCategory.hom_ext
        intro f
        exact relativeSpecOverHomEquiv_comp_left A.unop g.unop f))
    (fun a ↦ by
      refine NatTrans.ext (funext fun T ↦ ?_)
      apply ConcreteCategory.hom_ext
      intro f
      exact relativeSpecOverHomEquiv_comp_right a.unop T.unop f)

end

end TauCeti.AlgebraicGeometry

end
