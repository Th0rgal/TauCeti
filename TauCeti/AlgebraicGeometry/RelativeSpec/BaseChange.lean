/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import TauCeti.AlgebraicGeometry.RelativeSpec.UniversalProperty

/-!
# Base-change compatibility for relative Spec

For a morphism of schemes `f : Y ⟶ X` and a quasi-coherent commutative `𝒪ₓ`-algebra `A`, the
scheme-theoretic base change of `Spec_X A` along `f` is canonically isomorphic in
`AffineSchemeOver Y` to `Spec_Y (f^* A)`, naturally in `A`.

Rather than re-gluing open charts of the fiber product by hand, we derive this isomorphism from the
universal property of relative Spec (`TauCeti.AlgebraicGeometry.UniversalProperty`) together with:
1. the adjunction `Over.map f ⊣ Over.pullback f` between postcomposition and fiber product of
   schemes over `X` and `Y`,
2. the monoidal composition identification `(p ≫ f)_* 𝒪_T ≅ f_* (p_* 𝒪_T)` of pushforward
   structure algebras (`AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraCompIso`), and
3. the algebra pullback--pushforward adjunction bijection
   (`TauCeti.AlgebraicGeometry.pullbackPushforwardCommMonHomEquiv`).

## Main declarations

* `TauCeti.AlgebraicGeometry.baseChangeAffineSchemeOver`: the base-change functor
  `AffineSchemeOver X ⥤ AffineSchemeOver Y` along `f : Y ⟶ X`.
* `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraCompIso`: the canonical isomorphism
  `(p ≫ f).pushforwardStructureAlgebra ≅
    (Scheme.Modules.pushforward f).mapCommMon.obj p.pushforwardStructureAlgebra`.
* `TauCeti.AlgebraicGeometry.relativeSpecBaseChangeOverHomEquiv`: the natural bijection between
  `Over Y`-morphisms into the base change of `Spec_X A` and `Over Y`-morphisms into
  `Spec_Y (f^* A)`.
* `TauCeti.AlgebraicGeometry.relativeSpecBaseChangeIso`: the canonical isomorphism
  `(baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)) ≅
    (relativeSpec Y).obj (op ((pullbackQuasicoherentAlgebra f).obj A))` in `AffineSchemeOver Y`.
* `TauCeti.AlgebraicGeometry.relativeSpecBaseChangeNatIso`: the natural isomorphism of functors
  `relativeSpec X ⋙ baseChangeAffineSchemeOver f ≅
    (pullbackQuasicoherentAlgebra f).op ⋙ relativeSpec Y`.
* `TauCeti.AlgebraicGeometry.isPullback_relativeSpecBaseChange`: the fiber-product square
  characterizing `Spec_Y (f^* A)` as the pullback of `Spec_X A ⟶ X` along `f : Y ⟶ X`.

## References

* The Stacks Project, [Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, Proposition 1.5.2.
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

noncomputable section

variable {X Y T T' : Scheme.{u}} (p : T ⟶ Y) (f : Y ⟶ X)

/-- Pushing forward the structure-sheaf algebra along a composite morphism `p ≫ f` is canonically
isomorphic to pushing forward `p.pushforwardStructureAlgebra` along `f`. -/
@[expose]
def pushforwardStructureAlgebraCompIso :
    (p ≫ f).pushforwardStructureAlgebra ≅
      (Scheme.Modules.pushforward f).mapCommMon.obj p.pushforwardStructureAlgebra :=
  ((Functor.mapCommMonNatIso (Scheme.Modules.pushforwardComp p f)).symm ≪≫
    Functor.mapCommMonCompIso).app (CommMon.trivial T.Modules)

@[simp]
lemma pushforwardStructureAlgebraCompIso_hom_hom_hom :
    (p.pushforwardStructureAlgebraCompIso f).hom.hom.hom =
      (Scheme.Modules.pushforwardComp p f).inv.app (𝟙_ T.Modules) ≫ 𝟙 _ :=
  (rfl)

@[simp]
lemma pushforwardStructureAlgebraCompIso_inv_hom_hom :
    (p.pushforwardStructureAlgebraCompIso f).inv.hom.hom =
      𝟙 _ ≫ (Scheme.Modules.pushforwardComp p f).hom.app (𝟙_ T.Modules) :=
  (rfl)

lemma sectionsAlgHom_pushforwardStructureAlgebraCompIso_hom_apply (U : X.Opens)
    (x : Γ((p ≫ f).pushforwardStructureAlgebra.X, U)) :
    CommMon.sectionsAlgHom (p.pushforwardStructureAlgebraCompIso f).hom U x = x := by
  rw [CommMon.sectionsAlgHom_apply]
  rfl

lemma sectionsAlgHom_pushforward_mapCommMon_map_apply {M N : CommMon Y.Modules}
    (m : M ⟶ N) (U : X.Opens) (x : Γ(((Scheme.Modules.pushforward f).mapCommMon.obj M).X, U)) :
    CommMon.sectionsAlgHom ((Scheme.Modules.pushforward f).mapCommMon.map m) U x =
      CommMon.sectionsAlgHom m (f ⁻¹ᵁ U) x :=
  (CommMon.sectionsAlgHom_apply ((Scheme.Modules.pushforward f).mapCommMon.map m) U x).trans
    (CommMon.sectionsAlgHom_apply m (f ⁻¹ᵁ U) x).symm

/-- `pushforwardStructureAlgebraCompIso` is natural with respect to morphisms `g : T' ⟶ T` over
`Y`. -/
@[reassoc]
lemma pushforwardStructureAlgebraMap_comp_pushforwardStructureAlgebraCompIso_hom
    {p : T ⟶ Y} {p' : T' ⟶ Y} (g : T' ⟶ T) (hg : g ≫ p = p')
    (hgf : g ≫ (p ≫ f) = p' ≫ f) :
    Scheme.Hom.pushforwardStructureAlgebraMap g hgf ≫
        (p'.pushforwardStructureAlgebraCompIso f).hom =
      (p.pushforwardStructureAlgebraCompIso f).hom ≫
        (Scheme.Modules.pushforward f).mapCommMon.map
          (Scheme.Hom.pushforwardStructureAlgebraMap g hg) := by
  refine CommMon.hom_ext_of_sectionsAlgHom fun U ↦ AlgHom.ext fun x ↦ ?_
  have hL :
      CommMon.sectionsAlgHom
          (Scheme.Hom.pushforwardStructureAlgebraMap g hgf ≫
            (p'.pushforwardStructureAlgebraCompIso f).hom) U x =
        g.appLE ((p ≫ f) ⁻¹ᵁ U) ((p' ≫ f) ⁻¹ᵁ U)
          (by rw [← Scheme.Hom.comp_preimage, hgf]) x :=
    (AlgHom.congr_fun (CommMon.sectionsAlgHom_comp _ _ U) x).trans
      ((sectionsAlgHom_pushforwardStructureAlgebraCompIso_hom_apply p' f U _).trans
        ((Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply g hgf U x).trans
          ((Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply (p' ≫ f) U _).trans
            (congrArg (g.appLE ((p ≫ f) ⁻¹ᵁ U) ((p' ≫ f) ⁻¹ᵁ U)
                (by rw [← Scheme.Hom.comp_preimage, hgf]))
              (Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply (p ≫ f) U x)))))
  have hR :
      CommMon.sectionsAlgHom
          ((p.pushforwardStructureAlgebraCompIso f).hom ≫
            (Scheme.Modules.pushforward f).mapCommMon.map
              (Scheme.Hom.pushforwardStructureAlgebraMap g hg)) U x =
        g.appLE (p ⁻¹ᵁ (f ⁻¹ᵁ U)) (p' ⁻¹ᵁ (f ⁻¹ᵁ U)) (by subst hg; exact le_rfl) x :=
    (AlgHom.congr_fun (CommMon.sectionsAlgHom_comp _ _ U) x).trans
      ((congrArg
        (CommMon.sectionsAlgHom
          ((Scheme.Modules.pushforward f).mapCommMon.map
            (Scheme.Hom.pushforwardStructureAlgebraMap g hg)) U)
        (sectionsAlgHom_pushforwardStructureAlgebraCompIso_hom_apply p f U x)).trans
        ((sectionsAlgHom_pushforward_mapCommMon_map_apply f
          (Scheme.Hom.pushforwardStructureAlgebraMap g hg) U x).trans
          ((Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply g hg (f ⁻¹ᵁ U) x).trans
            ((Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply
              p' (f ⁻¹ᵁ U) _).trans
              (congrArg (g.appLE (p ⁻¹ᵁ (f ⁻¹ᵁ U)) (p' ⁻¹ᵁ (f ⁻¹ᵁ U)) (by subst hg; exact le_rfl))
                (Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply
                  p (f ⁻¹ᵁ U) x))))))
  exact hL.trans hR.symm

end

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {X Y Z : Scheme.{u}}

instance (f : Y ⟶ X) : MorphismProperty.HasPullbacksAlong (@IsAffineHom) f where
  hasPullback _ _ := inferInstance

instance (f : Y ⟶ X) : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) f where
  of_isPullback := MorphismProperty.IsStableUnderBaseChange.of_isPullback

/-- Base change of affine schemes over `X` along a scheme morphism `f : Y ⟶ X`, given by fiber
product over `X`. -/
@[expose]
def baseChangeAffineSchemeOver (f : Y ⟶ X) : AffineSchemeOver X ⥤ AffineSchemeOver Y :=
  MorphismProperty.Over.pullback (@IsAffineHom : MorphismProperty Scheme.{u})
    (⊤ : MorphismProperty Scheme.{u}) f

@[simp]
lemma baseChangeAffineSchemeOver_obj_left (f : Y ⟶ X) (V : AffineSchemeOver X) :
    ((baseChangeAffineSchemeOver f).obj V).left = pullback V.hom f :=
  (rfl)

@[simp]
lemma baseChangeAffineSchemeOver_obj_hom (f : Y ⟶ X) (V : AffineSchemeOver X) :
    ((baseChangeAffineSchemeOver f).obj V).hom = pullback.snd V.hom f :=
  (rfl)

@[simp]
lemma baseChangeAffineSchemeOver_map_left (f : Y ⟶ X) {V W : AffineSchemeOver X} (h : V ⟶ W) :
    ((baseChangeAffineSchemeOver f).map h).left =
      pullback.lift (pullback.fst V.hom f ≫ h.left) (pullback.snd V.hom f)
        (by simp [pullback.condition]) :=
  (rfl)

/-- Base change of affine schemes commutes with forgetting affineness into `Over`. -/
@[expose]
def baseChangeAffineSchemeOverCompForgetIso (f : Y ⟶ X) :
    baseChangeAffineSchemeOver f ⋙ affineSchemeOverForget Y ≅
      affineSchemeOverForget X ⋙ Over.pullback f :=
  MorphismProperty.Over.pullbackCompForgetIso f

/-- Base change of affine schemes respects composition of scheme morphisms. -/
@[expose]
def baseChangeAffineSchemeOverCompIso (g : Z ⟶ Y) (f : Y ⟶ X) :
    baseChangeAffineSchemeOver (g ≫ f) ≅
      baseChangeAffineSchemeOver f ⋙ baseChangeAffineSchemeOver g :=
  MorphismProperty.Over.pullbackComp g f

/-- Base change of affine schemes along equal scheme morphisms are canonically isomorphic. -/
@[expose]
def baseChangeAffineSchemeOverCongr {f₁ f₂ : Y ⟶ X} (h : f₁ = f₂) :
    baseChangeAffineSchemeOver f₁ ≅ baseChangeAffineSchemeOver f₂ :=
  MorphismProperty.Over.pullbackCongr h

@[reassoc]
lemma pullbackPushforwardCommMonHomEquiv_symm_precomp (f : Y ⟶ X)
    {A B : QuasicoherentAlgebra X} (a : B ⟶ A) (C : CommMon Y.Modules)
    (ψ : A.obj ⟶ (Scheme.Modules.pushforward f).mapCommMon.obj C) :
    (pullbackPushforwardCommMonHomEquiv f B C).symm (a.hom ≫ ψ) =
      ((pullbackQuasicoherentAlgebra f).map a).hom ≫
        (pullbackPushforwardCommMonHomEquiv f A C).symm ψ := by
  apply CommMon.hom_ext
  exact Adjunction.homEquiv_naturality_left_symm
    (Scheme.Modules.pullbackPushforwardAdjunction f) a.hom.hom.hom ψ.hom.hom

@[reassoc]
lemma pullbackPushforwardCommMonHomEquiv_symm_postcomp (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) {C D : CommMon Y.Modules} (m : C ⟶ D)
    (ψ : A.obj ⟶ (Scheme.Modules.pushforward f).mapCommMon.obj C) :
    (pullbackPushforwardCommMonHomEquiv f A D).symm
        (ψ ≫ (Scheme.Modules.pushforward f).mapCommMon.map m) =
      (pullbackPushforwardCommMonHomEquiv f A C).symm ψ ≫ m := by
  apply CommMon.hom_ext
  exact Adjunction.homEquiv_naturality_right_symm
    (Scheme.Modules.pullbackPushforwardAdjunction f) ψ.hom.hom m.hom.hom

/-- For a scheme morphism `f : Y ⟶ X`, a quasi-coherent `𝒪ₓ`-algebra `A`, and an arbitrary
`Y`-scheme `T : Over Y`, morphisms from `T` into the base change `(Spec_X A) ×_X Y` over `Y`
correspond bijectively to morphisms from `T` into `Spec_Y (f^* A)` over `Y`. -/
@[expose]
def relativeSpecBaseChangeOverHomEquiv (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) (T : Over Y) :
    (T ⟶ (affineSchemeOverForget Y).obj
      ((baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)))) ≃
    (T ⟶ (affineSchemeOverForget Y).obj
      ((relativeSpec Y).obj (op ((pullbackQuasicoherentAlgebra f).obj A)))) :=
  (((Over.mapPullbackAdj f).homEquiv T
      ((affineSchemeOverForget X).obj ((relativeSpec X).obj (op A)))).symm).trans
    ((relativeSpecOverPushforwardHomEquiv A ((Over.map f).obj T)).trans
      ((Iso.homCongr (Iso.refl A.obj)
          (Scheme.Hom.pushforwardStructureAlgebraCompIso T.hom f)).trans
        (((pullbackPushforwardCommMonHomEquiv f A
            T.hom.pushforwardStructureAlgebra).symm).trans
          (relativeSpecOverPushforwardHomEquiv
            ((pullbackQuasicoherentAlgebra f).obj A) T).symm)))

lemma relativeSpecBaseChangeOverHomEquiv_apply (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) (T : Over Y)
    (h : T ⟶ (affineSchemeOverForget Y).obj
      ((baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)))) :
    relativeSpecBaseChangeOverHomEquiv f A T h =
      (relativeSpecOverPushforwardHomEquiv ((pullbackQuasicoherentAlgebra f).obj A) T).symm
        ((pullbackPushforwardCommMonHomEquiv f A T.hom.pushforwardStructureAlgebra).symm
          (relativeSpecOverPushforwardHomEquiv A ((Over.map f).obj T)
            (((Over.mapPullbackAdj f).homEquiv T
              ((affineSchemeOverForget X).obj ((relativeSpec X).obj (op A)))).symm h) ≫
            (Scheme.Hom.pushforwardStructureAlgebraCompIso T.hom f).hom)) :=
  (rfl)

lemma relativeSpecBaseChangeOverHomEquiv_comp_left (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) {T' T : Over Y} (k : T' ⟶ T)
    (h : T ⟶ (affineSchemeOverForget Y).obj
      ((baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)))) :
    relativeSpecBaseChangeOverHomEquiv f A T' (k ≫ h) =
      k ≫ relativeSpecBaseChangeOverHomEquiv f A T h := by
  let V : Over X := (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))
  let h₀ : (Over.map f).obj T ⟶ V := ((Over.mapPullbackAdj f).homEquiv T V).symm h
  let φ₀ : A.obj ⟶ (T.hom ≫ f).pushforwardStructureAlgebra :=
    relativeSpecOverPushforwardHomEquiv A ((Over.map f).obj T) h₀
  apply (relativeSpecOverPushforwardHomEquiv ((pullbackQuasicoherentAlgebra f).obj A) T').injective
  rw [relativeSpecBaseChangeOverHomEquiv_apply, Equiv.apply_symm_apply,
    relativeSpecOverPushforwardHomEquiv_comp_left,
    relativeSpecBaseChangeOverHomEquiv_apply, Equiv.apply_symm_apply]
  have hadj : ((Over.mapPullbackAdj f).homEquiv T' V).symm (k ≫ h) =
      (Over.map f).map k ≫ h₀ :=
    Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj f) k h
  have h1 : relativeSpecOverPushforwardHomEquiv A ((Over.map f).obj T')
        (((Over.mapPullbackAdj f).homEquiv T' V).symm (k ≫ h)) =
      φ₀ ≫ Scheme.Hom.pushforwardStructureAlgebraMap k.left (Over.w ((Over.map f).map k)) :=
    (congrArg (relativeSpecOverPushforwardHomEquiv A ((Over.map f).obj T')) hadj).trans
      (relativeSpecOverPushforwardHomEquiv_comp_left A ((Over.map f).map k) h₀)
  have h2 : (φ₀ ≫ Scheme.Hom.pushforwardStructureAlgebraMap k.left (Over.w ((Over.map f).map k))) ≫
        (Scheme.Hom.pushforwardStructureAlgebraCompIso T'.hom f).hom =
      (φ₀ ≫ (Scheme.Hom.pushforwardStructureAlgebraCompIso T.hom f).hom) ≫
        (Scheme.Modules.pushforward f).mapCommMon.map
          (Scheme.Hom.pushforwardStructureAlgebraMap k.left (Over.w k)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (φ₀ ≫ ·)
        (Scheme.Hom.pushforwardStructureAlgebraMap_comp_pushforwardStructureAlgebraCompIso_hom
          f k.left (Over.w k) (Over.w ((Over.map f).map k)))).trans
        (Category.assoc _ _ _).symm)
  exact (congrArg
    (fun m ↦ (pullbackPushforwardCommMonHomEquiv f A T'.hom.pushforwardStructureAlgebra).symm
      (m ≫ (Scheme.Hom.pushforwardStructureAlgebraCompIso T'.hom f).hom)) h1).trans
    ((congrArg
      (pullbackPushforwardCommMonHomEquiv f A T'.hom.pushforwardStructureAlgebra).symm h2).trans
      (pullbackPushforwardCommMonHomEquiv_symm_postcomp f A
        (Scheme.Hom.pushforwardStructureAlgebraMap k.left (Over.w k))
        (φ₀ ≫ (Scheme.Hom.pushforwardStructureAlgebraCompIso T.hom f).hom)))

lemma relativeSpecBaseChangeOverHomEquiv_comp_right (f : Y ⟶ X)
    {A B : QuasicoherentAlgebra X} (a : B ⟶ A) (T : Over Y)
    (h : T ⟶ (affineSchemeOverForget Y).obj
      ((baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)))) :
    relativeSpecBaseChangeOverHomEquiv f B T
        (h ≫ (affineSchemeOverForget Y).map
          ((baseChangeAffineSchemeOver f).map ((relativeSpec X).map a.op))) =
      relativeSpecBaseChangeOverHomEquiv f A T h ≫
        (affineSchemeOverForget Y).map
          ((relativeSpec Y).map ((pullbackQuasicoherentAlgebra f).map a).op) := by
  let VA : Over X := (affineSchemeOverForget X).obj ((relativeSpec X).obj (op A))
  let VB : Over X := (affineSchemeOverForget X).obj ((relativeSpec X).obj (op B))
  let h₀ : (Over.map f).obj T ⟶ VA := ((Over.mapPullbackAdj f).homEquiv T VA).symm h
  let φ₀ : A.obj ⟶ (T.hom ≫ f).pushforwardStructureAlgebra :=
    relativeSpecOverPushforwardHomEquiv A ((Over.map f).obj T) h₀
  apply (relativeSpecOverPushforwardHomEquiv ((pullbackQuasicoherentAlgebra f).obj B) T).injective
  rw [relativeSpecBaseChangeOverHomEquiv_apply, Equiv.apply_symm_apply,
    relativeSpecOverPushforwardHomEquiv_comp_right,
    relativeSpecBaseChangeOverHomEquiv_apply, Equiv.apply_symm_apply]
  have hadj : ((Over.mapPullbackAdj f).homEquiv T VB).symm
      (h ≫ (Over.pullback f).map ((affineSchemeOverForget X).map ((relativeSpec X).map a.op))) =
      h₀ ≫ (affineSchemeOverForget X).map ((relativeSpec X).map a.op) :=
    Adjunction.homEquiv_naturality_right_symm (Over.mapPullbackAdj f) h
      ((affineSchemeOverForget X).map ((relativeSpec X).map a.op))
  change (pullbackPushforwardCommMonHomEquiv f B T.hom.pushforwardStructureAlgebra).symm
      (relativeSpecOverPushforwardHomEquiv B ((Over.map f).obj T)
        (((Over.mapPullbackAdj f).homEquiv T VB).symm
          (h ≫ (Over.pullback f).map
            ((affineSchemeOverForget X).map ((relativeSpec X).map a.op)))) ≫
        (Scheme.Hom.pushforwardStructureAlgebraCompIso T.hom f).hom) =
    ((pullbackQuasicoherentAlgebra f).map a).hom ≫
      (pullbackPushforwardCommMonHomEquiv f A T.hom.pushforwardStructureAlgebra).symm
        (φ₀ ≫ (Scheme.Hom.pushforwardStructureAlgebraCompIso T.hom f).hom)
  rw [hadj, relativeSpecOverPushforwardHomEquiv_comp_right, Category.assoc,
    pullbackPushforwardCommMonHomEquiv_symm_precomp]

/-- The natural isomorphism of `(Over Y)ᵒᵖ`-presheaves of points between `(Spec_X A) ×_X Y` and
`Spec_Y (f^* A)`. -/
@[expose]
def relativeSpecBaseChangePointsIso (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    yoneda.obj ((affineSchemeOverForget Y).obj
      ((baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)))) ≅
    yoneda.obj ((affineSchemeOverForget Y).obj
      ((relativeSpec Y).obj (op ((pullbackQuasicoherentAlgebra f).obj A)))) :=
  NatIso.ofComponents
    (fun T ↦
      { hom := TypeCat.ofHom (relativeSpecBaseChangeOverHomEquiv f A T.unop)
        inv := TypeCat.ofHom (relativeSpecBaseChangeOverHomEquiv f A T.unop).symm
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro h
          exact (relativeSpecBaseChangeOverHomEquiv f A T.unop).symm_apply_apply h
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro h
          exact (relativeSpecBaseChangeOverHomEquiv f A T.unop).apply_symm_apply h })
    (fun k ↦ by
      apply ConcreteCategory.hom_ext
      intro h
      exact relativeSpecBaseChangeOverHomEquiv_comp_left f A k.unop h)

/-- Base change of `Spec_X A` along `f : Y ⟶ X` is canonically isomorphic in `AffineSchemeOver Y`
to `Spec_Y (f^* A)`. -/
@[expose]
def relativeSpecBaseChangeIso (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    (baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)) ≅
      (relativeSpec Y).obj (op ((pullbackQuasicoherentAlgebra f).obj A)) :=
  ((fullyFaithfulAffineSchemeOverForget Y).comp Yoneda.fullyFaithful).preimageIso
    (relativeSpecBaseChangePointsIso f A)

@[simp]
lemma comp_map_relativeSpecBaseChangeIso_hom (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) (T : Over Y)
    (h : T ⟶ (affineSchemeOverForget Y).obj
      ((baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)))) :
    h ≫ (affineSchemeOverForget Y).map (relativeSpecBaseChangeIso f A).hom =
      relativeSpecBaseChangeOverHomEquiv f A T h :=
  congrArg (fun α ↦ α.app (op T) h)
    (((fullyFaithfulAffineSchemeOverForget Y).comp Yoneda.fullyFaithful).map_preimage
      (relativeSpecBaseChangePointsIso f A).hom)

@[simp]
lemma comp_map_relativeSpecBaseChangeIso_inv (f : Y ⟶ X)
    (A : QuasicoherentAlgebra X) (T : Over Y)
    (h : T ⟶ (affineSchemeOverForget Y).obj
      ((relativeSpec Y).obj (op ((pullbackQuasicoherentAlgebra f).obj A)))) :
    h ≫ (affineSchemeOverForget Y).map (relativeSpecBaseChangeIso f A).inv =
      (relativeSpecBaseChangeOverHomEquiv f A T).symm h :=
  congrArg (fun α ↦ α.app (op T) h)
    (((fullyFaithfulAffineSchemeOverForget Y).comp Yoneda.fullyFaithful).map_preimage
      (relativeSpecBaseChangePointsIso f A).inv)

/-- Relative Spec commutes with base change along `f : Y ⟶ X` up to canonical natural isomorphism
of functors `(QuasicoherentAlgebra X)ᵒᵖ ⥤ AffineSchemeOver Y`. -/
@[expose]
def relativeSpecBaseChangeNatIso (f : Y ⟶ X) :
    relativeSpec X ⋙ baseChangeAffineSchemeOver f ≅
      (pullbackQuasicoherentAlgebra f).op ⋙ relativeSpec Y :=
  NatIso.ofComponents
    (fun A ↦ relativeSpecBaseChangeIso f A.unop)
    (fun {A B} a ↦ by
      apply ((fullyFaithfulAffineSchemeOverForget Y).comp Yoneda.fullyFaithful).map_injective
      refine NatTrans.ext (funext fun T ↦ ?_)
      apply ConcreteCategory.hom_ext
      intro h
      exact (comp_map_relativeSpecBaseChangeIso_hom f B.unop T.unop
        (h ≫ (affineSchemeOverForget Y).map
          ((baseChangeAffineSchemeOver f).map ((relativeSpec X).map a)))).trans
        ((relativeSpecBaseChangeOverHomEquiv_comp_right f a.unop T.unop h).trans
          (congrArg (· ≫ (affineSchemeOverForget Y).map
            ((relativeSpec Y).map ((pullbackQuasicoherentAlgebra f).map a.unop).op))
            (comp_map_relativeSpecBaseChangeIso_hom f A.unop T.unop h).symm)))

@[simp]
lemma relativeSpecBaseChangeNatIso_hom_app (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    (relativeSpecBaseChangeNatIso f).hom.app (op A) = (relativeSpecBaseChangeIso f A).hom :=
  (rfl)

@[simp]
lemma relativeSpecBaseChangeNatIso_inv_app (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    (relativeSpecBaseChangeNatIso f).inv.app (op A) = (relativeSpecBaseChangeIso f A).inv :=
  (rfl)

/-- The canonical projection `Spec_Y (f^* A) ⟶ Spec_X A` induced by the base-change isomorphism
`relativeSpecBaseChangeIso f A`. -/
@[expose]
def relativeSpecBaseChangeFst (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    ((pullbackQuasicoherentAlgebra f).obj A).obj.relativeSpec ⟶ A.obj.relativeSpec :=
  (relativeSpecBaseChangeIso f A).inv.left ≫
    pullback.fst ((relativeSpec X).obj (op A)).hom f

@[reassoc, simp]
lemma relativeSpecBaseChangeIso_hom_left_relativeSpecBaseChangeFst
    (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    (relativeSpecBaseChangeIso f A).hom.left ≫ relativeSpecBaseChangeFst f A =
      pullback.fst ((relativeSpec X).obj (op A)).hom f :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.fst ((relativeSpec X).obj (op A)).hom f)
      (((affineSchemeOverForget Y ⋙ Over.forget Y).mapIso
        (relativeSpecBaseChangeIso f A)).hom_inv_id)).trans
      (Category.id_comp _))

@[reassoc (attr := simp)]
lemma relativeSpecBaseChangeFst_relativeSpecToBase (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    relativeSpecBaseChangeFst f A ≫ A.obj.relativeSpecToBase =
      ((pullbackQuasicoherentAlgebra f).obj A).obj.relativeSpecToBase ≫ f :=
  (Category.assoc _ _ _).trans
    ((congrArg ((relativeSpecBaseChangeIso f A).inv.left ≫ ·)
      (pullback.condition :
        pullback.fst ((relativeSpec X).obj (op A)).hom f ≫ A.obj.relativeSpecToBase =
          pullback.snd ((relativeSpec X).obj (op A)).hom f ≫ f)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f)
          (Over.w ((affineSchemeOverForget Y).map (relativeSpecBaseChangeIso f A).inv)))))

/-- `Spec_Y (f^* A)` forms a pullback square over `Y ⟶ X` with `Spec_X A ⟶ X`. -/
lemma isPullback_relativeSpecBaseChange (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    IsPullback (relativeSpecBaseChangeFst f A)
      ((pullbackQuasicoherentAlgebra f).obj A).obj.relativeSpecToBase
      A.obj.relativeSpecToBase f := by
  let V : AffineSchemeOver X := (relativeSpec X).obj (op A)
  let e : pullback V.hom f ≅
      ((pullbackQuasicoherentAlgebra f).obj A).obj.relativeSpec :=
    (affineSchemeOverForget Y ⋙ Over.forget Y).mapIso (relativeSpecBaseChangeIso f A)
  have hw : (relativeSpecBaseChangeIso f A).hom.left ≫
      ((pullbackQuasicoherentAlgebra f).obj A).obj.relativeSpecToBase =
      pullback.snd V.hom f :=
    Over.w ((affineSchemeOverForget Y).map (relativeSpecBaseChangeIso f A).hom)
  exact IsPullback.of_iso (IsPullback.of_hasPullback V.hom f)
    e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans
      (relativeSpecBaseChangeIso_hom_left_relativeSpecBaseChangeFst f A).symm)
    ((Category.comp_id _).trans hw.symm)
    (Category.id_comp _).symm
    (Category.id_comp _).symm

end

end TauCeti.AlgebraicGeometry

end
