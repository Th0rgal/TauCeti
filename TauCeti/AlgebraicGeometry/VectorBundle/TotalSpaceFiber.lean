/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk
public import TauCeti.AlgebraicGeometry.Modules.Stalk
public import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
public import TauCeti.AlgebraicGeometry.VectorBundle.Rank
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpaceBaseChange
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpaceFree

/-!
# Fibers of the total space of a finite locally free sheaf

For a finite locally free sheaf `E` on a scheme `X` and a point `x : X` with residue field `κ(x)`,
we define:
* `TauCeti.AlgebraicGeometry.moduleFiber E x`: the fiber `κ(x) ⊗_{𝒪_{X,x}} E_x` of `E` at `x` as
  an object of `ModuleCat (X.residueField x)`;
* `TauCeti.AlgebraicGeometry.affineSpaceOfModuleFiber E x`: the affine space
  `Spec (Sym_{κ(x)}((moduleFiber E x)^∨))` over `Spec κ(x)` associated to the dual of the module
  fiber;
* `TauCeti.AlgebraicGeometry.totalSpaceFiberIso E x`: canonical isomorphism in
  `Over (Spec (X.residueField x))` between the scheme-theoretic fiber of the total space `V(E)` over
  `x` and `affineSpaceOfModuleFiber E x`.
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- Extension of the module stalk `E_x` to the residue field `κ(x)`. -/
@[expose]
noncomputable def moduleFiber {X : Scheme.{u}} (E : FiniteLocallyFreeSheaf X) (x : X) :
    ModuleCat (X.residueField x) :=
  letI := (X.residue x).hom.toAlgebra
  ModuleCat.of (X.residueField x)
    (TensorProduct (X.presheaf.stalk x) (X.residueField x) (E.obj.presheaf.stalk x))

/-- The affine space `Spec (Sym_{κ(x)}((moduleFiber E x)^∨))` over `Spec κ(x)` associated to the
dual of `moduleFiber E x`. -/
@[expose]
noncomputable def affineSpaceOfModuleFiber {X : Scheme.{u}}
    (E : FiniteLocallyFreeSheaf X) (x : X) : Over (Spec (X.residueField x)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x)
    (SymmetricAlgebra (X.residueField x)
      (Module.Dual (X.residueField x) (moduleFiber E x))))))

/-- Bijection between `CommMon Y.Modules` morphisms out of `Sym_Y(f^* M)` and out of `f^*(Sym_X M)`
for a quasi-coherent sheaf `M` on `X`. -/
@[expose]
noncomputable def symmetricAlgebraBaseChangeHomEquiv {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : QuasicoherentSheaf X) (C : CommMon Y.Modules) :
    (((symmetricAlgebra Y).obj ((pullbackQuasicoherent f).obj M)).obj ⟶ C) ≃
      (((pullbackQuasicoherentAlgebra f).obj ((symmetricAlgebra X).obj M)).obj ⟶ C) :=
  (symmetricAlgebraCommMonHomEquiv ((pullbackQuasicoherent f).obj M).obj C).trans <|
    (Iso.homCongr (eqToIso (QuasicoherentSheaf.pullback_obj_obj f M)) (Iso.refl C.X)).trans <|
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M.obj C.X).trans <|
    (symmetricAlgebraCommMonHomEquiv M.obj
      ((Scheme.Modules.pushforward f).mapCommMon.obj C)).symm.trans <|
    (pullbackPushforwardCommMonHomEquiv f ((symmetricAlgebra X).obj M) C).symm

private lemma symmetricAlgebraBaseChangeHomEquiv_postcomp {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : QuasicoherentSheaf X) {C D : CommMon Y.Modules}
    (φ : ((symmetricAlgebra Y).obj ((pullbackQuasicoherent f).obj M)).obj ⟶ C) (m : C ⟶ D) :
    symmetricAlgebraBaseChangeHomEquiv f M D (φ ≫ m) =
      symmetricAlgebraBaseChangeHomEquiv f M C φ ≫ m := by
  let hEq : ((pullbackQuasicoherent f).obj M).obj = (Scheme.Modules.pullback f).obj M.obj :=
    QuasicoherentSheaf.pullback_obj_obj f M
  let u₀ : ((pullbackQuasicoherent f).obj M).obj ⟶ C.X :=
    symmetricAlgebraCommMonHomEquiv ((pullbackQuasicoherent f).obj M).obj C φ
  let u₁ : (Scheme.Modules.pullback f).obj M.obj ⟶ C.X := eqToHom hEq.symm ≫ u₀
  let v₀ : M.obj ⟶ (Scheme.Modules.pushforward f).obj C.X :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M.obj C.X u₁
  let ψ₀ : ((symmetricAlgebra X).obj M).obj ⟶ (Scheme.Modules.pushforward f).mapCommMon.obj C :=
    (symmetricAlgebraCommMonHomEquiv M.obj
      ((Scheme.Modules.pushforward f).mapCommMon.obj C)).symm v₀
  have h1 : eqToHom hEq.symm ≫
        symmetricAlgebraCommMonHomEquiv ((pullbackQuasicoherent f).obj M).obj D (φ ≫ m) ≫
        𝟙 D.X =
      u₁ ≫ m.hom.hom :=
    (congrArg (eqToHom hEq.symm ≫ ·)
      ((comp_id _).trans
        (symmetricAlgebraCommMonHomEquiv_postcomp ((pullbackQuasicoherent f).obj M).obj φ m))).trans
      (assoc (eqToHom hEq.symm) u₀ m.hom.hom).symm
  have h2 : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M.obj D.X
        (u₁ ≫ m.hom.hom) =
      v₀ ≫ (Scheme.Modules.pushforward f).map m.hom.hom :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right u₁ m.hom.hom
  have h3 : (symmetricAlgebraCommMonHomEquiv M.obj
        ((Scheme.Modules.pushforward f).mapCommMon.obj D)).symm
        (v₀ ≫ (Scheme.Modules.pushforward f).map m.hom.hom) =
      ψ₀ ≫ (Scheme.Modules.pushforward f).mapCommMon.map m := by
    apply (symmetricAlgebraCommMonHomEquiv M.obj
      ((Scheme.Modules.pushforward f).mapCommMon.obj D)).injective
    exact (Equiv.apply_symm_apply _ _).trans
      ((congrArg (· ≫ (Scheme.Modules.pushforward f).map m.hom.hom)
        (Equiv.apply_symm_apply _ v₀).symm).trans
        (symmetricAlgebraCommMonHomEquiv_postcomp M.obj ψ₀
          ((Scheme.Modules.pushforward f).mapCommMon.map m)).symm)
  have hu₁ : eqToHom hEq.symm ≫ u₀ ≫ 𝟙 C.X = u₁ :=
    congrArg (eqToHom hEq.symm ≫ ·) (comp_id u₀)
  exact (congrArg
    (fun w ↦ (pullbackPushforwardCommMonHomEquiv f ((symmetricAlgebra X).obj M) D).symm
      ((symmetricAlgebraCommMonHomEquiv M.obj
        ((Scheme.Modules.pushforward f).mapCommMon.obj D)).symm
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M.obj D.X w))) h1).trans
    ((congrArg
      (fun w ↦ (pullbackPushforwardCommMonHomEquiv f ((symmetricAlgebra X).obj M) D).symm
        ((symmetricAlgebraCommMonHomEquiv M.obj
          ((Scheme.Modules.pushforward f).mapCommMon.obj D)).symm w)) h2).trans
      ((congrArg
        (pullbackPushforwardCommMonHomEquiv f ((symmetricAlgebra X).obj M) D).symm h3).trans
        ((pullbackPushforwardCommMonHomEquiv_symm_postcomp f
          ((symmetricAlgebra X).obj M) m ψ₀).trans
          (congrArg
            (fun w ↦ (pullbackPushforwardCommMonHomEquiv f ((symmetricAlgebra X).obj M) C).symm
              ((symmetricAlgebraCommMonHomEquiv M.obj
                ((Scheme.Modules.pushforward f).mapCommMon.obj C)).symm
                ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M.obj C.X w)) ≫ m)
            hu₁.symm))))

/-- Pullback of quasi-coherent algebras commutes with forming the symmetric algebra of a
quasi-coherent sheaf. -/
noncomputable def symmetricAlgebraBaseChangeIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : QuasicoherentSheaf X) :
    (pullbackQuasicoherentAlgebra f).obj ((symmetricAlgebra X).obj M) ≅
      (symmetricAlgebra Y).obj ((pullbackQuasicoherent f).obj M) := by
  let A₁ : CommMon Y.Modules :=
    ((pullbackQuasicoherentAlgebra f).obj ((symmetricAlgebra X).obj M)).obj
  let A₂ : CommMon Y.Modules := ((symmetricAlgebra Y).obj ((pullbackQuasicoherent f).obj M)).obj
  let eCoyo : coyoneda.obj (op A₂) ≅ coyoneda.obj (op A₁) :=
    NatIso.ofComponents
      (fun C ↦
        { hom := TypeCat.ofHom (symmetricAlgebraBaseChangeHomEquiv f M C)
          inv := TypeCat.ofHom (symmetricAlgebraBaseChangeHomEquiv f M C).symm
          hom_inv_id := by
            apply ConcreteCategory.hom_ext
            intro φ
            exact (symmetricAlgebraBaseChangeHomEquiv f M C).symm_apply_apply φ
          inv_hom_id := by
            apply ConcreteCategory.hom_ext
            intro φ
            exact (symmetricAlgebraBaseChangeHomEquiv f M C).apply_symm_apply φ })
      (fun m ↦ by
        apply ConcreteCategory.hom_ext
        intro φ
        exact symmetricAlgebraBaseChangeHomEquiv_postcomp f M φ m)
  let eCommMon : A₁ ≅ A₂ := (Coyoneda.fullyFaithful.preimageIso eCoyo).unop
  exact ObjectProperty.isoMk _ eCommMon

/-- Base change of `totalSpaceScheme X` along `f : Y ⟶ X` is canonically isomorphic to
`totalSpaceScheme Y` of the pulled-back bundle. -/
noncomputable def totalSpaceSchemeBaseChangeIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : FiniteLocallyFreeSheaf X) :
    (baseChangeAffineSchemeOver f).obj ((totalSpaceScheme X).obj E) ≅
      (totalSpaceScheme Y).obj ((pullbackFiniteLocallyFree f).obj E) :=
  relativeSpecBaseChangeIso f
      ((symmetricAlgebra X).obj ((dualAsQuasicoherentOp X).obj E).unop) ≪≫
    (relativeSpec Y).mapIso
      (symmetricAlgebraBaseChangeIso f
        ((dualAsQuasicoherentOp X).obj E).unop).op.symm ≪≫
    (linearSpecScheme Y).mapIso
      ((pullbackFiniteLocallyFreeToQuasicoherentIso f (FiniteLocallyFreeSheaf.dual E) ≪≫
        (finiteLocallyFreeToQuasicoherent Y).mapIso
          (FiniteLocallyFreeSheaf.pullbackDualIso f E)).op.symm)

/-- Reindex a free sheaf of modules along an equivalence of index types. -/
private noncomputable def freeReindexIso {X : Scheme.{u}} {I J : Type u} (e : I ≃ J) :
    (_root_.SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ≅
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) J : X.Modules) :=
  let hI := _root_.SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I
  let hJ := _root_.SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) J
  let hom : (_root_.SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⟶
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) J : X.Modules) :=
    Cofan.IsColimit.desc hI (fun i ↦ _root_.SheafOfModules.ιFree (R := X.ringCatSheaf) (e i))
  let inv : (_root_.SheafOfModules.free (R := X.ringCatSheaf) J : X.Modules) ⟶
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) :=
    Cofan.IsColimit.desc hJ (fun j ↦ _root_.SheafOfModules.ιFree (R := X.ringCatSheaf) (e.symm j))
  { hom := hom
    inv := inv
    hom_inv_id :=
      Cofan.IsColimit.hom_ext hI (hom ≫ inv) (𝟙 _) fun i ↦
        (assoc (_root_.SheafOfModules.ιFree (R := X.ringCatSheaf) i) hom inv).symm.trans
          ((congrArg (· ≫ inv) (Cofan.IsColimit.fac hI _ i)).trans
            ((Cofan.IsColimit.fac hJ _ (e i)).trans
              ((congrArg (_root_.SheafOfModules.ιFree (R := X.ringCatSheaf))
                (e.symm_apply_apply i)).trans
                (comp_id _).symm)))
    inv_hom_id :=
      Cofan.IsColimit.hom_ext hJ (inv ≫ hom) (𝟙 _) fun j ↦
        (assoc (_root_.SheafOfModules.ιFree (R := X.ringCatSheaf) j) inv hom).symm.trans
          ((congrArg (· ≫ hom) (Cofan.IsColimit.fac hJ _ j)).trans
            ((Cofan.IsColimit.fac hI _ (e.symm j)).trans
              ((congrArg (_root_.SheafOfModules.ιFree (R := X.ringCatSheaf))
                (e.apply_symm_apply j)).trans
                (comp_id _).symm))) }

/-- Given a local basis `σ` of `E` over an open neighbourhood `U` of `x`, the pullback of `E`
along `X.fromSpecResidueField x` is isomorphic to the standard free bundle of rank `E.rank x` on
`Spec (X.residueField x)`. -/
private noncomputable def pullbackFromSpecResidueFieldIso {X : Scheme.{u}}
    (E : FiniteLocallyFreeSheaf X) (x : X) :
    (pullbackFiniteLocallyFree (X.fromSpecResidueField x)).obj E ≅
      freeFiniteLocallyFree (Spec (X.residueField x)) (E.rank x) := by
  let U : X.Opens := (E.exists_generatingSections x).choose
  have hx : x ∈ U := (E.exists_generatingSections x).choose_spec.choose
  let σ : (E.obj.over U).GeneratingSections :=
    (E.exists_generatingSections x).choose_spec.choose_spec.choose
  have hσ : IsIso σ.π :=
    (E.exists_generatingSections x).choose_spec.choose_spec.choose_spec.1
  have hI : Finite σ.I :=
    (E.exists_generatingSections x).choose_spec.choose_spec.choose_spec.2
  let f : Spec (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hrange : Set.range f ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecResidueField, U.range_ι, Set.singleton_subset_iff]
    exact hx
  let g : Spec (X.residueField x) ⟶ U.toScheme := IsOpenImmersion.lift U.ι f hrange
  have hg : g ≫ U.ι = f := IsOpenImmersion.lift_fac U.ι f hrange
  let eσ : _root_.SheafOfModules.free σ.I ≅ E.obj.over U := @asIso _ _ _ _ σ.π hσ
  let eU : (Scheme.Modules.pullback U.ι).obj E.obj ≅ _root_.SheafOfModules.free σ.I :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app E.obj).symm ≪≫
      Scheme.Modules.restrictIsoFreeOfOverIsoFree E.obj U eσ.symm
  let : (_root_.SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward g).IsRightAdjoint
  let eg : (Scheme.Modules.pullback g).obj (_root_.SheafOfModules.free σ.I) ≅
      _root_.SheafOfModules.free σ.I :=
    _root_.SheafOfModules.pullbackObjFreeIso g.toRingCatSheafHom σ.I
  let eI : σ.I ≃ ULift.{u} (Fin (E.rank x)) :=
    (Finite.equivFinOfCardEq (E.rank_apply_eq_natCard hx σ).symm).trans Equiv.ulift.symm
  let eReindex : _root_.SheafOfModules.free (R := (Spec (X.residueField x)).ringCatSheaf) σ.I ≅
      (freeFiniteLocallyFree (Spec (X.residueField x)) (E.rank x)).obj :=
    freeReindexIso eI
  exact ObjectProperty.isoMk (Scheme.Modules.isFiniteLocallyFree (Spec (X.residueField x)))
    (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj f E) ≪≫
      (Scheme.Modules.pullbackCongr hg.symm).app E.obj ≪≫
      (Scheme.Modules.pullbackComp g U.ι).symm.app E.obj ≪≫
      (Scheme.Modules.pullback g).mapIso eU ≪≫
      eg ≪≫
      eReindex)

private abbrev modulePresheaf {X : Scheme.{u}} (M : X.Modules) :
    _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u}) :=
  M.val

private noncomputable def stalkLinearFormOfOverHomSection {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hxU : x ∈ U)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hxV : x ∈ V) :
    (modulePresheaf M).obj (op V) →+ ↑(X.presheaf.stalk x) :=
  AddMonoidHom.mk'
    (fun m ↦ X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩
      (φ.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))
        ((modulePresheaf M).map (homOfLE inf_le_left : V ⊓ U ⟶ V).op m)))
    (fun a b ↦ (congrArg (fun t ↦ X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩
      (φ.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U))) t))
        (((modulePresheaf M).map (homOfLE inf_le_left : V ⊓ U ⟶ V).op).hom.map_add a b)).trans
          ((congrArg (X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩)
            ((φ.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom.map_add _ _)).trans
              (map_add (X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩).hom _ _)))

private lemma stalkLinearFormOfOverHomSection_res {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hxU : x ∈ U)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    {V W : X.Opens} (i : V ⟶ W) (hxV : x ∈ V) (m : (modulePresheaf M).obj (op W)) :
    stalkLinearFormOfOverHomSection M x U hxU φ V hxV ((modulePresheaf M).map i.op m) =
      stalkLinearFormOfOverHomSection M x U hxU φ W (i.le hxV) m := by
  let P := modulePresheaf M
  let j : V ⊓ U ⟶ W ⊓ U := homOfLE (inf_le_inf i.le le_rfl)
  let k : Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U) ⟶
      Over.mk (homOfLE inf_le_right : W ⊓ U ⟶ U) := Over.homMk j
  have hm : P.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op (P.map i.op m) =
      P.map j.op (P.map (homOfLE inf_le_left : W ⊓ U ⟶ W).op m) := by
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    rfl
  exact (congrArg (fun t ↦ X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩
    (φ.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U))) t)) hm).trans
      ((congrArg (X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩)
        (PresheafOfModules.naturality_apply φ.val k.op _)).trans
          (X.presheaf.germ_res_apply j x ⟨hxV, hxU⟩ _))

private lemma stalkLinearFormOfOverHomSection_smul {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hxU : x ∈ U)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hxV : x ∈ V) (r : X.presheaf.obj (op V))
    (m : (modulePresheaf M).obj (op V)) :
    stalkLinearFormOfOverHomSection M x U hxU φ V hxV (r • m) =
      X.presheaf.germ V x hxV r • stalkLinearFormOfOverHomSection M x U hxU φ V hxV m := by
  let P := modulePresheaf M
  let iV : V ⊓ U ⟶ V := homOfLE inf_le_left
  let iU : V ⊓ U ⟶ U := homOfLE inf_le_right
  let r' : Γ(X, V ⊓ U) := X.presheaf.map iV.op r
  let s : Γ(X, V ⊓ U) := φ.val.app (op (Over.mk iU)) (P.map iV.op m)
  refine (congrArg (fun t ↦ X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩
    (φ.val.app (op (Over.mk iU)) t)) (P.map_smul iV.op r m)).trans ?_
  refine (congrArg (X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩)
    ((φ.val.app (op (Over.mk iU))).hom.map_smul r' (P.map iV.op m))).trans ?_
  exact (map_mul (X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩).hom r' s).trans
    (congrArg (· * X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩ s)
      (X.presheaf.germ_res_apply iV x ⟨hxV, hxU⟩ r))

/-- A local linear form `M.over U ⟶ unit` over an open neighbourhood `U` of `x` induces an
`𝒪_{X,x}`-linear form on the module stalk `M_x`. -/
private noncomputable def stalkLinearFormOfOverHom {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hxU : x ∈ U)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ↑(M.presheaf.stalk x) →ₗ[X.presheaf.stalk x] ↑(X.presheaf.stalk x) :=
  (modulePresheaf M).stalkLiftCommRing (S := X.presheaf) x
    (stalkLinearFormOfOverHomSection M x U hxU φ)
    (stalkLinearFormOfOverHomSection_res M x U hxU φ)
    (stalkLinearFormOfOverHomSection_smul M x U hxU φ)

private lemma stalkLinearFormOfOverHom_germ {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hxU : x ∈ U)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : (modulePresheaf M).obj (op U)) :
    stalkLinearFormOfOverHom M x U hxU φ
        (TopCat.Presheaf.germ (modulePresheaf M).presheaf U x hxU m) =
      X.presheaf.germ U x hxU (φ.val.app (op (Over.mk (𝟙 U))) m) := by
  let P := modulePresheaf M
  let k : Over.mk (homOfLE inf_le_right : U ⊓ U ⟶ U) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE inf_le_left)
  have hg : stalkLinearFormOfOverHom M x U hxU φ
        (TopCat.Presheaf.germ P.presheaf U x hxU m) =
      X.presheaf.germ (U ⊓ U) x ⟨hxU, hxU⟩
        (φ.val.app (op (Over.mk (homOfLE inf_le_right : U ⊓ U ⟶ U)))
          (P.map (homOfLE inf_le_left : U ⊓ U ⟶ U).op m)) :=
    P.stalkLiftCommRing_germ (S := X.presheaf) x
      (stalkLinearFormOfOverHomSection M x U hxU φ)
      (stalkLinearFormOfOverHomSection_res M x U hxU φ)
      (stalkLinearFormOfOverHomSection_smul M x U hxU φ) U hxU m
  exact hg.trans ((congrArg (X.presheaf.germ (U ⊓ U) x ⟨hxU, hxU⟩)
    (PresheafOfModules.naturality_apply φ.val k.op m)).trans
      (X.presheaf.germ_res_apply (homOfLE inf_le_left) x ⟨hxU, hxU⟩ _))

/-- Extend an `R`-linear form `M →ₗ[R] R` to a `k`-linear form `(k ⊗[R] M) →ₗ[k] k`. -/
private noncomputable def baseChangeLinearForm {R k M : Type u} [CommRing R] [CommRing k]
    [Algebra R k] [AddCommGroup M] [Module R M] (c : M →ₗ[R] R) :
    TensorProduct R k M →ₗ[k] k :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • ((Algebra.ofId R k).toLinearMap.comp c)
      map_add' a b := by
        ext m
        exact add_smul a b (algebraMap R k (c m))
      map_smul' r a := by
        ext m
        exact mul_smul r a (algebraMap R k (c m)) }

@[simp]
private lemma baseChangeLinearForm_tmul {R k M : Type u} [CommRing R] [CommRing k]
    [Algebra R k] [AddCommGroup M] [Module R M] (c : M →ₗ[R] R) (a : k) (m : M) :
    baseChangeLinearForm c (a ⊗ₜ[R] m) = a * algebraMap R k (c m) :=
  rfl

/-- Given generators `g : I → M` spanning `M` over `R` and dual linear forms `c : I → (M →ₗ[R] R)`
satisfying `c i (g j) = δ_{j,i}`, the `k`-dual `Module.Dual k (k ⊗[R] M)` is `k`-linearly
equivalent to `I → k`. -/
private noncomputable def dualTensorProductEquivOfDualGenerators {R k M I : Type u}
    [CommRing R] [CommRing k] [Algebra R k] [AddCommGroup M] [Module R M]
    [Fintype I] [DecidableEq I]
    (g : I → M) (hspan : Submodule.span R (Set.range g) = ⊤)
    (c : I → (M →ₗ[R] R)) (hc : ∀ j i : I, c i (g j) = if j = i then 1 else 0) :
    Module.Dual k (TensorProduct R k M) ≃ₗ[k] (I → k) where
  toFun φ i := φ ((1 : k) ⊗ₜ[R] g i)
  map_add' φ ψ := rfl
  map_smul' a φ := rfl
  invFun v := ∑ i : I, v i • baseChangeLinearForm (c i)
  left_inv φ := by
    have hright : ∀ v : I → k,
        (fun j ↦ (∑ i : I, v i • baseChangeLinearForm (c i)) ((1 : k) ⊗ₜ[R] g j)) = v := by
      intro v
      funext j
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, baseChangeLinearForm_tmul,
        hc j, smul_eq_mul, one_mul]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Ne.symm hij]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hg : ∀ j : I,
        (∑ i : I, φ ((1 : k) ⊗ₜ[R] g i) • baseChangeLinearForm (c i)) ((1 : k) ⊗ₜ[R] g j) =
          φ ((1 : k) ⊗ₜ[R] g j) :=
      fun j ↦ congrFun (hright (fun i ↦ φ ((1 : k) ⊗ₜ[R] g i))) j
    have hm : ∀ m : M,
        (∑ i : I, φ ((1 : k) ⊗ₜ[R] g i) • baseChangeLinearForm (c i)) ((1 : k) ⊗ₜ[R] m) =
          φ ((1 : k) ⊗ₜ[R] m) := by
      intro m
      have hm_top : m ∈ Submodule.span R (Set.range g) := hspan.symm ▸ Submodule.mem_top
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hm_top
      have htmul : ((1 : k) ⊗ₜ[R] (∑ j : I, a j • g j)) =
          ∑ j : I, algebraMap R k (a j) • ((1 : k) ⊗ₜ[R] g j) := by
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [htmul, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [LinearMap.map_smul, LinearMap.map_smul, hg j]
    apply LinearMap.restrictScalars_injective R
    refine TensorProduct.ext' fun a m ↦ ?_
    change (∑ i : I, φ ((1 : k) ⊗ₜ[R] g i) • baseChangeLinearForm (c i)) (a ⊗ₜ[R] m) =
      φ (a ⊗ₜ[R] m)
    have ha : (a ⊗ₜ[R] m) = a • ((1 : k) ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ha, LinearMap.map_smul, LinearMap.map_smul, hm m]
  right_inv v := by
    funext j
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, baseChangeLinearForm_tmul,
      hc j, smul_eq_mul, one_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

/-- A `k`-linear equivalence `W ≃ₗ[k] (I → k)` induces a `k`-algebra equivalence
`SymmetricAlgebra k W ≃ₐ[k] MvPolynomial I k`. -/
private noncomputable def symmetricAlgebraEquivMvPolynomialOfLinearEquivPi {k W I : Type u}
    [CommSemiring k] [AddCommMonoid W] [Module k W] [Fintype I] [DecidableEq I]
    (eW : W ≃ₗ[k] (I → k)) :
    SymmetricAlgebra k W ≃ₐ[k] MvPolynomial I k := by
  let wToMvPoly : W →ₗ[k] MvPolynomial I k :=
    { toFun w := ∑ i : I, eW w i • MvPolynomial.X i
      map_add' w₁ w₂ := by
        simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' c w := by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul,
          Finset.smul_sum] }
  let toMvPoly : SymmetricAlgebra k W →ₐ[k] MvPolynomial I k :=
    SymmetricAlgebra.lift wToMvPoly
  let fromMvPoly : MvPolynomial I k →ₐ[k] SymmetricAlgebra k W :=
    MvPolynomial.aeval (fun i : I ↦ SymmetricAlgebra.ι k W (eW.symm (Pi.single i 1)))
  refine AlgEquiv.ofAlgHom toMvPoly fromMvPoly ?_ ?_
  · apply MvPolynomial.algHom_ext
    intro i
    change toMvPoly (fromMvPoly (MvPolynomial.X i)) = MvPolynomial.X i
    dsimp only [fromMvPoly, toMvPoly]
    rw [MvPolynomial.aeval_X, SymmetricAlgebra.lift_ι_apply]
    change ∑ j : I, eW (eW.symm (Pi.single i 1)) j • MvPolynomial.X j = MvPolynomial.X i
    rw [eW.apply_symm_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · apply SymmetricAlgebra.algHom_ext
    ext w
    change fromMvPoly (toMvPoly (SymmetricAlgebra.ι k W w)) = SymmetricAlgebra.ι k W w
    dsimp only [toMvPoly]
    rw [SymmetricAlgebra.lift_ι_apply]
    change fromMvPoly (∑ i : I, eW w i • MvPolynomial.X i) = SymmetricAlgebra.ι k W w
    rw [map_sum]
    have hsum : (∑ i : I, fromMvPoly (eW w i • MvPolynomial.X i)) =
        SymmetricAlgebra.ι k W (eW.symm (∑ i : I, eW w i • Pi.single i 1)) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      dsimp only [fromMvPoly]
      rw [map_smul, MvPolynomial.aeval_X, LinearEquiv.map_smul, LinearMap.map_smul]
    have hpi : (∑ i : I, eW w i • Pi.single i (1 : k)) = eW w := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij.symm]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hsum, hpi, eW.symm_apply_apply]

/-- The dual of the module fiber `moduleFiber E x` is `κ(x)`-linearly equivalent to
`ULift.{u} (Fin (E.rank x)) → X.residueField x`. -/
private noncomputable def dualModuleFiberEquivPi {X : Scheme.{u}}
    (E : FiniteLocallyFreeSheaf X) (x : X) :
    letI := (X.residue x).hom.toAlgebra
    Module.Dual (X.residueField x) (moduleFiber E x) ≃ₗ[X.residueField x]
      (ULift.{u} (Fin (E.rank x)) → X.residueField x) := by
  letI := (X.residue x).hom.toAlgebra
  let U : X.Opens := (E.exists_generatingSections x).choose
  have hx : x ∈ U := (E.exists_generatingSections x).choose_spec.choose
  let σ : (E.obj.over U).GeneratingSections :=
    (E.exists_generatingSections x).choose_spec.choose_spec.choose
  have hσ : IsIso σ.π :=
    (E.exists_generatingSections x).choose_spec.choose_spec.choose_spec.1
  have hI : Finite σ.I :=
    (E.exists_generatingSections x).choose_spec.choose_spec.choose_spec.2
  have : Fintype σ.I := Fintype.ofFinite σ.I
  letI : DecidableEq σ.I := Classical.decEq σ.I
  let eσ : _root_.SheafOfModules.free σ.I ≅ E.obj.over U := @asIso _ _ _ _ σ.π hσ
  let p (i : σ.I) : _root_.SheafOfModules.free σ.I ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U) :=
    Cofan.IsColimit.desc (_root_.SheafOfModules.isColimitFreeCofan σ.I)
      (fun j ↦ if j = i then 𝟙 _ else 0)
  let g (j : σ.I) : E.obj.presheaf.stalk x :=
    TopCat.Presheaf.germ E.obj.val.presheaf U x hx ((σ.s j).val (op (Over.mk (𝟙 U))))
  have hspan : Submodule.span (X.presheaf.stalk x) (Set.range g) = ⊤ :=
    SheafOfModules.GeneratingSections.span_germ_eq_top (R := X.sheaf) σ hx
  let c (i : σ.I) : E.obj.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    stalkLinearFormOfOverHom E.obj x U hx (eσ.inv ≫ p i)
  have hc (j i : σ.I) : c i (g j) = if j = i then 1 else 0 := by
    have hgerm : c i (g j) =
        X.presheaf.germ U x hx
          ((eσ.inv ≫ p i).val.app (op (Over.mk (𝟙 U))) ((σ.s j).val (op (Over.mk (𝟙 U))))) :=
      stalkLinearFormOfOverHom_germ E.obj x U hx (eσ.inv ≫ p i) ((σ.s j).val (op (Over.mk (𝟙 U))))
    have hsj : (σ.s j).val (op (Over.mk (𝟙 U))) =
        (_root_.SheafOfModules.ιFree j ≫ σ.π).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)) :=
      congrArg (fun t : (E.obj.over U).sections ↦ t.val (op (Over.mk (𝟙 U))))
        (_root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection σ.s j).symm
    have hcomp : (_root_.SheafOfModules.ιFree j ≫ σ.π) ≫ eσ.inv ≫ p i =
        if j = i then 𝟙 _ else 0 :=
      (Category.assoc _ _ _).trans
        ((congrArg (_root_.SheafOfModules.ιFree j ≫ ·) (Iso.hom_inv_id_assoc eσ (p i))).trans
          (Cofan.IsColimit.fac (_root_.SheafOfModules.isColimitFreeCofan σ.I) _ j))
    have happ : (eσ.inv ≫ p i).val.app (op (Over.mk (𝟙 U))) ((σ.s j).val (op (Over.mk (𝟙 U)))) =
        (if j = i then 𝟙 (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)) else 0).val.app
          (op (Over.mk (𝟙 U))) (1 : Γ(X, U)) :=
      (congrArg ((eσ.inv ≫ p i).val.app (op (Over.mk (𝟙 U)))) hsj).trans
        (congrArg (fun ψ : _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
            _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ↦
          ψ.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) hcomp)
    refine hgerm.trans ((congrArg (X.presheaf.germ U x hx) happ).trans ?_)
    split_ifs with hji
    · exact map_one (X.presheaf.germ U x hx).hom
    · exact map_zero (X.presheaf.germ U x hx).hom
  let eI : σ.I ≃ ULift.{u} (Fin (E.rank x)) :=
    (Finite.equivFinOfCardEq (E.rank_apply_eq_natCard hx σ).symm).trans Equiv.ulift.symm
  exact (dualTensorProductEquivOfDualGenerators g hspan c hc).trans
    (LinearEquiv.funCongrLeft (X.residueField x) (X.residueField x) eI.symm)

/-- The scheme-theoretic fiber of the total space `(totalSpaceScheme X).obj E` over `x : X` is
canonically isomorphic in `Over (Spec (X.residueField x))` to `affineSpaceOfModuleFiber E x`. -/
noncomputable def totalSpaceFiberIso {X : Scheme.{u}}
    (E : FiniteLocallyFreeSheaf X) (x : X) :
    Over.mk (((affineSchemeOverForget X).obj
      ((totalSpaceScheme X).obj E)).hom.fiberToSpecResidueField x) ≅
      affineSpaceOfModuleFiber E x := by
  let eBase : Over.mk (((affineSchemeOverForget X).obj
        ((totalSpaceScheme X).obj E)).hom.fiberToSpecResidueField x) ≅
      (affineSchemeOverForget (Spec (X.residueField x))).obj
        ((totalSpaceScheme (Spec (X.residueField x))).obj
          ((pullbackFiniteLocallyFree (X.fromSpecResidueField x)).obj E)) :=
    (affineSchemeOverForget (Spec (X.residueField x))).mapIso
      (totalSpaceSchemeBaseChangeIso (X.fromSpecResidueField x) E)
  let eTriv : (affineSchemeOverForget (Spec (X.residueField x))).obj
        ((totalSpaceScheme (Spec (X.residueField x))).obj
          ((pullbackFiniteLocallyFree (X.fromSpecResidueField x)).obj E)) ≅
      (affineSchemeOverForget (Spec (X.residueField x))).obj
        (affineSpaceOver (Spec (X.residueField x)) (E.rank x)) :=
    (affineSchemeOverForget (Spec (X.residueField x))).mapIso
      ((totalSpaceScheme (Spec (X.residueField x))).mapIso
        (pullbackFromSpecResidueFieldIso E x) ≪≫
        totalSpaceFreeIso (Spec (X.residueField x)) (E.rank x))
  let eSpec : (affineSchemeOverForget (Spec (X.residueField x))).obj
        (affineSpaceOver (Spec (X.residueField x)) (E.rank x)) ≅
      Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : X.residueField x →+*
          MvPolynomial (ULift.{u} (Fin (E.rank x))) (X.residueField x)))) :=
    (Over.isoMk (AffineSpace.SpecIso (n := ULift.{u} (Fin (E.rank x))) (X.residueField x)).symm
      (AffineSpace.SpecIso_inv_over (n := ULift.{u} (Fin (E.rank x))) (X.residueField x))).symm
  let eAlg : SymmetricAlgebra (X.residueField x)
        (Module.Dual (X.residueField x) (moduleFiber E x)) ≃ₐ[X.residueField x]
      MvPolynomial (ULift.{u} (Fin (E.rank x))) (X.residueField x) :=
    symmetricAlgebraEquivMvPolynomialOfLinearEquivPi (dualModuleFiberEquivPi E x)
  let eSym : Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : X.residueField x →+*
          MvPolynomial (ULift.{u} (Fin (E.rank x))) (X.residueField x)))) ≅
      affineSpaceOfModuleFiber E x :=
    Over.isoMk (Scheme.Spec.mapIso eAlg.toRingEquiv.toCommRingCatIso.op)
      ((Spec.map_comp
        (CommRingCat.ofHom (algebraMap (X.residueField x)
          (SymmetricAlgebra (X.residueField x)
            (Module.Dual (X.residueField x) (moduleFiber E x)))))
        eAlg.toRingEquiv.toCommRingCatIso.hom).symm.trans
        (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun c ↦ eAlg.commutes c))))
  exact eBase ≪≫ eTriv ≪≫ eSpec ≪≫ eSym

end

end TauCeti.AlgebraicGeometry
