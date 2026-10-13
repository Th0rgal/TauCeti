/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Affine
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# Affine pullback of symmetric powers

For a ring map `φ : R ⟶ S`, pullback along `Spec φ` commutes with symmetric powers of the
sheaf associated with any `R`-module. The comparison is natural in the module and does not
require flatness, finite presentation, or local freeness. It combines the affine computation
of symmetric powers with the identification of pullback with extension of scalars.

This is the affine calculation used to descend symmetric-power pullback comparisons on schemes.
It includes finite projective modules and therefore the affine charts of finite locally free
sheaves. The forward component is characterized as the composite of the affine comparisons and
the scalar-extension map, whose value on a pure tensor is explicit in
`TauCeti.coe_extendScalarsSymmetricPowerIso_hom_tmul`.

## References

* The Stacks Project, Lemma 10.13.6 (Tag 0C6F).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 (e).
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Pullback along a morphism of affine spectra commutes with symmetric powers of associated
sheaves, naturally in the module, for any ring map. -/
def tildePullbackSymmetricPowerIso (n : ℕ) :
    tilde.functor R ⋙ SheafOfModules.symmetricPower (Spec R).sheaf n ⋙
        Scheme.Modules.pullback (Spec.map φ) ≅
      tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ⋙
        SheafOfModules.symmetricPower (Spec S).sheaf n :=
  Functor.isoWhiskerRight (tildeSymmetricPowerNatIso (R := R) n).symm
      (Scheme.Modules.pullback (Spec.map φ)) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.symmetricPower.functor R n)
      (tildeFunctorCompPullbackIso φ) ≪≫
    Functor.isoWhiskerRight (TauCeti.extendScalarsSymmetricPowerNatIso.{u, u, u} φ.hom n)
      (tilde.functor S) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars φ.hom)
      (tildeSymmetricPowerNatIso (R := S) n) ≪≫
    Functor.isoWhiskerRight (tildeFunctorCompPullbackIso φ).symm
      (SheafOfModules.symmetricPower (Spec S).sheaf n)

/-- The affine pullback comparison is the scalar-extension comparison transported through
`tildeSymmetricPowerIso` and `tildeFunctorCompPullbackIso`. -/
@[simp]
theorem tildePullbackSymmetricPowerIso_hom_app (n : ℕ) (M : ModuleCat.{u} R) :
    (tildePullbackSymmetricPowerIso φ n).hom.app M =
      (Scheme.Modules.pullback (Spec.map φ)).map (tildeSymmetricPowerIso n M).inv ≫
        (tildeFunctorCompPullbackIso φ).hom.app (M.symmetricPower n) ≫
        tilde.map (TauCeti.extendScalarsSymmetricPowerIso.{u, u, u} φ.hom n M).hom ≫
        (tildeSymmetricPowerIso n ((ModuleCat.extendScalars φ.hom).obj M)).hom ≫
        (SheafOfModules.symmetricPower (Spec S).sheaf n).map
          ((tildeFunctorCompPullbackIso φ).inv.app M) := by
  simp only [tildePullbackSymmetricPowerIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, tildeSymmetricPowerNatIso_inv_app,
    TauCeti.extendScalarsSymmetricPowerNatIso_hom_app]
  -- The last two whiskered comparisons have endpoints identified through composite
  -- functors; `erw` crosses those functor-object wrappers before computing components.
  erw [Iso.trans_hom, NatTrans.comp_app]
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    tildeSymmetricPowerNatIso_hom_app]
  erw [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom]
  rfl

/-- The inverse affine pullback comparison reverses the affine and scalar-extension
comparisons. -/
@[simp]
theorem tildePullbackSymmetricPowerIso_inv_app (n : ℕ) (M : ModuleCat.{u} R) :
    (tildePullbackSymmetricPowerIso φ n).inv.app M =
      (SheafOfModules.symmetricPower (Spec S).sheaf n).map
          ((tildeFunctorCompPullbackIso φ).hom.app M) ≫
        (tildeSymmetricPowerIso n ((ModuleCat.extendScalars φ.hom).obj M)).inv ≫
        tilde.map (TauCeti.extendScalarsSymmetricPowerIso.{u, u, u} φ.hom n M).inv ≫
        (tildeFunctorCompPullbackIso φ).inv.app (M.symmetricPower n) ≫
        (Scheme.Modules.pullback (Spec.map φ)).map (tildeSymmetricPowerIso n M).hom := by
  simp only [tildePullbackSymmetricPowerIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_inv, tildeSymmetricPowerNatIso_hom_app,
    TauCeti.extendScalarsSymmetricPowerNatIso_inv_app]
  -- As in the forward formula, expose components across the composite-functor wrappers.
  erw [Iso.trans_inv, NatTrans.comp_app]
  simp only [Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    tildeSymmetricPowerNatIso_inv_app]
  erw [Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Iso.symm_inv]
  erw [Category.assoc]

end

end TauCeti.AlgebraicGeometry
