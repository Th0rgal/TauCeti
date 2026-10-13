/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower

/-!
# Symmetric powers and restriction of scalars

Restriction of scalars carries a natural symmetric-power comparison, induced on degree-`n`
homogeneous pieces of the symmetric algebra by the canonical semilinear map from the
scalar-restricted module to the original module. It need not be an isomorphism. This
construction supplies the sectionwise maps for symmetric powers of pushforwards of module
presheaves.
-/

public section

open CategoryTheory

namespace TauCeti.ModuleCat

universe u v w

noncomputable section

variable {S : Type u} {R : Type v} [CommRing S] [CommRing R] (f : S →+* R)

private def restrictScalarsSymmetricPowerApp (n : ℕ) (M : ModuleCat.{max u v w} R) :
    ((ModuleCat.restrictScalars f).obj M).symmetricPower n ⟶
      (ModuleCat.restrictScalars f).obj (M.symmetricPower n) :=
  ModuleCat.semilinearMapAddEquiv f _ _
    (TauCeti.SymmetricAlgebra.homogeneousSubmoduleMapₛₗ
      ((ModuleCat.semilinearMapAddEquiv f ((ModuleCat.restrictScalars f).obj M) M).symm
        (𝟙 ((ModuleCat.restrictScalars f).obj M))) n)

private lemma coe_restrictScalarsSymmetricPowerApp_apply (n : ℕ)
    (M : ModuleCat.{max u v w} R)
    (x : ((ModuleCat.restrictScalars f).obj M).symmetricPower n) :
    Subtype.val (restrictScalarsSymmetricPowerApp f n M x) =
      SymmetricAlgebra.mapₛₗ
        ((ModuleCat.semilinearMapAddEquiv f ((ModuleCat.restrictScalars f).obj M) M).symm
          (𝟙 ((ModuleCat.restrictScalars f).obj M))) x.1 :=
  TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n x

/-- Restriction of scalars carries the natural symmetric-power comparison, changing the
coefficient ring of a homogeneous symmetric-algebra element without changing its module
generators. -/
def restrictScalarsSymmetricPowerComparison (n : ℕ) :
    ModuleCat.restrictScalars.{max u v w} f ⋙ ModuleCat.symmetricPower.functor S n ⟶
      ModuleCat.symmetricPower.functor R n ⋙ ModuleCat.restrictScalars f where
  app := restrictScalarsSymmetricPowerApp f n
  naturality {M N} φ := by
    have key :
        (SymmetricAlgebra.map R φ.hom : _ →+* _).comp
            (SymmetricAlgebra.mapₛₗ
              ((ModuleCat.semilinearMapAddEquiv f ((ModuleCat.restrictScalars f).obj M) M).symm
                (𝟙 ((ModuleCat.restrictScalars f).obj M)))) =
          (SymmetricAlgebra.mapₛₗ
            ((ModuleCat.semilinearMapAddEquiv f ((ModuleCat.restrictScalars f).obj N) N).symm
              (𝟙 ((ModuleCat.restrictScalars f).obj N)))).comp
            (SymmetricAlgebra.map S ((ModuleCat.restrictScalars f).map φ).hom : _ →+* _) := by
      apply SymmetricAlgebra.ringHom_ext
      · ext r
        simp
      · intro m
        simp only [RingHom.comp_apply, RingHom.coe_coe, SymmetricAlgebra.map_apply_ι,
          SymmetricAlgebra.mapₛₗ_ι]
        rfl
    ext x
    apply Subtype.ext
    -- Both composites act in the ambient symmetric algebra by the two sides of `key`.
    exact ((coe_restrictScalarsSymmetricPowerApp_apply f n N _).trans
      (congrArg _ (ModuleCat.symmetricPower.coe_map_apply _ n x))).trans
      ((RingHom.congr_fun key.symm x.1).trans
        ((congrArg _ (coe_restrictScalarsSymmetricPowerApp_apply f n M x).symm).trans
          (ModuleCat.symmetricPower.coe_map_apply φ n _).symm))

/-- The restriction-of-scalars comparison is computed in the symmetric algebra by the ring
homomorphism induced by the canonical semilinear map from `(ModuleCat.restrictScalars f).obj M`
to `M`. -/
-- Explicit objects keep the coercion to a function in simp normal form.
@[simp]
theorem coe_restrictScalarsSymmetricPowerComparison_app_apply (n : ℕ)
    (M : ModuleCat.{max u v w} R)
    (x : ((ModuleCat.restrictScalars f).obj M).symmetricPower n) :
    Subtype.val ((ConcreteCategory.hom
      (X := ((ModuleCat.restrictScalars f).obj M).symmetricPower n)
      (Y := (ModuleCat.restrictScalars f).obj (M.symmetricPower n))
      ((restrictScalarsSymmetricPowerComparison f n).app M)) x) =
      SymmetricAlgebra.mapₛₗ
        ((ModuleCat.semilinearMapAddEquiv f ((ModuleCat.restrictScalars f).obj M) M).symm
          (𝟙 ((ModuleCat.restrictScalars f).obj M))) x.1 :=
  coe_restrictScalarsSymmetricPowerApp_apply f n M x

end

end TauCeti.ModuleCat
