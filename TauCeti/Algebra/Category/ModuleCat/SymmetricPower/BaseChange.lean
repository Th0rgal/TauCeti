/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BaseChange

/-!
# Extension of scalars and symmetric powers

Symmetric powers commute with extension of scalars along an arbitrary map of commutative rings.
This file packages `TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange` as a natural
isomorphism of module functors. Its forward map agrees in the ambient symmetric algebra with
`TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`. This is the module calculation for pullback
of symmetric powers of quasicoherent sheaves on affine schemes.

## References

* The Stacks Project, Lemma 10.13.6 (Tag 0C6F).
-/

public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace TauCeti

universe u₁ u₂ v

noncomputable section

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

/-- Symmetric powers commute with extension of scalars, without a flatness or finiteness
assumption. -/
def extendScalarsSymmetricPowerIso (n : ℕ) (M : ModuleCat.{max u₁ v} R) :
    (ModuleCat.extendScalars f).obj (M.symmetricPower n) ≅
      ((ModuleCat.extendScalars f).obj M).symmetricPower n := by
  let _ := f.toAlgebra
  exact (TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange
    (R := R) (S := S) (M := M) n).symm.toModuleIso

/-- On a pure tensor, the forward scalar-extension comparison is computed in the ambient
symmetric algebra by `TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`. -/
@[simp]
theorem coe_extendScalarsSymmetricPowerIso_hom_tmul (n : ℕ) (M : ModuleCat.{max u₁ v} R)
    (s : S) (x : M.symmetricPower n) :
    letI := f.toAlgebra
    Subtype.val ((extendScalarsSymmetricPowerIso.{u₁, u₂, v} f n M).hom (s ⊗ₜ[R,f] x)) =
      TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv (k := R) (K := S) (s ⊗ₜ[R] x.1) := by
  let _ := f.toAlgebra
  -- Identify the categorical pure tensor with the pure tensor for `f.toAlgebra` before
  -- applying the linear-equivalence formula.
  change (((TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange
    (R := R) (S := S) (M := M) n).symm (s ⊗ₜ[R] x) :
      _root_.SymmetricAlgebra S (S ⊗[R] M))) = _
  rw [TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleEquivBaseChange_symm_apply]
  rfl

/-- The scalar-extension comparison is natural in the module. -/
@[reassoc]
theorem extendScalarsSymmetricPowerIso_hom_naturality (n : ℕ)
    {M N : ModuleCat.{max u₁ v} R} (g : M ⟶ N) :
    (ModuleCat.extendScalars f).map (ModuleCat.symmetricPower.map g n) ≫
        (extendScalarsSymmetricPowerIso.{u₁, u₂, v} f n N).hom =
      (extendScalarsSymmetricPowerIso.{u₁, u₂, v} f n M).hom ≫
        ModuleCat.symmetricPower.map ((ModuleCat.extendScalars f).map g) n := by
  let _ := f.toAlgebra
  have hmap (s : S) (y : _root_.SymmetricAlgebra R M) :
      TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv (k := R) (K := S)
          (s ⊗ₜ[R] _root_.SymmetricAlgebra.map R g.hom y) =
        _root_.SymmetricAlgebra.map S (g.hom.baseChange S)
          (TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv (k := R) (K := S) (s ⊗ₜ[R] y)) := by
    simpa only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgEquiv.toAlgHom_apply, BialgEquiv.coe_toAlgEquiv] using
      AlgHom.congr_fun (g.hom.scalarTensorBialgEquiv_comp_map (S := S)) (s ⊗ₜ[R] y)
  have hfg (z : _root_.SymmetricAlgebra S (S ⊗[R] M)) :
      _root_.SymmetricAlgebra.map S (g.hom.baseChange S) z =
        _root_.SymmetricAlgebra.map S ((ModuleCat.extendScalars f).map g).hom z := by
    congr 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | tmul s x =>
    apply Subtype.ext
    -- Compare both composites on pure tensors inside the ambient symmetric algebra.
    exact ((coe_extendScalarsSymmetricPowerIso_hom_tmul f n N s
      (ModuleCat.symmetricPower.map g n x)).trans
      (congrArg (TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv (k := R) (K := S))
        (congrArg (s ⊗ₜ[R] ·) (ModuleCat.symmetricPower.coe_map_apply g n x)))).trans
      ((hmap s x.1).trans
        ((hfg _).trans
          ((congrArg (SymmetricAlgebra.map S ((ModuleCat.extendScalars f).map g).hom)
            (coe_extendScalarsSymmetricPowerIso_hom_tmul f n M s x).symm).trans
            (ModuleCat.symmetricPower.coe_map_apply ((ModuleCat.extendScalars f).map g) n _).symm)))

/-- The natural scalar-extension comparison for the `n`-th symmetric power. -/
def extendScalarsSymmetricPowerNatIso (n : ℕ) :
    ModuleCat.symmetricPower.functor.{max u₁ v} R n ⋙
        ModuleCat.extendScalars.{u₁, u₂, max u₁ v} f ≅
      ModuleCat.extendScalars.{u₁, u₂, max u₁ v} f ⋙
        ModuleCat.symmetricPower.functor.{max u₁ u₂ v} S n :=
  NatIso.ofComponents (extendScalarsSymmetricPowerIso.{u₁, u₂, v} f n)
    (fun g ↦ extendScalarsSymmetricPowerIso_hom_naturality.{u₁, u₂, v} f n g)

/-- The forward components of the natural scalar-extension comparison. -/
@[simp]
theorem extendScalarsSymmetricPowerNatIso_hom_app (n : ℕ) (M : ModuleCat.{max u₁ v} R) :
    (extendScalarsSymmetricPowerNatIso.{u₁, u₂, v} f n).hom.app M =
      (extendScalarsSymmetricPowerIso.{u₁, u₂, v} f n M).hom :=
  (rfl)

/-- The inverse components of the natural scalar-extension comparison. -/
@[simp]
theorem extendScalarsSymmetricPowerNatIso_inv_app (n : ℕ) (M : ModuleCat.{max u₁ v} R) :
    (extendScalarsSymmetricPowerNatIso.{u₁, u₂, v} f n).inv.app M =
      (extendScalarsSymmetricPowerIso.{u₁, u₂, v} f n M).inv :=
  (rfl)

end

end TauCeti
