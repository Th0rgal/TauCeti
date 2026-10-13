/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Ideal.Away
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# Finite ideles and ideals away from a finite set

The finite-idele valuation `adicOrd` records the multiplicity of every finite place in the
fractional ideal attached to a finite idele.  This file makes that dictionary available at the
prime-to carriers used by ray classes and Hecke characters:

1. For a Dedekind domain `R` with fraction field `K`, nonnegativity and positivity of `adicOrd x v`
   are characterized in terms of the local valuation `Valued.v ((x : 𝔸ᶠ[R, K]) v)` and membership
   in the local integer ring `v.adicCompletionIntegers K`, and everywhere nonnegativity of
   `adicOrd x` is identified with membership in `integralAdeles R K`.
2. For a number field `K` and a finite set of finite places `S`, vanishing of `adicOrd x` on `S`
   (equivalently, unit local valuation on `S`) cuts out the subgroup `adicOrdAway S` of finite
   ideles mapping into `NumberFieldArithmetic.idealsAway S` via `toIdealsAway S`, with kernel
   `(integralUnits (𝓞 K) K).subgroupOf (adicOrdAway S)` and induced quotient isomorphism
   `adicOrdAwayQuotientEquivIdealsAway S`.
3. Adding the condition that `adicOrd x v ≥ 0` at every finite place cuts out the submonoid
   `integralAdicOrdAway S` of everywhere-integral finite ideles that are local units on `S`.
   The monoid homomorphism `toIntegralIdealsAway S` maps `integralAdicOrdAway S` surjectively onto
   `NumberFieldArithmetic.integralIdealsAway S`, compatible with `toIdealsAway S` under
   `NumberFieldArithmetic.integralIdealsAwayHom S`, and its multiplicative kernel and fibers are
   governed by `integralUnits (𝓞 K) K`.

## Main definitions and results

* `IsDedekindDomain.FiniteAdeleRing.adicOrd_nonneg_iff`,
  `IsDedekindDomain.FiniteAdeleRing.adicOrd_pos_iff`, and
  `IsDedekindDomain.FiniteAdeleRing.forall_adicOrd_nonneg_iff_mem_integralAdeles`:
  valuation and integrality characterizations of `adicOrd`.
* `TauCeti.GlobalNumberFields.adicOrdAway`, `TauCeti.GlobalNumberFields.toIdealsAway`,
  `TauCeti.GlobalNumberFields.ker_toIdealsAway`, and
  `TauCeti.GlobalNumberFields.adicOrdAwayQuotientEquivIdealsAway`:
  the finite-idele subgroup for fractional ideals away from `S`, its surjective homomorphism to
  `NumberFieldArithmetic.idealsAway S`, its kernel, and the resulting quotient equivalence.
* `TauCeti.GlobalNumberFields.mem_mrange_integralIdealsAwayHom_iff` and
  `TauCeti.GlobalNumberFields.toIdealsAway_mem_mrange_integralIdealsAwayHom_iff`:
  characterization of the image of `NumberFieldArithmetic.integralIdealsAwayHom S` by nonnegativity
  of prime counts and finite-idele orders.
* `TauCeti.GlobalNumberFields.integralAdicOrdAway` and
  `TauCeti.GlobalNumberFields.toIntegralIdealsAway`:
  the submonoid of everywhere-integral finite ideles with unit components on `S` and its surjective
  monoid homomorphism onto `NumberFieldArithmetic.integralIdealsAway S`, together with the kernel
  and fiber theorems `mem_mker_toIntegralIdealsAway_iff`, `mker_toIntegralIdealsAway`,
  `toIntegralIdealsAway_eq_iff`, and `toIntegralIdealsAway_surjective`.
-/

public section

open IsDedekindDomain HeightOneSpectrum
open IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors NumberField

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `v`-adic order of a finite idele is nonnegative exactly when its `v`-adic valuation is at
most `1`. -/
@[simp]
theorem adicOrd_nonneg_iff {x : 𝔸ᶠ[R, K]ˣ} {v : HeightOneSpectrum R} :
    0 ≤ adicOrd x v ↔ Valued.v ((x : 𝔸ᶠ[R, K]) v) ≤ 1 := by
  rw [adicOrd_def, Left.nonneg_neg_iff, ← WithZero.exp_le_exp,
    WithZero.exp_log (valued_coe_units_apply_ne_zero x v), WithZero.exp_zero]

/-- The `v`-adic order of a finite idele is nonnegative exactly when its `v`-component lies in the
local valuation ring. -/
theorem adicOrd_nonneg_iff_mem_adicCompletionIntegers {x : 𝔸ᶠ[R, K]ˣ} {v : HeightOneSpectrum R} :
    0 ≤ adicOrd x v ↔ (x : 𝔸ᶠ[R, K]) v ∈ v.adicCompletionIntegers K := by
  rw [adicOrd_nonneg_iff, mem_adicCompletionIntegers]

/-- The `v`-adic order of a finite idele is positive exactly when its `v`-adic valuation is
strictly less than `1`. -/
@[simp]
theorem adicOrd_pos_iff {x : 𝔸ᶠ[R, K]ˣ} {v : HeightOneSpectrum R} :
    0 < adicOrd x v ↔ Valued.v ((x : 𝔸ᶠ[R, K]) v) < 1 := by
  rw [adicOrd_def, Left.neg_pos_iff, ← WithZero.exp_lt_exp,
    WithZero.exp_log (valued_coe_units_apply_ne_zero x v), WithZero.exp_zero]

/-- A finite idele has nonnegative order at every finite place if and only if its underlying finite
adele is everywhere integral. -/
theorem forall_adicOrd_nonneg_iff_mem_integralAdeles {x : 𝔸ᶠ[R, K]ˣ} :
    (∀ v : HeightOneSpectrum R, 0 ≤ adicOrd x v) ↔ (x : 𝔸ᶠ[R, K]) ∈ integralAdeles R K := by
  simp only [adicOrd_nonneg_iff_mem_adicCompletionIntegers, mem_integralAdeles]

end IsDedekindDomain.FiniteAdeleRing

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Fractional ideals away from a finite set -/

/-- A finite idele defines an ideal away from `S` exactly when its orders vanish on `S`. -/
theorem toFractionalIdeal_mem_idealsAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    toFractionalIdeal x ∈ NumberFieldArithmetic.idealsAway (K := K) S ↔
      ∀ v ∈ S, adicOrd x v = 0 := by
  rw [NumberFieldArithmetic.mem_idealsAway_iff]
  simp only [count_coe_toFractionalIdeal]

/-- A finite idele defines an ideal away from `S` exactly when it is a local unit at every place in
`S`. -/
theorem toFractionalIdeal_mem_idealsAway_iff_valued (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    toFractionalIdeal x ∈ NumberFieldArithmetic.idealsAway (K := K) S ↔
      ∀ v ∈ S, Valued.v ((x : 𝔸ᶠ[(𝓞 K), K]) v) = 1 := by
  simp only [toFractionalIdeal_mem_idealsAway_iff, adicOrd_eq_zero_iff]

/-- The finite ideles whose orders vanish on `S`, viewed as a subgroup. -/
noncomputable def adicOrdAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (𝔸ᶠ[(𝓞 K), K]ˣ) :=
  (NumberFieldArithmetic.idealsAway (K := K) S).comap
    (toFractionalIdeal (R := 𝓞 K) (K := K))

/-- Membership in `adicOrdAway S` means vanishing `v`-adic order at every place in `S`. -/
@[simp]
theorem mem_adicOrdAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    x ∈ adicOrdAway S ↔ ∀ v ∈ S, adicOrd x v = 0 := by
  rw [adicOrdAway, Subgroup.mem_comap, toFractionalIdeal_mem_idealsAway_iff]

/-- A finite idele lies in `adicOrdAway S` if and only if its valuation is `1` at every place in
`S`. -/
theorem mem_adicOrdAway_iff_valued (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    x ∈ adicOrdAway S ↔ ∀ v ∈ S, Valued.v ((x : 𝔸ᶠ[(𝓞 K), K]) v) = 1 := by
  simp only [mem_adicOrdAway_iff, adicOrd_eq_zero_iff]

/-- Every everywhere-integral finite-idele unit has vanishing order on `S`. -/
theorem integralUnits_le_adicOrdAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    integralUnits (𝓞 K) K ≤ adicOrdAway S :=
  fun _ hx ↦ (mem_adicOrdAway_iff_valued S _).mpr fun v _ ↦ mem_integralUnits_iff.mp hx v

/-- The ideal away from `S` attached to a finite idele whose orders vanish on `S`. -/
noncomputable def toIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    adicOrdAway S →* NumberFieldArithmetic.idealsAway (K := K) S :=
  ((toFractionalIdeal (R := 𝓞 K) (K := K)).comp (adicOrdAway S).subtype).codRestrict _
    fun x ↦ x.property

/-- Coercing `toIdealsAway S x` to a fractional ideal unit gives `toFractionalIdeal x`. -/
@[simp]
theorem toIdealsAway_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : adicOrdAway S) :
    (toIdealsAway S x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toFractionalIdeal (x : 𝔸ᶠ[(𝓞 K), K]ˣ) := by
  dsimp [toIdealsAway, MonoidHom.codRestrict, MonoidHom.comp, Subgroup.subtype]
  rfl

/-- The multiplicity at `v` of `toIdealsAway S x` is the `v`-adic order of `x`. -/
@[simp]
theorem count_coe_toIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : adicOrdAway S) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      (((toIdealsAway S x : NumberFieldArithmetic.idealsAway (K := K) S) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      adicOrd (x : 𝔸ᶠ[(𝓞 K), K]ˣ) v := by
  rw [toIdealsAway_apply, count_coe_toFractionalIdeal]

/-- The kernel of `toIdealsAway` consists of finite ideles with trivial fractional ideal. -/
@[simp]
theorem mem_ker_toIdealsAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : adicOrdAway S) :
    toIdealsAway S x = 1 ↔ (x : 𝔸ᶠ[(𝓞 K), K]ˣ) ∈ integralUnits (𝓞 K) K := by
  have hker : (toIdealsAway S).ker =
      ((toFractionalIdeal (R := 𝓞 K) (K := K)).comp (adicOrdAway S).subtype).ker := by
    exact MonoidHom.ker_codRestrict _ _ _
  rw [← MonoidHom.mem_ker, hker, ← MonoidHom.comap_ker, ker_toFractionalIdeal,
    Subgroup.mem_comap]
  simp only [Subgroup.subtype_apply]

/-- The kernel of `toIdealsAway S` is the subgroup of everywhere-integral units inside
`adicOrdAway S`. -/
theorem ker_toIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (toIdealsAway S).ker = (integralUnits (𝓞 K) K).subgroupOf (adicOrdAway S) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_ker_toIdealsAway_iff]

/-- The homomorphism from finite ideles with orders vanishing on `S` to ideals away from `S` is
surjective. -/
theorem toIdealsAway_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (toIdealsAway S) := by
  intro I
  obtain ⟨x, hx⟩ := toFractionalIdeal_surjective (K := K)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  have hx_mem : x ∈ adicOrdAway S := by
    rw [adicOrdAway, Subgroup.mem_comap, hx]
    exact I.property
  refine ⟨⟨x, hx_mem⟩, ?_⟩
  exact Subtype.ext hx

/-- **The group of fractional ideals away from `S` is the quotient of `adicOrdAway S` by the
everywhere-integral finite-idele units.** -/
noncomputable def adicOrdAwayQuotientEquivIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    adicOrdAway S ⧸ (integralUnits (𝓞 K) K).subgroupOf (adicOrdAway S) ≃*
      NumberFieldArithmetic.idealsAway (K := K) S :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toIdealsAway S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (toIdealsAway S) (toIdealsAway_surjective S))

/-- `adicOrdAwayQuotientEquivIdealsAway` sends the coset of a finite idele to its fractional ideal
away from `S`. -/
@[simp]
theorem adicOrdAwayQuotientEquivIdealsAway_mk (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : adicOrdAway S) :
    adicOrdAwayQuotientEquivIdealsAway S
      (x : adicOrdAway S ⧸ (integralUnits (𝓞 K) K).subgroupOf (adicOrdAway S)) =
      toIdealsAway S x := by
  rw [adicOrdAwayQuotientEquivIdealsAway, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk]

/-! ### Integral ideals away from a finite set -/

/-- A fractional ideal away from `S` lies in the range of `integralIdealsAwayHom S` if and only if
its multiplicity at every finite place is nonnegative. -/
theorem mem_mrange_integralIdealsAwayHom_iff {S : Finset (HeightOneSpectrum (𝓞 K))}
    {I : NumberFieldArithmetic.idealsAway (K := K) S} :
    I ∈ MonoidHom.mrange (NumberFieldArithmetic.integralIdealsAwayHom S) ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        0 ≤ FractionalIdeal.count K v ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) := by
  constructor
  · rintro ⟨J, rfl⟩ v
    have hJ : (J : Ideal (𝓞 K)) ≠ ⊥ := (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp J.2).1
    rw [NumberFieldArithmetic.coe_integralIdealsAwayHom, FractionalIdeal.count_coe K v hJ]
    exact Nat.cast_nonneg _
  · intro hnonneg
    let e : HeightOneSpectrum (𝓞 K) → ℕ := fun v ↦
      (FractionalIdeal.count K v ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)).toNat
    have he_cast (v : HeightOneSpectrum (𝓞 K)) :
        (e v : ℤ) = FractionalIdeal.count K v ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) :=
      Int.toNat_of_nonneg (hnonneg v)
    have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
        v.asIdeal ^ e v :=
      (Filter.eventually_cofinite.mp
        (FractionalIdeal.finite_factors ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K))).subset fun v hv hzero ↦
        hv (by simp [e, hzero])
    let J : Ideal (𝓞 K) := ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ e v
    have hJ0 : J ≠ ⊥ := finprod_ne_zero fun v ↦ pow_ne_zero _ v.ne_bot
    have hJcount (v : HeightOneSpectrum (𝓞 K)) :
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.count K v ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
            FractionalIdeal (𝓞 K)⁰ K) := by
      rw [FractionalIdeal.count_coe K v hJ0, Ideal.count_finprod_asIdeal_pow hfin v, he_cast]
    have hJS : J ∈ NumberFieldArithmetic.integralIdealsAway (K := K) S := by
      rw [NumberFieldArithmetic.mem_integralIdealsAway_iff_count_eq_zero]
      exact ⟨hJ0, fun v hv ↦
        (hJcount v).trans (NumberFieldArithmetic.mem_idealsAway_iff.mp I.2 v hv)⟩
    refine ⟨⟨J, hJS⟩, Subtype.ext <| Units.ext ?_⟩
    have h1 := FractionalIdeal.finprod_unitOfPrime_zpow_count
      (NumberFieldArithmetic.integralIdealsAwayHom S ⟨J, hJS⟩ : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    have h2 := FractionalIdeal.finprod_unitOfPrime_zpow_count (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    have hcount_eq (v : HeightOneSpectrum (𝓞 K)) :
        FractionalIdeal.count K v
          (((NumberFieldArithmetic.integralIdealsAwayHom S ⟨J, hJS⟩ :
            NumberFieldArithmetic.idealsAway (K := K) S) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
            FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.count K v ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
            FractionalIdeal (𝓞 K)⁰ K) := by
      rw [NumberFieldArithmetic.coe_integralIdealsAwayHom]
      exact hJcount v
    exact congrArg Units.val (h1.trans (by simp_rw [hcount_eq]; exact h2.symm))

/-- The fractional ideal of `x : adicOrdAway S` comes from an integral ideal away from `S` if and
only if all of its finite-place orders are nonnegative. -/
theorem toIdealsAway_mem_mrange_integralIdealsAwayHom_iff
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : adicOrdAway S) :
    toIdealsAway S x ∈ MonoidHom.mrange (NumberFieldArithmetic.integralIdealsAwayHom S) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ adicOrd (x : 𝔸ᶠ[(𝓞 K), K]ˣ) v := by
  rw [mem_mrange_integralIdealsAwayHom_iff]
  simp only [count_coe_toIdealsAway]

/-- The submonoid of finite ideles whose orders vanish on `S` and are nonnegative at every finite
place: equivalently, the everywhere-integral finite ideles that are local units on `S`. -/
noncomputable def integralAdicOrdAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Submonoid (𝔸ᶠ[(𝓞 K), K]ˣ) where
  carrier := {x | x ∈ adicOrdAway S ∧ ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ adicOrd x v}
  one_mem' := ⟨one_mem _, fun v ↦ by rw [adicOrd_one]⟩
  mul_mem' hx hy := ⟨mul_mem hx.1 hy.1, fun v ↦ by
    rw [adicOrd_mul]
    exact add_nonneg (hx.2 v) (hy.2 v)⟩

/-- Membership in `integralAdicOrdAway S` means vanishing orders on `S` and nonnegative orders at
every finite place. -/
@[simp]
theorem mem_integralAdicOrdAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    x ∈ integralAdicOrdAway S ↔
      (∀ v ∈ S, adicOrd x v = 0) ∧ ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ adicOrd x v := by
  change x ∈ adicOrdAway S ∧ _ ↔ _
  rw [mem_adicOrdAway_iff]

/-- Valuation characterization of `integralAdicOrdAway S`: unit valuation on `S` and valuation at
most `1` at every finite place. -/
theorem mem_integralAdicOrdAway_iff_valued (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    x ∈ integralAdicOrdAway S ↔
      (∀ v ∈ S, Valued.v ((x : 𝔸ᶠ[(𝓞 K), K]) v) = 1) ∧
        ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((x : 𝔸ᶠ[(𝓞 K), K]) v) ≤ 1 := by
  simp only [mem_integralAdicOrdAway_iff, adicOrd_eq_zero_iff, adicOrd_nonneg_iff]

/-- A finite idele lies in `integralAdicOrdAway S` if and only if it lies in `adicOrdAway S` and its
underlying finite adele is everywhere integral. -/
theorem mem_integralAdicOrdAway_iff_mem_integralAdeles (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    x ∈ integralAdicOrdAway S ↔
      x ∈ adicOrdAway S ∧ (x : 𝔸ᶠ[(𝓞 K), K]) ∈ integralAdeles (𝓞 K) K := by
  change x ∈ adicOrdAway S ∧ _ ↔ _
  rw [forall_adicOrd_nonneg_iff_mem_integralAdeles]

/-- Every everywhere-integral finite-idele unit lies in `integralAdicOrdAway S`. -/
theorem integralUnits_toSubmonoid_le_integralAdicOrdAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (integralUnits (𝓞 K) K).toSubmonoid ≤ integralAdicOrdAway S := by
  intro x hx
  rw [mem_integralAdicOrdAway_iff_valued]
  exact ⟨fun v _ ↦ mem_integralUnits_iff.mp hx v, fun v ↦ (mem_integralUnits_iff.mp hx v).le⟩

/-- The canonical inclusion of `integralAdicOrdAway S` into `adicOrdAway S`. -/
noncomputable def integralAdicOrdAwayToAdicOrdAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    integralAdicOrdAway S →* adicOrdAway S where
  toFun x := ⟨x.1, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Coercing `integralAdicOrdAwayToAdicOrdAway S x` to a finite idele gives `x`. -/
@[simp]
theorem coe_integralAdicOrdAwayToAdicOrdAway (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : integralAdicOrdAway S) :
    (integralAdicOrdAwayToAdicOrdAway S x : 𝔸ᶠ[(𝓞 K), K]ˣ) = x := by
  rfl

/-- Applying `integralAdicOrdAwayToAdicOrdAway S` to a lifted element of `adicOrdAway S` recovers
that element. -/
@[simp]
theorem integralAdicOrdAwayToAdicOrdAway_mk (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : adicOrdAway S) (hx : (x : 𝔸ᶠ[(𝓞 K), K]ˣ) ∈ integralAdicOrdAway S) :
    integralAdicOrdAwayToAdicOrdAway S ⟨x, hx⟩ = x := by
  rfl

/-- **The monoid homomorphism from `integralAdicOrdAway S` to `integralIdealsAway S`** sending an
everywhere-integral finite idele with unit components on `S` to the integral ideal away from `S`
with the same prime multiplicities. -/
noncomputable def toIntegralIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    integralAdicOrdAway S →* NumberFieldArithmetic.integralIdealsAway (K := K) S where
  toFun x :=
    ((toIdealsAway_mem_mrange_integralIdealsAwayHom_iff S
      (integralAdicOrdAwayToAdicOrdAway S x)).mpr x.2.2).choose
  map_one' := NumberFieldArithmetic.integralIdealsAwayHom_injective S <| by
    have h1 := ((toIdealsAway_mem_mrange_integralIdealsAwayHom_iff S
      (integralAdicOrdAwayToAdicOrdAway S 1)).mpr (1 : integralAdicOrdAway S).2.2).choose_spec
    rw [h1, map_one, map_one, map_one]
  map_mul' x y := NumberFieldArithmetic.integralIdealsAwayHom_injective S <| by
    have hxy := ((toIdealsAway_mem_mrange_integralIdealsAwayHom_iff S
      (integralAdicOrdAwayToAdicOrdAway S (x * y))).mpr (x * y).2.2).choose_spec
    have hx := ((toIdealsAway_mem_mrange_integralIdealsAwayHom_iff S
      (integralAdicOrdAwayToAdicOrdAway S x)).mpr x.2.2).choose_spec
    have hy := ((toIdealsAway_mem_mrange_integralIdealsAwayHom_iff S
      (integralAdicOrdAwayToAdicOrdAway S y)).mpr y.2.2).choose_spec
    rw [hxy, map_mul, map_mul, map_mul, hx, hy]

/-- `toIntegralIdealsAway S` is compatible with `toIdealsAway S` under
`integralIdealsAwayHom S`. -/
@[simp]
theorem integralIdealsAwayHom_toIntegralIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : integralAdicOrdAway S) :
    NumberFieldArithmetic.integralIdealsAwayHom S (toIntegralIdealsAway S x) =
      toIdealsAway S (integralAdicOrdAwayToAdicOrdAway S x) :=
  ((toIdealsAway_mem_mrange_integralIdealsAwayHom_iff S
    (integralAdicOrdAwayToAdicOrdAway S x)).mpr x.2.2).choose_spec

/-- Coercing `toIntegralIdealsAway S x` to a fractional ideal gives `toFractionalIdeal x`. -/
@[simp]
theorem coe_toIntegralIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : integralAdicOrdAway S) :
    ((toIntegralIdealsAway S x : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      toFractionalIdeal (x : 𝔸ᶠ[(𝓞 K), K]ˣ) := by
  rw [← NumberFieldArithmetic.coe_integralIdealsAwayHom S,
    integralIdealsAwayHom_toIntegralIdealsAway, toIdealsAway_apply,
    coe_integralAdicOrdAwayToAdicOrdAway]

/-- The multiplicity at `v` of `toIntegralIdealsAway S x` is the `v`-adic order of `x`. -/
@[simp]
theorem count_coe_toIntegralIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : integralAdicOrdAway S) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      ((toIntegralIdealsAway S x : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      adicOrd (x : 𝔸ᶠ[(𝓞 K), K]ˣ) v := by
  rw [coe_toIntegralIdealsAway, count_coe_toFractionalIdeal]

/-- **Kernel characterization for `toIntegralIdealsAway S`**: an element of
`integralAdicOrdAway S` maps to the unit ideal if and only if it is an everywhere-integral unit. -/
@[simp]
theorem mem_mker_toIntegralIdealsAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : integralAdicOrdAway S) :
    toIntegralIdealsAway S x = 1 ↔ (x : 𝔸ᶠ[(𝓞 K), K]ˣ) ∈ integralUnits (𝓞 K) K := by
  rw [← (NumberFieldArithmetic.integralIdealsAwayHom_injective S).eq_iff,
    integralIdealsAwayHom_toIntegralIdealsAway, map_one, mem_ker_toIdealsAway_iff,
    coe_integralAdicOrdAwayToAdicOrdAway]

/-- The multiplicative kernel of `toIntegralIdealsAway S` is the submonoid of everywhere-integral
units inside `integralAdicOrdAway S`. -/
theorem mker_toIntegralIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MonoidHom.mker (toIntegralIdealsAway S) =
      (integralUnits (𝓞 K) K).toSubmonoid.comap (integralAdicOrdAway S).subtype := by
  ext x
  rw [MonoidHom.mem_mker, Submonoid.mem_comap, Submonoid.coe_subtype, Subgroup.mem_toSubmonoid,
    mem_mker_toIntegralIdealsAway_iff]

/-- Two elements of `integralAdicOrdAway S` define the same integral ideal away from `S` if and
only if they differ by an everywhere-integral unit. -/
theorem toIntegralIdealsAway_eq_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x y : integralAdicOrdAway S) :
    toIntegralIdealsAway S x = toIntegralIdealsAway S y ↔
      (x : 𝔸ᶠ[(𝓞 K), K]ˣ)⁻¹ * (y : 𝔸ᶠ[(𝓞 K), K]ˣ) ∈ integralUnits (𝓞 K) K := by
  rw [← (NumberFieldArithmetic.integralIdealsAwayHom_injective S).eq_iff,
    integralIdealsAwayHom_toIntegralIdealsAway, integralIdealsAwayHom_toIntegralIdealsAway,
    ← inv_mul_eq_one, ← map_inv, ← map_mul, mem_ker_toIdealsAway_iff,
    Subgroup.coe_mul, Subgroup.coe_inv, coe_integralAdicOrdAwayToAdicOrdAway,
    coe_integralAdicOrdAwayToAdicOrdAway]

/-- **Every nonzero integral ideal prime to `S` is the image of an element of
`integralAdicOrdAway S` under `toIntegralIdealsAway S`.** -/
theorem toIntegralIdealsAway_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (toIntegralIdealsAway S) := by
  intro I
  obtain ⟨x, hx⟩ := toIdealsAway_surjective S (NumberFieldArithmetic.integralIdealsAwayHom S I)
  have hx_int : (x : 𝔸ᶠ[(𝓞 K), K]ˣ) ∈ integralAdicOrdAway S := by
    refine ⟨x.2, ?_⟩
    rw [← toIdealsAway_mem_mrange_integralIdealsAwayHom_iff S x, hx]
    exact ⟨I, rfl⟩
  refine ⟨⟨x.1, hx_int⟩, NumberFieldArithmetic.integralIdealsAwayHom_injective S ?_⟩
  rw [integralIdealsAwayHom_toIntegralIdealsAway, integralAdicOrdAwayToAdicOrdAway_mk]
  exact hx

/-- The finite-idele orders of a representative of an integral ideal are its ideal multiplicities.

In particular, these orders are nonnegative everywhere and vanish on the excluded finite set. -/
theorem exists_forall_adicOrd_eq_count_integralIdealsAway
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : NumberFieldArithmetic.integralIdealsAway (K := K) S) :
    ∃ x : 𝔸ᶠ[(𝓞 K), K]ˣ,
      ∀ v : HeightOneSpectrum (𝓞 K),
        adicOrd x v = FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨x, rfl⟩ := toIntegralIdealsAway_surjective S I
  exact ⟨x.1, fun v ↦ (count_coe_toIntegralIdealsAway S x v).symm⟩

end TauCeti.GlobalNumberFields

end
