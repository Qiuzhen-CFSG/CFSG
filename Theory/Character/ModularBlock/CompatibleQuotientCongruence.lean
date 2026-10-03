module

public import Theory.Character.ModularBlock.CompatibleCongruence
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Principal congruence blocks compatible with a quotient

For a finite group `H`, a normal subgroup `Z`, and arbitrary principal
congruence-block data `d` on `H`, the root `d.eta ^ |Z|` is primitive of order
`|H/Z|`. Its cyclotomic order embeds in the ambient one, and contraction of
the fixed ambient prime gives a maximal ideal above two. This constructs
actual quotient data without choosing an incompatible modular place.

Lagrange's formula gives the primitive-root order. The positive power relation
makes the order inclusion integral, so the general contraction results in
`CompatibleCongruence` give maximality and lying over two. Only the ordinary
character family is chosen independently; its place is replaced by these
prescribed fields. The residue-field and localization maps are the canonical
maps attached to contraction and are injective. Exposed definitions retain
the exact coefficient rings and prime instances for subsequent inflation.

This is the quotient counterpart of `CompatibleCongruence`'s subgroup
construction, providing the compatible coefficient places used in central
quotient arguments such as ABG III.6, pp.90–91. It asserts no modular-character,
basic-set, or Cartan comparison.
-/

public section

noncomputable section

namespace ModularBlock.CompatibleLocalBlock

open PrincipalBlockConstruction

universe u

variable {H : Type u} [Group H] [Finite H]

/-- The power of the ambient root appropriate to the quotient by `Z`. -/
@[expose] def quotientRoot (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) : ℂ :=
  d.eta ^ Nat.card Z

theorem quotientRoot_spec
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    IsPrimitiveRoot (quotientRoot d Z) (Nat.card (H ⧸ Z)) := by
  apply IsPrimitiveRoot.pow Nat.card_pos d.eta_spec
  rw [mul_comm]
  exact Z.card_eq_card_quotient_mul_card_subgroup

theorem quotientRoot_mem
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) :
    quotientRoot d Z ∈ cyclotomicOrder d.eta :=
  pow_mem_cyclotomicOrder (eta_mem_cyclotomicOrder d.eta) (Nat.card Z)

/-- Actual quotient principal data with the prescribed root and contracted prime. -/
@[expose] def compatibleQuotientPrincipalCongruenceBlockData
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    PrincipalCongruenceBlockData (H ⧸ Z) := by
  let family := Classical.choice (exists_principalCongruenceBlockData (H ⧸ Z))
  exact {
    I := family.I
    fintypeI := family.fintypeI
    decidableEqI := family.decidableEqI
    chi := family.chi
    complete := family.complete
    eta := quotientRoot d Z
    eta_spec := quotientRoot_spec d Z
    primeIdeal := contractedCyclotomicPrime (quotientRoot_mem d Z) d.primeIdeal
    primeIdeal_maximal := contractedCyclotomicPrime_isMaximal
      (quotientRoot_mem d Z) (Nat.card_pos (α := Z)) rfl
      d.primeIdeal d.primeIdeal_maximal
    primeIdeal_liesOverTwo := contractedCyclotomicPrime_liesOverTwo
      (quotientRoot_mem d Z) d.primeIdeal d.primeIdeal_liesOverTwo
    principal := family.principal
    principal_eq := family.principal_eq }

@[simp] theorem compatibleQuotientPrincipalCongruenceBlockData_eta
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    (compatibleQuotientPrincipalCongruenceBlockData d Z).eta =
      d.eta ^ Nat.card Z := rfl

@[simp] theorem compatibleQuotientPrincipalCongruenceBlockData_primeIdeal
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    (compatibleQuotientPrincipalCongruenceBlockData d Z).primeIdeal =
      contractedCyclotomicPrime (quotientRoot_mem d Z) d.primeIdeal := rfl

/-- Quotient principal data exist at the prescribed power root and ambient
prime contraction, witnessed by the canonical compatible construction. -/
theorem exists_compatibleQuotientPrincipalCongruenceBlockData
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    ∃ quotientData : PrincipalCongruenceBlockData (H ⧸ Z),
      quotientData.eta = d.eta ^ Nat.card Z ∧
      HEq quotientData.primeIdeal
        (contractedCyclotomicPrime (quotientRoot_mem d Z) d.primeIdeal) :=
  ⟨compatibleQuotientPrincipalCongruenceBlockData d Z, rfl, HEq.rfl⟩

instance contractedQuotientPrimeIdeal_isPrime
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    (contractedCyclotomicPrime (quotientRoot_mem d Z) d.primeIdeal).IsPrime := by
  change (compatibleQuotientPrincipalCongruenceBlockData d Z).primeIdeal.IsPrime
  infer_instance

/-- The compatible quotient residue field embedded in the ambient residue field. -/
@[expose] def compatibleQuotientResidueFieldInclusion
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    (cyclotomicOrder (compatibleQuotientPrincipalCongruenceBlockData d Z).eta ⧸
        (compatibleQuotientPrincipalCongruenceBlockData d Z).primeIdeal) →+*
      (cyclotomicOrder d.eta ⧸ d.primeIdeal) :=
  contractedResidueFieldInclusion (quotientRoot_mem d Z) d.primeIdeal

theorem compatibleQuotientResidueFieldInclusion_injective
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    Function.Injective (compatibleQuotientResidueFieldInclusion d Z) :=
  contractedResidueFieldInclusion_injective (quotientRoot_mem d Z) d.primeIdeal

@[simp] theorem compatibleQuotientResidueFieldInclusion_mk
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal]
    (coefficient : cyclotomicOrder
      (compatibleQuotientPrincipalCongruenceBlockData d Z).eta) :
    compatibleQuotientResidueFieldInclusion d Z
        (Ideal.Quotient.mk
          (compatibleQuotientPrincipalCongruenceBlockData d Z).primeIdeal coefficient) =
      Ideal.Quotient.mk d.primeIdeal
        (cyclotomicOrderInclusion (quotientRoot_mem d Z) coefficient) :=
  contractedResidueFieldInclusion_mk (quotientRoot_mem d Z) d.primeIdeal coefficient

/-- The compatible quotient localization embedded at the fixed ambient prime. -/
@[expose] def compatibleQuotientLocalizationInclusion
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    Localization.AtPrime
        (compatibleQuotientPrincipalCongruenceBlockData d Z).primeIdeal →+*
      Localization.AtPrime d.primeIdeal :=
  contractedLocalizationInclusion (quotientRoot_mem d Z) d.primeIdeal

@[simp] theorem compatibleQuotientLocalizationInclusion_algebraMap
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal]
    (coefficient : cyclotomicOrder
      (compatibleQuotientPrincipalCongruenceBlockData d Z).eta) :
    compatibleQuotientLocalizationInclusion d Z
        (algebraMap _ (Localization.AtPrime
          (compatibleQuotientPrincipalCongruenceBlockData d Z).primeIdeal) coefficient) =
      algebraMap _ (Localization.AtPrime d.primeIdeal)
        (cyclotomicOrderInclusion (quotientRoot_mem d Z) coefficient) :=
  contractedLocalizationInclusion_algebraMap (quotientRoot_mem d Z) d.primeIdeal coefficient

private theorem localRingHom_injective
    {source target : Type*} [CommRing source] [CommRing target] [IsDomain target]
    (sourcePrime : Ideal source) [sourcePrime.IsPrime]
    (targetPrime : Ideal target) [targetPrime.IsPrime]
    (inclusion : source →+* target) (contraction : sourcePrime = targetPrime.comap inclusion)
    (injective : Function.Injective inclusion) :
    Function.Injective (Localization.localRingHom sourcePrime targetPrime inclusion contraction) := by
  apply IsLocalization.map_injective_of_injective'
    (M := sourcePrime.primeCompl) (N := targetPrime.primeCompl)
    (Sₘ := Localization.AtPrime targetPrime)
  · exact fun not_mem => not_mem targetPrime.zero_mem
  · exact injective

theorem compatibleQuotientLocalizationInclusion_injective
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal] :
    Function.Injective (compatibleQuotientLocalizationInclusion d Z) :=
  localRingHom_injective
    (compatibleQuotientPrincipalCongruenceBlockData d Z).primeIdeal
    d.primeIdeal (cyclotomicOrderInclusion (quotientRoot_mem d Z)) rfl
    (Subring.inclusion_injective _)

end ModularBlock.CompatibleLocalBlock
