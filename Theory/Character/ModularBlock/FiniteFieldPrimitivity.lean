module

public import Theory.Character.ModularBlock.FiniteFieldExtension
public import Theory.Character.ModularBlock.CompatibleBrauerBlock
public import Theory.Character.ModularBlock.CyclotomicDVR

/-!
# Primitivity of the compatible local principal selector

The cyclotomic prime contains two and is therefore nonzero. Finiteness of
quotients of the cyclotomic integer order makes both the subgroup and ambient
residue fields finite. Extending the subgroup's augmentation-one selector
through the canonical residue-field inclusion preserves central primitivity
by the generic finite-field extension theorem.

Ported from the CompatibleSelector section of
`c3503435:glauberman_zStar/Submission/ZStar/FiniteFieldPrimitivity.lean`.
This theorem supplies the finite-field step of local principal-block
primitivity; its source-primitivity hypothesis is explicit.
-/

public section
noncomputable section
namespace ModularBlock.FiniteFieldPrimitivity
universe u

section CompatibleSelector

open PrincipalBlockConstruction

variable {G : Type u} [Group G] [Finite G]

theorem principalResidueField_finite
    (d : PrincipalCongruenceBlockData G) :
    Finite (BrauerBlockReduction.principalResidueField d) := by
  have hprime_ne_bot : d.primeIdeal ≠ ⊥ := by
    intro hbot
    have htwo := BlockPreliminaries.two_mem_of_liesOver
      d.primeIdeal d.primeIdeal_liesOverTwo
    rw [hbot, Ideal.mem_bot] at htwo
    exact two_ne_zero htwo
  exact CyclotomicDVR.cyclotomicOrder_quotient_finite
    (Nat.card_pos (α := G)).ne' d.eta_spec d.primeIdeal hprime_ne_bot

/-- Conditional specialization to the compatible local principal selector.
The only input is central primitivity before extending the residue field. -/
theorem localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive_of_source
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (hsource : IsCentrallyPrimitive
      (BrauerBlockReduction.reducedPrincipalBlockElement
        (CompatibleBrauerBlock.localData d H))) :
    IsCentrallyPrimitive
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H) := by
  let dH := CompatibleBrauerBlock.localData d H
  let k := BrauerBlockReduction.principalResidueField dH
  let K := BrauerBlockReduction.principalResidueField d
  let φ := CompatibleLocalBlock.compatibleSubgroupResidueFieldInclusion d H
  let : Field k := Ideal.Quotient.field dH.primeIdeal
  let : Field K := Ideal.Quotient.field d.primeIdeal
  let : Finite k := principalResidueField_finite dH
  let : Finite K := principalResidueField_finite d
  let : Algebra k K := φ.toAlgebra
  have hgeneric := map_isCentrallyPrimitive_of_augmentation_eq_one
    k K H
    (BrauerBlockReduction.reducedPrincipalBlockElement dH)
    hsource
    (BrauerBlockReduction.reducedPrincipalBlockElement_augmentation_eq_one dH)
  have halgebraMap : algebraMap k K = φ := rfl
  rw [halgebraMap] at hgeneric
  change IsCentrallyPrimitive
    (MonoidAlgebra.mapRingHom H
      (CompatibleLocalBlock.compatibleSubgroupResidueFieldInclusion d H)
      (BrauerBlockReduction.reducedPrincipalBlockElement dH))
  exact hgeneric

end CompatibleSelector


end ModularBlock.FiniteFieldPrimitivity
