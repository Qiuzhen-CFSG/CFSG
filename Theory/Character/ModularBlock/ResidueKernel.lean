module

public import Theory.Character.ModularBlock.PrincipalReduction

/-!
# Kernel of localized residue reduction

Reduction from the localization of the cyclotomic order at the principal
congruence prime kills exactly the nonunits. The residue map is surjective
because the quotient map is, and its kernel is maximal since the quotient
is a field. Uniqueness of the maximal ideal in the local ring identifies
that kernel with the nonunits. No block-primitivity result is needed.

This shared arithmetic lemma feeds scalar nilpotence and the Nagao
complement coefficient criterion. Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BlockPrimitivity.lean` (revision `c3503435`), preserving its
public namespace and theorem name.
-/

public section

namespace ModularBlock.BlockPrimitivity

private instance principalPrime_isPrime
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    d.primeIdeal.IsPrime := d.primeIdeal_maximal.isPrime

theorem localizationToResidue_eq_zero_iff_not_isUnit
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (a : Localization.AtPrime d.primeIdeal) :
    BrauerBlockReduction.localizationToResidue d a = 0 ↔ ¬ IsUnit a := by
  let : d.primeIdeal.IsMaximal := d.primeIdeal_maximal
  let : Field (BrauerBlockReduction.principalResidueField d) :=
    Ideal.Quotient.field d.primeIdeal
  have hsurjective : Function.Surjective
      (BrauerBlockReduction.localizationToResidue d) := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap (cyclotomicOrder d.eta)
      (Localization.AtPrime d.primeIdeal) b, ?_⟩
    exact BrauerBlockReduction.localizationToResidue_algebraMap d b
  have hkerMaximal :
      (RingHom.ker (BrauerBlockReduction.localizationToResidue d)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective
      (BrauerBlockReduction.localizationToResidue d) hsurjective
  have hker : RingHom.ker (BrauerBlockReduction.localizationToResidue d) =
      IsLocalRing.maximalIdeal (Localization.AtPrime d.primeIdeal) :=
    IsLocalRing.eq_maximalIdeal hkerMaximal
  rw [← RingHom.mem_ker, hker, IsLocalRing.mem_maximalIdeal]
  rfl

end ModularBlock.BlockPrimitivity

