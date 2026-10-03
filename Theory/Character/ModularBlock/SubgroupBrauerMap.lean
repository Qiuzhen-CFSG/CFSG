module
public import Theory.Character.ModularBlock.AugmentationSylowSupport
public import Theory.Character.ModularBlock.PrincipalReduction

/-!
# Sylow support of the reduced principal selector

For every finite group and chosen principal congruence-block datum, every
Sylow two-subgroup is a maximal coefficient-support subgroup of the reduced
principal selector. Its coefficient ring is the actual residue field of the
chosen prime above two.

The selector reduction is central and has augmentation one. The generic
augmentation-support theorem therefore applies, since the residue field
is nontrivial and has characteristic two. This module assembles the generic
subgroup Brauer restriction and Sylow-support results with principal
reduction, retaining the public subgroup-Brauer API for later defect and
normalizer arguments.

Ported from the final specialization in revision c3503435 of
public/lean-eval/glauberman_zStar, Submission/ZStar/SubgroupBrauerMap.lean.
-/

namespace ModularBlock.SubgroupBrauerMap

/-- Sylow two-subgroups give maximal coefficient support for the reduced
principal congruence-block selector. -/
public theorem reducedPrincipalBlockElement_sylow_isMaximalTwoCoefficientSupport
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (P : Sylow 2 G) :
    DefectSupport.IsMaximalTwoCoefficientSupport
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
      (P : Subgroup G) := by
  apply sylow_isMaximalTwoCoefficientSupport_of_augmentation_ne_zero
    P (BrauerBlockReduction.reducedPrincipalBlockElement d)
    (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)
  rw [BrauerBlockReduction.reducedPrincipalBlockElement_augmentation_eq_one d]
  exact one_ne_zero

end ModularBlock.SubgroupBrauerMap

