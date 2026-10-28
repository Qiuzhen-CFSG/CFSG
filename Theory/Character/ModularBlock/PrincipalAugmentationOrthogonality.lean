module
public import Theory.Character.ModularBlock.SubgroupPrincipalBrauer

/-!
# Orthogonality to the compatible principal selector

A primitive central idempotent of augmentation zero is orthogonal to the
compatible principal selector of any subgroup of a finite group. Otherwise
the two primitive idempotents coincide, contradicting augmentation one of
the principal selector. This isolates the reusable algebraic step from the
involution-specific ambient-factor extraction in Glauberman's Third Main
argument. Source: `Submission/ZStar/ThirdMainReduction.lean` at `c3503435`.
The selectors and their ambient residue-field coefficient maps are unchanged.
-/

public section
noncomputable section
namespace ModularBlock.PrincipalAugmentationOrthogonality
open PrincipalBlockConstruction
universe u
attribute [local instance] Fintype.ofFinite

theorem primitiveAugmentationZero_mul_localPrincipal_eq_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (L : Subgroup G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) L)
    (hbPrimitive : IsCentrallyPrimitive b)
    (hbAug : groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d) L b = 0) :
    b * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d L = 0 := by
  let K := BrauerBlockReduction.principalResidueField d
  let eLocal : MonoidAlgebra K L :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d L
  have hLocalPrimitive : IsCentrallyPrimitive eLocal := by
    simpa [eLocal, K] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d L
  by_contra hnonzero
  have heq : b = eLocal :=
    CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
      hbPrimitive hLocalPrimitive hnonzero
  have haugEq := congrArg (groupAlgebraAugmentation K L) heq
  have hzeroOne : (0 : K) = 1 := by
    calc
      0 = groupAlgebraAugmentation K L b := by
        simpa [K] using hbAug.symm
      _ = groupAlgebraAugmentation K L eLocal := haugEq
      _ = 1 := by
        simpa [eLocal, K] using
          CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
            d L
  exact zero_ne_one hzeroOne

end ModularBlock.PrincipalAugmentationOrthogonality
