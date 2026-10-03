module

public import Theory.Character.ModularBlock.NormalizerAction
public import Theory.Character.ModularBlock.SubgroupPrincipalBrauer

/-!
# Normalizer invariance of principal and extra Brauer factors

The ambient principal restriction is fixed coefficientwise by normalizer
conjugation. The compatible local principal selector is also fixed: its
conjugate is primitive with augmentation one, hence has nonzero intersection
with the original primitive selector and equals it. Their complementary
factor is therefore fixed, so conjugation preserves all defining properties
of a primitive augmentation-zero factor below that complement.

Ported from the corresponding embedding and principal-action parts of
`c3503435:glauberman_zStar/Submission/ZStar/NormalizerBrauerAction.lean`.
The original public names and hypotheses are retained.
-/

public section
noncomputable section
namespace ModularBlock.NormalizerBrauerAction
open Subgroup PrincipalBlockConstruction
universe u v
attribute [local instance] Fintype.ofFinite

private theorem mul_ne_zero_of_augmentation_eq_one
    {R H : Type*} [CommRing R] [Nontrivial R] [Group H]
    {a b : MonoidAlgebra R H}
    (ha : groupAlgebraAugmentation R H a = 1)
    (hb : groupAlgebraAugmentation R H b = 1) : a * b ≠ 0 := by
  intro hzero
  have h := congrArg (groupAlgebraAugmentation R H) hzero
  rw [map_mul, ha, hb, one_mul, map_zero] at h
  exact one_ne_zero h

/-- The direct Brauer image of the ambient principal selector is fixed by
the normalizer action. -/
theorem reducedPrincipalBlockElement_subgroupRestriction_fixed
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G)) :
    MonoidAlgebra.mapDomainRingEquiv
        (BrauerBlockReduction.principalResidueField d)
        (centralizerConjEquiv Q n)
        (DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d)) =
      DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d) := by
  exact subgroupRestriction_mapDomain_centralizerConjEquiv_eq_self
    Q n (BrauerBlockReduction.reducedPrincipalBlockElement d)
    (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)

/-- The compatible principal block of `C_G(Q)` is fixed by every element of
`N_G(Q)`.  Algebraically, its conjugate is again centrally primitive with
augmentation one, so it has nonzero intersection with the original
principal block and hence must coincide with it. -/
theorem localPrincipalBlockElement_mapDomain_centralizerConjEquiv_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G)) :
    MonoidAlgebra.mapDomainRingEquiv
        (BrauerBlockReduction.principalResidueField d)
        (centralizerConjEquiv Q n)
        (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G))) =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer (Q : Set G)) := by
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let E := MonoidAlgebra.mapDomainRingEquiv K (centralizerConjEquiv Q n)
  let eLocal : MonoidAlgebra K C :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
  have hLocalPrimitive : IsCentrallyPrimitive eLocal := by
    simpa [eLocal, C, K] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d C
  have hImagePrimitive : IsCentrallyPrimitive (E eLocal) :=
    map_isCentrallyPrimitive E hLocalPrimitive
  have hImageAug : groupAlgebraAugmentation K C (E eLocal) = 1 := by
    rw [show groupAlgebraAugmentation K C (E eLocal) =
        groupAlgebraAugmentation K C eLocal by
      simpa [E, C, K] using
        augmentation_mapDomain_centralizerConjEquiv Q n eLocal]
    simpa [eLocal, C, K] using
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
        d C
  have hProductNe : E eLocal * eLocal ≠ 0 := by
    apply mul_ne_zero_of_augmentation_eq_one
    · exact hImageAug
    · simpa [eLocal, C, K] using
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
          d C
  have heq : E eLocal = eLocal :=
    CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
      hImagePrimitive hLocalPrimitive hProductNe
  simpa [E, eLocal, C, K] using heq

/-- Hence the augmentation-zero complementary factor under the direct
Brauer image is also fixed by `N_G(Q)`. -/
theorem extraBrauerFactor_mapDomain_centralizerConjEquiv_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G)) :
    MonoidAlgebra.mapDomainRingEquiv
        (BrauerBlockReduction.principalResidueField d)
        (centralizerConjEquiv Q n)
        (SubgroupPrincipalBrauer.extraBrauerFactor d Q) =
      SubgroupPrincipalBrauer.extraBrauerFactor d Q := by
  rw [SubgroupPrincipalBrauer.extraBrauerFactor, map_sub,
    reducedPrincipalBlockElement_subgroupRestriction_fixed d Q n,
    localPrincipalBlockElement_mapDomain_centralizerConjEquiv_eq_self d Q n]

/-- Normalizer conjugation preserves every defining property of a primitive
nonprincipal factor under the direct ambient Brauer image. -/
theorem conjugate_primitiveExtraFactor
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G))
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hbPrimitive : IsCentrallyPrimitive b)
    (hbAug : groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) b = 0)
    (hbExtra : b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b) :
    let b' := MonoidAlgebra.mapDomainRingEquiv
      (BrauerBlockReduction.principalResidueField d)
      (centralizerConjEquiv Q n) b
    IsCentrallyPrimitive b' ∧
      groupAlgebraAugmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G)) b' = 0 ∧
      b' * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b' := by
  dsimp only
  let E := MonoidAlgebra.mapDomainRingEquiv
    (BrauerBlockReduction.principalResidueField d)
    (centralizerConjEquiv Q n)
  have hPrimitive : IsCentrallyPrimitive (E b) :=
    map_isCentrallyPrimitive E hbPrimitive
  have hAug : groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) (E b) = 0 := by
    rw [show groupAlgebraAugmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G)) (E b) =
        groupAlgebraAugmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G)) b by
      simpa [E] using augmentation_mapDomain_centralizerConjEquiv Q n b,
      hbAug]
  have hExtra : E b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = E b := by
    have hmap := congrArg E hbExtra
    rw [map_mul,
      extraBrauerFactor_mapDomain_centralizerConjEquiv_eq_self d Q n] at hmap
    exact hmap
  exact ⟨hPrimitive, hAug, hExtra⟩

end ModularBlock.NormalizerBrauerAction
