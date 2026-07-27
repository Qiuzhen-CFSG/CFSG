import Submission.ZStar.BlockPrimitivity
import Submission.ZStar.SubgroupBrauerMap

/-!
# The principal block inside a subgroup Brauer image

For every `2`-subgroup `Q`, the Brauer restriction of the reduced ambient
principal-block idempotent has augmentation one.  Consequently it contains
the compatible principal-block idempotent of `C_G(Q)` as a factor.

This is only the elementary principal-factor direction: it does not assert
that the Brauer image has no additional block factors.
-/

noncomputable section

namespace Submission.ZStar
namespace SubgroupPrincipalBrauer

open PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

/-- The direct subgroup Brauer image of the reduced ambient principal-block
idempotent is central. -/
theorem reducedPrincipalBlockElement_subgroupRestriction_mem_center
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d) ∈
      Set.center
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G))) := by
  exact SubgroupBrauerMap.subgroupCentralizerRestriction_mem_center
    Q (BrauerBlockReduction.reducedPrincipalBlockElement d)
    (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)

/-- The direct subgroup Brauer image of the reduced ambient principal-block
idempotent is idempotent. -/
theorem reducedPrincipalBlockElement_subgroupRestriction_isIdempotent
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    IsIdempotentElem
      (DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact
    SubgroupBrauerMap.subgroupCentralizerRestriction_isIdempotent_of_mem_center
      Q hQ (BrauerBlockReduction.reducedPrincipalBlockElement d)
      (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)
      (BrauerBlockReduction.reducedPrincipalBlockElement_isIdempotent d)

/-- Subgroup Brauer restriction preserves the augmentation-one property of
the ambient principal selector. -/
theorem reducedPrincipalBlockElement_subgroupRestriction_augmentation_eq_one
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G))
        (DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d)) = 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
      Q hQ (BrauerBlockReduction.reducedPrincipalBlockElement d)
      (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d),
    AugmentationScratch.reducedPrincipalBlockElement_augmentation_eq_one]

/-- The compatible principal block of `C_G(Q)` is a factor of the direct
`Q`-Brauer image of the ambient principal block.

Both idempotents have augmentation one, so their product is nonzero.  The
product is a central-idempotent factor of the centrally primitive local
principal selector and therefore equals that selector. -/
theorem localPrincipalBlockElement_mul_subgroupRestriction_eq_self
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G)) *
        DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer (Q : Set G)) := by
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let eLocal : MonoidAlgebra K C :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
  let eGQ : MonoidAlgebra K C :=
    DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hLocalPrimitive : BlockPrimitivity.IsCentrallyPrimitive eLocal := by
    simpa [eLocal, K, C] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d C
  have hGQCenter : eGQ ∈ Set.center (MonoidAlgebra K C) := by
    simpa [eGQ, K, C] using
      reducedPrincipalBlockElement_subgroupRestriction_mem_center d Q
  have hGQIdem : IsIdempotentElem eGQ := by
    simpa [eGQ, K, C] using
      reducedPrincipalBlockElement_subgroupRestriction_isIdempotent d Q hQ
  have hProductNe : eLocal * eGQ ≠ 0 := by
    apply AugmentationScratch.mul_ne_zero_of_augmentation_eq_one
    · simpa [eLocal, K, C] using
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
          d C
    · simpa [eGQ, K, C] using
        reducedPrincipalBlockElement_subgroupRestriction_augmentation_eq_one
          d Q hQ
  have hCommute : Commute eLocal eGQ :=
    (Semigroup.mem_center_iff.mp hLocalPrimitive.1 eGQ).symm
  have hProductCenter : eLocal * eGQ ∈ Set.center (MonoidAlgebra K C) :=
    Set.mul_mem_center hLocalPrimitive.1 hGQCenter
  have hProductIdem : IsIdempotentElem (eLocal * eGQ) :=
    IsIdempotentElem.mul_of_commute hCommute
      hLocalPrimitive.2.1 hGQIdem
  have hProductFactor : (eLocal * eGQ) * eLocal = eLocal * eGQ := by
    calc
      (eLocal * eGQ) * eLocal = eLocal * (eGQ * eLocal) :=
        mul_assoc _ _ _
      _ = eLocal * (eLocal * eGQ) := by rw [hCommute.eq.symm]
      _ = (eLocal * eLocal) * eGQ := (mul_assoc _ _ _).symm
      _ = eLocal * eGQ := by rw [hLocalPrimitive.2.1.eq]
  change eLocal * eGQ = eLocal
  exact hLocalPrimitive.2.2.2 (eLocal * eGQ)
    hProductCenter hProductIdem hProductFactor hProductNe

/-- The complementary part of the direct `Q`-Brauer image after removing
the compatible principal block of `C_G(Q)`. -/
noncomputable def extraBrauerFactor
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) :=
  DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d) Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) -
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer (Q : Set G))

theorem extraBrauerFactor_mem_center
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    extraBrauerFactor d Q ∈
      Set.center
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G))) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  rw [extraBrauerFactor, mul_sub, sub_mul,
    Semigroup.mem_center_iff.mp
      (reducedPrincipalBlockElement_subgroupRestriction_mem_center d Q) a,
    Semigroup.mem_center_iff.mp
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_mem_center
        d (Subgroup.centralizer (Q : Set G))) a]

/-- The direct subgroup Brauer image splits as its principal factor plus the
complementary factor. -/
theorem subgroupRestriction_eq_local_add_extra
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d) =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G)) +
        extraBrauerFactor d Q := by
  simp [extraBrauerFactor]

theorem extraBrauerFactor_isIdempotent
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    IsIdempotentElem (extraBrauerFactor d Q) := by
  let eLocal :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer (Q : Set G))
  let eGQ := DefectSupport.subgroupCentralizerRestriction
    (BrauerBlockReduction.principalResidueField d) Q
    (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hfactor : eLocal * eGQ = eLocal := by
    simpa [eLocal, eGQ] using
      localPrincipalBlockElement_mul_subgroupRestriction_eq_self d Q hQ
  have hcomm : eGQ * eLocal = eLocal := by
    have hc := Semigroup.mem_center_iff.mp
      (reducedPrincipalBlockElement_subgroupRestriction_mem_center d Q) eLocal
    exact hc.symm.trans hfactor
  change IsIdempotentElem (eGQ - eLocal)
  exact IsIdempotentElem.sub
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d (Subgroup.centralizer (Q : Set G)))
    (reducedPrincipalBlockElement_subgroupRestriction_isIdempotent d Q hQ)
    hfactor hcomm

theorem extraBrauerFactor_mul_local_eq_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    extraBrauerFactor d Q *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G)) = 0 := by
  let eLocal :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer (Q : Set G))
  let eGQ := DefectSupport.subgroupCentralizerRestriction
    (BrauerBlockReduction.principalResidueField d) Q
    (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hfactor : eLocal * eGQ = eLocal := by
    simpa [eLocal, eGQ] using
      localPrincipalBlockElement_mul_subgroupRestriction_eq_self d Q hQ
  have hcomm : eGQ * eLocal = eLocal := by
    have hc := Semigroup.mem_center_iff.mp
      (reducedPrincipalBlockElement_subgroupRestriction_mem_center d Q) eLocal
    exact hc.symm.trans hfactor
  change (eGQ - eLocal) * eLocal = 0
  rw [sub_mul, hcomm,
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d (Subgroup.centralizer (Q : Set G)), sub_self]

theorem extraBrauerFactor_mul_subgroupRestriction_eq_self
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    extraBrauerFactor d Q *
        DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) =
      extraBrauerFactor d Q := by
  let eLocal :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer (Q : Set G))
  let eGQ := DefectSupport.subgroupCentralizerRestriction
    (BrauerBlockReduction.principalResidueField d) Q
    (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hfactor : eLocal * eGQ = eLocal := by
    simpa [eLocal, eGQ] using
      localPrincipalBlockElement_mul_subgroupRestriction_eq_self d Q hQ
  change (eGQ - eLocal) * eGQ = eGQ - eLocal
  rw [sub_mul,
    reducedPrincipalBlockElement_subgroupRestriction_isIdempotent d Q hQ,
    hfactor]

/-- The complementary direct Brauer factor has augmentation zero. -/
theorem extraBrauerFactor_augmentation_eq_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G))
        (extraBrauerFactor d Q) = 0 := by
  rw [extraBrauerFactor, map_sub,
    reducedPrincipalBlockElement_subgroupRestriction_augmentation_eq_one d Q hQ,
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one,
    sub_self]

/-- The direct subgroup Brauer image equals its compatible principal factor
exactly when its complementary factor vanishes. -/
theorem subgroupRestriction_eq_local_iff_extra_eq_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G)) ↔
      extraBrauerFactor d Q = 0 := by
  rw [extraBrauerFactor, sub_eq_zero]

end SubgroupPrincipalBrauer
end Submission.ZStar
