module

public import Theory.Character.ModularBlock.NormalizerEmbedding
public import Theory.Character.ModularBlock.NormalizerPrincipalAction

/-!
# Principal and extra factors in the normalizer algebra

The embedded subgroup Brauer image is a central augmentation-one idempotent.
The compatible normalizer principal selector lies under this image and under
the embedded centralizer principal selector: augmentation makes each product
nonzero, and principal primitivity collapses the product to the selector.
The embedded extra factor is consequently orthogonal to the normalizer
principal selector, retaining its centrality, idempotence, augmentation zero,
and factor relation to the ambient restriction.

Ported from the principal-factor comparisons in
`c3503435:glauberman_zStar/Submission/ZStar/NormalizerBrauerAction.lean`.
The 2-subgroup hypothesis is retained exactly where restriction idempotence
or the complementary-factor identity requires it. No block-correspondence
or Third Main assumption enters these comparisons.
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

/-- The direct `Q`-Brauer image of the ambient principal idempotent becomes a
central idempotent of the normalizer algebra. -/
theorem embeddedSubgroupRestriction_principalProperties
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    let K := BrauerBlockReduction.principalResidueField d
    let e := normalizerAlgebraEmbedding K Q
      (DefectSupport.subgroupCentralizerRestriction K Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d))
    e ∈ Set.center (MonoidAlgebra K (Subgroup.normalizer (Q : Set G))) ∧
      IsIdempotentElem e ∧
      e ≠ 0 ∧
      groupAlgebraAugmentation K
        (Subgroup.normalizer (Q : Set G)) e = 1 := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let eC : MonoidAlgebra K C :=
    DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
  let E := normalizerAlgebraEmbedding K Q
  have hfixed : ∀ n : Subgroup.normalizer (Q : Set G),
      normalizerConjugate K Q n eC = eC := by
    intro n
    simpa [normalizerConjugate, eC, K, C] using
      (reducedPrincipalBlockElement_subgroupRestriction_fixed d Q n)
  have hcenter : E eC ∈ Set.center (MonoidAlgebra K N) := by
    exact normalizerAlgebraEmbedding_mem_center_of_fixed Q eC hfixed
  have hidemC : IsIdempotentElem eC := by
    simpa [eC, K, C] using
      SubgroupPrincipalBrauer.reducedPrincipalBlockElement_subgroupRestriction_isIdempotent
        d Q hQ
  have hidem : IsIdempotentElem (E eC) := hidemC.map E
  have haugC : groupAlgebraAugmentation K C eC = 1 := by
    simpa [eC, K, C] using
      SubgroupPrincipalBrauer.reducedPrincipalBlockElement_subgroupRestriction_augmentation_eq_one
        d Q hQ
  have haug : groupAlgebraAugmentation K N (E eC) = 1 := by
    calc
      groupAlgebraAugmentation K N (E eC) =
          groupAlgebraAugmentation K C eC :=
        augmentation_normalizerAlgebraEmbedding Q eC
      _ = 1 := haugC
  have hne : E eC ≠ 0 := by
    intro hzero
    have hzeroAug := congrArg (groupAlgebraAugmentation K N) hzero
    rw [haug, map_zero] at hzeroAug
    exact one_ne_zero hzeroAug
  exact ⟨by simpa [E, eC, K, C, N] using hcenter,
    by simpa [E, eC, K, C, N] using hidem,
    by simpa [E, eC, K, C, N] using hne,
    by simpa [E, eC, K, C, N] using haug⟩

/-! The principal selector of the normalizer is a factor of the embedded
`Q`-Brauer image.  This is the elementary principal part of the normalizer
step; it uses only central primitivity and augmentation, and makes no
Brauer-correspondence or Third Main assumption. -/

theorem normalizerLocalPrincipal_mul_embeddedSubgroupRestriction_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    let K := BrauerBlockReduction.principalResidueField d
    let N := Subgroup.normalizer (Q : Set G)
    let E := normalizerAlgebraEmbedding K Q
    let eN := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
    let eGQ := DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
    eN * E eGQ = eN := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let eN : MonoidAlgebra K N :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
  let eGQ : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)) :=
    DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hNprimitive : IsCentrallyPrimitive eN := by
    simpa [eN, N, K] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d N
  have hNaug : groupAlgebraAugmentation K N eN = 1 := by
    simpa [eN, N, K] using
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
        d N
  obtain ⟨hGQcenter, hGQidem, _hGQne, hGQaug⟩ :=
    embeddedSubgroupRestriction_principalProperties d Q hQ
  have hEcenter : E eGQ ∈ Set.center (MonoidAlgebra K N) := by
    simpa [E, eGQ, N, K] using hGQcenter
  have hEidem : IsIdempotentElem (E eGQ) := by
    simpa [E, eGQ, N, K] using hGQidem
  have hEaug : groupAlgebraAugmentation K N (E eGQ) = 1 := by
    simpa [E, eGQ, N, K] using hGQaug
  have hprodNe : eN * E eGQ ≠ 0 := by
    apply mul_ne_zero_of_augmentation_eq_one
    · exact hNaug
    · exact hEaug
  have hprodCenter : eN * E eGQ ∈ Set.center (MonoidAlgebra K N) :=
    Set.mul_mem_center hNprimitive.1 hEcenter
  have hcomm : Commute eN (E eGQ) :=
    (Semigroup.mem_center_iff.mp hNprimitive.1 (E eGQ)).symm
  have hprodIdem : IsIdempotentElem (eN * E eGQ) :=
    IsIdempotentElem.mul_of_commute hcomm hNprimitive.2.1 hEidem
  have hfactor : (eN * E eGQ) * eN = eN * E eGQ := by
    calc
      (eN * E eGQ) * eN = eN * (E eGQ * eN) := mul_assoc _ _ _
      _ = eN * (eN * E eGQ) := by rw [hcomm.eq]
      _ = (eN * eN) * E eGQ := (mul_assoc _ _ _).symm
      _ = eN * E eGQ := by rw [hNprimitive.2.1.eq]
  exact hNprimitive.2.2.2 (eN * E eGQ)
    hprodCenter hprodIdem hfactor hprodNe

/-! The normalizer principal selector is also a factor of the embedded
principal selector of `C_G(Q)`.  The two factor statements together isolate
the normalizer extra corner without any appeal to a block correspondence. -/

theorem normalizerLocalPrincipal_mul_embeddedCentralizerLocal_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    let K := BrauerBlockReduction.principalResidueField d
    let N := Subgroup.normalizer (Q : Set G)
    let C := Subgroup.centralizer (Q : Set G)
    let E := normalizerAlgebraEmbedding K Q
    let eN := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
    let eC := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
    eN * E eC = eN := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let C := Subgroup.centralizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let eN : MonoidAlgebra K N :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
  let eC : MonoidAlgebra K C :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
  have hNprimitive : IsCentrallyPrimitive eN := by
    simpa [eN, N, K] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d N
  have hNaug : groupAlgebraAugmentation K N eN = 1 := by
    simpa [eN, N, K] using
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
        d N
  have hEcenter : E eC ∈ Set.center (MonoidAlgebra K N) := by
    apply normalizerAlgebraEmbedding_mem_center_of_fixed Q eC
    intro n
    simpa [normalizerConjugate, E, eC, K, C] using
      localPrincipalBlockElement_mapDomain_centralizerConjEquiv_eq_self d Q n
  have hEidem : IsIdempotentElem (E eC) := by
    exact (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d C).map E
  have hEaug : groupAlgebraAugmentation K N (E eC) = 1 := by
    calc
      groupAlgebraAugmentation K N (E eC) =
          groupAlgebraAugmentation K C eC :=
        augmentation_normalizerAlgebraEmbedding Q eC
      _ = 1 := by
        simpa [eC, C, K] using
          CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
            d C
  have hprodNe : eN * E eC ≠ 0 := by
    apply mul_ne_zero_of_augmentation_eq_one
    · exact hNaug
    · exact hEaug
  have hprodCenter : eN * E eC ∈ Set.center (MonoidAlgebra K N) :=
    Set.mul_mem_center hNprimitive.1 hEcenter
  have hcomm : Commute eN (E eC) :=
    (Semigroup.mem_center_iff.mp hNprimitive.1 (E eC)).symm
  have hprodIdem : IsIdempotentElem (eN * E eC) :=
    IsIdempotentElem.mul_of_commute hcomm hNprimitive.2.1 hEidem
  have hfactor : (eN * E eC) * eN = eN * E eC := by
    calc
      (eN * E eC) * eN = eN * (E eC * eN) := mul_assoc _ _ _
      _ = eN * (eN * E eC) := by rw [hcomm.eq]
      _ = (eN * eN) * E eC := (mul_assoc _ _ _).symm
      _ = eN * E eC := by rw [hNprimitive.2.1.eq]
  exact hNprimitive.2.2.2 (eN * E eC)
    hprodCenter hprodIdem hfactor hprodNe

theorem embeddedExtraFactor_mul_normalizerLocalPrincipal_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    let K := BrauerBlockReduction.principalResidueField d
    let N := Subgroup.normalizer (Q : Set G)
    let E := normalizerAlgebraEmbedding K Q
    let eN := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
    E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * eN = 0 := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let C := Subgroup.centralizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let eN : MonoidAlgebra K N :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
  let eC : MonoidAlgebra K C :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
  have hNfactor : eN * E eC = eN := by
    simpa [eN, eC, N, C, E, K] using
      normalizerLocalPrincipal_mul_embeddedCentralizerLocal_eq_self d Q
  have horthC : SubgroupPrincipalBrauer.extraBrauerFactor d Q * eC = 0 := by
    simpa [eC, C, K] using
      SubgroupPrincipalBrauer.extraBrauerFactor_mul_local_eq_zero d Q hQ
  have hExtraCenter :
      E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) ∈
        Set.center (MonoidAlgebra K N) := by
    apply normalizerAlgebraEmbedding_mem_center_of_fixed Q
      (SubgroupPrincipalBrauer.extraBrauerFactor d Q)
    intro n
    exact extraBrauerFactor_mapDomain_centralizerConjEquiv_eq_self d Q n
  have hExtraComm :
      Commute (E (SubgroupPrincipalBrauer.extraBrauerFactor d Q)) eN :=
    (Semigroup.mem_center_iff.mp hExtraCenter eN).symm
  calc
    E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * eN =
        E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * (eN * E eC) := by
          rw [hNfactor]
    _ = (E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * eN) * E eC := by
          rw [mul_assoc]
    _ = (eN * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q)) * E eC := by
          rw [hExtraComm.eq]
    _ = eN * (E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * E eC) := by
          rw [mul_assoc]
    _ = eN * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q * eC) := by
          rw [← E.map_mul]
    _ = 0 := by rw [horthC, map_zero, mul_zero]

/-- The complementary `Q`-Brauer factor remains a central idempotent after
embedding in the normalizer algebra.  It has augmentation zero, is
orthogonal to the normalizer principal block, and is still a factor of the
embedded direct ambient Brauer image. -/
theorem embeddedExtraFactor_properties
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    let K := BrauerBlockReduction.principalResidueField d
    let N := Subgroup.normalizer (Q : Set G)
    let E := normalizerAlgebraEmbedding K Q
    let eExtra := E (SubgroupPrincipalBrauer.extraBrauerFactor d Q)
    let eN := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
    let eGQ := DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
    eExtra ∈ Set.center (MonoidAlgebra K N) ∧
      IsIdempotentElem eExtra ∧
      groupAlgebraAugmentation K N eExtra = 0 ∧
      eExtra * eN = 0 ∧
      eExtra * E eGQ = eExtra := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let eExtraC : MonoidAlgebra K C :=
    SubgroupPrincipalBrauer.extraBrauerFactor d Q
  let eExtra : MonoidAlgebra K N := E eExtraC
  let eN : MonoidAlgebra K N :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
  let eGQ : MonoidAlgebra K C :=
    DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hcenter : eExtra ∈ Set.center (MonoidAlgebra K N) := by
    apply normalizerAlgebraEmbedding_mem_center_of_fixed Q eExtraC
    intro n
    simpa [normalizerConjugate, eExtraC, K, C] using
      extraBrauerFactor_mapDomain_centralizerConjEquiv_eq_self d Q n
  have hidem : IsIdempotentElem eExtra := by
    exact (SubgroupPrincipalBrauer.extraBrauerFactor_isIdempotent d Q hQ).map E
  have haug : groupAlgebraAugmentation K N eExtra = 0 := by
    calc
      groupAlgebraAugmentation K N eExtra =
          groupAlgebraAugmentation K C eExtraC := by
        exact augmentation_normalizerAlgebraEmbedding Q eExtraC
      _ = 0 := by
        simpa [eExtraC, C, K] using
          SubgroupPrincipalBrauer.extraBrauerFactor_augmentation_eq_zero d Q hQ
  have horth : eExtra * eN = 0 := by
    simpa [eExtra, eExtraC, eN, E, N, K] using
      embeddedExtraFactor_mul_normalizerLocalPrincipal_eq_zero d Q hQ
  have hfactorC : eExtraC * eGQ = eExtraC := by
    simpa [eExtraC, eGQ, C, K] using
      SubgroupPrincipalBrauer.extraBrauerFactor_mul_subgroupRestriction_eq_self
        d Q hQ
  have hfactor : eExtra * E eGQ = eExtra := by
    change E eExtraC * E eGQ = E eExtraC
    rw [← E.map_mul, hfactorC]
  exact ⟨by simpa [eExtra, eExtraC, E, N, K] using hcenter,
    by simpa [eExtra, eExtraC, E, N, K] using hidem,
    by simpa [eExtra, eExtraC, E, N, K] using haug,
    by simpa [eExtra, eExtraC, eN, E, N, K] using horth,
    by simpa [eExtra, eExtraC, eGQ, E, N, K] using hfactor⟩

end ModularBlock.NormalizerBrauerAction
