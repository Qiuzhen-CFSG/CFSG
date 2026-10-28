module

public import Theory.Character.ModularBlock.NormalizerFixedTerm
public import Theory.Character.ModularBlock.FixedCosetTransfer
public import Theory.Character.ModularBlock.SubgroupCornerVanishing

/-!
# Exact normalizer support contradicts the principal corner

A nonzero normalizer-fixed idempotent of augmentation zero below a direct
principal Brauer image cannot have exact maximal coefficient support at
the original two-subgroup. Embed the factor in its normalizer algebra and
transfer it to the ambient group. Nonidentity fixed cosets vanish by exact
support, while the identity coset recovers the original factor under Brauer
restriction. Multiplication by the ambient principal selector puts this
transfer in the augmentation-zero principal corner. Corner nilpotence then
forces its recovered idempotent factor to be zero, a contradiction.

This is the exact-support branch of the Third Main maximal-obstruction
argument. It requires no normalizer-orbit construction or prior obstruction.
Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerThirdMain.lean` (revision `c3503435`).
-/

public section

noncomputable section

namespace ModularBlock.BrauerThirdMain

open PrincipalBlockConstruction

universe v

attribute [local instance] Fintype.ofFinite

/-- Exact normalizer support is impossible for a nonzero fixed
augmentation-zero factor under the direct principal Brauer image. -/
theorem false_of_exact_normalizer_support
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (Bc : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hBcIdem : IsIdempotentElem Bc)
    (hBcNe : Bc ≠ 0)
    (hBcAug : groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) Bc = 0)
    (hBcAmbient : Bc * DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d) Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = Bc)
    (hBcFixed : ∀ n : Subgroup.normalizer (Q : Set G),
      NormalizerBrauerAction.normalizerConjugate
        (BrauerBlockReduction.principalResidueField d) Q n Bc = Bc)
    (hMax : DefectSupport.IsMaximalTwoCoefficientSupport
      (NormalizerBrauerAction.normalizerAlgebraEmbedding
        (BrauerBlockReduction.principalResidueField d) Q Bc)
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))) :
    False := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let E := NormalizerBrauerAction.normalizerAlgebraEmbedding K Q
  let BN : MonoidAlgebra K N := E Bc
  let T : MonoidAlgebra K G :=
    RelativeTransferBrauer.relativeTransfer K N BN
  let eG : MonoidAlgebra K G :=
    BrauerBlockReduction.reducedPrincipalBlockElement d
  let a : MonoidAlgebra K G := T * eG
  have hBNcenter : BN ∈ Set.center (MonoidAlgebra K N) := by
    exact NormalizerBrauerAction.normalizerAlgebraEmbedding_mem_center_of_fixed
      Q Bc hBcFixed
  have hBNaug : groupAlgebraAugmentation K N BN = 0 := by
    calc
      groupAlgebraAugmentation K N BN =
          groupAlgebraAugmentation K
            (Subgroup.centralizer (Q : Set G)) Bc := by
              exact NormalizerBrauerAction.augmentation_normalizerAlgebraEmbedding
                Q Bc
      _ = 0 := hBcAug
  have hTcenter : T ∈ Set.center (MonoidAlgebra K G) := by
    exact RelativeTransferBrauer.relativeTransfer_mem_center N BN hBNcenter
  have hTaug : groupAlgebraAugmentation K G T = 0 := by
    rw [show groupAlgebraAugmentation K G T =
        (Fintype.card (G ⧸ N) : K) *
          groupAlgebraAugmentation K N BN by
      exact RelativeTransferBrauer.augmentation_relativeTransfer N BN,
      hBNaug, mul_zero]
  have hRecovery : DefectSupport.subgroupCentralizerRestriction K Q T = Bc := by
    calc
      DefectSupport.subgroupCentralizerRestriction K Q T =
          DefectSupport.subgroupCentralizerRestriction K Q
            (RelativeTransferBrauer.subgroupSubtypeMap K N BN) := by
              apply subgroupRestriction_relativeTransfer_eq_subtype_of_fixedTerms_zero
                Q hQ N Q.le_normalizer BN hBNcenter
              intro c hcFixed hcNe
              exact fixedTerm_zero_of_exact_normalizer_support
                Q hQ Bc (by simpa [BN, E, N] using hMax) c hcFixed hcNe
      _ = Bc := by
        simpa [BN, E, N] using
          subgroupRestriction_subgroupSubtypeMap_normalizerAlgebraEmbedding
            (R := K) Q Bc
  have heGcenter : eG ∈ Set.center (MonoidAlgebra K G) := by
    exact BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d
  have heGidem : IsIdempotentElem eG := by
    exact BrauerBlockReduction.reducedPrincipalBlockElement_isIdempotent d
  have haCenter : a ∈ Set.center (MonoidAlgebra K G) :=
    Set.mul_mem_center hTcenter heGcenter
  have haFactor : a * eG = a := by
    calc
      a * eG = T * (eG * eG) := by
        simp only [a, mul_assoc]
      _ = T * eG := by rw [heGidem.eq]
      _ = a := rfl
  have haAug : groupAlgebraAugmentation K G a = 0 := by
    rw [show groupAlgebraAugmentation K G a =
        groupAlgebraAugmentation K G T *
          groupAlgebraAugmentation K G eG by
      exact map_mul (groupAlgebraAugmentation K G) T eG,
      hTaug, zero_mul]
  have haRecovery : DefectSupport.subgroupCentralizerRestriction K Q a = Bc := by
    calc
      DefectSupport.subgroupCentralizerRestriction K Q a =
          DefectSupport.subgroupCentralizerRestriction K Q T *
            DefectSupport.subgroupCentralizerRestriction K Q eG := by
              exact SubgroupBrauerMap.subgroupCentralizerRestriction_mul_of_mem_center
                Q hQ T eG hTcenter heGcenter
      _ = Bc * DefectSupport.subgroupCentralizerRestriction K Q eG := by
            rw [hRecovery]
      _ = Bc := hBcAmbient
  have hzero : Bc = 0 :=
    eq_zero_of_subgroupRestriction_mul_eq_self_of_corner_augmentation_zero
      d Q hQ a Bc haCenter
      (by simpa [eG, a, K] using haFactor)
      (by simpa [a, K] using haAug)
      (by rw [haRecovery, hBcIdem.eq])
  exact hBcNe hzero

end ModularBlock.BrauerThirdMain

