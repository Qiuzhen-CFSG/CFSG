module

public import Glauberman.ZStar.ThirdMain.PrimitiveDefect
public import Glauberman.ZStar.NormalizerBrauerAction

/-!
# Extracting a primitive normalizer factor

The distinct orbit sum of a primitive augmentation-zero extra factor embeds
as a nonzero central idempotent in the normalizer algebra. Finiteness provides
a primitive central factor beneath it. The factor retains augmentation zero,
principal orthogonality, and the extra and ambient factor relations; centrality
forces a nonzero intersection with the original embedded orbit member.

This is `exists_primitiveNormalizerFactor_of_extra` from
`c3503435:glauberman_zStar/Submission/ZStar/ThirdMainReduction.lean`.
It needs only the explicit primitive extra factor and two-subgroup hypotheses,
not the involution obstruction that later supplies them.
-/

public section
noncomputable section
namespace Glauberman.ZStar.ThirdMainReduction
open ModularBlock PrincipalBlockConstruction
universe u
attribute [local instance] Fintype.ofFinite

theorem exists_primitiveNormalizerFactor_of_extra
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (β : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hQ : IsPGroup 2 Q)
    (hβprimitive : IsCentrallyPrimitive β)
    (hβaug : groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) β = 0)
    (hβextra : β * SubgroupPrincipalBrauer.extraBrauerFactor d Q = β) :
    ∃ α : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.normalizer (Q : Set G)),
      IsCentrallyPrimitive α ∧
      groupAlgebraAugmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.normalizer (Q : Set G)) α = 0 ∧
      α * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.normalizer (Q : Set G)) = 0 ∧
      α * NormalizerBrauerAction.normalizerAlgebraEmbedding
          (BrauerBlockReduction.principalResidueField d) Q
          (NormalizerBrauerAction.normalizerOrbitSum
            (BrauerBlockReduction.principalResidueField d) Q β) = α ∧
      α * NormalizerBrauerAction.normalizerAlgebraEmbedding
          (BrauerBlockReduction.principalResidueField d) Q
          (SubgroupPrincipalBrauer.extraBrauerFactor d Q) = α ∧
      α * NormalizerBrauerAction.normalizerAlgebraEmbedding
          (BrauerBlockReduction.principalResidueField d) Q
          (DefectSupport.subgroupCentralizerRestriction
            (BrauerBlockReduction.principalResidueField d) Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d)) = α ∧
      α * NormalizerBrauerAction.normalizerAlgebraEmbedding
          (BrauerBlockReduction.principalResidueField d) Q β ≠ 0 := by
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let E := NormalizerBrauerAction.normalizerAlgebraEmbedding K Q
  let Bc := NormalizerBrauerAction.normalizerOrbitSum K Q β
  let BN := E Bc
  let A := MonoidAlgebra K N
  let : Finite K := principalResidueField_finite d
  let : Field K := Ideal.Quotient.field d.primeIdeal
  let : Fintype K := Fintype.ofFinite K
  let : Fintype N := Fintype.ofFinite N
  let : DecidableEq N := Classical.decEq N
  let : Finite A := by
    exact Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  have hEmbedded :=
    NormalizerBrauerAction.embeddedNormalizerOrbitSum_primitiveExtraFactor_properties
      d Q β hβprimitive hβaug hβextra
  rcases hEmbedded with
    ⟨hBNcenter, hBNidem, hBNne, hBNaug, hBNextra, hBNleft⟩
  have hmap_subtype_ne :
      (Subring.subtype (Subring.center A))
          ⟨BN, hBNcenter⟩ ≠ 0 := by
    intro hzero
    apply hBNne
    exact hzero
  obtain ⟨αCI, hαprimitive, hαfactor, _hαmap⟩ :=
    CentralPrimitiveExistence.exists_isCentrallyPrimitive_factor_map_ne_zero
      (A := A) (B := A) (Subring.subtype (Subring.center A)) BN
      hBNcenter hBNidem hmap_subtype_ne
  let α : A := αCI.val
  have hαaug :
      groupAlgebraAugmentation K N α = 0 := by
    have h := congrArg (groupAlgebraAugmentation K N) hαfactor
    rw [map_mul, hBNaug, mul_zero] at h
    exact h.symm
  have hαextra : α * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) = α := by
    calc
      α * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) =
          (α * BN) * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) := by
            rw [hαfactor]
      _ = α * (BN * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q)) := by
            rw [mul_assoc]
      _ = α * BN := by rw [hBNextra]
      _ = α := hαfactor
  have hαlocal :
      α * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N = 0 := by
    have hExtraLocal :=
      NormalizerBrauerAction.embeddedExtraFactor_mul_normalizerLocalPrincipal_eq_zero
        d Q hQ
    calc
      α * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N =
          (α * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q)) *
            CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N := by
              rw [hαextra]
      _ = α * (E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) *
            CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N) := by
              rw [mul_assoc]
      _ = 0 := by
        rw [show E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) *
              CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N = 0 by
            simpa [E, K, N] using hExtraLocal,
          mul_zero]
  have hExtraAmbient :
      SubgroupPrincipalBrauer.extraBrauerFactor d Q *
          DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d) =
        SubgroupPrincipalBrauer.extraBrauerFactor d Q := by
    exact SubgroupPrincipalBrauer.extraBrauerFactor_mul_subgroupRestriction_eq_self
      d Q hQ
  have hEExtraAmbient :
      E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) *
          E (DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d)) =
        E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) := by
    rw [← E.map_mul, hExtraAmbient]
  have hαambient :
      α * E (DefectSupport.subgroupCentralizerRestriction K Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d)) = α := by
    calc
      α * E (DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d)) =
          (α * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q)) *
            E (DefectSupport.subgroupCentralizerRestriction K Q
              (BrauerBlockReduction.reducedPrincipalBlockElement d)) := by
                rw [hαextra]
      _ = α * (E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) *
            E (DefectSupport.subgroupCentralizerRestriction K Q
              (BrauerBlockReduction.reducedPrincipalBlockElement d))) := by
                rw [mul_assoc]
      _ = α * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) := by
                rw [hEExtraAmbient]
      _ = α := hαextra
  have hαleft : α * E β ≠ 0 := by
    exact NormalizerBrauerAction.mul_baseEmbedding_ne_zero_of_factor_embeddedOrbitSum
      Q β α hαprimitive.1 hαprimitive.2.2.1 hαfactor
  exact ⟨α,
    by simpa [α, A, K, N] using hαprimitive,
    by simpa [α, A, K, N] using hαaug,
    by simpa [α, A, K, N] using hαlocal,
    by simpa [α, A, K, N, E, Bc, BN] using hαfactor,
    by simpa [α, A, K, N, E, Bc, BN] using hαextra,
    by simpa [α, A, K, N, E] using hαambient,
    by simpa [α, A, K, N, E] using hαleft⟩

end Glauberman.ZStar.ThirdMainReduction
