module
public import Theory.Character.ModularBlock.NormalizerExtraOrbit

/-!
# Compatibility exports for normalizer Brauer actions

The normalizer-orbit proof for primitive augmentation-zero extra factors is
now in `Theory.Character.ModularBlock.NormalizerExtraOrbit`. This wrapper
preserves the historical action, embedding, principal-factor and orbit-sum
names used by the Glauberman campaign. The embedded-orbit assembly remains
here; only its required orbit-sum prerequisite moves to Theory. Invariance
makes the embedded orbit sum central in the normalizer group algebra, and
injectivity and multiplicativity preserve its nonvanishing and factor
identities. The Theory module records the orbit-sum proof and its source in
`Submission/ZStar/NormalizerBrauerAction.lean` at `c3503435`.
-/

public section
noncomputable section
namespace Glauberman.ZStar.NormalizerBrauerAction
open ModularBlock Subgroup PrincipalBlockConstruction
universe v
attribute [local instance] Fintype.ofFinite

export ModularBlock.NormalizerBrauerAction
  (centralizerConjEquiv
    centralizerConjEquiv_coe
    centralizerConjEquiv_symm_coe
    normalizerConjugate
    normalizerConjugate_apply
    normalizerConjugate_one
    normalizerConjugate_mul
    normalizerConjugate_inv_apply
    normalizerConjugate_apply_inv
    normalizerOrbit
    mem_normalizerOrbit_iff
    self_mem_normalizerOrbit
    image_normalizerConjugate_normalizerOrbit
    normalizerOrbitSum
    normalizerConjugate_orbitSum_eq_self
    subgroupRestriction_mapDomain_centralizerConjEquiv_eq_self
    map_isCentrallyPrimitive
    augmentation_mapDomain_centralizerConjEquiv
    mul_conjugate_eq_zero_or_conjugate_eq
    centralizerToNormalizer
    centralizerToNormalizer_coe
    normalizerAlgebraEmbedding
    normalizerAlgebraEmbedding_single
    normalizerAlgebraEmbedding_injective
    normalizerAlgebraEmbedding_conjugation
    normalizerAlgebraEmbedding_mem_center_of_fixed
    augmentation_normalizerAlgebraEmbedding
    mul_baseEmbedding_ne_zero_of_factor_embeddedOrbitSum
    reducedPrincipalBlockElement_subgroupRestriction_fixed
    localPrincipalBlockElement_mapDomain_centralizerConjEquiv_eq_self
    extraBrauerFactor_mapDomain_centralizerConjEquiv_eq_self
    conjugate_primitiveExtraFactor
    embeddedSubgroupRestriction_principalProperties
    normalizerLocalPrincipal_mul_embeddedSubgroupRestriction_eq_self
    normalizerLocalPrincipal_mul_embeddedCentralizerLocal_eq_self
    embeddedExtraFactor_mul_normalizerLocalPrincipal_eq_zero
    embeddedExtraFactor_properties)

export ModularBlock.NormalizerBrauerAction
  (normalizerOrbitSum_primitiveExtraFactor_properties)

/-- The orbit sum viewed in `K[N_G(Q)]` is a nonzero central idempotent in
the same augmentation-zero extra corner. -/
theorem embeddedNormalizerOrbitSum_primitiveExtraFactor_properties
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hbPrimitive : IsCentrallyPrimitive b)
    (hbAug : groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) b = 0)
    (hbExtra : b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b) :
    let K := BrauerBlockReduction.principalResidueField d
    let B := normalizerAlgebraEmbedding K Q
      (normalizerOrbitSum K Q b)
    B ∈ Set.center
        (MonoidAlgebra K (Subgroup.normalizer (Q : Set G))) ∧
      IsIdempotentElem B ∧
      B ≠ 0 ∧
      groupAlgebraAugmentation K
        (Subgroup.normalizer (Q : Set G)) B = 0 ∧
      B * normalizerAlgebraEmbedding K Q
          (SubgroupPrincipalBrauer.extraBrauerFactor d Q) = B ∧
      normalizerAlgebraEmbedding K Q b * B =
        normalizerAlgebraEmbedding K Q b := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let Bc := normalizerOrbitSum K Q b
  have hOrbit := normalizerOrbitSum_primitiveExtraFactor_properties
    d Q b hbPrimitive hbAug hbExtra
  rcases hOrbit with
    ⟨hBcCenter, hBcIdem, hBcNe, hBcAug, hBcExtra, hBcLeft, hBcFixed⟩
  have hBNcenter : E Bc ∈ Set.center (MonoidAlgebra K N) := by
    apply normalizerAlgebraEmbedding_mem_center_of_fixed Q Bc
    intro n
    exact hBcFixed n
  have hBNidem : IsIdempotentElem (E Bc) := by
    exact hBcIdem.map E
  have hEinj : Function.Injective E :=
    normalizerAlgebraEmbedding_injective (R := K) Q
  have hBNne : E Bc ≠ 0 := by
    intro hzero
    apply hBcNe
    apply hEinj
    simpa using hzero
  have hBNaug :
      groupAlgebraAugmentation K N (E Bc) = 0 := by
    calc
      groupAlgebraAugmentation K N (E Bc) =
          groupAlgebraAugmentation K C Bc := by
        exact augmentation_normalizerAlgebraEmbedding Q Bc
      _ = 0 := hBcAug
  have hBNextra :
      E Bc * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) = E Bc := by
    rw [← E.map_mul, hBcExtra]
  have hBNleft : E b * E Bc = E b := by
    rw [← E.map_mul, hBcLeft]
  exact ⟨by simpa [E, Bc, K, C, N] using hBNcenter,
    by simpa [E, Bc, K, C, N] using hBNidem,
    by simpa [E, Bc, K, C, N] using hBNne,
    by simpa [E, Bc, K, C, N] using hBNaug,
    by simpa [E, Bc, K, C, N] using hBNextra,
    by simpa [E, Bc, K, C, N] using hBNleft⟩

end Glauberman.ZStar.NormalizerBrauerAction
