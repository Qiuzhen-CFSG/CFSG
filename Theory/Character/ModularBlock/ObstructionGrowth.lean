module

public import Theory.Character.ModularBlock.ExtraObstruction
public import Theory.Character.ModularBlock.PrimitiveExtraFactor
public import Theory.Character.ModularBlock.NormalizerSupportGrowth

/-!
# Growth of primitive extra obstructions

A maximal coefficient-support subgroup strictly larger than the canonical
copy of Q in its normalizer yields an extra obstruction of larger ambient
order. The generic normalizer-support transport theorem supplies a nonzero
central idempotent with augmentation zero and the direct ambient Brauer
factor identity. Primitive-factor extraction then places a primitive factor
under the extra Brauer complement. The transported subgroup's strict order
increase is unchanged, supplying the growth branch of the maximal-obstruction
contradiction in Brauer's third main theorem.

This preserves the exact statement of
`exists_larger_extraObstruction_of_strict_normalizer_support` from
`public/lean-eval/glauberman_zStar`, `Submission/ZStar/BrauerThirdMain.lean`
(revision `c3503435`); its coefficient transport is isolated in
`Theory.Character.ModularBlock.NormalizerSupportGrowth`.
-/

public section

namespace ModularBlock.BrauerThirdMain

open ModularBlock PrincipalBlockConstruction

universe v

/-- A strictly larger maximal coefficient-support subgroup produces a
strictly larger primitive extra obstruction in the ambient group. -/
theorem exists_larger_extraObstruction_of_strict_normalizer_support
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (Bc : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hBcIdem : IsIdempotentElem Bc)
    (hBcAug : groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) Bc = 0)
    (hBcAmbient : Bc * DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d) Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = Bc)
    (hBcFixed : ∀ n : Subgroup.normalizer (Q : Set G),
      NormalizerBrauerAction.normalizerConjugate
        (BrauerBlockReduction.principalResidueField d) Q n Bc = Bc)
    (D : Subgroup (Subgroup.normalizer (Q : Set G)))
    (hDMax : DefectSupport.IsMaximalTwoCoefficientSupport
      (NormalizerBrauerAction.normalizerAlgebraEmbedding
        (BrauerBlockReduction.principalResidueField d) Q Bc) D)
    (hPD : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) < D) :
    ∃ DG : Subgroup G,
      IsExtraObstruction d DG ∧ Nat.card Q < Nat.card DG := by
  obtain ⟨DG, g, hDG, hgCenter, hgIdem, hgNe, hgAug, hgFactor, hcard⟩ :=
    ModularBlock.BrauerThirdMain.exists_larger_directBrauerIdempotent_of_strict_normalizer_support
      d Q hQ Bc hBcIdem hBcAug hBcAmbient hBcFixed D hDMax hPD
  obtain ⟨b, hbPrimitive, hbAug, hbExtra⟩ :=
    exists_primitiveExtraFactor_of_centralIdempotent
      d DG hDG g hgCenter hgIdem hgNe hgAug hgFactor
  exact ⟨DG, ⟨hDG, b, hbPrimitive, hbAug, hbExtra⟩, hcard⟩

end ModularBlock.BrauerThirdMain

