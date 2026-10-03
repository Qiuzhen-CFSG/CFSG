module

public import Theory.Character.ModularBlock.ExtraObstruction
public import Theory.Character.ModularBlock.NormalizerExtraOrbit

/-!
# The normalizer-orbit witness of an extra obstruction

The distinct normalizer conjugates of a primitive extra factor sum to a
fixed nonzero central idempotent of augmentation zero. The proved orbit-sum
properties preserve the extra-factor relation; composing it with the
direct-image factor identity puts the sum below the ambient principal
Brauer image. The resulting witness is the input to the exact-support
versus strict-support cases in the Third Main argument.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerThirdMain.lean` (revision `c3503435`).
-/

public section

noncomputable section

namespace ModularBlock.BrauerThirdMain

open ModularBlock PrincipalBlockConstruction

universe v

/-- The normalizer orbit sum packages an extra obstruction into a fixed
central idempotent, while preserving the direct ambient factor identity. -/
theorem normalizerOrbitWitness_of_extraObstruction
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQobs : IsExtraObstruction d Q) :
    let K := BrauerBlockReduction.principalResidueField d
    ∃ b : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)),
      ∃ Bc : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)),
        IsCentrallyPrimitive b ∧
        groupAlgebraAugmentation K
            (Subgroup.centralizer (Q : Set G)) b = 0 ∧
        b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b ∧
        Bc ∈ Set.center (MonoidAlgebra K
            (Subgroup.centralizer (Q : Set G))) ∧
        IsIdempotentElem Bc ∧ Bc ≠ 0 ∧
        groupAlgebraAugmentation K
            (Subgroup.centralizer (Q : Set G)) Bc = 0 ∧
        Bc * DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d) = Bc ∧
        b * Bc = b ∧
        (∀ n : Subgroup.normalizer (Q : Set G),
          NormalizerBrauerAction.normalizerConjugate K Q n Bc = Bc) := by
  dsimp only
  rcases hQobs with ⟨hQ, b, hbPrimitive, hbAug, hbExtra⟩
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let Bc := NormalizerBrauerAction.normalizerOrbitSum K Q b
  obtain ⟨hBcCenter, hBcIdem, hBcNe, hBcAug, hBcExtra, hBcLeft,
      hBcFixed⟩ :=
    NormalizerBrauerAction.normalizerOrbitSum_primitiveExtraFactor_properties
      d Q b hbPrimitive hbAug hbExtra
  have hBcAmbient : Bc * DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = Bc := by
    have hExtraAmbient :=
      SubgroupPrincipalBrauer.extraBrauerFactor_mul_subgroupRestriction_eq_self
        d Q hQ
    calc
      Bc * DefectSupport.subgroupCentralizerRestriction K Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) =
          (Bc * SubgroupPrincipalBrauer.extraBrauerFactor d Q) *
            DefectSupport.subgroupCentralizerRestriction K Q
              (BrauerBlockReduction.reducedPrincipalBlockElement d) := by
                rw [hBcExtra]
      _ = Bc * (SubgroupPrincipalBrauer.extraBrauerFactor d Q *
            DefectSupport.subgroupCentralizerRestriction K Q
              (BrauerBlockReduction.reducedPrincipalBlockElement d)) := by
                rw [mul_assoc]
      _ = Bc * SubgroupPrincipalBrauer.extraBrauerFactor d Q := by
                rw [hExtraAmbient]
      _ = Bc := hBcExtra
  exact ⟨b, Bc, hbPrimitive, hbAug, hbExtra,
    by simpa [Bc, C, K] using hBcCenter,
    by simpa [Bc, C, K] using hBcIdem,
    by simpa [Bc, C, K] using hBcNe,
    by simpa [Bc, C, K] using hBcAug,
    by simpa [Bc, C, K] using hBcAmbient,
    by simpa [Bc, C, K] using hBcLeft,
    by simpa [Bc, C, K] using hBcFixed⟩

end ModularBlock.BrauerThirdMain

