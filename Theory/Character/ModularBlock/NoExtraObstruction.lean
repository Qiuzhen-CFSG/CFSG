module
public import Theory.Character.ModularBlock.ObstructionOrbit
public import Theory.Character.ModularBlock.ObstructionGrowth
public import Theory.Character.ModularBlock.ExactNormalizerSupport

/-!
# No extra factor in a principal Brauer image

An extra obstruction is a primitive augmentation-zero factor below the
principal Brauer image at a two-subgroup. If any exists, choose one of
maximal subgroup order. Its normalizer orbit sum is a nonzero fixed
idempotent. Maximal coefficient support in the normalizer either equals
the original subgroup, contradicting principal-corner transfer, or yields
a strictly larger extra obstruction.

This is the involution-independent part of the maximal-obstruction proof
ported from `Submission/ZStar/BrauerThirdMain.lean` at c3503435.
It supplies principal Brauer equality at arbitrary two-subgroups for the
block-subsection arguments of ABG III.5, while preserving the existing
involution theorem as a consumer. No correspondence theorem is assumed.
-/

public section
noncomputable section
namespace ModularBlock.BrauerThirdMain
open ModularBlock Subgroup PrincipalBlockConstruction
universe v
attribute [local instance] Fintype.ofFinite

theorem not_isExtraObstruction
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    ¬ IsExtraObstruction d Q := by
  intro hQobs
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQobs, hQmax⟩ :=
    exists_maximal_extraObstruction d ⟨Q, hQobs⟩
  have hQ : IsPGroup 2 Q := hQobs.1
  obtain ⟨b, Bc, hbPrimitive, hbAug, hbExtra,
      hBcCenter, hBcIdem, hBcNe, hBcAug, hBcAmbient,
      hbBc, hBcFixed⟩ :=
    normalizerOrbitWitness_of_extraObstruction d Q hQobs
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let P : Subgroup N := Q.subgroupOf N
  let E := NormalizerBrauerAction.normalizerAlgebraEmbedding K Q
  let BN : MonoidAlgebra K N := E Bc
  have hBNne : BN ≠ 0 := by
    intro hzero
    apply hBcNe
    apply NormalizerBrauerAction.normalizerAlgebraEmbedding_injective
      (R := K) Q
    simpa [BN, E] using hzero
  obtain ⟨D, hDMax⟩ :=
    DefectSupport.exists_isMaximalTwoCoefficientSupport BN hBNne
  have hPp : IsPGroup 2 P := by
    simpa [P, N] using subgroupOf_normalizer_isPGroup Q hQ
  have hPnormal : P.Normal := by
    infer_instance
  have hcoeff : ∀ n : N, BN.coeff n ≠ 0 →
      n ∈ Subgroup.centralizer (P : Set N) := by
    intro n hn
    simpa [BN, E, P, N] using
      normalizerAlgebraEmbedding_coeff_centralizes Q Bc n hn
  have hPLeD : P ≤ D :=
    DefectSupport.normalTwoSubgroup_le_of_isMaximalTwoCoefficientSupport_of_coeff_centralizes
      BN D hDMax P hPp hPnormal hcoeff
  by_cases hDP : D = P
  · have hPMax : DefectSupport.IsMaximalTwoCoefficientSupport
        (NormalizerBrauerAction.normalizerAlgebraEmbedding K Q Bc)
        (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) := by
      simpa [BN, E, P, N, hDP] using hDMax
    exact false_of_exact_normalizer_support
      d Q hQ Bc hBcIdem hBcNe hBcAug hBcAmbient hBcFixed hPMax
  · have hPD : P < D :=
      lt_of_le_of_ne hPLeD (Ne.symm hDP)
    obtain ⟨DG, hDGobs, hcard⟩ :=
      exists_larger_extraObstruction_of_strict_normalizer_support
        d Q hQ Bc hBcIdem hBcAug hBcAmbient hBcFixed
        D (by simpa [BN, E, N] using hDMax)
        (by simpa [P, N] using hPD)
    exact (Nat.not_lt_of_ge (hQmax DG hDGobs)) hcard

end ModularBlock.BrauerThirdMain
