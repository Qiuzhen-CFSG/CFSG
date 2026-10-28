module

public import Glauberman.ZStar.ThirdMain.NonprincipalFactor
public import Glauberman.ZStar.ThirdMain.NormalizerFactor
public import Glauberman.ZStar.NormalizerBrauerPair

/-!
# A normalizer obstruction from failed principal Brauer equality

Failure of involution principal Brauer equality yields an admissible primitive
augmentation-zero factor in a two-subgroup centralizer. Its normalizer
conjugates remain primitive extra factors and are equal or orthogonal.
The orbit-sum extraction supplies a primitive normalizer factor in the extra
corner which meets the original embedded factor. Finally, the subgroup is
Sylow or has a strictly larger two-subgroup inside its normalizer.

This assembles the critical normalizer route from
`c3503435:glauberman_zStar/Submission/ZStar/ThirdMainReduction.lean`.
The lower extraction modules also export the nonprincipal ambient-factor
and augmentation-zero orthogonality results used by BrauerThirdMain. No
Brauer correspondence or Third Main assumption enters this reduction.
-/

public section
noncomputable section
namespace Glauberman.ZStar.ThirdMainReduction
open ModularBlock PrincipalBlockConstruction
universe u
attribute [local instance] Fintype.ofFinite

theorem exists_admissible_primitiveAmbientBrauerFactor_with_normalizerOrbit_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let K := BrauerBlockReduction.principalResidueField d
    ∃ Q : Subgroup H,
      ∃ β : MonoidAlgebra K
          (Subgroup.centralizer
            ((Q.map H.subtype : Subgroup G) : Set G)),
        IsPGroup 2 (Q.map H.subtype : Subgroup G) ∧
          IsCentrallyPrimitive β ∧
          groupAlgebraAugmentation K
              (Subgroup.centralizer
                ((Q.map H.subtype : Subgroup G) : Set G)) β = 0 ∧
          β * DefectSupport.subgroupCentralizerRestriction K
              (Q.map H.subtype : Subgroup G)
              (BrauerBlockReduction.reducedPrincipalBlockElement d) = β ∧
          β * SubgroupPrincipalBrauer.extraBrauerFactor d
              (Q.map H.subtype : Subgroup G) = β ∧
          Subgroup.centralizer
              ((Q.map H.subtype : Subgroup G) : Set G) ≤ H ∧
          ∀ n : Subgroup.normalizer
              ((Q.map H.subtype : Subgroup G) : Set G),
            let βn := MonoidAlgebra.mapDomainRingEquiv K
              (NormalizerBrauerAction.centralizerConjEquiv
                (Q.map H.subtype : Subgroup G) n) β
            IsCentrallyPrimitive βn ∧
              groupAlgebraAugmentation K
                  (Subgroup.centralizer
                    ((Q.map H.subtype : Subgroup G) : Set G)) βn = 0 ∧
              βn * SubgroupPrincipalBrauer.extraBrauerFactor d
                  (Q.map H.subtype : Subgroup G) = βn ∧
              (β * βn = 0 ∨ βn = β) := by
  dsimp only
  obtain ⟨Q, β, hQ, hβprimitive, hβaug, hβambient,
      _hβlocal, hβextra, hQadmissible⟩ :=
    exists_admissible_primitiveAmbientBrauerFactor_orthogonal_principal_of_not_brauerEquality
      d z hzI hne
  let H := Subgroup.centralizer ({z} : Set G)
  let K := BrauerBlockReduction.principalResidueField d
  let QG : Subgroup G := Q.map H.subtype
  refine ⟨Q, β, hQ, hβprimitive, hβaug, hβambient,
    hβextra, hQadmissible, ?_⟩
  intro n
  have hconj := NormalizerBrauerAction.conjugate_primitiveExtraFactor
    d QG n β hβprimitive hβaug hβextra
  have horbit :=
    NormalizerBrauerAction.mul_conjugate_eq_zero_or_conjugate_eq
      (R := K) QG n β hβprimitive
  exact ⟨hconj.1, hconj.2.1, hconj.2.2,
    by simpa [QG, K, H] using horbit⟩

theorem exists_admissible_primitiveNormalizerFactor_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let K := BrauerBlockReduction.principalResidueField d
    ∃ Q : Subgroup H,
      let QG : Subgroup G := Q.map H.subtype
      ∃ β : MonoidAlgebra K (Subgroup.centralizer (QG : Set G)),
        ∃ α : MonoidAlgebra K (Subgroup.normalizer (QG : Set G)),
          IsPGroup 2 QG ∧
          IsCentrallyPrimitive β ∧
          groupAlgebraAugmentation K
              (Subgroup.centralizer (QG : Set G)) β = 0 ∧
          β * DefectSupport.subgroupCentralizerRestriction K
              QG
              (BrauerBlockReduction.reducedPrincipalBlockElement d) = β ∧
          β * SubgroupPrincipalBrauer.extraBrauerFactor d QG = β ∧
          Subgroup.centralizer (QG : Set G) ≤ H ∧
          IsCentrallyPrimitive α ∧
          groupAlgebraAugmentation K
              (Subgroup.normalizer (QG : Set G)) α = 0 ∧
          α * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
              (Subgroup.normalizer (QG : Set G)) = 0 ∧
          α * NormalizerBrauerAction.normalizerAlgebraEmbedding K
              QG
              (NormalizerBrauerAction.normalizerOrbitSum K
                QG β) = α ∧
          α * NormalizerBrauerAction.normalizerAlgebraEmbedding K
              QG (SubgroupPrincipalBrauer.extraBrauerFactor d QG) = α ∧
          α * NormalizerBrauerAction.normalizerAlgebraEmbedding K QG
              (DefectSupport.subgroupCentralizerRestriction K QG
                (BrauerBlockReduction.reducedPrincipalBlockElement d)) = α ∧
          α * NormalizerBrauerAction.normalizerAlgebraEmbedding K
              QG β ≠ 0 := by
  dsimp only
  let H := Subgroup.centralizer ({z} : Set G)
  let K := BrauerBlockReduction.principalResidueField d
  obtain ⟨Q, β, hQ, hβprimitive, hβaug, hβambient,
      hβextra, hQadmissible, _horbit⟩ :=
    exists_admissible_primitiveAmbientBrauerFactor_with_normalizerOrbit_of_not_brauerEquality
      d z hzI hne
  let QG : Subgroup G := Q.map H.subtype
  obtain ⟨α, hαprimitive, hαaug, hαlocal, hαfactor, hαextra,
      hαambient, hαleft⟩ :=
    exists_primitiveNormalizerFactor_of_extra d QG β
      hQ hβprimitive hβaug hβextra
  exact ⟨Q, β, α, hQ, hβprimitive, hβaug, hβambient, hβextra,
    hQadmissible, hαprimitive, hαaug, hαlocal,
    hαfactor, hαextra, hαambient, hαleft⟩

theorem exists_normalizerExtraObstruction_with_growth_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let K := BrauerBlockReduction.principalResidueField d
    ∃ Q : Subgroup H,
      let QG : Subgroup G := Q.map H.subtype
      ∃ β : MonoidAlgebra K (Subgroup.centralizer (QG : Set G)),
        ∃ α : MonoidAlgebra K (Subgroup.normalizer (QG : Set G)),
          IsPGroup 2 QG ∧
          IsCentrallyPrimitive β ∧
          groupAlgebraAugmentation K
              (Subgroup.centralizer (QG : Set G)) β = 0 ∧
          β * SubgroupPrincipalBrauer.extraBrauerFactor d QG = β ∧
          Subgroup.centralizer (QG : Set G) ≤ H ∧
          IsCentrallyPrimitive α ∧
          groupAlgebraAugmentation K
              (Subgroup.normalizer (QG : Set G)) α = 0 ∧
          α * NormalizerBrauerAction.normalizerAlgebraEmbedding K QG
              (SubgroupPrincipalBrauer.extraBrauerFactor d QG) = α ∧
          α * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
              (Subgroup.normalizer (QG : Set G)) = 0 ∧
          α * NormalizerBrauerAction.normalizerAlgebraEmbedding K QG β ≠ 0 ∧
          ((∃ P : Sylow 2 G, (P : Subgroup G) = QG) ∨
            ∃ R : Subgroup G,
              IsPGroup 2 R ∧
                QG < R ∧
                R ≤ Subgroup.normalizer QG ∧
                Nat.card QG < Nat.card R) := by
  dsimp only
  let H := Subgroup.centralizer ({z} : Set G)
  let K := BrauerBlockReduction.principalResidueField d
  obtain ⟨Q, β, α, hQ, hβprimitive, hβaug, _hβambient, hβextra,
      hQadmissible, hαprimitive, hαaug, hαlocal, _hαfactor,
      hαextra, _hαambient, hαleft⟩ :=
    exists_admissible_primitiveNormalizerFactor_of_not_brauerEquality
      d z hzI hne
  let QG : Subgroup G := Q.map H.subtype
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstep :=
    NormalizerBrauerPair.exists_sylow_eq_or_exists_strict_supergroup_le_normalizer
      QG hQ
  exact ⟨Q, β, α, hQ, hβprimitive, hβaug, hβextra,
    hQadmissible, hαprimitive, hαaug, hαextra, hαlocal, hαleft,
    by simpa [QG, H] using hstep⟩


end Glauberman.ZStar.ThirdMainReduction
