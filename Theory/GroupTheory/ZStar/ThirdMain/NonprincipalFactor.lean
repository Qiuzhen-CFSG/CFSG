module

public import Theory.GroupTheory.ZStar.ThirdMain.AmbientBrauerFactor
public import Theory.Character.ModularBlock.SubgroupPrincipalBrauer
public import Theory.Character.ModularBlock.PrincipalAugmentationOrthogonality

/-!
# The extracted ambient factor is nonprincipal

The reusable orthogonality lemma is re-exported from Theory.
A primitive central factor of augmentation zero is orthogonal to the
compatible principal selector: otherwise primitivity identifies them,
contradicting the principal selector's augmentation one. Applying this to
the admissible factor shows that it lies under the extra subgroup Brauer
factor, while retaining the direct ambient factor and centralizer conditions.

Ported from the nonprincipal-factor and primitive augmentation-zero arguments
in `c3503435:glauberman_zStar/Submission/ZStar/ThirdMainReduction.lean`.
-/

public section
noncomputable section
namespace Glauberman.ZStar.ThirdMainReduction
open ModularBlock PrincipalBlockConstruction
universe u
attribute [local instance] Fintype.ofFinite

export ModularBlock.PrincipalAugmentationOrthogonality
  (primitiveAugmentationZero_mul_localPrincipal_eq_zero)

theorem exists_admissible_primitiveAmbientBrauerFactor_orthogonal_principal_of_not_brauerEquality
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
          β * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
              (Subgroup.centralizer
                ((Q.map H.subtype : Subgroup G) : Set G)) = 0 ∧
          β * SubgroupPrincipalBrauer.extraBrauerFactor d
              (Q.map H.subtype : Subgroup G) = β ∧
          Subgroup.centralizer
              ((Q.map H.subtype : Subgroup G) : Set G) ≤ H := by
  dsimp only
  obtain ⟨Q, β, hQ, hβprimitive, hβaug, hβambient, hQadmissible⟩ :=
    exists_admissible_primitiveAmbientBrauerFactor_of_not_brauerEquality
      d z hzI hne
  let H := Subgroup.centralizer ({z} : Set G)
  let K := BrauerBlockReduction.principalResidueField d
  let QG : Subgroup G := Q.map H.subtype
  let C : Subgroup G := Subgroup.centralizer (QG : Set G)
  let eLocal : MonoidAlgebra K C :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
  have hβLocal : β * eLocal = 0 := by
    exact primitiveAugmentationZero_mul_localPrincipal_eq_zero d C β hβprimitive hβaug
  have hβExtra : β * SubgroupPrincipalBrauer.extraBrauerFactor d QG = β := by
    rw [SubgroupPrincipalBrauer.extraBrauerFactor, mul_sub]
    change β *
          DefectSupport.subgroupCentralizerRestriction K QG
              (BrauerBlockReduction.reducedPrincipalBlockElement d) -
        β * eLocal = β
    rw [show β *
          DefectSupport.subgroupCentralizerRestriction K QG
              (BrauerBlockReduction.reducedPrincipalBlockElement d) = β by
        simpa [QG, K, H] using hβambient,
      hβLocal, sub_zero]
  exact ⟨Q, β, hQ, hβprimitive, hβaug, hβambient,
    by simpa [eLocal, C, QG, K, H] using hβLocal,
    by simpa [QG, K, H] using hβExtra, hQadmissible⟩

end Glauberman.ZStar.ThirdMainReduction
