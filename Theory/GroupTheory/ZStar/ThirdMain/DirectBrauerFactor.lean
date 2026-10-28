module

public import Theory.GroupTheory.ZStar.ThirdMain.PrimitiveDefect
public import Theory.Character.ModularBlock.BrauerTransitivity

/-!
# Transporting the primitive defect factor to the ambient Brauer image

The maximal-support primitive factor lies in the involution centralizer.
Its subgroup Brauer restriction is nonzero and factors the iterated ambient
principal image. Admissibility identifies the centralizer inside that
involution centralizer with the ambient centralizer. Transport along this
exact equivalence and Brauer transitivity place the factor under the direct
ambient subgroup Brauer image. Orthogonality to the local principal selector
also gives augmentation zero.

Ported from `primitiveDefectBlock_directBrauerFactor_of_not_brauerEquality`
in `c3503435:glauberman_zStar/Submission/ZStar/ThirdMainReduction.lean`.
This transports the extraction without assuming any Brauer correspondence.
-/

public section
noncomputable section
namespace Glauberman.ZStar.ThirdMainReduction
open ModularBlock PrincipalBlockConstruction
universe u
attribute [local instance] Fintype.ofFinite

theorem primitiveDefectBlock_directBrauerFactor_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let K := BrauerBlockReduction.principalResidueField d
    ∃ Q : Subgroup H,
      ∃ f : MonoidAlgebra K H,
        IsCentrallyPrimitive f ∧
          DefectSupport.IsMaximalTwoCoefficientSupport f Q ∧
          groupAlgebraAugmentation K H f = 0 ∧
          Subgroup.centralizer
              ((Q.map H.subtype : Subgroup G) : Set G) ≤ H ∧
          ∃ E : Subgroup.centralizer (Q : Set H) ≃*
              Subgroup.centralizer
                ((Q.map H.subtype : Subgroup G) : Set G),
            let fQ := DefectSupport.subgroupCentralizerRestriction K Q f
            let eGQ := DefectSupport.subgroupCentralizerRestriction K
              (Q.map H.subtype : Subgroup G)
              (BrauerBlockReduction.reducedPrincipalBlockElement d)
            MonoidAlgebra.mapDomainRingHom K E.toMonoidHom fQ ≠ 0 ∧
              MonoidAlgebra.mapDomainRingHom K E.toMonoidHom fQ * eGQ =
                MonoidAlgebra.mapDomainRingHom K E.toMonoidHom fQ := by
  dsimp only
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let K := BrauerBlockReduction.principalResidueField d
  obtain ⟨Q, f, hfprimitive, hfb, hfMax, hQadmissible⟩ :=
    exists_admissible_primitiveDefectBlock_of_not_brauerEquality d z hzI hne
  let eB : MonoidAlgebra K H :=
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  let E := BrauerTransitivity.centralizerMapEquiv H Q hQadmissible
  let fQ : MonoidAlgebra K (Subgroup.centralizer (Q : Set H)) :=
    DefectSupport.subgroupCentralizerRestriction K Q f
  let bQ : MonoidAlgebra K (Subgroup.centralizer (Q : Set H)) :=
    DefectSupport.subgroupCentralizerRestriction K Q eB
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : z * z = 1 := by simpa [pow_two] using hzI.2
  have heBcenter : eB ∈ Set.center (MonoidAlgebra K H) := by
    simpa [eB, K, H] using
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z
  have horth : f *
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H = 0 := by
    have hmul := congrArg
      (fun x : MonoidAlgebra K H => x *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H)
      hfb
    rw [mul_assoc, RelativeTransferBrauer.extraBrauerFactor_mul_local_eq_zero d z hz,
      mul_zero] at hmul
    exact hmul.symm
  have hfaug : groupAlgebraAugmentation K H f = 0 := by
    exact RelativeTransferBrauer.centralizerFactor_augmentation_eq_zero d z f horth
  have hfrestrict : fQ ≠ 0 := by
    simpa [fQ] using
      (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero f Q).mp
        hfMax.1 |>.2
  have hfB : f * eB = f := by
    have hmul := congrArg (fun x : MonoidAlgebra K H => x * eB) hfb
    have hbB : RelativeTransferBrauer.extraBrauerFactor d z * eB =
        RelativeTransferBrauer.extraBrauerFactor d z := by
      simpa [eB, K, H] using
        RelativeTransferBrauer.extraBrauerFactor_mul_brauer_eq_self d z hz
    rw [mul_assoc, hbB] at hmul
    exact hmul.symm.trans hfb
  have hfactorQ : fQ * bQ = fQ := by
    calc
      fQ * bQ = DefectSupport.subgroupCentralizerRestriction K Q (f * eB) := by
        symm
        exact SubgroupBrauerMap.subgroupCentralizerRestriction_mul_of_mem_center
          Q hfMax.1.1 f eB hfprimitive.1 heBcenter
      _ = fQ := by rw [hfB]
  have hmapf_ne : MonoidAlgebra.mapDomainRingHom K E.toMonoidHom fQ ≠ 0 := by
    intro hzero
    apply hfrestrict
    exact MonoidAlgebra.mapDomain_injective E.injective hzero
  have hmapfactor :
      MonoidAlgebra.mapDomainRingHom K E.toMonoidHom fQ *
          MonoidAlgebra.mapDomainRingHom K E.toMonoidHom bQ =
        MonoidAlgebra.mapDomainRingHom K E.toMonoidHom fQ := by
    rw [← map_mul]
    exact congrArg (MonoidAlgebra.mapDomainRingHom K E.toMonoidHom) hfactorQ
  have htrans :
      MonoidAlgebra.mapDomainRingHom K E.toMonoidHom bQ =
        DefectSupport.subgroupCentralizerRestriction K
          (Q.map H.subtype : Subgroup G)
          (BrauerBlockReduction.reducedPrincipalBlockElement d) := by
    simpa [E, bQ, eB, H, K,
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement] using
      (BrauerTransitivity.mapDomain_iteratedCentralizerRestriction_eq_subgroupRestriction
        (R := K) z Q hQadmissible
          (BrauerBlockReduction.reducedPrincipalBlockElement d))
  rw [htrans] at hmapfactor
  exact ⟨Q, f, hfprimitive, hfMax, hfaug, hQadmissible,
    E, hmapf_ne, hmapfactor⟩

end Glauberman.ZStar.ThirdMainReduction
