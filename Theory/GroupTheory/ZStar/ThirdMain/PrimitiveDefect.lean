module

public import Theory.Character.ModularBlock.InvolutionExtraFactor
public import Theory.Character.ModularBlock.DefectSupport
public import Theory.Character.ModularBlock.SubgroupBrauerMap

/-!
# A primitive maximal-support witness to failed principal Brauer equality

Failure of principal Brauer equality makes the extra involution factor
nonzero. Choose a two-subgroup of maximal coefficient support. The central
involution then forces its ambient centralizer into the involution
centralizer. The subgroup Brauer homomorphism sees this extra factor;
finite-ring primitive-factor extraction produces a central primitive factor
with the same maximal support. Any larger support of that factor would also
support the extra factor, contradicting maximality.

This is the first extraction step of Brauer's Third Main argument. Ported
from the live maximal-support and primitive-defect statements in
`c3503435:glauberman_zStar/Submission/ZStar/ThirdMainReduction.lean`.
The finite residue-field theorem is a compatibility wrapper around the
shared cyclotomic finite-quotient result.
-/

public section
noncomputable section
namespace Glauberman.ZStar.ThirdMainReduction
open ModularBlock PrincipalBlockConstruction
universe u
attribute [local instance] Fintype.ofFinite

theorem principalResidueField_finite
    {G : Type u} [Group G] [Finite G] (d : PrincipalCongruenceBlockData G) :
    Finite (BrauerBlockReduction.principalResidueField d) :=
  FiniteFieldPrimitivity.principalResidueField_finite d

theorem exists_admissible_maximalSupport_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let b := RelativeTransferBrauer.extraBrauerFactor d z
    ∃ Q : Subgroup H,
      DefectSupport.IsMaximalTwoCoefficientSupport b Q ∧
        Subgroup.centralizer
            ((Q.map H.subtype : Subgroup G) : Set G) ≤ H := by
  dsimp only
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) H :=
    RelativeTransferBrauer.extraBrauerFactor d z
  have hbne : b ≠ 0 := by
    intro hbzero
    apply hne
    change CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H =
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
    have hsub :
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
            CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H = 0 := by
      simpa only [b, H, RelativeTransferBrauer.extraBrauerFactor] using hbzero
    exact (sub_eq_zero.mp hsub).symm
  obtain ⟨Q, hQ⟩ :=
    DefectSupport.exists_isMaximalTwoCoefficientSupport
      (G := H) b hbne
  refine ⟨Q, hQ, ?_⟩
  exact
    DefectSupport.ambientCentralizer_le_involutionCentralizer_of_maximalSupport
      (R := BrauerBlockReduction.principalResidueField d) (G := G)
      z hzI.1 (by simpa [pow_two] using hzI.2) b Q hQ

theorem exists_admissible_primitiveDefectBlock_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let b := RelativeTransferBrauer.extraBrauerFactor d z
    ∃ Q : Subgroup H,
      ∃ f : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) H,
        IsCentrallyPrimitive f ∧
          f * b = f ∧
          DefectSupport.IsMaximalTwoCoefficientSupport f Q ∧
          Subgroup.centralizer
              ((Q.map H.subtype : Subgroup G) : Set G) ≤ H := by
  dsimp only
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let K := BrauerBlockReduction.principalResidueField d
  let b : MonoidAlgebra K H := RelativeTransferBrauer.extraBrauerFactor d z
  obtain ⟨Q, hQ, hQadmissible⟩ :=
    exists_admissible_maximalSupport_of_not_brauerEquality d z hzI hne
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite K := principalResidueField_finite d
  let : Fintype K := Fintype.ofFinite K
  let : Fintype H := Fintype.ofFinite H
  let : DecidableEq H := Classical.decEq H
  let : Finite (MonoidAlgebra K H) := by
    exact Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  have hz : z * z = 1 := by simpa [pow_two] using hzI.2
  have hbcenter : b ∈ Set.center (MonoidAlgebra K H) := by
    simpa [b, K, H] using RelativeTransferBrauer.extraBrauerFactor_mem_center d z
  have hbidem : IsIdempotentElem b := by
    simpa [b, K, H] using
      RelativeTransferBrauer.extraBrauerFactor_isIdempotent d z hz
  let phi := SubgroupBrauerMap.subgroupCentralizerRestrictionCenterHom
    2 K Q hQ.1.1
  have hbrb : DefectSupport.subgroupCentralizerRestriction K Q b ≠ 0 :=
    (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero b Q).mp
      hQ.1 |>.2
  have hphiB : phi ⟨b, hbcenter⟩ ≠ 0 := by
    intro hzero
    apply hbrb
    have hzero' := congrArg
      (fun x : Subring.center
          (MonoidAlgebra K (Subgroup.centralizer (Q : Set H))) =>
        (x : MonoidAlgebra K (Subgroup.centralizer (Q : Set H)))) hzero
    simpa [phi] using hzero'
  obtain ⟨fCI, hfprimitive, hfb, hfphi⟩ :=
    CentralPrimitiveExistence.exists_isCentrallyPrimitive_factor_map_ne_zero
      phi b hbcenter hbidem hphiB
  let f : MonoidAlgebra K H := fCI.val
  have hfbr : DefectSupport.subgroupCentralizerRestriction K Q f ≠ 0 := by
    intro hzero
    apply hfphi
    apply Subtype.ext
    change DefectSupport.subgroupCentralizerRestriction K Q fCI.val = 0
    exact hzero
  have hfSupportQ : DefectSupport.HasTwoCoefficientSupport f Q :=
    (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero f Q).mpr
      ⟨hQ.1.1, hfbr⟩
  have hfMax : DefectSupport.IsMaximalTwoCoefficientSupport f Q := by
    refine ⟨hfSupportQ, ?_⟩
    intro Q' hQ'f
    have hfbr' : DefectSupport.subgroupCentralizerRestriction K Q' f ≠ 0 :=
      (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero f Q').mp
        hQ'f |>.2
    have hbbr' : DefectSupport.subgroupCentralizerRestriction K Q' b ≠ 0 := by
      intro hbzero
      apply hfbr'
      have hmul :=
        SubgroupBrauerMap.subgroupCentralizerRestriction_mul_of_mem_center
          Q' hQ'f.1 f b hfprimitive.1 hbcenter
      rw [hfb, hbzero, mul_zero] at hmul
      exact hmul
    apply hQ.2 Q'
    exact
      (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero b Q').mpr
        ⟨hQ'f.1, hbbr'⟩
  exact ⟨Q, f, hfprimitive, hfb, hfMax, hQadmissible⟩

end Glauberman.ZStar.ThirdMainReduction

