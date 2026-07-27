import Submission.ZStar.DefectSupport
import Submission.ZStar.RelativeTransferBrauer
import Submission.ZStar.SubgroupBrauerMap
import Submission.ZStar.CentralPrimitiveExistence
import Submission.ZStar.BrauerTransitivity
import Submission.ZStar.SubgroupPrincipalBrauer
import Submission.ZStar.CentralPrimitiveFactor
import Submission.ZStar.NormalizerBrauerPair
import Submission.ZStar.NormalizerBrauerAction

/-!
# Reduction of principal Brauer equality to an admissible extra factor

If the involution principal-Brauer equality fails, the complementary local
idempotent is nonzero.  The coefficient-support construction then supplies a
maximal supporting 2-subgroup, and the central involution forces the
admissibility inequality required in Juhász's proof of Brauer's Third Main
Theorem.

No correspondence theorem is assumed here.  The remaining step is precisely
to use First Main plus Nagao to rule out this admissible extra factor over the
ambient principal block.
-/

noncomputable section

namespace Submission.ZStar
namespace ThirdMainReduction

open PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

theorem principalResidueField_finite
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) :
    Finite (BrauerBlockReduction.principalResidueField d) := by
  have hprime_ne_bot : d.primeIdeal ≠ ⊥ := by
    intro hbot
    have htwo := BlockPreliminaries.two_mem_of_liesOver
      d.primeIdeal d.primeIdeal_liesOverTwo
    have hzero : (2 : Representation.cyclotomicOrder d.eta) = 0 := by
      simpa [hbot] using htwo
    exact two_ne_zero hzero
  exact CyclotomicDVR.cyclotomicOrder_quotient_finite
    (Nat.card_pos (α := G)).ne' d.eta_spec d.primeIdeal hprime_ne_bot

/-- Failure of principal Brauer equality produces an admissible maximal
2-subgroup in the coefficient support of the extra local factor. -/
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

/-- The maximal-support witness produced by failure of principal Brauer
equality has a genuinely nonzero central-idempotent Brauer image.  This is
the block-pair datum to which First Main and Nagao must be applied. -/
theorem exists_admissible_nonzeroCentralIdempotentBrauerImage_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let b := RelativeTransferBrauer.extraBrauerFactor d z
    ∃ Q : Subgroup H,
      DefectSupport.IsMaximalTwoCoefficientSupport b Q ∧
        Subgroup.centralizer
            ((Q.map H.subtype : Subgroup G) : Set G) ≤ H ∧
        (DefectSupport.subgroupCentralizerRestriction
            (BrauerBlockReduction.principalResidueField d) Q b ∈
          Set.center
            (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
              (Subgroup.centralizer (Q : Set H)))) ∧
        IsIdempotentElem
          (DefectSupport.subgroupCentralizerRestriction
            (BrauerBlockReduction.principalResidueField d) Q b) ∧
        DefectSupport.subgroupCentralizerRestriction
            (BrauerBlockReduction.principalResidueField d) Q b ≠ 0 := by
  dsimp only
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) H :=
    RelativeTransferBrauer.extraBrauerFactor d z
  obtain ⟨Q, hQ, hQadmissible⟩ :=
    exists_admissible_maximalSupport_of_not_brauerEquality d z hzI hne
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : z * z = 1 := by simpa [pow_two] using hzI.2
  have himage :=
    SubgroupBrauerMap.maximalSupport_restriction_isNonzeroCentralIdempotent
      b (by simpa [b, H] using RelativeTransferBrauer.extraBrauerFactor_mem_center d z)
      (by simpa [b, H] using RelativeTransferBrauer.extraBrauerFactor_isIdempotent d z hz)
      Q hQ
  exact ⟨Q, hQ, hQadmissible, himage⟩

/-- Refine the extra idempotent to an actual block idempotent without losing
the chosen defect subgroup.  Thus failure of principal Brauer equality
produces an admissible nonprincipal block with a genuine maximal Brauer
defect group; the remaining step is exactly Third Main. -/
theorem exists_admissible_primitiveDefectBlock_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let b := RelativeTransferBrauer.extraBrauerFactor d z
    ∃ Q : Subgroup H,
      ∃ f : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) H,
        BlockPrimitivity.IsCentrallyPrimitive f ∧
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
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite K := principalResidueField_finite d
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype H := Fintype.ofFinite H
  letI : DecidableEq H := Classical.decEq H
  letI : Finite (MonoidAlgebra K H) := by
    change Finite (H →₀ K)
    infer_instance
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

/-! The primitive witness can be placed on the two complementary sides of
the local and ambient selectors.  These are the exact properties needed by
the First Main/Nagao correspondence argument below.  Notice that no
Brauer-equality statement is used as an assumption here: the two displayed
factor identities are consequences of the witness relation `f * b = f` and
of the defining complementary-factor identities for `b`.
-/

/-- Failure of principal Brauer equality produces an admissible centrally
primitive local block factor which is orthogonal to the compatible local
principal selector (hence has augmentation zero), while remaining a factor
of the ambient principal Brauer image. -/
theorem exists_admissible_primitiveDefectBlock_orthogonal_local_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let b := RelativeTransferBrauer.extraBrauerFactor d z
    ∃ Q : Subgroup H,
      ∃ f : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) H,
        BlockPrimitivity.IsCentrallyPrimitive f ∧
          f * b = f ∧
          f * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H = 0 ∧
          AugmentationScratch.augmentation
              (BrauerBlockReduction.principalResidueField d) H f = 0 ∧
          f * BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z = f ∧
          DefectSupport.IsMaximalTwoCoefficientSupport f Q ∧
          Subgroup.centralizer
              ((Q.map H.subtype : Subgroup G) : Set G) ≤ H := by
  dsimp only
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let K := BrauerBlockReduction.principalResidueField d
  let b : MonoidAlgebra K H := RelativeTransferBrauer.extraBrauerFactor d z
  obtain ⟨Q, f, hfprimitive, hfb, hfMax, hQadmissible⟩ :=
    exists_admissible_primitiveDefectBlock_of_not_brauerEquality d z hzI hne
  have hz : z * z = 1 := by simpa [pow_two] using hzI.2
  have horth : f *
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H = 0 := by
    have hmul := congrArg
      (fun x : MonoidAlgebra K H => x *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H)
      hfb
    rw [mul_assoc, RelativeTransferBrauer.extraBrauerFactor_mul_local_eq_zero d z hz,
      mul_zero] at hmul
    exact hmul.symm
  have hfaug : AugmentationScratch.augmentation K H f = 0 := by
    exact RelativeTransferBrauer.centralizerFactor_augmentation_eq_zero d z f horth
  have hfambient : f *
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z = f := by
    have hmul := congrArg
      (fun x : MonoidAlgebra K H => x *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z)
      hfb
    rw [mul_assoc, RelativeTransferBrauer.extraBrauerFactor_mul_brauer_eq_self d z hz] at hmul
    exact hmul.symm.trans hfb
  exact ⟨Q, f, hfprimitive, hfb, horth, hfaug, hfambient, hfMax, hQadmissible⟩

/-! A maximal support factor still contains the distinguished central
involution of the centralizer.  This is a support statement, not a block
correspondence assertion. -/

theorem primitiveDefectBlock_support_contains_involution
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    ∃ Q : Subgroup H,
      ∃ f : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) H,
        BlockPrimitivity.IsCentrallyPrimitive f ∧
          DefectSupport.IsMaximalTwoCoefficientSupport f Q ∧
          ∃ zH : H, (zH : G) = z ∧ zH ∈ Q := by
  dsimp only
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  obtain ⟨Q, f, hfprimitive, _hfb, hfMax, _hQadmissible⟩ :=
    exists_admissible_primitiveDefectBlock_of_not_brauerEquality d z hzI hne
  have hzHmem : z ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  let zH : H := ⟨z, hzHmem⟩
  have hzHne : zH ≠ 1 := by
    intro h
    apply hzI.1
    exact congrArg Subtype.val h
  have hzHsq : zH * zH = 1 := by
    apply Subtype.ext
    simpa [zH] using (show z * z = 1 from by simpa [pow_two] using hzI.2)
  have hzHcenter : zH ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp h.2
  have hzHQ : zH ∈ Q :=
    DefectSupport.centralInvolution_mem_of_isMaximalTwoCoefficientSupport
      f Q hfMax zH hzHne hzHsq hzHcenter
  exact ⟨Q, f, hfprimitive, hfMax, zH, rfl, hzHQ⟩

/-! The primitive witness gives a nonzero factor of the direct ambient
Brauer image at its maximal support subgroup.  This is the precise
coefficient-level input for a First Main/Nagao correspondence theorem. -/

theorem primitiveDefectBlock_directBrauerFactor_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let K := BrauerBlockReduction.principalResidueField d
    ∃ Q : Subgroup H,
      ∃ f : MonoidAlgebra K H,
        BlockPrimitivity.IsCentrallyPrimitive f ∧
          DefectSupport.IsMaximalTwoCoefficientSupport f Q ∧
          AugmentationScratch.augmentation K H f = 0 ∧
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
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have hfaug : AugmentationScratch.augmentation K H f = 0 := by
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
    exact Finsupp.mapDomain_injective E.injective hzero
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

/-! Extracting one primitive factor from the direct ambient image gives an
actual Brauer-pair witness.  This is still only an algebraic extraction; the
statement that such an admissible pair over the principal block must itself
be principal is the remaining Third Main input. -/

theorem exists_admissible_primitiveAmbientBrauerFactor_of_not_brauerEquality
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
          BlockPrimitivity.IsCentrallyPrimitive β ∧
          AugmentationScratch.augmentation K
              (Subgroup.centralizer
                ((Q.map H.subtype : Subgroup G) : Set G)) β = 0 ∧
          β * DefectSupport.subgroupCentralizerRestriction K
              (Q.map H.subtype : Subgroup G)
              (BrauerBlockReduction.reducedPrincipalBlockElement d) = β ∧
          Subgroup.centralizer
              ((Q.map H.subtype : Subgroup G) : Set G) ≤ H := by
  dsimp only
  obtain ⟨Q, f, hfprimitive, hfMax, hfaug, hQadmissible,
      E, _hmapf_ne, hmapfactor⟩ :=
    primitiveDefectBlock_directBrauerFactor_of_not_brauerEquality d z hzI hne
  let C : Subgroup G := Subgroup.centralizer
    ((Q.map (Subgroup.centralizer ({z} : Set G)).subtype :
      Subgroup G) : Set G)
  let A := MonoidAlgebra (BrauerBlockReduction.principalResidueField d) C
  let g : A :=
    MonoidAlgebra.mapDomainRingEquiv
      (BrauerBlockReduction.principalResidueField d) E
      (DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q f)
  let eGQ : A :=
    DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d)
      (Q.map (Subgroup.centralizer ({z} : Set G)).subtype : Subgroup G)
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
  letI : Finite (BrauerBlockReduction.principalResidueField d) :=
    principalResidueField_finite d
  letI : Fintype (BrauerBlockReduction.principalResidueField d) :=
    Fintype.ofFinite (BrauerBlockReduction.principalResidueField d)
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : Finite A := by
    change Finite (C →₀ BrauerBlockReduction.principalResidueField d)
    infer_instance
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfQcenter :
      DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q f ∈
        Set.center
          (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer
            (Q : Set (Subgroup.centralizer ({z} : Set G))))) := by
    exact SubgroupBrauerMap.subgroupCentralizerRestriction_mem_center
      Q f hfprimitive.1
  have hfQidem :
      IsIdempotentElem
        (DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q f) := by
    exact SubgroupBrauerMap.subgroupCentralizerRestriction_isIdempotent_of_mem_center
      Q hfMax.1.1 f hfprimitive.1 hfprimitive.2.1
  have hgcenter : g ∈ Set.center A := by
    simpa [g, A, C] using
      BrauerTransitivity.mapDomainRingEquiv_mem_center
        (R := BrauerBlockReduction.principalResidueField d) E
        (DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q f) hfQcenter
  have hgidem : IsIdempotentElem g := by
    change IsIdempotentElem
      (MonoidAlgebra.mapDomainRingEquiv
        (BrauerBlockReduction.principalResidueField d) E
        (DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q f))
    exact BrauerTransitivity.mapDomainRingEquiv_isIdempotent
      (R := BrauerBlockReduction.principalResidueField d) E
      (DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q f) hfQidem
  have hgne : g ≠ 0 := by
    have hfrestrict :
        DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q f ≠ 0 :=
      (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero f Q).mp
        hfMax.1 |>.2
    change MonoidAlgebra.mapDomainRingEquiv
        (BrauerBlockReduction.principalResidueField d) E
        (DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q f) ≠ 0
    exact BrauerTransitivity.mapDomainRingEquiv_ne_zero
      (R := BrauerBlockReduction.principalResidueField d) E
      (DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q f) hfrestrict
  have hmap_subtype_ne :
      (Subring.subtype (Subring.center A))
          ⟨g, hgcenter⟩ ≠ 0 := by
    intro hzero
    apply hgne
    exact hzero
  obtain ⟨βCI, hβprimitive, hβfactor, _hβmap⟩ :=
    CentralPrimitiveExistence.exists_isCentrallyPrimitive_factor_map_ne_zero
      (A := A) (B := A) (Subring.subtype (Subring.center A)) g
      hgcenter hgidem hmap_subtype_ne
  let β : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) C :=
    βCI.val
  have hfQaug :
      AugmentationScratch.augmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer
            (Q : Set (Subgroup.centralizer ({z} : Set G))))
          (DefectSupport.subgroupCentralizerRestriction
            (BrauerBlockReduction.principalResidueField d) Q f) = 0 := by
    rw [SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
      Q hfMax.1.1 f hfprimitive.1, hfaug]
  have hgaug :
      AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d) C g = 0 := by
    rw [show AugmentationScratch.augmentation
          (BrauerBlockReduction.principalResidueField d) C g =
        AugmentationScratch.augmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer
            (Q : Set (Subgroup.centralizer ({z} : Set G))))
          (DefectSupport.subgroupCentralizerRestriction
            (BrauerBlockReduction.principalResidueField d) Q f) by
      simpa [g, C] using
        BrauerTransitivity.augmentation_mapDomainRingEquiv
          (R := BrauerBlockReduction.principalResidueField d) E
          (DefectSupport.subgroupCentralizerRestriction
            (BrauerBlockReduction.principalResidueField d) Q f)]
    exact hfQaug
  have hβaug :
      AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d) C β = 0 := by
    have h := congrArg
      (AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d) C) hβfactor
    rw [map_mul, hgaug, mul_zero] at h
    exact h.symm
  have hβambient : β * eGQ = β := by
    have hfactor' : β * g = β := hβfactor
    have hge : g * eGQ = g := by
      change
        MonoidAlgebra.mapDomainRingHom
              (BrauerBlockReduction.principalResidueField d) E.toMonoidHom
              (DefectSupport.subgroupCentralizerRestriction
                (BrauerBlockReduction.principalResidueField d) Q f) *
            DefectSupport.subgroupCentralizerRestriction
              (BrauerBlockReduction.principalResidueField d)
              (Q.map (Subgroup.centralizer ({z} : Set G)).subtype : Subgroup G)
              (BrauerBlockReduction.reducedPrincipalBlockElement d) =
          MonoidAlgebra.mapDomainRingHom
            (BrauerBlockReduction.principalResidueField d) E.toMonoidHom
            (DefectSupport.subgroupCentralizerRestriction
              (BrauerBlockReduction.principalResidueField d) Q f)
      exact hmapfactor
    calc
      β * eGQ = (β * g) * eGQ := by rw [hfactor']
      _ = β * (g * eGQ) := by rw [mul_assoc]
      _ = β * g := by rw [hge]
      _ = β := hfactor'
  have hQmap : IsPGroup 2
      (Q.map (Subgroup.centralizer ({z} : Set G)).subtype : Subgroup G) :=
    hfMax.1.1.map (Subgroup.centralizer ({z} : Set G)).subtype
  exact ⟨Q, β, hQmap, hβprimitive, hβaug, hβambient, hQadmissible⟩

/-! The extracted admissible factor is genuinely nonprincipal in its direct
ambient centralizer.  The principal factor has augmentation one, whereas the
extracted factor has augmentation zero; central primitivity therefore makes
their intersection vanish. -/

/-- Failure of involution principal-Brauer equality produces an admissible
augmentation-zero primitive factor under the direct ambient Brauer image,
orthogonal to the compatible principal block of the same centralizer. -/
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
          BlockPrimitivity.IsCentrallyPrimitive β ∧
          AugmentationScratch.augmentation K
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
  have hLocalPrimitive : BlockPrimitivity.IsCentrallyPrimitive eLocal := by
    simpa [eLocal, C, QG, K, H] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d C
  have hβLocal : β * eLocal = 0 := by
    by_contra hnonzero
    have heq : β = eLocal :=
      CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
        hβprimitive hLocalPrimitive hnonzero
    have hzeroOne : (0 : K) = 1 := by
      calc
        0 = AugmentationScratch.augmentation K C β := by
          simpa [C, QG, K, H] using hβaug.symm
        _ = AugmentationScratch.augmentation K C eLocal :=
          congrArg (AugmentationScratch.augmentation K C) heq
        _ = 1 := by
          simpa [eLocal, C, QG, K, H] using
            CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
              d C
    exact zero_ne_one hzeroOne
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

/-! The maximal-support block can now be placed on the intermediate group
`Q C_H(Q)`.  Extracting a primitive factor which remains visible under the
`Q`-Brauer map gives exactly the intermediate block in the algebraic part of
Juhasz's Lemma 2(c): its defect group is the canonical copy of `Q`, and its
augmentation is still zero.  No block-induction or First Main conclusion is
used in this extraction. -/

/-- Failure of principal Brauer equality yields a centrally primitive block
on `Q C_H(Q)` whose defect group is exactly the canonical copy of `Q`.  The
factor identity records its link to the original block's direct `Q`-Brauer
restriction; it is a conclusion of the construction, not an assumption. -/
theorem exists_qcCentralizer_primitiveExactDefectBlock_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let K := BrauerBlockReduction.principalResidueField d
    ∃ Q : Subgroup H,
      ∃ f : MonoidAlgebra K H,
        let L := NormalizerBrauerPair.qcCentralizer Q
        let P := Q.subgroupOf L
        ∃ γ : MonoidAlgebra K L,
          BlockPrimitivity.IsCentrallyPrimitive f ∧
            AugmentationScratch.augmentation K H f = 0 ∧
            DefectSupport.IsMaximalTwoCoefficientSupport f Q ∧
            BlockPrimitivity.IsCentrallyPrimitive γ ∧
            γ * NormalizerBrauerPair.qcCentralizerAlgebraEmbedding K Q
                (DefectSupport.subgroupCentralizerRestriction K Q f) = γ ∧
            AugmentationScratch.augmentation K L γ = 0 ∧
            DefectSupport.IsMaximalTwoCoefficientSupport γ P ∧
            Subgroup.centralizer
                ((Q.map H.subtype : Subgroup G) : Set G) ≤ H := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  letI : Field K := Ideal.Quotient.field d.primeIdeal
  obtain ⟨Q, f, hfprimitive, _hfb, _horth, hfaug, _hfambient,
      hfMax, hQadmissible⟩ :=
    exists_admissible_primitiveDefectBlock_orthogonal_local_of_not_brauerEquality
      d z hzI hne
  let L := NormalizerBrauerPair.qcCentralizer Q
  let P : Subgroup L := Q.subgroupOf L
  let fQ : MonoidAlgebra K
      (Subgroup.centralizer
        (Q : Set (Subgroup.centralizer ({z} : Set G)))) :=
    DefectSupport.subgroupCentralizerRestriction K Q f
  let eL : MonoidAlgebra K L :=
    NormalizerBrauerPair.qcCentralizerAlgebraEmbedding K Q fQ
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite K := principalResidueField_finite d
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype L := Fintype.ofFinite L
  letI : DecidableEq L := Classical.decEq L
  letI : Finite (MonoidAlgebra K L) := by
    change Finite (L →₀ K)
    infer_instance
  have hfQcenter : fQ ∈
      Set.center (MonoidAlgebra K
        (Subgroup.centralizer
          (Q : Set (Subgroup.centralizer ({z} : Set G))))) := by
    exact SubgroupBrauerMap.subgroupCentralizerRestriction_mem_center
      Q f hfprimitive.1
  have hfQidem : IsIdempotentElem fQ := by
    exact
      SubgroupBrauerMap.subgroupCentralizerRestriction_isIdempotent_of_mem_center
        Q hfMax.1.1 f hfprimitive.1 hfprimitive.2.1
  have hfQne : fQ ≠ 0 := by
    exact
      (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero f Q).mp
        hfMax.1 |>.2
  have heLcenter : eL ∈ Set.center (MonoidAlgebra K L) := by
    change NormalizerBrauerPair.qcCentralizerAlgebraEmbedding K Q fQ ∈
      Set.center
        (MonoidAlgebra K (NormalizerBrauerPair.qcCentralizer Q))
    exact NormalizerBrauerPair.qcCentralizerAlgebraEmbedding_mem_center
      Q fQ hfQcenter
  have heLidem : IsIdempotentElem eL := by
    change IsIdempotentElem
      (NormalizerBrauerPair.qcCentralizerAlgebraEmbedding K Q fQ)
    exact NormalizerBrauerPair.qcCentralizerAlgebraEmbedding_isIdempotent
      Q fQ hfQidem
  have hPmax : DefectSupport.IsMaximalTwoCoefficientSupport eL P := by
    change DefectSupport.IsMaximalTwoCoefficientSupport
      (NormalizerBrauerPair.qcCentralizerAlgebraEmbedding K Q
        (DefectSupport.subgroupCentralizerRestriction K Q f))
      (Q.subgroupOf (NormalizerBrauerPair.qcCentralizer Q))
    exact
      NormalizerBrauerPair.subgroupOf_qcCentralizer_isMaximalSupport_of_embedding_restriction
        f Q hfMax
  let phi := SubgroupBrauerMap.subgroupCentralizerRestrictionCenterHom
    2 K P hPmax.1.1
  have heLRestrNe :
      DefectSupport.subgroupCentralizerRestriction K P eL ≠ 0 :=
    (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero eL P).mp
      hPmax.1 |>.2
  have hphiEL : phi ⟨eL, heLcenter⟩ ≠ 0 := by
    intro hzero
    apply heLRestrNe
    have hzero' := congrArg
      (fun x : Subring.center
          (MonoidAlgebra K (Subgroup.centralizer (P : Set L))) =>
        (x : MonoidAlgebra K (Subgroup.centralizer (P : Set L)))) hzero
    simpa [phi] using hzero'
  obtain ⟨γCI, hγprimitive, hγfactor, hγphi⟩ :=
    CentralPrimitiveExistence.exists_isCentrallyPrimitive_factor_map_ne_zero
      phi eL heLcenter heLidem hphiEL
  let γ : MonoidAlgebra K L := γCI.val
  have hγRestrNe :
      DefectSupport.subgroupCentralizerRestriction K P γ ≠ 0 := by
    intro hzero
    apply hγphi
    apply Subtype.ext
    change DefectSupport.subgroupCentralizerRestriction K P γCI.val = 0
    exact hzero
  have hγSupportP : DefectSupport.HasTwoCoefficientSupport γ P :=
    (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero γ P).mpr
      ⟨hPmax.1.1, hγRestrNe⟩
  have hγMax : DefectSupport.IsMaximalTwoCoefficientSupport γ P := by
    exact SubgroupBrauerMap.isMaximalTwoCoefficientSupport_of_central_factor
      γ eL hγprimitive.1 heLcenter hγfactor P hPmax hγSupportP
  have hfQaug :
      AugmentationScratch.augmentation K
          (Subgroup.centralizer
            (Q : Set (Subgroup.centralizer ({z} : Set G)))) fQ = 0 := by
    rw [SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
      Q hfMax.1.1 f hfprimitive.1, hfaug]
  have heLaug : AugmentationScratch.augmentation K L eL = 0 := by
    calc
      AugmentationScratch.augmentation K L eL =
          AugmentationScratch.augmentation K
            (Subgroup.centralizer
              (Q : Set (Subgroup.centralizer ({z} : Set G)))) fQ := by
        change AugmentationScratch.augmentation K
            (NormalizerBrauerPair.qcCentralizer Q)
              (NormalizerBrauerPair.qcCentralizerAlgebraEmbedding K Q fQ) =
          AugmentationScratch.augmentation K
            (Subgroup.centralizer
              (Q : Set (Subgroup.centralizer ({z} : Set G)))) fQ
        exact
          NormalizerBrauerPair.augmentation_qcCentralizerAlgebraEmbedding Q fQ
      _ = 0 := hfQaug
  have hγaug : AugmentationScratch.augmentation K L γ = 0 := by
    have h := congrArg (AugmentationScratch.augmentation K L) hγfactor
    rw [map_mul, heLaug, mul_zero] at h
    exact h.symm
  exact ⟨Q, f, γ, hfprimitive, hfaug, hfMax, hγprimitive,
    by simpa [γ, eL, fQ, L] using hγfactor,
    by simpa [γ, L] using hγaug,
    by simpa [γ, P, L] using hγMax, hQadmissible⟩

/-- Ambient form of the preceding construction.  Under admissibility the
canonical equivalence `Q C_H(Q) ≃ Q C_G(Q)` transports the primitive block
and its exact defect group to Juhasz's literal intermediate subgroup. -/
theorem exists_ambientQcCentralizer_primitiveExactDefectBlock_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let K := BrauerBlockReduction.principalResidueField d
    ∃ Q : Subgroup H,
      let QG : Subgroup G := Q.map H.subtype
      ∃ β : MonoidAlgebra K (NormalizerBrauerPair.qcCentralizer QG),
        BlockPrimitivity.IsCentrallyPrimitive β ∧
          AugmentationScratch.augmentation K
              (NormalizerBrauerPair.qcCentralizer QG) β = 0 ∧
          DefectSupport.IsMaximalTwoCoefficientSupport β
            (QG.subgroupOf (NormalizerBrauerPair.qcCentralizer QG)) ∧
          NormalizerBrauerPair.qcCentralizer QG ≤ H := by
  dsimp only
  obtain ⟨Q, _f, γ, _hfprimitive, _hfaug, _hfMax, hγprimitive,
      _hγfactor, hγaug, hγMax, hQadmissible⟩ :=
    exists_qcCentralizer_primitiveExactDefectBlock_of_not_brauerEquality
      d z hzI hne
  let H := Subgroup.centralizer ({z} : Set G)
  let K := BrauerBlockReduction.principalResidueField d
  let QG : Subgroup G := Q.map H.subtype
  let E := NormalizerBrauerPair.qcCentralizerMapEquiv H Q hQadmissible
  let β : MonoidAlgebra K (NormalizerBrauerPair.qcCentralizer QG) :=
    MonoidAlgebra.mapDomainRingEquiv K E γ
  have hβprimitive : BlockPrimitivity.IsCentrallyPrimitive β := by
    simpa [β, E, QG, K, H] using
      NormalizerBrauerAction.map_isCentrallyPrimitive
        (MonoidAlgebra.mapDomainRingEquiv K E) hγprimitive
  have hβaug : AugmentationScratch.augmentation K
      (NormalizerBrauerPair.qcCentralizer QG) β = 0 := by
    rw [show AugmentationScratch.augmentation K
          (NormalizerBrauerPair.qcCentralizer QG) β =
        AugmentationScratch.augmentation K
          (NormalizerBrauerPair.qcCentralizer Q) γ by
      simpa [β, E, QG, K, H] using
        BrauerTransitivity.augmentation_mapDomainRingEquiv E γ]
    simpa [K, H] using hγaug
  have hβMaxMapped :=
    DefectSupport.isMaximalTwoCoefficientSupport_mapDomainRingEquiv
      E γ (Q.subgroupOf (NormalizerBrauerPair.qcCentralizer Q)) hγMax
  have hPmap :
      (Q.subgroupOf (NormalizerBrauerPair.qcCentralizer Q)).map
          E.toMonoidHom =
        QG.subgroupOf (NormalizerBrauerPair.qcCentralizer QG) := by
    simpa [E, QG, H] using
      NormalizerBrauerPair.subgroupOf_qcCentralizer_map_qcCentralizerMapEquiv
        H Q hQadmissible
  rw [hPmap] at hβMaxMapped
  have hβMax : DefectSupport.IsMaximalTwoCoefficientSupport β
      (QG.subgroupOf (NormalizerBrauerPair.qcCentralizer QG)) := by
    simpa [β, E, QG, K, H] using hβMaxMapped
  have hqc : NormalizerBrauerPair.qcCentralizer QG ≤ H := by
    simpa [QG, H] using
      NormalizerBrauerPair.qcCentralizer_le_of_ambientCentralizer_le
        H Q hQadmissible
  exact ⟨Q, β, hβprimitive, hβaug, hβMax, hqc⟩

/-! The ambient-centralizer factor can also be embedded directly in
`Q C_G(Q)`.  The next theorem records the weaker containment statement used
by the already-developed ambient normalizer branch. -/

theorem exists_qcCentralizer_maximalSupportWitness_of_not_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    let H := Subgroup.centralizer ({z} : Set G)
    let K := BrauerBlockReduction.principalResidueField d
    ∃ Q : Subgroup H,
      let QG : Subgroup G := Q.map H.subtype
      ∃ β : MonoidAlgebra K (Subgroup.centralizer (QG : Set G)),
        ∃ D : Subgroup (NormalizerBrauerPair.qcCentralizer QG),
          IsPGroup 2 QG ∧
            BlockPrimitivity.IsCentrallyPrimitive β ∧
            AugmentationScratch.augmentation K
                (Subgroup.centralizer (QG : Set G)) β = 0 ∧
            β * SubgroupPrincipalBrauer.extraBrauerFactor d QG = β ∧
            Subgroup.centralizer (QG : Set G) ≤ H ∧
            DefectSupport.IsMaximalTwoCoefficientSupport
              (NormalizerBrauerPair.qcCentralizerAlgebraEmbedding K QG β) D ∧
            QG.subgroupOf (NormalizerBrauerPair.qcCentralizer QG) ≤ D := by
  dsimp only
  obtain ⟨Q, β, hQ, hβprimitive, hβaug, _hβambient,
      _hβlocal, hβextra, hQadmissible⟩ :=
    exists_admissible_primitiveAmbientBrauerFactor_orthogonal_principal_of_not_brauerEquality
      d z hzI hne
  let H := Subgroup.centralizer ({z} : Set G)
  let K := BrauerBlockReduction.principalResidueField d
  let QG : Subgroup G := Q.map H.subtype
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD, hQD⟩ :=
    NormalizerBrauerPair.exists_maximalSupport_qcCentralizerEmbedding_containing
      QG hQ β hβprimitive.2.2.1
  exact ⟨Q, β, D, hQ, hβprimitive, hβaug, hβextra,
    hQadmissible, by simpa [QG, K, H] using hD,
    by simpa [QG, H] using hQD⟩

/-! The group-theoretic normalizer branch of Juhasz's induction can now be
attached directly to the primitive obstruction.  If its supporting subgroup
is not Sylow, its normalizer contains a strictly larger `2`-subgroup; the
subgroup `Q C_G(Q)` lies in both the original admissible centralizer and the
normalizer.  No First Main or block-induction conclusion is asserted here. -/

/-- Failure of principal Brauer equality yields the nonprincipal primitive
Brauer factor together with the exact Sylow/strict-normalizer-growth
dichotomy used in the induction proof of Third Main. -/
theorem exists_admissible_primitiveAmbientBrauerFactor_with_normalizerStep_of_not_brauerEquality
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
          BlockPrimitivity.IsCentrallyPrimitive β ∧
          AugmentationScratch.augmentation K
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
              ((Q.map H.subtype : Subgroup G) : Set G) ≤ H ∧
          NormalizerBrauerPair.qcCentralizer
              (Q.map H.subtype : Subgroup G) ≤
            H ⊓ Subgroup.normalizer (Q.map H.subtype : Subgroup G) ∧
          ((NormalizerBrauerPair.qcCentralizer
              (Q.map H.subtype : Subgroup G)).subgroupOf
              (Subgroup.normalizer
                ((Q.map H.subtype : Subgroup G) : Set G))).Normal ∧
          ((∃ P : Sylow 2 G,
              (P : Subgroup G) = (Q.map H.subtype : Subgroup G)) ∨
            ∃ R : Subgroup G,
              IsPGroup 2 R ∧
                (Q.map H.subtype : Subgroup G) < R ∧
                R ≤ Subgroup.normalizer
                  (Q.map H.subtype : Subgroup G) ∧
                Nat.card (Q.map H.subtype : Subgroup G) < Nat.card R) := by
  dsimp only
  obtain ⟨Q, β, hQ, hβprimitive, hβaug, hβambient,
      hβlocal, hβextra, hQadmissible⟩ :=
    exists_admissible_primitiveAmbientBrauerFactor_orthogonal_principal_of_not_brauerEquality
      d z hzI hne
  let H := Subgroup.centralizer ({z} : Set G)
  let QG : Subgroup G := Q.map H.subtype
  have hbase : NormalizerBrauerPair.qcCentralizer QG ≤
      H ⊓ Subgroup.normalizer QG := by
    exact
      NormalizerBrauerPair.qcCentralizer_le_inf_of_ambientCentralizer_le
        H Q hQadmissible
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstep :=
    NormalizerBrauerPair.exists_sylow_eq_or_exists_strict_supergroup_le_normalizer
      QG hQ
  exact ⟨Q, β, hQ, hβprimitive, hβaug, hβambient,
    hβlocal, hβextra, hQadmissible,
    by simpa [QG, H] using hbase,
    by simpa [QG, H] using
      (NormalizerBrauerPair.qcCentralizer_subgroupOf_normalizer_isNormal QG),
    by simpa [QG, H] using hstep⟩

/-! The primitive factor's full normalizer orbit is now controlled: every
conjugate is another augmentation-zero primitive factor under the same extra
Brauer idempotent, and two orbit members are equal or orthogonal. -/

/-- Normalizer-orbit form of the obstruction supplied by failure of
principal Brauer equality. -/
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
          BlockPrimitivity.IsCentrallyPrimitive β ∧
          AugmentationScratch.augmentation K
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
            BlockPrimitivity.IsCentrallyPrimitive βn ∧
              AugmentationScratch.augmentation K
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

/-! The normalizer orbit sum can now be descended to a primitive normalizer
block.  This is the finite central-idempotent step preceding First Main and
Nagao; no correspondence theorem is used in the extraction. -/

/-- An augmentation-zero primitive block is orthogonal to the compatible
principal block over the same subgroup algebra. -/
theorem primitiveAugmentationZero_mul_localPrincipal_eq_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (L : Subgroup G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) L)
    (hbPrimitive : BlockPrimitivity.IsCentrallyPrimitive b)
    (hbAug : AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d) L b = 0) :
    b * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d L = 0 := by
  let K := BrauerBlockReduction.principalResidueField d
  let eLocal : MonoidAlgebra K L :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d L
  have hLocalPrimitive : BlockPrimitivity.IsCentrallyPrimitive eLocal := by
    simpa [eLocal, K] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d L
  by_contra hnonzero
  have heq : b = eLocal :=
    CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
      hbPrimitive hLocalPrimitive hnonzero
  have haugEq := congrArg (AugmentationScratch.augmentation K L) heq
  have hzeroOne : (0 : K) = 1 := by
    calc
      0 = AugmentationScratch.augmentation K L b := by
        simpa [K] using hbAug.symm
      _ = AugmentationScratch.augmentation K L eLocal := haugEq
      _ = 1 := by
        simpa [eLocal, K] using
          CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
            d L
  exact zero_ne_one hzeroOne

/-- A primitive augmentation-zero factor under a direct `Q`-Brauer image
produces a primitive augmentation-zero factor in the normalizer algebra. -/
theorem exists_primitiveNormalizerFactor_of_extra
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (β : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hQ : IsPGroup 2 Q)
    (hβprimitive : BlockPrimitivity.IsCentrallyPrimitive β)
    (hβaug : AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) β = 0)
    (hβextra : β * SubgroupPrincipalBrauer.extraBrauerFactor d Q = β) :
    ∃ α : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.normalizer (Q : Set G)),
      BlockPrimitivity.IsCentrallyPrimitive α ∧
      AugmentationScratch.augmentation
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
  letI : Finite K := principalResidueField_finite d
  letI : Field K := Ideal.Quotient.field d.primeIdeal
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype N := Fintype.ofFinite N
  letI : DecidableEq N := Classical.decEq N
  letI : Finite A := by
    change Finite (N →₀ K)
    infer_instance
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
      AugmentationScratch.augmentation K N α = 0 := by
    have h := congrArg (AugmentationScratch.augmentation K N) hαfactor
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

/-- Failure of involution principal-Brauer equality therefore yields the full
admissible primitive pair together with a primitive normalizer block. -/
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
          BlockPrimitivity.IsCentrallyPrimitive β ∧
          AugmentationScratch.augmentation K
              (Subgroup.centralizer (QG : Set G)) β = 0 ∧
          β * DefectSupport.subgroupCentralizerRestriction K
              QG
              (BrauerBlockReduction.reducedPrincipalBlockElement d) = β ∧
          β * SubgroupPrincipalBrauer.extraBrauerFactor d QG = β ∧
          Subgroup.centralizer (QG : Set G) ≤ H ∧
          BlockPrimitivity.IsCentrallyPrimitive α ∧
          AugmentationScratch.augmentation K
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

/-! This is the consolidated endpoint immediately before the genuine First
Main/Nagao input.  A failed principal Brauer equality gives a nonprincipal
primitive block in `C_G(Q)`, a primitive block in `N_G(Q)` lying in the
embedded extra corner and meeting the original block, and the exact
Sylow-or-strict-normalizer-growth alternative for `Q`. -/

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
          BlockPrimitivity.IsCentrallyPrimitive β ∧
          AugmentationScratch.augmentation K
              (Subgroup.centralizer (QG : Set G)) β = 0 ∧
          β * SubgroupPrincipalBrauer.extraBrauerFactor d QG = β ∧
          Subgroup.centralizer (QG : Set G) ≤ H ∧
          BlockPrimitivity.IsCentrallyPrimitive α ∧
          AugmentationScratch.augmentation K
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
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstep :=
    NormalizerBrauerPair.exists_sylow_eq_or_exists_strict_supergroup_le_normalizer
      QG hQ
  exact ⟨Q, β, α, hQ, hβprimitive, hβaug, hβextra,
    hQadmissible, hαprimitive, hαaug, hαextra, hαlocal, hαleft,
    by simpa [QG, H] using hstep⟩

end ThirdMainReduction
end Submission.ZStar
