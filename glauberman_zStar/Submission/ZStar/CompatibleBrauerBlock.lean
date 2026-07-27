import Submission.ZStar.CompatibleLocalBlock
import Submission.ZStar.BrauerBlockReduction
import Submission.ZStar.AugmentationScratch

/-!
# Compatible local and ambient principal-block idempotents

The compatible subgroup datum has a residue field which embeds in the
ambient residue field.  This file uses that embedding to place the reduced
local principal-block idempotent and the involution Brauer image of the
ambient principal-block idempotent in the same centralizer group algebra.

The two elements are proved central and idempotent here.  Their equality (or
the corresponding factor statement) is precisely the remaining
Brauer-correspondence input.
-/

noncomputable section

namespace Submission.ZStar

namespace CompatibleBrauerBlock

open PrincipalBlockConstruction
open CompatibleLocalBlock

universe u v

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [Finite G]

private instance ambientPrime_isPrime
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

private theorem mapRingHom_mem_center
    {R S : Type*} [CommRing R] [CommRing S]
    {H : Type v} [Group H]
    (f : R →+* S) (e : MonoidAlgebra R H)
    (he : e ∈ Set.center (MonoidAlgebra R H)) :
    MonoidAlgebra.mapRingHom H f e ∈
      Set.center (MonoidAlgebra S H) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      have hcomm := Semigroup.mem_center_iff.mp he
        (MonoidAlgebra.single g (1 : R))
      have hmap := congrArg (MonoidAlgebra.mapRingHom H f) hcomm
      have hcommOne :
          (MonoidAlgebra.single g (1 : S)) *
              MonoidAlgebra.mapRingHom H f e =
            MonoidAlgebra.mapRingHom H f e *
              MonoidAlgebra.single g (1 : S) := by
        simpa using hmap
      rw [show (MonoidAlgebra.single g r : MonoidAlgebra S H) =
          r • MonoidAlgebra.single g 1 by simp]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun x : MonoidAlgebra S H => r • x) hcommOne

/-- The compatible local principal congruence-block datum. -/
abbrev localData (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :=
  compatibleSubgroupPrincipalCongruenceBlockData d H

private instance localPrime_isPrime
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    (localData d H).primeIdeal.IsPrime :=
  (localData d H).primeIdeal_maximal.isPrime

/-- Reduction commutes with the inclusion from the compatible local
localization into the ambient localization. -/
theorem compatibleSubgroupLocalizationToResidue_commutes
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    (BrauerBlockReduction.localizationToResidue d).comp
        (compatibleSubgroupLocalizationInclusion d H) =
      (compatibleSubgroupResidueFieldInclusion d H).comp
        (BrauerBlockReduction.localizationToResidue (localData d H)) := by
  apply IsLocalization.ringHom_ext (localData d H).primeIdeal.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [compatibleSubgroupLocalizationInclusion_algebraMap,
    BrauerBlockReduction.localizationToResidue_algebraMap,
    BrauerBlockReduction.localizationToResidue_algebraMap]
  exact contractedResidueFieldInclusion_mk
    (subgroupRoot_mem d H) d.primeIdeal a

/-- The compatible local principal-block idempotent transported to the
ambient localization, before reduction modulo the ambient prime. -/
noncomputable def localPrincipalBlockElementInAmbientLocalization
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal) H :=
  MonoidAlgebra.mapRingHom H
    (compatibleSubgroupLocalizationInclusion d H)
    (BlockOrthogonality.localizedPrincipalBlockElement (localData d H))

theorem localPrincipalBlockElementInAmbientLocalization_mem_center
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    localPrincipalBlockElementInAmbientLocalization d H ∈
      Set.center (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H) := by
  exact mapRingHom_mem_center
    (compatibleSubgroupLocalizationInclusion d H)
    (BlockOrthogonality.localizedPrincipalBlockElement (localData d H))
    (BlockOrthogonality.localizedPrincipalBlockElement_mem_center
      (localData d H))

theorem localPrincipalBlockElementInAmbientLocalization_isIdempotent
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    IsIdempotentElem
      (localPrincipalBlockElementInAmbientLocalization d H) := by
  change MonoidAlgebra.mapRingHom H
      (compatibleSubgroupLocalizationInclusion d H)
      (BlockOrthogonality.localizedPrincipalBlockElement (localData d H)) *
      MonoidAlgebra.mapRingHom H
        (compatibleSubgroupLocalizationInclusion d H)
        (BlockOrthogonality.localizedPrincipalBlockElement (localData d H)) =
    MonoidAlgebra.mapRingHom H
      (compatibleSubgroupLocalizationInclusion d H)
      (BlockOrthogonality.localizedPrincipalBlockElement (localData d H))
  rw [← map_mul]
  exact congrArg (MonoidAlgebra.mapRingHom H
      (compatibleSubgroupLocalizationInclusion d H))
    (BlockOrthogonality.localizedPrincipalBlockElement_isIdempotent
      (localData d H))

/-- The reduced local principal-block idempotent after extending coefficients
to the ambient residue field. -/
noncomputable def localPrincipalBlockElementInAmbientResidue
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    MonoidAlgebra (BrauerBlockReduction.principalResidueField d) H :=
  MonoidAlgebra.mapRingHom H
    (compatibleSubgroupResidueFieldInclusion d H)
    (BrauerBlockReduction.reducedPrincipalBlockElement (localData d H))

/-- The ambient-localization lift above reduces to the previously defined
compatible local principal selector in the ambient residue field. -/
theorem localPrincipalBlockElementInAmbientLocalization_reduce
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    MonoidAlgebra.mapRingHom H
        (BrauerBlockReduction.localizationToResidue d)
        (localPrincipalBlockElementInAmbientLocalization d H) =
      localPrincipalBlockElementInAmbientResidue d H := by
  change MonoidAlgebra.mapRingHom H
      (BrauerBlockReduction.localizationToResidue d)
      (MonoidAlgebra.mapRingHom H
        (compatibleSubgroupLocalizationInclusion d H)
        (BlockOrthogonality.localizedPrincipalBlockElement (localData d H))) =
    MonoidAlgebra.mapRingHom H
      (compatibleSubgroupResidueFieldInclusion d H)
      (MonoidAlgebra.mapRingHom H
        (BrauerBlockReduction.localizationToResidue (localData d H))
        (BlockOrthogonality.localizedPrincipalBlockElement (localData d H)))
  rw [← RingHom.comp_apply, ← RingHom.comp_apply,
    ← MonoidAlgebra.mapRingHom_comp, ← MonoidAlgebra.mapRingHom_comp,
    compatibleSubgroupLocalizationToResidue_commutes]

theorem localPrincipalBlockElementInAmbientResidue_mem_center
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    localPrincipalBlockElementInAmbientResidue d H ∈
      Set.center
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) H) := by
  exact mapRingHom_mem_center
    (compatibleSubgroupResidueFieldInclusion d H)
    (BrauerBlockReduction.reducedPrincipalBlockElement (localData d H))
    (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center (localData d H))

theorem localPrincipalBlockElementInAmbientResidue_isIdempotent
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    IsIdempotentElem (localPrincipalBlockElementInAmbientResidue d H) := by
  change MonoidAlgebra.mapRingHom H
      (compatibleSubgroupResidueFieldInclusion d H)
      (BrauerBlockReduction.reducedPrincipalBlockElement (localData d H)) *
      MonoidAlgebra.mapRingHom H
        (compatibleSubgroupResidueFieldInclusion d H)
        (BrauerBlockReduction.reducedPrincipalBlockElement (localData d H)) =
    MonoidAlgebra.mapRingHom H
      (compatibleSubgroupResidueFieldInclusion d H)
      (BrauerBlockReduction.reducedPrincipalBlockElement (localData d H))
  rw [← map_mul]
  exact congrArg (MonoidAlgebra.mapRingHom H
      (compatibleSubgroupResidueFieldInclusion d H))
    (BrauerBlockReduction.reducedPrincipalBlockElement_isIdempotent (localData d H))

@[simp] theorem localPrincipalBlockElementInAmbientResidue_apply
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (h : H) :
    localPrincipalBlockElementInAmbientResidue d H h =
      compatibleSubgroupResidueFieldInclusion d H
        (BrauerBlockReduction.reducedPrincipalBlockElement (localData d H) h) := by
  exact MonoidAlgebra.mapRingHom_apply _ _ _

/-- The transported local principal-block idempotent has augmentation one. -/
theorem localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d) H
        (localPrincipalBlockElementInAmbientResidue d H) = 1 := by
  change AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d) H
      (MonoidAlgebra.mapRingHom H
        (compatibleSubgroupResidueFieldInclusion d H)
        (BrauerBlockReduction.reducedPrincipalBlockElement (localData d H))) = 1
  rw [AugmentationScratch.augmentation_mapRingHom,
    AugmentationScratch.reducedPrincipalBlockElement_augmentation_eq_one,
    map_one]

/-- At an involution, the local principal selector and the ambient Brauer
selector have nonzero intersection.  This is the strongest comparison forced
by augmentation alone: both selectors act as one on the trivial module. -/
theorem localPrincipalBlockElement_mul_involutionBrauer_ne_zero
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z ≠ 0 := by
  exact AugmentationScratch.mul_ne_zero_of_augmentation_eq_one _ _
    (localPrincipalBlockElementInAmbientResidue_augmentation_eq_one d
      (Subgroup.centralizer ({z} : Set G)))
    (AugmentationScratch.involutionBrauerPrincipalBlockElement_augmentation_eq_one
      d z hz)

/-- The nonzero intersection of the two principal selectors is itself a
central idempotent. -/
theorem localPrincipalBlockElement_mul_involutionBrauer_isCentralIdempotent
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    let H := Subgroup.centralizer ({z} : Set G)
    let eLocal := localPrincipalBlockElementInAmbientResidue d H
    let eBrauer :=
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
    eLocal * eBrauer ∈
        Set.center (MonoidAlgebra
          (BrauerBlockReduction.principalResidueField d) H) ∧
      IsIdempotentElem (eLocal * eBrauer) ∧
      eLocal * eBrauer ≠ 0 := by
  dsimp only
  let eLocal := localPrincipalBlockElementInAmbientResidue d
    (Subgroup.centralizer ({z} : Set G))
  let eBrauer :=
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  have hLocalCenter : eLocal ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))) :=
    localPrincipalBlockElementInAmbientResidue_mem_center d _
  have hBrauerCenter : eBrauer ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))) :=
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z
  refine ⟨Set.mul_mem_center hLocalCenter hBrauerCenter, ?_, ?_⟩
  · exact IsIdempotentElem.mul_of_commute
      (Semigroup.mem_center_iff.mp hLocalCenter eBrauer).symm
      (localPrincipalBlockElementInAmbientResidue_isIdempotent d _)
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_isIdempotent
        d z hz)
  · exact localPrincipalBlockElement_mul_involutionBrauer_ne_zero d z hz

/-- The remaining characteristic-two Brauer-correspondence assertion: the
Brauer image of the ambient principal-block idempotent is exactly the
transported compatible local principal-block idempotent. -/
def InvolutionPrincipalBrauerEquality
    (d : PrincipalCongruenceBlockData G) (z : G) : Prop :=
  let H := Subgroup.centralizer ({z} : Set G)
  localPrincipalBlockElementInAmbientResidue d H =
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z

end CompatibleBrauerBlock

end Submission.ZStar
