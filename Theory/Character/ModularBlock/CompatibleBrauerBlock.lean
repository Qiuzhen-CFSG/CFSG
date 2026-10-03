module

public import Theory.Character.ModularBlock.CompatibleCongruence
public import Theory.Character.ModularBlock.PrincipalReduction

/-!
# Compatible local and ambient principal-block idempotents

The compatible subgroup datum has a residue field which embeds in the
ambient residue field.  This file uses that embedding to place the reduced
local principal-block idempotent and the involution Brauer image of the
ambient principal-block idempotent in the same centralizer group algebra.

The two elements are proved central and idempotent here.  Their equality (or
the corresponding factor statement) is precisely the remaining
Brauer-correspondence input.

Naturality of localization and residue maps identifies the two ways to
reduce the lifted local selector. Coefficient extension preserves centrality
and idempotence; both selectors have augmentation one, so their product is
nonzero. Commuting idempotents then give the central-idempotent intersection.
The explicit coefficient maps and equality predicate are exposed for the
subsequent primitivity and Brauer-correspondence arguments.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CompatibleBrauerBlock.lean` (revision `c3503435`), reusing
the shared centrality and augmentation API.
-/

public section

noncomputable section

namespace ModularBlock

namespace CompatibleBrauerBlock

open PrincipalBlockConstruction
open CompatibleLocalBlock

universe u v

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [Finite G]

/-- The compatible local principal congruence-block datum. -/
abbrev localData (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :=
  compatibleSubgroupPrincipalCongruenceBlockData d H

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
@[expose] noncomputable def localPrincipalBlockElementInAmbientLocalization
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal) H :=
  MonoidAlgebra.mapRingHom H
    (compatibleSubgroupLocalizationInclusion d H)
    (BlockOrthogonality.localizedPrincipalBlockElement (localData d H))

theorem localPrincipalBlockElementInAmbientLocalization_mem_center
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    localPrincipalBlockElementInAmbientLocalization d H ∈
      Set.center (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H) := by
  exact BrauerBlockReduction.mapRingHom_mem_center
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
@[expose] noncomputable def localPrincipalBlockElementInAmbientResidue
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
  exact BrauerBlockReduction.mapRingHom_mem_center
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
    (localPrincipalBlockElementInAmbientResidue d H).coeff h =
      compatibleSubgroupResidueFieldInclusion d H
        ((BrauerBlockReduction.reducedPrincipalBlockElement (localData d H)).coeff h) := by
  rfl

/-- The transported local principal-block idempotent has augmentation one. -/
theorem localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d) H
        (localPrincipalBlockElementInAmbientResidue d H) = 1 := by
  change groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d) H
      (MonoidAlgebra.mapRingHom H
        (compatibleSubgroupResidueFieldInclusion d H)
        (BrauerBlockReduction.reducedPrincipalBlockElement (localData d H))) = 1
  rw [groupAlgebraAugmentation_mapRingHom,
    BrauerBlockReduction.reducedPrincipalBlockElement_augmentation_eq_one,
    map_one]

/-- At an involution, the local principal selector and the ambient Brauer
selector have nonzero intersection.  This is the strongest comparison forced
by augmentation alone: both selectors act as one on the trivial module. -/
theorem localPrincipalBlockElement_mul_involutionBrauer_ne_zero
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z ≠ 0 := by
  intro hzero
  have h := congrArg
    (groupAlgebraAugmentation (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G))) hzero
  rw [map_mul, localPrincipalBlockElementInAmbientResidue_augmentation_eq_one,
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement_augmentation_eq_one d z hz,
    one_mul, map_zero] at h
  exact one_ne_zero h

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
@[expose] def InvolutionPrincipalBrauerEquality
    (d : PrincipalCongruenceBlockData G) (z : G) : Prop :=
  let H := Subgroup.centralizer ({z} : Set G)
  localPrincipalBlockElementInAmbientResidue d H =
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z

end CompatibleBrauerBlock

end ModularBlock

