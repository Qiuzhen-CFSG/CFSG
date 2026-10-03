module

public import Theory.GroupTheory.ZStar.ThirdMain.DirectBrauerFactor

/-!
# A primitive factor in the ambient centralizer

A failed involution Brauer equality gives a nonzero direct Brauer factor.
Its centralizer transport is central and idempotent, so finiteness permits
extracting a primitive central factor beneath it. Augmentation zero passes
to the restriction, transport, and primitive factor. The resulting factor
therefore lies beneath the ambient principal Brauer image, with the same
admissible two-subgroup.

Ported from the ambient-factor extraction in
`c3503435:glauberman_zStar/Submission/ZStar/ThirdMainReduction.lean`.
-/

public section
noncomputable section
namespace Glauberman.ZStar.ThirdMainReduction
open ModularBlock PrincipalBlockConstruction
universe u
attribute [local instance] Fintype.ofFinite

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
          IsCentrallyPrimitive β ∧
          groupAlgebraAugmentation K
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
  let : Finite (BrauerBlockReduction.principalResidueField d) :=
    principalResidueField_finite d
  let : Fintype (BrauerBlockReduction.principalResidueField d) :=
    Fintype.ofFinite (BrauerBlockReduction.principalResidueField d)
  let : Fintype C := Fintype.ofFinite C
  let : DecidableEq C := Classical.decEq C
  let : Finite A := by
    exact Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
      groupAlgebraAugmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer
            (Q : Set (Subgroup.centralizer ({z} : Set G))))
          (DefectSupport.subgroupCentralizerRestriction
            (BrauerBlockReduction.principalResidueField d) Q f) = 0 := by
    rw [SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
      Q hfMax.1.1 f hfprimitive.1, hfaug]
  have hgaug :
      groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d) C g = 0 := by
    rw [show groupAlgebraAugmentation
          (BrauerBlockReduction.principalResidueField d) C g =
        groupAlgebraAugmentation
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
      groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d) C β = 0 := by
    have h := congrArg
      (groupAlgebraAugmentation
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

end Glauberman.ZStar.ThirdMainReduction
