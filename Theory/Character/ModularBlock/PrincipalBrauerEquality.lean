module
public import Theory.Character.ModularBlock.NoExtraObstruction

/-!
# Principal Brauer equality for two-subgroups

For every two-subgroup of a finite group, the Brauer restriction of the
ambient principal selector equals the compatible principal selector of its
centralizer. Their extra factor is a central idempotent of augmentation zero.
If it were nonzero, finite-ring primitive extraction would produce an extra
obstruction, excluded by the maximal-support transfer argument.

This extends the involution assembly of the completed Glauberman block
development without changing its selectors or coefficient maps. It is the
principal-block correspondence input to the subsection constructions in
Alperin--Brauer--Gorenstein, Chapter III, Section 5. Full-defect nonprincipal
block correspondence and decomposition columns are separate later results.
-/

public section
namespace ModularBlock.PrincipalBrauer
open ModularBlock PrincipalBlockConstruction BrauerThirdMain
universe u

/-- Principal Brauer restriction agrees with the compatible local principal selector. -/
theorem subgroupPrincipalBrauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) (hQ : IsPGroup 2 Q) :
    DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d) =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer (Q : Set G)) := by
  apply (SubgroupPrincipalBrauer.subgroupRestriction_eq_local_iff_extra_eq_zero d Q).mpr
  by_contra hne
  obtain ⟨b, hbPrimitive, hbAug, hbExtra⟩ :=
    exists_primitiveExtraFactor_of_centralIdempotent d Q hQ
      (SubgroupPrincipalBrauer.extraBrauerFactor d Q)
      (SubgroupPrincipalBrauer.extraBrauerFactor_mem_center d Q)
      (SubgroupPrincipalBrauer.extraBrauerFactor_isIdempotent d Q hQ)
      hne
      (SubgroupPrincipalBrauer.extraBrauerFactor_augmentation_eq_zero d Q hQ)
      (SubgroupPrincipalBrauer.extraBrauerFactor_mul_subgroupRestriction_eq_self d Q hQ)
  exact not_isExtraObstruction d Q ⟨hQ, b, hbPrimitive, hbAug, hbExtra⟩

end ModularBlock.PrincipalBrauer
