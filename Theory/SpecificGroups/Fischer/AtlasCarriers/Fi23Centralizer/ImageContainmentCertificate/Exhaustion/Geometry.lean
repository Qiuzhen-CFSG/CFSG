module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Evaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Separation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness6
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness7

/-!
# Separation and commutation for the Fi23 centralizer exhaustion

Induction along the checked original representative words proves their images
at 0 and candidate(0). These images separate every nonbase representative.
Disjoint inverse-cycle certificates identify each of the eight original saved
witnesses with its checked action, which commutes with the candidate table.
Only identification of the two source generator maps is left explicit in the
permutation commutation theorem, exactly as in `Exhaustion.Evaluation`.

These are the two geometric certificates consumed by the shared exhaustion
assembly. They do not assert Schreier edge membership or centralizer coverage.
Source: ATLAS F23G1-p31671B0 and the unchanged saved `centralizer-data.g`, for
GLS3 Table 5.3u and the conjugation description near line 754 of Chapter 5.
`Geometry/source/README.md` records reproduction, conventions and measurements.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion
open Fi24Prime.Fi23Lift.Certificate

theorem separation_check : checkPow separationCheck 0 15 = true :=
  Geometry.separation_of_checks Geometry.evaluationChecks

theorem witnessGenerators_commute_of_source_maps
    (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x) :
    ∀ j : Fin 8, witnessGenerator j * inclusion candidate =
      inclusion candidate * witnessGenerator j := by
  intro j
  fin_cases j
  · exact Geometry.Witness0.commutes hA hB
  · exact Geometry.Witness1.commutes hA hB
  · exact Geometry.Witness2.commutes hA hB
  · exact Geometry.Witness3.commutes hA hB
  · exact Geometry.Witness4.commutes hA hB
  · exact Geometry.Witness5.commutes hA hB
  · exact Geometry.Witness6.commutes hA hB
  · exact Geometry.Witness7.commutes hA hB

/-- Application of the separation certificate to the original commuting representatives. -/
theorem representative_separated_of_source_maps
    (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x)
    (x : Fin 31671) (hx : representative x * candidate = candidate * representative x) :
    x = base :=
  representative_separated_of_check hA hB separation_check x hx

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion
