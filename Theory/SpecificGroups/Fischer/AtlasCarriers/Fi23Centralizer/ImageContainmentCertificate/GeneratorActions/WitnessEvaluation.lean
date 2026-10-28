module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation.Checks0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation.Checks1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation.Checks2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation.Checks3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation.Checks4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation.Checks5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation.Checks6
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation.Checks7

/-!
# Exact Fi23 witness actions on all published coordinates

Each of the eight literal inverse cycle products acts on the 3511 published
coordinates by the unchanged shared image table. Existing unconditional
evaluation theorems certify the original inverse cycle products, including
decoding and disjoint supports. Bounded checks compare their actions with the
shared tables at every coordinate, including the extra letter labelled `none`.

This discharges precisely the `hwitnesses` premise of
`witnessGenerator_point_action_of_tables`. Identification of the tables with
Fi22 words is a separate certificate family. No centralizer coverage is used.

Source: `ImageContainmentCertificate/source/centralizer-data.g`, the retained
`ImageData` relabeling, and GLS3 Table 5.3u (the Fischer discussion near line
1042 of `refs/KGroup/GLS3/Chapter5(sec3-).tex`).
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions
open WitnessEvaluation

/-- Every literal witness has its proposed action on every published coordinate. -/
theorem witness_point_action (j : Fin 8) (i : Option (Fin 3510)) :
    witnessGenerator j (ImageData.point i) =
      ImageData.point (Option.map (imageAction j) i) := by
  have h : witnessGenerator j (ImageData.pointIndex (finSuccEquivLast.symm i)) =
      target j (finSuccEquivLast.symm i) := by
    rcases j with ⟨j, hj⟩
    interval_cases j
    · exact generator0_pointIndex _
    · exact generator1_pointIndex _
    · exact generator2_pointIndex _
    · exact generator3_pointIndex _
    · exact generator4_pointIndex _
    · exact generator5_pointIndex _
    · exact generator6_pointIndex _
    · exact generator7_pointIndex _
  simpa only [target, ImageData.point, Equiv.apply_symm_apply] using h

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions
