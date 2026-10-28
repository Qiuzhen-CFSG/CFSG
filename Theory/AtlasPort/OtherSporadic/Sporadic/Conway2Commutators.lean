/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway2Commutators.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway2Geometry
public import Theory.AtlasPort.OtherSporadic.Conway.Co2SignCommutators
public import Theory.AtlasPort.OtherSporadic.Conway.Co2Connector

/-!
Noncommuting elements and an explicit connector in the actual Conway Co2 model.
The results specialize the shortened-sign commutators and sextet connector.

Source: Gerald Höhn, `Atlas/Sporadic/Conway2Commutators.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway2
open Atlas.Conway

theorem exists_mul_ne_mul : ∃ g h : Model, g*h ≠ h*g := co2_noncommuting_pair

def connector : Model := co2ConnectorElement

theorem connector_sq : connector * connector = 1 := Subtype.ext co2Connector_sq

theorem connector_outside_local : connector ∉ LocalGroup := by
  intro h
  exact co2Connector_not_monomial
    ((le_of_eq (orthogonalLineStabilizer_eq_monomial ((0,0),0) ((0,0),1) (by decide))) h)

end Atlas.Sporadic.Conway2
