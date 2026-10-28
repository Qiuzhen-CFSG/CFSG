/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway2Simplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co2Simplicity

/-!
Simplicity and faithful orthogonal-line action of the actual Conway Co2 model.
The proof specializes the established Iwasawa argument for its full vector stabilizer.

Source: Gerald Höhn, `Atlas/Sporadic/Conway2Simplicity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

namespace Atlas.Sporadic.Conway2

theorem faithful : FaithfulSMul Model Points := Atlas.Conway.co2_lines_faithful

theorem isSimpleGroup : IsSimpleGroup Model := Atlas.Conway.co2_simple

end Atlas.Sporadic.Conway2
