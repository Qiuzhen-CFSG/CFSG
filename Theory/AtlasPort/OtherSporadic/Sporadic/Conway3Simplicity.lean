/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway3Simplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3Simplicity
/-!
Simplicity of the full norm-six Leech-vector stabilizer.
The proof uses the primitive point action and maximal simple Mathieu triangle stabilizer.

Source: Gerald Höhn, `Atlas/Sporadic/Conway3Simplicity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

namespace Atlas.Sporadic.Conway3

theorem isSimpleGroup : IsSimpleGroup Model := Atlas.Conway.co3_simple

end Atlas.Sporadic.Conway3
