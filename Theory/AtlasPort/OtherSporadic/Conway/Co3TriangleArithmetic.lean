/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleArithmetic.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleParameters
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleArithmetic.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

namespace Atlas.Conway
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem co3_triangle_ambient_divisibility (T : Finset (Fin 8)) (h0 : 0 ∈ T) (h3 : 3 ∈ T)
    (hd : (∑ t ∈ T, co3TriangleSize t) ∣ 8315553613086720000) :
    T = {0,1,3} ∨ T = Finset.univ := by
  revert hd h3 h0 T
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem co3_triangle_block_divisibility (T : Finset (Fin 8)) (h0 : 0 ∈ T)
    (hd : (∑ t ∈ T, co3TriangleSize t) ∣ 48600) :
    T = {0} ∨ T = {0,1,3} ∨ T = Finset.univ := by
  revert hd h0 T
  decide +kernel

end Atlas.Conway
