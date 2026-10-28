/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway3Maximality.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3Triangles
public import Theory.AtlasPort.OtherSporadic.Conway.Co3MathieuMaximal
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Sporadic/Conway3Maximality.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway3
open Atlas.Codes Atlas.Lattices Atlas.Conway

def triangleType : Triangles → Fin 8 := co3TriangleType co3MarkedCoordinate

theorem triangle_subdegree (t : Fin 8) :
    Nat.card {y : Triangles // triangleType y = t} = co3TriangleSize t := co3_triangle_type_card _ t

theorem triangle_mathieu_orbits (x y : Triangles) :
    (∃ g : Mathieu23PointModel co3MarkedCoordinate, mathieu23Embedding g • x = y) ↔
      triangleType x = triangleType y := co3_triangle_mathieu_orbit_iff _ x y

theorem triangles_transitive : MulAction.IsPretransitive Model Triangles := co3_triangles_transitive

theorem triangles_primitive : MulAction.IsPreprimitive Model Triangles := co3_triangles_primitive

theorem triangle_stabilizer_maximal : IsCoatom TriangleStabilizer := co3_mathieu23_maximal

end Atlas.Sporadic.Conway3
