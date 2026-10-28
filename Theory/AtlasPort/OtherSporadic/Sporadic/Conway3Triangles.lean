/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway3Triangles.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3Geometry
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleCount
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Sporadic/Conway3Triangles.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway3
open Atlas.Codes Atlas.Lattices Atlas.Conway

/-- Intrinsic oriented 2-3-4 Leech triangles with fixed norm-six side. -/
abbrev Triangles := Co3Triangles ((0,0),0)

instance triangleAction : MulAction Model Triangles := co3TrianglesAction ((0,0),0)

def baseTriangle : Triangles := co3BaseTriangle _

theorem triangles_card : Nat.card Triangles = 48600 := co3_triangles_card _

def triangleParametersEquiv :
    ((t : Fin 8) × Co3TriangleParameters ((0,0),0) t) ≃ Triangles := co3TriangleEquiv _

theorem triangle_shape_card (t : Fin 8) :
    Nat.card {y : leech // Co3TriangleShape ((0,0),0) t y} = co3TriangleSize t :=
  co3_triangle_shape_card _ t

theorem triangle_stabilizer_eq : MulAction.stabilizer Model baseTriangle = TriangleStabilizer :=
  co3_triangle_stabilizer_eq _

end Atlas.Sporadic.Conway3
