/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3MathieuMaximal.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TrianglePrimitivity
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3MathieuMaximal.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction

instance co3TriangleNontrivial : Nontrivial (Co3Triangles co3MarkedCoordinate) := by
  refine ⟨⟨co3BaseTriangle co3MarkedCoordinate,co3TrianglePair,?_⟩⟩
  intro he
  have ht := congrArg (co3TriangleType co3MarkedCoordinate) he
  rw [co3_base_triangle_type,co3TrianglePair_type] at ht
  exact (by decide : (0 : Fin 8) ≠ 1) ht

theorem co3_mathieu23_maximal : IsCoatom (Co3TriangleStabilizer co3MarkedCoordinate) := by
  rw [← co3_triangle_stabilizer_eq]
  let := co3_triangles_primitive
  exact IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive Co3MarkedModel (co3BaseTriangle co3MarkedCoordinate)

end Atlas.Conway
