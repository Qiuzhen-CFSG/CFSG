/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleFusion.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleFusionCoordinates
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleFusion.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def co3TriangleFusionElement (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a) : Co3MarkedModel :=
  ⟨co3FusionIsometry p,co3Fusion_fixes_normSix p hp⟩

theorem co3_base_triangle_type : co3TriangleType co3MarkedCoordinate (co3BaseTriangle co3MarkedCoordinate) = 0 :=
  co3_triangle_shape_coordinate_type co3MarkedCoordinate 0 _ rfl

theorem co3TrianglePair_shape :
    Co3TriangleShape co3MarkedCoordinate 1 (minimumPairPlus ((0,0),1) ((0,0),2)) := by
  refine ⟨{((0,0),1),((0,0),2)},by decide,by decide,?_⟩
  decide +kernel

def co3TrianglePair : Co3Triangles co3MarkedCoordinate :=
  ⟨minimumPairPlus ((0,0),1) ((0,0),2),co3_triangle_shape_sound _ 1 _ co3TrianglePair_shape⟩

theorem co3TrianglePair_type : co3TriangleType co3MarkedCoordinate co3TrianglePair = 1 :=
  co3_triangle_shape_coordinate_type _ 1 _ co3TrianglePair_shape

theorem co3TriangleFusion_base_type (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget) :
    co3TriangleType co3MarkedCoordinate (co3TriangleFusionElement p hp • co3BaseTriangle co3MarkedCoordinate) = 3 := by
  change co3TriangleCoordinateType co3MarkedCoordinate
    ((co3FusionIsometry p).val (oddMinimumVector co3MarkedCoordinate 0)).val = 3
  simp only [co3TriangleCoordinateType,co3Fusion_triangle_base_coordinate p hp hO]
  norm_num

theorem co3TriangleFusion_pair_type (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget) :
    co3TriangleType co3MarkedCoordinate (co3TriangleFusionElement p hp • co3TrianglePair) = 5 := by
  change co3TriangleCoordinateType co3MarkedCoordinate
    ((co3FusionIsometry p).val (minimumPairPlus ((0,0),1) ((0,0),2))).val = 5
  simp only [co3TriangleCoordinateType,co3Fusion_triangle_pair_coordinate p hp hO]
  norm_num

theorem co3_triangle_two_fusions : ∃ g : Co3MarkedModel,
    co3TriangleType co3MarkedCoordinate (g • co3BaseTriangle co3MarkedCoordinate) = 3 ∧
      co3TriangleType co3MarkedCoordinate (g • co3TrianglePair) = 5 := by
  obtain ⟨p,hp,hO⟩ := co3Fusion_permutation_exists
  exact ⟨co3TriangleFusionElement p hp,co3TriangleFusion_base_type p hp hO,co3TriangleFusion_pair_type p hp hO⟩

end Atlas.Conway
