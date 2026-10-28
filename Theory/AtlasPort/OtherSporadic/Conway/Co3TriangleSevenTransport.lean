/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleSevenTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleSixTransport
public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadMixedTransport
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleSevenTransport.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem co3_triangle_shape_seven_transitive (a : Omega) (x y : leech)
    (hx : Co3TriangleShape a 7 x) (hy : Co3TriangleShape a 7 y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  obtain ⟨b,c,hb,hc,hca,hcb,rfl⟩ := hx
  obtain ⟨e,d,he,hd,hda,hde,rfl⟩ := hy
  let D : Dodecad := ⟨support c.val,(dodecads_mem _).mpr ⟨c,hc,rfl⟩⟩
  let E : Dodecad := ⟨support d.val,(dodecads_mem _).mpr ⟨d,hd,rfl⟩⟩
  obtain ⟨g,hg,hbe,ha⟩ := dodecad_mixed_flags_transitive D E b a e a
    ((golay_coordinate_support c b).mpr hcb) (by simp [D,support,hca])
    ((golay_coordinate_support d e).mpr hde) (by simp [E,support,hda])
  exact ⟨⟨g,ha⟩,by rw [permutation_oddMinimumVector,hbe,golay_support_transport g c d hg]⟩

theorem co3_triangle_shape_transitive (a : Omega) (t : Fin 8) (x y : leech)
    (hx : Co3TriangleShape a t x) (hy : Co3TriangleShape a t y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  by_cases ht : t.val < 6
  · exact co3_triangle_first_six_transitive a t ht x y hx hy
  have h : t = 6 ∨ t = 7 := by omega
  rcases h with rfl | rfl
  · exact co3_triangle_shape_six_transitive a x y hx hy
  · exact co3_triangle_shape_seven_transitive a x y hx hy

end Atlas.Conway
