/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleOddTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleCount
public import Theory.AtlasPort.OtherSporadic.Conway.NormSixOctadOrbit
public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadMarkedPairTransport
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleOddTransport.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem permutation_oddMinimumVector (g : Mathieu24CodeModel) (b : Omega) (c : golay) :
    (permutationEmbedding g).val (oddMinimumVector b c) =
      oddMinimumVector (g.val b) (golayPermutationEquiv g c) := by
  apply Subtype.ext
  change integerPermutation g.val (signChange c.val (oddProfileBase {b} ∅)) = _
  rw [permutation_sign_conjugation,permutation_odd_singleton]
  rfl

theorem golay_support_transport (g : Mathieu24CodeModel) (c d : golay)
    (h : permuteBlock g.val (support c.val) = support d.val) : golayPermutationEquiv g c = d := by
  apply Subtype.ext
  apply support_injective
  exact (coordinatePermutation_support g.val c.val).trans h

theorem golay_complement_transport (g : Mathieu24CodeModel) (c d : golay)
    (h : golayPermutationEquiv g (golayCodeComplement c) = golayCodeComplement d) :
    golayPermutationEquiv g c = d := by
  apply Subtype.ext
  funext i
  have hi := congrArg (fun c : golay => c.val i) h
  change c.val (g.val.symm i)+1 = d.val i+1 at hi
  exact add_right_cancel hi

theorem co3_triangle_shape_two_transitive (a : Omega) (x y : leech)
    (hx : Co3TriangleShape a 2 x) (hy : Co3TriangleShape a 2 y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  obtain ⟨c,hc,hca,rfl⟩ := hx
  obtain ⟨d,hd,hda,rfl⟩ := hy
  let c' := golaySixteenCoordinateEquiv a ⟨c,hc,hca⟩
  let d' := golaySixteenCoordinateEquiv a ⟨d,hd,hda⟩
  have hcO : support c'.val.val ∈ octads := (octads_mem _).mpr ⟨c'.val,c'.prop.1,rfl⟩
  have hdO : support d'.val.val ∈ octads := (octads_mem _).mpr ⟨d'.val,d'.prop.1,rfl⟩
  have hca' : a ∉ support c'.val.val := by simp [support,c'.prop.2]
  have hda' : a ∉ support d'.val.val := by simp [support,d'.prop.2]
  obtain ⟨g,hg,ha⟩ := mathieu24_octad_exterior_transitive _ _ hcO hdO a a hca' hda'
  have he := golay_complement_transport g c d (golay_support_transport g c'.val d'.val hg)
  exact ⟨⟨g,ha⟩,by rw [permutation_oddMinimumVector,ha,he]⟩

theorem co3_triangle_shape_three_transitive (a : Omega) (x y : leech)
    (hx : Co3TriangleShape a 3 x) (hy : Co3TriangleShape a 3 y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  obtain ⟨b,c,hb,hc,hca,hcb,rfl⟩ := hx
  obtain ⟨e,d,he,hd,hda,hde,rfl⟩ := hy
  have hcO : support c.val ∈ octads := (octads_mem _).mpr ⟨c,hc,rfl⟩
  have hdO : support d.val ∈ octads := (octads_mem _).mpr ⟨d,hd,rfl⟩
  obtain ⟨g,hg,ha,hbe⟩ := mathieu24_octad_marked_pair_transitive _ _ hcO hdO a b a e
    ((golay_coordinate_support c a).mpr hca) ((golay_coordinate_support c b).mpr hcb) (Ne.symm hb)
    ((golay_coordinate_support d a).mpr hda) ((golay_coordinate_support d e).mpr hde) (Ne.symm he)
  exact ⟨⟨g,ha⟩,by rw [permutation_oddMinimumVector,hbe,golay_support_transport g c d hg]⟩

theorem co3_triangle_shape_four_transitive (a : Omega) (x y : leech)
    (hx : Co3TriangleShape a 4 x) (hy : Co3TriangleShape a 4 y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  obtain ⟨b,c,hb,hc,hca,hcb,rfl⟩ := hx
  obtain ⟨e,d,he,hd,hda,hde,rfl⟩ := hy
  have hcO : support c.val ∈ octads := (octads_mem _).mpr ⟨c,hc,rfl⟩
  have hdO : support d.val ∈ octads := (octads_mem _).mpr ⟨d,hd,rfl⟩
  obtain ⟨g,hg,ha,hbe⟩ := mathieu24_octad_exterior_pair_transitive _ _ hcO hdO a b a e
    (by simp [support,hca]) (by simp [support,hcb]) (Ne.symm hb)
    (by simp [support,hda]) (by simp [support,hde]) (Ne.symm he)
  exact ⟨⟨g,ha⟩,by rw [permutation_oddMinimumVector,hbe,golay_support_transport g c d hg]⟩

end Atlas.Conway
