/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleSixTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleSmallTransport
public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadInsidePairTransport
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleSixTransport.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem co3_triangle_shape_six_transitive (a : Omega) (x y : leech)
    (hx : Co3TriangleShape a 6 x) (hy : Co3TriangleShape a 6 y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  obtain ⟨S,hS,s,haS,hns,hx⟩ := hx
  obtain ⟨T,hT,t,haT,hnt,hy⟩ := hy
  have hws : hammingNorm s = 2 := by rw [supportNegativeCount_eq_weight] at hns; omega
  have hwt : hammingNorm t = 2 := by rw [supportNegativeCount_eq_weight] at hnt; omega
  obtain ⟨b,c,hbc,hN⟩ := Finset.card_eq_two.mp ((signedSupportNegative_card S s).trans hws)
  obtain ⟨d,e,hde,hM⟩ := Finset.card_eq_two.mp ((signedSupportNegative_card T t).trans hwt)
  have hbS : b ∈ S := signedSupportNegative_subset S s (by rw [hN]; simp)
  have hcS : c ∈ S := signedSupportNegative_subset S s (by rw [hN]; simp)
  have hdT : d ∈ T := signedSupportNegative_subset T t (by rw [hM]; simp)
  have heT : e ∈ T := signedSupportNegative_subset T t (by rw [hM]; simp)
  obtain ⟨g,hg,hgb,hgc,ha⟩ := mathieu24_octad_inside_pair_outside_transitive S T hS hT
    b c a d e a hbS hcS hbc haS hdT heT hde haT
  have hneg : permuteBlock g.val (signedSupportNegative S s) = signedSupportNegative T t := by
    rw [hN,hM]
    simp [permuteBlock,hgb,hgc]
  refine ⟨⟨g,ha⟩,Subtype.ext ?_⟩
  change integerPermutation g.val x.val = y.val
  rw [hx,hy]
  funext i
  have he := congrFun (permutation_signedSupport_of_sets g S T s t hg hneg) i
  change 2*signedSupport S s (g.val.symm i) = 2*signedSupport T t i
  change signedSupport S s (g.val.symm i) = signedSupport T t i at he
  rw [he]

end Atlas.Conway
