/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleSmallTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleOddTransport
public import Theory.AtlasPort.OtherSporadic.Conway.SignedSupportNegative
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleSmallTransport.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem co3_triangle_shape_zero_transitive (a : Omega) (x y : leech)
    (hx : Co3TriangleShape a 0 x) (hy : Co3TriangleShape a 0 y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  exact ⟨1,hx.trans hy.symm⟩

theorem co3_triangle_shape_one_transitive (a : Omega) (x y : leech)
    (hx : Co3TriangleShape a 1 x) (hy : Co3TriangleShape a 1 y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  obtain ⟨S,hS,haS,hx⟩ := hx
  obtain ⟨T,hT,haT,hy⟩ := hy
  obtain ⟨g,hga,hg⟩ := mathieu24_fixing_small_set_transitive {a} S T 2
    (by simpa using haS) (by simpa using haT) hS hT (by simp)
  refine ⟨⟨g,hga a (by simp)⟩,Subtype.ext ?_⟩
  change integerPermutation g.val x.val = y.val
  rw [hx,hy,permutation_constantSupport,hg]

theorem octad_negative_four_transport (a : Omega) (S T : Finset Omega)
    (hS : S ∈ octads) (hT : T ∈ octads) (s : S → Bit) (t : T → Bit)
    (haS : a ∈ S) (haT : a ∈ T) (hs : s ⟨a,haS⟩ = 0) (ht : t ⟨a,haT⟩ = 0)
    (hws : hammingNorm s = 4) (hwt : hammingNorm t = 4) :
    ∃ g : Mathieu24CodeModel, g.val a = a ∧ permuteBlock g.val S = T ∧
      permuteBlock g.val (signedSupportNegative S s) = signedSupportNegative T t := by
  have has := signedSupportNegative_positive S s a haS hs
  have hat := signedSupportNegative_positive T t a haT ht
  obtain ⟨g,hga,hg⟩ := mathieu24_fixing_small_set_transitive {a}
    (signedSupportNegative S s) (signedSupportNegative T t) 4
    (by simpa using has) (by simpa using hat)
    ((signedSupportNegative_card S s).trans hws) ((signedSupportNegative_card T t).trans hwt)
    (by simp)
  have ha : g.val a = a := hga a (by simp)
  refine ⟨g,ha,?_,hg⟩
  apply octad_unique_on_five (insert a (signedSupportNegative T t)) _ T
  · rw [Finset.card_insert_of_notMem hat,signedSupportNegative_card,hwt]
  · exact (codePreserving_octadPreserving g.val g.prop S).mp hS
  · exact hT
  · apply Finset.insert_subset
    · exact Finset.mem_image.mpr ⟨a,haS,ha⟩
    · rw [← hg]
      exact Finset.image_subset_image (signedSupportNegative_subset S s)
  · exact Finset.insert_subset haT (signedSupportNegative_subset T t)

theorem co3_triangle_shape_five_transitive (a : Omega) (x y : leech)
    (hx : Co3TriangleShape a 5 x) (hy : Co3TriangleShape a 5 y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  obtain ⟨S,hS,s,⟨haS,hs⟩,hns,hx⟩ := hx
  obtain ⟨T,hT,t,⟨haT,ht⟩,hnt,hy⟩ := hy
  have hws : hammingNorm s = 4 := by rw [supportNegativeCount_eq_weight] at hns; omega
  have hwt : hammingNorm t = 4 := by rw [supportNegativeCount_eq_weight] at hnt; omega
  obtain ⟨g,ha,hg,hN⟩ := octad_negative_four_transport a S T hS hT s t haS haT hs ht hws hwt
  refine ⟨⟨g,ha⟩,Subtype.ext ?_⟩
  change integerPermutation g.val x.val = y.val
  rw [hx,hy]
  funext i
  have he := congrFun (permutation_signedSupport_of_sets g S T s t hg hN) i
  change 2*signedSupport S s (g.val.symm i) = 2*signedSupport T t i
  change signedSupport S s (g.val.symm i) = signedSupport T t i at he
  rw [he]

theorem co3_triangle_first_six_transitive (a : Omega) (t : Fin 8) (ht : t.val < 6)
    (x y : leech) (hx : Co3TriangleShape a t x) (hy : Co3TriangleShape a t y) :
    ∃ g : Mathieu23PointModel a, (permutationEmbedding g.val).val x = y := by
  fin_cases t
  · exact co3_triangle_shape_zero_transitive a x y hx hy
  · exact co3_triangle_shape_one_transitive a x y hx hy
  · exact co3_triangle_shape_two_transitive a x y hx hy
  · exact co3_triangle_shape_three_transitive a x y hx hy
  · exact co3_triangle_shape_four_transitive a x y hx hy
  · exact co3_triangle_shape_five_transitive a x y hx hy
  · norm_num at ht
  · norm_num at ht

end Atlas.Conway
