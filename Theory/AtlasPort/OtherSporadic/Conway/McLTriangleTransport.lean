/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLTriangleTransport.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLTriangleCounts
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleSixTransport
public import Theory.AtlasPort.OtherSporadic.Mathieu.OrderedTripleTransport

/-!
Mathieu22 transport within each of the four triangle shapes.
Marked coordinate permutations transport the explicit Golay octad and
signed-octad parameters while preserving both marked coordinates.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLTriangleTransport.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

private def mclMarkedPermutation (g : Mathieu24CodeModel)
    (ha : g.val co3MarkedCoordinate = co3MarkedCoordinate)
    (hp : g.val co3BasePoint.val = co3BasePoint.val) : McLMathieuModel :=
  ⟨⟨g,ha⟩,Subtype.ext hp⟩

private theorem mcl_inside_triple_transport (O P : Finset Omega)
    (hO : O ∈ octads) (hP : P ∈ octads) (b e : Omega)
    (hba : b ≠ co3MarkedCoordinate) (hbp : b ≠ co3BasePoint.val)
    (hea : e ≠ co3MarkedCoordinate) (hep : e ≠ co3BasePoint.val)
    (haO : co3MarkedCoordinate ∈ O) (hpO : co3BasePoint.val ∈ O) (hbO : b ∈ O)
    (haP : co3MarkedCoordinate ∈ P) (hpP : co3BasePoint.val ∈ P) (heP : e ∈ P) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val O = P ∧
      g.val co3MarkedCoordinate = co3MarkedCoordinate ∧
      g.val co3BasePoint.val = co3BasePoint.val ∧ g.val b = e := by
  obtain ⟨g,hga,hgp,hgb⟩ := mathieu24_ordered_triple_transport
    co3MarkedCoordinate co3BasePoint.val b co3MarkedCoordinate co3BasePoint.val e
    (Ne.symm co3BasePoint.prop) hba hbp (Ne.symm co3BasePoint.prop) hea hep
  obtain ⟨h,hh,hhO⟩ := mathieu24_marked_octad_transitive
    {co3MarkedCoordinate,co3BasePoint.val,e} (permuteBlock g.val O) P
    (by
      have h1 := Finset.card_insert_le co3MarkedCoordinate {co3BasePoint.val,e}
      have h2 := Finset.card_insert_le co3BasePoint.val {e}
      simp only [Finset.card_singleton] at h2
      omega)
    ((codePreserving_octadPreserving g.val g.prop O).mp hO) hP
    (by
      apply Finset.insert_subset (Finset.mem_image.mpr ⟨_,haO,hga⟩)
      apply Finset.insert_subset (Finset.mem_image.mpr ⟨_,hpO,hgp⟩)
      exact Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨_,hbO,hgb⟩))
    (by simp [Finset.insert_subset_iff,haP,hpP,heP])
  refine ⟨h*g,?_,?_,?_,?_⟩
  · change permuteBlock (h.val*g.val) O = P
    rw [permuteBlock_mul,hhO]
  · change h.val (g.val co3MarkedCoordinate) = _
    rw [hga,hh _ (by simp)]
  · change h.val (g.val co3BasePoint.val) = _
    rw [hgp,hh _ (by simp)]
  · change h.val (g.val b) = e
    rw [hgb,hh _ (by simp)]

theorem mcl_triangle_shape_one_transitive (x y : leech)
    (hx : McLTriangleShape 1 x) (hy : McLTriangleShape 1 y) :
    ∃ g : McLMathieuModel, (permutationEmbedding g.val.val).val x = y := by
  obtain ⟨c,hc,hca,hcp,rfl⟩ := hx
  obtain ⟨d,hd,hda,hdp,rfl⟩ := hy
  obtain ⟨g,hg,ha,hp⟩ := mathieu24_octad_exterior_pair_transitive
    (support c.val) (support d.val) ((octads_mem _).mpr ⟨c,hc,rfl⟩)
    ((octads_mem _).mpr ⟨d,hd,rfl⟩)
    co3MarkedCoordinate co3BasePoint.val co3MarkedCoordinate co3BasePoint.val
    (by simp [support,hca]) (by simp [support,hcp]) (Ne.symm co3BasePoint.prop)
    (by simp [support,hda]) (by simp [support,hdp]) (Ne.symm co3BasePoint.prop)
  exact ⟨mclMarkedPermutation g ha hp,by
    change (permutationEmbedding g).val _ = _
    rw [permutation_oddMinimumVector,hp,golay_support_transport g c d hg]⟩

theorem mcl_triangle_shape_two_transitive (x y : leech)
    (hx : McLTriangleShape 2 x) (hy : McLTriangleShape 2 y) :
    ∃ g : McLMathieuModel, (permutationEmbedding g.val.val).val x = y := by
  obtain ⟨b,c,hba,hbp,hc,hca,hcp,hcb,rfl⟩ := hx
  obtain ⟨e,d,hea,hep,hd,hda,hdp,hde,rfl⟩ := hy
  obtain ⟨g,hg,ha,hp,hbe⟩ := mcl_inside_triple_transport
    (support c.val) (support d.val) ((octads_mem _).mpr ⟨c,hc,rfl⟩)
    ((octads_mem _).mpr ⟨d,hd,rfl⟩) b e hba hbp hea hep
    ((golay_coordinate_support c _).mpr hca) ((golay_coordinate_support c _).mpr hcp)
    ((golay_coordinate_support c _).mpr hcb) ((golay_coordinate_support d _).mpr hda)
    ((golay_coordinate_support d _).mpr hdp) ((golay_coordinate_support d _).mpr hde)
  exact ⟨mclMarkedPermutation g ha hp,by
    change (permutationEmbedding g).val _ = _
    rw [permutation_oddMinimumVector,hbe,golay_support_transport g c d hg]⟩

private theorem negative_pair_with_mark (T : Finset Omega) (s : T → Bit)
    (hn : supportNegativeCount T s = 2) (p : Omega)
    (hp : ∃ h : p ∈ T, s ⟨p,h⟩ = 1) :
    ∃ b, p ≠ b ∧ signedSupportNegative T s = {p,b} := by
  have hw : hammingNorm s = 2 := by rw [supportNegativeCount_eq_weight] at hn; omega
  have hm : p ∈ signedSupportNegative T s := by
    obtain ⟨hp,hs⟩ := hp
    exact (signedSupportNegative_mem T s p).mpr ⟨hp,by rw [hs]; decide⟩
  obtain ⟨b,c,hbc,hN⟩ := Finset.card_eq_two.mp ((signedSupportNegative_card T s).trans hw)
  rw [hN] at hm
  rcases Finset.mem_insert.mp hm with hb | hc
  · subst b; exact ⟨c,hbc,hN⟩
  · have hc := Finset.mem_singleton.mp hc
    subst c
    exact ⟨b,Ne.symm hbc,hN.trans (Finset.pair_comm _ _)⟩

theorem mcl_triangle_shape_three_transitive (x y : leech)
    (hx : McLTriangleShape 3 x) (hy : McLTriangleShape 3 y) :
    ∃ g : McLMathieuModel, (permutationEmbedding g.val.val).val x = y := by
  obtain ⟨S,hS,s,haS,hns,hps,hx⟩ := hx
  obtain ⟨T,hT,t,haT,hnt,hpt,hy⟩ := hy
  obtain ⟨b,hpb,hN⟩ := negative_pair_with_mark S s hns co3BasePoint.val hps
  obtain ⟨e,hpe,hM⟩ := negative_pair_with_mark T t hnt co3BasePoint.val hpt
  have hbS : b ∈ S := signedSupportNegative_subset S s (by rw [hN]; simp)
  have heT : e ∈ T := signedSupportNegative_subset T t (by rw [hM]; simp)
  obtain ⟨g,hg,hp,hbe,ha⟩ := mathieu24_octad_inside_pair_outside_transitive S T hS hT
    co3BasePoint.val b co3MarkedCoordinate co3BasePoint.val e co3MarkedCoordinate
    hps.choose hbS hpb haS hpt.choose heT hpe haT
  have hneg : permuteBlock g.val (signedSupportNegative S s) = signedSupportNegative T t := by
    rw [hN,hM]
    simp [permuteBlock,hp,hbe]
  refine ⟨mclMarkedPermutation g ha hp,Subtype.ext ?_⟩
  change integerPermutation g.val x.val = y.val
  rw [hx,hy]
  funext i
  have he := congrFun (permutation_signedSupport_of_sets g S T s t hg hneg) i
  change 2*signedSupport S s (g.val.symm i) = 2*signedSupport T t i
  change signedSupport S s (g.val.symm i) = signedSupport T t i at he
  rw [he]

theorem mcl_triangle_shape_transitive (t : Fin 4) (x y : leech)
    (hx : McLTriangleShape t x) (hy : McLTriangleShape t y) :
    ∃ g : McLMathieuModel, (permutationEmbedding g.val.val).val x = y := by
  fin_cases t
  · exact ⟨1,hx.trans hy.symm⟩
  · exact mcl_triangle_shape_one_transitive x y hx hy
  · exact mcl_triangle_shape_two_transitive x y hx hy
  · exact mcl_triangle_shape_three_transitive x y hx hy
end Atlas.Conway
