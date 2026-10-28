/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSHexadComparison.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSGraph
public import Theory.AtlasPort.OtherSporadic.Mathieu.HexadDesignCounts
public import Theory.AtlasPort.OtherSporadic.Combinatorics.HexadIntersectionCounts

/-!
Comparison of the lattice graph with the hexad extension graph.
Explicit point and hexad bijections preserve each incidence case and give a graph isomorphism.

Source: Gerald Höhn, `Atlas/Conway/HSHexadComparison.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices Atlas.Combinatorics
attribute [local instance] Classical.propDecidable
local instance : Fintype (Mathieu23Points co3MarkedCoordinate) := Fintype.ofFinite _
local instance : Fintype HSPointLabels := Fintype.ofFinite _

abbrev HSWittHexads := {B // B ∈ mathieu22Blocks co3MarkedCoordinate co3BasePoint}

def hsHexadLabelEquiv : HSHexadLabels ≃ HSWittHexads :=
  (show HSHexadLabels ≃ {B // B ∈ mathieu23Blocks co3MarkedCoordinate ∧ co3BasePoint ∈ B} from {
    toFun B := ⟨B.val.val,B.val.prop,B.prop⟩
    invFun B := ⟨⟨B.val,B.prop.1⟩,B.prop.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }).trans
      (derivedBlocksThroughEquiv (mathieu23Blocks co3MarkedCoordinate) co3BasePoint).symm

theorem hs_hexad_mem (B : HSHexadLabels) (c : HSPointLabels) :
    c ∈ (hsHexadLabelEquiv B).val ↔ c.val ∈ B.val.val := by
  have h := derivedBlocksThroughEquiv_other_mem (mathieu23Blocks co3MarkedCoordinate)
    co3BasePoint c (hsHexadLabelEquiv B)
  have he : (derivedBlocksThroughEquiv (mathieu23Blocks co3MarkedCoordinate) co3BasePoint
      (hsHexadLabelEquiv B)).val = B.val.val :=
    congrArg Subtype.val ((derivedBlocksThroughEquiv (mathieu23Blocks co3MarkedCoordinate)
      co3BasePoint).apply_symm_apply ⟨B.val.val,B.val.prop,B.prop⟩)
  rw [he] at h
  exact h.symm

set_option maxHeartbeats 800000 in
theorem hs_hexad_intersection (B C : HSHexadLabels) :
    (B.val.val ∩ C.val.val).card =
      ((hsHexadLabelEquiv B).val ∩ (hsHexadLabelEquiv C).val).card+1 := by
  let e := derivedBlocksThroughEquiv (mathieu23Blocks co3MarkedCoordinate) co3BasePoint
  have hB : B.val.val = insert co3BasePoint (complementBlockLift co3BasePoint (hsHexadLabelEquiv B).val) :=
    (congrArg Subtype.val (e.apply_symm_apply ⟨B.val.val,B.val.prop,B.prop⟩)).symm
  have hC : C.val.val = insert co3BasePoint (complementBlockLift co3BasePoint (hsHexadLabelEquiv C).val) :=
    (congrArg Subtype.val (e.apply_symm_apply ⟨C.val.val,C.val.prop,C.prop⟩)).symm
  rw [hB,hC,← Finset.insert_inter_distrib]
  have hm : complementBlockLift co3BasePoint (hsHexadLabelEquiv B).val ∩
      complementBlockLift co3BasePoint (hsHexadLabelEquiv C).val =
      complementBlockLift co3BasePoint ((hsHexadLabelEquiv B).val ∩ (hsHexadLabelEquiv C).val) :=
    (Finset.map_inter _ _).symm
  rw [hm,Finset.card_insert_of_notMem (complementBlockLift_not_mem _ _),complementBlockLift_card]

theorem hs_hexads_disjoint_adjacent (B C : HSHexadLabels) :
    hsWittGraph.Adj (Sum.inr (Sum.inr B)) (Sum.inr (Sum.inr C)) ↔
      Disjoint (hsHexadLabelEquiv B).val (hsHexadLabelEquiv C).val := by
  rw [hs_witt_hexads_adjacent,hs_hexad_intersection]
  simp [Finset.card_eq_zero,Finset.disjoint_iff_inter_eq_empty]

theorem hs_hexad_design_data : HexadDesignData (mathieu22Blocks co3MarkedCoordinate co3BasePoint) where
  card := mathieu22Blocks_card _ _
  size := mathieu22Blocks_size _ _
  point := by
    intro b
    convert mathieu22Blocks_through_point_card co3MarkedCoordinate co3BasePoint b using 1
    congr 1
    ext E
    simp only [Finset.mem_filter]
  pair := by
    intro b c hbc
    convert mathieu22Blocks_through_pair_card co3MarkedCoordinate co3BasePoint b c hbc using 1
    congr 1
    ext E
    simp only [Finset.mem_filter]
  intersection := by
    intro B hB C hC hBC
    convert mathieu22_hexad_intersection co3MarkedCoordinate co3BasePoint B C hB hC hBC using 1 <;> apply Iff.of_eq <;> congr 2 <;> ext j <;> simp only [Finset.mem_inter]

end Atlas.Conway
