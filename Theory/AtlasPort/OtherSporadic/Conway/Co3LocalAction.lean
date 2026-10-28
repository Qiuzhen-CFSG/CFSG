/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3LocalAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3HeptadNeighbourCounts
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3LocalAction.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def co3BaseDecomposition : MinimumDecompositions (normSixVector co3MarkedCoordinate) :=
  co3PointHeptadDecompositionEquiv _ (Sum.inl co3BasePoint)

abbrev Co3PointStabilizer := MulAction.stabilizer Co3MarkedModel co3BaseDecomposition

def co3LocalMathieuElement (p : Mathieu23PointModel co3MarkedCoordinate)
    (hp : p • co3BasePoint = co3BasePoint) : Co3PointStabilizer :=
  ⟨mathieu23ToNormSixStabilizer _ p,by
    change mathieu23ToNormSixStabilizer _ p • co3PointHeptadDecompositionEquiv _ (Sum.inl co3BasePoint) = _
    rw [← co3PointHeptadDecomposition_equivariant]
    change co3PointHeptadDecompositionEquiv _ (Sum.inl (p • co3BasePoint)) = _
    rw [hp]; rfl⟩

theorem co3_local_class_transporter (q r : Co3PointHeptad co3MarkedCoordinate)
    (he : co3LocalType _ co3BasePoint q = co3LocalType _ co3BasePoint r) :
    ∃ g : Co3PointStabilizer, g • co3PointHeptadDecompositionEquiv _ q =
      co3PointHeptadDecompositionEquiv _ r := by
  obtain ⟨p,hp,hr⟩ := co3_local_mathieu_transitive _ co3BasePoint q r he
  refine ⟨co3LocalMathieuElement p hp,?_⟩
  change mathieu23ToNormSixStabilizer _ p • co3PointHeptadDecompositionEquiv _ q = _
  rw [← co3PointHeptadDecomposition_equivariant,hr]

theorem co3LocalType_zero_iff (q : Co3PointHeptad co3MarkedCoordinate) :
    co3LocalType _ co3BasePoint q = 0 ↔ q = Sum.inl co3BasePoint := by
  cases q with
  | inl c => simp [co3LocalType]
  | inr B => simp only [co3LocalType]; split_ifs <;> simp

theorem co3Fusion_complement_heptad (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget)
    (B : Co3Heptads co3MarkedCoordinate)
    (hB : (⟨co3FusionIsometry p,co3Fusion_fixes_normSix p hp⟩ : Co3MarkedModel) •
      co3PointHeptadDecompositionEquiv _ (Sum.inl co3OutsidePoint) =
      co3PointHeptadDecompositionEquiv _ (Sum.inr B)) :
    (co3FusionIsometry p).val (minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val) =
      normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B ∧ co3BasePoint ∉ B.val := by
  have he := congrArg Subtype.val hB
  change ({minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val,
    normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val} : Finset leech).image
      (co3FusionIsometry p).val = {co3HeptadEndpoint _ B,normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B} at he
  have hm : (co3FusionIsometry p).val (minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val) ∈
      ({co3HeptadEndpoint _ B,normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B} : Finset leech) := by
    rw [← he]; exact Finset.mem_image.mpr ⟨_,Finset.mem_insert_self _ _,rfl⟩
  have hc : (co3FusionIsometry p).val (minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val) =
      normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B := by
    rcases Finset.mem_insert.mp hm with h | h
    · have hh := co3Fusion_image_marked_coordinate p hp hO
      change ((co3FusionIsometry p).val (minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val)).val co3MarkedCoordinate = 3 at hh
      rw [h,co3HeptadEndpoint_marked] at hh
      norm_num at hh
    · exact Finset.mem_singleton.mp h
  refine ⟨hc,?_⟩
  have hd := (co3FusionIsometry p).prop (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)
    (minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val)
  rw [co3Fusion_fixes_base_endpoint p hp,hc,co3Point_heptad_complement_dot,
    co3_point_pair_dot _ _ _ (by decide) (by decide) (by decide)] at hd
  by_contra h
  simp [h] at hd

theorem co3Fusion_not_preserves_through (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget) :
    (co3ThroughHeptadVectors co3MarkedCoordinate co3BasePoint).image (co3FusionIsometry p).val ≠
      co3ThroughHeptadVectors co3MarkedCoordinate co3BasePoint := by
  intro hs
  obtain ⟨B,hB⟩ := co3Fusion_heptad_image p hp hO
  obtain ⟨hc,hb⟩ := co3Fusion_complement_heptad p hp hO B hB
  have hn := leech_isometry_neighbour_card (co3FusionIsometry p) _ hs
    (minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val) 16
  rw [hc,co3_complement_heptad_neighbours _ _ B hb,
    co3_point_heptad_neighbours _ co3BasePoint co3OutsidePoint (by decide)] at hn
  norm_num at hn

end Atlas.Conway
