/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3ActionTransitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3FusionCoordinates
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3Geometry
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3ActionTransitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def co3OutsidePoint : Mathieu23Points co3MarkedCoordinate := ⟨((0,1),0),by change ((0,1),0) ≠ co3MarkedCoordinate; decide⟩

theorem co3Fusion_heptad_image (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget) :
    ∃ B : {B // B ∈ mathieu23Blocks co3MarkedCoordinate},
    (⟨co3FusionIsometry p,co3Fusion_fixes_normSix p hp⟩ : Co3MarkedModel) • co3PointHeptadDecompositionEquiv _ (Sum.inl co3OutsidePoint) =
      co3PointHeptadDecompositionEquiv _ (Sum.inr B) := by
  let g : Co3MarkedModel := ⟨co3FusionIsometry p,co3Fusion_fixes_normSix p hp⟩
  obtain ⟨q,hq⟩ := (co3PointHeptadDecompositionEquiv co3MarkedCoordinate).surjective
    (g • co3PointHeptadDecompositionEquiv _ (Sum.inl co3OutsidePoint))
  cases q with
  | inr B => exact ⟨B,hq.symm⟩
  | inl b =>
    have he := congrArg Subtype.val hq
    change ({minimumPairPlus co3MarkedCoordinate b.val,
      normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate b.val} : Finset leech) =
      ({minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val,
      normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val} : Finset leech).image g.val.val at he
    have hm : g.val.val (minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val) ∈
        ({minimumPairPlus co3MarkedCoordinate b.val,
        normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate b.val} : Finset leech) := by
      rw [he]; exact Finset.mem_image.mpr ⟨_,Finset.mem_insert_self _ _,rfl⟩
    have hc := co3Fusion_image_marked_coordinate p hp hO
    change (g.val.val (minimumPairPlus co3MarkedCoordinate co3OutsidePoint.val)).val co3MarkedCoordinate = 3 at hc
    rcases Finset.mem_insert.mp hm with h | h
    · rw [h] at hc
      have hb : b.val ≠ co3MarkedCoordinate := b.prop
      simp [minimumPairPlus,coordinateVector,hb.symm] at hc
    · have h := Finset.mem_singleton.mp h
      rw [h] at hc
      change (normSixVector co3MarkedCoordinate).val co3MarkedCoordinate-
        (minimumPairPlus co3MarkedCoordinate b.val).val co3MarkedCoordinate = 3 at hc
      have hb : b.val ≠ co3MarkedCoordinate := b.prop
      simp [normSixVector_apply,minimumPairPlus,coordinateVector,hb.symm] at hc

theorem co3_point_heptad_fusion : ∃ g : Co3MarkedModel,
    ∃ B : {B // B ∈ mathieu23Blocks co3MarkedCoordinate},
    g • co3PointHeptadDecompositionEquiv _ (Sum.inl co3OutsidePoint) =
      co3PointHeptadDecompositionEquiv _ (Sum.inr B) := by
  obtain ⟨p,hp,hO⟩ := co3Fusion_permutation_exists
  obtain ⟨B,hB⟩ := co3Fusion_heptad_image p hp hO
  exact ⟨⟨co3FusionIsometry p,co3Fusion_fixes_normSix p hp⟩,B,hB⟩

theorem co3_all_decompositions_in_orbit (q : Co3PointHeptad co3MarkedCoordinate) :
    co3PointHeptadDecompositionEquiv _ q ∈ MulAction.orbit Co3MarkedModel
      (co3PointHeptadDecompositionEquiv _ (Sum.inl co3OutsidePoint)) := by
  cases q with
  | inl b =>
    obtain ⟨p,hp⟩ := co3_points_mathieu_transitive _ co3OutsidePoint b
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨mathieu23ToNormSixStabilizer _ p,?_⟩
    rw [← co3PointHeptadDecomposition_equivariant,hp]
  | inr B =>
    obtain ⟨g,C,hg⟩ := co3_point_heptad_fusion
    obtain ⟨p,hp⟩ := co3_heptads_mathieu_transitive _ C B
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨mathieu23ToNormSixStabilizer _ p*g,?_⟩
    rw [mul_smul,hg,← co3PointHeptadDecomposition_equivariant,hp]

theorem co3_decompositions_pretransitive :
    MulAction.IsPretransitive Co3MarkedModel (MinimumDecompositions (normSixVector co3MarkedCoordinate)) := by
  apply (MulAction.isPretransitive_iff_base
    (co3PointHeptadDecompositionEquiv _ (Sum.inl co3OutsidePoint))).mpr
  intro y
  obtain ⟨q,rfl⟩ := (co3PointHeptadDecompositionEquiv co3MarkedCoordinate).surjective y
  exact MulAction.mem_orbit_iff.mp (co3_all_decompositions_in_orbit q)

end Atlas.Conway
