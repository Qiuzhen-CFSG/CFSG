/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3DoubleTransitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3ThirdLocalOrbit
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3DoubleTransitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev co3LocalOrbit := MulAction.orbit Co3PointStabilizer
  (co3PointHeptadDecompositionEquiv co3MarkedCoordinate (Sum.inl co3OutsidePoint))

theorem co3_non_through_local_orbit (q : Co3PointHeptad co3MarkedCoordinate)
    (h0 : q ≠ Sum.inl co3BasePoint) (h2 : co3LocalType _ co3BasePoint q ≠ 2) :
    co3PointHeptadDecompositionEquiv _ q ∈ co3LocalOrbit := by
  cases q with
  | inl c =>
    have hc : c ≠ co3BasePoint := fun h => h0 (congrArg Sum.inl h)
    have ho : co3OutsidePoint ≠ co3BasePoint := by
      intro h; have hh := congrArg Subtype.val h; cases hh
    obtain ⟨g,hg⟩ := co3_local_class_transporter (Sum.inl co3OutsidePoint) (Sum.inl c)
      (by simp [co3LocalType,hc,ho])
    exact MulAction.mem_orbit_iff.mpr ⟨g,hg⟩
  | inr B =>
    have hb : co3BasePoint ∉ B.val := by intro hb; simp [co3LocalType,hb] at h2
    obtain ⟨p,hp,hO⟩ := co3Fusion_permutation_exists
    obtain ⟨C,hC⟩ := co3Fusion_heptad_image p hp hO
    have hc := (co3Fusion_complement_heptad p hp hO C hC).2
    let g : Co3PointStabilizer :=
      ⟨⟨co3FusionIsometry p,co3Fusion_fixes_normSix p hp⟩,co3Fusion_fixes_base_decomposition p hp⟩
    obtain ⟨h,hh⟩ := co3_local_class_transporter (Sum.inr C) (Sum.inr B)
      (by simp [co3LocalType,hc,hb])
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨h*g,?_⟩
    rw [mul_smul]
    have hg : g • co3PointHeptadDecompositionEquiv _ (Sum.inl co3OutsidePoint) =
        co3PointHeptadDecompositionEquiv _ (Sum.inr C) := hC
    rw [hg,hh]

theorem co3_all_other_local_orbit (q : Co3PointHeptad co3MarkedCoordinate)
    (h0 : q ≠ Sum.inl co3BasePoint) : co3PointHeptadDecompositionEquiv _ q ∈ co3LocalOrbit := by
  by_cases h2 : co3LocalType _ co3BasePoint q = 2
  · obtain ⟨g,F,r,hF,hr2,hr⟩ := co3_third_local_fusion
    have hr0 : r ≠ Sum.inl co3BasePoint := by
      intro he
      have hfix : g • co3BaseDecomposition = co3BaseDecomposition := g.prop
      have hh : g • co3PointHeptadDecompositionEquiv _ (Sum.inr F) = g • co3BaseDecomposition := by
        rw [hr,he,hfix]; rfl
      have hx := (co3PointHeptadDecompositionEquiv co3MarkedCoordinate).injective (smul_left_cancel g hh)
      cases hx
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp (co3_non_through_local_orbit r hr0 hr2)
    have hback : co3PointHeptadDecompositionEquiv _ (Sum.inr F) ∈ co3LocalOrbit := by
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨g⁻¹*h,?_⟩
      rw [mul_smul,hh,← hr,inv_smul_smul]
    obtain ⟨k,hk⟩ := co3_local_class_transporter (Sum.inr F) q
      (by simpa [co3LocalType,hF] using h2.symm)
    obtain ⟨l,hl⟩ := MulAction.mem_orbit_iff.mp hback
    exact MulAction.mem_orbit_iff.mpr ⟨k*l,by rw [mul_smul,hl,hk]⟩
  · exact co3_non_through_local_orbit q h0 h2

theorem co3_point_stabilizer_complement_transitive :
    MulAction.IsPretransitive Co3PointStabilizer (SubMulAction.ofStabilizer Co3MarkedModel co3BaseDecomposition) := by
  constructor
  intro x y
  obtain ⟨p,hp⟩ := (co3PointHeptadDecompositionEquiv co3MarkedCoordinate).surjective x.val
  obtain ⟨q,hq⟩ := (co3PointHeptadDecompositionEquiv co3MarkedCoordinate).surjective y.val
  have hp0 : p ≠ Sum.inl co3BasePoint := by
    intro h; apply x.prop
    change x.val = co3BaseDecomposition
    rw [← hp,h]; rfl
  have hq0 : q ≠ Sum.inl co3BasePoint := by
    intro h; apply y.prop
    change y.val = co3BaseDecomposition
    rw [← hq,h]; rfl
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (co3_all_other_local_orbit p hp0)
  obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp (co3_all_other_local_orbit q hq0)
  refine ⟨h*g⁻¹,Subtype.ext ?_⟩
  change (h*g⁻¹) • x.val = y.val
  rw [← hp,← hq,← hg,mul_smul,inv_smul_smul,hh]

theorem co3_decompositions_two_transitive :
    MulAction.IsMultiplyPretransitive Co3MarkedModel
      (MinimumDecompositions (normSixVector co3MarkedCoordinate)) 2 := by
  let := co3_decompositions_pretransitive
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := co3BaseDecomposition)).mpr
  exact MulAction.is_one_pretransitive_iff.mpr co3_point_stabilizer_complement_transitive

theorem co3_decompositions_primitive : MulAction.IsPreprimitive Co3MarkedModel
    (MinimumDecompositions (normSixVector co3MarkedCoordinate)) :=
  MulAction.isPreprimitive_of_is_two_pretransitive co3_decompositions_two_transitive

end Atlas.Conway
