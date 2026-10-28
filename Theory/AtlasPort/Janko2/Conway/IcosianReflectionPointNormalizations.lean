/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionPointNormalizations.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianPointNormalizations
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionDiagonalImage

/-!
# IcosianReflectionPointNormalizations

The full frame stabilizer and all root reflections lie in the reflection subgroup.
The point-normalizer construction therefore proves root-point transitivity for that
subgroup.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionPointNormalizations.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway

/-- Every actual quaternionic root line is reached by actual root reflections.
This is separated from the independent incidence count. -/
theorem icosianReflectionGroup_point_normalizer (p : IcosianRootPoint) :
    ∃ g : icosianReflectionGroup,g.val • icosianRootAxisPoint 0=p := by
  obtain ⟨g,hg,he⟩ := icosianRootPoint_normalizers_in icosianReflectionGroup
    icosian_full_frame_generated_by_reflections icosianRootReflectionOf_mem p
  exact ⟨⟨g,hg⟩,he⟩

instance icosianReflectionGroup_rootPoint_pretransitive :
    MulAction.IsPretransitive icosianReflectionGroup IcosianRootPoint where
  exists_smul_eq p q := by
    obtain ⟨g,hg⟩ := icosianReflectionGroup_point_normalizer p
    obtain ⟨h,hh⟩ := icosianReflectionGroup_point_normalizer q
    refine ⟨h*g⁻¹,?_⟩
    change (h.val*g.val⁻¹) • p=q
    rw [mul_smul,← hg,inv_smul_smul,hh]

end Atlas.Conway
