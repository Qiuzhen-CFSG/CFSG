/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionFrameGeneration.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisTransitionImages
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionPointNormalizations
public import Theory.AtlasPort.Janko2.Conway.IcosianRootFrameStabilizer

/-!
# IcosianReflectionFrameGeneration

Root-point transitivity and the five-frame local action give frame transitivity. The
full frame stabilizer already lies in the reflection subgroup, proving generation of
the entire group.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionFrameGeneration.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open scoped Pointwise

/-- Root-line transitivity and the local five-frame action give transitivity
on actual quaternionic root frames. -/
theorem icosianReflectionGroup_frame_normalizer (F : IcosianRootFrame) :
    ∃ g : icosianReflectionGroup,g.val • icosianLocalCoordinateRootFrame=F := by
  classical
  have hn : F.val.Nonempty := Finset.card_pos.mp (by rw [F.property.1]; omega)
  obtain ⟨p,hp⟩ := hn
  obtain ⟨g,hg⟩ := icosianReflectionGroup_point_normalizer p
  have hF : icosianRootAxisPoint 0∈(g.val⁻¹ • F).val := by
    have h := (icosianRootFrame_smul_mem_iff g.val⁻¹ F p).mpr hp
    rw [← hg,inv_smul_smul] at h
    exact h
  obtain ⟨h,hh0,hh⟩ := icosianReflectionGroup_transitive_axis_frames (g.val⁻¹ • F) hF
  refine ⟨g*h,?_⟩
  change (g.val*h.val) • icosianLocalCoordinateRootFrame=F
  rw [mul_smul,hh,smul_inv_smul]

instance icosianReflectionGroup_frame_pretransitive :
    MulAction.IsPretransitive icosianReflectionGroup IcosianRootFrame where
  exists_smul_eq F G := by
    obtain ⟨g,hg⟩ := icosianReflectionGroup_frame_normalizer F
    obtain ⟨h,hh⟩ := icosianReflectionGroup_frame_normalizer G
    refine ⟨h*g⁻¹,?_⟩
    change (h.val*g.val⁻¹) • F=G
    rw [mul_smul,← hg,inv_smul_smul,hh]

instance icosianHermitian_frame_pretransitive :
    MulAction.IsPretransitive icosianHermitianGroup IcosianRootFrame where
  exists_smul_eq F G := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq icosianReflectionGroup F G
    exact ⟨g.val,hg⟩

/-- The entire actual quaternion-linear Hermitian lattice group is generated
by its actual root reflections: the full frame stabilizer is already in W. -/
theorem icosianReflectionGroup_eq_top : icosianReflectionGroup=⊤ := by
  apply top_unique
  intro f _
  obtain ⟨g,hg⟩ := icosianReflectionGroup_frame_normalizer
    (f • icosianLocalCoordinateRootFrame)
  have hs : g.val⁻¹*f∈icosianCoordinateFrameStabilizer := by
    rw [← icosianLocalCoordinateRootFrame_stabilizer]
    change (g.val⁻¹*f) • icosianLocalCoordinateRootFrame=icosianLocalCoordinateRootFrame
    rw [mul_smul,← hg,inv_smul_smul]
  have hm := icosianReflectionGroup.mul_mem g.property
    (icosian_full_frame_generated_by_reflections hs)
  simpa only [mul_inv_cancel_left] using hm

end Atlas.Conway
