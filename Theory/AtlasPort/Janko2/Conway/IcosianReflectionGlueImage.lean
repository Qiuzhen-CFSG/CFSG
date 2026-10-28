/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionGlueImage.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionSignKernel
public import Theory.AtlasPort.Janko2.Codes.IcosianGlueGeneration

/-!
# IcosianReflectionGlueImage

The monomial part of the reflection subgroup maps to a subgroup of the glue
stabilizer. Containment of the reduction kernel turns finite-image generation into
full frame generation.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionGlueImage.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes

def icosianReflectionMonomialSubgroup : Subgroup icosianLiftedMonomial :=
  icosianReflectionGroup.comap icosianMonomialToHermitian

def icosianLiftedReduction : icosianLiftedMonomial →* IcosianGlueMonomialGroup GoldenFour :=
  icosianMonomialReduction.comp icosianLiftedMonomial.subtype

def icosianReflectionGlueImage : Subgroup (IcosianGlueMonomialGroup GoldenFour) :=
  icosianReflectionMonomialSubgroup.map icosianLiftedReduction

theorem icosianLiftedReduction_kernel_le_reflections :
    icosianLiftedReduction.ker≤ icosianReflectionMonomialSubgroup := by
  intro g hg
  exact icosianMonomial_kernel_mem_reflections g hg

theorem icosianReflectionGlueImage_le :
    icosianReflectionGlueImage≤ icosianGlueMonomialStabilizer GoldenFour := by
  rintro g ⟨x,hx,rfl⟩
  exact x.property

/-- The already verified sign kernel reduces full frame generation to the
complete small finite gluing stabilizer. -/
theorem icosianFrame_le_reflections_of_glue
    (h : icosianGlueMonomialStabilizer GoldenFour≤ icosianReflectionGlueImage) :
    icosianCoordinateFrameStabilizer≤ icosianReflectionGroup := by
  rw [← icosianMonomial_range_eq_frameStabilizer]
  rintro f ⟨g,rfl⟩
  have hm : icosianLiftedReduction g∈icosianReflectionGlueImage := h g.property
  have hc : g∈icosianReflectionGlueImage.comap icosianLiftedReduction := hm
  change g∈(icosianReflectionMonomialSubgroup.map icosianLiftedReduction).comap
    icosianLiftedReduction at hc
  rw [Subgroup.comap_map_eq_self icosianLiftedReduction_kernel_le_reflections] at hc
  exact hc

end Atlas.Conway
