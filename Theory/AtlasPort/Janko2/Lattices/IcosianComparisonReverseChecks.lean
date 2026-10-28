/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianComparisonReverseChecks.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonGeneratorsData
public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonSpace

/-!
# Icosian Comparison Reverse Checks

Explicit preimages of all 38 retained Leech generators satisfy the
icosian congruences. Kernel-checked finite arithmetic verifies both
membership and the comparison matrix images.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianComparisonReverseChecks.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix

theorem icosianComparisonPreimage_mem (j : Fin 38) :
    icosianComparisonPreimage j ∈ icosianLeechModule := by
  rw [icosianLeechModule_mem,icosianP_mem,icosianP_mem,icosianPZero_mem]
  simp only [icosianComparisonPreimage,map_sub,map_add,icosianModuloTwo_synthesis,
    Matrix.sub_apply,Matrix.add_apply]
  revert j
  decide +kernel

theorem icosianComparison_preimage_arithmetic : ∀ j : Fin 38,
    icosianComparisonMatrix *ᵥ icosianRealCoordinates
      (icosianCoordinateEmbedding (icosianComparisonPreimage j)) =
    rationalEmbedding (icosianComparisonTargetGenerator j) := by
  decide +kernel

theorem icosianComparison_preimage_check (j : Fin 38) :
    icosianComparison (icosianCoordinateEmbedding (icosianComparisonPreimage j)) =
      rationalEmbedding (icosianComparisonTargetGenerator j) :=
  icosianComparison_preimage_arithmetic j

end Atlas.Lattices
