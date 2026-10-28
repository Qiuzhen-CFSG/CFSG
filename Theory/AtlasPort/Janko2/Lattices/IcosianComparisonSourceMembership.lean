/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianComparisonSourceMembership.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonGeneratorsData

/-!
# Icosian Comparison Source Membership

The 36 comparison source vectors satisfy the integral icosian lattice
congruences. Reducing their synthesis coefficients modulo two turns
membership into kernel-checked finite matrix identities.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianComparisonSourceMembership.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Atlas.Lattices
open Atlas.Algebra
open scoped Matrix

theorem icosianComparisonSourceGenerator_mem (j : Fin 36) :
    icosianComparisonSourceGenerator j ∈ icosianLeechModule := by
  rw [icosianLeechModule_mem,icosianP_mem,icosianP_mem,icosianPZero_mem]
  simp only [icosianComparisonSourceGenerator,map_sub,map_add,icosianModuloTwo_synthesis,
    Matrix.sub_apply,Matrix.add_apply]
  revert j
  decide +kernel

end Atlas.Lattices
