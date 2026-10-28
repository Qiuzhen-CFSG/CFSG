module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/Simplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.Primitivity
public import Theory.AtlasPort.LinearGroups.G2.IwasawaCriterion
public import Theory.AtlasPort.LinearGroups.G2.IwasawaLocal

/-! The primitive singular-point action and perfect long-root Iwasawa structure prove simplicity over every finite field of size greater than two. -/

@[expose] public section

namespace Atlas.G2
variable {K : Type*} [Field K] [Finite K]

/-- The actual octonion automorphism group is simple over every finite field of size >2. -/
theorem isSimple (hq : 2 < Nat.card K) : IsSimpleGroup (Model K) := by
  let := singularPoints_primitive (K := K)
  let := isPerfect hq
  exact (iwasawa hq).isSimpleGroup Group.IsPerfect.commutator_eq_top inferInstance

end Atlas.G2
