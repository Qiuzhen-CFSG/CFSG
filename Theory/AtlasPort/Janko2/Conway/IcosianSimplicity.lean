/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianSimplicity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianPrimitivity

/-!
# IcosianSimplicity

The proved six-suborbit primitivity discharges the remaining premise of the Iwasawa
argument. Thus the concrete projective icosian group is simple.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianSimplicity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway

/-- Nonabelian simplicity of the actual sign quotient of the full
right-quaternion-linear Hermitian stabilizer of the icosian Leech lattice. -/
theorem icosianProjective_simple : IsSimpleGroup IcosianProjectiveModel := by
  let := icosianProjective_rootPoint_primitive
  exact icosianProjective_simple_of_primitive

end Atlas.Conway
