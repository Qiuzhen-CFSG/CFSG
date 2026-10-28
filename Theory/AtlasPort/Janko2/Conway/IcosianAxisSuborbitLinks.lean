/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisSuborbitLinks.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisTransitionEvaluation
public import Theory.AtlasPort.Janko2.Conway.IcosianLocalBReference
public import Theory.AtlasPort.Janko2.Conway.IcosianRootLocalReferences
public import Theory.AtlasPort.Janko2.Lattices.IcosianRootPermutations

/-!
# IcosianAxisSuborbitLinks

Concrete roots are inputs for the axis transition words. Matrix evaluation determines
the coordinate norms of the resulting orbit links.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisSuborbitLinks.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

def icosianAxisLinkBInput : IcosianRoot :=
  icosianRootPermute (Equiv.swap 0 1) icosianLocalBRoot

def icosianAxisLinkCInput : IcosianRoot :=
  icosianRootPermute (Equiv.swap 0 1) icosianLocalCRoot

/-- An axis-fixing reflection word joins the nonorthogonal B and C local pieces. -/
theorem icosianAxisTransition_B_C_norm (j : Fin 3) :
    icosianNorm ((icosianAxisTransitionWord 0).val
      (icosianCoordinateEmbedding icosianAxisLinkBInput.val) j)=(![2,1,1] j) := by
  rw [icosianAxisTransitionWord_matrix_apply]
  fin_cases j <;> decide +kernel

/-- A second axis-fixing word joins the norm-one C and D local pieces. -/
theorem icosianAxisTransition_C_D_norm (j : Fin 3) :
    icosianNorm ((icosianAxisTransitionWord 1).val
      (icosianCoordinateEmbedding icosianAxisLinkCInput.val) j)=
        (![1,1+goldenTau,2-goldenTau] j) := by
  rw [icosianAxisTransitionWord_matrix_apply]
  fin_cases j <;> decide +kernel

end Atlas.Conway
