/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/McLaughlinSimplicity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLSimplicity
public import Theory.AtlasPort.OtherSporadic.GroupTheory.NonabelianSimplePerfect
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
Simplicity and perfectness of the concrete McLaughlin group.
The primitive triangle action and the second graph action prove simplicity;
the endpoint permutation kernel is the commutator of the unordered-pair stabilizer.

Source: Gerald Höhn, ATLAS, `Atlas/Sporadic/McLaughlinSimplicity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.McLaughlin
open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped IsMulCommutative

theorem isSimpleGroup : IsSimpleGroup Model := mcl_simple

theorem perfect : Group.IsPerfect Model := by
  let := isSimpleGroup
  exact Atlas.GroupTheory.nonabelian_simple_perfect Model exists_mul_ne_mul

theorem pair_commutator_eq_kernel : commutator PairStabilizer = endpointPermutation.ker := by
  let : IsMulCommutative (Equiv.Perm Endpoints) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr (by rw [mcl_endpoints_card])
  apply le_antisymm (Abelianization.commutator_subset_ker endpointPermutation)
  let := perfect
  have : Group.IsPerfect toPairStabilizer.range := Group.IsPerfect.range toPairStabilizer
  have hr : toPairStabilizer.range ≤ commutator PairStabilizer := by
    rw [← toPairStabilizer.range.commutator_eq_self]
    exact Subgroup.commutator_mono le_top le_top
  rw [toPairStabilizer_range] at hr
  exact hr

theorem pair_commutator_eq_model_image : commutator PairStabilizer = toPairStabilizer.range := by
  rw [pair_commutator_eq_kernel,toPairStabilizer_range]

end Atlas.Sporadic.McLaughlin
