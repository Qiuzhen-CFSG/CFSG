/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/HigmanSimsSimplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSims
public import Theory.AtlasPort.OtherSporadic.Conway.HSSimplicity
public import Theory.AtlasPort.OtherSporadic.GroupTheory.NonabelianSimplePerfect

/-!
Simplicity and perfectness of the Higman–Sims model.
The primitive graph action and simple point stabilizer prove simplicity; an explicit noncommuting pair proves perfectness.

Source: Gerald Höhn, `Atlas/Sporadic/HigmanSimsSimplicity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway MulAction

theorem primitive : IsPreprimitive Model Points := hs_graph_primitive

theorem regular_normal_impossible (N : Subgroup Model) [N.Normal]
    [IsPretransitive N Points]
    (h : ∀ n : N, n • basePoint = basePoint → n = 1) : False :=
  hs_regular_normal_impossible N h

theorem isSimpleGroup : IsSimpleGroup Model := hs_simple

theorem perfect : Group.IsPerfect Model := by
  let := isSimpleGroup
  exact Atlas.GroupTheory.nonabelian_simple_perfect Model exists_mul_ne_mul

end Atlas.Sporadic.HigmanSims
