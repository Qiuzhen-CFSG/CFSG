/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/CoordinateVectorStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MonomialStabilizer
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/CoordinateVectorStabilizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- SO1: fixing any lattice coordinate axis vector forces membership in the actual monomial group. -/
theorem coordinateEight_fixer_mem_monomial (g : LeechIsometryGroup) (a : Omega)
    (hg : g.val (coordinateEight a) = coordinateEight a) : g ∈ monomialSubgroup := by
  rw [← standardCrossStabilizer_eq_monomial,standardCrossStabilizer_mem]
  have hs : standardCross = standardCrossAt a := standardCross_independent _ _
  rw [hs]
  apply Subtype.ext
  change leechModTwoRepresentation g (leechReduction (coordinateEight a)) =
    leechReduction (coordinateEight a)
  rw [leechModTwoRepresentation_reduce,hg]

/-- Pointwise fixation of a pair whose sum is an axis forces the same conclusion. -/
theorem axis_sum_pair_fixer_mem_monomial (g : LeechIsometryGroup) (a : Omega) (x y : leech)
    (hxy : x + y = coordinateEight a) (hx : g.val x = x) (hy : g.val y = y) :
    g ∈ monomialSubgroup := by
  apply coordinateEight_fixer_mem_monomial g a
  rw [← hxy,map_add,hx,hy]

end Atlas.Conway
