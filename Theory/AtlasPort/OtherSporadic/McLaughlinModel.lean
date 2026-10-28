/-
Copyright (c) 2026 Gerald Höhn.
Based on ATLAS's McLaughlin construction and simplicity proof.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.McLaughlinSimplicity
public import Theory.AtlasPort.OtherSporadic.Sporadic.McLaughlinGraph

/-!
# The McLaughlin triangle stabilizer

The exported carrier `Atlas.Sporadic.McLaughlin.Model` is
`Atlas.Conway.McLModel`, the pointwise stabilizer of the specified Leech 2-2-3
triangle inside the norm-six vector stabilizer. Its embedding into Co3 is
`Atlas.Sporadic.McLaughlin.toConway3`.

The endpoint permutation kernel has index two in the unordered endpoint
stabilizer, giving order 898128000. The primitive faithful action on 2025
triangles has simple Mathieu22 stabilizer. A second action on 275 graph
vertices excludes the regular normal subgroup case, proving simplicity.
The embedded Mathieu22 supplies the noncommuting-pair witness.

Source: Gerald Höhn, ATLAS, `Atlas/Sporadic/McLaughlinSimplicity.lean` and
`Atlas/Sporadic/McLaughlinGraph.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public re-exports of the source interfaces.
Definition bodies remain exposed where the geometric constructions require
cross-module coordinate reduction.
-/
