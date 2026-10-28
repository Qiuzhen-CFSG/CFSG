/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootGeometryCard.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointCount
public import Theory.AtlasPort.Janko2.Lattices.IcosianRootCount

/-!
# IcosianRootGeometryCard

The independently counted 37800 roots and 120-element scalar fibers give 315 root
points. The positive cardinality also supplies finiteness.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootGeometryCard.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


namespace Atlas.Conway
open Atlas.Lattices

theorem icosianRootPoint_card : Nat.card IcosianRootPoint=315 :=
  icosianRootPoint_card_of_root_card icosianRoots_card

instance icosianRootPoint_finite : Finite IcosianRootPoint :=
  Nat.finite_of_card_ne_zero (by rw [icosianRootPoint_card]; decide)

end Atlas.Conway
