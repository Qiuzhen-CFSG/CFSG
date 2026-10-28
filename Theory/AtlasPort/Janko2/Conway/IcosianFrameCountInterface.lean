/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianFrameCountInterface.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointOrthogonality
public import Theory.AtlasPort.Janko2.Conway.IcosianRootGeometryCard
public import Theory.AtlasPort.Janko2.Combinatorics.RegularUniqueTriangleCount

/-!
# IcosianFrameCountInterface

A degree-ten orthogonality relation on 315 root points with unique triangle
completion has 525 frames. The general incidence-counting theorem proves this
conditional interface.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianFrameCountInterface.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Combinatorics

/-- The remaining geometric local obligations imply the exact count of all
actual quaternionic root frames. No group order or transitivity is a premise. -/
theorem icosianRootFrame_card_of_local_geometry
    (hdegree : ∀ p : IcosianRootPoint,
      Nat.card {q : IcosianRootPoint // IcosianRootPointOrthogonal p q}=10)
    (hthird : ∀ p q : IcosianRootPoint,IcosianRootPointOrthogonal p q →
      ∃! r : IcosianRootPoint,IcosianRootPointOrthogonal p r ∧ IcosianRootPointOrthogonal q r) :
    Nat.card IcosianRootFrame=525 := by
  let : Fintype IcosianRootPoint := Fintype.ofFinite _
  exact regular_unique_triangle_count_315_10 IcosianRootPointOrthogonal
    (fun _ _ => icosianRootPointOrthogonal_symm) icosianRootPointOrthogonal_irrefl
    hthird icosianRootPoint_card hdegree

end Atlas.Conway
