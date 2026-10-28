/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleParameterInjective
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleCount.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- Independent coordinate/Golay parametrization of the intrinsic triangle set. -/
def co3TriangleEquiv (a : Omega) :
    ((t : Fin 8) × Co3TriangleParameters a t) ≃ Co3Triangles a :=
  Equiv.ofBijective (co3TriangleParameterMap a)
    ⟨co3TriangleParameterMap_injective a,co3TriangleParameterMap_surjective a⟩

theorem co3_triangles_card (a : Omega) : Nat.card (Co3Triangles a) = 48600 := by
  rw [← Nat.card_congr (co3TriangleEquiv a),co3_triangle_total_parameters_card]

def co3TriangleShapeEquiv (a : Omega) (t : Fin 8) :
    Co3TriangleParameters a t ≃ {y : leech // Co3TriangleShape a t y} :=
  Equiv.ofBijective (fun p => ⟨co3TriangleParameterVector a t p,co3_triangle_parameter_shape a t p⟩)
    ⟨fun p q h => co3TriangleParameterVector_injective a t (congrArg Subtype.val h),by
      intro y
      obtain ⟨p,hp⟩ := co3_triangle_parameter_represents a t y.val y.prop
      exact ⟨p,Subtype.ext hp⟩⟩

theorem co3_triangle_shape_card (a : Omega) (t : Fin 8) :
    Nat.card {y : leech // Co3TriangleShape a t y} = co3TriangleSize t := by
  rw [← Nat.card_congr (co3TriangleShapeEquiv a t),co3_triangle_parameters_card]

end Atlas.Conway
