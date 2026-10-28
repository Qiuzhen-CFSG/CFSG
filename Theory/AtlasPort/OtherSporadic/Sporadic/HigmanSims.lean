/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/HigmanSims.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsLocal
public import Theory.AtlasPort.OtherSporadic.Conway.HSRankThree

/-!
Order and rank-three actions of the Higman–Sims group.
The full triangle stabilizer has order 44352000 by the saturated Conway3 and Mathieu22 orbit bounds.

Source: Gerald Höhn, `Atlas/Sporadic/HigmanSims.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway MulAction

abbrev SideStabilizer := HSSideStabilizer

def sideStabilizerEquiv : SideStabilizer ≃* Model := hsSideStabilizerEquiv

theorem card : Nat.card Model = 44352000 := hs_order

theorem order : Nat.card Model = 2^9*3^2*5^3*7*11 := hs_order_factored

theorem saturated_orbit_bounds :
    Nat.card (orbit Conway3.Model baseSide) = 11178 ∧
      Nat.card (orbit Model basePoint) = 100 := hs_saturated_orbit_bounds

theorem side_orbit_univ : orbit Conway3.Model baseSide = Set.univ := hs_side_orbit_univ

theorem graph_orbit_univ : orbit Model basePoint = Set.univ := hs_graph_orbit_univ

theorem sides_transitive : IsPretransitive Conway3.Model Sides := hs_sides_transitive

theorem transitive : IsPretransitive Model Points := hs_graph_transitive

theorem conway3_order_identity : 11178*Nat.card Model = Nat.card Conway3.Model := hs_conway3_order_identity

theorem mathieu22_order_identity : Nat.card Model = 100*Nat.card MathieuModel := hs_mathieu22_order_identity

def localOrbitEquiv : orbitRel.Quotient PointStabilizer Points ≃ Fin 3 := hsLocalOrbitEquiv

theorem rank_three : Nat.card (orbitRel.Quotient PointStabilizer Points) = 3 := hs_graph_rank_three

def sideOrbitEquiv : orbit Conway3.Model baseSide ≃ Sides := Equiv.ofBijective Subtype.val
  ⟨Subtype.val_injective,by intro y; exact ⟨⟨y,by rw [side_orbit_univ]; trivial⟩,rfl⟩⟩

def graphOrbitEquiv : orbit Model basePoint ≃ Points := Equiv.ofBijective Subtype.val
  ⟨Subtype.val_injective,by intro y; exact ⟨⟨y,by rw [graph_orbit_univ]; trivial⟩,rfl⟩⟩

theorem side_orbit_equivariant (g : Conway3.Model) (y : orbit Conway3.Model baseSide) :
    sideOrbitEquiv (g • y) = g • sideOrbitEquiv y := rfl

theorem graph_orbit_equivariant (g : Model) (y : orbit Model basePoint) :
    graphOrbitEquiv (g • y) = g • graphOrbitEquiv y := rfl

end Atlas.Sporadic.HigmanSims
