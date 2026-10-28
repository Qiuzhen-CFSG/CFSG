/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway3Action.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3DoubleTransitivity
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Sporadic/Conway3Action.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway3
open Atlas.Codes Atlas.Lattices Atlas.Conway

theorem finite_points : Finite Points := Nat.finite_of_card_ne_zero (by rw [degree]; decide)

theorem transitive : MulAction.IsPretransitive Model Points := co3_decompositions_pretransitive

theorem two_transitive : MulAction.IsMultiplyPretransitive Model Points 2 :=
  co3_decompositions_two_transitive

theorem primitive : MulAction.IsPreprimitive Model Points := co3_decompositions_primitive

def basePoint : Points := co3BaseDecomposition

/-- The full point stabilizer, retained without any future group identification. -/
abbrev PointStabilizer := MulAction.stabilizer Model basePoint

theorem point_stabilizer_card : Nat.card PointStabilizer = 1796256000 := by
  let := transitive
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Model basePoint)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_congr (Equiv.Set.univ _),degree,card] at h
  change 276*Nat.card PointStabilizer = 495766656000 at h
  omega

theorem point_stabilizer_complement_transitive :
    MulAction.IsPretransitive PointStabilizer (SubMulAction.ofStabilizer Model basePoint) :=
  co3_point_stabilizer_complement_transitive

end Atlas.Sporadic.Conway3
