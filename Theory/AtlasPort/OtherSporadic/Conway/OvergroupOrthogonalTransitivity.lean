/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OvergroupOrthogonalTransitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalOrbitFusion
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OvergroupOrthogonalTransitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem strict_overgroup_orthogonal_orbit_full (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) (i j : Omega) (hij : i ≠ j) (base : LeechShell 4)
    (hb : integerDot (minimumPairPlus i j).val base.val.val = 0)
    (x : LeechShell 4) (hx : integerDot (minimumPairPlus i j).val x.val.val = 0) :
    x ∈ MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base :=
  orthogonal_orbit_fusion H hH.le i j hij base hb
    (strict_overgroup_orthogonal_orbit_dvd H hH
      ⟨minimumPairPlus i j,minimumPairPlus_norm i j hij⟩ base hb) x hx

theorem strict_overgroup_orthogonal_orbit_card (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) (i j : Omega) (hij : i ≠ j) (base : LeechShell 4)
    (hb : integerDot (minimumPairPlus i j).val base.val.val = 0) :
    Nat.card (MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base) = 93150 := by
  have he : MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base =
      {x : LeechShell 4 | integerDot (minimumPairPlus i j).val x.val.val = 0} := by
    ext x
    exact ⟨orthogonal_point_orbit_orthogonal H i j base hb x,
      strict_overgroup_orthogonal_orbit_full H hH i j hij base hb x⟩
  rw [Nat.card_congr (Equiv.setCongr he)]
  exact orthogonalMinimumShell_card i j hij

end Atlas.Conway
