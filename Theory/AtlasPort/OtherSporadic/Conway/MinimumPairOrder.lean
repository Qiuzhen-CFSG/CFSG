/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimumPairOrder.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OvergroupOrthogonalTransitivity
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalPairStabilizer
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimumPairOrder.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem shell_stabilizer_eq (H : Subgroup LeechIsometryGroup) (x : LeechShell 4) :
    MulAction.stabilizer H x = leechVectorStabilizer H x.val := by
  ext g
  change g • x = x ↔ g.val.val x.val = x.val
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

def minimumPairMinusShell (e : Fin 2 ↪ Omega) : LeechShell 4 :=
  ⟨minimumPairMinus (e 0) (e 1),minimumPairMinus_norm _ _ (e.injective.ne (by decide))⟩

def nestedPairStabilizerEquiv (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup ≤ H) (e : Fin 2 ↪ Omega) :
    MulAction.stabilizer (leechVectorStabilizer H (minimumPairPlus (e 0) (e 1)))
      (minimumPairMinusShell e) ≃ orthogonalPairStabilizer e where
  toFun g := ⟨g.val.val.val,(orthogonalPairStabilizer_mem e _).mpr
    ⟨g.val.prop,congrArg Subtype.val g.prop⟩⟩
  invFun g := ⟨⟨⟨g.val,orthogonalPairStabilizer_le_overgroup e H hH g.prop⟩,
    ((orthogonalPairStabilizer_mem e _).mp g.prop).1⟩,
      Subtype.ext ((orthogonalPairStabilizer_mem e _).mp g.prop).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem strict_overgroup_point_stabilizer_order (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) (e : Fin 2 ↪ Omega) :
    Nat.card (leechVectorStabilizer H (minimumPairPlus (e 0) (e 1))) =
      93150 * (1024 * 443520) := by
  let y : LeechShell 4 := minimumPairMinusShell e
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (leechVectorStabilizer H (minimumPairPlus (e 0) (e 1))) y)
  rw [Nat.card_prod,strict_overgroup_orthogonal_orbit_card H hH _ _
    (e.injective.ne (by decide)) y (minimumPair_orthogonal _ _ (e.injective.ne (by decide))),
    Nat.card_congr (nestedPairStabilizerEquiv H hH.le e),orthogonalPairStabilizer_order] at hc
  exact hc.symm

end Atlas.Conway
