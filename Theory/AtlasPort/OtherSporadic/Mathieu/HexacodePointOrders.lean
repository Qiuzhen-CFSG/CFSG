/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodePointStabilizer

/-!
# HexacodePointOrders

The coordinate stabilizer in the hexacode automorphism group has order 360 and its
local-action kernel has order 60. Coordinate transitivity gives the first count;
surjectivity onto the six local isometries gives the second.

Source: `Atlas/Mathieu/HexacodePointOrders.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

instance hexCoordinateAction : MulAction HexAutomorphisms HexIndex :=
  MulAction.compHom HexIndex hexCoordinateHom

theorem hexCoordinateAction_transitive (i j : HexIndex) : ∃ g : HexAutomorphisms, g • i = j := by
  obtain ⟨g,hg⟩ := hexCoordinateHom_surjective (Equiv.swap i j)
  refine ⟨g,?_⟩
  change hexCoordinateHom g i = j
  rw [hg,Equiv.swap_apply_left]

def hexPointOrbitEquiv (i : HexIndex) : MulAction.orbit HexAutomorphisms i ≃ HexIndex :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,by
    intro j
    exact ⟨⟨j,MulAction.mem_orbit_iff.mpr (hexCoordinateAction_transitive i j)⟩,rfl⟩⟩

def hexPointOrbitStabilizerEquiv (i : HexIndex) : HexIndex × hexPointStabilizer i ≃ HexAutomorphisms :=
  ((hexPointOrbitEquiv i).symm.prodCongr (Equiv.refl _)).trans
    (MulAction.orbitProdStabilizerEquivGroup HexAutomorphisms i)

theorem hexPointStabilizer_card (i : HexIndex) : Nat.card (hexPointStabilizer i) = 360 := by
  have h := Nat.card_congr (hexPointOrbitStabilizerEquiv i)
  rw [Nat.card_prod,hexAutomorphisms_card] at h
  have hc : Nat.card HexIndex = 6 := by simp [HexIndex]
  rw [hc] at h
  omega

def hexPointKernel (i : HexIndex) : Subgroup (hexPointStabilizer i) := (hexPointLocal i).ker

theorem hexPointKernel_card (i : HexIndex) : Nat.card (hexPointKernel i) = 60 := by
  have h := (hexPointLocal i).ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr (hexPointLocal_surjective i),
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup KIsometry) ≃* KIsometry).toEquiv,
    kIsometry_card,hexPointStabilizer_card] at h
  change Nat.card (hexPointKernel i) * 6 = 360 at h
  omega

end Atlas.Codes
