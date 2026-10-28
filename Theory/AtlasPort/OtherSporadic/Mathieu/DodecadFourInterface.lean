/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadFourRegular
public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadPointOrders

/-!
# DodecadFourInterface

The actual four-point dodecad stabilizer is multiplicatively equivalent to its
parametrized affine stabilizer. The coordinate-compatible equivalences transfer its
order and recover the full dodecad-stabilizer order from four-transitivity.

Source: `Atlas/Mathieu/DodecadFourInterface.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

abbrev dodecadFourFixing (i : HexIndex) (p : DodecadParameters i) :=
  fixingSubgroup (Mathieu12DodecadModel (dodecadParametersSupport i p).val)
    {z : Mathieu12Points (dodecadParametersSupport i p).val | z.val ∈ tetrad i}

def dodecadFourActualEquiv (i : HexIndex) (p : DodecadParameters i) :
    (MulAction.stabilizer (TetradPointStabilizer i) (dodecadParametersSupport i p).val) ≃*
      dodecadFourFixing i p where
  toFun x := ⟨⟨x.val.val,x.prop⟩,by
    apply (mem_fixingSubgroup_iff _).mpr
    intro z hz
    apply Subtype.ext
    exact x.val.prop ⟨z.val,hz⟩⟩
  invFun x := ⟨⟨x.val.val,by
    apply (mem_fixingSubgroup_iff _).mpr
    intro z hz
    let z' : Mathieu12Points (dodecadParametersSupport i p).val :=
      ⟨z,(dodecadParametersSupport i p).prop hz⟩
    exact congrArg Subtype.val (((mem_fixingSubgroup_iff _).mp x.prop) z' hz)⟩,x.val.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def dodecadFourAffineEquiv (i : HexIndex) (p : DodecadParameters i) :
    dodecadAffineStabilizer i p ≃* dodecadFourFixing i p :=
  (dodecadAffineActualEquiv i p).trans (dodecadFourActualEquiv i p)

theorem dodecadFourAffineEquiv_coordinates (i : HexIndex) (p : DodecadParameters i)
    (x : dodecadAffineStabilizer i p) (z : Omega) :
    (dodecadFourAffineEquiv i p x).val.val.val z =
      affinePermutation x.val.left.toAdd.val.val x.val.right.val.val.val z := rfl

theorem dodecadFourFixing_card (i : HexIndex) (p : DodecadParameters i) :
    Nat.card (dodecadFourFixing i p) = 8 := by
  rw [← Nat.card_congr (dodecadFourAffineEquiv i p).toEquiv,dodecadAffineStabilizer_card]

theorem mathieu12_order_from_four_points (D : Dodecad) (e : Fin 4 ↪ Mathieu12Points D) :
    Nat.card (Mathieu12DodecadModel D) = (12*11*10*9) *
      Nat.card (dodecadOrderedStabilizer D e) := by
  rw [mathieu12_order,mathieu12_four_point_order]

end Atlas.Codes
