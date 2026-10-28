/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.TetradLocalAction

/-!
# HexacodeZeroCoordinate

Hexacode words vanishing at one coordinate form a sixteen-element module preserved by
that coordinate stabilizer. Restricting its linear action gives the affine tetrad
pointwise model and its order 960.

Source: `Atlas/Mathieu/HexacodeZeroCoordinate.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def hexZeroCoordinate (i : HexIndex) : Submodule Bit hexacode := (hexCoordinate i).ker

theorem hexZeroCoordinate_card (i : HexIndex) : Nat.card (hexZeroCoordinate i) = 16 := by
  classical
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,hexZeroCoordinate,LinearMap.mem_ker] using hexCoordinate_fiber i 0

theorem hexZeroCoordinate_other_surjective (i j : HexIndex) (hij : i ≠ j) (u : K) :
    ∃ h : hexZeroCoordinate i, h.val.val j = u := by
  obtain ⟨h,hi,hj⟩ := hex_two_values i j hij 0 u
  exact ⟨⟨h,hi⟩,hj⟩

def hexZeroAct (i : HexIndex) (g : hexPointStabilizer i) (h : hexZeroCoordinate i) : hexZeroCoordinate i :=
  ⟨hexAction g.val h.val,by
    change g.val.val.localMap i (h.val.val (g.val.val.perm.symm i)) = 0
    rw [hexPointStabilizer_inv_fixed]
    have hh : h.val.val i = 0 := h.prop
    rw [hh,map_zero]⟩

def hexZeroLinear (i : HexIndex) (g : hexPointStabilizer i) :
    hexZeroCoordinate i ≃ₗ[Bit] hexZeroCoordinate i where
  toFun := hexZeroAct i g
  invFun := hexZeroAct i g⁻¹
  left_inv h := by
    apply Subtype.ext
    change hexAction g.val⁻¹ (hexAction g.val h.val) = h.val
    rw [← LinearEquiv.mul_apply,← map_mul,inv_mul_cancel,map_one]
    rfl
  right_inv h := by
    apply Subtype.ext
    change hexAction g.val (hexAction g.val⁻¹ h.val) = h.val
    rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl
  map_add' h k := Subtype.ext (map_add (hexAction g.val) h.val k.val)
  map_smul' r h := Subtype.ext (map_smul (hexAction g.val) r h.val)

def hexZeroAffineAction (i : HexIndex) : hexPointKernel i →* MulAut (Multiplicative (hexZeroCoordinate i)) where
  toFun g := (hexZeroLinear i g.val).toAddEquiv.toMultiplicative
  map_one' := by apply MulEquiv.ext; intro h; rfl
  map_mul' g h := by apply MulEquiv.ext; intro v; rfl

abbrev TetradPointAffine (i : HexIndex) :=
  Multiplicative (hexZeroCoordinate i) ⋊[hexZeroAffineAction i] hexPointKernel i

def hexZeroInclusion (i : HexIndex) : Multiplicative (hexZeroCoordinate i) →* Multiplicative hexacode where
  toFun h := Multiplicative.ofAdd h.toAdd.val
  map_one' := rfl
  map_mul' _ _ := rfl

def tetradPointAffineInclusion (i : HexIndex) : TetradPointAffine i →* SextetAffineGroup :=
  SemidirectProduct.map (hexZeroInclusion i)
    ((hexPointStabilizer i).subtype.comp (hexPointKernel i).subtype)
    (by intro g; apply MonoidHom.ext; intro h; rfl)

theorem tetradPointAffine_card (i : HexIndex) : Nat.card (TetradPointAffine i) = 960 := by
  rw [SemidirectProduct.card,Nat.card_congr (Multiplicative.toAdd : Multiplicative (hexZeroCoordinate i) ≃ _),
    hexZeroCoordinate_card,hexPointKernel_card]

end Atlas.Codes
